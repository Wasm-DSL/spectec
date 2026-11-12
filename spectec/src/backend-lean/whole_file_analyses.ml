open Il.Ast
open Util.Source

(* Running examples used throughout this file.

   BEq example — setminus1_ and setminus_:

     IL:
       (DecD "setminus1_"
         [(TypP "X"); (ExpP "X_0" (VarT "X")); (ExpP "var_0_lst" (IterT (VarT "X") List))]
         (VarT "bool")
         [clause1: body = ListE [VarE "X_0"]
          clause2: body = IfE (CmpE `EqOp _ (VarE "w" : VarT "X") (VarE "w_1"))
                               [ListE []] [CallE "setminus1_" [TypA (VarT "X"); ...]]])

       (DecD "setminus_"
         [(TypP "X"); (ExpP "var_0_lst" (IterT (VarT "X") List)); ...]
         ...
         [clause1: body = ListE []
          clause2: body = CatE (CallE "setminus1_" [TypA (VarT "X"); ...])
                                (CallE "setminus_"  [TypA (VarT "X"); ...])])

     Goal Lean signatures (the [BEq X] binders being generated):
       def setminus1_ (X : Type) [BEq X] (X_0 : X) (var_0_lst : List X) : Bool := ...
       def setminus_  (X : Type) [BEq X] (var_0_lst : List X) ... : ... := ...

   Inhabited example — fun_relaxed2:

     IL:
       (DecD "fun_relaxed2"
         [(TypP "r_X"); (ExpP "v_relaxed2" (VarT "relaxed2"));
          (ExpP "X_0" (VarT "r_X")); (ExpP "X_1" (VarT "r_X"))]
         (VarT "r_X")
         [clause: body = IfE (VarE "ND")
                             (IdxE (ListE [VarE "X_0"; VarE "X_1"] : IterT (VarT "r_X") List)
                                   (CallE "proj_relaxed2_0" [ExpA (VarE "v_relaxed2")]))
                             (IdxE (ListE [VarE "X_0"; VarE "X_1"] : IterT (VarT "r_X") List)
                                   (NumE 0))])

     Goal Lean signature (the [Inhabited r_X] binder being generated):
       def fun_relaxed2 (v_relaxed2 : relaxed2) (r_X : Type) [Inhabited r_X]
           (X_0 : r_X) (X_1 : r_X) : r_X :=
         if ND then ([X_0, X_1])[proj_relaxed2_0 v_relaxed2]! else ([X_0, X_1])[0]! *)

(* Flatten `RecD` (`mutual`) groups into a flat list of their member defs, in
   order, dropping the RecD wrapper. Most gather_* analyses below only care
   about facts local to each individual def (a TypD's shape, a HintD's
   target, ...) and not about which defs share a mutual block with which --
   walking `flatten_defs il` instead of `il` removes the need to hand-roll
   "and also recurse into RecD" in each of them.
   Analyses that DO care about grouping (e.g. gather_relation_case_groups,
   which needs to know which RelD's are bundled together in the same
   `mutual` block) work directly on `il` instead and do not use this. *)
let rec flatten_defs (il : script) : Il.Ast.def list =
  List.concat_map (fun (d : Il.Ast.def) -> match d.it with
    | RecD defs -> flatten_defs defs
    | _ -> [d]
  ) il

(* Iterate over every DecD in the script (including inside RecD groups), applying f
   to each and returning one (name, result) pair per function.
   e.g. map_over_decs il (fun _id params _ _ -> params)
     → [("setminus1_", [TypP "X"; ExpP "X_0" (VarT "X"); ...]); ...] *)
let map_over_decs
    (il : script)                                                              (* e.g. all top-level defs of the Wasm spec *)
    (f : Il.Ast.id -> Il.Ast.param list -> Il.Ast.typ -> Il.Ast.clause list -> 'a)
    : (string * 'a) list =                                                     (* e.g. [("setminus1_", [TypP "X"; ...]); ...] *)
  List.filter_map (fun (def : Il.Ast.def) -> match def.it with
    | DecD (id, params, typ, clauses) -> Some (id.it, f id params typ clauses)
    | _ -> None
  ) (flatten_defs il)

(* Iterate over every RelD in the script (including inside RecD groups), applying f
   to each and returning one (name, result) pair per relation.
   e.g. map_over_rels il (fun _id params _ _ rules -> rules)
     → [("fun_disjoint_", [rule1; ...]); ...]
   Kept separate from map_over_decs rather than generalising that combinator itself:
   several other callers in this file (gather_defs_needing_catchall,
   gather_defs_with_unconvertible_params, gather_defs_passed_as_higher_order_args)
   are intentionally DecD-only by design -- see the "Risk/edge cases" note near
   analyze_typp_needs's own callers. *)
let map_over_rels
    (il : script)
    (f : Il.Ast.id -> Il.Ast.param list -> Il.Ast.mixop -> Il.Ast.typ -> Il.Ast.rule list -> 'a)
    : (string * 'a) list =
  List.filter_map (fun (def : Il.Ast.def) -> match def.it with
    | RelD (id, params, mixop, typ, rules) -> Some (id.it, f id params mixop typ rules)
    | _ -> None
  ) (flatten_defs il)

(* Core infrastructure: two-phase TypP-need analysis.

   Determines, for every DecD, which of its TypP names require a given typeclass
   instance (e.g. [BEq X] or [Inhabited X]).

   Phase 1 — direct: walk each function body with the caller-supplied `detect` callback.
             `detect ~typp_names e` returns the TypP names triggered by expression e.
   Phase 2 — fixpoint: propagate through CallE. If callee needs [TC X_k] for its k-th TypP
             and the caller passes its own abstract VarT "Yi" as that argument, the caller
             also needs [TC Yi]. Repeat until stable.

   Result: function-name → list-of-TypP-names-needing-the-typeclass.
   Functions with no TypP parameters or no detected needs are absent.
     BEq:       [("setminus1_", ["X"]); ("setminus_", ["X"])]
     Inhabited: [("fun_relaxed2", ["r_X"]); ("fun_relaxed4", ["r_X"])] *)
let analyze_typp_needs
    (il : script)                                                              (* e.g. all top-level defs of the Wasm spec *)
    ~(detect : typp_names:string list -> exp -> string list)                   (* e.g. for BEq: given ["X"] and CmpE `EqOp _ (VarE "w" : VarT "X") _, returns ["X"] *)
    : (string * string list) list =                                            (* e.g. [("setminus1_", ["X"]); ("setminus_", ["X"])] *)

  (* Extract TypP names from a param list.
     [TypP "X"; ExpP "X_0" (VarT "X"); ...] → ["X"]  |  [ExpP "v_state" (VarT "state")] → [] *)
  let typp_names_of (params : Il.Ast.param list) : string list =              (* e.g. [TypP "X"; ExpP "X_0" ...] → ["X"] *)
    List.filter_map (fun p -> match p.it with
      | TypP id -> Some id.it
      | _ -> None) params
  in

  (* A generic function's body, whichever kind of def it came from -- lets phase 1
     and phase 2 walk a DecD's clauses or a RelD's rules through one shared code
     path below, instead of duplicating both phases per def-kind. Scoped to this
     function only (via `let open struct ... end`), since nothing else in the
     file needs to distinguish the two. *)
  let open struct
    type def_body =
      | ClauseBody of Il.Ast.clause list
      | RuleBody of Il.Ast.rule list
  end in
  let (collect_body : string list Il.Walk.collector -> def_body -> string list) =
    fun c body -> match body with
      | ClauseBody clauses -> List.concat_map (Il.Walk.collect_clause c) clauses
      | RuleBody rules -> List.concat_map (Il.Walk.collect_rule c) rules
  in

  (* Collect (name, params, body) for every DecD *and* RelD once.
     Used in both phases to avoid re-walking the script on every fixpoint iteration.
     DecD/RelD names never collide -- deftorel.ml converts a given def from one
     kind to the other wholesale, never both under the same name in the final IL --
     so @-concatenating the two maps is safe.
     e.g. [("setminus1_", ([TypP "X"; ...], ClauseBody [clause1; clause2]));
           ("fun_disjoint_", ([TypP "X"; ...], RuleBody [rule1; ...])); ...] *)
  let decs : (string * (Il.Ast.param list * def_body)) list =
    map_over_decs il (fun _id params _typ clauses -> (params, ClauseBody clauses))
    @ map_over_rels il (fun _id params _mixop _typ rules -> (params, RuleBody rules))
  in

  (* Phase 0: derive callee-name → param-list map from decs for positional type-arg matching
     in phase 2. When we see CallE "setminus1_" [TypA (VarT "X"); ...], this lets us look up
     setminus1_'s TypP list ["X"] to match argument positions to TypP names -- now also
     covering RelD callees reached via a RulePr premise (e.g. "fun_setminus1_").
     e.g. [("setminus1_", [TypP "X"; ...]); ("fun_disjoint_", [TypP "X"; ...]); ...] *)
  let params_map : (string * Il.Ast.param list) list =                        (* e.g. [("setminus1_", [TypP "X"; ...]); ...] *)
    List.map (fun (name, (params, _)) -> (name, params)) decs
  in

  (* Phase 1 collector: wrap `detect` in the Walk.collector interface.
     `detect ~typp_names e` is the caller-supplied pattern.
     `true` means: always recurse into sub-expressions.
     e.g. for BEq with typp_names=["X"] and e = CmpE `EqOp _ (VarE "w" : VarT "X") _:
       detect fires → (["X"], true)  (keep walking children) *)
  let make_direct_collector
      (typp_names : string list)                                               (* e.g. ["X"] — TypP names in scope for this function *)
      : string list Il.Walk.collector =                                        (* e.g. collector that returns ["X"] on CmpE over VarT "X" *)
    { (Il.Walk.base_collector [] (@)) with
      collect_exp = fun e -> (detect ~typp_names e, true) }
  in

  (* Phase 1: run the direct collector over every function's clauses.
     Produces the initial map of functions with directly detected needs.
     BEq:
       setminus1_: clause2 body has CmpE (VarE "w" : VarT "X") _ → ["X"]   retained
       setminus_:  clause2 body has only CallE                   → []        filtered out
       initial_map = [("setminus1_", ["X"])]
     Inhabited:
       fun_relaxed2: body has IdxE (ListE ... : IterT (VarT "r_X") List) → ["r_X"] retained
       fun_relaxed4: same pattern                                          → ["r_X"] retained
       initial_map = [("fun_relaxed2", ["r_X"]); ("fun_relaxed4", ["r_X"])] *)
  let initial_map : (string * string list) list =                             (* e.g. [("setminus1_", ["X"])] for BEq — functions with directly detected needs *)
    List.filter_map (fun (name, (params, body)) ->
      let typp_names : string list = typp_names_of params in                 (* e.g. ["X"] for setminus1_, [] for local_ *)
      if typp_names = [] then None                                            (* no type params → nothing to detect *)
      else
        let c : string list Il.Walk.collector = make_direct_collector typp_names in
        let found : string list =
          collect_body c body
          |> List.sort_uniq String.compare
        in                                                                    (* e.g. ["X"] for setminus1_, [] for setminus_ *)
        if found = [] then None else Some (name, found)
    ) decs
  in

  (* Phase 2 propagation logic, shared by two different call sites: a `CallE`
     (an ordinary function calling another) and a `RulePr` (a relation's rule
     invoking another relation as a premise). Per deftorel.ml's
     create_fun_prem/cvt_def_to_rel, a RulePr's args are the order-preserving
     non-ExpA subsequence of the original call's args, so they align
     positionally with the callee's own params exactly like a CallE's TypA
     args align to a DecD's TypP params -- the exact same matching logic
     applies unchanged to both.

     For CallE("setminus1_", [TypA (VarT "X"); ExpA (VarE "w_1"); ExpA (VarE "lst")])
     (or, equally, a RulePr premise invoking a RelD callee the same way):
       callee_typps = ["X"]          (setminus1_'s TypP list from params_map)
       type_args    = [VarT "X"]     (TypA entries from args, positionally matching callee_typps)
       callee_needs = ["X"]          (setminus1_ needs [BEq X])
       List.combine → [("X", VarT "X")]
       "X" ∈ callee_needs, "X" ∈ typp_names ["X"] of caller (setminus_) → caller gains "X"
       Lean effect: [BEq X] is added to setminus_'s signature

     The `None` branches express "no propagation needed" — two valid cases:
       type_arg is not VarT (e.g. Nat, IterT ...): the concrete type has a globally available
         instance, which Lean's typeclass search resolves automatically. No constraint on caller.
       type_arg = VarT(xi,[]) but xi ∉ typp_names: xi is a globally defined concrete type name,
         not the caller's abstract TypP. Again resolved globally by Lean. No constraint on caller.
     We only propagate (Some xi) when the caller is forwarding its own abstract TypP xi,
     because only then does the caller lack a concrete instance in scope. *)
  let propagate_callee
      (typp_names : string list)                                               (* e.g. ["X"] — TypP names in scope for the caller being analysed *)
      (needs_map : (string * string list) list)                                (* e.g. [("setminus1_", ["X"])] — currently known needs, grows each fixpoint step *)
      (callee_name : string)                                                    (* e.g. "setminus1_" *)
      (args : Il.Ast.arg list)                                                  (* e.g. [TypA (VarT "X"); ExpA (VarE "w_1"); ...] *)
      : string list =
    match List.assoc_opt callee_name params_map with
    | None -> []                                                    (* callee not a DecD/RelD we know about, e.g. a built-in *)
    | Some callee_params ->
        let callee_typps : string list = typp_names_of callee_params in  (* e.g. ["X"] for setminus1_ *)
        (* TypA entries from the call site, positionally matching callee_typps:
           [TypA (VarT "X"); ExpA (VarE "w_1"); ...] → [VarT "X"] *)
        let type_args : Il.Ast.typ list =
          List.filter_map (fun a -> match a.it with
            | TypA t -> Some t | _ -> None) args
        in
        let callee_needs : string list =                            (* e.g. ["X"] for setminus1_ *)
          List.assoc_opt callee_name needs_map |> Option.value ~default:[]
        in
        (* pair each callee TypP with the corresponding type argument positionally;
           equal length by IL well-formedness (each TypA matches exactly one TypP) *)
        List.combine callee_typps type_args
        |> List.filter_map (fun (callee_typp, type_arg) ->
          if not (List.mem callee_typp callee_needs) then None      (* callee doesn't need [TC] for this TypP slot *)
          else match type_arg.it with
            | VarT (xi, []) when List.mem xi.it typp_names ->
                (* Caller forwards its own abstract TypP xi (e.g. VarT "X" where "X" ∈ typp_names).
                   Lean has no concrete instance for xi in scope → must constrain the caller. *)
                Some xi.it                                          (* e.g. Some "X" → setminus_ gains [BEq X] *)
            | VarT (_, []) ->
                (* type_arg is a VarT but not one of the caller's own TypP names.
                   Scenario 2: xi names a globally defined concrete type (e.g. VarT "Nat").
                   Lean's global typeclass search resolves [TC Nat] automatically.
                   No constraint on the caller is needed. *)
                None
            | _ ->
                (* type_arg is not a bare VarT — it's a concrete compound type (e.g. IterT, BoolT, NumT).
                   Scenario 1: the callee is instantiated at a concrete type.
                   Lean's global typeclass search resolves [TC <concrete>] automatically.
                   No constraint on the caller is needed. *)
                None)
  in

  (* Phase 2 collector: propagate needs through both CallE edges (ordinary
     function calls) and RulePr edges (a relation's rule invoking another
     relation as a premise) using the shared logic above. Both hooks return
     `(found, true)` so traversal continues into any nested sub-expressions
     or sub-premises (e.g. a RulePr wrapped in NegPr/IterPr for spectec's
     `-- otherwise` clauses) -- collect_prem's own NegPr/IterPr cases
     re-invoke this hook on the unwrapped RulePr. *)
  let make_propagation_collector
      (typp_names : string list)                                               (* e.g. ["X"] — TypP names in scope for the caller being analysed *)
      (needs_map : (string * string list) list)                                (* e.g. [("setminus1_", ["X"])] — currently known needs, grows each fixpoint step *)
      : string list Il.Walk.collector =                                        (* e.g. collector that returns ["X"] when caller calls setminus1_ with TypA (VarT "X") *)
    { (Il.Walk.base_collector [] (@)) with
      collect_exp = (fun e ->
        let found = match e.it with
          | CallE (callee_id, args) -> propagate_callee typp_names needs_map callee_id.it args
          | _ -> []
        in (found, true));
      collect_prem = (fun p ->
        let found = match p.it with
          | RulePr (callee_id, args, _mixop, _exp) ->
              propagate_callee typp_names needs_map callee_id.it args
          | _ -> []
        in (found, true));
    }
  in

  (* One fixpoint step: walk every function, propagating CallE-based needs into acc.
     Uses fold_left so that when a function gains a new need mid-pass, the updated
     needs_map is immediately visible to functions processed later in the same pass —
     this converges in fewer passes than computing all updates from the old state first.

     BEq iteration 1 (acc = [("setminus1_", ["X"])]):
       "setminus1_": calls itself → callee_needs=["X"], type_arg=VarT "X",
                     current=["X"] already → additions=[] → no change
       "setminus_":  calls setminus1_ → new_needs=["X"], current=[] → additions=["X"]
                     acc updated → [("setminus1_", ["X"]); ("setminus_", ["X"])], any_changed=true
     BEq iteration 2:
       "setminus_": calls setminus_ → callee_needs=["X"], current=["X"] → additions=[]
       any_changed=false → fixpoint done *)
  let one_step
      (needs_map : (string * string list) list)                               (* e.g. [("setminus1_", ["X"])] at start of iteration 1 *)
      : (string * string list) list * bool =                                  (* e.g. ([("setminus1_", ["X"]); ("setminus_", ["X"])], true) after iteration 1 *)
    List.fold_left (fun (acc, any_changed) (name, (params, body)) ->
      let typp_names : string list = typp_names_of params in                 (* e.g. ["X"] for setminus_ *)
      if typp_names = [] then (acc, any_changed)
      else
        let c : string list Il.Walk.collector = make_propagation_collector typp_names acc in
        let new_needs : string list =
          collect_body c body
          |> List.sort_uniq String.compare
        in                                                                    (* e.g. ["X"] for setminus_ in iteration 1 *)
        let current : string list = List.assoc_opt name acc |> Option.value ~default:[] in  (* e.g. [] for setminus_ before update *)
        let additions : string list =
          List.filter (fun x -> not (List.mem x current)) new_needs
        in                                                                    (* e.g. ["X"] for setminus_ — newly discovered *)
        if additions = [] then (acc, any_changed)
        else
          let merged : string list = List.sort_uniq String.compare (current @ additions) in  (* e.g. ["X"] *)
          let updated : (string * string list) list =
            if List.mem_assoc name acc then
              List.map (fun (n, ns) -> if n = name then (n, merged) else (n, ns)) acc
            else
              (name, merged) :: acc                                           (* e.g. acc with ("setminus_", ["X"]) appended *)
          in
          (updated, true)
    ) (needs_map, false) decs
  in

  (* Repeat one_step until no function gains new needs.
     Terminates because each step either adds entries (finite domain) or returns false. *)
  let rec fixpoint
      (needs_map : (string * string list) list)                               (* e.g. [("setminus1_", ["X"])] → stabilises to [("setminus1_", ["X"]); ("setminus_", ["X"])] *)
      : (string * string list) list =                                         (* e.g. [("setminus1_", ["X"]); ("setminus_", ["X"])] for BEq *)
    match one_step needs_map with
    | (map', true)  -> fixpoint map'
    | (map', false) -> map'
  in

  fixpoint initial_map

(* Compute which DecD functions need [BEq X] for each TypP "X".
   Fires on MemE and CmpE(EqOp|NeOp) where the compared/searched element has type VarT "Xi".
   e.g. setminus1_ clause2: CmpE `EqOp _ (VarE "w" : VarT "X") _ → needs BEq for "X"
   Result: [("setminus1_", ["X"]); ("setminus_", ["X"])]
   These become [BEq X] instance binders in the generated Lean signatures. *)
let gather_defs_needing_beq (il : script) : (string * string list) list =
  analyze_typp_needs il ~detect:(fun ~typp_names e ->
    match e.it with
    | MemE (e1, _)
    | CmpE (`EqOp, _, e1, _)
    | CmpE (`NeOp, _, e1, _) ->
        (* e1 has type VarT "Xi" ∈ typp_names: comparing an abstract-typed value needs [BEq Xi]
           e.g. e1 = VarE "w" : VarT "X",  typp_names = ["X"]  → ["X"]
           Lean: [BEq X] inserted after (X : Type) in the generated signature *)
        (match e1.note.it with
        | VarT (id, []) when List.mem id.it typp_names -> [id.it]
        | _ -> [])
    | _ -> [])

(* Compute which DecD functions need [Inhabited X] for each TypP "X".
   Fires on IdxE(list_e, _) when list_e's element type is a TypP VarT.
   e.g. fun_relaxed2: IdxE(ListE [X_0;X_1] : IterT(VarT "r_X",List), i)
     → list_e.note = IterT(VarT "r_X", List), "r_X" ∈ typp_names → needs Inhabited for "r_X"
   Needed because [i]! (List.get!) returns `default` via Inhabited when the index is out of bounds.
   Result: [("fun_relaxed2", ["r_X"]); ("fun_relaxed4", ["r_X"])]
   These become [Inhabited r_X] instance binders in the generated Lean signatures. *)
let gather_defs_needing_inhabited (il : script) : (string * string list) list =
  analyze_typp_needs il ~detect:(fun ~typp_names e ->
    match e.it with
    | IdxE (list_e, _) ->
        (* list_e has type IterT(VarT "Xi", _) ∈ typp_names: indexing an abstract-typed list needs [Inhabited Xi]
           e.g. list_e : IterT(VarT "r_X", List),  typp_names = ["r_X"]  → ["r_X"]
           Lean: [Inhabited r_X] inserted after (r_X : Type) in the generated signature *)
        (match list_e.note.it with
        | IterT ({it = VarT (id, []); _}, _) when List.mem id.it typp_names -> [id.it]
        | _ -> [])
    | _ -> [])

(* Collect the names of all IL types defined as inductive (VariantT).
   These become Lean `inductive` types with namespaced constructors, e.g. externtype.GLOBAL.
   AliasT (abbrev) and StructT (structure) types are excluded.
   Recurses into RecD groups to handle mutually recursive types like instr/admininstr.
   e.g. TypD("addrtype", _, [InstD(_, _, VariantT _)]) → "addrtype" *)
let gather_variant_type_names (il : script) : string list =
  List.filter_map (fun (def : Il.Ast.def) -> match def.it with
    | TypD (id, _, [{it = InstD (_, _, {it = VariantT _; _}); _}]) -> Some id.it   (* e.g. "addrtype" → "addrtype" *)
    | _ -> None
  ) (flatten_defs il)

(* Build a map (alias_name → underlying_variant_name) for non-parametric type
   aliases that transitively resolve to a VariantT type.

   Running example — Wasm 3.0 has:
     inductive addrtype where | I32 | I64   (* VariantT → in variant_names *)
     abbrev Inn : Type := addrtype           (* AliasT   → NOT in variant_names *)

   Without this map, a CaseE with note VarT("Inn",[]) falls through to LeadingDot
   and emits .I32 — ambiguous when Lean can't infer the list element type from
   List.length alone.  With the map, "Inn" resolves to "addrtype" and we emit
   the unambiguous addrtype.I32.

   Parametric aliases (e.g. `type list X := X*`) are deliberately excluded:
   their underlying VarT carries non-empty args (e.g. VarT("List",[VarT "X"])),
   so they never match VarT(_, []) and are skipped. The ambiguity problem only
   arises for zero-arg aliases used as bare constructor sources. *)
let gather_alias_to_variant_map
    (il : script)                      (* full IL script *)
    (variant_names : string list)      (* e.g. ["addrtype"; "numtype"; ...] *)
    : (string * string) list =         (* e.g. [("Inn","addrtype"); ("Fnn","numtype")] *)
  (* Step 1: collect every non-parametric alias X → Y as a flat list.
     TypD("Inn", _, [InstD(_, _, AliasT(VarT("addrtype", [])))])
       → Some ("Inn", "addrtype")
     TypD("list", _, [InstD(_, _, AliasT(VarT("List", [VarT "X"])))])
       → None  (args non-empty, excluded) *)
  let raw_aliases : (string * string) list =
    List.filter_map (fun (def : Il.Ast.def) ->
      match def.it with
      | TypD (alias_id, _,
              [{it = InstD (_, _, {it = AliasT {it = VarT (underlying_id, []); _}; _}); _}]) ->
          (* alias_id.it = "Inn", underlying_id.it = "addrtype" *)
          Some (alias_id.it, underlying_id.it)
      | _ -> None
    ) il
  in
  (* Step 2: transitively resolve X → ... → variant, guarding against cycles.
     resolve "Inn" [] :
       "Inn" ∉ visited, ∉ variant_names
       raw_aliases has "Inn" → "addrtype"
       resolve "addrtype" ["Inn"] :
         "addrtype" ∈ variant_names → Some "addrtype"
       → Some "addrtype"
     resolve "Zzz" [] where Zzz has no alias entry → None (not added to map) *)
  let rec resolve (name : string) (visited : string list) : string option =
    if List.mem name visited then None               (* cycle guard *)
    else if List.mem name variant_names then Some name   (* reached a variant root *)
    else match List.assoc_opt name raw_aliases with
      | Some underlying -> resolve underlying (name :: visited)   (* follow the chain *)
      | None -> None    (* dead end: not a variant and not aliased further *)
  in
  (* Step 3: for each alias, attempt full resolution; keep only those that reach a variant.
     ("Inn", "addrtype") → resolve "Inn" [] = Some "addrtype" → keep ("Inn", "addrtype")
     ("u32", "uN") where uN is StructT → resolve "u32" [] = None → drop *)
  List.filter_map (fun (alias_name : string) ->
    match resolve alias_name [] with
    | Some variant_name -> Some (alias_name, variant_name)   (* e.g. ("Inn","addrtype") *)
    | None -> None
  ) (List.map fst raw_aliases)

(* Collect the names of all IL types that were originally type families.
   The type-family-removal pass annotates each flattened type with
   HintD(TypH(id, [type_family_hint])). After flattening, functions that
   pattern-match on these types are genuinely partial in Lean because
   cross-product constructor combinations exist syntactically but were
   impossible in the original dependent type.
   e.g. "num_", "lane_" → were type families → lpacknum_ needs a catch-all. *)
let gather_type_family_type_names (il : script) : string list =
  let hint_id = Middlend.Typefamilyremoval.type_family_hint_id in
  List.filter_map (fun (def : Il.Ast.def) -> match def.it with
    | HintD { it = TypH (id, hints); _ }
      when List.exists (fun h -> h.hintid.it = hint_id) hints -> Some id.it
    | _ -> None
  ) (flatten_defs il)

(* Collect names of functions generated by the type-family-removal pass as projections.
   These functions already have a complete pattern match (either the exact constructor arm
   or | _ => none for multi-instance families; just the constructor arm for single-instance
   families where the type is inhabited by exactly one constructor). Adding another catch-all
   arm would produce duplicate wildcards and a Lean error.
   e.g. "proj_cvtop___2", "proj_vtestop__0" *)
let gather_projection_func_names (il : script) : string list =
  let hint_id = Middlend.Typefamilyremoval.projection_hint_id in
  List.filter_map (fun (def : Il.Ast.def) -> match def.it with
    | HintD { it = DecH (id, hints); _ }
      when List.exists (fun h -> h.hintid.it = hint_id) hints -> Some id.it
    | _ -> None
  ) (flatten_defs il)

(* Compute which DecD functions need a `| _ => Inhabited.default` catch-all arm.
   After type-family flattening, a function that pattern-matches on a formerly-indexed
   type argument has syntactically valid but semantically impossible constructor
   combinations — Lean's exhaustiveness checker rejects the definition.
   Mirrors the Rocq backend's `has_typ_fam` heuristic: add a catch-all when the function
   has more than one param and at least one ExpP param has a type-family type
   (directly, under IterT, or as a component of a TupT tuple type).
   NOTE: fvternop_-style genuine partiality (functions defined only for a subset of
   constructors of a NON-type-family type) is not handled here; that is a separate issue. *)
let gather_defs_needing_catchall
    (il : script)
    ~(proj_names : string list)
    : string list =
  let tf_names = gather_type_family_type_names il in
  if tf_names = [] then []
  else begin
    (* Matches Rocq's is_type_family: VarT in tf_set, IterT, or TupT containing one *)
    let rec is_tf_typ (t : Il.Ast.typ) =
      match t.it with
      | VarT (id, _) -> List.mem id.it tf_names
      | IterT (t', _) -> is_tf_typ t'
      | TupT xts -> List.exists (fun (_, t') -> is_tf_typ t') xts
      | _ -> false
    in
    (* Mirrors backend.ml's is_deconstruction *)
    let is_decon (arg : Il.Ast.arg) =
      match arg.it with
      | ExpA {it = VarE _; _} | TypA {it = VarT _; _} | DefA _ -> false
      | ExpA _ | TypA _ -> true
      | _ -> false
    in
    let check (name : string) (params : Il.Ast.param list) (clauses : Il.Ast.clause list) =
      (* (c) skip projection functions generated by the type-family-removal pass *)
      if List.mem name proj_names then false
      (* Rocq: requires > 1 param and at least one ExpP has a type-family type *)
      else if List.length params <= 1 then false
      else if not (List.exists (fun p ->
          match p.it with ExpP (_, t) -> is_tf_typ t | _ -> false) params)
        then false
      else begin
        let n = List.length params in
        (* (b) which param positions are ever destructured across all clauses *)
        let ever_decon =
          List.fold_left (fun acc clause ->
            let DefD (_, args, _, _) = clause.it in
            List.map2 (||) acc (List.map is_decon args)
          ) (List.init n (fun _ -> false)) clauses
        in
        if not (List.exists Fun.id ever_decon) then false
        else begin
          (* (d) is the last clause already an all-pass-through wildcard arm? *)
          match List.rev clauses with
          | [] -> false
          | last :: _ ->
            let DefD (_, last_args, _, _) = last.it in
            let last_is_catchall =
              List.for_all2 (fun decon arg -> not decon || not (is_decon arg))
                ever_decon last_args
            in
            not last_is_catchall
        end
      end
    in
    map_over_decs il (fun id params _typ clauses -> check id.it params clauses)
    |> List.filter_map (fun (name, needs) -> if needs then Some name else None)
  end

(* Collect all IL type names that need a Lean `Append` instance.
   A type X needs Append when the IL uses CompE (++) with an X-typed operand.
   e.g. CompE(e1 : VarT "store", e2 : VarT "store") → "store" needs Append *)
let gather_types_that_need_append_instances (il : script) : string list =
  let collected = ref [] in
  let module Visitor = Il.Iter.Make(
    struct
      include Il.Iter.Skip
      let visit_exp e =
        match e.it with
        | CompE (e1, e2) ->
          if e1.note.it <> e2.note.it then
            failwith "CompE types don't match!"
          else
            (match e1.note.it with
            | VarT (id, []) -> collected := id.it :: !collected   (* e.g. "store" *)
            | _ -> ())
        | _ -> ()
    end
  )
  in
  List.iter Visitor.def il;
  List.sort_uniq String.compare !collected

(* Collect, for each `mutual` block (RecD group) in the script, the case/rule
   id of every RelD relation bundled inside it. Standalone RelDs (not inside a
   RecD) form their own singleton group, since they can never collide with
   anything else in the same Lean `mutual` block.
   e.g. `mutual Instr_ok ... Instrs_ok ... end` with Instr_ok's rules named
   [...; "frame"; ...] and Instrs_ok's rules named [...; "frame"; ...]
     → one group: [("Instr_ok", [...; "frame"; ...]); ("Instrs_ok", [...; "frame"; ...])] *)
let gather_relation_case_groups (il : script) : (string * string list) list list =
  let relation_cases (id : id) (rules : rule list) : string * string list =
    (id.it, List.map (fun (r : rule) -> let RuleD (rid, _, _, _, _) = r.it in rid.it) rules)
  in
  let collect def : (string * string list) list list =
    match def.it with
    | RelD (id, _, _, _, rules) -> [[relation_cases id rules]]
    | RecD defs ->
        let group = List.concat_map (fun d -> match d.it with
          | RelD (id, _, _, _, rules) -> [relation_cases id rules]
          | _ -> []
        ) defs in
        (* Non-RelD members of this RecD (types, defs, ...) contribute no
           relation cases here but may still share the block; their own
           constructor names are not covered by this analysis (see NOTE
           on the field below). *)
        if group = [] then [] else [group]
    | _ -> []
  in
  List.concat_map collect il

(* For each RelD relation, the subset of its own rule-case ids that collide
   with a same-named case in ANOTHER RelD bundled in the same `mutual` block
   (RecD group). Keyed by relation id -- NOT a flat name set -- because
   collision is a per-group property: "frame" colliding inside the
   Instr_ok2/Instrs_ok2 group must not cause Instrs_ok's unrelated "frame"
   case (a different, non-overlapping mutual group with no internal "frame"
   collision) to be renamed too. A flat set would conflate the two groups and
   make Instrs_ok's naming depend on an edit to Instr_ok2/Instrs_ok2 elsewhere
   in the script -- exactly the kind of action-at-a-distance fragility this
   analysis exists to avoid.

   These are exactly the names that trigger the Lean `induction ... using`
   bug documented in test-lean/bug.lean: `getAltNumFields` resolves
   alternative names by an unqualified, first-match linear search over every
   constructor in the whole mutual group, so a same-named case in a sibling
   relation silently shadows this one and `introN` is asked for the wrong
   number of binders.
   e.g. Instr_ok2 and Instrs_ok2 both have a rule case named "frame"
     → [("Instr_ok2", ["frame"]); ("Instrs_ok2", ["frame"])] is in the result,
       so backend.ml prepends each relation's own name to that one case only,
       leaving every non-colliding case (the vast majority, including
       already-prefixed auto-derived ones like "fun_sum_case_1") untouched.
   NOTE: this only tracks RelD rule-case names. A VariantT datatype's plain
   constructors (built in create_typcase) bundled in the same mutual block are
   not included, so a clash between a rule case and a datatype constructor --
   or between two datatype constructors -- would not be caught here. Extending
   coverage to those would mean gathering their names the same way inside
   gather_relation_case_groups and merging them into the same per-group name
   list before the collision count below. *)
let gather_colliding_relation_case_names (il : script) : (string * string list) list =
  let groups = gather_relation_case_groups il in
  List.concat_map (fun (group : (string * string list) list) ->
    let all_case_names = List.concat_map snd group in
    let counts = Hashtbl.create 16 in
    List.iter (fun n ->
      Hashtbl.replace counts n (1 + (try Hashtbl.find counts n with Not_found -> 0))
    ) all_case_names;
    List.filter_map (fun (rel_id, case_names) ->
      let colliding = List.filter (fun n -> Hashtbl.find counts n > 1) case_names in
      if colliding = [] then None else Some (rel_id, colliding)
    ) group
  ) groups

(* ---- Generic hint index ------------------------------------------------

   A flat index from an IL id's name to every hint attached to it, regardless
   of which HintD variant declared it. This module is deliberately
   hint-content-agnostic: it doesn't know what "wf-lemma-rel", "mode", or any
   other hintid means, only how to find hints by the id they're attached to.
   Adding a new kind of hint anywhere in the frontend/middle-end therefore
   never requires touching this module -- only the *consumer* that wants to
   interpret a specific hintid needs to change.

   Motivating example: undep.ml generates a `*_is_wf` relation for certain
   RelD/DecD's and tags it with a `wf-lemma-rel` (or `wf-lemma-func`) hint --
   `HintD (RelH (lemma_id, [{hintid = Middlend.Undep.wf_rel_id; ...}]))` --
   to mark "this relation should be rendered as a lemma, not an inductive".
   The Rocq backend already consumes this (src/backend-rocq/print.ml's
   `wf_lemma_set` / `register_hints` / `render_wfness_func_lemma`), just via
   a hardcoded StringSet built solely for that one hint. `Hint_index` gives
   the same lookup generically: `ids_with_hint index Middlend.Undep.wf_rel_id`
   is that StringSet, and any future hint kind gets the same treatment for
   free -- no new gather_* pass needed, just a new hintid to query for.

   There's a related, narrower module already in the codebase --
   src/il/hints.ml's `build_il_hints`, consumed by undep.ml -- but it's
   purpose-built for exactly one hint ("mode") and parses it inline while
   gathering, and it doesn't recurse into RecD groups (so a mode hint on a
   relation bundled in a `mutual` block is currently missed). Generalizing
   that shared module into this same shape, with mode-parsing becoming a
   consumer of the generic index rather than baked into the gathering pass,
   would be a nice follow-up -- but it's shared infra also used directly by
   undep.ml, so it's out of scope here; this module stays Lean-backend-local
   for now. *)
module Hint_index = struct
  module StringMap = Map.Make (String)

  (* Hints in declaration order, per id. A plain list rather than a true Set:
     `hint` (Il.Ast.hint, carrying an El.Ast.exp) has no comparison function
     in this codebase, and preserving multiplicity/order matches how hints
     are already represented on a single HintD anyway. *)
  type t = hint list StringMap.t

  let empty : t = StringMap.empty

  let add_many (target_id : string) (hints : hint list) (index : t) : t =
    StringMap.update target_id (function
      | None -> Some hints
      | Some existing -> Some (existing @ hints)
    ) index

  (* Every hint attached to `target_id`, in declaration order.
     e.g. hints_of index "fadd__is_wf" → [{hintid = "wf-lemma-rel"; ...}] *)
  let hints_of (index : t) (target_id : string) : hint list =
    StringMap.find_opt target_id index |> Option.value ~default:[]

  let get_hint (index : t) ~(hint_id : string) (target_id : string) : hint option =
    let hints = hints_of index target_id in
    List.find_opt (fun (h : hint) -> h.hintid.it = hint_id) hints

  (* Does `target_id` carry a hint whose hintid is exactly `hint_id`?
     e.g. has_hint index ~hint_id:Middlend.Undep.wf_rel_id "fadd__is_wf" *)
  let has_hint (index : t) ~(hint_id : string) (target_id : string) : bool =
    (* List.exists (fun (h : hint) -> h.hintid.it = hint_id) (hints_of index target_id) *)
    let h = get_hint index ~hint_id:hint_id target_id in
    Option.is_some h  

  (* Every id carrying a hint whose hintid is exactly `hint_id`. Mirrors the
     Rocq backend's `wf_lemma_set` pattern generically: that set is exactly
     `ids_with_hint index Middlend.Undep.wf_rel_id
        @ ids_with_hint index Middlend.Undep.wf_func_id`. *)
  let ids_with_hint (index : t) (hint_id : string) : string list =
    StringMap.fold (fun id hints acc ->
      if List.exists (fun (h : hint) -> h.hintid.it = hint_id) hints
      then id :: acc else acc
    ) index []
    |> List.sort_uniq String.compare
end

(* Index every HintD in the script (including inside RecD groups) by the id
   it was declared against.
   - TypH/RelH/DecH/GramH each attach hints to a single id directly, so they
     index straightforwardly.
   - RuleH (rel_id, rule_id, hints) attaches hints to one specific rule of a
     relation; it's indexed by the RULE's id, since that's the id a caller
     actually has in hand when looking at e.g. an `_inductive_case`. NOTE:
     rule-case ids are only guaranteed unique *within* a relation's own
     mutual block (see gather_colliding_relation_case_names above) -- two
     different relations in different, unrelated mutual blocks can have a
     same-named rule. A caller that needs to disambiguate a RuleH hint in
     that situation should cross-reference that analysis; this index alone
     cannot tell the two apart. *)
let gather_hints (il : script) : Hint_index.t =
  List.fold_left (fun index (def : Il.Ast.def) -> match def.it with
    | HintD { it = TypH (id, hints); _ }
    | HintD { it = RelH (id, hints); _ }
    | HintD { it = DecH (id, hints); _ }
    | HintD { it = GramH (id, hints); _ } ->
      Hint_index.add_many id.it hints index
    | HintD { it = RuleH (_rel_id, rule_id, hints); _ } ->
      Hint_index.add_many rule_id.it hints index
    | _ -> index
  ) Hint_index.empty (flatten_defs il)

(* ---- Deriving-clause classification -------------------------------------

   Determines, for every top-level VariantT/StructT/RelD id in the script,
   which "deriving category" it falls into -- the single fact backend.ml
   needs to decide its Lean `deriving` clause (see Backend.deriving_for_
   category). A pure, whole-script pass, like every other analysis in this
   file, rather than an incremental Hashtbl mutated during backend.ml's
   def-by-def code generation -- so its correctness no longer depends on
   backend.ml traversing `il` in a particular (dependency) order the way an
   incremental pass would.

   The underlying question, for a data type (VariantT) or structure
   (StructT), is: does Lean's stock `deriving DecidableEq`/`ReflBEq`/
   `LawfulBEq` handler actually succeed on it? Verified directly
   (test-lean/sandbox_6.lean): it fails exactly when a field nests a
   self-reference under a container (e.g. `List T`) -- confirmed identical
   for `structure` and `inductive`, byte-for-byte the same error message
   ("None of the deriving handlers for class `DecidableEq` applied to
   `<name>`") -- or when a field's type is itself such a type. That makes
   this a transitive-closure problem over the type dependency graph: a type
   is "bad" (falls back to a conservative clause) if it is itself
   self-nested, if it is a member of a genuine multi-type mutual-recursion
   group (out of scope for per-type shape analysis), or if it references
   another type that is (transitively) bad.
*)

type deriving_category =
  | RelationCategory
    (* RelD, not a wf-lemma: a Prop-valued inductive relation (e.g.
       [Instr_ok]). A Prop built from premised constructors generally has no
       default inhabitant, so this never gets [Inhabited]/[BEq] either --
       matches the Rocq backend, which never emits an eqtype/inhabitance
       proof for a RelD (see [render_relation] in backend-rocq/print.ml). *)
  | PlainDataCategory
    (* A VariantT or StructT, standalone (not part of a genuine multi-type
       mutual group), with no self-nesting, no bad-type reference, and no
       type parameters. *)
  | PolymorphicDataCategory
    (* Like [PlainDataCategory], but with a [TypP] parameter (e.g.
       [list (X : Type)]). Lean auto-threads the needed instance constraint
       (e.g. [DecidableEq X]) into the derived instance itself, so this
       behaves identically to [PlainDataCategory] today -- kept as its own
       category because the Rocq backend can't do the same (its
       [cant_do_equality] unconditionally [Admitted]s any [TypP] case),
       which is worth keeping visible even though it doesn't currently
       change [Backend.deriving_for_category]'s output. *)
  | SelfNestedDataCategory
    (* A VariantT or StructT, standalone, that nests a self-reference under
       a container (per [typ_nests_self_ref]), or that (transitively)
       references another type in this category or
       [MutualGroupDataCategory]. This is the "`deriving DecidableEq` for
       nested inductives (e.g. `instr`)" gap PR #192 flagged
       (leanprover/lean4#2329) -- the Rocq backend doesn't have this
       restriction, since its eq_dec proofs are ordinary
       structurally-recursive Fixpoints rather than a derive-handler. *)
  | MutualGroupDataCategory
    (* A VariantT or StructT that is a member of a genuine multi-type
       mutual-recursion group (an [Il.Ast.RecD], after stripping HintD
       members and wf-lemma-tagged RelD's, with more than one remaining
       member). [typ_nests_self_ref] only reasons about one type's own
       fields, not about a whole mutually-recursive family, so this is out
       of scope for per-type shape analysis and treated conservatively
       regardless of the type's own shape. *)

(* A field type "nests" a self-reference when the reference to [parent_id]
   occurs underneath some other type application (an [IterT], or a [VarT]
   with type arguments) rather than appearing bare at the top of the field.
   Type parameters are not a blocker either way -- Lean auto-threads the
   needed instance constraint (e.g. [DecidableEq X]) into the derived
   instance itself -- so this only needs to walk for nesting, not for
   polymorphism (see [PolymorphicDataCategory]). *)
let rec typ_nests_self_ref (parent_id : string) (under_wrapper : bool) (t : Il.Ast.typ) : bool
  = match t.it with
    | VarT (id, []) -> under_wrapper && id.it = parent_id
    | VarT (id, args) ->
      (under_wrapper && id.it = parent_id) ||
      List.exists (fun (a : Il.Ast.arg) -> match a.it with
        | TypA typ -> typ_nests_self_ref parent_id true typ
        | _ -> false
      ) args
    | IterT (t', _) -> typ_nests_self_ref parent_id true t'
    | TupT id_typ_list -> List.exists (fun (_, typ) -> typ_nests_self_ref parent_id under_wrapper typ) id_typ_list
    | BoolT | NumT _ | TextT -> false

(* Whether [t] references any id in [bad] -- the propagation step of the
   transitive-closure fixpoint, parameterised over the current "bad" set
   rather than a global mutable table, so it can be reused unchanged at
   every fixpoint iteration. *)
let rec typ_refs_any (bad : string list) (t : Il.Ast.typ) : bool
  = match t.it with
    | VarT (id, args) ->
      List.mem id.it bad ||
      List.exists (fun (a : Il.Ast.arg) -> match a.it with
        | TypA typ -> typ_refs_any bad typ
        | _ -> false
      ) args
    | IterT (t', _) -> typ_refs_any bad t'
    | TupT id_typ_list -> List.exists (fun (_, typ) -> typ_refs_any bad typ) id_typ_list
    | BoolT | NumT _ | TextT -> false

(* The shape of a top-level construct that participates in deriving
   classification at all -- everything else (DecD, GramD, HintD, wf-lemma-
   tagged RelD) is excluded upstream, in [shape_of_def]. Lets
   [field_typs_of_shape]/the fixpoint below treat VariantT, StructT, and
   AliasT uniformly (all three are just "a list of field types to check" --
   one, for an alias), while still letting classification branch on "is
   this even a relation" (skip field analysis entirely), "is this an alias"
   (participates in the fixpoint but never gets a `deriving` clause of its
   own, so is filtered out of the final result), vs "is this one of the two
   real data shapes". *)
type deriving_shape =
  | ShapeVariant of Il.Ast.typcase list
  | ShapeStruct of Il.Ast.typfield list
  | ShapeAlias of Il.Ast.typ
  | ShapeRelation

let field_typs_of_shape (shape : deriving_shape) : Il.Ast.typ list =
  match shape with
  | ShapeVariant ts -> List.map (fun ((_, (typ, _, _), _) : Il.Ast.typcase) -> typ) ts
  | ShapeStruct ts -> List.map (fun ((_, (typ, _, _), _) : Il.Ast.typfield) -> typ) ts
  | ShapeAlias t -> [t]
  | ShapeRelation -> []

(* Classifies a single top-level def by its raw shape (id, its own type
   params, and its VariantT/StructT/AliasT/RelD payload) -- [None] for
   anything that doesn't participate in deriving classification at all
   (DecD, GramD, HintD). Excludes wf-lemma-tagged RelD's, which render as
   standalone theorems (see Backend.WfLemmaTheoremConstruct), not as
   inductives, and so never carry a `deriving` clause of any kind.

   AliasT (abbrev) is included even though an abbrev never itself gets a
   `deriving` clause: e.g. `abbrev expr := List instr`, where `instr` is
   self-nested. A later type with a field of type `expr` (not `instr`
   directly) must still inherit the restriction -- confirmed necessary by
   `elemmode`'s `v_expr : expr` field, which only fails to derive because
   `expr` transitively reaches the already-bad `instr`. [ShapeAlias] lets
   the same field-reference fixpoint below propagate through an alias
   exactly like it does through a VariantT/StructT field, without a
   self-nesting check of its own (an abbrev can't be self-referential --
   Lean rejects a recursive plain type synonym outright -- so
   [typ_nests_self_ref] is never applied to one, matching the pre-whole-
   file-analysis version of this check). [gather_deriving_categories]
   filters [ShapeAlias] entries back out of its returned list, since no
   call site ever looks an abbrev's id up there. *)
let shape_of_def (hints : Hint_index.t) (def : Il.Ast.def) : (string * Il.Ast.quant list * deriving_shape) option
  = match def.it with
    | TypD (id, params, [{it = InstD (_, _, {it = VariantT ts; _}); _}]) ->
      Some (id.it, params, ShapeVariant ts)
    | TypD (id, params, [{it = InstD (_, _, {it = StructT ts; _}); _}]) ->
      Some (id.it, params, ShapeStruct ts)
    | TypD (id, params, [{it = InstD (_, _, {it = AliasT t; _}); _}]) ->
      Some (id.it, params, ShapeAlias t)
    | RelD (id, params, _, _, _)
      when not (Hint_index.has_hint hints ~hint_id:Middlend.Undep.wf_rel_id id.it
                || Hint_index.has_hint hints ~hint_id:Middlend.Undep.wf_func_id id.it)
      -> Some (id.it, params, ShapeRelation)
    | _ -> None

(* Every VariantT/StructT id that is a member of a genuine multi-type
   mutual-recursion group: an [Il.Ast.RecD], after stripping HintD members,
   with more than one remaining member, where every remaining member has a
   recognised [deriving_shape] (VariantT, StructT, or non-wf-lemma RelD; an
   AliasT member disqualifies the group, same as any other unrecognised
   member -- consistent with the original code, where an all-abbrev-or-def
   RecD is a wholly different mutual-group kind, [MutualDefAbbrev], never
   mixed with inductives/structures) -- if any member doesn't match, this
   isn't the homogeneous case and no member of it is treated as a
   mutual-group data type. Mirrors backend.ml's former [MutualConstruct]
   override ([create_mutual_construct]'s [is_inductive]/
   [all_inductive_or_structure] check) exactly, including counting relation
   members toward the ">1 members" threshold -- a single data type sharing
   a `mutual` block with two-or-more total members (relations included) is
   still conservative. *)
let gather_mutual_group_data_ids (il : script) (hints : Hint_index.t) : string list =
  List.concat_map (fun (def : Il.Ast.def) -> match def.it with
    | RecD defs ->
      let defs = List.filter (fun (d : Il.Ast.def) -> match d.it with HintD _ -> false | _ -> true) defs in
      let shapes = List.filter_map (shape_of_def hints) defs in
      if List.length shapes = List.length defs && List.length defs > 1 then
        List.filter_map (fun (id, _, shape) -> match shape with
          | ShapeVariant _ | ShapeStruct _ -> Some id
          | ShapeAlias _ | ShapeRelation -> None
        ) shapes
      else []
    | _ -> []
  ) il

(* Runs the full classification: seeds the "bad" set with direct
   self-nesters and mutual-group data members, then fixpoint-propagates
   badness through field references -- of a VariantT/StructT/AliasT
   referencing a bad type, itself becomes bad -- exactly reproducing the
   closure the old incremental Hashtbl-during-codegen approach computed as
   a side effect of dependency-ordered traversal, just order-independently.
   [ShapeAlias] entries participate in the fixpoint (so badness propagates
   correctly through an alias) but are filtered out of the returned list,
   since an abbrev never gets a `deriving` clause of its own. *)
let gather_deriving_categories (il : script) : (string * deriving_category) list =
  let hints = gather_hints il in
  let shapes : (string * Il.Ast.quant list * deriving_shape) list =
    List.filter_map (shape_of_def hints) (flatten_defs il)
  in
  let mutual_group_data_ids = gather_mutual_group_data_ids il hints in
  let is_self_nested (id, _, shape) =
    List.exists (typ_nests_self_ref id false) (field_typs_of_shape shape)
  in
  let initial_bad =
    List.filter_map (fun ((id, _, shape) as entry) -> match shape with
      | ShapeRelation | ShapeAlias _ -> None
      | ShapeVariant _ | ShapeStruct _ ->
        if is_self_nested entry || List.mem id mutual_group_data_ids then Some id else None
    ) shapes
    |> List.sort_uniq String.compare
  in
  let rec fixpoint (bad : string list) : string list =
    let additions = List.filter_map (fun (id, _, shape) ->
      if List.mem id bad then None
      else match shape with
        | ShapeRelation -> None
        | ShapeVariant _ | ShapeStruct _ | ShapeAlias _ ->
          if List.exists (typ_refs_any bad) (field_typs_of_shape shape) then Some id else None
    ) shapes in
    if additions = [] then bad
    else fixpoint (List.sort_uniq String.compare (bad @ additions))
  in
  let bad_set = fixpoint initial_bad in
  List.filter_map (fun (id, params, shape) ->
    let category = match shape with
      | ShapeAlias _ -> None
      | ShapeRelation -> Some RelationCategory
      | ShapeVariant _ | ShapeStruct _ ->
        Some (
          if List.mem id mutual_group_data_ids then MutualGroupDataCategory
          else if List.mem id bad_set then SelfNestedDataCategory
          else if params <> [] then PolymorphicDataCategory
          else PlainDataCategory
        )
    in
    Option.map (fun c -> (id, c)) category
  ) shapes

(* The result of the whole-script pre-pass, consumed by code generation in backend.ml.
   Computed once before code emission and stored in the `analysis` ref below. *)
type whole_script_analysis =
  {
    types_needing_append_instances : string list;
    variant_type_names : string list;
    (* Maps alias type names to the underlying VariantT name they resolve to.
       e.g. [("Inn", "addrtype"); ("Fnn", "numtype")]
       Used in CaseE to emit addrtype.I32 instead of ambiguous .I32. *)
    alias_to_variant_map : (string * string) list;
    (* Maps function names to TypP names that require [BEq X].
       e.g. [("setminus1_", ["X"]); ("setminus_", ["X"])]
       Generates [BEq X] instance binders after (X : Type) in those functions' Lean signatures. *)
    defs_needing_beq : (string * string list) list;
    (* Maps function names to TypP names that require [Inhabited X].
       e.g. [("fun_relaxed2", ["r_X"]); ("fun_relaxed4", ["r_X"])]
       Generates [Inhabited r_X] instance binders after (r_X : Type) in those functions' Lean signatures. *)
    defs_needing_inhabited : (string * string list) list;
    (* Names of functions that need `| _ => Inhabited.default` appended to their match.
       After type-family flattening, cross-product constructor combinations are syntactically
       valid but semantically impossible; this catch-all makes the match exhaustive for Lean.
       Projection functions and functions that already have a wildcard last arm are excluded.
       e.g. ["lpacknum_"; "const"; "cvtop_"] *)
    defs_needing_catchall : string list;
    (* Maps a RelD relation's own id to the subset of its rule-case ids that
       collide with a same-named case in a sibling RelD bundled in the same
       `mutual` block (see gather_colliding_relation_case_names above).
       e.g. [("Instr_ok2", ["frame"]); ("Instrs_ok2", ["frame"])] when those
       two -- and only those two -- share a "frame" case in one mutual block.
       backend.ml looks up its own relation id here and prepends the
       relation's own name only to a case whose id appears in that relation's
       own entry, to work around the Lean `induction ... using` bug in
       test-lean/bug.lean without renaming every already-unique case, and
       without letting a collision in one mutual block affect naming in an
       unrelated one. *)
    colliding_relation_case_names : (string * string list) list;
    (* Every hint in the script, indexed by the id it was declared against
       (see Hint_index / gather_hints above). Hint-content-agnostic: this
       field doesn't special-case any particular hintid, so a consumer that
       cares about one (e.g. backend.ml eventually rendering a `*_is_wf`
       relation as a lemma when it carries undep.ml's wf-lemma-rel /
       wf-lemma-func hint, mirroring the Rocq backend's `wf_lemma_set`)
       queries it directly via `Hint_index.has_hint` / `ids_with_hint`
       rather than needing a new gather_* field here. *)
    hints : Hint_index.t;
    (* Maps every top-level VariantT/StructT/RelD id to its [deriving_category]
       (see "Deriving-clause classification" above). backend.ml looks its own
       id up here and passes the result through [Backend.deriving_for_category]
       to get the actual Lean `deriving` clause -- no analysis happens at
       code-generation time any more.
       e.g. [("instr", SelfNestedDataCategory); ("Instr_ok", RelationCategory)] *)
    deriving_categories : (string * deriving_category) list;
  }

(* Run all whole-script analyses and bundle the results. *)
let analyze_whole_script (il : script) : whole_script_analysis =
  let variant_type_names : string list = gather_variant_type_names il in
  {
    types_needing_append_instances = gather_types_that_need_append_instances il;
    variant_type_names;
    alias_to_variant_map = gather_alias_to_variant_map il variant_type_names;
    defs_needing_beq = gather_defs_needing_beq il;
    defs_needing_inhabited = gather_defs_needing_inhabited il;
    deriving_categories = gather_deriving_categories il;
    defs_needing_catchall =
      (let proj_names = gather_projection_func_names il in
       gather_defs_needing_catchall il ~proj_names);
    colliding_relation_case_names = gather_colliding_relation_case_names il;
    hints = gather_hints il;
  }

(* Mutable cell holding the current script's analysis results.
   Initialised to empty values; overwritten by `analysis := analyze_whole_script il`
   before code generation begins. *)
let analysis : whole_script_analysis ref = ref {
  types_needing_append_instances = [];
  variant_type_names = [];
  alias_to_variant_map = [];
  defs_needing_beq = [];
  defs_needing_inhabited = [];
  deriving_categories = [];
  defs_needing_catchall = [];
  colliding_relation_case_names = [];
  hints = Hint_index.empty;
}
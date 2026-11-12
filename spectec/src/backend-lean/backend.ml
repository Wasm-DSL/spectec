open Il.Ast
open Util.Source
(* open Il.Walk *)
open Lean_ast
open Lean_builder
open Lean_utils
open Whole_file_analyses

let error at msg = Util.Error.error at "Lean4 translation" msg
module NonEmptyList = Util.Lib.NonEmptyList





















(* let convert_alias (id : string) () *)

let rec create_curried_func (term_chain : term list) : term
  = match term_chain with
    | [] -> failwith "create_curried_func: empty term_chain"
    | [t] -> t
    | t :: ts -> FunType (t, create_curried_func ts)

let create_numtyp (nt : Il.Ast.numtyp) : term
  = match nt with
    | `NatT -> Ident "Nat"
    | `IntT -> Ident "Int" 
    | `RatT -> Ident "Rat"   (* no stdlib Rat in Lean 4, needs import *)
    | `RealT -> Ident "Real" (* same *)


let rec create_iter_typ (iter : Il.Ast.iter) (t : typ) : term
  = match iter with
    | Opt -> FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (create_typ t)])
    | List -> FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (create_typ t)])
    | List1 -> FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (create_typ t)])
    | ListN _ -> FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (create_typ t)])

and create_typ (t : Il.Ast.typ) : term
  = match t.it with
    | VarT (id, []) -> Ident id.it
    | VarT (id, args) ->
      (* Genuine parameterised type application, e.g. list(valtype).
         TypA args are type arguments; ExpA/DefA/GramA are not valid here. *)
      let arg_terms = List.map (fun a -> match a.it with
        | TypA typ -> Term (create_typ typ)
        | _ -> error t.at ("non-TypA arg in parameterised VarT: " ^ id.it)
      ) args in
      FunApp (Ident id.it, NonEmptyList.from_list_unsafe arg_terms)
    | BoolT -> Ident "Bool"
    | NumT nt -> create_numtyp nt
    | TextT -> Ident "String"
    | TupT [] -> Ident "Unit"
    | TupT id_typ_list -> (
      let terms = List.map (fun (_, typ) -> create_typ typ) id_typ_list in
      let rec construct_prod l
        = match l with
          | [] -> failwith "should have been handled by earlier case"
          | [t] -> t
          | t :: ts -> ProdType (t, construct_prod ts)
      in
      construct_prod terms
    )
    | IterT (t, iter) -> create_iter_typ iter t

let lean_id_char c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'

(* Bracket atoms ({}, [], ()) are valid SpecTec mixop delimiters but not Lean identifiers.
   Strip them; the enclosed arguments become explicit constructor parameters instead. *)
let mixop_to_id (m : Il.Ast.mixop) : string
  = let raw = Xl.Mixop.to_string_with (Fun.const "") "" m in
    let id = String.of_seq (Seq.filter lean_id_char (String.to_seq raw)) in
    if id = "" then failwith ("mixop_to_id: empty Lean identifier from mixop \"" ^ raw ^ "\"")
    else id

let create_inductive_type_with_params_applied
  (parent_type : Il.Ast.id)
  (params : Il.Ast.quant list)
  : term
  = match params with
    | [] -> Ident parent_type.it
    | _
      when List.for_all (fun p -> match p.it with TypP _ -> true | _ -> false) params
      ->
        let args = List.map (
          fun p -> match p.it with
            | TypP t -> Term (Ident t.it)
            | _ -> failwith "all params of a typecase should be TypP"
        ) params in
        FunApp (Ident parent_type.it, NonEmptyList.from_list_unsafe args)
    | _ -> failwith "all params of a typecase should be TypP"

let standard_deriving : _deriving = {
  deriving = ["Inhabited"; "BEq"];
  derive_deceq = true;
}
let extended_eq_deriving : _deriving = {
  deriving = ["Inhabited"; "BEq"; "DecidableEq"; "ReflBEq"; "LawfulBEq"];
  derive_deceq = false;
}
let empty_deriving : _deriving = {
  deriving = [];
  derive_deceq = false;
}

(*
  The [deriving] clause for each [Whole_file_analyses.deriving_category] (see
  that type's doc comment for what each category means and why). This is the
  single place that would need to change to route a category through a
  stronger equality mechanism (e.g. test-lean/ExtendedDeriveDecEq.lean's
  [derive_deceq] command) instead of falling back to [standard_deriving].
*)
let deriving_for_category (category : deriving_category) : _deriving
  = match category with
    | RelationCategory -> empty_deriving
    | PlainDataCategory | PolymorphicDataCategory -> extended_eq_deriving
    | SelfNestedDataCategory | MutualGroupDataCategory -> standard_deriving

(*
  The precomputed [deriving_category] for [id] (see
  [Whole_file_analyses.gather_deriving_categories]), translated straight to
  its Lean `deriving` clause. Every call site that used to run its own
  self-nesting/bad-reference analysis (or, for structures, skip analysis
  entirely) now just looks its own id up here.
*)
let deriving_of_id (id : Il.Ast.id) : _deriving
  = match List.assoc_opt id.it (!analysis).deriving_categories with
    | Some category -> deriving_for_category category
    | None -> failwith ("deriving_of_id: " ^ id.it ^ " missing from whole-script deriving-category analysis")

(*
  The trailing [DeriveDeceq] command for a type or mutual group, if
  [deriving] calls for one -- [] otherwise. [names] is every candidate id
  that could stand in for the group (just the one id for a standalone type;
  every member's id for a mutual group) -- [ExtendedDeriveDecEq.lean]'s
  command only ever needs one representative name (it derives the whole
  group and warns if given more than one), currently just the first of
  [names]. Kept as a list, rather than a single pre-chosen name, so that
  choice can be revisited here later without touching call sites.
*)
(* Tracks whether [deceq_commands_for] emitted a [DeriveDeceq] command this
   run -- consulted by exe-spectec/main.ml to decide whether the generated
   file needs `import ExtendedDeriveDecEq` at its head (that syntax doesn't
   exist without it: `derive_deceq` is a command ExtendedDeriveDecEq.lean
   declares, not part of Lean's own grammar). Reset in [create_script],
   mirroring [used_prem_arities] et al. below. *)
let used_derive_deceq : bool ref = ref false

let deceq_commands_for (names : string list) (deriving : _deriving) : command list =
  if not deriving.derive_deceq then []
  else match names with
    | [] -> []
    | representative :: _ ->
      used_derive_deceq := true;
      [DeriveDeceq (NonEmptyList.from_list_unsafe [representative])]

let create_unop_bool (op : Il.Ast.unop) : term
  = match op with
    | `PlusOp -> failwith "This should never be triggered, since we want to just write a plain number. create_exp should have a special case for `PlusOp."
    | `MinusOp -> Ident "-"
    | `NotOp -> Ident "!"

(* NOTE: there is no `create_unop_prop` because the only case is `NegPr`, which
does not supply a unop type parameter. *)

let create_binop_bool (op : Il.Ast.binop) : term
  = match op with
    | `AndOp -> Ident "&&"
    | `OrOp -> Ident "||"
    | `ImplOp -> Ident "→"
    | `EquivOp -> Ident "↔"
    | `AddOp -> Ident "+"
    | `SubOp -> Ident "-"
    | `MulOp -> Ident "*"
    | `DivOp -> Ident "/"
    | `ModOp -> Ident "%"
    | `PowOp -> Ident "^"

let create_binop_prop (op : Il.Ast.binop) : term
  = match op with
    | `AndOp -> Ident "∧"
    | `OrOp -> Ident "∨"
    | `ImplOp -> Ident "→"
    | `EquivOp -> Ident "↔"
    | `AddOp -> Ident "+"
    | `SubOp -> Ident "-"
    | `MulOp -> Ident "*"
    | `DivOp -> Ident "/"
    | `ModOp -> Ident "%"
    | `PowOp -> Ident "^"

let create_cmpop_prop (op : Il.Ast.cmpop) : term
  = match op with
    | `EqOp -> Ident "="
    | `NeOp -> Ident "≠"
    | `LtOp -> Ident "<"
    | `GtOp -> Ident ">"
    | `LeOp -> Ident "≤"
    | `GeOp -> Ident "≥"

let create_cmpop_bool (op : Il.Ast.cmpop) : term
  = match op with
    | `EqOp -> Ident "=="
    | `NeOp -> Ident "!="
    | `LtOp -> Ident "<"
    | `GtOp -> Ident ">"
    | `LeOp -> Ident "≤"
    | `GeOp -> Ident "≥"

let create_optyp (t : Il.Ast.optyp) : term
  = match t with
    | `BoolT -> Ident "Bool"
    | `NatT -> Ident "Nat"
    | `IntT -> Ident "Int"
    | `RatT -> Ident "Rat"
    | `RealT -> Ident "Real"

let create_atom (a : Il.Ast.atom) : string
  = match a.it with
    | Atom s -> s
    | _ -> failwith "expected Atom"


type path_seg =
  | DotSeg of Il.Ast.atom
  | IdxSeg of Il.Ast.exp
  | SliceSeg of Il.Ast.exp * Il.Ast.exp


let subscript_of_int (n : int) : string =
  let sub_digit = function
    | '0' -> "₀" | '1' -> "₁" | '2' -> "₂" | '3' -> "₃" | '4' -> "₄"
    | '5' -> "₅" | '6' -> "₆" | '7' -> "₇" | '8' -> "₈" | '9' -> "₉"
    | c   -> String.make 1 c
  in
  String.concat "" (List.map sub_digit (List.of_seq (String.to_seq (string_of_int n))))

let map_name_of_arity (n : int) : string =
  if n = 1 then "Map"
  else "Map" ^ subscript_of_int n

let used_exp_arities : int list ref = ref []

let omap_name_of_arity (n : int) : string =
  if n = 1 then "OMap"
  else "OMap" ^ subscript_of_int n

let used_opt_arities : int list ref = ref []


let rec create_exp (e : Il.Ast.exp) : term
  = match e.it with
    | VarE id -> Ident id.it
    | BoolE b -> if b then Ident "true" else Ident "false"
    | NumE n -> (
      match n with
        | `Nat n -> Num (LeanNat n)
        | `Int i -> Num (LeanInt i)
        | `Rat r -> Num (LeanRat r)
        | `Real r -> Num (LeanReal r)
      )
    | TextE t -> Text t
    | UnE (`PlusOp, _, e) -> create_exp e
    | UnE (op, _, e)
      -> FunApp (
        create_unop_bool op,
        NonEmptyList.from_list_unsafe [Term (create_exp e)]
      )
    | BinE (op, _, e1, e2)
      -> BinaryInfixFunApp (
        Term (create_exp e1),
        create_binop_bool op,
        Term (create_exp e2)
      )
    | CmpE (op, _, e1, e2)
      -> BinaryInfixFunApp (
        Term (create_exp e1),
        create_cmpop_bool op,
        Term (create_exp e2)
      )
    | TupE exps -> Tuple (List.map create_exp exps)
    | ProjE (exp, idx)
      ->
        let length_of_exp =
          match exp.it with
          | TupE exps -> List.length exps
          | _ ->
            (match exp.note.it with
             | TupT fields -> List.length fields
             | _ -> 1)
        in

        (* For a 1-element "tuple", the Lean backend generates proj_ functions
           returning the value directly (not wrapped in a product), so projecting
           field 0 is a no-op. fold_left over [] returns create_exp exp unchanged. *)
        let selector_elems =
          if length_of_exp <= 1 then
            []
          else
            (* Right-nested Lean tuples: idx twos, then "1" unless last element *)
            let twos = List.init idx (fun _ -> "2") in
            if idx = length_of_exp - 1 then twos
            else twos @ ["1"]
        in

        List.fold_left
          (fun acc selector_elem -> DotProj (acc, Ident selector_elem))
          (create_exp exp)
          selector_elems

    | CaseE (mixop, exp)
      ->
        let mixop_args : term list
          = match exp.it with
            | TupE exps -> List.map create_exp exps
            | _ -> [create_exp exp]
        in

        (* Qualify with the variant type name from the IL note: .GLOBAL → externtype.GLOBAL.
           Case 1: direct VariantT — use the type name as-is.
             VarT("addrtype",[]) + "I32" → addrtype.I32
           Case 2: alias that resolves to a VariantT — use the underlying name.
             VarT("Inn",[]) + "I32" → addrtype.I32  (Inn = abbrev addrtype)
             Without this, List.length [.I32, .I64] emits .I32 which is ambiguous
             when Lean has no element-type context from List.length alone.
           Case 3: everything else (struct, u32, …) — leading-dot notation.
             VarT("u32",[]) + "mk_uN" → .mk_uN  (u32 is abbrev uN, no namespace) *)
        let namespaced_mixop : term = match e.note.it with
          | VarT (id, _) when List.mem id.it !analysis.variant_type_names ->
              Ident (id.it ^ "." ^ mixop_to_id mixop)
          | VarT (id, _) ->
              (match List.assoc_opt id.it !analysis.alias_to_variant_map with
               | Some variant_name -> Ident (variant_name ^ "." ^ mixop_to_id mixop)
               | None -> LeadingDot (Ident (mixop_to_id mixop)))
          | _ -> LeadingDot (Ident (mixop_to_id mixop))
        in
        
        if List.length mixop_args = 0 then
          namespaced_mixop
        else
          FunApp (
            namespaced_mixop,
            NonEmptyList.from_list_unsafe
              (List.map (fun arg -> Term arg) mixop_args)
          )
    | UncaseE (exp, mixop) -> error exp.at "Uncase should have been eliminated by uncase-removal pass!"
    | OptE (Some exp) -> FunApp (Ident "some", NonEmptyList.from_list_unsafe [Term (create_exp exp)])
    | OptE (None) -> Ident "none"
    | TheE exp -> FunApp (DotProj (Ident "Option", Ident "get!"), NonEmptyList.from_list_unsafe [Term (create_exp exp)])
    | StrE struct_fields
      ->
        let field_terms = List.map (
          fun (atom, exp) -> (create_atom atom, create_exp exp)
        ) struct_fields in
        Struct {
          fields = List.map (fun (field_name, field_value) -> AssignedField {
            l_val = Ident_SILV field_name;
            is_private = false;
            term = field_value;
          }) field_terms;
          (* Annotate with the struct's type from the IL note so Lean can infer the struct type.
             e.g. { TYPES := [], ... } becomes ({ ... } : context) *)
          type_annotation = Some (create_typ e.note);
        }
    | DotE (exp, atom)
      -> DotProj (create_exp exp, Ident (create_atom atom))
    | CompE (e1, e2) -> BinaryInfixFunApp (Term (create_exp e1), Ident "++", Term (create_exp e2))
    | ListE exps -> List (List.map create_exp exps)
    | LiftE option_term -> FunApp (DotProj (Ident "Option", Ident "toList"), NonEmptyList.from_list_unsafe [Term (create_exp option_term)])
    | MemE (e1, e2) -> FunApp (DotProj (Ident "List", Ident "contains"), NonEmptyList.from_list_unsafe [Term (create_exp e2); Term (create_exp e1)])
    | LenE e1 -> FunApp (DotProj (Ident "List", Ident "length"), NonEmptyList.from_list_unsafe [Term (create_exp e1)])
    (* TODO: tackle pattern matching version of CatE *)
    | CatE (e1, e2) -> BinaryInfixFunApp (Term (create_exp e1), Ident "++", Term (create_exp e2))
    | IdxE (e1, e2) -> Index {
        collection = create_exp e1;
        index = create_exp e2;
        index_type = Unsafe
      }
    | SliceE (e1, e2, e3) ->
        (* SliceE(xs, from, len): xs[from : from+len].
           Lean's xs[i:j] syntax gives Subarray (not List), so use List combinators. *)
        FunApp (
          DotProj (Ident "List", Ident "take"),
          NonEmptyList.from_list_unsafe [
            Term (create_exp e3);
            Term (FunApp (
              DotProj (Ident "List", Ident "drop"),
              NonEmptyList.from_list_unsafe [
                Term (create_exp e2);
                Term (create_exp e1)
              ]
            ))
          ]
        )
    | UpdE (e1, p, e2) -> create_upd_exp e1 p (fun _ -> create_exp e2)
    | ExtE (e1, p, e2) ->
        let concat_old_term_to_new_list_exp (existing_term : term) : term
          = BinaryInfixFunApp (
              Term (existing_term),
              Ident "++",
              Term (create_exp e2)
            )
        in

        (match e2.it with
          | ListE _ -> create_upd_exp e1 p (fun existing_term -> concat_old_term_to_new_list_exp existing_term)
          | VarE _ -> create_upd_exp e1 p (fun existing_term -> concat_old_term_to_new_list_exp existing_term)
          | _ -> failwith ("ExtE must take a list as the new value" ^ " (got: " ^ (Il.Print.string_of_exp e2) ^ ")"))
    | IfE (if_exp, then_exp, else_exp) -> IfThenElse {
        cond = create_exp if_exp;
        then_branch = create_exp then_exp;
        else_branch = create_exp else_exp;
      }
    | CallE (id, args) ->
      let func = (Ident id.it : term) in
      let arg_terms = List.map (fun arg -> Term (create_arg arg)) args in
      (match arg_terms with
       | [] -> func
       | _ -> FunApp (func, NonEmptyList.from_list_unsafe arg_terms))
    | IterE (exp, iterexp) -> create_iter exp iterexp
    | CvtE (exp, `IntT, `NatT) ->
      FunApp (
        DotProj (Ident "Int", Ident "toNat"),
        NonEmptyList.from_list_unsafe [Term (create_exp exp)]
      )
    | CvtE (exp, `RatT, `NatT) | CvtE (exp, `RealT, `NatT) ->
      FunApp (
        Ident "rat_to_nat",
        NonEmptyList.from_list_unsafe [Term (create_exp exp)]
      )
    | CvtE (exp, _numtyp1, numtyp2) ->
      BinaryInfixFunApp (
        Term (create_exp exp),
        Ident ":",
        Term (create_numtyp numtyp2)
      )
      (* let func = Ident "cast" in
      let arg_terms = NonEmptyList.from_list_unsafe [
        Term (create_exp exp);
        Term (create_numtyp numtyp1);
        Term (create_numtyp numtyp2);
      ] in
      FunApp (func, arg_terms) *)
    | _ -> failwith "not implemented yet for create_exp"
    
and create_iter
  (*
      Let's say we have an example like


      (a.map (fun w x y z => w + x + y + z)).ap b |>.ap c |>.ap d

      from

      (IterE
        (BinE AddOp NatT
          (BinE AddOp NatT
            (BinE AddOp NatT (VarE "a") (VarE "b"))
            (VarE "c"))
          (VarE "d"))
        List
        (iterexp "a" (ListE (NumE (Nat 1)) (NumE (Nat 2)) (NumE (Nat 3))))
        (iterexp "b" (ListE (NumE (Nat 4)) (NumE (Nat 5)) (NumE (Nat 6))))
        (iterexp "c" (ListE (NumE (Nat 7)) (NumE (Nat 8)) (NumE (Nat 9))))
        (iterexp "d" (ListE (NumE (Nat 10)) (NumE (Nat 11)) (NumE (Nat 12))))
      )
  *)
  (exp : Il.Ast.exp)            (*
                                  (BinE AddOp NatT
                                    (BinE AddOp NatT
                                      (BinE AddOp NatT (VarE "a") (VarE "b"))
                                      (VarE "c"))
                                    (VarE "d"))
                                *)
  (iterexp : Il.Ast.iterexp)
  : term =
    let (
      iter,                     (* List *)
      id_exp_list               (*
                                  (iterexp "a" (ListE (NumE (Nat 1)) (NumE (Nat 2)) (NumE (Nat 3))))
                                  (iterexp "b" (ListE (NumE (Nat 4)) (NumE (Nat 5)) (NumE (Nat 6))))
                                  (iterexp "c" (ListE (NumE (Nat 7)) (NumE (Nat 8)) (NumE (Nat 9))))
                                  (iterexp "d" (ListE (NumE (Nat 10)) (NumE (Nat 11)) (NumE (Nat 12))))
                                *)
    ) = iterexp in

    let arity = List.length id_exp_list in

    let elem_name_generator (id : Il.Ast.id) : string
      (*
        Gives sensible names to the variables that will be used to represent
        elements of a list in the lambda. For example,

        a.map (fun a_elem b_elem c_elem d_elem => a_elem + b_elem + c_elem + d_elem) |>.ap b |>.ap c |>.ap d

        ^          ^
        list       list elem
      *)
      = id.it ^ "_elem"
    in

    (* Typed binder `(id_elem : T)` for a real collection entry, where `T` is
       read off the collection's own IL type annotation (its `.note`, which
       for any entry in `id_exp_list` is always `IterT (elem_typ, _)` --
       List/List1/ListN/Opt all wrap their element type this way). Renamed to
       `id_elem` (not left as `id`) to avoid shadowing when the element var
       and its own collection var share the same IL name (e.g. {v_expr <-
       v_expr}) -- see `body` below for the matching substitution. *)
    let typed_binder_for_collection ((id, coll_exp) : Il.Ast.id * Il.Ast.exp) : fun_binder =
      let elem_typ = match coll_exp.note.it with
        | IterT (t, _) -> t
        | _ -> failwith "create_iter_exp: expected an iterated collection type"
      in
      BracketedBinder_FB (
        ExplicitParam (
          NonEmptyList.from_list_unsafe [Ident_IOH (elem_name_generator id)],
          create_typ elem_typ
        )
      )
    in

    (* Typed binder for the synthetic index introduced by `ListN (_, Some
       idx)`. Bound under its ORIGINAL IL name, not elem_name_generator-
       renamed: unlike a real collection entry, the index's "collection" is
       always a freshly-built `List.range n_exp` term, never a bare reference
       to a variable literally named `idx` -- so it can never collide with its
       own collection reference the way a real element can, and there's
       nothing to rename it against. `exp`'s body already refers to this exact
       name, so leaving it alone here keeps the generated Lean using the same
       name the spec author wrote (and `body` below deliberately never
       substitutes it). Always `Nat`, since `List.range`'s element type is
       `Nat` unconditionally -- there's no `.note` to consult here as there is
       for a real collection, since this binder isn't drawn from one. *)
    let typed_binder_for_index (idx : Il.Ast.id) : fun_binder =
      BracketedBinder_FB (
        ExplicitParam (
          NonEmptyList.from_list_unsafe [Ident_IOH idx.it],
          Ident "Nat" (* This is safe because this case always uses List.range *)
        )
      )
    in

    (* Renaming happens entirely at the Lean-term level, after `exp` is
       converted -- the original IL/EL expression is never touched. Only real
       collection elements are substituted (to their `_elem`-suffixed name,
       matching typed_binder_for_collection); the synthetic index, when
       present, is deliberately excluded (see typed_binder_for_index) so it
       keeps its author-chosen name in the generated Lean. Independent of
       `iter`/arity, so it's shared unchanged across every branch below. *)
    let body : term =
      let substs =
        List.map (fun (id, _) -> (id.it, Ident (elem_name_generator id))) id_exp_list
      in
      subst_lean_term substs (create_exp exp)
    in

    let collections = List.map (fun (_, coll_exp) -> create_exp coll_exp) id_exp_list in

    let create_zip
      (*
        Creates a term that zips together the lists in `list_terms` using the
        function `zipping_func`. For example, given

        list_terms = [a, b, c, d]
        zipping_func = fun a_elem, b_elem, c_elem, d_elem => a_elem + b_elem + c_elem + d_elem

        The result will be the term:

        a.map (fun w x y z => w + x + y + z) |>.ap b |>.ap c |>.ap d

        where List.ap is our custom application function that should be defined in the prologue.
      *)

      (list_terms : term list)               (* [a, b, c, d]*)
      (zipping_func : term)                  (* fun a_elem, b_elem, c_elem, d_elem => a_elem + b_elem + c_elem + d_elem *)
      : term =

      (* this helper exists because we need a recursive function, but we also
      need to reverse the terms list exactly once on entry. The reversing is
      just to make it convenient to do hd and tl. *)
      let rec go
        (reversed_terms : term list)      (* [d, c, b, a]*)
        (func : term)                     (* fun a_elem, b_elem, c_elem, d_elem => a_elem + b_elem + c_elem + d_elem *)
        : term =

        let arity = List.length reversed_terms in

        match arity with
        | 0 -> failwith "arity should never reach 0 here"
        | 1 ->
          let term = List.hd reversed_terms in
          FunApp (
            (RightPipelineField (term, Ident "map")),
            NonEmptyList.from_list_unsafe
              [Term func]
          )
        | _ ->
          let term = List.hd reversed_terms in
          let nested = go (List.tl reversed_terms) func in
          FunApp (
            RightPipelineField (
              nested,
              Ident "ap"
            ),
            NonEmptyList.from_list_unsafe
              [Term term]
          )
      in

      go (List.rev list_terms) zipping_func
    in

    match arity, iter with
    | 0, ListN (n_exp, None) ->
      (*
        List.replicate n_exp exp
      *)
      FunApp (
        DotProj (Ident "List", Ident "replicate"),
        NonEmptyList.from_list_unsafe
          [Term (create_exp n_exp); Term (create_exp exp)]
      )

    | 0, ListN (n_exp, Some idx) ->
      (*
        List.range n_exp |>.map (fun idx => exp)
      *)
      FunApp (
        RightPipelineField (
          FunApp (
            DotProj (Ident "List", Ident "range"),
            NonEmptyList.from_list_unsafe [Term (create_exp n_exp)]
          ),
          Ident "map"
        ),
        NonEmptyList.from_list_unsafe
          [
            Term (Lambda {
              params = NonEmptyList.from_list_unsafe [typed_binder_for_index idx];
              body;
            })
          ]
      )

    | arity, (List | List1 | ListN (_, None)) when arity > 0 ->

      let lambda_func : term =
        Lambda {
          params = NonEmptyList.from_list_unsafe (List.map typed_binder_for_collection id_exp_list);
          body;
        }
      in
      used_exp_arities := arity :: !used_exp_arities;
      FunApp (
        Ident (map_name_of_arity arity),
        NonEmptyList.from_list_unsafe (
          Term lambda_func :: List.map (fun c -> Term c) collections
        )
      )

    | arity, Opt when arity > 0 ->

      let lambda_func : term =
        Lambda {
          params = NonEmptyList.from_list_unsafe (List.map typed_binder_for_collection id_exp_list);
          body;
        }
      in
      used_opt_arities := arity :: !used_opt_arities;
      FunApp (
        Ident (omap_name_of_arity arity),
        NonEmptyList.from_list_unsafe (
          Term lambda_func :: List.map (fun c -> Term c) collections
        )
      )

    | arity, ListN (n_exp, Some idx) when arity > 0 ->

      let range_term =
        FunApp (
          DotProj (Ident "List", Ident "range"),
          NonEmptyList.from_list_unsafe [Term (create_exp n_exp)]
        )
      in

      let lambda_with_index = Lambda {
          params = NonEmptyList.from_list_unsafe (
            typed_binder_for_index idx :: List.map typed_binder_for_collection id_exp_list
          );
          body;
        }
      in

      create_zip (range_term :: collections) lambda_with_index

    | _ -> failwith "other cases should not exist!"

and create_arg (arg : Il.Ast.arg) : term
  = match arg.it with
    | ExpA exp -> create_exp exp
    | TypA typ -> create_typ typ
    | DefA id -> Ident id.it
    | GramA _ -> failwith "not implemented yet"


    (* | BinE (op, t, e1, e2) -> *)

    (* | VarE (_, _) -> error e.at "arg list in VarE must be empty because they should be eliminated by undep!"
    | BoolE b -> if b then Ident "true" else Ident "false"
    | NumE n -> Num n
    | TextE s -> Text s
    | TupE [] -> Unit
    | TupE l -> Tuple (List.map create_exp l)
    | CatE (e1, e2) -> FunApp (Ident "List.append", NonEmptyList.from_list_unsafe [Term (create_exp e1); Term (create_exp e2)])
    | BinE (op, typ, e1, e2) ->
      let op_str = match op with
        | AddOp -> "+"
        | SubOp -> "-"
        | MulOp -> "*"
        | DivOp -> "/" *)

(* TODO check AI-generated *)
and create_upd_exp
  (root : Il.Ast.exp)
  (p : Il.Ast.path)
  (* (new_val : Il.Ast.exp) *)
  (operation_on_old_val : term -> term)
  : term =
  
  let flatten_path (p : Il.Ast.path) : path_seg list =
    let rec go p = match p.it with
      | RootP -> []
      | DotP (p', a)       -> go p' @ [DotSeg a]
      | IdxP (p', e)       -> go p' @ [IdxSeg e]
      | SliceP (p', e1, e2)-> go p' @ [SliceSeg (e1, e2)]
    in go p
  in


  let counter = ref 0 in
  let fresh () = incr counter; "elem_" ^ string_of_int !counter in


  (* List.modify lst idx body *)
  let create_list_modify (lst : term) (idx : term) (body : term) =
    FunApp (DotProj (Ident "List", Ident "modify"),
            NonEmptyList.from_list_unsafe [Term lst; Term idx; Term body])
  in


  let rec go
    (prev : term)
    (segs : path_seg list) =
    match segs with
    | [] -> operation_on_old_val prev
    | [DotSeg a] ->
        UpdateStruct {
          struct_to_update = prev;
          fields_to_update = [AssignedField {
            l_val = Ident_SILV (create_atom a);
            is_private = false;
            term = operation_on_old_val (DotProj (prev, Ident (create_atom a)));
          }]
        }
    | DotSeg a :: rest ->
        let field = create_atom a in
        UpdateStruct {
          struct_to_update = prev;
          fields_to_update = [AssignedField {
            l_val = Ident_SILV field;
            is_private = false;
            term = go (DotProj (prev, Ident field)) rest;
          }]
        }
    | IdxSeg e :: rest ->
        let v = fresh () in
        create_list_modify prev (create_exp e) (simple_lambda v (go (Ident v) rest))
    | SliceSeg (e1, e2) :: rest ->
        (* Slice update: extract the subrange [e1 .. e1+e2) of prev, recurse into it
           (via go old_slice rest), then splice the updated slice back in.
           Terminal (rest=[]):     go old_slice [] = operation_on_old_val old_slice.
           Non-terminal (rest!=[]): go old_slice rest navigates further WITHIN the slice.
           Mirrors how IdxSeg delegates to go (Ident v) rest on a single element.
           Example (terminal):     s[.MEMS[x].BYTES[i : j] = b*]
             prev = elem_1.BYTES,  e1 = i,  e2 = j,  operation_on_old_val _ = b*
           Example (non-terminal): s[.MEMS[i : n][k] = mi]
             prev = s.MEMS,  rest = [IdxSeg k],  operation_on_old_val _ = mi

           The read side above (drop_e1/old_slice) is already safe as-is: take/drop
           saturate at prev's real length rather than growing anything. The WRITE
           side below is NOT naturally safe if taken naively as
             (prev.take e1 ++ new_middle) ++ prev.drop (e1 + e2)
           -- that formula is only length-preserving when new_middle's actual
           length equals e2 exactly. It doesn't in general (e.g. an
           out-of-bounds memory store, where e1 + |new_middle| > prev.length):
           .take saturates and .drop past the end returns [], so the naive
           result would be LONGER than prev. This is a real soundness bug (it
           lets $with_mem grow a memory's BYTES list on an OOB store), not a
           cosmetic one, so the write side clamps the offset and the effective
           write length against prev's real length before splicing -- this is
           the Lean-combinator analogue of Rocq's `list_slice_update`, which is
           unconditionally length-preserving because it recurses structurally
           on the list itself. Clamping against new_middle's ACTUAL length
           (rather than trusting e2_t) is what makes this correct generally,
           not just for $with_mem: e.g. wasm-1.0's module-instantiation rules
           reach this same arm with the length written as `|a*|` (tied to the
           replacement list by construction), and the ExtE/"append" call path
           (see create_exp's ExtE arm above) deliberately makes new_middle
           longer than old_slice -- both are handled uniformly by clamping on
           new_middle.length instead of on a declared/assumed length. *)
        let e1_t : term = create_exp e1 in
        (* e1_t : term  ----  e.g.  i *)
        let e2_t : term = create_exp e2 in
        (* e2_t : term  ----  e.g.  j *)
        let drop_e1 : term =
          FunApp (DotProj (prev, Ident "drop"),
                  NonEmptyList.from_list_unsafe [Term e1_t]) in
        (* drop_e1 : term  ----  e.g.  elem_1.BYTES.drop i *)
        let old_slice : term =
          FunApp (DotProj (drop_e1, Ident "take"),
                  NonEmptyList.from_list_unsafe [Term e2_t]) in
        (* old_slice : term  ----  e.g.  (elem_1.BYTES.drop i).take j  = bytes[i..i+j) *)
        let new_middle : term = go old_slice rest in
        (* new_middle : term  ----  terminal: b*;  non-terminal: List.modify old_slice k ... *)
        FunApp (Ident "splice", NonEmptyList.from_list_unsafe [Term prev; Term new_middle; Term e1_t])
        (* result : term  ----  e.g.  splice elem_1.BYTES b* i. `splice` (prologue
           helper, lean_builder.ml) clamps the offset and the effective write
           length against prev's real length before splicing, so this can never
           grow past prev -- the Lean-combinator analogue of Rocq's
           `list_slice_update`. It clamps against new_middle's ACTUAL length
           (not e2_t), which is what makes it correct generally, not just for
           $with_mem: e.g. wasm-1.0's module-instantiation rules reach this
           same arm with the length written as `|a*|`, and the ExtE/"append"
           call path (see create_exp's ExtE arm above) deliberately makes
           new_middle longer than old_slice -- both are handled uniformly. *)
  in
  go (create_exp root) (flatten_path p)


(* ── IterPr helpers ─────────────────────────────────────────────────────────
   These are standalone (not in the create_exp and-chain) because they only
   depend on create_exp (defined above) and create_prem/create_iter_prem
   (defined below as a mutual let rec pair).
   ─────────────────────────────────────────────────────────────────────────── *)


(*
  make_left_zip collections

  Build a left-associatively zipped list from two or more Lean terms using
  the |>.zip syntax (RightPipelineField).

  Example with 2 inputs [m_lst; n_lst] (Pairs_ok):
    m_lst |>.zip (n_lst)  →  m_lst.zip n_lst  : List (m × n)

  Example with 3 inputs [xs; ys; zs]:
    xs |>.zip (ys) |>.zip (zs)  →  (xs.zip ys).zip zs  : List ((α × β) × γ)

  This is only called for n ≥ 2.
*)
let make_left_zip (collections : term list) : term =
  (* collections = [xs; ys; zs; ...]  (at least 2 elements) *)
  List.fold_left
    (fun acc coll ->
      (* acc.zip coll  →  FunApp(RightPipelineField(acc, "zip"), [coll]) *)
      FunApp (
        RightPipelineField (acc, Ident "zip"),
        NonEmptyList.from_list_unsafe [Term coll]
      ))
    (List.hd collections)    (* start with xs *)
    (List.tl collections)    (* fold in ys, then zs, etc. *)

(*
  make_proj i n base

  Return the Lean projection for element at 0-indexed position i in a
  left-nested tuple of depth n, rooted at base.

  Left-nested structure (how List.zip chains):
    n=2 : α × β           → i=0: base.1   i=1: base.2
      (Pairs_ok: base=__iter_tuple; i=0 → "v_m"=__iter_tuple.1, i=1 → "v_n"=__iter_tuple.2)
    n=3 : (α × β) × γ     → i=0: base.1.1   i=1: base.1.2   i=2: base.2
    n=4 : ((α×β)×γ) × δ   → i=0: base.1.1.1  i=1: base.1.1.2  i=2: base.1.2  i=3: base.2

  Recursive rule:
    n=1        → base             (scalar, no tuple)
    i = n-1    → base.2           (last element is always the right component)
    otherwise  → proj i (n-1) base.1   (recurse into left sub-tuple)
*)
let rec make_proj (i : int) (n : int) (base : term) : term =
  if n = 1 then
    base                                               (* n=1: element is the term itself *)
  else if i = n - 1 then
    DotProj (base, Ident "2")                         (* last element → .2 *)
  else
    make_proj i (n - 1) (DotProj (base, Ident "1"))  (* recurse into left sub-tuple via .1 *)


(*
  Forall generation helpers
  ──────────────────────────────────────────────────────────────────────────────
  Named Forall predicates are generated once at the top of the file and then
  referenced at every IterPr usage site, replacing inline BoundedForall nodes.

  Naming: Forall (arity 1), Forall₂ (arity 2), Forall₃ (arity 3), ...
  Definitions are constructed using make_left_zip and make_proj so the body
  exactly mirrors the inline form — only the wrapping changes.

  Example generated definitions:
    def Forall {α₁ : Type} (P : α₁ → Prop) (xs₁ : List α₁) : Prop :=
      ∀ t_elem ∈ xs₁, P t_elem

    def Forall₂ {α₁ α₂ : Type} (P : α₁ → α₂ → Prop) (xs₁ : List α₁) (xs₂ : List α₂) : Prop :=
      ∀ t ∈ xs₁ |>.zip xs₂, P (t.1) (t.2)
  ──────────────────────────────────────────────────────────────────────────────
*)

let forall_with_arity (n : int) : string =
  if n = 1 then "Forall"
  else "Forall" ^ subscript_of_int n

(*
  used_prem_arities  records every arity that create_iter_prem actually emits
  a ForallN call for during the create_def pass.  Populated as a side effect;
  used in create_script to emit only ForallN definitions that are genuinely
  referenced.  This avoids spurious definitions for IterPr nodes that live
  inside GramD (or other silently-skipped IL branches) and are never reached
  by create_iter_prem.
*)
let used_prem_arities : int list ref = ref []

(*
  make_forall_def n  constructs the Lean 'def' for the n-ary Forall predicate,
  using make_left_zip and make_proj for the body so the generated definition
  is consistent with the inline BoundedForall form it replaces.
*)
let make_forall_def (n : int) : command =
  assert (n >= 1);
  let indices  = List.init n (fun i -> i) in
  let type_var i = Printf.sprintf "α%s" (subscript_of_int (i + 1)) in  (* α₁, α₂, … *)
  let coll_var i = Printf.sprintf "xs%s" (subscript_of_int (i + 1)) in (* xs₁, xs₂, … *)
  let tuple_var = "t" in
  let elem_var  = "t_elem" in  (* used only for n = 1 *)

  (* P : α₁ → α₂ → … → αN → Prop *)
  let p_type = List.fold_right
    (fun i acc -> FunType (Ident (type_var i), acc))
    indices Prop
  in

  (* {α₁ α₂ … αN : Type} *)
  let type_binder = BracketedBinder (ImplicitParam (
    NonEmptyList.from_list_unsafe (List.map (fun i -> Ident_IOH (type_var i)) indices),
    Type None
  )) in

  (* (P : α₁ → … → αN → Prop) *)
  let p_binder = BracketedBinder (ExplicitParam (
    NonEmptyList.from_list_unsafe [Ident_IOH "P"],
    p_type
  )) in

  (* (xs₁ : List α₁) … (xsN : List αN) *)
  let coll_binders = List.map (fun i ->
    BracketedBinder (ExplicitParam (
      NonEmptyList.from_list_unsafe [Ident_IOH (coll_var i)],
      FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident (type_var i))])
    ))
  ) indices in

  let body =
    if n = 1 then
      BoundedForall {
        var        = elem_var;
        collection = Ident (coll_var 0);
        body       = FunApp (Ident "P", NonEmptyList.from_list_unsafe [Term (Ident elem_var)]);
      }
    else
      let collections = List.map (fun i -> Ident (coll_var i)) indices in
      let zipped = make_left_zip collections in
      let proj_args = NonEmptyList.from_list_unsafe
        (List.map (fun i -> Term (make_proj i n (Ident tuple_var))) indices)
      in
      BoundedForall {
        var        = tuple_var;
        collection = zipped;
        body       = FunApp (Ident "P", proj_args);
      }
  in

  Def (DefAsgn {
    modifier  = empty_modifier;
    id        = forall_with_arity n;
    signature = ([type_binder; p_binder] @ coll_binders, Some Prop);
    body;
  })

(*
  make_map_def n  constructs the Lean 'def' for the n-ary Map combinator.

  def Map  {α₁ β : Type} (f : α₁ → β)           (xs₁ : List α₁) : List β :=
    xs₁.map f
  def Map₂ {α₁ α₂ β : Type} (f : α₁ → α₂ → β)  (xs₁ : List α₁) (xs₂ : List α₂) : List β :=
    xs₁.map f |>.ap xs₂
  def Map₃ {α₁ α₂ α₃ β : Type} ...               ... : List β :=
    xs₁.map f |>.ap xs₂ |>.ap xs₃
*)
let make_map_def (n : int) : command =
  assert (n >= 1);
  let indices   = List.init n (fun i -> i) in
  let type_var i = Printf.sprintf "α%s" (subscript_of_int (i + 1)) in
  let coll_var i = Printf.sprintf "xs%s" (subscript_of_int (i + 1)) in

  (* {α₁ ... αN β : Type} *)
  let type_binder = BracketedBinder (ImplicitParam (
    NonEmptyList.from_list_unsafe (
      List.map (fun i -> Ident_IOH (type_var i)) indices @ [Ident_IOH "β"]
    ),
    Type None
  )) in

  (* f : α₁ → ... → αN → β *)
  let f_type = List.fold_right
    (fun i acc -> FunType (Ident (type_var i), acc))
    indices (Ident "β")
  in
  let f_binder = BracketedBinder (ExplicitParam (
    NonEmptyList.from_list_unsafe [Ident_IOH "f"],
    f_type
  )) in

  (* (xs₁ : List α₁) … (xsN : List αN) *)
  let coll_binders = List.map (fun i ->
    BracketedBinder (ExplicitParam (
      NonEmptyList.from_list_unsafe [Ident_IOH (coll_var i)],
      FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident (type_var i))])
    ))
  ) indices in

  (* return type : List β *)
  let return_type =
    FunApp (Ident "List", NonEmptyList.from_list_unsafe [Term (Ident "β")])
  in

  (* body: xs₁.map f |>.ap xs₂ |>.ap xs₃ ... *)
  let body =
    List.fold_left
      (fun acc i ->
        FunApp (
          RightPipelineField (acc, Ident "ap"),
          NonEmptyList.from_list_unsafe [Term (Ident (coll_var i))]
        )
      )
      (FunApp (
        RightPipelineField (Ident (coll_var 0), Ident "map"),
        NonEmptyList.from_list_unsafe [Term (Ident "f")]
      ))
      (List.tl indices)
  in

  Def (DefAsgn {
    modifier  = empty_modifier;
    id        = map_name_of_arity n;
    signature = ([type_binder; f_binder] @ coll_binders, Some return_type);
    body;
  })

(*
  make_omap_def n  constructs the Lean 'def' for the n-ary OMap combinator,
  the Option-valued analogue of MapN.

  def OMap  {α₁ β : Type} (f : α₁ → β)          (xs₁ : Option α₁) : Option β :=
    xs₁.map f
  def OMap₂ {α₁ α₂ β : Type} (f : α₁ → α₂ → β) (xs₁ : Option α₁) (xs₂ : Option α₂) : Option β :=
    xs₁.map f |>.ap xs₂
*)
let make_omap_def (n : int) : command =
  assert (n >= 1);
  let indices   = List.init n (fun i -> i) in
  let type_var i = Printf.sprintf "α%s" (subscript_of_int (i + 1)) in
  let coll_var i = Printf.sprintf "xs%s" (subscript_of_int (i + 1)) in

  let type_binder = BracketedBinder (ImplicitParam (
    NonEmptyList.from_list_unsafe (
      List.map (fun i -> Ident_IOH (type_var i)) indices @ [Ident_IOH "β"]
    ),
    Type None
  )) in

  let f_type = List.fold_right
    (fun i acc -> FunType (Ident (type_var i), acc))
    indices (Ident "β")
  in
  let f_binder = BracketedBinder (ExplicitParam (
    NonEmptyList.from_list_unsafe [Ident_IOH "f"],
    f_type
  )) in

  let coll_binders = List.map (fun i ->
    BracketedBinder (ExplicitParam (
      NonEmptyList.from_list_unsafe [Ident_IOH (coll_var i)],
      FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (Ident (type_var i))])
    ))
  ) indices in

  let return_type =
    FunApp (Ident "Option", NonEmptyList.from_list_unsafe [Term (Ident "β")])
  in

  let body =
    List.fold_left
      (fun acc i ->
        FunApp (
          RightPipelineField (acc, Ident "ap"),
          NonEmptyList.from_list_unsafe [Term (Ident (coll_var i))]
        )
      )
      (FunApp (
        RightPipelineField (Ident (coll_var 0), Ident "map"),
        NonEmptyList.from_list_unsafe [Term (Ident "f")]
      ))
      (List.tl indices)
  in

  Def (DefAsgn {
    modifier  = empty_modifier;
    id        = omap_name_of_arity n;
    signature = ([type_binder; f_binder] @ coll_binders, Some return_type);
    body;
  })


(*
  create_prem and create_iter_prem are mutually recursive:
    create_prem dispatches IterPr to create_iter_prem
    create_iter_prem calls create_prem on (possibly renamed) sub-premises

  ── create_prem ────────────────────────────────────────────────────────────
  Translates an IL premise into a Lean term (always a Prop-valued expression).

  ── create_iter_prem ───────────────────────────────────────────────────────
  Translates IterPr(p, iterexp) into a kernel-safe BoundedForall term.

  IterPr(p, (iter, id_exp_list)) means:
    "premise p holds for every simultaneous assignment of variables id_i to
     elements drawn in parallel from their respective collections."

  We use ∀ x ∈ xs, P x rather than inductive Forall/Forall₂ because the
  inductive form breaks Lean's positivity checker inside mutual inductive
  blocks (see PR #192 discussion, Lean issue leanprover/lean4#1964).

  ARITY 0 — no iteration variables, emit the premise directly:
    IterPr(IfPr(x == y), (List, []))
    →  x == y

  ARITY 1 — single collection, emit ∀ var ∈ collection, body:
    IterPr(RulePr("TypeOk", VarE "t"), (List, [("t", VarE "ts")]))
    →  ∀ t ∈ ts, TypeOk (t)

    No renaming needed: the prem body already uses "t" as the element
    variable, and BoundedForall binds "t" exactly.

  ARITY ≥ 2 — zip all collections, bind one tuple variable, project each:
    IterPr(
      RulePr("Pair_ok", (Infix Arg |- Arg), TupE [VarE "v_n"; VarE "v_m"]),
      (List, [("v_m", VarE "m_lst"); ("v_n", VarE "n_lst")])
    )
    →  ∀ __iter_tuple ∈ m_lst |>.zip (n_lst),
         Pair_ok (__iter_tuple.2) (__iter_tuple.1)

  Algorithm for arity ≥ 2:
    1. Build zipped collection: m_lst |>.zip (n_lst)
    2. create_prem on the UNCHANGED prem → Lean term with Ident "v_n", Ident "v_m"
    3. Substitute: "v_m" (i=0) → __iter_tuple.1, "v_n" (i=1) → __iter_tuple.2
       — this is safe (no capture) because subst_lean_term drops a name from
       the active substitution as soon as it descends into a binder that
       rebinds it (see subst_lean_term's BoundedForall/Lambda cases).
    4. Wrap in BoundedForall { var = "__iter_tuple"; collection = m_lst |>.zip (n_lst); body }

  For Opt iteration the option is converted to a list via Option.toList.
*)
let rec create_prem (p : Il.Ast.prem) : term = match p.it with
  | RulePr (
    (id : Il.Ast.id),
    (rel_args : Il.Ast.arg list),
    (mixop : Il.Ast.mixop),
    (exp : Il.Ast.exp)
  ) ->
    (* `rel_args` carries the relation's own TypP/DefP/GramP quantifiers (e.g. the
       `X` in a polymorphic relation like fun_concat_), positionally corresponding
       to the callee's own params (see deftorel.ml's cvt_def_to_rel/create_fun_prem).
       They must be rendered before the ordinary value/tuple arguments to match the
       relation's declared parameter order. *)
    let flattened_mixop_args : term list
      = match exp.it with
        | TupE exps -> List.map create_exp exps
        | _ -> [create_exp exp]
    in
    let args = List.map create_arg rel_args @ flattened_mixop_args in
    (match args with
      | [] -> Ident id.it
      | args ->
        FunApp (
          Ident id.it,
          NonEmptyList.from_list_unsafe (List.map (fun arg -> Term arg) args)
        ))
  | IfPr (
    (exp : Il.Ast.exp)
  ) ->
    let rec create_exp_as_prop (exp : Il.Ast.exp) : term =
    match exp.it with
      | BinE (op, _, e1, e2)
        -> BinaryInfixFunApp (
          Term (create_exp_as_prop e1),
          create_binop_prop op,
          Term (create_exp_as_prop e2)
        )
      | CmpE (op, _, e1, e2)
        -> BinaryInfixFunApp (
          Term (create_exp_as_prop e1),
          create_cmpop_prop op,
          Term (create_exp_as_prop e2)
        )
    | UnE (`NotOp, _, e) ->
        Not (create_exp_as_prop e)
    | _ -> create_exp exp
    in
    create_exp_as_prop exp
  | IterPr (inner_prem, iterexp) ->
      create_iter_prem inner_prem iterexp   (* dispatch to the arity-independent handler *)
  | NegPr (inner_prem) ->
      Not (create_prem inner_prem)
  | ElsePr -> failwith "create_prem: ElsePr should have been filtered out by filter_else_prems"
  | LetPr _  -> failwith "LetPr should have been handled separately"

(*
  create_iter_prem — see the large comment block above create_prem for full docs.
*)
and create_iter_prem
  (prem       : Il.Ast.prem)
  (iterexp    : Il.Ast.iterexp)
  : term =

  let (
    iter,           (* List *)
    id_exp_list
  ) = iterexp in

  (* Wrap a collection term in Option.toList if this is an Opt iteration.
  e.g. for IterPr(p, (Opt, [("x", opt_exp)])):
    opt_exp : Option α  →  Option.toList opt_exp : List α *)
  let to_list_if_opt (t : term) : term =
    match iter with
    | Opt ->
        FunApp (
          DotProj (Ident "Option", Ident "toList"),
          NonEmptyList.from_list_unsafe [Term t]
        )
    | _ -> t
  in

  (* Every real collection's IL type annotation is `IterT (elem_typ, _)`
     (List/List1/ListN/Opt all wrap their element type this way) -- read
     `elem_typ` off it and convert to a Lean type term. *)
  let elem_typ_of (e : Il.Ast.exp) : term =
    match e.note.it with
    | IterT (t, _) -> create_typ t
    | _ -> failwith "create_iter_prem: expected an iterated collection type"
  in

  let typed_binder (name : string) (typ : term) : fun_binder =
    BracketedBinder_FB (
      ExplicitParam (NonEmptyList.from_list_unsafe [Ident_IOH name], typ)
    )
  in

  (* Renamed Lean identifier for a real collection's element, shared by
     `entries` (the binder's name) and `substs` (the rewrite target) below,
     so the two can never drift out of sync with each other. Always renamed
     to avoid colliding with its own collection variable's name (e.g.
     {v_expr <- v_expr}). *)
  let elem_name (id : Il.Ast.id) : string = id.it ^ "_elem" in

  (* One entry per lambda parameter, in the exact positional order used
     throughout: the synthetic index first (if `iter` supplies one), then
     each real collection in its original order. Each entry already carries
     its FINAL Lean binder name: the index keeps its author-chosen name
     (its "collection" is always a freshly-built `List.range n_exp` term,
     never a bare reference to a variable literally named `idx`, so unlike a
     real collection it can never collide with its own collection reference,
     and there's nothing to rename it against), while each real collection's
     element is `elem_name`-renamed. The index is always typed Nat, since
     List.range's element type is Nat unconditionally and there's no `.note`
     to consult for a binder that isn't drawn from a real collection. *)
  let entries : (string * term * term) list =   (* (binder name, collection term, element type term) *)
    (match iter with
     | ListN (n_exp, Some idx) ->
         [(idx.it,
           FunApp (
             DotProj (Ident "List", Ident "range"),
             NonEmptyList.from_list_unsafe [Term (create_exp n_exp)]
           ),
           Ident "Nat")]
     | _ -> [])
    @ List.map
        (fun (id, e) -> (elem_name id, to_list_if_opt (create_exp e), elem_typ_of e))
        id_exp_list
  in

  let params_of (entries : (string * term * term) list) : fun_binder list =
    List.map (fun (name, _, typ) -> typed_binder name typ) entries
  in
  let colls_of (entries : (string * term * term) list) : term list =
    List.map (fun (_, coll, _) -> coll) entries
  in

  (* Renaming happens only for real elements -- the index, when present, is
     deliberately excluded (see `entries` above), so it keeps its
     author-chosen name in the generated Lean, exactly like create_iter_exp. *)
  let substs = List.map (fun (id, _) -> (id.it, Ident (elem_name id))) id_exp_list in
  let body = subst_lean_term substs (create_prem prem) in

  match entries with

  (* ── Arity 0: degenerate — no iteration, emit premise directly ───────── *)
  | [] ->
      body

  (* ── Arity 1 ─────────────────────────────────────────────────────────── *)
  | [(name, coll_term, typ)] ->
      (*
        Emit:  Forall (fun (id_elem : T) => body) collection
      *)
      used_prem_arities := 1 :: !used_prem_arities;
      FunApp (
        Ident (forall_with_arity 1),
        NonEmptyList.from_list_unsafe [
          Term (Lambda {
            params = NonEmptyList.from_list_unsafe [typed_binder name typ];
            body;
          });
          Term coll_term;
        ]
      )

  (* ── Arity ≥ 2 ────────────────────────────────────────────────────────── *)
  | _ ->
      (*
        Emit:  ForallN (fun (id₁_elem : T₁) … (idN_elem : TN) => body) xs₁ … xsN

        params_of/colls_of are both plain `List.map` over this same `entries`
        list, so they're guaranteed equal in length by construction -- no
        length check needed, there's no way for them to diverge.
      *)
      let arity = List.length entries in
      used_prem_arities := arity :: !used_prem_arities;
      let lambda = Lambda {
        params = NonEmptyList.from_list_unsafe (params_of entries);
        body;
      } in
      FunApp (
        Ident (forall_with_arity arity),
        NonEmptyList.from_list_unsafe (Term lambda :: List.map (fun c -> Term c) (colls_of entries))
      )


let filter_else_prems (prems : Il.Ast.prem list) : Il.Ast.prem list =
  (*
    ElsePr ("-- otherwise") carries no actual condition to check at runtime —
    it just marks "this is the fallback clause" for the else/else-simplification
    middlend passes. Drop it here so it never turns into a printed guard; e.g.

      def $opt_(syntax X, x1) = none  -- otherwise

    should render as a plain match arm body, not `TEMPORARY_PREM → none` or
    `True → none`.
  *)
  List.filter (fun p -> match p.it with ElsePr -> false | _ -> true) prems

let separate_out_let_prems_in_order (prems : Il.Ast.prem list) : Il.Ast.prem list * Il.Ast.prem list =
  (*
    We use this to extract the LetPr prems in order to render them as a series
    of let bindings at the very start of the premise chain.

    Importantly, we extract them in the order they appear in the IL, because the
    LetPr premises may depend on each other (e.g. `let x = 1` then `let y = x +
    1`).
  *)
  let let_prems, other_prems =
    List.partition
      (fun p -> match p.it with LetPr _ -> true | _ -> false)
      prems
  in
  (let_prems, other_prems)

(* For inductive proposition constructors: renders each premise on its own line.
   Use this when building the signature of an inductive relation case. *)
let append_prems_to_prop (conclusion : term) (prems : Il.Ast.prem list) : term =
  let prems = filter_else_prems prems in
  match prems with
  | [] -> conclusion
  | _  -> Premises (List.map create_prem prems @ [conclusion])

let prepend_let_prems (prems : Il.Ast.prem list) (next : term) : term =
  let prepend_let_prem (p : Il.Ast.prem) (next : term) : term = match p.it with
    | LetPr (_, exp1, exp2) ->
        Let {
          let_config = [];
          let_decl = LetPatDecl ({
            pat = create_exp exp1;
            type_ = None;
            value = create_exp exp2;
          });
          body = next;
        }
    | _ -> failwith "create_let_prems: expected only LetPr"
  in
  List.fold_right prepend_let_prem prems next

(* For definition bodies: renders as a flat FunType chain (inline →).
   Use this when building the body of a def match arm or no-match clause. *)
let append_prems_to_term (term : term) (prems : Il.Ast.prem list) : term =
  let prems = filter_else_prems prems in

  if prems = [] then
    term
  else
    let let_prems, other_prems = separate_out_let_prems_in_order prems in
    let prems_as_terms = List.map create_prem other_prems in
    prepend_let_prems let_prems (create_curried_func (prems_as_terms @ [term]))

let create_typcase
  (* 
  Take the example of a toy inductive type

  inductive vec (X : Type) : Type
    | mk_vec (X_lst : List X) (v_n : n) : X_lst.length < v_n -> vec X

  This function is responsible for creating typecases such as

    | mk_vec (X_lst : List X) (v_n : n) : X_lst.length < v_n -> vec X
  *)
  (parent_type    : Il.Ast.id)            (* In the example, this would be `vec` *)
  (parent_params  : Il.Ast.quant list)    (* In the example, this would be `(X : Type)` *)
  (typcase        : Il.Ast.typcase)       (* In the example, this would be `mk_vec (X_lst : List X) {v_n : n} : X_lst.length < v_n` *)
  : _inductive_case
  =
  
  let (
    mixop,                  (* mk_vec *)
    (
      typ,                  (* (X_lst : List X) *)
      quants,               (* (v_n : n) *)
      prems                 (* X_lst.length < v_n *)
    ),
    _                       (* hints are ignored *)
  ) = typcase
  in

  let inductive_type_with_params_applied (* vec X *)
    = create_inductive_type_with_params_applied parent_type parent_params
  in

  (*
  
  NOTE: From:

    syntax list(syntax X) = X*  -- if |X*| < $(2^32)

  We don't create:

    inductive list (X : Type) : Type where
      | mk_list (X_lst : List X) : (List.length X_lst) < (2 ^ 32) → list X
    deriving Inhabited, BEq

  but rather:

    inductive list (X : Type) : Type where
      | mk_list (X_lst : List X) : list X
    deriving Inhabited, BEq

  because we expect a wf_list to be generated in future versions.
  
  *)

  (* let appended_with_prems (* X_lst.length < v_n -> vec X *)
    = append_prems_to_term inductive_type_with_params_applied prems
  in *)

  let params_from_typ (* (X_lst : List X) *)
    = match typ.it with
        | TupT id_typ_list ->

            (* TODO: Check Claude-generated hash table id dedup algo *)
            let counts = Hashtbl.create 4 in
            List.iter (fun (id, _) ->
              let n = try Hashtbl.find counts id.it with Not_found -> 0 in
              Hashtbl.replace counts id.it (n + 1)
            ) id_typ_list;
            let seen = Hashtbl.create 4 in
            List.map (fun (id, typ) ->
              let name =
                if Hashtbl.find counts id.it > 1 then begin
                  let k = try Hashtbl.find seen id.it with Not_found -> 0 in
                  Hashtbl.replace seen id.it (k + 1);
                  id.it ^ "_" ^ string_of_int k
                end else id.it
              in
              BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH name],
                create_typ typ
              ))
            ) id_typ_list
        | _ -> failwith "typ under typcase must be TupT!"
  in

  (* TODO: Check what this means and if it is needed. *)
  (* let params_from_quants (* (v_n : n) *)
    = List.map (
      fun q -> match q.it with
        | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
          NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
          create_typ typ
        ))
        | _ -> failwith "only ExpP should be here"
    ) quants
  in *)
  
  {
    modifier = empty_modifier;
    id = mixop_to_id mixop;
    signature = (
      params_from_typ,
      Some inductive_type_with_params_applied
    );
  }

(*
  il_env holds an Il.Env.t built from the whole script (see create_script),
  used only by remove_overlapping_clauses below to evaluate closed function
  calls when deciding whether two DecD clauses are duplicates.
*)
let il_env : Il.Env.t ref = ref Il.Env.empty

(*
  same algorithm as in backend-rocq/disamb.ml

  For something like:

  def $cunpack(storagetype) : consttype hint(show $unpack(%)) hint(partial)
  def $cunpack(consttype) = consttype
  def $cunpack(packtype) = I32
  def $cunpack(lanetype) = $lunpack(lanetype)  ;; HACK

  the subexpansion pass causes `def cunpack` to have both
  `| storagetype.I32 => some consttype.I32`
  and
  `| storagetype.I32 => some (consttype_numtype (lunpack lanetype.I32))`

  We check if both the LHS and RHS of the match are the same. In order to
  to this, we also need to evaluate the RHS, to show that, for instance,

  `some consttype.I32`
  is the same as
  `some (consttype_numtype (lunpack lanetype.I32))`

*)
let remove_overlapping_clauses (clauses : Il.Ast.clause list) : Il.Ast.clause list =
  let same_clause (c1 : Il.Ast.clause) (c2 : Il.Ast.clause) : bool =
    let DefD (_, args1, exp1, _) = c1.it in
    let DefD (_, args2, exp2, _) = c2.it in
    let lhs_same = Il.Eq.eq_list Il.Eq.eq_arg args1 args2 in
    let rhs_same = Il.Eq.eq_exp
                     (Il.Eval.reduce_exp !il_env exp1)
                     (Il.Eval.reduce_exp !il_env exp2)
    in
    lhs_same && rhs_same
  in
  Util.Lib.List.nub same_clause clauses



(* What top-level Lean construct `create_def` will render `def` as. This is
   the single source of truth for that classification -- comment_desc_def
   (below) and the RecD case of create_def both used to re-derive it
   independently by pattern-matching on def.it directly, which is how the
   RelD case went stale: matching def.it alone can't see that a RelD tagged
   wf-lemma-rel/wf-lemma-func renders as a Theorem, not an Inductive (that
   requires consulting the hint index, same as create_def's own RelD case
   does), so anything computing this by hand risks the same drift the old
   is_def did too -- it called any non-empty-clause DecD "Def", without
   checking whether it's actually a temporarily_axioms fallback (Opaque). *)
type top_level_construct_type =
  | AbbrevConstruct             (* TypD -> AliasT:     `abbrev X := ...` *)
  | InductiveTypeConstruct      (* TypD -> VariantT:   `inductive X where ...` *)
  | InductiveRelationConstruct  (* RelD, not a wf-lemma: `inductive X : ... -> Prop where ...` *)
  | StructureConstruct          (* TypD -> StructT:    `structure X where ...` *)
  | TypeFamilyConstruct         (* TypD, none of the above -- create_def emits no command *)
  | WfLemmaTheoremConstruct     (* RelD tagged wf-lemma-rel/wf-lemma-func: `theorem X ... := by sorry` *)
  | DefConstruct                (* DecD with clauses, not a temporarily_axioms fallback: `def X ... := ...` *)
  | OpaqueConstruct             (* DecD with no clauses, or a temporarily_axioms fallback: `opaque X ... := ...` *)
  | MutualConstruct             (* RecD: `mutual ... end` *)
  | GrammarConstruct            (* GramD -- create_def emits no command *)
  | HintConstruct               (* HintD -- carries no code-gen information *)

let get_top_level_construct_type (def : Il.Ast.def) : top_level_construct_type =
  match def.it with
  | TypD (_, _, [{it = InstD (_, _, {it = AliasT _; _}); _}]) -> AbbrevConstruct
  | TypD (_, _, [{it = InstD (_, _, {it = VariantT _; _}); _}]) -> InductiveTypeConstruct
  | TypD (_, _, [{it = InstD (_, _, {it = StructT _; _}); _}]) -> StructureConstruct
  | TypD _ -> TypeFamilyConstruct
  | RecD _ -> MutualConstruct
  | RelD (id, _, _, _, _) when
      Hint_index.has_hint (!analysis.hints) ~hint_id:Middlend.Undep.wf_rel_id id.it
      || Hint_index.has_hint (!analysis.hints) ~hint_id:Middlend.Undep.wf_func_id id.it
    -> WfLemmaTheoremConstruct
  | RelD _ -> InductiveRelationConstruct
  | DecD (id, _, _, _) when Hint_index.has_hint (!analysis.hints) ~hint_id:Backend_interpreter.Interpreter.builtin_hint_id id.it -> OpaqueConstruct
  | DecD (_, _, _, []) -> OpaqueConstruct
  | DecD _ -> DefConstruct
  | HintD _ -> HintConstruct
  | GramD _ -> GrammarConstruct

(* A short, human-readable label for what kind of top-level construct `def`
   is, mirroring the Rocq backend's `comment_desc_def` (src/backend-rocq/
   print.ml) so the two backends describe the same IL shapes the same way. *)
let comment_desc_def (def : Il.Ast.def) : string =
  match get_top_level_construct_type def with
  | AbbrevConstruct -> "Type Alias Definition"
  | InductiveTypeConstruct -> "Inductive Type Definition"
  | InductiveRelationConstruct -> "Inductive Relations Definition"
  | StructureConstruct -> "Record Creation Definition"
  | TypeFamilyConstruct -> "Type Family Definition"
  | WfLemmaTheoremConstruct -> "Well-Formedness Theorem"
  | DefConstruct -> "Auxiliary Definition"
  | OpaqueConstruct -> "Axiom Definition"
  | MutualConstruct -> "Mutual Recursion"
  | GrammarConstruct -> "Grammar Production Definition"
  | HintConstruct -> "Hint Definition"

(* `def`'s originating location in the .spectec source, as a Lean doc-comment
   ready to drop into a `decl_modifier`'s `comment` field -- e.g.
     Some "Axiom Definition at: doc/example/NanoWasm.spectec:136.1-136.30"
   The file/line/col comes straight from `def.at` (every Il.Ast.def, being a
   `phrase`, already carries this -- no whole-file analysis needed). Exposed
   standalone (rather than inlined into create_def) so the comment
   text/format can be tweaked independently of create_def's dispatch logic. *)
let create_comment (def : Il.Ast.def) : doc_comment option =
  Some (comment_desc_def def ^ " at: " ^ Util.Source.string_of_region def.at)

let create_abbrev_construct (def : Il.Ast.def) : command list =
  match def.it with
    | TypD (id, params, [{it = (InstD (quants, args, {it = AliasT t; _})); _}])
      ->
      [
        Abbrev (AbbrevAsgn {
          modifier = { empty_modifier with comment = create_comment def };
          id = id.it;
          signature = ([], Some (Type None));
          body = create_typ t;
        })
      ]
    | _ -> failwith "unreachable: get_top_level_construct_type already confirmed AbbrevConstruct"

let create_inductive_type_construct (def : Il.Ast.def) : command list =
  match def.it with
    | TypD (id, params, [{it = (InstD (quants, args, {it = VariantT ts; _})); _}])
      ->
        (* (X : Type) *)
        let create_typ_binder (quant : Il.Ast.quant) : _params
          = match quant.it with
            | TypP id -> BracketedBinder(ExplicitParam(
              NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
              Type None
            ))
            | _ -> failwith "only TypP should be here"
        in

        let deriving = deriving_of_id id in
        Inductive {
          modifier = { empty_modifier with comment = create_comment def };
          id = id.it;
          signature = (
            List.map
              create_typ_binder
              params,

            Some (Type None)
          );
          cases = List.map (create_typcase id params) ts;
          deriving;
        } :: deceq_commands_for [id.it] deriving
    | _ -> failwith "unreachable: get_top_level_construct_type already confirmed InductiveTypeConstruct"

let create_structure_construct (def : Il.Ast.def) : command list =
  match def.it with
    | TypD (id, params, [{it = (InstD (quants, args, {it = StructT ts; _})); _}])
      ->
      let create_struct_field (typfield : Il.Ast.typfield) : struct_field
        =
        let (atom, (typ, quants, prems), hints) = typfield in
        StructSimpleBinder {
          modifier = empty_modifier;
          id = Xl.Atom.to_string atom;
          signature = ([], Some (create_typ typ));
        }
      in

      let fields = List.map create_struct_field ts in

      let deriving = deriving_of_id id in
      let typ_struct : command
        = Structure {
          modifier = { empty_modifier with comment = create_comment def };
          id = id.it;
          binders = [];
          universe = None;
          constructor = Some (empty_modifier, "MK" ^ id.it); (* following previous version *)
          fields = fields;
          deriving;
        }
      in
      let deceq_cmds = deceq_commands_for [id.it] deriving in

      if not (List.mem id.it !analysis.types_needing_append_instances) then
        typ_struct :: deceq_cmds
      else
        (*
          If the type needs append instances, then create the append function,
          then the instance. For instance (hehe):

          def _append_moduleinst (arg1 arg2 : (moduleinst)) : moduleinst where
            TYPES := arg1.TYPES ++ arg2.TYPES
            FUNCS := arg1.FUNCS ++ arg2.FUNCS
            GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
            TABLES := arg1.TABLES ++ arg2.TABLES
            MEMS := arg1.MEMS ++ arg2.MEMS
            EXPORTS := arg1.EXPORTS ++ arg2.EXPORTS

          instance : Append moduleinst where
            append arg1 arg2 := _append_moduleinst arg1 arg2

        *)
        let append_func : command
          =
          
          let is_composable_field_type (typ : Il.Ast.typ) : bool
            = match typ.it with
              | IterT (_t, _) -> true
              | VarT (id, []) -> List.mem id.it !analysis.types_needing_append_instances
              | _ -> false
          in

          let all_fields_are_composable : bool
            = List.for_all (fun (_, (typ, _, _), _) -> is_composable_field_type typ) ts
          in

          if not all_fields_are_composable then
            failwith ("Cannot create append function for type " ^ id.it ^ " because not all fields are composable.")
          else

            let struct_type : term = Ident id.it in

            let arg1 : string = "arg1" in
            let arg2 : string = "arg2" in

            let create_appended_field (typfield : typfield) : struct_inst_field =
              let (atom, (typ, quants, prems), hints) = typfield in
              let field_name = Xl.Atom.to_string atom in

              let append_term_for (typ : Il.Ast.typ) (a : term) (b : term) : term =
                match typ.it with
                | IterT (_, Opt) ->
                  (* Option composition: b overrides a if present, else fall back to a *)
                  FunApp (
                    DotProj (Ident "Option", Ident "orElse"),
                    NonEmptyList.from_list_unsafe [
                      Term a;
                      Term (Lambda {
                        params = NonEmptyList.from_list_unsafe [Hole_FB];
                        body = b;
                      })
                    ]
                  )
                | IterT (_, _) ->
                  BinaryInfixFunApp (Term a, Ident "++", Term b)   (* List/List1/ListN *)
                | VarT _ ->
                  BinaryInfixFunApp (Term a, Ident "++", Term b)   (* nested composable struct *)
                | _ -> failwith "unreachable — is_composable_field_type already checked"
              in

              AssignedField {
                l_val = Ident_SILV (create_atom atom);
                is_private = false;
                term = append_term_for typ
                  (DotProj (Ident arg1, Ident field_name))
                  (DotProj (Ident arg2, Ident field_name));
              }
            in

            let appended_fields : struct_inst_field list = List.map create_appended_field ts in
          
            Def (
              DefStruct {
                modifier = { empty_modifier with comment = create_comment def };
                id = "append_" ^ id.it;
                signature = (
                  [
                    BracketedBinder(ExplicitParam(
                      NonEmptyList.from_list_unsafe [Ident_IOH arg1; Ident_IOH arg2],
                      struct_type
                    ));
                  ],
                  Some (struct_type)
                );
                body = appended_fields
              }
            )

          

        in

        let append_instance : command =
          Instance {
            modifier = { empty_modifier with comment = create_comment def };
            priority = None;
            id = None;
            signature = (
              [],
              FunApp (
                Ident "Append",
                NonEmptyList.from_list_unsafe [
                  Term (Ident id.it)
                ]
              )
            );
            body = [
              AssignedField {
                l_val = Ident_SILV "append";
                is_private = false;
                term = Ident ("append_" ^ id.it); (* TODO: refactor append_ - making id function *)
              }
            ]
          }
        in

        [typ_struct]
        @ deceq_cmds
        @ [
          append_func;
          append_instance;
        ]
    | _ -> failwith "unreachable: get_top_level_construct_type already confirmed StructureConstruct"

let create_wf_lemma_theorem_construct (def : Il.Ast.def) : command list =
  match def.it with
    | RelD (
        id,     (* fun_sum *)
        quants,     (* undep should get rid of params, so this should be empty *)
        mixop,
        typ,    (* (TupT (typbind "_" (IterT nat List)) (typbind "_" nat)) *)
        rules   (* (RuleD "fun_sum_case_0" (Seq Arg Arg) (TupE (ListE) (NumE (Nat 0)))) *)
      )
      ->
        (*

        This code supports the hack from undep where a lemma is smuggled in as
        an inductive type in IL

        Creates something like:

        theorem fzero_is_wf (v_N : N) (ret_val : fN) :
          ret_val = (fzero v_N) →
          wf_fN v_N ret_val
          
          := by sorry

        *)

        let is_axiom =
          (* omg I need to look up monadic stuff in ocaml when I have time *)
          let wf_rel_hint = Hint_index.get_hint !analysis.hints ~hint_id:Middlend.Undep.wf_rel_id id.it  in
          let wf_func_hint = Hint_index.get_hint !analysis.hints ~hint_id:Middlend.Undep.wf_func_id id.it in
          let wf_rel_is_axiom = Option.map (fun (h:hint) -> h.hintexp.it = BoolE true) wf_rel_hint in
          let wf_func_is_axiom = Option.map (fun (h:hint) -> h.hintexp.it = BoolE true) wf_func_hint in
          (* let _ = Printf.printf "%b, %b, %b, %b\n"  in *)
          List.exists (fun (e : bool option) -> e = Some true) [wf_rel_is_axiom; wf_func_is_axiom]
        in

        let rule = match rules with
          | [rule] -> rule
          | _ -> failwith "wf-lemma relation should have exactly one rule"
        in

        let RuleD (
          rule_id,      (* fzero_is_wf_0 *)
          rule_quants,  (*
                          (ExpP "v_N" (VarT "N"))
                          (ExpP "ret_val" (VarT "fN"))
                        *)
          rule_mixop,   (* (Seq Arg Arg) *)
          rule_exp,     (* (TupE (VarE "v_N") (VarE "ret_val")) *)
          rule_prems    (*
                          (IfPr (CmpE EqOp bool (VarE "ret_val") (CallE "fzero" (ExpA (VarE "v_N")))))
                          (RulePr "wf_fN" (Seq Arg Arg) (TupE (VarE "v_N") (VarE "ret_val")))
                        *)
        ) = rule.it
        in

        let signature = (
          List.map (fun q -> match q.it with
            | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
                create_typ typ
              ))
            | TypP id -> BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
                Type None
              ))
            (* A higher-order function quantifier (e.g. the wf-lemma for a
                function like fvunop_ that itself takes a callback
                f_ : N -> fN -> List fN). Mirrors the DefP case in the
                ordinary (non-lemma) signature builder just below, and
                Rocq's render_param_type (src/backend-rocq/print.ml),
                which renders the same DefP as a curried function type. *)
            | DefP (id, params, typ) ->
              let param_types = List.map (fun p -> match p.it with
                | ExpP (_, typ) -> create_typ typ
                | _ -> failwith "only ExpP should be here"
              ) params in
              BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
                create_curried_func (param_types @ [create_typ typ])
              ))
            | _ -> failwith "only ExpP, TypP, and DefP should be here"
          ) rule_quants,

          (* The last premise is the theorem's actual conclusion (e.g.
              `wf_fN v_N ret_val`); everything before it is a hypothesis
              the theorem assumes (e.g. `ret_val = fzero v_N`). Premises
              renders the last element as the conclusion (no arrow). *)
          Premises (List.map create_prem rule_prems)
        )
      in

      if is_axiom then
        [
          Axiom {
            id = id.it;
            signature = signature;
          }
        ]
      else

        [
          Theorem {
            modifier = { empty_modifier with comment = create_comment def };
            id = id.it;
            signature = signature;
            proof = Sorry;
          }
        ]
    | _ -> failwith "unreachable: get_top_level_construct_type already confirmed WfLemmaTheoremConstruct"

let create_inductive_relation_construct (def : Il.Ast.def) : command list =
  match def.it with
    | RelD (
        id,     (* fun_sum *)
        quants,     (* undep should get rid of params, so this should be empty *)
        mixop,
        typ,    (* (TupT (typbind "_" (IterT nat List)) (typbind "_" nat)) *)
        rules   (* (RuleD "fun_sum_case_0" (Seq Arg Arg) (TupE (ListE) (NumE (Nat 0)))) *)
      )
      ->
      (*
        Taking the example of
      
        inductive fun_sum : List Nat → Nat → Prop where
          | fun_sum_case_0 : fun_sum [] 0
          | fun_sum_case_1 (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) :
              fun_sum n'_lst var_0 →
              fun_sum ([v_n] ++ n'_lst) (v_n + var_0)
      *)

      (* Which of this relation's TypP names need [BEq X] / [Inhabited X] instance
         binders -- computed globally by Whole_file_analyses.analyze_typp_needs
         (extended to also walk RelD rules and RulePr premises, see that file).
         Keyed by this RelD's own id (e.g. "fun_disjoint_"), already the
         fun_-prefixed final-IL name -- identical lookup to create_def_construct's. *)
      let typp_names_needing_beq : string list =
        List.assoc_opt id.it (!analysis).defs_needing_beq
        |> Option.value ~default:[]
      in
      let typp_names_needing_inhabited : string list =
        List.assoc_opt id.it (!analysis).defs_needing_inhabited
        |> Option.value ~default:[]
      in

      let signature : _params list (* (f_ : N → iN → iN) *)
        = List.concat_map (
          fun q -> match q.it with
            | DefP (id, params, typ) ->
              let param_types = List.map (fun p -> match p.it with
                | ExpP (_, typ) -> create_typ typ
                | _ -> failwith "only ExpP should be here"
              ) params in
              [BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
                (* create_typ typ *)
                create_curried_func (param_types @ [create_typ typ])
              ))]
            | TypP t ->
              let explicit : _params = BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH t.it],
                Type None                                                 (* (X : Type) -- always emitted *)
              )) in
              let beq : _params list =
                if List.mem t.it typp_names_needing_beq then
                  [BracketedBinder(InstanceParam(                         (* [BEq X] *)
                    FunApp(Ident "BEq", NonEmptyList.from_list_unsafe [Term (Ident t.it)])
                  ))]
                else []
              in
              let inhabited : _params list =
                if List.mem t.it typp_names_needing_inhabited then
                  [BracketedBinder(InstanceParam(                         (* [Inhabited X] *)
                    FunApp(Ident "Inhabited", NonEmptyList.from_list_unsafe [Term (Ident t.it)])
                  ))]
                else []
              in
              [explicit] @ beq @ inhabited
            | _ -> failwith "only DefP and TypP should be here"
        ) quants
      in

      (* TODO: This might be duplicated logic *)
      let create_relations_inductive_type (typ : Il.Ast.typ) : term
        (* List Nat → Nat → Prop *)
        = match typ.it with
          | VarT _ | BoolT | NumT _ | TextT | IterT _ -> FunType (create_typ typ, Ident "Prop")
          | TupT [] -> Ident "Prop"
          | TupT id_typ_list ->
            let types = List.map (fun (_, typ) -> create_typ typ) id_typ_list in
            let types_and_prop = types @ [Ident "Prop"] in
            create_curried_func types_and_prop
      in

      let create_relations_inductive_case
        (rule : Il.Ast.rule)
        (rel_id : Il.Ast.id)
        (quants_from_parent : Il.Ast.quant list)
        : _inductive_case
        (*
          | fun_sum_case_1 (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) :
                fun_sum n'_lst var_0 →
                fun_sum ([v_n] ++ n'_lst) (v_n + var_0)
        *)
        = match rule.it with
          | RuleD (
              id,     (* fun_sum_case_1 *)
              quants, (*
                        (ExpP "v_n" nat)
                        ...
                      *)
              mixop,
              exp,    (*
                        (TupE
                          (CatE (ListE (VarE "v_n")) (VarE "n'_lst"))
                          (BinE AddOp nat (VarE "v_n") (VarE "var_0"))
                        )
                        ...
                      *)
              prems   (* (RulePr "fun_sum" (Seq Arg Arg) (TupE (VarE "n'_lst") (VarE "var_0"))) *)
            )
            ->
            let quant_id (q : Il.Ast.quant) : string
              = match q.it with
                | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _, _) -> id.it
            in
            let parent_ids : string list = List.map quant_id quants_from_parent in
            let quants_not_in_parent : quant list (* (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) *)
              (* Quantifiers already declared by the enclosing RelD's own header
                 (e.g. a relation's `syntax X` parameter) must not be redeclared
                 per-case: Lean auto-generalizes an inductive's own parameters into
                 every constructor, so redeclaring them here would just shadow the
                 real one with an unused, dangling binder of the same name. *)
              = List.filter (fun q -> not (List.mem (quant_id q) parent_ids)) quants
            in
            let params_from_args : _params list (* (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) *)
              =

              let param_from_arg (q : Il.Ast.quant) : _params option
                = match q.it with
                  | ExpP (id, typ) -> Some(BracketedBinder(ExplicitParam(
                      NonEmptyList.from_list_unsafe [Ident_IOH id.it;], (* TODO: disambiguate Ident *)
                      create_typ typ
                    )))
                  | TypP id -> Some(BracketedBinder(ExplicitParam(
                      NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
                      Type None
                    )))
                  | DefP _ -> None
                  | _ -> failwith "only ExpP should be here"
              in
              List.filter_map param_from_arg quants_not_in_parent
            in

            let exp_with_rel_id_prepended : term (* fun_sum ([v_n] ++ n'_lst) (v_n + var_0) *)
              = let mixop_args : term list
                  = match exp.it with
                    | TupE exps -> List.map create_exp exps
                    | _ -> [create_exp exp]
                in
                (* Lean 4 parametric inductives require parameters to appear explicitly in
                   constructor conclusions: `Foo a b` not just `Foo b`. Prepend the
                   enclosing RelD's own TypP/DefP parameter ids, in their declared
                   order - Lean does not auto-omit inductive parameters from
                   conclusions.
                   e.g. for `inductive fun_concat_ (X : Type) : ... where`, this
                   turns the conclusion `fun_concat_ ([w_lst] ++ w'_lst_lst) (w_lst ++ var_0)`
                   into `fun_concat_ X ([w_lst] ++ w'_lst_lst) (w_lst ++ var_0)`. *)
                let parent_param_args : term list
                  = List.filter_map (fun (q : Il.Ast.quant) -> match q.it with
                      | DefP (id, _, _) | TypP id -> Some (Ident id.it : term)
                      | _ -> None
                    ) quants_from_parent
                in
                let id_as_term = (Ident rel_id.it : term) in
                FunApp (
                  id_as_term,
                  NonEmptyList.from_list_unsafe (List.map (fun arg -> Term arg) (parent_param_args @ mixop_args))
                )
            in
            
            {
              modifier = empty_modifier;
              (* Prepend the relation's own name only to cases whose bare id
                 actually collides with a same-named case in a sibling
                 relation of the same `mutual` block (see
                 Whole_file_analyses.gather_colliding_relation_case_names):
                 Lean's `induction ... using` resolves alternative field
                 counts by a bare, unqualified constructor-name lookup across
                 the *whole* mutual group, so a same-named constructor in
                 another type silently shadows this one (test-lean/bug.lean).
                 Leaving non-colliding cases untouched avoids renaming the
                 vast majority of cases that are already unique. *)
              id =
                (let this_rel_collisions =
                   List.assoc_opt rel_id.it (!analysis).colliding_relation_case_names
                   |> Option.value ~default:[]
                 in
                 if List.mem id.it this_rel_collisions
                 then rel_id.it ^ "_" ^ id.it  (* Instrs_ok_frame *)
                 else id.it);
              signature = (
                params_from_args,         (* (v_n : Nat) (n'_lst : List Nat) (var_0 : Nat) *)

                (*
                    fun_sum n'_lst var_0 →
                    fun_sum ([v_n] ++ n'_lst) (v_n + var_0)
                *)
                Some (
                  append_prems_to_prop
                    exp_with_rel_id_prepended
                    prems
                )
              );
            }

      in

      (* let () = Printf.eprintf "DEBUG create_relations_inductive_type: %s  typ=%s\n%!" id.it (Il.Print.string_of_typ typ) in *)
      [
        Inductive {
          modifier = { empty_modifier with comment = create_comment def };
          id = id.it;                       (* fun_sum *)
          signature = (
            signature,
            Some (create_relations_inductive_type typ)   (* List Nat → Nat → Prop *)
          );
          cases = List.map (fun rule -> create_relations_inductive_case rule id quants) rules;
          deriving = deriving_of_id id;
        }
      ]
    | _ -> failwith "unreachable: get_top_level_construct_type already confirmed InductiveRelationConstruct"

let create_def_construct (def : Il.Ast.def) : command list =
  match def.it with
    | DecD (
      id,                               (* "Ki" *)
      [],                               (* This handles the case with no params *)
      typ,                              (* nat *)
      [{it = DefD ([], [], exp, []); _}]    (* (NumE (Nat 1024)) *)
    )

    (*
      Let's say we have a definition like

      def $Ki : nat
      def $Ki = 1024

      We want to generate a Lean4 definition like

      def Ki : Nat := 1024
    *)
      ->
      [
        Def (DefAsgn {
          modifier = { empty_modifier with comment = create_comment def };
          id = id.it;                               (* "Ki" *)
          signature = (
            [],
            Some (create_typ typ)                   (* Nat *)
          );
          body = create_exp exp;                    (* 1024 *)
        })
      ]


    | DecD (
      id,     (* "local" *)
      params, (*
                (ExpP "v_state" (VarT "state"))
                (ExpP "v_localidx" (VarT "localidx"))
              *)
      typ,    (* (VarT "val") *)
      clauses (*
                (DecD
                  "local"
                  (ExpP "v_state" (VarT "state"))
                  (ExpP "v_localidx" (VarT "localidx"))
                  (VarT "val")
                  (DefD
                    (ExpP "s" (VarT "store"))
                    (ExpP "f" (VarT "frame"))
                    (ExpP "x" nat)
                    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
                    (ExpA (VarE "x"))
                    (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x"))
                  )
                )
              *)
    ) ->
      (*
        Let's say we have a definition like

        /- Auxiliary Definition at: doc/example/NanoWasm.spectec:82.1-82.34 -/
        def «local» (v_state : state) (v_localidx : localidx) : val :=
          match v_state with
          | .mk_state s f => ((f.LOCALS)[v_localidx]!)

        corresponding to IL AST

        (DecD
          "local"
          (ExpP "v_state" (VarT "state"))
          (ExpP "v_localidx" (VarT "localidx"))
          (VarT "val")
          (DefD
            (ExpP "s" (VarT "store"))
            (ExpP "f" (VarT "frame"))
            (ExpP "x" nat)
            (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
            (ExpA (VarE "x"))
            (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x"))
          )
        )

      *)


      (* Which of this function's TypP names need [BEq X] / [Inhabited X] instance binders.
         Both are computed globally by whole_file_analyses before code generation starts.
         e.g. setminus1_: typp_names_needing_beq=["X"], typp_names_needing_inhabited=[]
              fun_relaxed2: typp_names_needing_beq=[], typp_names_needing_inhabited=["r_X"] *)
      let typp_names_needing_beq : string list =
        List.assoc_opt id.it (!analysis).defs_needing_beq
        |> Option.value ~default:[]
      in
      let typp_names_needing_inhabited : string list =
        List.assoc_opt id.it (!analysis).defs_needing_inhabited
        |> Option.value ~default:[]
      in

      let signature : opt_decl_sig (* (v_state : state) (v_localidx : localidx) : val *)
        =
          let params_as_binders : _params list
            (* Each TypP emits (X : Type) always, then [BEq X] and/or [Inhabited X] as needed.
               e.g. setminus1_'s TypP "X" → [(X : Type); [BEq X]]
                    fun_relaxed2's TypP "r_X" → [(r_X : Type); [Inhabited r_X]]
               ExpP and DefP each emit exactly one binder. *)
            = List.concat_map (
              fun p -> match p.it with
                | TypP t ->
                  let explicit : _params = BracketedBinder(ExplicitParam(
                    NonEmptyList.from_list_unsafe [Ident_IOH t.it],
                    Type None                                                (* (X : Type) -- always emitted *)
                  )) in
                  let beq : _params list =
                    if List.mem t.it typp_names_needing_beq then
                      [BracketedBinder(InstanceParam(                        (* [BEq X] -- e.g. for setminus1_ *)
                        FunApp(Ident "BEq", NonEmptyList.from_list_unsafe [Term (Ident t.it)])
                      ))]
                    else []
                  in
                  let inhabited : _params list =
                    if List.mem t.it typp_names_needing_inhabited then
                      [BracketedBinder(InstanceParam(                        (* [Inhabited X] -- e.g. for fun_relaxed2 *)
                        FunApp(Ident "Inhabited", NonEmptyList.from_list_unsafe [Term (Ident t.it)])
                      ))]
                    else []
                  in
                  [explicit] @ beq @ inhabited
                | ExpP (id, typ) -> [BracketedBinder(ExplicitParam(
                  NonEmptyList.from_list_unsafe [Ident_IOH id.it;], (* (var_0_lst : List X) *)
                  create_typ typ
                ))]
                | DefP (
                    id,
                    params,
                    typ
                  ) ->
                  let param_types = List.map (fun p -> match p.it with
                    | ExpP (_, typ) -> create_typ typ
                    | _ -> failwith "only ExpP should be here"
                  ) params in
                  [
                    (* (f_ : N → iN → iN) *)
                    BracketedBinder(ExplicitParam(
                      NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
                      create_curried_func (param_types @ [create_typ typ])
                    ))
                  ]
                | _ -> error p.at ("only ExpP or TypP should be here 2, got: " ^ Il.Print.string_of_param p)
            ) params
          in

          params_as_binders,
          Some (create_typ typ) (* val *)
      in

      (* Drop clauses that middlend/subexpansion.ml's per-clause type-family
         expansion left overlapping with an earlier clause (see
         remove_overlapping_clauses above) before any match-arm generation
         below sees them, so e.g. cunpack never gets a duplicate
         `storagetype.I32` arm. *)
      let clauses = remove_overlapping_clauses clauses in

      (* type param_match_arm_binding_state =
        | NeverDeconstructed
        | DeconstructedAtLeastOnce
        |  *)

      (* let check_params_ever_deconstructed
        (params : Il.Ast.quant list)  (*
                                        (ExpP "v_state" (VarT "state"))
                                        (ExpP "v_localidx" (VarT "localidx"))
                                      *)
        (clause : Il.Ast.clause)
        : bool list =

        let DefD (
          _,
          args,     (*
                      corr. to v_state    ---- (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
                      corr. to v_localidx ---- (ExpA (VarE "x"))
                    *)
          _,
          _
        ) = clause.it
        in

        List.map2
          (fun param arg ->
            match param.it, arg.it with
              | ExpP (param_id, _), ExpA (VarE arg_id) -> false
              | TypP _, TypA _ -> false
              | _, _ -> failwith "unexpected param/arg combination"
          )
          params
          args

      in *)

      let is_deconstruction (arg : Il.Ast.arg) : bool =
        match arg.it with
          | ExpA {it = VarE _; _} -> false
          | ExpA _ -> true
          | TypA {it = VarT _; _} -> false
          | TypA _ -> true
          | DefA _ -> false
          | _ -> failwith ("only ExpA or TypA should be here" ^ Il.Print.string_of_arg arg)
      in

      let clause_deconstruction_list (clause : Il.Ast.clause) : bool list =
        let DefD (
          _,
          args,     (*
                      corr. to v_state    ---- (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
                      corr. to v_localidx ---- (ExpA (VarE "x"))
                    *)
          _,
          _
        ) = clause.it
        in
        List.map is_deconstruction args
      in

      let all_clauses_deconstruction_list : bool list list =
        List.map clause_deconstruction_list clauses
      in

      let param_ever_deconstructed_list : bool list =
        List.fold_left
          (List.map2 (fun acc decon -> acc || decon))
          (List.init (List.length params) (fun _ -> false))
          all_clauses_deconstruction_list
      in

      
      
      (* TODO: see if we should / can remove unnecessary components of match term *)
      let create_clause
        (*
          | .mk_state s f => ((f.LOCALS)[v_localidx]!)
        *)
        (clause : Il.Ast.clause)
        (params_from_parent : Il.Ast.quant list)   (*
                                              (ExpP "v_state" (VarT "state"))
                                              (ExpP "v_localidx" (VarT "localidx"))
                                            *)
        (param_ever_deconstructed_list : bool list)  (*
                                              [true; false]
                                            *)
        : term list * term =

          let DefD (
            quants,   (*
                        (ExpP "s" (VarT "store"))
                        (ExpP "f" (VarT "frame"))
                        (ExpP "x" nat)
                      *)
            args,     (*
                        corr. to v_state    ---- (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
                        corr. to v_localidx ---- (ExpA (VarE "x"))
                      *)
            exp,      (* (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x")) *)
            prems
          ) = clause.it in

          let args_deconstructed_in_at_least_one_clause : arg list =
            let pairs = List.combine args param_ever_deconstructed_list in
            let remaining
              = List.filter_map (fun (arg, ever_deconstructed) ->
                if ever_deconstructed then Some arg else None
              ) pairs
            in
            remaining
          in

          let arg_to_lhs_pattern (* .mk_state s f *)
            ~(is_passthrough : bool)
            (arg : Il.Ast.arg)
            : term
            = if is_passthrough then Hole Hole
              else match arg.it with
              | TypA ({it = VarT (x, []); _} as t) -> create_typ t
              | TypA _ -> failwith "only VarT should be here"
              | ExpA exp -> (
                match exp.it with
                  | CatE (exp1, exp2) ->
                    (* CatE (ListE [e], rest) in IL means [e] ++ rest = e :: rest.
                       Unwrap the singleton ListE so the pattern binds the element,
                       not a singleton list containing it. *)
                    let head_pat = match exp1.it with
                      | ListE [e] -> create_exp e
                      | _ -> create_exp exp1
                    in
                    BinaryInfixFunApp (
                      Term head_pat,
                      Ident "::",
                      Term (create_exp exp2)
                    )
                  | IterE (exp, _) -> create_exp exp
                  | _ -> create_exp exp
              )
              | _ -> failwith "only TypA or ExpA should be here"
          in

          let args_deconstructed_in_other_clauses_but_not_here : arg list =

            let args_that_are_not_deconstructed_here : arg list =
              List.filter
                (fun arg -> not (is_deconstruction arg))
                args
            in

            List.filter
              (* TODO: Check if structural equality works here *)
              (fun arg -> List.mem arg args_deconstructed_in_at_least_one_clause)
              args_that_are_not_deconstructed_here
          in

          (*
            [
              (
                (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f")))),
                (ExpP "v_state" (VarT "state"))
              );
              (
                (ExpA (VarE "x")),
                (ExpP "v_localidx" (VarT "localidx"))
              )
            ]
          *)
          let args_to_original_names_substs : (arg * quant) list =
            List.combine args params_from_parent
          in

          (* [("x", "v_localidx")] -- corr. to v_localidx via args_to_original_names_substs *)
          let substs : (string * string) list =

            (* Rename every non-deconstructed (pass-through VarE) arg to its parent param name.
               This covers two scenarios:
               1. Pass-through in THIS clause, deconstructed in another clause:
                  e.g.  clause A: ((s;f), Foo x)  clause B: ((s;f), y)  =>  rename "y"->"v_thing"
               2. Pass-through everywhere, but the match is on a DIFFERENT param:
                  e.g.  fun_type (v_state, v_typeidx): clause ((s;f), x) matches only v_state,
                  leaving "x" unbound in the arm body without this rename. *)
            let substs_arg_to_quant : (arg * quant) list =
              List.filter
                (fun (arg, _) -> not (is_deconstruction arg))
                args_to_original_names_substs
            in

            List.filter_map
              (fun (arg, quant) -> match arg.it, quant.it with
                | ExpA {it = VarE id; _}, ExpP (qid, _) -> Some (id.it, qid.it)
                | TypA {it = VarT (id, []); _}, TypP qid -> Some (id.it, qid.it)
                | _ -> None
              )
              substs_arg_to_quant

          in

          let subst_func (id : string) : string =
            try List.assoc id substs
            with Not_found -> id
          in

          let rename_il_vars (subst_func : string -> string) (exp : Il.Ast.exp) : Il.Ast.exp =

            let t = { Il.Walk.base_transformer with
              transform_var_id = fun id -> { id with it = subst_func id.it }
            } in

            Il.Walk.transform_exp t exp
          in

          let renamed_exp = rename_il_vars subst_func exp in

          (* TODO: refactor to avoid spamming transformers *)
          let rename_transformer = { Il.Walk.base_transformer with
            transform_var_id = fun id -> { id with it = subst_func id.it }
          } in
          let renamed_prems = List.map (Il.Walk.transform_prem rename_transformer) prems in

          List.map
            (fun arg ->
              let is_passthrough = List.mem arg args_deconstructed_in_other_clauses_but_not_here in
              arg_to_lhs_pattern ~is_passthrough arg
            )
            args_deconstructed_in_at_least_one_clause,
            append_prems_to_term (create_exp renamed_exp) renamed_prems
      in


      let create_match_term
        (params_from_parent : Il.Ast.quant list)   (*
                                              (ExpP "v_state" (VarT "state"))
                                              (ExpP "v_localidx" (VarT "localidx"))
                                            *)
        (param_ever_deconstructed_list : bool list)
        : term list
        =
        List.filter_map (fun (p, keep) ->
          if not keep then None
          else Some (match p.it with
            | ExpP (id, _) -> (Ident id.it : term)
            | TypP id      -> (Ident id.it : term)
            | _ -> error p.at ("only ExpP or TypP should be here 3, got: " ^ Il.Print.string_of_param p)
          )
        ) (List.combine params_from_parent param_ever_deconstructed_list)
      in

      let match_terms = create_match_term params param_ever_deconstructed_list in
      let cases = List.map (fun clause -> create_clause clause params param_ever_deconstructed_list) clauses in

      let body =
        if match_terms = [] then
          (*
            No param was ever deconstructed — no match needed.
            Emit the body of the (single) clause directly.

            Example: def min (nat : Nat) (nat_0 : Nat) : Nat :=
                       if nat ≤ nat_0 then nat else nat_0

            create_clause's substs covers scenario 3 (pass-through here, deconstructed
            elsewhere). When match_terms = [], nothing is deconstructed anywhere, so
            substs = [] and the clause body still uses clause-local names (e.g. "i", "j").
            We apply a full rename of all pass-through args to outer param names here.
          *)
          let DefD (_, clause_args, clause_exp, clause_prems) = (List.hd clauses).it in
          (* [("i", "nat"); ("j", "nat_0")] *)
          let full_substs : (string * string) list =
            List.filter_map (fun (arg, quant) ->
              match arg.it, quant.it with
              (* clause uses "i" for outer param "nat" -- rename "i" -> "nat" *)
              | ExpA {it = VarE id; _}, ExpP (qid, _) when id.it <> qid.it ->
                Some (id.it, qid.it)
              (* clause uses type var "X" for outer TypP "X'" -- rename if different *)
              | TypA {it = VarT (id, []); _}, TypP qid when id.it <> qid.it ->
                Some (id.it, qid.it)
              | _ -> None
            ) (List.combine clause_args params)
          in
          let subst_func id = try List.assoc id full_substs with Not_found -> id in
          let t = { Il.Walk.base_transformer with
            transform_var_id = fun id -> { id with it = subst_func id.it }
          } in
          (* if nat ≤ nat_0 then nat else nat_0  (after renaming i->nat, j->nat_0) *)
          let renamed = Il.Walk.transform_exp t clause_exp in
          let renamed_prems = List.map (Il.Walk.transform_prem t) clause_prems in
          append_prems_to_term (create_exp renamed) renamed_prems
        else
          Match { match_terms; cases = cases }
      in

      [
        Def (DefAsgn {
          modifier = { empty_modifier with comment = create_comment def };
          id = id.it;
          signature = signature;
          body;
        })
      ]
    | _ -> failwith "unreachable: get_top_level_construct_type already confirmed DefConstruct"

let create_opaque_construct (def : Il.Ast.def) : command list =
  match def.it with
    | DecD (
      id,       (* "float" *)
      params,   (*
                  (ExpP "nat" nat)
                  (ExpP "var_0" (IterT nat List))
                *)
      typ,      (* (VarT "const") *)
      []
    ) ->
      (*
        Let's say we have a definition like

        /- Axiom Definition at: doc/example/NanoWasm.spectec:136.1-136.30 -/
        opaque float (nat : Nat) (var_0 : (List Nat)) : const := opaqueDef

        corresponding to IL AST

        (DecD
          "float"
          (ExpP "nat" nat)
          (ExpP "var_0" (IterT nat List))
          (VarT "const")
          []
        )
      *)
      let signature : decl_sig (* (nat : Nat) (var_0 : (List Nat)) : const *)
        =
          List.map (
            fun p -> match p.it with
              | TypP t -> BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH t.it;], (* (X : Type) *)
                Type None
              ))
              | ExpP (id, typ) -> BracketedBinder(ExplicitParam(
                NonEmptyList.from_list_unsafe [Ident_IOH id.it;], (* (v_state : state) *)
                create_typ typ
              ))
              | _ -> error p.at ("only ExpP or TypP should be here 1, got: " ^ Il.Print.string_of_param p)
          ) params,
          create_typ typ

          
      in
      [
        Opaque {
          modifier = { empty_modifier with comment = create_comment def };
          id = id.it;                               (* "float" *)
          signature = signature;
          rhs = Some opaque_def;
        }
      ]
    (* | DecD (id, [], typ, clauses)
      -> None *)

      

    | DecD (
      id,     (* "local" *)
      params, (*
                (ExpP "v_state" (VarT "state"))
                (ExpP "v_localidx" (VarT "localidx"))
              *)
      typ,    (* (VarT "val") *)
      clauses (*
                (DecD
                  "local"
                  (ExpP "v_state" (VarT "state"))
                  (ExpP "v_localidx" (VarT "localidx"))
                  (VarT "val")
                  (DefD
                    (ExpP "s" (VarT "store"))
                    (ExpP "f" (VarT "frame"))
                    (ExpP "x" nat)
                    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
                    (ExpA (VarE "x"))
                    (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x"))
                  )
                )
              *)
    ) ->
      (*
        Let's say we have a definition like

        /- Auxiliary Definition at: doc/example/NanoWasm.spectec:82.1-82.34 -/
        def «local» (v_state : state) (v_localidx : localidx) : val :=
          match v_state with
          | .mk_state s f => ((f.LOCALS)[v_localidx]!)

        corresponding to IL AST

        (DecD
          "local"
          (ExpP "v_state" (VarT "state"))
          (ExpP "v_localidx" (VarT "localidx"))
          (VarT "val")
          (DefD
            (ExpP "s" (VarT "store"))
            (ExpP "f" (VarT "frame"))
            (ExpP "x" nat)
            (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
            (ExpA (VarE "x"))
            (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x"))
          )
        )

      *)


      (* Which of this function's TypP names need [BEq X] / [Inhabited X] instance binders.
         Both are computed globally by whole_file_analyses before code generation starts.
         e.g. setminus1_: typp_names_needing_beq=["X"], typp_names_needing_inhabited=[]
              fun_relaxed2: typp_names_needing_beq=[], typp_names_needing_inhabited=["r_X"] *)
      let typp_names_needing_beq : string list =
        List.assoc_opt id.it (!analysis).defs_needing_beq
        |> Option.value ~default:[]
      in
      let typp_names_needing_inhabited : string list =
        List.assoc_opt id.it (!analysis).defs_needing_inhabited
        |> Option.value ~default:[]
      in

      let signature : opt_decl_sig (* (v_state : state) (v_localidx : localidx) : val *)
        =
          let params_as_binders : _params list
            (* Each TypP emits (X : Type) always, then [BEq X] and/or [Inhabited X] as needed.
               e.g. setminus1_'s TypP "X" → [(X : Type); [BEq X]]
                    fun_relaxed2's TypP "r_X" → [(r_X : Type); [Inhabited r_X]]
               ExpP and DefP each emit exactly one binder. *)
            = List.concat_map (
              fun p -> match p.it with
                | TypP t ->
                  let explicit : _params = BracketedBinder(ExplicitParam(
                    NonEmptyList.from_list_unsafe [Ident_IOH t.it],
                    Type None                                                (* (X : Type) -- always emitted *)
                  )) in
                  let beq : _params list =
                    if List.mem t.it typp_names_needing_beq then
                      [BracketedBinder(InstanceParam(                        (* [BEq X] -- e.g. for setminus1_ *)
                        FunApp(Ident "BEq", NonEmptyList.from_list_unsafe [Term (Ident t.it)])
                      ))]
                    else []
                  in
                  let inhabited : _params list =
                    if List.mem t.it typp_names_needing_inhabited then
                      [BracketedBinder(InstanceParam(                        (* [Inhabited X] -- e.g. for fun_relaxed2 *)
                        FunApp(Ident "Inhabited", NonEmptyList.from_list_unsafe [Term (Ident t.it)])
                      ))]
                    else []
                  in
                  [explicit] @ beq @ inhabited
                | ExpP (id, typ) -> [BracketedBinder(ExplicitParam(
                  NonEmptyList.from_list_unsafe [Ident_IOH id.it;], (* (var_0_lst : List X) *)
                  create_typ typ
                ))]
                | DefP (
                    id,
                    params,
                    typ
                  ) ->
                  let param_types = List.map (fun p -> match p.it with
                    | ExpP (_, typ) -> create_typ typ
                    | _ -> failwith "only ExpP should be here"
                  ) params in
                  [
                    (* (f_ : N → iN → iN) *)
                    BracketedBinder(ExplicitParam(
                      NonEmptyList.from_list_unsafe [Ident_IOH id.it;],
                      create_curried_func (param_types @ [create_typ typ])
                    ))
                  ]
                | _ -> error p.at ("only ExpP or TypP should be here 2, got: " ^ Il.Print.string_of_param p)
            ) params
          in

          params_as_binders,
          Some (create_typ typ) (* val *)
      in

        [
          Opaque {
            modifier = { empty_modifier with comment = create_comment def };
            id = id.it;
            signature = (fst signature, Option.get (snd signature));
            rhs = Some opaque_def;
          }
        ]
    | _ -> failwith "unreachable: get_top_level_construct_type already confirmed OpaqueConstruct"

let rec create_mutual_construct (def : Il.Ast.def) : command list =
  match def.it with
      | RecD defs ->
        (
          (* HintD entries carry no code-gen information; strip them before
            length-checking or categorizing the remaining members. *)
          let defs = List.filter (fun d -> match d.it with HintD _ -> false | _ -> true) defs in
          (* A RelD tagged wf-lemma-rel/wf-lemma-func is rendered above (in the
            RelD case of create_def) as a standalone `theorem ... := by sorry`,
            not an inductive -- and it isn't mutually recursive with its
            siblings, so it doesn't need to live inside a `mutual` block at
            all. Pull these out before classifying the rest of the group:
            left in, `is_inductive` below treats every RelD as inductive
            regardless of the hint, so a wf-lemma RelD gets bundled into
            `all_inductive_or_structure`'s `defs`, `create_def def` for it
            returns `[Theorem _]` (not `[Inductive _]`), and the
            `filter_map` below silently drops it -- producing a `mutual ...
            end` with nothing between when a whole group is wf-lemma RelD's
            (e.g. free_heaptype_is_wf and its siblings). *)
          let is_wf_lemma = fun def -> get_top_level_construct_type def = WfLemmaTheoremConstruct in
          let wf_lemma_defs, defs = List.partition is_wf_lemma defs in
          let wf_lemma_theorems = List.concat_map create_def wf_lemma_defs in
          wf_lemma_theorems @
          (match List.length defs with
            | 0 -> []
            | 1 -> create_def (List.hd defs)
            | _ ->
              let is_inductive = fun def -> match get_top_level_construct_type def with
                | InductiveRelationConstruct | InductiveTypeConstruct -> true
                | _ -> false
              in
              let is_structure = fun def -> get_top_level_construct_type def = StructureConstruct in
              let is_def = fun def -> get_top_level_construct_type def = DefConstruct in
              let is_abbrev = fun def -> get_top_level_construct_type def = AbbrevConstruct in
              let all_inductive_or_structure = List.for_all (fun def -> is_inductive def || is_structure def) defs in
              let all_abbrev_or_def = List.for_all (fun def -> is_abbrev def || is_def def) defs in
              (
                match all_inductive_or_structure, all_abbrev_or_def with
                  | true, _ ->
                    (* Every member's `deriving` clause is already correct as
                       computed by [create_def] -- genuine multi-type mutual
                       recursion is folded into [MutualGroupDataCategory] by
                       Whole_file_analyses.gather_deriving_categories's
                       whole-script pre-pass (via [gather_mutual_group_data_ids]),
                       not decided here. In particular this never touches a
                       relation member's (e.g. [Instr_ok]'s) own [RelationCategory]
                       classification -- see that type's doc comment for why
                       forcing [Inhabited]/[BEq] onto a Prop-valued relation is
                       wrong regardless of its mutual-group membership. *)
                    (* [create_def] on an individual member can return more than
                       just the [Inductive]/[Structure] itself -- e.g. its own
                       redundant [DeriveDeceq] command, self-appended by
                       [create_inductive_type_construct]/[create_structure_construct]
                       whenever [deriving.derive_deceq] is set, since those
                       functions don't know they're being called from inside a
                       mutual group that already emits one combined
                       `derive_deceq` for the whole block below. Search for the
                       [Inductive]/[Structure] within the list rather than
                       requiring it be the sole element, and drop any such
                       per-member extras -- otherwise, when every member in the
                       group needs per-member deceq, none of them match the old
                       singleton pattern and both lists end up empty. *)
                    let inductives = List.filter_map (fun def ->
                      List.find_map (function Inductive i -> Some i | _ -> None) (create_def def)
                    ) defs in
                    let structures = List.filter_map (fun def ->
                      List.find_map (function Structure s -> Some s | _ -> None) (create_def def)
                    ) defs in
                    (* Every member shares the same [deriving] (the whole
                       group is uniformly [MutualGroupDataCategory]), so any
                       one of them tells us whether the group needs a
                       trailing `derive_deceq` -- [deceq_commands_for] picks
                       which name(s) to actually use from the full pool. *)
                    let names = List.map (fun (i : _inductive) -> i.id) inductives
                      @ List.map (fun (s : _structure) -> s.id) structures in
                    let deriving = match inductives, structures with
                      | ind :: _, _ -> ind.deriving
                      | [], s :: _ -> s.deriving
                      | [], [] -> failwith "unreachable: all_inductive_or_structure with >1 members"
                    in
                    [Mutual (MutualInductiveStructure (inductives, structures))]
                    @ deceq_commands_for names deriving

                  | false, true ->
                    let defs' = List.filter_map (fun def -> (* Name collision *)
                      match create_def def with [Def s] -> Some s | _ -> None
                    ) defs in
                    let abbrevs = List.filter_map (fun def ->
                      match create_def def with [Abbrev i] -> Some i | _ -> None
                    ) defs in
                    [Mutual (MutualDefAbbrev (defs', abbrevs))]
                  | false, false -> []
              )
          )
        )
    | _ -> failwith "unreachable: get_top_level_construct_type already confirmed MutualConstruct"

and create_def (def : Il.Ast.def) : command list
  = match get_top_level_construct_type def with
    | AbbrevConstruct -> create_abbrev_construct def
    | InductiveTypeConstruct -> create_inductive_type_construct def
    | StructureConstruct -> create_structure_construct def
    | TypeFamilyConstruct | GrammarConstruct | HintConstruct -> []
    | WfLemmaTheoremConstruct -> create_wf_lemma_theorem_construct def
    | InductiveRelationConstruct -> create_inductive_relation_construct def
    | DefConstruct -> create_def_construct def
    | OpaqueConstruct -> create_opaque_construct def
    | MutualConstruct -> create_mutual_construct def

    (* | RelD (
        id,
        quants,
        mixop,
        typ,
        rules
      ) -> failwith (
          "should have been handled by earlier case" ^ "              ||||||||           "
          ^ "id=" ^ id.it ^ "              ||||||||           "
          ^ "quants=" ^ String.concat "   XXX   " (List.map Il.Print.string_of_quant quants) ^ "              ||||||||           "
          ^ "mixop=" ^ Il.Print.string_of_mixop mixop ^ "              ||||||||           "
          ^ "typ=" ^ Il.Print.string_of_typ typ ^ "              ||||||||           "
          ^ "rules=" ^ String.concat "   XXX   " (List.map Il.Print.string_of_rule rules) ^ "              ||||||||           "
        ) *)


let prologue : command list =
  [
    list_ap;
    option_ap;
    rat_to_nat;
    splice;
  ]

let create_script (il : script) : _script =
  analysis := analyze_whole_script il;
  il_env := Il.Env.env_of_script il;
  (* Generate all commands.  Side effects record used arities for each family. *)
  used_prem_arities := [];
  used_exp_arities  := [];
  used_opt_arities  := [];
  used_derive_deceq := false;
  let generated = List.concat (List.map (fun def -> create_def def) il) in
  let forall_defs =
    List.sort_uniq compare !used_prem_arities
    |> List.map make_forall_def
  in
  let map_defs =
    List.sort_uniq compare !used_exp_arities
    |> List.map make_map_def
  in
  let omap_defs =
    List.sort_uniq compare !used_opt_arities
    |> List.map make_omap_def
  in
  {
    (* `derive_deceq` is a command ExtendedDeriveDecEq.lean declares, not
       part of Lean's own grammar, so it only parses once that file is
       imported -- see [used_derive_deceq]'s doc comment above. *)
    imports = if !used_derive_deceq then ["ExtendedDeriveDecEq"] else [];
    commands = prologue @ forall_defs @ map_defs @ omap_defs @ generated;
  }

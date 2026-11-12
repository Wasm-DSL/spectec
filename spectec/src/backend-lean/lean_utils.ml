open Lean_ast
module NonEmptyList = Util.Lib.NonEmptyList

(*
  ── Lean AST mapper ──────────────────────────────────────────────────────────

  Generic pre-order term mapper.  `map_term` is called on each node BEFORE
  the walker recurses into its children:

    None     → recurse into children with the same mapper (default structural walk)
    Some t'  → use t' as the result; do NOT recurse further

  This pre-order / short-circuit design supports scope-sensitive operations like
  capture-avoiding substitution, where a handler for a binder node must recurse
  into the binder body with a DIFFERENT mapper.  In that case the handler
  returns Some(...) and calls walk_term itself with the adjusted mapper.

  Compare: Il.Walk.transformer, which is post-order (recurse first, then apply
  the hook).  Post-order cannot express scope-sensitive transformations because
  by the time the hook sees a binder, its body has already been recursed with
  the wrong context.
  ─────────────────────────────────────────────────────────────────────────── *)

type mapper = {
  map_term : term -> term option;
  (* None = default structural recursion; Some t' = use t', stop here *)
}

let base_mapper : mapper = { map_term = Fun.const None }

let rec walk_term (m : mapper) (t : term) : term =
  match m.map_term t with
  | Some t' -> t'
  | None ->
    let w     = walk_term m in
    let w_arg = fun (Term inner) -> Term (w inner) in
    let w_sif = function
      | Ident_SIF _ as sif -> sif           (* field name — not a variable *)
      | AssignedField { l_val; is_private; term } ->
          AssignedField { l_val; is_private; term = w term }
    in
    let w_bounds = function
      | SliceFrom e           -> SliceFrom (w e)
      | SliceTo e             -> SliceTo (w e)
      | SliceBetween (e1, e2) -> SliceBetween (w e1, w e2)
    in
    (
      match t with

      (* ── Leaves: no sub-terms to walk ───────────────────────────────────── *)
      | Ident _ | Hole _ | Sort _ | Type _ | Prop
      | Num _ | Text _ | AnonymousApp | By _ -> t

      (* ── Structural nodes ───────────────────────────────────────────────── *)
      | FunType (a, b)  -> FunType (w a, w b)
      | ProdType (a, b) -> ProdType (w a, w b)

      | FunApp (f, args) ->
          FunApp (w f, NonEmptyList.from_list_unsafe
                        (List.map w_arg (NonEmptyList.to_list args)))

      | FunAppEllipsis (f, args) ->
          FunAppEllipsis (w f, List.map w_arg args)

      | BinaryInfixFunApp (a1, op, a2) ->
          BinaryInfixFunApp (w_arg a1, w op, w_arg a2)

      | Tuple ts           -> Tuple (List.map w ts)
      | Lean_ast.List ts   -> Lean_ast.List (List.map w ts)

      | DotProj (t1, field) -> DotProj (w t1, field) (* field is a selector, not a variable *)

      | LeadingDot t1 -> LeadingDot (w t1)

      | Struct { fields; type_annotation } ->
          Struct { fields          = List.map w_sif fields;
                  type_annotation = Option.map w type_annotation }

      | Index { collection; index; index_type } ->
          Index { collection = w collection; index = w index; index_type }

      | Slice { collection; bounds } ->
          Slice { collection = w collection; bounds = w_bounds bounds }

      | UpdateStruct { struct_to_update; fields_to_update } ->
          UpdateStruct { struct_to_update = w struct_to_update;
                        fields_to_update = List.map w_sif fields_to_update }

      | Lambda { params; body } ->
          (* Default walk does NOT filter params for capture-avoidance; that is
            the caller's responsibility via a custom map_term handler. *)
          Lambda { params; body = w body }

      | IfThenElse { cond; then_branch; else_branch } ->
          IfThenElse { cond = w cond; then_branch = w then_branch; else_branch = w else_branch }

      | Match { match_terms; cases } ->
          (* Pattern binders in cases are not tracked here; see subst_lean_term
            for the note on why this is currently safe. *)
          Match { match_terms = List.map w match_terms;
                  cases       = List.map (fun (pats, body) -> (List.map w pats, w body)) cases }

      | BoundedForall { var; collection; body } ->
          (* Default walk does NOT filter `var` for capture-avoidance; see Lambda note. *)
          BoundedForall { var; collection = w collection; body = w body }

      | RightPipelineField (t1, t2) ->
          RightPipelineField (w t1, t2)  (* t2 is a method/field name — not a variable *)

      | Not t1 -> Not (w t1)

      | Premises lines -> Premises (List.map w lines)

      | Let { let_config; let_decl; body } ->
          let let_decl' = match let_decl with
            | LetPatDecl d -> LetPatDecl { pat = w d.pat; type_ = Option.map w d.type_; value = w d.value }
          in
          Let { let_config; let_decl = let_decl'; body = w body }
      
      | Sorry -> Sorry
    )

(*
  subst_lean_term substs t

  Capture-avoiding substitution: replace every free Ident occurrence according
  to `substs`, stopping at any binder (Lambda / BoundedForall) that rebinds the
  substitution target.

  Built on walk_term: the mapper intercepts Ident, Lambda, and BoundedForall
  before the default walk can touch them; everything else is handled by the
  default structural recursion.

  Example (Pairs_ok arity-2 IterPr):
    substs = [("v_m", DotProj(Ident "__iter_tuple", Ident "1"));
              ("v_n", DotProj(Ident "__iter_tuple", Ident "2"))]
    t      = FunApp(Ident "Pair_ok", [Term(Ident "v_n"); Term(Ident "v_m")])
    result = FunApp(Ident "Pair_ok",
               [Term(DotProj(Ident "__iter_tuple", Ident "2"));
                Term(DotProj(Ident "__iter_tuple", Ident "1"))])

  Only Ident leaf nodes are substituted; field selectors inside DotProj are
  left alone (they are constant field names, not variables), which the default
  walk of DotProj already ensures by not recursing into `field`.

  NOTE on Match: create_prem / create_exp never construct Match terms on the
  call path that reaches subst_lean_term, so pattern binders in Match cases
  cannot shadow a substitution target in practice.  If that ever changes, the
  match-case handler below needs the same shadow-filtering as Lambda.
*)
let rec subst_lean_term (substs : (string * term) list) (t : term) : term =
  let mapper = { map_term = function

    | Ident id ->
        Some (match List.assoc_opt id substs with
              | Some repl -> repl
              | None      -> Ident id)

    | Lambda { params; body } ->
        (* CAPTURE-AVOIDANCE: remove any substs whose key is rebound by a param. *)
        let idents_of_bracketed_binder = function
          | ExplicitParam (idents, _)
          | ImplicitParam (idents, _)
          | OptAutoParam (idents, _, _) -> NonEmptyList.to_list idents
          | InstanceParam _ -> []   (* anonymous instance binder, no name to shadow with *)
        in
        let names_of_fun_binder = function
          | Ident_FB n -> [n]
          | Hole_FB -> []
          | BracketedBinder_FB bb ->
              List.filter_map (function Ident_IOH n -> Some n | Hole_IOH _ -> None)
                (idents_of_bracketed_binder bb)
        in
        let bound        = List.concat_map names_of_fun_binder (NonEmptyList.to_list params) in
        let inner_substs = List.filter (fun (k, _) -> not (List.mem k bound)) substs in
        Some (Lambda { params; body = subst_lean_term inner_substs body })

    | BoundedForall { var; collection; body } ->
        (* CAPTURE-AVOIDANCE: remove `var` from substs before entering body.
           `collection` is not under the binder, so it uses the full substs. *)
        let inner_substs = List.filter (fun (k, _) -> k <> var) substs in
        Some (BoundedForall { var;
                               collection = subst_lean_term substs collection;
                               body       = subst_lean_term inner_substs body })

    | _ -> None   (* default structural recursion for all other nodes *)
  } in
  walk_term mapper t

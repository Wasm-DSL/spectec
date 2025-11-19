open Il.Ast
open Util.Source

module StringSet = Set.Make(String)

let iter_prem_rels_list = ["List.Forall"; "List.Forall2"; "List_Forall3"]
let iter_exp_lst_funcs = ["List.map"; "list_zipWith"; "list_map3"]
let iter_exp_opt_funcs = ["option_map"; "option_zipWith"; "option_map3"]
let error at msg = Util.Error.error at "Rocq translation" msg 

let rec list_split (f : 'a -> bool) = function 
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

type exptype =
  | LHS
  | RHS
  | REL

let var_prefix = "var_"


let reserved_ids = ["N"; "in"; "In"; 
                    "S";
                    "return";
                    "if";
                    "bool";
                    "prod";
                    "at";
                    "()"; "tt"; 
                    "Import"; "Export"; 
                    "List"; "String"; 
                    "Type"; "list"; "nat"] |> StringSet.of_list

let remove_iter_from_type t =
  match t.it with
  | IterT (t', _) -> t'
  | _ -> t
let empty_name s = match s with
  | "" -> "NO_NAME"
  | _ -> s

let is_typ_bind b = match b.it with
  | TypB _ -> true
  | _ -> false

let string_of_list_prefix prefix delim str_func ls = 
  match ls with
  | [] -> ""
  | _ -> prefix ^ String.concat delim (List.map str_func ls)

let string_of_list_suffix suffix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> String.concat delim (List.map str_func ls) ^ suffix

let string_of_list prefix suffix delim str_func ls =
  match ls with
  | [] -> ""
  | _ -> prefix ^ String.concat delim (List.map str_func ls) ^ suffix

let square_parens s = "[" ^ s ^ "]"
let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"
let comment_parens s = "(* " ^ s ^ " *)"

let family_type_suffix = "entry"

let env_ref = ref Il.Env.empty

let is_record_typ inst = 
  match inst.it with
  | InstD (_, _, {it = StructT _; _}) -> true
  | _ -> false

let is_variant_typ inst = 
  match inst.it with
  | InstD (_, _, {it = VariantT _; _}) -> true
  | _ -> false

let is_alias_typ inst = 
  match inst.it with
  | InstD (_, _, {it = AliasT _; _}) -> true
  | _ -> false

let is_alias_typ_def def = 
  match def.it with
  | TypD(_ , _, [{it = InstD (_, _, {it = AliasT _; _}); _}]) -> true
  | _ -> false

let check_trivial_append env typ = 
  match typ.it with
  | IterT _ -> true
  | VarT (id, _) -> 
    begin match (Il.Env.find_opt_typ env id) with
    | Some (_, [inst]) when is_record_typ inst -> true
    | _ -> false
    end
  | _ -> false

let is_inductive d = 
  match d.it with
  | RelD _ -> true
  | TypD(_, _, [inst]) when is_variant_typ inst || is_alias_typ inst -> true
  | _ -> false
    
let comment_desc_def d = 
  match d.it with
  | TypD (_, _, [inst]) when is_alias_typ inst -> "Type Alias Definition"
  | TypD (_, _, [inst]) when is_variant_typ inst -> "Inductive Type Definition"
  | TypD (_, _, [inst]) when is_record_typ inst -> "Record Creation Definition"
  | TypD _ -> "Type Family Definition"
  | RecD _ -> "Mutual Recursion"
  | DecD (_, _, _, []) -> "Axiom Definition"
  | DecD _ -> "Auxiliary Definition"
  | RelD _ -> "Inductive Relations Definition"
  | HintD _ -> "Hint Definition"
  | GramD _ -> "Grammar Production Definition"

let render_unop unop = 
  match unop with
  | `NotOp   -> "negb "
  | `PlusOp  -> ""
  | `MinusOp -> "0 - "
let render_binop binop = 
  match binop with
  | `AndOp   -> " && " 
  | `OrOp    -> " || "
  | `ImplOp  -> " -> "
  | `EquivOp -> " <-> "
  | `AddOp   -> " + " 
  | `SubOp   -> " - " 
  | `MulOp   -> " * " 
  | `DivOp   -> " / "
  | `ModOp   -> " mod "
  | `PowOp   -> " ^ " 

let render_cmpop cmpop =
  match cmpop with
  | `EqOp -> " == "
  | `NeOp -> " != "
  | `LtOp -> " < "
  | `GtOp -> " > "
  | `LeOp -> " <= "
  | `GeOp -> " >= "

let is_atomid a =
  match a.it with
  | Xl.Atom.Atom _ -> true
  | _ -> false 

let render_id id = 
  match id with
  | s when StringSet.mem s reserved_ids -> "res_" ^ s
  | _ -> id

let render_atom a =
  match a.it with
  | Xl.Atom.Atom a -> render_id a
  | _ -> ""

let render_mixop typ_id (m : mixop) = 
  let s = (match m with
    | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> render_id a
    | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.filter is_atomid atoms |> List.map render_atom)) mixop
    )
  ) in
  (* HACK - should be done in improve ids *)
  match s with
  | "_" -> "mk_" ^ typ_id 
  | s when Il.Env.mem_typ !env_ref (s $ no_region) -> "mk_" ^ s
  | s -> s

let get_bind_id b = 
  match b.it with
  | ExpB (id, _) | TypB id | DefB (id, _, _) | GramB (id, _, _) -> id.it

let get_param_id b = 
  match b.it with
  | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _) -> id.it

let render_numtyp nt = 
  match nt with
  | `NatT -> "nat"
  | `IntT -> "nat"
  | `RatT -> "nat"
  | `RealT -> "nat"

let transform_case_tup e = 
  match e.it with
  | TupE exps -> exps
  | _ -> [e]

let transform_case_typ t =
  match t.it with
  | TupT typs -> List.map snd typs
  | _ -> [t]

let transform_case_args t =
  match t.it with
  | TupT typs -> typs
  | _ -> [(VarE ("_" $ t.at) $$ t.at % t, t)]

let get_type_args t = 
  match t.it with
  | VarT (_, args) -> args
  | _ -> error t.at ("Following type should be a variable type: " ^ Il.Print.string_of_typ t)

let rec render_param_type exp_type alias_set param = 
  match param.it with
  | ExpP (_, typ) -> render_type exp_type alias_set typ
  | TypP _ -> "eqType"
  | DefP (_, params, typ) -> 
    string_of_list_suffix " -> " " -> " (render_param_type exp_type alias_set) params ^ render_type exp_type alias_set typ
  | GramP _ -> comment_parens ("Unsupported param: " ^ Il.Print.string_of_param param)

and render_type exp_type alias_set typ = 
  let rt_func = render_type exp_type alias_set in
  match typ.it with
  | VarT (id, []) when StringSet.mem id.it alias_set -> rt_func (Il.Eval.reduce_typ !env_ref typ) 
  | VarT (id, []) -> id.it
  | VarT (id, args) -> parens (id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type alias_set) args))
  | BoolT -> "bool"
  | NumT nt -> render_numtyp nt
  | TextT -> "string"
  | TupT [] -> "unit"
  | TupT typs -> String.concat " * " (List.map (fun (_, t) -> rt_func t) typs)
  | IterT (t, Opt) -> parens ("option " ^ rt_func t)
  | IterT (t, _) -> parens ("list " ^ rt_func t)

and render_exp exp_type alias_set exp =
  let r_func = render_exp exp_type alias_set in
  match exp.it with 
  | VarE id -> render_id id.it
  | BoolE b -> string_of_bool b
  | NumE (`Nat n) -> Z.to_string n (* TODO fix nums *)
  | NumE (`Int n) -> Z.to_string n (* TODO fix nums *)
  | NumE (`Rat n) -> Q.to_string n (* TODO fix nums *)
  | NumE (`Real n) -> string_of_float n (* TODO fix nums *)
  | TextE s -> "\"" ^ String.escaped s ^ "\""
  | UnE (unop, _, e1) -> parens (render_unop unop ^ r_func e1)
  | BinE (binop, _, e1, e2) -> parens (r_func e1 ^ render_binop binop ^ r_func e2)
  | CmpE (cmpop, _, e1, e2) -> parens (r_func e1 ^ render_cmpop cmpop ^ r_func e2)
  | TupE [] -> "()"
  | TupE exps -> parens (String.concat ", " (List.map r_func exps))
  | ProjE (e, i) -> 
    let typs = transform_case_typ e.note in 
    let rec make_proj_chain idx len e = 
      match idx, len with
      | 0, 0 -> r_func e
      | i, n when i <= n -> parens ("snd " ^ r_func e)
      | _ -> parens ("fst " ^ (make_proj_chain idx (len - 1) e))
    in
    begin match typs with
    | [_] -> r_func e
    | _ -> make_proj_chain i (List.length typs - 1) e 
    end
  | CaseE (m, e) when exp_type = LHS -> 
    let name = Il.Print.string_of_typ_name exp.note in
    let exps = transform_case_tup e in
    begin match exps with
    | [] -> render_mixop name m
    | _ -> parens (render_mixop name m ^ " " ^ String.concat " " (List.map r_func exps))
    end
  | CaseE (m, e) -> 
    let exps = transform_case_tup e in
    let name = Il.Print.string_of_typ_name exp.note in
    (* Reduce here to remove type aliasing *)
    let args = get_type_args (Il.Eval.reduce_typ !env_ref exp.note) in
    let implicit_args = if args = [] then "" else " " ^ String.concat " " (List.init (List.length args) (fun _ -> "_")) in
    begin match exps with
    | [] -> render_mixop name m
    | _ -> parens (render_mixop name m ^ implicit_args ^ " " ^ String.concat " " (List.map r_func exps))
    end
  | UncaseE _ -> error exp.at "Encountered uncase. Run uncase-removal pass"
  | OptE (Some e) -> parens ("Some " ^ r_func e)
  | OptE None -> "None"
  | TheE e -> parens ("the " ^ r_func e)
  | StrE fields -> "{| " ^ (String.concat "; " (List.map (fun (a, e) -> render_atom a ^ " := " ^ r_func e) fields)) ^ " |}"
  | DotE (e, a) -> parens (render_atom a ^ " " ^ r_func e)
  | CompE (e1, e2) -> parens (r_func e1 ^ " @@ " ^ r_func e2)
  | ListE [] -> "[]"
  | ListE exps -> square_parens (String.concat "; " (List.map r_func exps)) 
  | LiftE e -> parens ("option_to_list " ^ r_func e)
  | MemE (e1, e2) -> parens (r_func e1 ^ " \\in " ^ r_func e2)
  | LenE e1 -> parens ("List.length " ^ r_func e1)
  | CatE ({it = ListE [e1]; _}, e2) when exp_type = LHS -> parens (r_func e1 ^ " :: " ^ r_func e2) 
  | CatE (e1, e2) -> parens (r_func e1 ^ " ++ " ^ r_func e2)
  | IdxE (e1, e2) -> parens ("lookup_total " ^ r_func e1 ^ " " ^ r_func e2)
  | SliceE (e1, e2, e3) -> parens ("list_slice" ^ r_func e1 ^ " " ^ r_func e2 ^ " " ^ r_func e3)
  | UpdE (e1, p, e2) -> render_path_start p alias_set e1 false e2
  | ExtE (e1, p, e2) -> render_path_start p alias_set e1 true e2
  | CallE (id, args) -> parens (render_id id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type alias_set) args))
  (* Iter handling *)
  | IterE (e, (ListN (n, _), [])) -> parens ("List.repeat " ^ (r_func e) ^ " " ^ (r_func n)) 
  | IterE (e, (_, [])) -> r_func e
  | IterE (e, _) when exp_type = LHS -> r_func e
  | IterE (e, (iter, iter_binds)) ->
    let binds = List.map (fun (id, e) -> parens (render_id id.it  ^ " : " ^ render_type exp_type alias_set (remove_iter_from_type e.note))) iter_binds in
    let iter_exps = List.map snd iter_binds in 
    let n = List.length iter_binds - 1 in
    let lst = if iter = Opt then iter_exp_opt_funcs else iter_exp_lst_funcs in
    let pred_name = match (List.nth_opt lst n) with 
    | Some s -> s
    | None -> error exp.at "Iteration exceeded the supported amount for rocq translation"
    in 
    parens (pred_name ^ " " ^ render_lambda binds (r_func e) ^ " " ^ 
    String.concat " " (List.map (render_exp exp_type alias_set) iter_exps))
  | CvtE (e1, _nt1, nt2) -> parens (r_func e1 ^ " : " ^ render_numtyp nt2)
  | SubE _ -> error exp.at "Encountered subtype expression. Please run sub pass"

and render_arg exp_type alias_set a = 
  match a.it with 
  | ExpA e -> render_exp exp_type alias_set e
  | TypA t -> render_type exp_type alias_set t
  | DefA id -> render_id id.it 
  | _ -> comment_parens ("Unsupported arg: " ^ Il.Print.string_of_arg a)

and render_bind exp_type alias_set b =
  match b.it with
  | ExpB (id, typ) -> parens (render_id id.it  ^ " : " ^ render_type exp_type alias_set typ)
  | TypB id -> parens (render_id id.it  ^ " : Type")
  | DefB (id, params, typ) -> 
    parens (render_id id.it  ^ " : " ^ 
    string_of_list_suffix " -> " " -> " (render_param_type exp_type alias_set) params ^
    render_type exp_type alias_set typ)
  | GramB _ -> comment_parens ("Unsupported bind: " ^ Il.Print.string_of_bind b)

and render_param exp_type alias_set param = 
  let get_id p =
    match p.it with
    | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _) -> render_id id.it 
  in
  parens (get_id param ^ " : " ^ render_param_type exp_type alias_set param)


(* PATH Functions *)
and transform_list_path (p : path) = 
  match p.it with   
  | RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) when p'.it = RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) -> p' :: transform_list_path p'

and render_lambda binds text =
  parens ("fun " ^ String.concat " " binds ^ " => " ^ text)

and render_path_start (p : path) alias_set start_exp is_extend end_exp = 
  let paths = List.rev (p :: transform_list_path p) in
  (render_path paths alias_set (start_exp.note) p.at 0 (Some start_exp) is_extend end_exp)

and render_path (paths : path list) alias_set typ at n name is_extend end_exp = 
  let render_record_update t1 t2 t3 =
    parens (t1 ^ " <| " ^ t2 ^ " := " ^ t3 ^ " |>")
  in
  let r_func_e = render_exp RHS alias_set in
  let is_dot p = (match p.it with
    | DotP _ -> true
    | _ -> false 
  ) in
  let list_name num = (match name with
    | Some exp -> exp
    | None -> VarE ((var_prefix ^ string_of_int num) $ no_region) $$ no_region % typ
  ) in
  let new_name_typ = remove_iter_from_type (list_name n).note in
  let new_name = var_prefix ^ string_of_int (n + 1) in 
  match paths with
  (* End logic for extend *)
  | [{it = IdxP (_, e); _}] when is_extend -> 
    let extend_term = parens (new_name ^ " ++ " ^ r_func_e end_exp) in
    let bind = render_bind RHS alias_set (ExpB (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_update_func " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ render_lambda [bind] extend_term)
  | [{it = DotP (_, a); _}] when is_extend -> 
    let projection_term = parens (render_atom a ^ " " ^ r_func_e (list_name n)) in
    let extend_term = parens (projection_term ^ " ++ " ^ r_func_e end_exp) in
    render_record_update (r_func_e (list_name n)) (render_atom a) extend_term
  | [{it = SliceP (_, e1, e2); _}] when is_extend -> 
    let extend_term = parens (new_name ^ " ++ " ^ r_func_e end_exp) in
    let bind = render_bind RHS alias_set (ExpB (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_slice_update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ render_lambda [bind] extend_term)
  (* End logic for update *)
  | [{it = IdxP (_, e); _}] -> 
    let bind = render_bind RHS alias_set (ExpB ("_" $ no_region, new_name_typ) $ no_region) in
    parens ("list_update_func " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [bind] (r_func_e end_exp))
  | [{it = DotP (_, a); _}] -> 
    render_record_update (r_func_e (list_name n)) (render_atom a) (r_func_e end_exp)
  | [{it = SliceP (_, e1, e2); _}] -> 
    parens ("list_slice_update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ r_func_e end_exp)
  (* Middle logic *)
  | {it = IdxP (_, e); note; _} :: ps -> 
    let path_term = render_path ps alias_set note at (n + 1) None is_extend end_exp in
    let new_name = var_prefix ^ string_of_int (n + 1) in 
    let bind = render_bind RHS alias_set (ExpB (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_update_func " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [bind] path_term)
  | ({it = DotP _; note; _} as p) :: ps -> 
    let (dot_paths, ps') = list_split is_dot (p :: ps) in
    let (end_atom, dot_paths') = match List.rev dot_paths with
      | {it = DotP (_, a'); _} :: ds -> (a', ds)
      | _ -> assert false (* Impossible since it has p *)
    in
    let projection_term = List.fold_right (fun p acc -> 
      match p.it with
      | DotP (_, a') -> 
        DotE (acc, a') $$ no_region % p.note
      | _ -> error at "Should be a record access" (* Should not happen *)
    )  dot_paths' (list_name n) in
    let update_fields = String.concat ";" (List.map (fun p -> 
      match p.it with
      | DotP (_, a) -> render_atom a
      | _ -> error at "Should be a record access" 
    ) dot_paths) in
    let new_term = parens (render_atom end_atom ^ " " ^ r_func_e projection_term) in
    let new_exp = DotE (projection_term, end_atom) $$ no_region % note in 
    if ps' = [] 
      then (
        let final_term = if is_extend then parens (new_term ^ " ++ " ^ r_func_e end_exp) else r_func_e end_exp in
        render_record_update (r_func_e (list_name n)) update_fields final_term
      )
      else (
        let path_term = render_path ps' alias_set note at n (Some new_exp) is_extend end_exp in
        render_record_update (r_func_e (list_name n)) update_fields path_term
      )
  | ({it = SliceP (_, _e1, _e2); _} as p) :: _ps ->
    (* TODO - this is not entirely correct. Still unsure how to implement this as a term *)
    (* let new_typ = transform_type' NORMAL note in
    let path_term = render_path ps new_typ at (n + 1) None is_extend end_exp $@ transform_type' NORMAL note in
    let new_name = var_prefix ^ string_of_int (n + 1) in
    let lambda_typ = T_arrowtype [new_name_typ; new_typ] in
    T_app (T_exp_basic T_sliceupdate $@ anytype',
      [list_name n; transform_exp NORMAL e1; transform_exp NORMAL e2; T_lambda ([(new_name, new_name_typ)], path_term) $@ lambda_typ]) *)
    comment_parens (Il.Print.string_of_path p)
  (* Catch all error if we encounter empty list or RootP *)
  | _ -> error at "Paths should not be empty"

and render_binders (alias_set : StringSet.t) (binds : bind list) = 
  string_of_list_prefix " " " " (render_bind RHS alias_set) binds

let render_binders_ids (binds : bind list) = 
  string_of_list_prefix " " " " get_bind_id binds

let render_match_binders params =
  String.concat ", " (List.map get_param_id params)

let render_params alias_set params = 
  string_of_list_prefix " " " " (render_param RHS alias_set) params

let render_match_args alias_set args =
  string_of_list_prefix " " ", " (render_arg LHS alias_set) args


let string_of_eqtype_proof recursive (cant_do_equality: bool) alias_set id (binds : bind list) =
  let binders = render_binders alias_set binds in 
  let binder_ids = render_binders_ids binds in
  let id' = render_id id in 
  (* Decidable equality proof *)
  (* e.g.
    Definition functype_eq_dec : forall (tf1 tf2 : functype),
      {tf1 = tf2} + {tf1 <> tf2}.
    Proof. decidable_equality. Defined.
    Definition functype_eqb v1 v2 : bool := functype_eq_dec v1 v2.
    Definition eqfunctypeP : Equality.axiom functype_eqb :=
      eq_dec_Equality_axiom functype functype_eq_dec.

    HB.instance Definition _ := hasDecEq.Build (functype) (eqfunctypeP).
    *)
  (if cant_do_equality then comment_parens "FIXME - No clear way to do decidable equality" ^ "\n" else "") ^
  (match recursive with
  | true -> 
    
    "Fixpoint " ^ id' ^ "_eq_dec" ^ binders ^ " (v1 v2 : " ^ id' ^ binder_ids ^ ") {struct v1} :\n" ^
    "  {v1 = v2} + {v1 <> v2}.\n" ^
    let proof = if cant_do_equality then "Admitted" else "decide equality; do ? decidable_equality_step. Defined" in
    "Proof. " ^ proof ^ ".\n\n"
  | false -> 
    "Definition " ^ id' ^ "_eq_dec : forall" ^ binders ^ " (v1 v2 : " ^ id' ^ binder_ids ^ "),\n" ^
    "  {v1 = v2} + {v1 <> v2}.\n" ^
    
    let proof = if cant_do_equality then "Admitted" else "do ? decidable_equality_step. Defined" in
    "Proof. " ^ proof ^ ".\n\n") ^ 

  "Definition " ^ id' ^ "_eqb" ^ binders ^ " (v1 v2 : " ^ id' ^ binder_ids ^ ") : bool :=\n" ^
  "\tis_left" ^ parens (id' ^ "_eq_dec" ^ binder_ids ^ " v1 v2") ^ ".\n" ^  
  "Definition eq" ^ id' ^ "P" ^ binders ^ " : Equality.axiom " ^ parens (id' ^ "_eqb" ^ binder_ids) ^ " :=\n" ^
  "\teq_dec_Equality_axiom " ^ parens (id' ^ binder_ids) ^ " " ^ parens (id' ^ "_eq_dec" ^ binder_ids) ^ ".\n\n" ^
  "HB.instance Definition _" ^ binders ^ " := hasDecEq.Build " ^ parens (id' ^ binder_ids) ^ " " ^ parens ("eq" ^ id' ^ "P" ^ binder_ids) ^ ".\n" ^
  "Hint Resolve " ^ id' ^ "_eq_dec : eq_dec_db" 

let string_of_relation_args alias_set typ = 
  string_of_list "" " -> " " -> " (render_type REL alias_set) (transform_case_typ typ)
  
let rec render_prem alias_set prem =
  let r_func = render_prem alias_set in 
  match prem.it with
  | IfPr exp -> render_exp REL alias_set exp
  | RulePr (id, _m, exp) -> parens (render_id id.it ^ string_of_list_prefix " " " " (render_exp REL alias_set) (transform_case_tup exp))
  | NegPr p -> parens ("~" ^ r_func p)
  | ElsePr -> "True " ^ comment_parens ("Unsupported premise: otherwise") (* Will be removed by an else pass *)
  | IterPr (p, (_, [])) -> r_func p
  | IterPr (p, (iter, ps)) -> 
    let option_conversion s = if iter = Opt then parens ("option_to_list " ^ s) else s in
    let binds = List.map (fun (id, e) -> parens (render_id id.it ^ " : " ^ render_type REL alias_set (remove_iter_from_type e.note))) ps in
    let iter_exps = List.map snd ps in 
    let n = List.length ps - 1 in
    let pred_name = match (List.nth_opt iter_prem_rels_list n) with 
    | Some s -> s
    | None -> error prem.at "Iteration exceeded the supported amount for rocq translation"
    in 
    pred_name ^ " " ^ render_lambda binds (r_func p) ^ " " ^ 
    String.concat " " (List.map (render_exp REL alias_set) iter_exps |> List.map option_conversion)
  | LetPr _ -> 
    "True " ^ comment_parens ("Unsupported premise: " ^ Il.Print.string_of_prem prem)
 
let render_typealias alias_set id binds typ = 
  "Definition " ^ id ^ render_binders alias_set binds ^ " : Type := " ^ render_type RHS alias_set typ

let render_record recursive alias_set id binds fields = 
  let constructor_name = "MK" ^ id in
  let inhabitance_binders = render_binders alias_set binds in 
  let binders = render_binders_ids binds in 

  (* Standard Record definition *)
  "Record " ^ id ^ inhabitance_binders ^ " := " ^ constructor_name ^ "\n{\t" ^ 
  String.concat "\n;\t" (List.map (fun (a, (_, typ, _), _) -> 
    render_atom a ^ " : " ^ render_type RHS alias_set typ) fields) ^ "\n}.\n\n" ^

  (* Inhabitance proof for default values *)
  "Global Instance Inhabited_" ^ id ^ inhabitance_binders ^ " : Inhabited " ^ parens (id ^ binders) ^ " := \n" ^
  "{default_val := {|\n\t" ^
      String.concat ";\n\t" (List.map (fun (a, _, _) -> 
        render_atom a  ^ " := default_val") fields) ^ "|} }.\n\n" ^

  (* Append instance *)
  "Definition _append_" ^ id ^ inhabitance_binders ^ " (arg1 arg2 : " ^ parens (id ^ binders) ^ ") :=\n" ^ 
  "{|\n\t" ^ String.concat "\t" ((List.map (fun (a, (_, t, _), _) ->
    let record_id' = render_atom a in
    if (check_trivial_append !env_ref t) 
    then record_id' ^ " := " ^ "arg1.(" ^ record_id' ^ ") @@ arg2.(" ^ record_id' ^ ");\n" 
    else record_id' ^ " := " ^ "arg1.(" ^ record_id' ^ "); " ^ comment_parens "FIXME - Non-trivial append" ^ "\n" 
  )) fields) ^ "|}.\n\n" ^ 
  "Global Instance Append_" ^ id ^ " : Append " ^ id ^ " := { _append arg1 arg2 := _append_" ^ id ^ " arg1 arg2 }.\n\n" ^

  (* Setter proof *)
  "#[export] Instance eta__" ^ id ^ " : Settable _ := settable! " ^ constructor_name ^ " <" ^ 
  String.concat ";" (List.map (fun (a, _, _) -> render_atom a) fields) ^ ">"
  ^ ".\n\n" ^ string_of_eqtype_proof recursive false alias_set id [] 

let rec has_typ id t =
  match t.it with
  | VarT (id', _) -> id'.it = id
  | IterT (t', _) ->  has_typ id t'
  | TupT pairs -> List.exists (fun (_, t') -> has_typ id t') pairs
  | _ -> false

let inhabitance_proof alias_set id binds cases = 
  (* Inhabitance proof for default values *)
  let inhabitance_binders = render_binders alias_set binds in 
  let binders = render_binders_ids binds in 
  "Global Instance Inhabited__" ^ id ^ inhabitance_binders ^ " : Inhabited " ^ parens (id ^ binders) ^
  let rec render_proof cs = 
    (match cs with
      | [] -> "(* FIXME: no inhabitant found! *) .\n" ^
              "\tAdmitted"
      | (m, (_, t, _), _) :: ts -> 
        let typs = transform_case_typ t in
        if (List.exists (has_typ id) typs) then render_proof ts else 
        " := { default_val := " ^ render_mixop id m ^ binders ^ 
        string_of_list_prefix " " " " (fun _ -> "default_val" ) (transform_case_typ t) ^ " }")
  in
  render_proof cases 

let cant_do_equality binds cases = 
  (List.exists is_typ_bind binds) ||
  (List.exists (fun (_, (binds', _, _), _) -> List.exists is_typ_bind binds') cases)
  
let render_case_typs alias_set t = 
  let typs = transform_case_args t in
  string_of_list_prefix " " " " (fun (e, t) -> 
    parens (render_exp RHS alias_set e ^ " : " ^ render_type RHS alias_set t)) typs

let render_variant_typ alias_set is_recursive prefix id binds cases = 
  prefix ^ id ^ render_binders alias_set binds ^ " : Type :=\n\t" ^
  String.concat "\n\t" (List.map (fun (m, (_, t, _), _) ->
    "| " ^ render_mixop id m ^ render_case_typs alias_set t ^ " : " ^ id ^ render_binders_ids binds   
  )  cases) ^ 
  if is_recursive then "" else
  (* Inhabitance proof *)
  ".\n\n" ^ inhabitance_proof alias_set id binds cases ^
  (* Eq proof *)
  ".\n\n" ^ string_of_eqtype_proof is_recursive (cant_do_equality binds cases) alias_set id binds

let render_function_def alias_set prefix id params r_typ clauses = 
  prefix ^ id ^ render_params alias_set params ^ " : " ^ render_type RHS alias_set r_typ ^ " :=\n" ^
  "\tmatch " ^ render_match_binders params ^ " return " ^ render_type RHS alias_set r_typ ^ " with\n\t\t" ^
  String.concat "\n\t\t" (List.map (fun clause -> match clause.it with
    | DefD (_, args, exp, _) -> 
    "|" ^ render_match_args alias_set args ^ " => " ^ render_exp RHS alias_set exp) clauses) ^
  "\n\tend"

let render_relation alias_set prefix id typ rules = 
  prefix ^ id ^ " : " ^ string_of_relation_args alias_set typ ^ "Prop :=\n\t" ^
  String.concat "\n\t" (List.map (fun rule -> match rule.it with
    | RuleD (rule_id, binds, _, exp, prems) ->
      let string_prems = string_of_list "\n\t\t" " ->\n\t\t" " ->\n\t\t" (render_prem alias_set) prems in
      let forall_quantifiers = string_of_list "forall " ", " " " (render_bind REL alias_set) binds in
      "| " ^ render_id rule_id.it ^ " : " ^ forall_quantifiers ^ string_prems ^ render_id id ^ " " ^ String.concat " " (List.map (render_exp REL alias_set) (transform_case_tup exp))
  ) rules)

let render_axiom prefix alias_set id params r_typ =
  prefix ^ id  ^ " : " ^ string_of_list "forall " ", " " " (render_param RHS alias_set) params ^ render_type RHS alias_set r_typ

let render_rel_axiom alias_set prefix id typ =
  prefix ^ id  ^ " : " ^ string_of_relation_args alias_set typ ^ "Prop"

let render_global_declaration id alias_set typ exp = 
  "Definition " ^ id  ^ " : " ^ render_type RHS alias_set typ ^ " := " ^ render_exp RHS alias_set exp

let render_extra_info alias_set def = 
  match def.it with
  | TypD (id, _, [{it = InstD (binds, _, {it = AliasT typ; _}); _}]) -> 
    Some (render_typealias alias_set id.it binds typ)
  | TypD (id, _, [{it = InstD (binds, _, {it = VariantT typcases; _}); _}]) -> 
    Some (inhabitance_proof alias_set id.it binds typcases ^ ".\n\n" ^
    string_of_eqtype_proof true (cant_do_equality binds typcases) alias_set id.it binds)
  | _ -> None

let get_type_alias_id def = 
  match def.it with
  | TypD (id, _, [inst]) when is_alias_typ inst -> Some id.it
  | _ -> None

let has_prems c = 
  match c.it with
  | DefD (_, _, _, prems) -> prems <> []

let start_prefix def = 
  match def.it with
  | _ when is_inductive def -> "Inductive "
  | DecD (_, _, _, []) -> "Axiom "
  | DecD (_, _, _, _clauses) -> "Axiom " (* TODO add condition: when List.exists has_prems clauses*)
  (* Enable this when deftorel comes in: | DecD _ -> "Fixpoint " *)
  | TypD (_, _, [inst]) when is_record_typ inst -> "Record "
  | _ -> ""

let is_axiom def =
  match def.it with
  | DecD (_, _, _, _clauses) -> true
  | _ -> false

(* TODO - revise mutual recursion with other defs such as records and axioms *)
let rec string_of_def has_endline recursive (alias_set : StringSet.t) def = 
  let end_newline = if has_endline then ".\n\n" else "" in 
  let start = if recursive then "" else comment_parens (comment_desc_def def ^ " at: " ^ Util.Source.string_of_region def.at) ^ "\n" in
  match def.it with
  | TypD (id, _, [{it = InstD (binds, _, {it = AliasT typ; _}); _}]) -> 
    if recursive then "" else 
    start ^ render_typealias alias_set (render_id id.it) binds typ ^ end_newline
  | TypD (id, _, [{it = InstD (binds, _, {it = StructT typfields; _}); _}])-> 
    start ^ render_record recursive alias_set (render_id id.it) binds typfields ^ end_newline
  | TypD (id, _, [{it = InstD (binds, _, {it = VariantT typcases; _}); _}]) -> 
    let prefix = if recursive then "" else "Inductive " in
    start ^ render_variant_typ alias_set recursive prefix (render_id id.it) binds typcases ^ end_newline
  | DecD (id, [], typ, [{it = DefD ([], [], exp, _); _}]) -> 
    start ^ render_global_declaration (render_id id.it) alias_set typ exp ^ end_newline
  | DecD (id, params, typ, []) -> 
    let prefix = if recursive then "" else "Axiom " in
    start ^ render_axiom prefix alias_set (render_id id.it) params typ ^ end_newline
  | DecD (id, params, typ, _clauses)  -> (* TODO add condition: when List.exists has_prems clauses*)
    let prefix = if recursive then "" else "Axiom " in
    start ^ render_axiom prefix alias_set (render_id id.it) params typ ^ end_newline
  (* TODO activate this when deftorel comes in *)
  (* | DecD (id, params, typ, clauses) -> 
    let prefix = if recursive then "" else "Definition " in
    start ^ render_function_def alias_set prefix id.it params typ clauses ^ end_newline *)
  | RelD (id, _, typ, []) -> 
    let prefix = if recursive then "" else "Axiom " in
    start ^ render_rel_axiom alias_set prefix (render_id id.it) typ ^ end_newline
  | RelD (id, _, typ, rules) -> 
    let prefix = if recursive then "" else "Inductive " in
    start ^ render_relation alias_set prefix (render_id id.it) typ rules ^ end_newline
  (* Mutual recursion - special handling for rocq *)
  | RecD defs -> start ^ (match defs with
    | [] -> ""
    | [d] -> 
      let extra_info = render_extra_info alias_set d in
      start_prefix d ^ 
      string_of_def false true StringSet.empty d ^
      begin match extra_info with
      | None -> end_newline
      | Some s -> end_newline ^ s ^ end_newline
      end
    (* HACK - this is simply to deal with functions that are not supposed to be axioms.
    The functions that are supposed to be axioms should not be mutually recursive anyways.
    *)
    | (d :: _defs') when List.exists is_axiom defs ->
      let prefix = ".\n\n" ^ start_prefix d in
      let aliases = StringSet.union alias_set (List.filter_map get_type_alias_id defs |> StringSet.of_list) in 
      let extra_info = String.concat ".\n\n" (List.filter_map (render_extra_info alias_set) defs) in
      start_prefix d ^ 
      String.concat prefix (
        Util.Lib.List.filter_not is_alias_typ_def defs |> 
        List.map (string_of_def false true aliases)
      ) ^ ".\n\n" ^ 
      extra_info ^ if extra_info = "" then "" else end_newline
    | (d :: _defs') -> 
      let prefix = "\n\nwith\n\n" in
      let aliases = StringSet.union alias_set (List.filter_map get_type_alias_id defs |> StringSet.of_list) in 
      let extra_info = String.concat ".\n\n" (List.filter_map (render_extra_info alias_set) defs) in
      start_prefix d ^ 
      String.concat prefix (
        Util.Lib.List.filter_not is_alias_typ_def defs |> 
        List.map (string_of_def false true aliases)
      ) ^ ".\n\n" ^ 
      extra_info ^ if extra_info = "" then "" else end_newline
    )
  | _ -> error def.at ("Unsupported def: " ^ Il.Print.string_of_def def)

let exported_string = 
  "(* Imported Code *)\n" ^
  "From Coq Require Import String List Unicode.Utf8 Reals.\n" ^
  "From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.\n" ^
  "From HB Require Import structures.\n" ^
  "From RecordUpdate Require Import RecordSet.\n" ^
  "Declare Scope wasm_scope.\n\n" ^
  "Class Inhabited (T: Type) := { default_val : T }.\n\n" ^
  "Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=\n" ^
  "\tList.nth n l default_val.\n\n" ^
  "Definition the {T : Type} {_ : Inhabited T} (arg : option T) : T :=\n" ^
	"\tmatch arg with\n" ^
	"\t\t| None => default_val\n" ^
	"\t\t| Some v => v\n" ^
	"\tend.\n\n" ^
  "Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=\n" ^
  "\tList.map (fun '(x, y) => f x y) (List.combine xs ys).\n\n" ^
  "Definition option_zipWith {α β γ: Type} (f: α -> β -> γ) (x: option α) (y: option β): option γ := \n" ^
  "\tmatch x, y with\n" ^
  "\t\t| Some x, Some y => Some (f x y)\n" ^
  "\t\t| _, _ => None\n" ^
  "\tend.\n\n" ^
  "Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=\n" ^
  "\tmatch l, n with\n" ^
  "\t\t| nil, _ => nil\n" ^
  "\t\t| x :: l', O => y :: l'\n" ^
  "\t\t| x :: l', S n => x :: list_update l' n y\n" ^
  "\tend.\n\n" ^
  "Definition option_append {α: Type} (x y: option α) : option α :=\n" ^
  "\tmatch x with\n" ^
  "\t\t| Some _ => x\n" ^
  "\t\t| None => y\n" ^
  "\tend.\n\n" ^
  "Definition option_map {α β : Type} (f : α -> β) (x : option α) : option β :=\n" ^
	"\tmatch x with\n" ^
	"\t\t| Some x => Some (f x)\n" ^
	"\t\t| _ => None\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_update_func {α: Type} (l: list α) (n: nat) (y: α -> α): list α :=\n" ^
	"\tmatch l, n with\n" ^
	"\t\t| nil, _ => nil\n" ^
	"\t\t| x :: l', O => (y x) :: l'\n" ^
	"\t\t| x :: l', S n => x :: list_update_func l' n y\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_slice {α: Type} (l: list α) (i: nat) (j: nat): list α :=\n" ^
	"\tmatch l, i, j with\n" ^
	"\t\t| nil, _, _ => nil\n" ^
	"\t\t| x :: l', O, O => nil\n" ^
	"\t\t| x :: l', S n, O => nil\n" ^
	"\t\t| x :: l', O, S m => x :: list_slice l' 0 m\n" ^
	"\t\t| x :: l', S n, m => list_slice l' n m\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_slice_update {α: Type} (l: list α) (i: nat) (j: nat) (update_l: list α): list α :=\n" ^
	"\tmatch l, i, j, update_l with\n" ^
	"\t\t| nil, _, _, _ => nil\n" ^
	"\t\t| l', _, _, nil => l'\n" ^
	"\t\t| x :: l', O, O, _ => nil\n" ^
	"\t\t| x :: l', S n, O, _ => nil\n" ^
	"\t\t| x :: l', O, S m, y :: u_l' => y :: list_slice_update l' 0 m u_l'\n" ^
	"\t\t| x :: l', S n, m, _ => x :: list_slice_update l' n m update_l\n" ^
	"\tend.\n\n" ^
  "Definition list_extend {α: Type} (l: list α) (y: α): list α :=\n" ^
  "\ty :: l.\n\n" ^
  "Definition option_map3 {A B C D: Type} (f: A -> B -> C -> D) (x: option A) (y: option B) (z: option C): option D :=\n" ^ 
	"\tmatch x, y, z with\n" ^
	"\t\t| Some x, Some y, Some z => Some (f x y z)\n" ^ 
	"\t\t| _, _, _ => None\n" ^
	"\tend.\n\n" ^
  "Definition list_map3 {A B C D: Type} (f : A -> B -> C -> D) (xs : list A) (ys : list B) (zs : list C) : list D :=\n" ^
	"\tList.map (fun '(x, (y, z)) => f x y z) (List.combine xs (List.combine ys zs)).\n\n" ^
  "Inductive List_Forall3 {A B C: Type} (R : A -> B -> C -> Prop): list A -> list B -> list C -> Prop :=\n" ^
  "\t| Forall3_nil : List_Forall3 R nil nil nil\n" ^ 
  "\t| Forall3_cons : forall x y z l l' l'',\n"^
  "\t\tR x y z -> List_Forall3 R l l' l'' -> List_Forall3 R (x :: l) (y :: l') (z :: l'').\n\n" ^
  "Class Append (α: Type) := _append : α -> α -> α.\n\n" ^
  "Infix \"@@\" := _append (right associativity, at level 60) : wasm_scope.\n\n" ^
  "Global Instance Append_List_ {α: Type}: Append (list α) := { _append l1 l2 := List.app l1 l2 }.\n\n" ^
  "Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.\n\n" ^
  "Global Instance Append_nat : Append (nat) := { _append n1 n2 := n1 + n2}.\n\n" ^
  "Global Instance Inh_unit : Inhabited unit := { default_val := tt }.\n\n" ^
  "Global Instance Inh_nat : Inhabited nat := { default_val := O }.\n\n" ^
  "Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.\n\n" ^
  "Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.\n\n" ^
  "Global Instance Inh_Z : Inhabited Z := { default_val := Z0 }.\n\n" ^
  "Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.\n\n" ^
  "Global Instance Inh_type : Inhabited Type := { default_val := nat }.\n\n" ^
  "Definition option_to_list {T: Type} (arg : option T) : list T :=\n" ^
	"\tmatch arg with\n" ^
	"\t\t| None => nil\n" ^
  "\t\t| Some a => a :: nil\n" ^ 
	"\tend.\n\n" ^
  "Coercion option_to_list: option >-> list.\n\n" ^
  "Coercion Z.to_nat: Z >-> nat.\n\n" ^
  "Coercion Z.of_nat: nat >-> Z.\n\n" ^
  "Coercion ratz: int >-> rat.\n\n" ^
  "Create HintDb eq_dec_db.\n\n" ^
  "Ltac decidable_equality_step :=\n" ^
  "  do [ by eauto with eq_dec_db | decide equality ].\n\n" ^
  "Lemma eq_dec_Equality_axiom :\n" ^
  "  forall (T : Type) (eq_dec : forall (x y : T), decidable (x = y)),\n" ^
  "  let eqb v1 v2 := is_left (eq_dec v1 v2) in Equality.axiom eqb.\n" ^
  "Proof.\n" ^
  "  move=> T eq_dec eqb x y. rewrite /eqb.\n" ^
  "  case: (eq_dec x y); by [apply: ReflectT | apply: ReflectF].\n" ^
  "Qed.\n\n" ^
  "Class Coercion (A B : Type) := { coerce : A -> B }.\n\n" ^
  "Notation \"x ':>' B\" := (coerce (A:=_) (B:=B) x)\n" ^
  "(at level 70, right associativity).\n\n" ^
  "Definition option_coerce {A B : Type} `{Coercion A B} (a_opt : option A): option B :=\n" ^
  "\tmatch a_opt with\n" ^
  "\t\t| Some a => Some (coerce a)\n" ^
  "\t\t| None => None\n" ^
  "\tend.\n\n" ^
  "Definition list_coerce {A B : Type} `{Coercion A B} (a_list : list A): list B :=\n" ^
  "\tList.map (fun a => coerce a) a_list.\n\n" ^
  "Definition id_coerce {A : Type} (a : A) : A := a.\n\n" ^
  "Definition transitive_coerce {A B C : Type} `{Coercion A B} `{Coercion B C} (a : A): C :=\n" ^
	"\tcoerce (coerce a).\n\n" ^
  "Global Instance option_coercion (A B : Type) {_: Coercion A B}: Coercion (option A) (option B) := { coerce := option_coerce }.\n\n" ^
  "Global Instance list_coercion (A B : Type) {_: Coercion A B}: Coercion (list A) (list B) := { coerce := list_coerce }.\n\n" ^
  "Global Instance id_coercion (A : Type): Coercion A A := { coerce := id_coerce }.\n\n" ^
  "Global Instance transitive_coercion (A B C : Type) `{Coercion A B} `{Coercion B C}: Coercion A C := { coerce := transitive_coerce }.\n\n" ^
  "Open Scope wasm_scope.\n" ^
  "Import ListNotations.\n" ^
  "Import RecordSetNotations.\n\n"

let rec is_valid_def def = 
  match def.it with
  | GramD _ | HintD _ -> false
  | RecD defs -> List.for_all is_valid_def defs
  | _ -> true
  
let string_of_script (il : script) =
  env_ref := Il.Env.env_of_script il;
  exported_string ^
  "(* Generated Code *)\n" ^
  String.concat "" (List.filter is_valid_def il |> List.map (string_of_def true false StringSet.empty))
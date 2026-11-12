open Il.Ast
open Util.Source
(* open Il.Walk *)


(* NOTES FOR CONRAD MEETING *)
(* List of reserved ids in Isabelle? *)
(* coercion *)
(* :> operation *)
(* Struct extension *)
(* axiomatization *)



module StringSet = Set.Make(String)

let ra = "⇒"
let lra = "⟹"

let sanitise_id s =
  let rec aux i =
    if i >= String.length s then ""
    else if List.mem s.[i] ['('; ')'; '\''; ' '; '_'] then aux (i + 1)
    else String.make 1 s.[i] ^ aux (i + 1)
  in aux 0
  


type isabelle_env = (* Il.Env.t ref *)
  { mutable il_env : Il.Env.t;
    mutable wf_lemma_set : StringSet.t
    (* mutable partial_funs : StringSet.t *)
  } 


let new_env () = (* Il.Env.empty *)
  { il_env = Il.Env.empty;
    wf_lemma_set = StringSet.empty
    (*    partial_funs = StringSet.empty *)
  } 

let env_ref = ref (new_env ())

(* let is_partial (id : id) = StringSet.mem id.it !env_ref.partial_funs

let register_partial (id : id) =
  !env_ref.partial_funs <- StringSet.add id.it !env_ref.partial_funs
 *)


let is_let p =
  match p.it with
  | LetPr _ -> true
  | _ -> false


let iter_prem_rels_list = ["list_all"; "list_all2"; "list_all3"; "list_all4"] 
let iter_exp_lst_funcs = ["map"; "list_zipWith"; "list_map3"; "list_map4"] 
let sup_iter_prem_rels_list = ["list_alli"] 
let iter_exp_opt_funcs = ["map_option"; "option_zipWith"; "option_map3"; "option_map4"] 
let error at msg = Util.Error.error at "Isabelle translation" msg 


let rec list_split (f : 'a -> bool) = function 
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

let get_type_var t = 
  match t.it with
  | VarT (id, _) when not (Il.Env.mem_typ !env_ref.il_env id) -> [id.it]
  | _ -> []

let needs_inh_class e =
  match e.it with
  | IdxE _ | TheE _ -> (get_type_var e.note, false)
  | _ -> ([], true)

let needs_inh_class_path p = 
  match p.it with
  | IdxP _ -> (get_type_var p.note, false)
  | _ -> ([], true)

type exptype =
  | LHS
  | RHS
  | REL

let var_prefix = "var_"

let reserved_ids = 
  ["theory"; "imports"; "begin"; "end"; 
   "definition"; "abbreviation"; "notation";
   "datatype"; "codatatype"; "record"; "typedef";
   "fun"; "function"; "primrec";
   "inductive"; "coinductive";
   "axiomatization";
   "lemma"; "theorem"; "corollary";
   "proof"; "qed";
   "assume"; "show"; "have"; "thus"; "then";
   "if"; "else"; "in";
   "fix"; "let"; "next";
   "by"; "apply"; "done";
   "sorry"; "passive"; "declare"; "syntax";
   "list_all3"; "list_all4"; "list_zipWith"; "list_map3"; "list_map4";
   "foralli_help"; "list_foralli"; "option_zipWith";
   "option_map3"; "option_map4"; "option_to_list"; "list_slice";
   "mkseq"; "repeat"; "the";
   "locale"; "context"; "interpretation";
   "class"; "instance";
   "nat"; "int"; "real"; "bool"; "char";
   "list"; "option"; "prod"; "sum";
   "Nil"; "Cons"; "None"; "Some";
   "Inl"; "Inr"; "True"; "False";
   "not"; "and"; "or"; "ALL"; "EX"; "INF"; "SUP";
   "CONST"; "TYPE"; "MIN"; "MAX";
   "id"; "map"; "fold"; "set"; "fst"; "snd";
   "length"; "hd"; "tl"; "Suc" ]
  |> StringSet.of_list

let remove_iter_from_type t =
  match t.it with
  | IterT (t', _) -> t'
  | _ -> t
let empty_name s = match s with
  | "" -> "NO_NAME"
  | _ -> s

let is_typ_quant b = match b.it with
  | TypP _ -> true
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
let ssreflect_square_parens s = "[" ^ s ^ "]"
let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"
let comment_parens s = "(* " ^ s ^ " *)"
let line_parens spc s = "|" ^ spc ^ s ^ spc ^ "|"
let quotes s = "\"" ^ s ^ "\""
let coerce s = "<" ^ s ^ ">"

let family_type_suffix = "entry"

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

type append_kind =
  OptionAppend | ListAppend | RecordAppend | NotAppend

let check_trivial_append env typ = 
  match typ.it with
  | IterT (_, Opt) -> OptionAppend
  | IterT _ -> ListAppend
  | VarT (id, _) -> 
    begin match (Il.Env.find_opt_typ env id) with
    | Some (_, [inst]) when is_record_typ inst -> RecordAppend
    | _ -> NotAppend
    end
  | _ -> NotAppend

    
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
  | `NotOp   -> "~ "
  | `PlusOp  -> ""
  | `MinusOp -> "0 - "
let render_binop binop = 
  match binop with
  | `AndOp   -> " ∧ " 
  | `OrOp    -> " ∨ "
  | `ImplOp  -> " ⟶ "
  | `EquivOp -> " ⟷ "
  | `AddOp   -> " + " 
  | `SubOp   -> " - " 
  | `MulOp   -> " * " 
  | `DivOp   -> " div "
  | `ModOp   -> " mod "
  | `PowOp   -> " ^ " 

let render_cmpop cmpop =
  match cmpop with
  | `EqOp -> " = "
  | `NeOp -> " ≠ "
  | `LtOp -> " < "
  | `GtOp -> " > "
  | `LeOp -> " ≤ "
  | `GeOp -> " ≥ "

let is_atomid a =
  match a.it with
  | Xl.Atom.Atom _ -> true
  | _ -> false 

let render_id id = 
  let id = if id.[String.length id - 1] = '_' then id ^ "underscore" else id in
  let id = if id.[String.length id - 1] = '?' then String.sub id 0 (String.length id - 1) ^ "_questionmark" else id in
  let id = if id.[0] = '_' then "underscore" ^ id else id in
  if StringSet.mem id reserved_ids then "res_" ^ id else id

let render_atom ?(in_mixop = false) a =
  match a.it with
  | Xl.Atom.Atom a when in_mixop -> a
  | Xl.Atom.Atom a -> render_id a
  | _ -> ""

let render_mixop typ_id (m : mixop) = 
  let s = (match m with
    (* | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> render_id a *)
    | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.filter is_atomid atoms |> List.map (render_atom ~in_mixop:true))) (Xl.Mixop.flatten mixop)
    )
  ) in
  (* HACK - should be done in improve ids *)
  match s with
  | "_" -> "mk_" ^ typ_id 
  | s when Il.Env.mem_typ !env_ref.il_env (s $ no_region) -> "mk_" ^ s
  | s -> render_id s

let get_param_id b = 
  match b.it with
  | ExpP (id, _) | TypP id | DefP (id, _, _) | GramP (id, _, _) -> render_id id.it

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
  | _ -> [("_" $ t.at, t)]

let get_type_args t = 
  match t.it with
  | VarT (_, args) -> args
  | _ -> error t.at ("Following type should be a variable type: " ^ Il.Print.string_of_typ t)


let rec render_int_pattern n =
  if n = Z.zero then "0"
  else if n = Z.one then "(Suc 0)"
  else "(Suc " ^ render_int_pattern (Z.sub n Z.one) ^ ")"






let rec render_param_types_list exp_type typids params =
  let typids, resl =
    List.fold_left (fun (typids, resl) param ->
        let paramid = get_param_id param in
        match param.it with
        | ExpP (_, typ) -> typids, (paramid, render_type exp_type typids typ) :: resl
        | TypP id -> StringSet.add id.it typids, resl
        | DefP (_, params, typ) ->
           let typids', resl' = render_param_types exp_type typids params in
           typids, (paramid, parens (resl' ^ render_type exp_type typids' typ)) :: resl
        | GramP _ -> error param.at ("Unsupported param: " ^ Il.Print.string_of_param param)
      ) (typids, []) params in
  typids, List.rev resl
and render_param_types exp_type typids params =
  let typids, resl = render_param_types_list exp_type typids params in
  typids, string_of_list_suffix (" " ^ ra ^ " ") (" " ^ ra ^ " ") snd resl

and render_typ_arg exp_type typids a =
  match a.it with
  | ExpA { it = NumE (`Nat n) ; _ }
    | ExpA { it = NumE (`Int n) ; _ } when n >= Z.zero ->
     None, render_int_pattern n
  | ExpA e -> None, render_exp exp_type typids e
  | TypA t -> Some t, ""
  | DefA id -> None, render_id id.it 
  | _ -> error a.at ("Unsupported arg: " ^ Il.Print.string_of_arg a)

and render_typ_args exp_type typids args =
  let resl = List.map (render_typ_arg exp_type typids) args in
  List.filter_map fst resl, string_of_list_prefix " " " " snd resl

and string_of_argsl exp_type typids = function
  | [] -> ""
  | [t] -> render_type exp_type typids t ^ " "
  | l -> string_of_list "(" ") " ", " (render_type exp_type typids) l


and render_type exp_type typids typ = 
  let rt_func = render_type exp_type typids in
  match typ.it with
  | VarT (id, []) -> if StringSet.mem id.it typids then "'" ^ id.it else render_id id.it
  | VarT (id, args) ->
     let argsl, argsr = render_typ_args exp_type typids args in
     parens (string_of_argsl exp_type typids argsl ^ render_id id.it ^ if argsr = " " then "" else argsr)
  | BoolT -> "bool"
  | NumT nt -> render_numtyp nt
  | TextT -> "string"
  | TupT [] -> "unit"
  | TupT typs -> parens (String.concat " * " (List.map (fun (_, t) -> rt_func t) typs))
  | IterT (t, Opt) -> parens (rt_func t ^ " option")
  | IterT (t, _) -> parens (rt_func t ^ " list")

and render_exp exp_type typids exp =
  let r_func = render_exp exp_type typids in
  match exp.it with 
  | VarE id -> render_id id.it
  | BoolE b -> if b then "True" else "False"
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
      | i, n when i >= n -> parens ("snd " ^ r_func e)
      | _ -> parens ("fst " ^ (make_proj_chain idx (len - 1) e))
    in
    begin match typs with
    | [_] -> r_func e
    | _ -> make_proj_chain i (List.length typs - 1) e 
    end
  | CaseE (m, e) -> 
    let name = Il.Print.string_of_typ_name (Il.Eval.reduce_typ !env_ref.il_env exp.note) |> render_id in
    let exps = transform_case_tup e in
    begin match exps with
    | [] -> render_mixop name m
    | _ -> parens (render_mixop name m ^ " " ^ String.concat " " (List.map r_func exps))
    end
  | UncaseE _ -> error exp.at "Encountered uncase. Run uncase-removal pass"
  | OptE (Some e) -> parens ("Some " ^ r_func e)
  | OptE None -> "None"
  | TheE e -> parens ("the " ^ parens (r_func e))
  | StrE fields -> "⦇ " ^ (String.concat ", " (List.map (fun (a, e) -> 
    render_atom a ^ " = " ^ r_func e) fields)) ^ " ⦈"
  | DotE (e, a) -> 
    parens (render_atom a ^ " " ^ r_func e)
  | CompE (e1, e2) ->
     begin match exp.note.it with
     | VarT (id, _) -> parens ("append_" ^ render_id id.it ^ " " ^ r_func e1 ^ " " ^ r_func e2)
     | _ -> error exp.at "should be record type"
     end
  | ListE [] -> "[]"
  | ListE exps -> ssreflect_square_parens (String.concat ", " (List.map r_func exps)) 
  | LiftE e -> parens ("option_to_list " ^ r_func e)
  | MemE (e1, e2) -> parens (r_func e1 ^ " ∈ set " ^ r_func e2)
  | LenE e1 -> parens ("length " ^ (r_func e1))
  | CatE ({it = ListE [e1]; _}, e2) when exp_type = LHS -> parens (r_func e1 ^ " # " ^ r_func e2) 
  | CatE (e1, e2) -> parens (r_func e1 ^ " @ " ^ r_func e2)
  | IdxE (e1, e2) -> parens (r_func e1 ^ " ! " ^ r_func e2)
  | SliceE (e1, e2, e3) -> parens ("list_slice " ^ r_func e1 ^ " " ^ r_func e2 ^ " " ^ r_func e3)
  | UpdE (e1, p, e2) -> render_path_start p typids e1 false e2
  | ExtE (e1, p, e2) -> render_path_start p typids e1 true e2
  | CallE (id, args) -> parens (render_id id.it ^ " " ^ String.concat " " (List.map (render_arg exp_type typids) args)) 
  (* Iter handling *)
  | IterE (e, (ListN (n, Some id), [])) -> 
    parens ("mkseq " ^ render_lambda [id.it] (r_func e) ^ " " ^ (r_func n)) 
  | IterE (e, (ListN (n, None), [])) -> parens ("repeat " ^ (r_func n) ^ " " ^ (r_func e)) 
  | IterE (e, (_, [])) -> r_func e
  | IterE (e, _) when exp_type = LHS -> r_func e
  | IterE (e, (iter, iter_quants)) ->
    let quants = List.map (fun (id, e) -> parens (render_id id.it  ^ " :: " ^ render_type exp_type typids (remove_iter_from_type e.note))) iter_quants in
    let iter_exps = List.map snd iter_quants in 
    let n = List.length iter_quants - 1 in
    let lst = if iter = Opt then iter_exp_opt_funcs else iter_exp_lst_funcs in
    let pred_name = match (List.nth_opt lst n) with 
    | Some s -> s
    | None -> error exp.at ("Iteration " ^ string_of_int n ^ " exceeded the supported amount for isabelle translation")
    in 
    parens (pred_name ^ " " ^ render_lambda quants (r_func e) ^ " " ^ 
    String.concat " " (List.map r_func iter_exps))
  | CvtE (e1, _nt1, nt2) -> parens (r_func e1 ^ " :: " ^ render_numtyp nt2)
  | SubE _ -> error exp.at "Encountered subtype expression. Please run sub pass"
  | IfE (e1, e2, e3) -> parens ("if " ^ r_func e1 ^ " then " ^ r_func e2 ^ " else " ^ r_func e3)

and render_arg exp_type typids a : string = 
  match a.it with
  | ExpA { it = NumE (`Nat n) ; _ }
    | ExpA { it = NumE (`Int n) ; _ } when n >= Z.zero ->
     render_int_pattern n
  | ExpA e -> render_exp exp_type typids e
  | TypA _t -> "" 
  | DefA id -> render_id id.it 
  | _ -> comment_parens ("Unsupported arg: " ^ Il.Print.string_of_arg a)

and render_quant exp_type b =
  match b.it with
  | ExpP (id, typ) -> None, parens (render_id id.it  ^ " :: " ^ render_type exp_type StringSet.empty (* TODO: is this correct? *) typ)
  | TypP id -> Some id.it , ""
  | DefP (id, params, typ) ->
     None, let typids, resl = render_param_types exp_type StringSet.empty params in
     parens (render_id id.it  ^ " :: " ^
     resl ^
     render_type exp_type typids typ)
  | GramP _ -> error b.at ("Unsupported quant: " ^ Il.Print.string_of_quant b)

and render_params_genl prolog epilog exp_type params =
  let typids, resl = render_param_types_list exp_type StringSet.empty params in
  typids, string_of_list prolog epilog " " (fun (id, rend) -> parens (id ^ " :: " ^ rend)) resl

(* PATH Functions *)
and transform_list_path (p : path) = 
  match p.it with   
  | RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) when p'.it = RootP -> []
  | IdxP (p', _) | SliceP (p', _, _) | DotP (p', _) -> p' :: transform_list_path p'

and render_lambda quants text =
  parens ("λ " ^ String.concat " " quants ^ ". " ^ text)

and render_path_start (p : path) typids start_exp is_extend end_exp = 
  let paths = List.rev (p :: transform_list_path p) in
  (render_path paths typids (start_exp.note) p.at 0 (Some start_exp) is_extend end_exp)

and render_path (paths : path list) typids typ at n name is_extend end_exp = 
  let rec render_record_update t1 t2 t3 =
    match t2 with
    | [] -> failwith "path should be nonempty" 
    | [t2] -> parens (t1 ^ " ⦇ " ^ t2 ^ " := " ^ t3 ^ "  ⦈")
    | t2 :: q -> parens (t1 ^ " ⦇ " ^ t2 ^ " := " ^ render_record_update (t2 ^ " " ^ t1) q t3 ^ "  ⦈")
  in
  let r_func_e = render_exp RHS typids in
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
    let extend_term = parens (new_name ^ " @ " ^ r_func_e end_exp) in
    let _, quant = render_quant RHS (ExpP (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_update_func " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ render_lambda [quant] extend_term)
  | [{it = DotP (_p, a); _}] when is_extend -> 
    let projection_term = parens (render_atom a ^ " " ^ r_func_e (list_name n)) in
    let extend_term = parens (projection_term ^ " @ " ^ r_func_e end_exp) in
    render_record_update (r_func_e (list_name n)) [render_atom a] extend_term
  | [{it = SliceP (_, e1, e2); _}] when is_extend -> 
    let extend_term = parens (new_name ^ " @ " ^ r_func_e end_exp) in
    let _, quant = render_quant RHS (ExpP (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_slice_update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ render_lambda [quant] extend_term)
  (* End logic for update *)
  | [{it = IdxP (_, e); _}] -> 
    let _, quant = render_quant RHS (ExpP ("_" $ no_region, new_name_typ) $ no_region) in
    parens ("list_update_func " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [quant] (r_func_e end_exp))
  | [{it = DotP (_p, a); _}] ->
    render_record_update (r_func_e (list_name n)) [render_atom a] (r_func_e end_exp)
  | [{it = SliceP (_, e1, e2); _}] -> 
    parens ("list_slice_update " ^ r_func_e (list_name n) ^ " " ^ r_func_e e1 ^ " " ^ r_func_e e2 ^ " " ^ r_func_e end_exp)
  (* Middle logic *)
  | {it = IdxP (_, e); note; _} :: ps -> 
    let path_term = render_path ps typids note at (n + 1) None is_extend end_exp in
    let new_name = var_prefix ^ string_of_int (n + 1) in 
    let _, quant = render_quant RHS (ExpP (new_name $ no_region, new_name_typ) $ no_region) in
    parens ("list_update_func " ^ r_func_e (list_name n) ^ " " ^ r_func_e e ^ " " ^ render_lambda [quant] path_term)
  | ({it = DotP _; note; _} as p) :: ps -> 
    let (dot_paths, ps') = list_split is_dot (p :: ps) in
    let (end_name, end_atom, dot_paths') = match List.rev dot_paths with
      | {it = DotP (_p, a'); _} :: ds -> 
        (render_atom a', a', ds)
      | _ -> assert false (* Impossible since it has p *)
    in
    let projection_term = List.fold_right (fun p acc -> 
      match p.it with
      | DotP (_, a') -> 
        DotE (acc, a') $$ no_region % p.note
      | _ -> error at "Should be a record access" (* Should not happen *)
    )  dot_paths' (list_name n) in
    let update_fields = (List.map (fun p -> 
      match p.it with
      | DotP (_p', a) -> 
         render_atom a
      | _ -> error at "Should be a record access" 
    ) dot_paths) in
    let new_term = parens (end_name ^ " " ^ r_func_e projection_term) in
    let new_exp = DotE (projection_term, end_atom) $$ no_region % note in 
    if ps' = [] 
      then (
        let final_term = if is_extend then parens (new_term ^ " @ " ^ r_func_e end_exp) else r_func_e end_exp in
        render_record_update (r_func_e (list_name n)) update_fields final_term
      )
      else (
        let path_term = render_path ps' typids note at n (Some new_exp) is_extend end_exp in
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

and render_quants (quants : quant list) =
  let resl = List.map (render_quant RHS) quants in
  List.filter_map fst resl, string_of_list_prefix " " " " snd resl

let render_quants_ids (quants : quant list) = 
  string_of_list_prefix " " " " get_param_id quants

let render_match_quanters params =
  String.concat ", " (List.map get_param_id params)

let render_params =
  render_params_genl " " " " RHS

let render_match_args typids args =
  string_of_list_prefix " " " " (render_arg LHS typids) args



let string_of_relation_args typ =
  (*  render_param_types REL StringSet.empty (transform_case_typ typ) *)
 string_of_list_suffix (" " ^ ra ^ " ") (" " ^ ra ^ " ") (render_type REL StringSet.empty) (transform_case_typ typ) 


let rec render_prem typids prem =
  let r_func = render_prem typids in 
  match prem.it with
  | IfPr exp -> render_exp REL typids exp
  | RulePr (id, args, _m, exp) -> parens (render_id id.it ^ string_of_list_prefix " " " " (render_arg REL typids) args ^ 
    string_of_list_prefix " " " " (render_exp REL typids) (transform_case_tup exp))
  | NegPr p -> parens ("~" ^ r_func p)
  | ElsePr -> error prem.at "Unsupported Else premise" (* "True" (* ^ comment_parens ("Unsupported premise: otherwise") *) (* Will be removed by an else pass *) *)
  | IterPr (p, (ListN (e, Some i), [])) ->
    let pred_name = "holds_upto" in
    pred_name ^ " " ^ render_lambda [i.it] (r_func p) ^ " " ^ (render_exp REL typids e)

  | IterPr (p, (_, [])) -> r_func p

  | IterPr (p, (ListN (_, Some i), ps)) ->
    let quants = List.map (fun (id, e) -> parens (render_id id.it ^ " :: " ^ render_type REL typids (remove_iter_from_type e.note))) ps in
    let iter_exps = List.map snd ps in 
    let n = List.length ps - 1 in
    let pred_name = match (List.nth_opt sup_iter_prem_rels_list n) with 
    | Some s -> s
    | None -> error prem.at ("Iteration " ^ string_of_int n ^ " exceeded the supported amount for isabelle translation")
    in 
    pred_name ^ " " ^ render_lambda (i.it :: quants) (r_func p) ^ " " ^ 
    String.concat " " (List.map (render_exp REL typids) iter_exps)
  | IterPr (p, (iter, ps)) -> 
     let option_conversion s = if iter = Opt then parens ("option_to_list " ^ s) else s in
    let quants = List.map (fun (id, e) -> parens (render_id id.it ^ " :: " ^ render_type REL typids (remove_iter_from_type e.note))) ps in
    let iter_exps = List.map snd ps in 
    let n = List.length ps - 1 in
    let pred_name = match (List.nth_opt iter_prem_rels_list n) with 
    | Some s -> s
    | None -> error prem.at ("Iteration " ^ string_of_int n ^ " exceeded the supported amount for isabelle translation")
    in 
    pred_name ^ " " ^ render_lambda quants (r_func p) ^ " " ^ 
    String.concat " " (List.map (render_exp REL typids) iter_exps |> List.map option_conversion)
  | LetPr (_, e1, e2) ->
     "(let " ^ render_exp LHS typids e1 ^ " = " ^ render_exp RHS typids e2 ^ " in "




let string_of_quantl = function
  | [] -> ""
  | [id] -> "'" ^ id ^ " "
  | l -> string_of_list "(" ") " ", " (fun id -> "'" ^ id) l





let render_typealias id quants typ =
  let quantl, quantr = render_quants quants in
  let rtyp = render_type RHS (StringSet.of_list quantl) typ in
  string_of_quantl quantl ^ id ^ quantr ^ " = " ^ quotes rtyp 


let render_record id quants fields = 
  let _constructor_name = "MK" ^ id in
  let quantl, inhabitance_quanters = render_quants quants in 
  let quanters = render_quants_ids quants in
  let typids = StringSet.of_list quantl in

  (* Standard Record definition *)
  string_of_quantl quantl ^ id ^ inhabitance_quanters ^ " =\n\t" ^ 
  String.concat "\n\t" (List.map (fun (a, (typ, _, _), _) -> 
                            render_atom a ^ " :: " ^ quotes (render_type RHS typids typ)) fields) ^ "\n\n"

  ^
    "definition append_" ^ id ^ inhabitance_quanters ^ " :: \"" ^ id ^ quanters ^ " " ^ ra ^ " " ^ id ^ quanters ^ " " ^ ra ^ " " ^ id ^ quanters ^ "\" where\n" ^
    "\t\"append_" ^ id ^ inhabitance_quanters ^ " arg1 arg2 = ⦇\n\t\t" ^
      String.concat ",\n\t\t" (List.map (fun (a, (t, _, _), _) ->
                                   let record_id' = render_atom a in
                                   match check_trivial_append !env_ref.il_env t with
                                     ListAppend -> record_id' ^ " = " ^ record_id' ^ " arg1 @ " ^ record_id' ^ " arg2"
                                   | OptionAppend -> record_id' ^ " = " ^ record_id' ^ " arg1 @@@ " ^ record_id' ^ " arg2" 
                                   | RecordAppend ->
                                      begin match t.it with
                                      | VarT (id, _) -> record_id' ^ " = append_" ^ id.it ^ " (" ^ record_id' ^ " arg1) (" ^ record_id' ^ " arg2)"
                                      | _ -> error t.at "should be record type" end
                                   | NotAppend -> record_id' ^ " = " ^ record_id' ^ " arg1" (* ^ comment_parens "FIXME - Non-trivial append"  *)
                                 ) fields) ^ "\n\t⦈\"\n\n" 



let rec has_typ id t =
  match t.it with
  | VarT (id', _) -> id'.it = id
  | IterT (t', _) ->  has_typ id t'
  | TupT pairs -> List.exists (fun (_, t') -> has_typ id t') pairs
  | _ -> false



let cant_do_equality quants cases = 
  (List.exists is_typ_quant quants) ||
  (List.exists (fun (_, (_, quants', _), _) -> List.exists is_typ_quant quants') cases)

let render_case_typs typids t = 
  let typs = transform_case_args t in
  string_of_list_prefix " " " " (fun (_i, t) -> 
      quotes (render_type RHS typids t)) typs

let render_variant_typ id quants cases =
  let quantl, quantr = render_quants quants in
  let typids = StringSet.of_list quantl in
  string_of_quantl quantl ^ id ^ quantr ^ " =\n\t" ^
    match cases with
    | [] -> "Dummy " ^ comment_parens "This variant type should have at least one case"
    | (m, (t, _, _), _) :: cases ->
       "  " ^ render_mixop id m ^ render_case_typs typids t ^ "\n\t" ^
         String.concat "\n\t" (List.map (fun (m, (t, _, _), _) ->
                                   "| " ^ render_mixop id m ^ render_case_typs typids t 
                                 )  cases)  


let render_inh_param inhib_type_vars param = 
  match param.it with
  | TypP id when List.mem id.it inhib_type_vars -> Some ("{_ : Inhabited " ^ render_id id.it ^ "}")
  | _ -> None

let render_single_type id at typids params = 
  let is_typ_param p = 
    match p.it with
    | TypP _ -> true
    | _ -> false 
  in
  match List.rev params with
  | {it = ExpP (_, typ); _} :: ps when List.for_all is_typ_param ps -> (render_type RHS typids typ)
  | _ -> error at ("Given projection function: " ^ id ^ " has invalid parameters!")

let close_lets let_prems =
  String.make (List.length let_prems) ')'

let render_function_def id params r_typ clauses = 
  let typids, resl = render_param_types RHS StringSet.empty params in
  id ^ " :: " ^ quotes (resl ^ render_type RHS typids r_typ),
  (List.map
     (fun clause -> match clause.it with
                    | DefD (_, args, exp, prems) ->

                       let (let_prems, others) = List.partition is_let prems in
                       assert (List.for_all (fun o -> o.it = ElsePr) others); 
                       let string_of_let = string_of_list "\n\t\t\t " "\n\t\t\t " "\n\t\t\t " (render_prem typids) let_prems in 
                       
                       quotes (id ^ render_match_args typids args ^ " = " ^ string_of_let ^ render_exp RHS typids exp ^ close_lets let_prems)) clauses
  )

let render_wfness_func_lemma id rule = 
  let RuleD (_, quants, _, _, prems) = rule.it in
  let typids, _l = render_param_types_list RHS StringSet.empty quants in
  (*  let forall_quantifiers = string_of_list "\\<forall> " ".\n\t" " " snd l in *)
  let letprems, others = List.partition is_let prems in
  let string_lets = string_of_list "" "" "\n\t " (render_prem typids) letprems in
  let string_prems = string_of_list "" "" (" " ^ lra ^ "\n\t ") (render_prem typids) others in
  id ^ " :\n\t" ^ quotes ((* forall_quantifiers ^ *) string_lets ^ string_prems ^ close_lets letprems) ^ "\n" ^
  "sorry"

let render_relation id typ rules =
  let resl = string_of_relation_args typ in
  render_id id ^ " :: " ^ quotes (resl ^ "bool"),
  (List.map (fun rule ->
       match rule.it with
       | RuleD (rule_id, quants, _, exp, prems) ->

          let letprems, others = List.partition is_let prems in
          let quantl, _quantr = render_quants quants in
          let quantl = StringSet.of_list quantl in
          (*          let forall_quantifiers = string_of_list "\\<forall> " ". " " " (fun x -> x) quantr in *)
          let string_lets = string_of_list "\t\t" "" "\n\t\t " (render_prem quantl) letprems in
          let string_prems = (* "\n\t\t" ^ *) string_of_list_suffix (" " ^ lra ^ "\n\t\t ") (" " ^ lra ^ "\n\t\t ") (render_prem quantl) others in
          render_id (rule_id.it) ^ " :\n\t\t" ^ quotes ((* forall_quantifiers ^ *) string_lets ^ string_prems ^ render_id id ^ " " ^ String.concat " " (List.map (render_exp REL quantl) (transform_case_tup exp)) ^ close_lets letprems)
     ) rules)

let render_axiom id params r_typ =
  let typids, resl = render_param_types RHS StringSet.empty params in
  id ^ " :: " ^ quotes (resl ^ render_type RHS typids r_typ)

let render_rel_axiom id typ =
  let resl = string_of_relation_args typ in
  id ^ " :: " ^ quotes (resl ^ "bool")

let render_global_declaration id typ exp = 
  id ^ " :: " ^ quotes (render_type RHS StringSet.empty typ) ^ " where\n\t" ^ quotes (id ^ " = " ^ render_exp RHS StringSet.empty exp)

let has_prems c = 
  let only_otherwise prems =
    match prems with
    | [{it = ElsePr; _}] -> true
    | prems when List.for_all is_let prems -> true
    | _ -> false
  in
  match c.it with
  | DefD (_, _, _, prems) -> prems <> [] && not (only_otherwise prems)


let is_axiom def =
  match def.it with
  | DecD (_, _, _, _clauses) -> true
  | _ -> false

type isabelle_header =
  Ifun
| Idef
| Iax
| Irec
| Iind
| Idat
| Itsyn
| Iwf


let is_typ_param x =
  match x.it with
  | TypP _ -> true
  | _ -> false
let is_typ_arg x =
  match x.it with
  | TypA _ -> true
  | _ -> false

let is_wf_lemma d = 
  match d.it with
  | RelD (id, _, _, _, _) when StringSet.mem id.it !env_ref.wf_lemma_set ->
    true
  | _ -> false


(* TODO - revise mutual recursion with other defs such as records and axioms *)
let rec components_of_def def =
  let start = comment_parens (comment_desc_def def ^ " at: " ^ Util.Source.string_of_region def.at) ^ "\n" in
  match def.it with
  | TypD (id, _, [{it = InstD (quants, _, {it = AliasT typ; _}); _}]) -> 
     start , [Itsyn] , [render_typealias (render_id id.it) quants typ] , []
  | TypD (id, _, [{it = InstD (quants, _, {it = StructT typfields; _}); _}])->
     (* TODO: deal with recursive records *)
    start , [Irec] , [render_record (render_id id.it) quants typfields] , []
  | TypD (id, _, [{it = InstD (quants, _, {it = VariantT typcases; _}); _}]) -> 
    start , [Idat] , [render_variant_typ (render_id id.it) quants typcases] , []
  | DecD (id, params, typ, [{it = DefD (quants, args, exp, _); _}])
       when List.for_all is_typ_param params && List.for_all is_typ_arg args && List.for_all is_typ_param quants -> 
    start , [Idef] , [render_global_declaration (render_id id.it) typ exp] , []
  | DecD (id, params, typ, []) ->
     start , [Iax], [render_axiom (render_id id.it) params typ], []
  | DecD (id, params, typ, clauses) when List.exists has_prems clauses ->
    start , [Iax], [render_axiom (render_id id.it) params typ], []
  | DecD (id, params, typ, clauses) ->
     let header, clauses = render_function_def (render_id id.it) params typ (clauses) in
     start, [Ifun], [header], clauses
  | RelD (id, _, _, typ, []) -> 
     start , [Iax], [render_rel_axiom (render_id id.it) typ], []
  | RelD (id, _, _, _, [rule]) when is_wf_lemma def ->
    start , [Iwf], [render_wfness_func_lemma id.it rule], []
  | RelD (id, _, _, typ, rules) -> 
     let header, clauses = render_relation (render_id id.it) typ rules in
     start, [Iind], [header], clauses
  (* Mutual recursion - special handling for isabelle *)
  | RecD defs ->
     let l = List.map components_of_def defs in
     let kwds, hdrs, clauses =
       List.fold_right (fun (_, kwds, hdrs, clauses) (acckwds, acchdrs, accclauses) ->
           kwds @ acckwds, hdrs @ acchdrs, clauses @ accclauses) l ([], [], []) in
     start, kwds, hdrs, clauses

  | _ -> error def.at ("Unsupported def: " ^ Il.Print.string_of_def def)



let string_of_def def =
  let start, kwds, hdrs, clauses = components_of_def def in
  match kwds, hdrs with
  | [Itsyn], [hdr] -> start ^ "type_synonym " ^ hdr ^ "\n\n"
  | Itsyn :: _, _ -> error def.at "Several type aliases defined mutually recursively"
  | [Irec], [hdr] -> start ^ "record " ^ hdr ^ "\n\n"
  | Irec :: _, _ -> error def.at "Several records defined mutually recursively"
  | [Idef], [hdr] -> start ^ "definition " ^ hdr ^ "\n\n"
  | Idef :: _, _ -> error def.at "Several global variables defined mutually recursively"
  | [Iwf], [hdr] -> start ^ "lemma " ^ hdr ^ "\n\n"
  | Iwf :: _,_ -> error def.at "Several well-formedness lemmas defined mutually recursively"
  | Idat :: kwds, _ ->
     if List.for_all (function Idat -> true | _ -> false) kwds
     then start ^ "datatype " ^ String.concat "\n\nand\n\n" hdrs ^ "\n\n"
     else error def.at "datatype defined mutually recursively with something that is not a datatype"
  | Iax :: kwds, _ ->
     if List.for_all (function Iax -> true | _ -> false) kwds
     then start ^ "axiomatization " ^ String.concat "\nand " hdrs ^ "\n\n"
     else error def.at "axiomatization defined mutually recursively with something that is not an axiomatization"
  | Ifun :: kwds, _ ->
     if List.for_all (function Ifun -> true | _ -> false) kwds
                     (*     then start ^ "fun " ^ String.concat "\nand " hdrs ^ " where\n\t\t  " ^ String.concat "\n\t\t| " clauses ^ "\n\n" *)
     then start ^ "function (sequential, domintros) " ^ String.concat "\nand " hdrs ^ " where\n\t\t  " ^ String.concat "\n\t\t| " clauses ^ "\n\tby pat_completeness auto\n\n" 
     else error def.at "function defined mutually recursively with something that is not a function"
  | Iind :: kwds, _ ->
     if List.for_all (function Iind -> true | _ -> false) kwds
     then start ^ "inductive " ^ String.concat "\nand " hdrs ^ " where\n\t  " ^ String.concat "\n\t| " clauses ^ "\n\n"
     else error def.at "inductive defined mutually recursively with something that is not an inductive"
  | [], _ -> ""


let exported_string =
  "(* Imported Code *)\n" ^
  "\timports Main\n" ^ 
  "begin\n\n" ^
  "inductive list_all3 :: \"('a " ^ ra ^ " 'b " ^ ra ^ " 'c " ^ ra ^ " bool) " ^ ra ^ " 'a list " ^ ra ^ " 'b list " ^ ra ^ " 'c list " ^ ra ^ " bool\" where\n" ^
  "\tlist_all3_nil : \"list_all3 R [] [] []\" |\n" ^
  "\tlist_all3_cons: \"R a b c " ^ lra ^ " list_all3 R as bs cs " ^ lra ^ " list_all3 R (a # as) (b # bs) (c # cs)\"\n\n" ^
  "inductive list_all4 :: \"('a " ^ ra ^ " 'b " ^ ra ^ " 'c " ^ ra ^ " 'd " ^ ra ^ " bool) " ^ ra ^ " 'a list " ^ ra ^ " 'b list " ^ ra ^ " 'c list " ^ ra ^ " 'd list " ^ ra ^ " bool\" where\n" ^
  "\tlist_all4_nil : \"list_all4 R [] [] [] []\" |\n" ^
  "\tlist_all4_cons: \"R a b c d " ^ lra ^ " list_all4 R as bs cs ds " ^ lra ^ " list_all4 R (a # as) (b # bs) (c # cs) (d # ds)\"\n\n" ^
  "definition list_zipWith :: \"('a " ^ ra ^ " 'b " ^ ra ^ " 'c) " ^ ra ^ " 'a list " ^ ra ^ " 'b list " ^ ra ^ " 'c list\" where\n" ^
  "\t\"list_zipWith f xs ys = map (λ (x, y). f x y) (zip xs ys)\"\n\n" ^
  "definition list_map3 :: \"('a " ^ ra ^ " 'b " ^ ra ^ " 'c " ^ ra ^ " 'd) " ^ ra ^ " 'a list " ^ ra ^ " 'b list " ^ ra ^ " 'c list " ^ ra ^ " 'd list\" where\n" ^
  "\t\"list_map3 f xs ys zs = map (λ (x, (y, z)). f x y z) (zip xs (zip ys zs))\"\n\n" ^
  "definition list_map4 :: \"('a " ^ ra ^ " 'b " ^ ra ^ " 'c " ^ ra ^ " 'd " ^ ra ^ " 'e) " ^ ra ^ " 'a list " ^ ra ^ " 'b list " ^ ra ^ " 'c list " ^ ra ^ " 'd list " ^ ra ^ " 'e list\" where\n" ^
  "\t\"list_map4 f xs ys zs ws = map (λ (x, (y, (z, w))). f x y z w) (zip xs (zip ys (zip zs ws)))\"\n\n" ^
  "inductive foralli_help :: \"(nat " ^ ra ^ " 'a " ^ ra ^ " bool) " ^ ra ^ " nat " ^ ra ^ " 'a list " ^ ra ^ " bool\" where\n" ^
  "\tforalli_nil : \"foralli_help f n []\" |\n" ^
  "\tforalli_cons : \"f n x " ^ lra ^ " foralli_help f (n + 1) l " ^ lra ^ " foralli_help f n (x # l)\"\n\n" ^
  "definition list_foralli :: \"(nat " ^ ra ^ " 'a " ^ ra ^ " bool) " ^ ra ^ " 'a list " ^ ra ^ " bool\" where\n" ^
  "\t\"list_foralli f xs = foralli_help f 0 xs\"\n\n" ^
  "fun option_zipWith :: \"('a " ^ ra ^ " 'b " ^ ra ^ " 'c) " ^ ra ^ " 'a option " ^ ra ^ " 'b option " ^ ra ^ " 'c option\" where\n" ^
  "\t\"option_zipWith f (Some x) (Some y) = Some (f x y)\" |\n" ^
  "\t\"option_zipWith _ _ _ = None\"\n\n" ^
  "fun option_map3 :: \"('a " ^ ra ^ " 'b " ^ ra ^ " 'c " ^ ra ^ " 'd) " ^ ra ^ " 'a option " ^ ra ^ " 'b option " ^ ra ^ " 'c option " ^ ra ^ " 'd option\" where\n" ^
  "\t\"option_map3 f (Some x) (Some y) (Some z) = Some (f x y z)\" |\n" ^
  "\t\"option_map3 f _ _ _ = None\"\n\n" ^
  "fun option_map4 :: \"('a " ^ ra ^ " 'b " ^ ra ^ " 'c " ^ ra ^ " 'd " ^ ra ^ " 'e) " ^ ra ^ " 'a option " ^ ra ^ " 'b option " ^ ra ^ " 'c option " ^ ra ^ " 'd option " ^ ra ^ " 'e option\" where\n" ^
  "\t\"option_map4 f (Some x) (Some y) (Some z) (Some w) = Some (f x y z w)\" |\n" ^
  "\t\"option_map4 f _ _ _ _ = None\"\n\n" ^
  "fun option_to_list :: \"'a option " ^ ra ^ "'a list\" where\n" ^
  "\t\"option_to_list None = []\" |\n" ^
  "\t\"option_to_list (Some a) = [a]\"\n\n" ^
  "fun list_slice :: \"'a list " ^ ra ^ " nat " ^ ra ^ " nat " ^ ra ^ " 'a list\" where\n" ^
  "\t\"list_slice [] _ _ = []\" |\n" ^
  "\t\"list_slice (x # l) 0 0 = []\" |\n" ^
  "\t\"list_slice (x # l) (Suc n) 0 = []\" |\n" ^
  "\t\"list_slice (x # l) 0 (Suc m) = x # list_slice l 0 m\" |\n" ^
  "\t\"list_slice (x # l) (Suc n) m = list_slice l n m\"\n\n" ^
  "fun mkseq :: \"(nat " ^ ra ^ " 'a) " ^ ra ^ " nat " ^ ra ^ "'a list\" where\n" ^
  "\t\"mkseq _ 0 = []\" |\n" ^
  "\t\"mkseq f (Suc n) = mkseq f n @ [f n]\"\n\n" ^
  "fun repeat :: \"nat " ^ ra ^ " 'a " ^ ra ^ " 'a list\" where\n" ^
  "\t\"repeat 0 _ = []\" |\n" ^
  "\t\"repeat (Suc n) x = x # repeat n x\"\n\n" ^
  "fun list_update_func :: \"'a list " ^ ra ^ " nat " ^ ra ^ " ('a " ^ ra ^ " 'a) " ^ ra ^ " 'a list\" where\n" ^
  "\t\"list_update_func [] _ _ = []\" |\n" ^
  "\t\"list_update_func (x # l) 0 y = (y x) # l\" |\n" ^
  "\t\"list_update_func (x # l) (Suc n) y = x # list_update_func l n y\"\n\n" ^
  "fun list_slice_update :: \"'a list " ^ ra ^ " nat " ^ ra ^ " nat " ^ ra ^ " 'a list " ^ ra ^ " 'a list\" where\n" ^
  "\t\"list_slice_update [] _ _ _ = []\" |\n" ^
  "\t\"list_slice_update l _ _ [] = l\" |\n" ^
  "\t\"list_slice_update (x # l) _ 0 _ = []\" |\n" ^
  "\t\"list_slice_update (x # l) 0 (Suc m) (y # ul) = y # list_slice_update l 0 m ul\" |\n" ^
  "\t\"list_slice_update (x # l) (Suc n) m ul = x # list_slice_update l n m ul\"\n\n" ^
  "fun option_append :: \"'a option " ^ ra ^ " 'a option " ^ ra ^ " 'a option\" (infixl \"@@@\" 70) where\n" ^
  "\t\"option_append (Some x) _ = Some x\" |\n" ^
  "\t\"option_append None y = y\"\n\n" ^
  "fun list_alli_aux :: \"(nat " ^ ra ^ " 'a " ^ ra ^ " bool) " ^ ra ^ " nat " ^ ra ^ " 'a list " ^ ra ^ " bool\" where\n" ^
  "\t\"list_alli_aux f n [] = True\" |\n" ^
  "\t\"list_alli_aux f n (x # q) = (f n x ∧ list_alli_aux f (Suc n) q)\"\n\n" ^
  "definition list_alli :: \"(nat " ^ ra ^ " 'a " ^ ra ^ " bool) " ^ ra ^ " 'a list " ^ ra ^ " bool\" where\n" ^
  "\t\"list_alli f l = list_alli_aux f 0 l\"\n\n" ^
  "definition holds_upto :: \"(nat " ^ ra ^ " bool) " ^ ra ^ " nat " ^ ra ^ " bool\" where\n" ^
  "\t\"holds_upto P n ≡ ∀ i < n. P i\"\n\n"
        




let rec filter_def def = 
  match def.it with
  | GramD _ | HintD _ -> None
  | RecD defs -> Some {def with it = RecD (List.filter_map filter_def defs) } 
  | _ -> Some def

(* let is_partial_hint hint = hint.hintid.it = "partial" *)
let is_wf_func_hint h = h.hintid.it = Middlend.Undep.wf_func_id
let is_wf_rel_hint h = h.hintid.it = Middlend.Undep.wf_rel_id

let register_hints env def =
  match def.it with
  | HintD { it = RelH (id, hints); _} when List.exists is_wf_func_hint hints -> 
    env.wf_lemma_set <- StringSet.add id.it env.wf_lemma_set
  | HintD { it = RelH (id, hints); _} when List.exists is_wf_rel_hint hints -> 
    env.wf_lemma_set <- StringSet.add id.it env.wf_lemma_set
(*  | HintD {it = DecH (id, hints); _} when List.exists is_partial_hint hints ->
    register_partial id *)
  | _ -> () 
     
let string_of_script theoryname (il : script) =
  !env_ref.il_env <- Il.Env.env_of_script il;
  List.iter (register_hints !env_ref) il; 
  let il' = Disamb.transform il in 
  "theory " ^ theoryname ^ "\n" ^
  exported_string ^
  "(* Generated Code *)\n" ^
    String.concat "" (List.filter_map filter_def il' |> List.map (string_of_def (* true false *))) ^  
      "end\n" 
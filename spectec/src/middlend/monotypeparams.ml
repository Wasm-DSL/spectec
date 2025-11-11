open Il.Ast
open Il.Print
open Il
open Util.Source
open Util.Error
open Either

(* Env Creation and utility functions *)

module StringMap = Map.Make(String)
module IdSet = Set.Make(String)

module ExpSet = Set.Make(struct
  type t = Il.Ast.exp
  let compare exp1 exp2 = if Il.Eq.eq_exp exp1 exp2 then 0 
    else String.compare (string_of_exp exp1) (string_of_exp exp2) (* HACK - Need better way to compare expressions, only hurts performance *)
end
)

module TypSet = Set.Make(struct
  type t = Il.Ast.typ
  let compare typ1 typ2 = if Il.Eq.eq_typ typ1 typ2 then 0 
    else String.compare (string_of_typ typ1) (string_of_typ typ2) (* HACK - Need better way to compare types, only hurts performance *)
end
)

type monoenv = 
{
  mutable calls: (ExpSet.t ref) StringMap.t;
  mutable concrete_dependent_types: (TypSet.t ref) StringMap.t;
  mutable il_env: Il.Env.t;
}

let new_env = 
{
  calls = StringMap.empty;
  concrete_dependent_types = StringMap.empty;
  il_env = Il.Env.empty
}

let mono = "Monomorphization"

let map_snd f = List.map (fun (v1, v2) -> (v1, f v2))

let msg_prefix = "Encountered an unbounded type: "


let error at msg = error at mono (msg_prefix ^ msg)

let print_env (m_env : monoenv) = 
  print_endline "Printing the m_env: ";
  print_endline " ";

  print_endline "Function calls:";
  StringMap.iter (fun id exps -> 
    print_string ("Set with key " ^ id ^ "{");
    print_string (String.concat ", " (List.map string_of_exp (ExpSet.elements !exps)));
    print_endline "}") m_env.calls;
  
  print_endline "Dependent Types:";
  StringMap.iter (fun id typs -> 
    print_string ("Set with key " ^ id ^ "{");
    print_string (String.concat ", " (List.map string_of_typ (TypSet.elements !typs)));
    print_endline "}") m_env.concrete_dependent_types
  

let bind_typ m_env' id t =
  if id = "_" then m_env' else
    match StringMap.find_opt id m_env' with 
    | None -> StringMap.add id (ref (TypSet.singleton t)) m_env'
    | Some set -> set := TypSet.add t !set; m_env'

let bind_exp m_env' id t =
  if id = "_" then m_env' else
    match StringMap.find_opt id m_env' with 
    | None -> StringMap.add id (ref (ExpSet.singleton t)) m_env'
    | Some set -> set := ExpSet.add t !set; m_env'

      
let concrete_dep_types_bind m_env id t =
  m_env.concrete_dependent_types <- bind_typ m_env.concrete_dependent_types id t

let function_calls_bind m_env id t =
  m_env.calls <- bind_exp m_env.calls id t

let reduce_type_arg (m_env : Il.Env.t) (arg : arg): arg = 
  (match arg.it with
  | TypA typ -> TypA (Utils.reduce_type_aliasing m_env typ)
  | a -> a
  ) $ arg.at

let rec get_dep_args_typ t = 
  match t.it with
  | VarT (_, args) -> args
  | IterT (t', _) -> get_dep_args_typ t'
  | TupT typs -> List.concat_map (fun (_, t') -> get_dep_args_typ t') typs 
  | _ -> []
  
and get_dep_args arg = 
  match arg.it with
  | TypA typ -> get_dep_args_typ typ
  | _ -> []

let rec create_dep_type args t = 
  (match t.it with
  | VarT (id, []) -> VarT (id, []) $ t.at, args
  | VarT (id, args') when List.length args' <= List.length args -> 
    let part_args, rest = Util.Lib.List.split (List.length args') args in
    VarT (id, part_args) $ t.at, rest
  | IterT (t', iter) -> 
    let t'', rest = create_dep_type args t' in
    IterT (t'', iter) $ t.at, rest
  | TupT typs -> 
    let typs', rest = List.fold_left (fun (typs', args') (e, t') -> 
      let (t'', rest') = create_dep_type args' t' in 
      ((e, t'') :: typs', rest')
    ) ([], args) typs in
    TupT typs' $ t.at, rest
  | _ -> t, []
  )
  
and create_dep_type_args args arg = 
  match arg.it with
  | TypA typ -> TypA (fst (create_dep_type args typ)) $ arg.at
  | _ -> arg
  
let transform_atom (a : atom) = 
  match a.it with
  | Atom s -> s
  | _ -> ""

let is_atomid (a : atom) =
  match a.it with
  | Atom _ -> true
  | _ -> false

let is_type_arg (a : arg) = 
  match a.it with
  | TypA _ | DefA _ -> true
  | _ -> false

let is_type_param (p : param) =
  match p.it with
  | TypP _ | DefP _ -> true
  | _ -> false

(* String transformation functions *)

let to_string_mixop (m : mixop) = match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> a
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )

let rec to_string_exp (exp : exp) : string = 
  match exp.it with
  | BoolE _ | NumE _ | TextE _ -> string_of_exp exp
  | ListE exps -> "l" ^ String.concat "_" (List.map to_string_exp exps) 
  | TupE [] -> ""
  | TupE exps -> String.concat "_" (List.map to_string_exp exps) 
  | CaseE (mixop, {it = TupE []; _}) -> to_string_mixop mixop 
  | CaseE (_mixop, exp) -> to_string_exp exp
  | CvtE (e, _, _) -> to_string_exp e
  | SubE (e, _, _) -> to_string_exp e
  (* | _ -> assert false *)
  | _ -> error exp.at ("Cannot transform " ^ string_of_exp exp ^ " into string")

and to_string_typ (typ : typ) : string = 
  match typ.it with
  | BoolT | NumT _ | TextT -> string_of_typ typ
  | VarT (id, _) -> id.it
  | IterT (typ, iter) -> string_of_typ typ ^ "_" ^ string_of_iter iter
  | TupT [] -> ""
  | TupT exp_typ_pairs -> "tt" ^ String.concat "_" (List.map (fun (_, t) -> to_string_typ t) exp_typ_pairs) 

and to_string_arg (arg : arg): string =
  match arg.it with
  | ExpA exp -> to_string_exp exp
  | TypA typ -> to_string_typ typ
  | DefA id -> id.it
  | _ -> ""

and transform_id_from_args (id : id) (args : arg list): id =
  if args = [] then id else 
  id.it ^ "_mono_" ^ String.concat "_" (List.map to_string_arg args) $ id.at

let create_args_pairings (args_ids : id list) (concrete_args : arg list): Il.Subst.subst =
  List.fold_left (fun acc (id, arg) -> 
    if id.it = "_" then acc else
    match arg.it with
    | ExpA exp -> Il.Subst.add_varid acc id exp
    | TypA typ -> Il.Subst.add_typid acc id typ
    | DefA x -> Il.Subst.add_defid acc id x
    | GramA g -> Il.Subst.add_gramid acc id g
  ) Il.Subst.empty (List.combine args_ids concrete_args)

(* Simple getters which traverse part of the AST *)

let get_dependent_type_args (typ : typ): arg list = 
  match typ.it with  
  | VarT (_, concrete_args) -> concrete_args
  | _ -> error typ.at "Applied monomorphization on a non-concrete dependent type"

let get_function_call (exp : exp): id * arg list =
  match exp.it with
  | CallE (id, args) -> (id, args)
  | _ -> error exp.at "Applied monomorphization on a non-function call expression"

let get_variable_id_from_param (param : param): id =
  match param.it with
  | ExpP (id, _) -> id
  | TypP id -> id
  | DefP (id, _, _) -> id
  | GramP (id, _) -> id

let rec generate_params ids args = 
  match args with
  | [] -> ([], [], [])
  | a :: ags -> 
    let dep_args = get_dep_args a in
    let (new_ids, new_binds, new_params, new_args') = List.fold_left (fun (ids', binds, params, args') a -> 
      match a.it with
      | ExpA e -> 
        let typ_id = to_string_typ e.note in 
        let name = Utils.generate_var ids' typ_id in
        let bind = ExpB (name $ a.at, e.note) $ a.at in
        let new_param = ExpP (name $ e.at, e.note) $ a.at in
        let new_arg = ExpA (VarE (name $ e.at) $$ e.at % e.note) $ e.at in
        (name :: ids', bind :: binds, new_param :: params, new_arg :: args')
      | _ -> assert false
    ) (ids, [], [], []) dep_args in
    let (binds', params', args') = generate_params new_ids ags in
    let a' = create_dep_type_args new_args' a in
    (new_binds @ binds', new_params @ params', a' :: args')

let rec transform_exp (m_env : monoenv) (subst : Subst.subst) (exp : exp): exp =
  let t_func = transform_exp m_env subst in
  (match exp.it with
  | UnE (unop, optyp, e) -> UnE (unop, optyp, t_func e)
  | BinE (binop, optyp, e1, e2) -> BinE (binop, optyp, t_func e1, t_func e2)
  | CmpE (cmpop, optyp, e1, e2) -> CmpE (cmpop, optyp, t_func e1, t_func e2)
  | TupE exps -> TupE (List.map t_func exps)
  | ProjE (e, i) -> ProjE (t_func e, i)
  | CaseE (m, e) -> CaseE (m, t_func e) 
  | UncaseE (e, m) -> UncaseE (t_func e, m)
  | OptE (Some e) -> OptE (Some (t_func e))
  | TheE e -> TheE (t_func e)
  | StrE expfields -> StrE (map_snd t_func expfields)
  | DotE (e, a) -> DotE (t_func e, a)
  | CompE (e1, e2) -> CompE (t_func e1, t_func e2)
  | ListE exps -> ListE (List.map t_func exps)
  | LiftE e -> LiftE (t_func e)
  | MemE (e1, e2) -> MemE (t_func e1, t_func e2)
  | LenE e -> LenE (t_func e)
  | CatE (e1, e2) -> CatE (t_func e1, t_func e2)
  | IdxE (e1, e2) -> IdxE (t_func e1, t_func e2)
  | SliceE (e1, e2, e3) -> SliceE (t_func e1, t_func e2, t_func e3)
  | UpdE (e1, path, e2) -> UpdE (t_func e1, transform_path m_env subst path, t_func e2)
  | ExtE (e1, path, e2) -> ExtE (t_func e1, transform_path m_env subst path, t_func e2)
  | CallE (id, _) when not (Il.Env.mem_def m_env.il_env id) -> 
    (* Must be a function parameter, subst it *)
    (Il.Subst.subst_exp subst exp).it
  | CallE (id, args) ->
    let subst_args = List.map (transform_arg m_env subst) args in
    let (type_args, normal_args) = List.partition is_type_arg subst_args in
    if type_args <> []
    then (
      let r_args = List.map (reduce_type_arg m_env.il_env) type_args in
      let new_id = transform_id_from_args id r_args in
      let extra_args = List.concat_map get_dep_args r_args in
      function_calls_bind m_env id.it (CallE (new_id, r_args) $$ exp.at % exp.note);
      CallE (new_id, extra_args @ normal_args)
      )
    else
      CallE (id, subst_args)
  | IterE (e, iterexp) -> IterE (t_func e, transform_iterexp m_env subst iterexp)
  | CvtE (e, ntyp1, ntyp2) -> CvtE (t_func e, ntyp1, ntyp2)
  | SubE (e, t1, t2) -> SubE (t_func e, transform_type m_env subst t1, transform_type m_env subst t2)
  | e -> e
  ) $$ exp.at % (transform_type m_env subst exp.note)

and transform_iterexp (m_env : monoenv) (subst : Subst.subst) (iterexp : iterexp): iterexp = 
  let (iter, id_exp_pairs) = iterexp in
  (transform_iter m_env subst iter, map_snd (transform_exp m_env subst) id_exp_pairs)

and transform_iter (m_env : monoenv) (subst : Subst.subst) (iter : iter): iter =
  match iter with 
  | ListN (e, id) -> ListN(transform_exp m_env subst e, id)
  | i -> i

and transform_path (m_env : monoenv) (subst : Subst.subst) (path : path): path = 
  (match path.it with
  | RootP -> RootP
  | IdxP (p, e) -> IdxP (transform_path m_env subst p, transform_exp m_env subst e)
  | SliceP (p, e1, e2) -> SliceP (transform_path m_env subst p, transform_exp m_env subst e1, transform_exp m_env subst e2)
  | DotP (p, a) -> DotP (transform_path m_env subst p, a)
  ) $$ path.at % (transform_type m_env subst path.note)

and transform_type (m_env : monoenv) (subst: Subst.subst) (typ : typ): typ = 
  (match typ.it with
  | VarT (id, []) when not (Il.Env.mem_typ m_env.il_env id) -> 
    (* It is a type parameter, subst it *)
    (Il.Subst.subst_typ subst typ).it
  | VarT (id, args) when args <> [] ->
    let subst_args = List.map (transform_arg m_env subst) args in 
    let (type_args, normal_args) = List.partition is_type_arg subst_args in
    if type_args <> [] 
      then (
        let reduced_args = List.map (fun arg -> reduce_type_arg m_env.il_env arg) type_args in
        let extra_args = List.concat_map get_dep_args reduced_args in
        concrete_dep_types_bind m_env id.it (VarT(id, reduced_args) $ typ.at);
        VarT (transform_id_from_args id reduced_args, extra_args @ normal_args) 
      )
      else (VarT (id, subst_args))
  | TupT exp_typ_pairs -> TupT (List.map (fun (e, t) -> (e, transform_type m_env subst t)) exp_typ_pairs)
  | IterT (t, iter) -> IterT (transform_type m_env subst t, transform_iter m_env subst iter)
  | t -> t
  ) $ typ.at

and transform_arg (m_env : monoenv) (subst : Subst.subst) (arg : arg) : arg =
  (match arg.it with
  | ExpA exp -> ExpA (transform_exp m_env subst exp)
  | TypA typ -> TypA (transform_type m_env subst typ)
  | DefA _ -> (Subst.subst_arg subst arg).it
  | _ -> arg.it) $ arg.at
  
and transform_param (m_env : monoenv) (subst : Subst.subst) (param : param) : param =
  (match param.it with 
  | ExpP (id, typ) -> ExpP (id, transform_type m_env subst typ)
  | p -> p
  ) $ param.at

and transform_bind (m_env : monoenv) (subst : Subst.subst) (bind : bind) : bind =
  (match bind.it with
  | ExpB (id, typ) -> ExpB(id, transform_type m_env subst typ)
  | b -> b) $ bind.at
    
and transform_prem (m_env : monoenv) (subst : Subst.subst) (prem : prem): prem = 
  (match prem.it with
  | IfPr e -> IfPr (transform_exp m_env subst e)
  | RulePr (id, m, e) -> RulePr (id, m, transform_exp m_env subst e)
  | IterPr (p, iterexp) -> IterPr (transform_prem m_env subst p, transform_iterexp m_env subst iterexp)
  | ElsePr -> ElsePr
  | LetPr (exp1, exp2, ids) -> LetPr (transform_exp m_env subst exp1, transform_exp m_env subst exp2, ids)
  | NegPr p -> NegPr (transform_prem m_env subst p)
  ) $ prem.at

and transform_sym m_env subst s = 
  (match s.it with
  | VarG (id, args) -> VarG (id, List.map (transform_arg m_env subst) args)
  | SeqG syms -> SeqG (List.map (transform_sym m_env subst) syms)
  | AltG syms -> AltG (List.map (transform_sym m_env subst) syms)
  | RangeG (syml, symu) -> RangeG (transform_sym m_env subst syml, transform_sym m_env subst symu)
  | IterG (sym, (iter, id_exp_pairs)) -> IterG (transform_sym m_env subst sym, (transform_iter m_env subst iter, 
      List.map (fun (id, exp) -> (id, transform_exp m_env subst exp)) id_exp_pairs)
    )
  | AttrG (e, sym) -> AttrG (transform_exp m_env subst e, transform_sym m_env subst sym)
  | sym -> sym 
  ) $ s.at 


(* TODO think about how to resolve type params for type families*)
and transform_family_type_instances (_m_env : monoenv) (params : param list) (id : id) (insts : inst list) =
  Left (TypD (id, params, insts) $ id.at)

let typ_bind subst b = 
  match b.it with
  | TypB id -> not (Subst.mem_typid subst id)
  | DefB (id, _, _) -> not (Subst.mem_defid subst id)
  | _ -> true

let typ_arg subst a = 
  let free = Free.free_arg a in
  let typids = free.typid in 
  let defids = free.defid in 
  not (
    Free.Set.exists (fun id -> Subst.mem_typid subst (id $ no_region)) typids ||
    Free.Set.exists (fun id -> Subst.mem_defid subst (id $ no_region)) defids
  )

let transform_type_creation (m_env : monoenv) (id : id) params (inst : inst) at =
  match inst.it with 
    | InstD (binds, args, deftyp) -> 
      let type_params, rest = List.partition is_type_param params in 
      let transform_deftyp func = match type_params, StringMap.find_opt id.it m_env.concrete_dependent_types with
      | [], None -> (* Means its a normal type *) 
        Left (TypD (id, params, [InstD (binds, args, func Il.Subst.empty) $ inst.at]) $ at)
      | _, None -> 
        print_endline ("WARNING: dependent type " ^ id.it ^ " is not being used, removing it.");
        Right [] (* Remove the dependent type as not used *)
      | _, Some set_ref ->
        Right (List.map ( fun t -> 
          let dep_args = get_dependent_type_args t in 
          let ids = List.map (fun i -> (Utils.get_param_id i).it) params in 
          let used_param_ids = List.map get_variable_id_from_param type_params in 
          let (new_binds, new_params, dep_args') = generate_params ids dep_args in
          let subst = create_args_pairings used_param_ids dep_args' in 
          let def' = TypD (transform_id_from_args id dep_args, new_params @ rest, 
          [InstD (
          new_binds @ List.filter (typ_bind subst) binds 
                    |> List.map (transform_bind m_env subst), 
          List.map Utils.make_arg_from_bind new_binds @ List.filter (typ_arg subst) args 
                                                 |> List.map (transform_arg m_env subst), 
          func subst) $ inst.at]) in
          (def' $ inst.at)
        ) (TypSet.elements !set_ref))
      in
      (match deftyp.it with 
      | AliasT typ -> transform_deftyp (fun subst -> AliasT (transform_type m_env subst typ) $ deftyp.at) 
      | StructT typfields -> (
        transform_deftyp (fun subst -> StructT (List.map (fun (a, (bs, t, prems), hints) -> 
            (a, (List.map (transform_bind m_env subst) bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typfields) 
          $ deftyp.at)
      )
      | VariantT typcases -> 
        transform_deftyp (fun subst -> VariantT (List.map (fun (m, (bs, t, prems), hints) -> 
          (m, (List.map (transform_bind m_env subst) bs, transform_type m_env subst t, List.map (transform_prem m_env subst) prems), hints)) typcases) 
        $ deftyp.at)
    )

let transform_clause (m_env : monoenv) (subst : Subst.subst) binds (clause : clause) : clause =
  match clause.it with
  | DefD (binds', args, exp, prems) ->
    DefD (binds @ List.filter (typ_bind subst) binds' |> List.map (transform_bind m_env subst), 
    List.map Utils.make_arg_from_bind binds @ List.filter (typ_arg subst) args |> List.map (transform_arg m_env subst), 
    transform_exp m_env subst exp, 
    List.map (transform_prem m_env subst) prems) $ clause.at
        
let transform_function_definitions (m_env : monoenv) (id : id) (params: param list) (return_type : typ) (clauses : clause list) (at : Util.Source.region) =
  let used, unused = List.partition is_type_param params in
  match (StringMap.find_opt id.it m_env.calls), used with
  | _, [] -> (* function has no type parameters *) 
    let subst = Il.Subst.empty in
    Left (DecD (id, params, transform_type m_env subst return_type, List.map (transform_clause m_env subst []) clauses) $ at)
  | None, _ -> (* function is not used *) 
    print_endline ("WARNING: function " ^ id.it ^ " is not being used, removing it.");
    Right []
  | Some set_ref, _ -> (* function has type params *)
    Right (List.map (fun e -> 
      let (new_id, call_args) = get_function_call e in 
      let ids = List.map (fun i -> (Utils.get_param_id i).it) params in 
      let (new_binds, new_params, call_args') = generate_params ids call_args in 
      let used_param_ids = List.map get_variable_id_from_param used in 
      let subst = create_args_pairings used_param_ids call_args' in
      let def' = DecD (new_id.it $ id.at, new_params @ List.map (transform_param m_env subst) unused, 
        transform_type m_env subst return_type, 
        List.map (transform_clause m_env subst new_binds) clauses) in 
      def' $ at
    ) (ExpSet.elements !set_ref))

let transform_rule (m_env : monoenv) (rule : rule) : rule =
  match rule.it with
  | RuleD (rule_id, binds, mixop, exp, prems) ->
    RuleD(rule_id, 
    List.map (transform_bind m_env Subst.empty) binds, 
    mixop, 
    transform_exp m_env Subst.empty exp, 
    List.map (transform_prem m_env Subst.empty) prems) $ rule.at

let transform_prod m_env subst prod = 
  (match prod.it with 
  | ProdD (binds, sym, exp, prems) -> ProdD (List.map (transform_bind m_env subst) binds,
    transform_sym m_env subst sym,
    transform_exp m_env subst exp,
    List.map (transform_prem m_env subst) prems
  )) $ prod.at

let rec transform_def m_env def =
  (match def.it with
  | TypD (id, params, [inst]) when Utils.check_normal_type_creation inst -> 
    transform_type_creation m_env id params inst def.at
  | TypD (id, params, insts) -> 
    transform_family_type_instances m_env params id insts
  | RelD (id, mixop, typ, rules) -> 
    Left (RelD (id, mixop, typ, List.map (transform_rule m_env) rules) $ def.at)
  | DecD (id, params, typ, clauses) -> 
    transform_function_definitions m_env id params typ clauses def.at
  | RecD defs ->
    let max_iteration = 100 in
    (* 
    For mutual recursion, since we do not know the order of functions, we need to iterate until
    we find no change to the monomorphization list.
    *)
    let rec fix n prev defs = 
      let (normal_defs, mono_list) = List.partition_map (transform_def m_env) defs in
      let flat_m_list = List.concat mono_list in
      if n > max_iteration then error def.at "Reached max iteration for monomorphization" else
      (* For first iteration, if there are no monomorphized functions, just return it as normal *)
      if n = 0 && flat_m_list = prev then Left (RecD (normal_defs) $ def.at) else
      (* Check that there is no change from previous iteration *)
      if flat_m_list = prev 
        then Right [RecD (normal_defs @ flat_m_list) $ def.at] 
        else fix (n + 1) flat_m_list defs
    in
    fix 0 [] defs
  |  GramD (id, params, typ, prods) -> Left (GramD (id, 
    List.map (transform_param m_env Subst.empty) params, 
    transform_type m_env Subst.empty typ, 
    List.map (transform_prod m_env Subst.empty) prods) $ def.at)
  | _ -> Left def
  )

let rec reorder_monomorphized_functions m_env mono_list d =
  let rec get_ids d = 
    match d.it with
    | TypD (id, _, _) | RelD (id, _, _, _) | DecD (id, _, _, _) -> [id.it]
    | RecD defs -> List.concat_map get_ids defs
    | _ -> []
  in
  
  let partition_list mono_list def = 
    let free_def_vars = Free.free_def def in
    List.partition (fun d -> 
      let ids = Free.Set.of_list (get_ids d) in
      let typs = Free.Set.is_empty (Free.Set.inter ids free_def_vars.typid) in
      let funcs = Free.Set.is_empty (Free.Set.inter ids free_def_vars.defid) in
      typs && funcs
    ) mono_list 
  in

  let rec repeat_partition lst def =
    let (rest, filtered_list) = partition_list lst def in
    if filtered_list = [] then (rest, []) else
    let (rest', filtered_list') = List.fold_left (fun (rs, fs) def' -> 
      let rs', fs' = repeat_partition rs def' in
      (rs', fs' @ fs)
    ) (rest, []) filtered_list in 
    (rest', filtered_list' @ filtered_list)
  in
  match d.it with
  | RecD defs -> 
    let (rest, new_defs) = List.split (List.map (reorder_monomorphized_functions m_env mono_list) defs) in
    (List.concat rest, [RecD (List.concat new_defs) $ d.at])
  | _ -> repeat_partition mono_list d

(* Main transformation function *)
let transform (script: Il.Ast.script) =
  let m_env = new_env in 
  m_env.il_env <- Il.Env.env_of_script script;
  (* Reverse the script in order to monomorphize nested ones correctly *)
  let transformed_script, mono_list = List.partition_map (transform_def m_env) (List.rev script) in
  print_env m_env;
  let rest, t_script = List.fold_right (fun d (m_list, res) ->
    let (rest, filtered_m_list) = reorder_monomorphized_functions m_env m_list d in
    (rest, d :: filtered_m_list @ res)
  ) transformed_script (List.concat mono_list, []) in
  assert (rest = []);
  print_endline "Mono defs: ";
  print_endline (Il.Print.string_of_script (List.concat mono_list));
  List.rev t_script
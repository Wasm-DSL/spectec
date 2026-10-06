

open Util
open Source
open Il.Ast
open Il
open Il.Walk
open Il.Subst

(* Errors *)

let error at msg = Error.error at "sub expression expansion" msg

(* reduction after subst is cleanup, leave irreducible args to sub pass *)
let reduce_arg_safe env a = try Il.Eval.reduce_arg env a with Il.Eval.Irred -> a

(* Environment *)

(* Global IL env *)
let env_ref = ref Il.Env.empty

let empty_tuple_exp at = TupE [] $$ at % (TupT [] $ at)

(* Computes the cartesian product of a given list. *)
let product_of_lists (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> v :: existing) lst) acc) [[]] lists

let product_of_lists_append (lists : 'a list list) = 
  List.fold_left (fun acc lst ->
    List.concat_map (fun existing -> 
      List.map (fun v -> existing @ [v]) lst) acc) [[]] lists

let get_quant_id q =
  match q.it with
  | ExpP (id, _) | TypP id 
  | DefP (id, _, _) | GramP (id, _, _) -> id.it

let eq_sube (id, t1, t2) (id', t1', t2') =
  Eq.eq_id id id' && Eq.eq_typ t1 t1' && Eq.eq_typ t2 t2'

let collect_sube_exp e = 
  match e.it with
  (* Assumption - nested sub expressions do not exist. Must also be a varE. *)
  | SubE ({it = VarE id; _}, t1, t2) -> ([id, t1, t2], false)
  | _ -> ([], true)

let check_matching c_args match_args = 
  Option.is_some (try 
    Eval.match_list Eval.match_arg !env_ref Subst.empty c_args match_args 
    with Eval.Irred -> None)

let get_case_typ t = 
  match t.it with
  | TupT typs -> typs
  | _ -> ["_" $ t.at, t]

let collect_all_instances case_typ ids at inst =
  match inst.it with
  | InstD (_, _, {it = VariantT typcases; _}) when 
    List.for_all (fun (_, (t, _, _), _) -> t.it = TupT []) typcases  -> 
    List.map (fun (m, _, _) -> ([], CaseE (m, empty_tuple_exp no_region) $$ at % case_typ)) typcases
  | InstD (_, _, {it = VariantT typcases; _}) -> 
    let _, new_cases = 
      List.fold_left (fun (ids', acc) (m, (t, _, _), _) ->
        let typs = get_case_typ t in
        let new_quants, typs' = Utils.improve_ids_quants ids' true t.at typs in
        let exps = List.map (fun (id, t) -> VarE id $$ id.at % t) typs' in 
        let tup_exp = TupE exps $$ at % t in
        let case_exp = CaseE (m, tup_exp) $$ at % case_typ in
        let new_ids = List.map get_quant_id new_quants in 
        (new_ids @ ids', (new_quants, case_exp) :: acc)  
      ) (ids, []) typcases
    in
    new_cases
  | _ -> error at "Expected a variant type"

let rec collect_all_instances_typ ids at typ =
  match typ.it with
  | VarT (var_id, dep_args) -> let (_, insts) = Il.Env.find_typ !env_ref var_id in 
    (match insts with
    | [] -> [] (* Should never happen *)
    | _ -> 
      let inst_opt = List.find_opt (fun inst -> 
        match inst.it with 
        | InstD (_, args, _) -> check_matching dep_args args
      ) insts in
      match inst_opt with
      | None -> error at ("Could not find specific instance for typ: " ^ Il.Print.string_of_typ typ)
      | Some inst -> collect_all_instances typ ids at inst
    )
  | TupT exp_typ_pairs -> 
    let instances_list = List.map (fun (_, t) -> 
      collect_all_instances_typ ids at t
    ) exp_typ_pairs in
    let product = product_of_lists_append instances_list in
    List.map (fun lst -> 
      let quants, exps = List.split lst in 
      List.concat quants, TupE exps $$ at % typ) product
  | _ -> []

let base_sube_collector : (id * typ * typ) list collector = base_collector [] (@)
let sube_collector = { base_sube_collector with collect_exp = collect_sube_exp }

let subst_list_of_subs subs quants =
  let ids = List.map get_quant_id quants in

  (* Collect all cases for the specific subtype, generating any potential quantifiers in the process *)
  let _, cases = 
    List.fold_left (fun (quants, cases) (id, t1, _) -> 
      let ids' = List.map get_quant_id quants @ ids in
      let instances = collect_all_instances_typ ids' id.at t1 in 
      let new_quants = List.concat_map fst instances in
      let cases'' = List.map (fun case_data -> (id, case_data)) instances in
      (new_quants @ quants, cases'' :: cases)
    ) (quants, []) subs 
  in

  (* Compute cartesian product for all cases and generate a subst *)
  let cases' = product_of_lists cases in
  let subst_list = List.map (List.fold_left (fun (quants, subst) (id, (quants', exp)) -> 
    (quants' @ quants, Il.Subst.add_varid subst id exp)) ([], Il.Subst.empty)
  ) cases' in
Lib.List.nub (fun (quants', subst) (quants'', subst') ->
    Eq.eq_list Eq.eq_param quants' quants'' && Map.equal (fun exp exp' -> Eq.eq_exp exp exp') subst.varid subst'.varid
  ) subst_list

(* sub exps in type args of family apps, expand use site to concrete instances *)
let rec collect_sube_in_typ t =
  match t.it with
  | VarT (_, args) -> List.concat_map (collect_arg sube_collector) args
  | TupT pairs -> List.concat_map (fun (_, t') -> collect_sube_in_typ t') pairs
  | IterT (t', _) -> collect_sube_in_typ t'
  | _ -> []

(* collect sub exps in type positions, quant types and note types *)
let collect_typ_subs quants args exps prems =
  let note_collector =
    { base_sube_collector with collect_exp = (fun e -> (collect_sube_in_typ e.note, true)) } in
  let from_quants = List.concat_map (fun q ->
    match q.it with
    | ExpP (_, t) -> collect_sube_in_typ t
    | _ -> []) quants in
  let from_args = List.concat_map (collect_arg note_collector) args in
  let from_exps = List.concat_map (collect_exp note_collector) exps in
  let from_prems = List.concat_map (collect_prem note_collector) prems in
  (* let-premise bound var types aren't expressions, walk separately *)
  let rec letpr_quant_subs p = match p.it with
    | LetPr (qs, _, _) -> List.concat_map (fun q ->
        match q.it with
        | ExpP (_, t) -> collect_sube_in_typ t
        | _ -> []) qs
    | IterPr (p', _) -> letpr_quant_subs p'
    | NegPr p' -> letpr_quant_subs p'
    | _ -> []
  in
  let from_letprs = List.concat_map letpr_quant_subs prems in
  Lib.List.nub eq_sube (from_quants @ from_args @ from_exps @ from_prems @ from_letprs)

let t_rule rule =
  match rule.it with
  | RuleD (id, quants, m, exp, prems) ->
    let subs = collect_typ_subs quants [] [exp] prems in
    if subs = [] then [rule] else
    let subst_list = subst_list_of_subs subs quants in
    List.mapi (fun i (quants', subst) ->
      let new_exp = Il.Subst.subst_exp subst exp in
      let new_prems = Il.Subst.subst_list Il.Subst.subst_prem subst prems in
      let quants_filtered = Lib.List.filter_not (fun b -> match b.it with
        | ExpP (id, _) -> Il.Subst.mem_varid subst id
        | _ -> false
      ) (quants' @ quants) in
      let new_quants, _ = Il.Subst.subst_params subst quants_filtered in
      let id' = if List.length subst_list = 1 then id
        else (id.it ^ "-" ^ string_of_int i) $ id.at in
      RuleD (id', new_quants, m, new_exp, new_prems) $ rule.at
    ) subst_list

let t_clause clause =
  match clause.it with
  | DefD (quants, lhs, rhs, prems) ->
    let lhs_subs = List.concat_map (fun a ->
      Lib.List.nub eq_sube (collect_arg sube_collector a)) lhs in
    let typ_subs = collect_typ_subs quants lhs [rhs] prems in
    let subs = Lib.List.nub eq_sube (lhs_subs @ typ_subs) in
    (* nothing to expand, leave clause untouched, don't re-reduce args (can diverge) *)
    if subs = [] then [clause] else
    let subst_list = subst_list_of_subs subs quants in
    List.map (fun (quants', subst) -> 
      (* Subst all occurrences of the subE id *)
      let new_lhs = Il.Subst.subst_args subst lhs in
      let new_prems = Il.Subst.subst_list Il.Subst.subst_prem subst prems in
      let new_rhs = Il.Subst.subst_exp subst rhs in

      (* Filtering quants - only the subst ids *)
      let quants_filtered = Lib.List.filter_not (fun b -> match b.it with
        | ExpP (id, _) -> Il.Subst.mem_varid subst id
        | _ -> false
      ) (quants' @ quants) in 
      let new_quants, _ = Il.Subst.subst_params subst quants_filtered in
      (* Reduction is done here to remove subtyping expressions *)
      DefD (new_quants, List.map (reduce_arg_safe !env_ref) new_lhs, new_rhs, new_prems) $ clause.at
    ) subst_list

let t_inst inst =
  match inst.it with 
  | InstD (quants, lhs, deftyp) ->
    let subs = List.concat_map (fun a ->
      Lib.List.nub eq_sube (collect_arg sube_collector a)) lhs in
    if subs = [] then [inst] else
    let subst_list = subst_list_of_subs (Lib.List.nub eq_sube subs) quants in
    List.map (fun (quants', subst) -> 
      (* Subst all occurrences of the subE id *)
      let new_lhs = Il.Subst.subst_args subst lhs in
      let new_rhs = Il.Subst.subst_deftyp subst deftyp in

      (* Filtering quants - only the subst ids *)
      let quants_filtered = Lib.List.filter_not (fun b -> match b.it with
        | ExpP (id, _) -> Il.Subst.mem_varid subst id
        | _ -> false
      ) (quants' @ quants) in 

      let new_quants, _ = Il.Subst.subst_params subst quants_filtered in
      (* Reduction is done here to remove subtyping expressions *)
      InstD (new_quants, List.map (reduce_arg_safe !env_ref) new_lhs, new_rhs) $ inst.at
    ) subst_list


let rec t_def def =
  match def.it with
  | RecD defs -> { def with it = RecD (List.map t_def defs) }
  | DecD (id, params, typ, clauses) ->
    { def with it = DecD (id, params, typ, List.concat_map t_clause clauses) }
  | TypD (id, params, insts) ->
    { def with it = TypD (id, params, List.concat_map t_inst insts)}
  | RelD (id, params, m, typ, rules) ->
    { def with it = RelD (id, params, m, typ, List.concat_map t_rule rules) }
  | _ -> def

let transform (defs : script) =
  env_ref := Il.Env.env_of_script defs;
  List.map (t_def) defs
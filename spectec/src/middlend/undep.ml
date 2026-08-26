open Il.Ast
open Util.Source
open Util.Error
open Il
open Il.Walk
open Util

module StringSet = Set.Make(String)

type env = {
  mutable wf_set : StringSet.t;
  mutable il_env : Il.Env.t;

  (* Hint sets *)
  mutable proj_set : StringSet.t;
  mutable tf_set : StringSet.t;
  mutable wfopt_set : StringSet.t;
  mutable il_hintenv : Hints.t 
}

let empty () = {
  wf_set = StringSet.empty;
  il_env = Il.Env.empty;
  proj_set = StringSet.empty;
  tf_set = StringSet.empty;
  wfopt_set = StringSet.empty;
  il_hintenv = Hints.empty
}

let wf_pred_prefix = "wf_"
let rule_prefix = "case_"

let wf_lemma_suffix = "_is_wf"

let wf_hint_id = "wf-relation"
let wf_func_id = "wf-lemma-func"
let wf_rel_id = "wf-lemma-rel"
let wf_opt_id = "wfopt"

type wfstate =
  | WfAll     (* Places wf premises whenever it encounters a term/variable that needs well-formedness check*)
  | WfMinimal (* Places only wf premises in terms in relations and functions that do not appear in the conclusion *)
  | WfNone    (* Does not place any wf premises in relations/functions *)

type wfdef = 
  | Rel of id
  | Func
  
(* State that indicates what the placement algorithm should do *)
let wf_state : wfstate ref = ref WfMinimal

let error at msg = error at "Undep error" msg

let make_arg p = 
  (match p.it with
  | ExpP (id, typ) -> ExpA (VarE id $$ id.at % typ) 
  | TypP id -> TypA (VarT (id, []) $ id.at)
  | DefP (id, _, _) -> DefA id 
  | GramP (id, _, _) -> GramA (VarG (id, []) $ id.at)
  ) $ p.at

let rec split3concat = function
    [] -> ([], [], [])
  | (x,y, z)::l ->
    let (rx, ry, rz) = split3concat l in 
    (x @ rx, y @ ry, z @ rz)

let remove_last_char s =
  if not (String.ends_with ~suffix:"*" s || String.ends_with ~suffix:"?" s) then s else  
  let len = String.length s in
  if len = 0 then s
  else String.sub s 0 (len - 1)

let bind_wf_set env id =
  if id <> "" && id <> "_" then
  env.wf_set <- StringSet.add id env.wf_set

let is_part_of_quant (free_set : Free.sets) p =
  match p.it with
  | ExpP (id, _) -> Free.Set.mem id.it free_set.varid 
  | TypP id -> Free.Set.mem id.it free_set.typid
  | DefP (id, _, _) -> Free.Set.mem id.it free_set.defid
  | GramP (id, _, _) -> Free.Set.mem id.it free_set.gramid

let is_type_arg arg = 
  match arg.it with
  | TypA _ -> true
  | _ -> false

let is_type_param param =
  match param.it with
  | TypP _ -> true
  | _ -> false

let check_iter free_set iter =
  match iter with
  | ListN (_, Some id) -> Free.Set.mem id.it free_set
  | _ -> false

let has_wf_opt env rid = StringSet.mem rid.it env.wfopt_set

let can_optimize wfdef env = 
  match wfdef with
  | Func -> true (* Functions can always be optimized because mode is always known *)
  | Rel id -> has_wf_opt env id (* Relations need wf opt hint *) 

let filter_iter_quants exp iter_quants = 
  let free_vars = (Free.free_exp exp).varid in
  (List.fold_left (fun (free_set, acc) (iter, id_exp_pairs) ->
    let has_definite_iter = check_iter free_set iter in

    let new_id_exp_pairs = List.filter (fun (id, _) -> 
      Free.Set.mem id.it free_set
    ) id_exp_pairs in
    
    (* Must preserve iteration if the iteration variable (i.e. i) is used,
     * EVEN if the list itself is not being used.
     *)
    let new_id_exp_pairs' = if has_definite_iter then id_exp_pairs else
      new_id_exp_pairs 
    in
  
    if new_id_exp_pairs' = [] && (not has_definite_iter) then (free_set, acc) else 
    let iter_vars = List.fold_left (fun acc (_, e) ->
      Free.Set.union acc (Free.free_exp e).varid  
    ) Free.Set.empty new_id_exp_pairs' in 
    let new_set = Free.Set.union iter_vars free_set in
    (new_set, (iter, new_id_exp_pairs') :: acc)
  ) (free_vars, []) iter_quants) 
  |> snd |> List.rev 

let rec create_collector wfdef env iterexps = 
  let base_collector_iters: ((exp * typ) * iterexp list) list collector = base_collector [] (@) in
  { base_collector_iters with collect_exp = collect_userdef_exp wfdef env iterexps; collect_prem = collect_userdef_prem wfdef env iterexps }

and collect_userdef_exp wfdef env iterexps e = 
  match e.it with
  | CallE (id, _) when not (StringSet.mem id.it env.proj_set) && not (can_optimize wfdef env) -> 
    ([((e, e.note), filter_iter_quants e iterexps)], true)
  | CaseE _ | StrE _ -> ([((e, e.note), filter_iter_quants e iterexps)], false)
  | IterE (e1, ((_, id_exp_pairs) as iterexp)) -> 
    let c1 = create_collector wfdef env iterexps in
    let c2 = create_collector wfdef env (iterexp :: iterexps) in 
    (collect_exp c2 e1 @ 
    List.concat_map (fun (_, exp) -> collect_exp c1 exp) id_exp_pairs, false)
  | _ -> ([], true)

and collect_userdef_prem wfdef env iterexps p =
  match p.it with
  | IterPr (p', ((_, id_exp_pairs) as iterexp)) -> 
    let c1 = create_collector wfdef env iterexps in
    let c2 = create_collector wfdef env (iterexp :: iterexps) in 
    (collect_prem c2 p' @
    List.concat_map (fun (_, exp) -> collect_exp c1 exp) id_exp_pairs, false)
  | _ -> ([], true) 

and t_typ t = 
  (match t.it with
  | VarT (id, args) -> VarT (id, List.filter is_type_arg args)
  | typ -> typ
  ) $ t.at

and t_exp env e = 
  (match e.it with
    (* Remove every arg but last for family projections *)
  | CallE (id, args) when StringSet.mem id.it env.proj_set && args <> [] -> 
    CallE (id, [(Lib.List.last args)])
    (* HACK - Change IterE of option and list with no iteration variable into a OptE *)
  | IterE (e1, (Opt, [])) -> 
    OptE (Some e1)
  | IterE (e1, (List, [])) | IterE (e1, (List1, [])) ->
    ListE [e1] 
  | exp -> exp
  ) $$ e.at % e.note

let t_inst env inst = 
  let tf = { base_transformer with transform_exp = t_exp env; transform_typ = t_typ } in
  (match inst.it with
  | InstD (quants, args, deftyp) -> InstD (List.map (transform_param tf) quants |> List.filter is_type_param, List.map (transform_arg tf) args |> List.filter is_type_arg, 
    (match deftyp.it with 
    | AliasT typ -> AliasT (transform_typ tf typ)
    | StructT typfields -> StructT (List.map (fun (a, (typ, c_quants, _prems), hints) ->
        (a, (transform_typ tf typ, List.map (transform_param tf) c_quants, []), hints)  
      ) typfields)
    | VariantT typcases -> 
      VariantT (List.map (fun (m, (typ, c_quants, _prems), hints) -> 
        (m, (transform_typ tf typ, List.map (transform_param tf) c_quants, []), hints)  
      ) typcases)
    ) $ deftyp.at
  )) $ inst.at

let needs_wfness env def = 
  match def.it with
  | TypD (_, _, [{it = InstD (quants, _, deftyp); _}]) ->
    let prems_list = match deftyp.it with
    | StructT typfields -> List.map (fun (_, (_, _, prems), _) -> prems) typfields
    | VariantT typcases -> List.map (fun (_, (_, _, prems), _) -> prems) typcases
    | _ -> []
    in
    List.exists (fun b -> match b.it with
      | ExpP (id, _) -> StringSet.mem id.it env.wf_set
      | _ -> false 
    ) quants ||
    List.exists (fun prems -> prems <> []) prems_list
  | _ -> false

let rec get_wf_pred env (exp, t) = 

  let get_id iter exp =
    match exp.it with
    | VarE id -> id
    | _ -> 
      let s_iter = if iter = Opt then "?" else "*" in
      let free_vars = (Free.free_exp exp).varid |> Free.Set.elements in
      Utils.generate_var free_vars "iter" ^ s_iter $ exp.at 
  in
  let t' = Utils.reduce_type_aliasing env.il_env t in
  let exp' = {exp with note = t'} in 
  match t'.it with
    | VarT (id, args) when StringSet.mem id.it env.wf_set ->
      let new_mixop = Xl.Mixop.(Seq (List.init (List.length args + 1) (fun _ -> Arg ()))) in
      let exp_args = List.filter_map (fun a -> match a.it with 
        | ExpA exp -> Some exp
        | _ -> None
      ) args in
      let tupt = TupT (List.map (fun e -> "_" $ id.at, e.note) exp_args) $ id.at in
      let tuple_exp = TupE (exp_args @ [exp']) $$ id.at % tupt in
      [RulePr (wf_pred_prefix ^ id.it $ id.at, [], new_mixop, tuple_exp) $ id.at]
    | IterT (typ, iter) ->
      let name = get_id iter exp' in
      let name' = remove_last_char name.it $ name.at in 
      let prems = get_wf_pred env (VarE name' $$ name.at % typ, typ) in
      List.map (fun prem -> IterPr (prem, (iter, [(name', exp')])) $ name.at) prems
    | TupT exp_typ_pairs -> 
      let prems = 
        List.mapi (fun idx (_, typ) -> 
          get_wf_pred env (ProjE (exp', idx) $$ exp.at % typ, typ)) exp_typ_pairs |> 
        List.concat 
      in
      prems
    | _ -> []

let non_empty_var id = id.it <> "" && id.it <> "_"

let get_exp_typ q = 
  match q.it with
  | ExpP (id, typ) -> Some (VarE id $$ id.at % typ, typ)
  | _ -> None

let generate_well_formed_rel_hint id at: hint = { hintid = wf_hint_id $ at; hintexp = El.Ast.VarE (id, []) $ at} 
let generate_well_formed_func_hint at: hint = { hintid = wf_func_id $ at; hintexp = El.Ast.SeqE [] $ at} 
let generate_well_formed_rel_lemma_hint at: hint = { hintid = wf_rel_id $ at; hintexp = El.Ast.SeqE [] $ at} 

let create_well_formed_predicate env id inst = 
  let tf = { base_transformer with transform_exp = t_exp env; transform_typ = t_typ} in
  let at = id.at in 
  let user_typ = VarT(id, []) $ at in
  let create_pairs quants = List.split (List.filter_map (fun b -> match b.it with 
      | ExpP (id', typ) -> Some (("_" $ id'.at, typ), (id', typ))
      | _ -> None
    ) quants) in
  let tupt pairs = TupT (pairs @ [("_" $ at, user_typ)]) $ at in
  let new_mixop pairs = Xl.Mixop.(Seq (List.init (List.length pairs + 1) (fun _ -> Arg ()))) in
  let hint = HintD (RelH (wf_pred_prefix ^ id.it $ id.at, [generate_well_formed_rel_hint id at]) $ at) $ at in 
  match inst.it with
  (* Variant well formedness predicate creation *)
  | InstD (quants, _args, {it = VariantT typcases; _}) -> 
    let pairs_without_names, dep_exp_typ_pairs = create_pairs quants in
    let rules = List.mapi (fun i (m, (case_typ, case_quants, prems), _) ->
      let exp_typ_pairs = match case_typ.it with
        | TupT tups -> tups
        | _ -> [("_" $ id.at, case_typ)] 
      in 
      let extra_quants, t_pairs = Utils.improve_ids_quants [] true id.at exp_typ_pairs in
      let new_quants = case_quants @ extra_quants in 
      let exp = TupE (List.map (fun (id, t) -> VarE id $$ id.at % t) t_pairs) $$ at % (TupT t_pairs $ at) in 
      let case_exp = CaseE (m, exp) $$ at % user_typ in
      let tuple_exp = TupE (List.map (fun (id, t) -> VarE id $$ id.at % t) dep_exp_typ_pairs @ [case_exp]) $$ at % tupt pairs_without_names in
      let extra_prems = List.filter_map get_exp_typ new_quants |> List.concat_map (get_wf_pred env) in
      RuleD (id.it ^ "_" ^ rule_prefix ^ Int.to_string i $ at, 
        List.map (transform_param tf) (quants @ new_quants), new_mixop dep_exp_typ_pairs, 
        transform_exp tf tuple_exp, 
        List.map (transform_prem tf) (extra_prems @ prems)
      ) $ at
    ) typcases
    in
    let has_no_prems = List.for_all (fun rule -> match rule.it with
      | RuleD (_, _, _, _, prems) -> prems = []   
    ) rules in
    if has_no_prems then [] else 
    let relation = RelD (wf_pred_prefix ^ id.it $ id.at, [], new_mixop dep_exp_typ_pairs, tupt pairs_without_names, rules) $ at in 
    bind_wf_set env id.it;
    [relation; hint]

  (* Struct/Record well formedness predicate creation *)
  | InstD (quants, _args, {it = StructT typfields; _}) -> 
    let pairs_without_names, dep_exp_typ_pairs = create_pairs quants in
    let atoms = List.map (fun (a, _, _) -> a) typfields in
    let is_wrapped, pairs, rule_prems = split3concat (List.map (fun (_, (t, _, prems), _) ->
      let tups, wrapped = match t.it with 
        | TupT tups when List.exists (fun (id, _) -> non_empty_var id) tups -> tups, true
        | TupT [] -> [], false
        | _ -> [("_" $ id.at, t)], false
      in 
      ([wrapped], tups, prems)
    ) typfields) in

    let (rule_quants, pairs') = Utils.improve_ids_quants [] true at pairs in
    let new_prems = (List.filter_map get_exp_typ rule_quants |> List.concat_map (get_wf_pred env)) @ rule_prems in
    let str_exp = StrE (List.map2 (fun a ((id, t), wrapped) -> 
      let tupt = TupT [(id, t)] $ at in
      let tupe = TupE [VarE id $$ id.at % t] $$ at % tupt in 
      if wrapped then (a, tupe) else 
      (a, VarE id $$ id.at % t)
    ) atoms (List.combine pairs' is_wrapped)) $$ at % user_typ in 
    let tupe = TupE (List.map (fun (id, t) -> VarE id $$ id.at % t) dep_exp_typ_pairs @ [str_exp]) $$ at % tupt pairs_without_names in
    let rule = RuleD (id.it ^ "_" ^ rule_prefix $ id.at, 
      List.map (transform_param tf) (quants @ rule_quants), 
      new_mixop dep_exp_typ_pairs, 
      tupe, 
      List.map (transform_prem tf) (new_prems)) $ at 
    in
  
    if new_prems = [] then [] else 
    let relation = RelD (wf_pred_prefix ^ id.it $ id.at, [], new_mixop dep_exp_typ_pairs, tupt pairs_without_names, [rule]) $ at in 
    bind_wf_set env id.it;
    [relation; hint]
  | _ -> []

let get_wf_terms wfdef env cl exp prems = 
  let is_calle e = match e.it with
    | CallE _ -> true
    | _ -> false
  in
  let exp_terms = collect_exp cl exp in
  let wf_terms = (if !wf_state = WfMinimal && can_optimize wfdef env then [] else exp_terms) @ List.concat_map (collect_prem cl) prems in
  let (call_prems, constr_prems) = List.partition (fun ((e1, _), _) -> is_calle e1) wf_terms in
  let unique_func = Util.Lib.List.nub (fun ((e1, _t1), iterexp1) ((e2, _t2), iterexp2) -> 
    Il.Eq.eq_exp e1 e2 && Il.Eq.eq_list Il.Eq.eq_iterexp iterexp1 iterexp2
  ) in
  let filter_terms_func = Lib.List.filter_not (fun ((e1, _), iterexp1) -> 
    List.exists (fun ((e2, _), iterexp2) -> 
      Il.Eq.eq_exp e1 e2 && Il.Eq.eq_list Il.Eq.eq_iterexp iterexp1 iterexp2
    ) exp_terms
  ) in
  match !wf_state with
  | WfNone -> ([], [])
  | WfMinimal when can_optimize wfdef env -> (call_prems |> unique_func |> filter_terms_func, constr_prems |> unique_func |> filter_terms_func)
  | _ -> (unique_func call_prems, unique_func constr_prems)

let get_extra_prems wfdef env quants exp prems = 
  let cl = create_collector wfdef env [] in 
  let unique_call_terms, unique_constr_terms = get_wf_terms wfdef env cl exp prems in  
  let wf_creation_func = List.concat_map (fun (pair, iterexps) -> 
    List.map (fun prem' -> List.fold_left (fun acc iterexp ->
      IterPr (acc, iterexp) $ acc.at   
    ) prem' iterexps) (get_wf_pred env pair) 
  ) in
  let call_prems, constr_prems = wf_creation_func unique_call_terms, wf_creation_func unique_constr_terms in
    
  (* Leverage the fact that the wellformed predicates are "bubbled up" and remove unnecessary wf preds *)
  let free_vars_exp = (Free.free_exp exp).varid in
  let free_vars = (Free.free_list Free.free_prem constr_prems).varid in 
  let quants_filtered = Lib.List.filter_not (fun b -> 
    match b.it, !wf_state with 
    | ExpP (id, _), WfMinimal when can_optimize wfdef env -> 
      Free.Set.mem id.it free_vars || Free.Set.mem id.it free_vars_exp
    | ExpP (id, _), WfMinimal
    | ExpP (id, _), WfAll -> Free.Set.mem id.it free_vars
    | _ -> true
  ) quants in
  let quant_prems = (List.filter_map get_exp_typ quants_filtered) |> List.concat_map (get_wf_pred env) in
  quant_prems @ call_prems @ constr_prems
    
let t_rule rid env rule = 
  let tf = { base_transformer with transform_exp = t_exp env; transform_typ = t_typ} in
  (match rule.it with
  | RuleD (id, quants, m, exp, prems) -> 
    let extra_prems = get_extra_prems (Rel rid) env quants exp prems in 
    RuleD (id, 
      List.map (transform_param tf) quants, 
      m, 
      transform_exp tf exp, 
      List.map (transform_prem tf) (prems @ extra_prems) 
    )
  ) $ rule.at

let t_clause env clause =
  let tf = { base_transformer with transform_exp = t_exp env; transform_typ = t_typ} in
  (match clause.it with 
  | DefD (quants, args, exp, prems) -> 
    let free_args = Free.free_list Free.free_arg args in 
    (* Only focus on generating wf preds for variables not in the arguments *)
    let filtered_quants = Lib.List.filter_not (is_part_of_quant free_args) quants in
    let extra_prems = get_extra_prems Func env filtered_quants exp prems in 
    DefD (List.map (transform_param tf) quants, 
      List.map (transform_arg tf) args,
      transform_exp tf exp, 
      List.map (transform_prem tf) (prems @ extra_prems)
    )
  ) $ clause.at

let is_not_exp_param param =
  match param.it with
  | ExpP _ -> false
  | _ -> true

let get_def_id def = 
  match def.it with 
  | TypD (id, _, _) -> id
  | _ -> "" $ def.at

let remove_unused_params def =
  match def.it with
  | DecD (id, params, typ, clauses) -> 
    let params' = [Lib.List.last params] in
    let clauses' = List.map (fun clause -> match clause.it with
      | DefD (quants, args, exp, prems) -> 
        let a = Lib.List.last args in
        let free_vars = Free.free_arg a in 
        let filtered_quants = List.filter (is_part_of_quant free_vars) quants in
        DefD (filtered_quants, [a], exp, prems) $ clause.at  
    ) clauses in
    { def with it = DecD (id, params', typ, clauses') }
  | _ -> def

let rec return_type_needs_wfness env (rt : typ) : bool =
  let rt' = Utils.reduce_type_aliasing env.il_env rt in 
  match rt'.it with
  | VarT (id, _) -> StringSet.mem id.it env.wf_set
  | TupT tups -> tups |> List.map snd |> List.exists (return_type_needs_wfness env)
  | IterT (t, _) -> return_type_needs_wfness env t
  | _ -> false

(* HACK: Lemma is actually represented as a relation *)
let generate_wf_lemma_func env tf id params rtyp = 
  let lemma_name = id.it ^ wf_lemma_suffix in 
  let params' = Utils.improve_ids_params params in 
  let wf_prems = List.concat_map (fun p -> match p.it with
    | ExpP (id, typ) -> get_wf_pred env (VarE id $$ id.at % typ, typ)
    | _ -> [] 
  ) params' in 
  let ids = List.map Utils.get_param_id params in
  let text_ids = List.map (fun p -> p.it) ids in 
  let ret_exp_name = Utils.annot_new_name (Utils.generate_var text_ids "ret_val") rtyp in 
  let ret_exp = VarE (ret_exp_name $ id.at) $$ id.at % rtyp in
  let fcall_exp = CallE (id, List.map make_arg params') $$ id.at % rtyp in
  let fcall_prem = IfPr (CmpE (`EqOp, `BoolT, ret_exp, fcall_exp) $$ id.at % (BoolT $ id.at)) $ id.at in
  let wf_conclusion = get_wf_pred env (ret_exp, rtyp) in
  
  let ret_param = ExpP (ret_exp_name $ id.at, rtyp) $ id.at in
  let new_quants = params' @ [ret_param] in 

  let fixed, not_fixed = List.partition_map (fun p -> match p.it with
    | ExpP (id', typ) -> Right (VarE id' $$ id'.at % typ)
    | _ -> Left p
  ) params' 
  in
  let typtups = List.filter_map (fun p -> match p.it with
    | ExpP (id', typ) -> Some (id', typ)
    | _ -> None
  ) params' 
  in
  let tupt = TupT (typtups @ [(ret_exp_name $ id.at, ret_exp.note)]) $ id.at in
  let tupe = TupE (not_fixed @ [ret_exp]) $$ id.at % tupt in 
  let new_mixop = Xl.Mixop.(Seq (List.init (List.length not_fixed + 1) (fun _ -> Arg ()))) in
  let rule = RuleD (
    lemma_name ^ "_0" $ id.at, 
    new_quants, 
    new_mixop,
    tupe,
    wf_prems @ [fcall_prem] @ wf_conclusion
  ) $ id.at
  in
  let hint = HintD (RelH (lemma_name $ id.at, [generate_well_formed_func_hint id.at]) $ id.at) $ id.at in 
  let relation = RelD (lemma_name $ id.at, 
    List.map (transform_param tf) fixed, new_mixop, 
    transform_typ tf tupt, 
    [transform_rule tf rule]) $ id.at in
  [hint; relation]

let generate_wf_lemma_rel env mop tf id params typ modemap = 
  let typs = match typ.it with
    | TupT typs' -> List.mapi (fun i (tid, t) -> 
      let new_id = "var_" ^ Int.to_string i in 
      if tid.it = "_" then (new_id $ tid.at, t) else (tid, t)) typs'
    | _ -> ["var_0" $ no_region, typ]
  in
  let lemma_name = id.it ^ wf_lemma_suffix in 
  assert (List.length typs = Hints.IntMap.cardinal modemap);
  let elements = Hints.IntMap.bindings modemap in
  let quants, typs' = Utils.improve_ids_quants [] true id.at typs in
  let exps = List.map (fun (id', t) -> VarE id' $$ id'.at % t) typs' in 
  let ins, outs = 
    List.map2 (fun (id', t) (_, mode) -> 
      ((VarE id' $$ id'.at % t, t), mode)
    ) typs' elements |>
    List.partition_map (fun (t, mode) -> match mode with
      | Hints.In -> Left t
      | Hints.Out -> Right t
  ) in
  let tupt = TupT (typs') $ id.at in
  let tupe = TupE exps $$ id.at % tupt in
  let wf_inputs = List.concat_map (get_wf_pred env) ins in
  let rel_pr = RulePr (id, List.map make_arg params, mop, tupe) $ id.at in
  let wf_outputs = List.concat_map (get_wf_pred env) outs in
  let new_mixop = Xl.Mixop.(Seq (List.init (List.length quants) (fun _ -> Arg ()))) in
  if outs = [] || wf_outputs = [] then [] else (* No need to generate lemma for bool outputs *)
  let rule = RuleD (lemma_name ^ "_0" $ id.at, params @ quants, new_mixop, tupe, wf_inputs @ [rel_pr] @ wf_outputs) $ id.at in
  let hint = HintD (RelH (lemma_name $ id.at, [generate_well_formed_rel_lemma_hint id.at]) $ id.at) $ id.at in 
  let relation = 
    RelD (lemma_name $ id.at, 
    params, 
    new_mixop, 
    tupt, 
    [rule]) $ id.at in
  [hint; transform_def tf relation]

let rec t_def env def = 
  let tf = { base_transformer with transform_exp = t_exp env; transform_typ = t_typ } in
  match def.it with
  | TypD (id, params, [inst]) when List.exists is_not_exp_param params -> 
    (TypD (id, List.map (transform_param tf) params |> List.filter is_type_param, [inst]) $ def.at, [])
  | TypD (id, params, [inst]) -> 
    let relation = create_well_formed_predicate env id inst in
    (TypD (id, List.map (transform_param tf) params |> List.filter is_type_param, [t_inst env inst]) $ def.at, relation)
  | TypD (_, _, _) -> 
    error def.at "Multiples instances encountered, please run type family removal pass first."
  | RelD (id, params, m, typ, rules) -> 
    let wf_lemma = 
      match (Hints.find_opt id.it env.il_hintenv.modes) with
      | Some modemap -> generate_wf_lemma_rel env m tf id params typ modemap
      | _ -> []
    in
    (RelD (id, List.map (transform_param tf) params |> List.filter is_type_param, m, transform_typ tf typ, List.map (t_rule id env) rules) $ def.at, wf_lemma)
  | DecD (id, params, typ, clauses) -> 
    let d = DecD (id, 
      List.map (transform_param tf) params, 
      transform_typ tf typ, 
      List.map (t_clause env) clauses
      ) $ def.at 
    in
    let is_proj_func = StringSet.mem id.it env.proj_set in
    let t_d = if StringSet.mem id.it env.proj_set then remove_unused_params d else d in
    let wf_lemma = if !wf_state = WfMinimal && return_type_needs_wfness env typ && not is_proj_func
      then generate_wf_lemma_func env tf id params typ 
      else [] 
    in
    (t_d, wf_lemma)
  | GramD (id, params, typ, prods) -> 
    (GramD (id, List.map (transform_param tf) params, transform_typ tf typ, List.map (transform_prod tf) prods) $ def.at, [])
  | RecD defs -> 
    if List.exists (needs_wfness env) defs 
      then List.iter (fun d -> bind_wf_set env (get_def_id d).it) defs; 
    let defs', wf_relations = List.map (t_def env) defs |> List.split in
    let rec_defs = RecD defs' $ def.at in
    if List.concat wf_relations = [] then (rec_defs, []) else
    (rec_defs, [RecD (List.concat wf_relations) $ def.at])
  | HintD hintdef -> (HintD hintdef $ def.at, [])
let has_proj_hint (hint : hint) = hint.hintid.it = Typefamilyremoval.projection_hint_id
let has_tf_hint (hint : hint) = hint.hintid.it = Typefamilyremoval.type_family_hint_id
let has_wfopt_hint (hint : hint) = hint.hintid.it = wf_opt_id

let create_hints env (d : def) = 
  match d.it with
  | HintD {it = DecH (id, hints); _} when List.exists has_proj_hint hints ->
    env.proj_set <- StringSet.add id.it env.proj_set
  | HintD {it = TypH (id, hints); _} when List.exists has_tf_hint hints ->
    env.tf_set <- StringSet.add id.it env.tf_set
  | HintD {it = RelH (id, hints); _} when List.exists has_wfopt_hint hints ->
    env.wfopt_set <- StringSet.add id.it env.wfopt_set
  | _ -> ()
  
let transform (il : script): script =
  let env = empty () in 
  env.il_env <- Il.Env.env_of_script il;
  List.iter (create_hints env) il;
  env.il_hintenv <- Hints.build_il_hints error il;
  List.concat_map (fun d -> 
    let (t_d, wf_relations) = t_def env d in 
    t_d :: wf_relations
  ) il
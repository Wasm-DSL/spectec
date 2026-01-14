open Il.Ast
open Util.Source
open Util
open Il

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type env =
{ 
  il_env : Il.Env.t;
  mutable rel_to_else_map : text list StringMap.t;
  mutable else_set_to_remove : StringSet.t;
  mutable wf_relations : StringSet.t
}

let new_env il = {
  il_env = Il.Env.env_of_script il;
  rel_to_else_map = StringMap.empty;
  else_set_to_remove = StringSet.empty;
  wf_relations = StringSet.empty
}

let is_else_rel_hint hint = hint.hintid.it = Else.else_relation_hint_id
let is_wf_rel_hint hint = hint.hintid.it = Undep.wf_hint_id

let bind_else_set env id = 
  env.else_set_to_remove <- StringSet.add id env.else_set_to_remove

let register_else_rel env id base_rel_id =
  env.rel_to_else_map <- StringMap.update base_rel_id (fun opt -> 
    match opt with
    | Some ids -> Some (id.it :: ids)
    | _ -> Some [id.it]  
  ) env.rel_to_else_map

let register_wf_rel env id = 
  env.wf_relations <- StringSet.add id.it env.wf_relations

let rec register_hints env (def : def) =
  match def.it with
  | HintD {it = RelH (id, hints); _} when List.exists is_wf_rel_hint hints ->
    register_wf_rel env id
  | HintD {it = RelH (id, hints); _} when List.exists is_else_rel_hint hints ->
    begin match List.find_opt is_else_rel_hint hints with
    | Some {hintexp = { it = TextE rel_id; _}; _} -> 
      register_else_rel env id rel_id
    | _ -> ()
    end
  | RecD defs -> List.iter (register_hints env) defs
  | _ -> ()

let (let*) = Option.bind

let is_boolean_prem prem = 
  match prem.it with
  | IfPr _ -> true
  (* | IterPr (p, _) -> is_boolean_prem p *)
  | _ -> false

let neg_cmpop cmpop =
  match cmpop with
  | `LeOp -> `GtOp
  | `GtOp -> `LeOp
  | `GeOp -> `LtOp
  | `LtOp -> `GeOp
  | `EqOp -> `NeOp
  | `NeOp -> `EqOp

let rec neg_exp exp = 
  { exp with it = 
  match exp.it with
  | CmpE (cmpop, optyp, e1, e2) -> CmpE (neg_cmpop cmpop, optyp, e1, e2)
  | BinE (`AndOp, optyp, e1, e2) -> BinE (`OrOp, optyp, neg_exp e1, neg_exp e2)
  | BinE (`OrOp, optyp, e1, e2) -> BinE (`AndOp, optyp, neg_exp e1, neg_exp e2)
  | UnE (`NotOp, _, e1) -> e1.it
  | _ -> UnE (`NotOp, `BoolT, exp) 
  }

let get_exp prem =
  match prem.it with
  | IfPr exp -> Some (neg_exp exp)
  | _ -> None

let is_wf_or_neg_prem else_ids env prem =
  match prem.it with
  | RulePr (id, _, _) -> StringSet.mem id.it env.wf_relations
  | NegPr { it = RulePr (id, _, _); _} -> List.mem id.it else_ids
  | _ -> false

let is_neg_prem else_ids prem = 
  match prem.it with
  | NegPr { it = RulePr (id, _, _); _} -> List.mem id.it else_ids
  | _ -> false

let is_in_bind (free_sets : Free.sets) b = 
  match b.it with
  | ExpB (id, _) -> Free.Set.mem id.it free_sets.varid
  | TypB id -> Free.Set.mem id.it free_sets.typid
  | DefB (id, _, _) -> Free.Set.mem id.it free_sets.defid
  | GramB (id, _, _) -> Free.Set.mem id.it free_sets.gramid

let t_rule env else_ids rule = 
  let RuleD (id, binds, m, exp, prems) = rule.it in
  let* else_id = List.find_opt (fun id -> List.exists (is_neg_prem [id]) prems) else_ids in
  let* else_relation = Il.Env.find_opt_rel env.il_env (else_id $ no_region) in
  let (_, _, rules) = else_relation in
  let free_vars_binds = Free.free_list Free.bound_bind binds in 
  let prems', binds' = List.map (fun r ->
    let RuleD (_, binds', _, _, prems') = r.it in
    let free_vars = Free.diff (Free.free_list Free.free_prem prems') free_vars_binds in 
    Lib.List.filter_not (is_wf_or_neg_prem else_ids env) prems', List.filter (is_in_bind free_vars) binds'
  ) rules |> List.split in
  let prems', binds' = List.concat prems', List.concat binds' in
  
  if prems' = [] || not (List.for_all is_boolean_prem prems') then None else
  let neg_exps = List.filter_map get_exp prems' in
  match neg_exps with
  | [] -> None
  | x :: xs -> 
    let new_exp = List.fold_left (fun acc exp -> BinE (`OrOp, `BoolT, acc, exp) $$ x.at % (BoolT $ x.at)) x xs in 
    let new_prem = IfPr new_exp $ x.at in
    bind_else_set env else_id;
    Some { rule with it = RuleD (id, binds @ binds', m, exp, new_prem :: Lib.List.filter_not (is_neg_prem else_ids) prems) }

let rec t_def env d = 
  {d with it = 
  match d.it with
  | RelD (id, m, typ, rules) when StringMap.mem id.it env.rel_to_else_map -> 
    let else_ids = StringMap.find id.it env.rel_to_else_map in
    RelD (id, m, typ, List.map (fun r -> match (t_rule env else_ids r) with
      | None -> r
      | Some r' -> r'
    ) rules)
  | RecD defs -> RecD (List.map (t_def env) defs)
  | d' -> d'
  }

let is_part_of_else_set env d = 
  match d.it with
  | RelD (id, _, _, _) -> StringSet.mem id.it env.else_set_to_remove
  | _ -> false

let transform defs =
  let env = new_env defs in
  List.iter (register_hints env) defs;
  List.map (t_def env) defs |>
  Lib.List.filter_not (is_part_of_else_set env) 
  

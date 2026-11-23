open Il.Ast
open Util.Source
open Il
open Il.Walk

let construct_let_prem prev_free_vars quants exp1 exp2 at =
  let free_vars = (Free.free_exp exp1).varid in
  let let_quants, rest = List.partition (fun q -> match q.it with
    | ExpP (id, _) -> Free.Set.mem id.it free_vars && not (Free.Set.mem id.it prev_free_vars)
    | _ -> false
  ) quants 
  in
  LetPr (let_quants, exp1, exp2) $ at, rest

let diff = Free.Set.diff
let union = Free.Set.union
let inter = Free.Set.inter
let empty = Free.Set.empty

let valid_exp exp =
  let get_id e = match e.it with
    | VarE id -> Some id
    | IterE (_, (_, [(_, {it = VarE id; _})])) -> Some id
    | _ -> None
  in
  let continue = true in
  let validity = 
    match exp.it with
    | StrE _  
    | CaseE _ 
    | VarE _
    | TupE _ -> true  
    | IterE (e, (iter, [(id, {it = VarE _; _})])) ->
      iter <= List1 &&
      begin match (get_id e) with
      | Some id' -> Il.Eq.eq_id id id'
      | None -> false
      end
    | _ -> false
  in
  (validity, continue)

let inferrable_exp exp =
  let continue = true in
  let validity = 
    match exp.it with
    (* OptE (for some reason) and StrE can never have their types inferred *)
    | OptE _
    | StrE _ -> false 
    | _ -> true
  in
  (validity, continue)
  
let t_prems quants free_vars_start prems =
  let valid_lhs_checker = { forall_base_checker with collect_exp = valid_exp } in
  let valid_rhs_checker = { forall_base_checker with collect_exp = inferrable_exp } in  
  let (_, new_quants, new_prems) = List.fold_left ( fun (free, quants, prev_prems) p ->
    let free_vars = (Free.free_prem p).varid in
    match p.it with
    | IfPr {it = CmpE (`EqOp, _, exp1, exp2); _} 
      when inter (Free.free_exp exp1).varid free = empty &&
           diff (Free.free_exp exp2).varid free  = empty &&
           collect_exp valid_lhs_checker exp1 &&
           collect_exp valid_rhs_checker exp2 -> 
      let (p, new_quants) = construct_let_prem free quants exp1 exp2 p.at in
      (union free free_vars, new_quants, p :: prev_prems)
    | IfPr {it = CmpE (`EqOp, _, exp1, exp2); _} 
      when diff (Free.free_exp exp1).varid free  = empty &&
           inter (Free.free_exp exp2).varid free = empty &&
           collect_exp valid_lhs_checker exp2 &&
           collect_exp valid_rhs_checker exp1 ->
      let (p, new_quants) = construct_let_prem free quants exp2 exp1 p.at in
      (union free free_vars, new_quants, p :: prev_prems)
    | _ -> (union free free_vars, quants, p :: prev_prems) 
  ) (free_vars_start, quants, []) prems in
  (List.rev new_prems, new_quants)

let t_clause c = 
  let { it = DefD (quants, args, exp, prems); _} = c in
  let free_vars = (Free.free_list Free.free_arg args).varid in 
  let (new_prems, new_quants) = t_prems quants free_vars prems in
  { c with it = DefD (new_quants, args, exp, new_prems) }

let rec t_def d = 
  match d.it with
  | DecD (id, params, typ, clauses) ->
    { d with it = DecD (id, params, typ, List.map t_clause clauses) }
  | RecD defs -> RecD (List.map t_def defs) $ d.at
  | _ -> d

let transform defs = List.map t_def defs

open Il.Ast
open Util.Source
open Il
open Il.Walk

let construct_let_prem exp1 exp2 at =
  LetPr (exp1, exp2, Free.Set.elements (Free.free_exp exp1).varid) $ at

let diff = Free.Set.diff
let union = Free.Set.union
let empty = Free.Set.empty

let valid_exp exp =
  let continue = true in
  let validity = 
    match exp.it with
    | StrE _  
    | TupE _
    | CaseE _ 
    | IterE _
    | VarE _ -> true
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
  
let t_prems free_vars_start prems =
  let valid_lhs_checker = { forall_base_checker with collect_exp = valid_exp } in
  let valid_rhs_checker = { forall_base_checker with collect_exp = inferrable_exp } in  
  List.fold_left ( fun (free, prev_prems) p ->
    let free_vars = (Free.free_prem p).varid in
    match p.it with
    | IfPr {it = CmpE (`EqOp, _, exp1, exp2); _} 
      when diff (Free.free_exp exp1).varid free <> empty &&
           diff (Free.free_exp exp2).varid free =  empty &&
           collect_exp valid_lhs_checker exp1 &&
           collect_exp valid_rhs_checker exp2 -> 
      (union free free_vars, construct_let_prem exp1 exp2 p.at :: prev_prems)
    | IfPr {it = CmpE (`EqOp, _, exp1, exp2); _} 
      when diff (Free.free_exp exp1).varid free = empty  &&
           diff (Free.free_exp exp2).varid free <> empty &&
           collect_exp valid_lhs_checker exp2 &&
           collect_exp valid_rhs_checker exp1 ->
      (union free free_vars, construct_let_prem exp2 exp1 p.at :: prev_prems)
    | _ -> (union free free_vars, p :: prev_prems) 
  ) (free_vars_start, []) prems |>
  snd |>
  List.rev

let t_clause c = 
  let { it = DefD (binds, args, exp, prems); _} = c in
  let free_vars = (Free.free_list Free.free_arg args).varid in 
  { c with it = DefD (binds, args, exp, t_prems free_vars prems) }

let rec t_def d = 
  match d.it with
  | DecD (id, params, typ, clauses) ->
    { d with it = DecD (id, params, typ, List.map t_clause clauses) }
  | RecD defs -> RecD (List.map t_def defs) $ d.at
  | _ -> d

let transform defs = List.map t_def defs

(*
Lifts type aliases out of mutual groups.
*)

open Util
open Source
open Il.Ast

(* Errors *)

(* let error at msg = Error.error at "if-then-else introduction" msg *)

let clauses_have_same_args (c1 : clause) (c2 : clause) =
  match (c1.it, c2.it) with
  | (DefD (binds1, args1, _, _), DefD (binds2, args2, _, _)) ->
    Il.Eq.eq_list Il.Eq.eq_bind binds1 binds2 &&
    Il.Eq.eq_list Il.Eq.eq_arg args1 args2
 
let group_clauses_by_same_args clauses =
  let group_helper acc clause =
    match acc with
    | [] -> [[clause]]
    | group :: rest ->
      let representative = List.hd group in
      if clauses_have_same_args representative clause then
        (group @ [clause]) :: rest
      else
        [clause] :: group :: rest
  in
  List.fold_left group_helper [] clauses |> List.rev

let rec is_bool_premise prem =
  match prem.it with
   | IfPr _exp -> true
   | NegPr prem -> is_bool_premise prem
   | _ -> false
   
let is_else_premise prem =
  match prem.it with
  | ElsePr -> true
  | _ -> false

let has_only_else_premise clause =
  match clause.it with
  | DefD (_, _, _, ([_] as prems)) ->
    List.for_all is_else_premise prems
  | _ -> false

let has_only_bool_prems (clause : clause) : exp list option =
  match clause.it with
  | DefD (_, _, _, prems) ->
    if List.for_all is_bool_premise prems then
      Some (List.filter_map (fun prem -> match prem.it with
        | IfPr exp -> Some exp
        | NegPr _ -> None
        | _ -> None) prems)
    else
      None

let rec mk_conj : exp list -> exp = function 
  | [] -> BoolE true $$ (no_region, BoolT $ no_region)
  | [e] -> e
  | e :: rest ->
    BinE (`AndOp, `BoolT, e, mk_conj rest) $$ (no_region, BoolT $ no_region)

let mk_if (cond : exp) (then_exp : exp) (else_exp : exp) : exp =
  IfE (cond, then_exp, else_exp) $$ (no_region, then_exp.note)

let rec t_clause_group_to_expr (clauses : clause list) : exp option =
  match clauses with
  | [] -> None
  | [clause] ->
    if has_only_else_premise clause then
      match clause.it with
      | DefD (_, _, rhs, _) -> Some rhs
    else
      None
  | clause :: rest_clauses ->
    match has_only_bool_prems clause with
    | None -> None
    | Some conds ->
      match clause.it with
      | DefD (_, _, rhs, _) ->
        match t_clause_group_to_expr rest_clauses with
        | None -> None
        | Some else_exp -> Some (mk_if (mk_conj conds) rhs else_exp)

let t_clause_group (clauses : clause list) : clause list =
  match t_clause_group_to_expr clauses with
  | None -> clauses
  | Some exp -> 
    let rep = List.hd clauses in
    let DefD (binds, args, _rhs, _prems) = rep.it in
    [{ rep with it = DefD (binds, args, exp, []) }]


let t_clauses clauses =
  List.concat_map t_clause_group (group_clauses_by_same_args clauses)

let rec t_def (def : def) : def = { def with it = t_def' def.it }
and t_def' = function
  | RecD defs ->
      RecD (List.map t_def defs)
  | DecD (id, params, typ, clauses) ->
    DecD (id, params, typ, t_clauses clauses) 
  | def -> def

let transform (defs : script) : script =
  List.map t_def defs

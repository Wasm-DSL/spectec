(* 
  This pass simplifies definite iteration and non-linear patterns
  by utilizing premises.
  
  It achieves this through the following steps:
  - For non-linear patterns:
    * For each clause, we traverse the arguments and keep track
    of all variables in expressions. If a variable appears more
    than once, we generate a fresh version of the variable and
    keep it for later.
    * Once we have traversed the entire argument list, we use
    the variables tracked to generate new quantifiers and equality
    premises.
  - For definite iteration:
    * For each clause, we traverse the arguments, and collect
    all variables used for definite iteration (i.e. the e in ListN e _ )
    and the respective lists being iterated.
    * Using the collected variables, we iterate through the list to create
    the equality premises.


  For example (for non-linear pattern), take the function:

  def $find(nat, nat* ) : bool
  def $find(n, eps ) = false
  def $find(n, n n'* ) = true
  def $find(n, n_1 n'* ) = $find( n, n'* )
  Would be transformed as such:

  def $find(nat : nat, nat* ) : bool
  def $find{n : nat}(n, []) = false
  def $find{n : nat, `n'*` : nat*, n#1 : nat}(n, [n#1] ++ n'*{n' <- `n'*`}) = true
    -- if (n = n#1)
  def $find{n : nat, n_1 : nat, `n'*` : nat*}(n, [n_1] ++ n'*{n' <- `n'*`}) = $find(n, n'*{n' <- `n'*`})

  For definite iteration:

  def $len( int* ) : nat
  def $len(i^n) = n 

  to
  
  def $len(int* ) : nat
  def $len{n : nat, `i*` : int*}(i^n{i <- `i*`}) = n
    -- if (n = |`i*`|)
*)

open Il.Ast
open Il.Walk
open Util
open Source

module StringMap = Map.Make(String)

let (let*) = Option.bind

let create_eq_prem id typ id' = 
  let idexp = VarE id $$ id.at % typ in
  let idexp' = VarE (id' $ id.at) $$ id.at % typ in
  let exp = CmpE (`EqOp, `BoolT, idexp, idexp') $$ id.at % (BoolT $ id.at) in
  IfPr exp $ id.at 

let create_eq_prem_exp e e' = 
  let exp = CmpE (`EqOp, `BoolT, e, e') $$ e.at % (BoolT $ e.at) in
  IfPr exp $ e.at 

let t_exp varmap exp = 
  match exp.it with
  | VarE id -> 
    let fresh_var = ref id.it in 
    varmap := StringMap.update id.it (fun opt -> 
      match opt with
      | Some lst -> 
        fresh_var := Il.Fresh.fresh_varid id.it;    
        Some (!fresh_var :: lst)
      | None -> Some []
    ) !varmap;
    { exp with it = VarE (!fresh_var $ id.at) }
  | _ -> exp

let c_exp exp = 
  match exp.it with
  | IterE (_, (ListN (e'', _), eps)) -> ([e'', eps], true)
  | _ -> ([], true)

let t_exp2 exp = 
  match exp.it with
  | IterE (e, (_, eps)) -> { exp with it = IterE (e, (List, eps)) }
  | _ -> exp

let t_typ2 typ = 
  match typ.it with
  | IterT (t, ListN _) -> { typ with it = IterT (t, List) }
  | _ -> typ
    
let handle_non_linear clause = 
  let DefD (quants, args, exp, prs) = clause.it in
  let varmap = ref StringMap.empty in 
  let tf = { base_transformer with transform_exp = t_exp varmap; transform_types_of_exp = false } in

  let args' = List.map (transform_arg tf) args in 
  let new_quants, new_prs = List.filter_map (fun q -> match q.it with
    | ExpP (id, typ) -> 
      let* ts = StringMap.find_opt id.it !varmap in
      if ts = [] then None else 
      let q' = List.map (fun id' -> ExpP (id' $ id.at, typ) $ id.at) ts in
      let prs'= List.map (create_eq_prem id typ) ts in
      Some (q', prs')
    | _ -> None
  ) quants |> List.split
  in

  { clause with it = DefD (quants @ (List.concat new_quants), args', exp, prs @ (List.concat new_prs)) }

let handle_definite_iter clause = 
  let DefD (quants, args, exp, prs) = clause.it in
  let lst_cl = base_collector [] (@) in
  let cl = { lst_cl with collect_exp = c_exp } in
  let tf = { base_transformer with transform_exp = t_exp2; transform_typ = t_typ2 } in

  let lst = List.concat_map (collect_arg cl) args in 
  let new_prs = List.concat_map (fun (n, eps) ->
    let lene e = LenE e $$ e.at % (NumT `NatT $ e.at) in 
    List.map (fun (_, e) -> create_eq_prem_exp n (lene e)) eps   
  ) lst 
  in
  
  { clause with it = DefD (quants, List.map (transform_arg tf) args, exp, prs @ new_prs) }

let rec t_def def = 
  match def.it with
  | DecD (id, params, rt, clauses) -> { def with it = DecD (id, params, rt, 
    clauses |> List.map handle_non_linear |> List.map handle_definite_iter) }
  | RecD defs -> { def with it = RecD (List.map t_def defs) }
  | _ -> def

let transform il = List.map t_def il

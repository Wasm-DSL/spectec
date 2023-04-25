(*
This transformation
1) reorders premises and
2) explicitly denotate a premise if it is an assignment.
by performing dataflow analysis.

*)

open Util
open Source
open Il.Ast
open Il.Free

(* for debugging *)
let debug = 0 (* 1 : print msg, 2 : fail *)
let fail prem =
  let msg = "Animation failed:" ^ Il.Print.string_of_prem prem in
  match debug with
  | 1 -> Printf.printf "%s\n" msg
  | 2 -> failwith msg
  | _ -> ()

(* free_lhs_??? are equivalent to free_??? in Il.Free module,
   except k appearing in val^k is not considered free.
   see block and loop instructions *)

let empty =
  {synid = Set.empty; relid = Set.empty; varid = Set.empty; defid = Set.empty}
let free_varid id = {empty with varid = Set.singleton id.it}

let rec free_lhs_exp e =
  match e.it with
  | VarE id -> free_varid id
  | BoolE _ | NatE _ | TextE _ -> empty
  | UnE (_, e1) | LenE e1 | TheE e1 | MixE (_, e1) | SubE (e1, _, _) ->
    free_lhs_exp e1
  | BinE (_, e1, e2) | CmpE (_, e1, e2)
  | IdxE (e1, e2) | CompE (e1, e2) | CatE (e1, e2) ->
    free_list free_lhs_exp [e1; e2]
  | SliceE (e1, e2, e3) -> free_list free_lhs_exp [e1; e2; e3]
  | OptE eo -> free_opt free_lhs_exp eo
  | TupE es | ListE es -> free_list free_lhs_exp es
  | UpdE (e1, p, e2) | ExtE (e1, p, e2) ->
    union (free_list free_lhs_exp [e1; e2]) (free_lhs_path p)
  | StrE efs -> free_list free_lhs_expfield efs
  | CallE (_id, e1) -> free_lhs_exp e1
  | IterE (e1, iter) -> union (free_lhs_exp e1) (free_lhs_iterexp iter)
  | DotE (_t, e1, _) | CaseE (_, e1, _t) -> free_lhs_exp e1

and free_lhs_expfield (_, e) = free_lhs_exp e

and free_lhs_path p =
  match p.it with
  | RootP -> empty
  | IdxP (p1, e) -> union (free_lhs_path p1) (free_lhs_exp e)
  | SliceP (p1, e1, e2) ->
    union (free_lhs_path p1) (union (free_lhs_exp e1) (free_lhs_exp e2))
  | DotP (p1, _) -> free_lhs_path p1

and free_lhs_iterexp (_iter, ids) = free_list free_varid ids

(* Helper for handling free-var set *)
let subset x y = Set.subset x.varid y.varid
let disjoint x y = Set.disjoint x.varid y.varid

(* Check if a given premise is tight:
     all free variables in the premise is known *)
let is_tight env prem = subset (free_prem prem) env

(* Check if a given premise is an assignment:
     is eqaulity, and all free variables in one side of equality is known *)
let is_assign env prem = match prem.it with
| IfPr e -> ( match e.it with
  | CmpE(EqOp, l, r) ->
    if subset (free_exp l) env && disjoint (free_exp r) env then
      Either.Left (AssignPr(r, l) $ prem.at)
    else if subset (free_exp r) env && disjoint (free_exp l) env then
      Either.Left (AssignPr(l, r) $ prem.at)
    else if subset (free_exp l) env || subset (free_exp r) env then (
      (* TODO: if ($bytes_(o0, c) = $mem(z, 0)[(i + n_O) : (o1 / 8)]) *)
      fail prem;
      if subset (free_exp l) env then
        Either.Left (AssignPr(r, l) $ prem.at)
      else
        Either.Left (AssignPr(l, r) $ prem.at)
    )
    else
      Either.Right prem
  | _ -> Either.Right prem
  )
| _ -> Either.Right prem

(* Generate fresh variables *)
let _fresh = ref 0
let fresh _ =
  let id = !_fresh in
  _fresh := id + 1;
  "tmp" ^ string_of_int id

(* Simplify assign target of each premises *)
let rec simplify_assign_target assign =
  let bind_var e = match e.it with
    | VarE _
    | IterE (_, (Opt, _))
    | IterE (_, (List, _))
    | IterE (_, (List1, _)) -> (e, [])
    | _ ->
      let fresh = (VarE ( fresh() $ no_region)) $ no_region in
      let new_assigns = simplify_assign_target (AssignPr (e, fresh) $ no_region) in
      (fresh, new_assigns)
  in
  let bind_vars = List.fold_left (fun (ids, acc) e ->
    let (id, new_assigns) = bind_var e in
    (ids @ [id], acc @ new_assigns)
  ) ([], [])
  in
  match assign.it with
  | AssignPr(target, rhs) -> ( match target.it with
    | VarE _  | IterE _ -> [assign]
    | ListE es ->
      let (vars, new_assigns) = bind_vars es in
      let simplified_assign = AssignPr((ListE vars) $ target.at, rhs) $ assign.at in
      simplified_assign :: new_assigns
    | OptE _ -> [assign]
    | MixE (mixOp, { it = TupE es ; at = _ }) ->
      let (vars, new_assigns) = bind_vars es in
      let simplified_assign = AssignPr(MixE(mixOp, TupE vars $ target.at) $ target.at, rhs) $ assign.at in
      simplified_assign :: new_assigns
    | CaseE (atom, { it = TupE es; at = _}, t) ->
      let (vars, new_assigns) = bind_vars es in
      let simplified_assign = AssignPr(CaseE(atom, TupE vars $ target.at, t) $ target.at, rhs) $ assign.at in
      simplified_assign :: new_assigns
    | CaseE (atom, e, t) ->
      let (var, new_assigns) = bind_var e in
      let simplified_assign = AssignPr(CaseE(atom, var, t) $ target.at, rhs) $ assign.at in
      simplified_assign :: new_assigns
    | CallE _ -> fail assign; [assign]
    | _ -> fail assign; [assign]
    )
  | _ -> failwith "Unreachable"

(* Mutual recursive functions that iteratively select tight and assignment premises,
   effectively sorting the premises as a result *)
let rec select_tight prems acc env = ( match prems with
| [] -> acc
| _ ->
  let (tights, non_tights) = List.partition (is_tight env) prems in
  select_assign non_tights (acc @ tights) env
)
and select_assign prems acc env = ( match prems with
| [] -> acc
| _ -> let (assigns, non_assigns) = List.partition_map (is_assign env) prems in
  ( match assigns with
  | [] -> List.iter fail non_assigns; ( acc @ prems )
  | _ ->
    let new_assigns = List.concat_map simplify_assign_target assigns in
    let new_env = new_assigns |> List.map free_prem |> List.fold_left union env in
    select_tight non_assigns (acc @ new_assigns) new_env
  )
)

(* Animate the list of premises *)
let animate_prems lhs prems =
  _fresh := 0;

  let known_vars = free_lhs_exp lhs in
  let reorder prems = select_tight prems [] known_vars in
  reorder prems

(* Animate rule *)
let animate_rule r = match r.it with
  | RuleD(id, _ , _, _, _) when id.it = "pure" || id.it = "read" -> r (* TODO: remove this line *)
  | RuleD(id, binds, mixop, e, prems) -> (
    match (mixop, e.it) with
    (* lhs* ~> rhs* *)
    | ([ [] ; [Star ; SqArrow] ; [Star]] , TupE ([lhs; _rhs]))
    (* lhs ~> rhs* *)
    | ([ [] ; [SqArrow] ; [Star]] , TupE ([lhs; _rhs]))
    (* lhs ~> rhs *)
    | ([ [] ; [SqArrow] ; []] , TupE ([lhs; _rhs])) ->
      let new_prems = animate_prems lhs prems in
      RuleD(id, binds, mixop, e, new_prems) $ r.at
    | _ -> r
  )

(* Animate def it it is a relation *)
let animate_def d = match d.it with
  | RelD(id, mixop, t, rules) ->
    let new_rules = List.map animate_rule rules in
    RelD(id, mixop, t, new_rules) $ d.at
  | _ -> d

(* Main entry *)
let transform (defs : script) =
  List.map animate_def defs

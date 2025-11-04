open Il.Ast
open Il
open Util.Source

module StringSet = Set.Make(String)

module ExpMap = Map.Make(struct
  type t = exp
  let compare exp1 exp2 = if Eq.eq_exp exp1 exp2 then 0
    (* HACK - Need better way to compare exps, only hurts performance *)
    else String.compare (Print.string_of_exp exp1) (Print.string_of_exp exp2)
end)

type env = {
  mutable env : Il.Env.t;
  mutable rel_set : StringSet.t;
  mutable def_arg_set : StringSet.t
}

let empty_env = {
  env = Il.Env.empty;
  rel_set = StringSet.empty;
  def_arg_set = StringSet.empty
}

let fun_prefix = "fun_"

let apply_iter_to_var id iter =
  match iter with
  | Opt -> id ^ Il.Print.string_of_iter Opt
  | _ -> id ^ Il.Print.string_of_iter List

let get_bind_id b = 
  match b.it with
  | ExpB (id, _) -> id.it
  | TypB id -> id.it
  | DefB (id, _, _) -> id.it
  | GramB (id, _, _) -> id.it

let get_exp_arg a = 
  match a.it with
  | ExpA exp -> exp
  | _ -> assert false

let transform_typ_iter i =
  match i with
  | ListN _ -> 
    (* Definite iterators not allowed in types *)
    List
  | _ -> i

let filter_iter_binds args iter_binds = 
  let free_vars = (Free.free_list Free.free_arg args).varid in
  (List.fold_left (fun (free_set, acc) (iter, id_exp_pairs) -> 
    let new_id_exp_pairs = List.filter (fun (id, _) -> 
      Free.Set.mem id.it free_set
    ) id_exp_pairs in
    if new_id_exp_pairs = [] then (free_set, acc) else 
    let iter_vars = List.fold_left (fun acc (_, e) ->
      Free.Set.union acc (Free.free_exp e).varid  
    ) Free.Set.empty new_id_exp_pairs in 
    let new_set = Free.Set.union iter_vars free_set in
    (new_set, (iter, new_id_exp_pairs) :: acc)
  ) (free_vars, []) iter_binds) 
  |> snd |> List.rev

let rec collect_fcalls_exp iter_binds env e = 
  match e.it with
  | CallE (id, args) when StringSet.mem id.it env.rel_set -> 
    let new_iter_binds = filter_iter_binds args iter_binds in
    ((fun_prefix ^ id.it $ id.at, args, e.note), new_iter_binds, List.length new_iter_binds) ::
    List.concat_map (collect_fcalls_arg iter_binds env) args
  | CallE (_, args) -> List.concat_map (collect_fcalls_arg iter_binds env) args
  | StrE fields -> List.concat_map (fun (_a, e1) -> collect_fcalls_exp iter_binds env e1) fields
  | UnE (_, _, e1) | CvtE (e1, _, _) | LiftE e1 | TheE e1 | OptE (Some e1) 
  | ProjE (e1, _) | UncaseE (e1, _)
  | CaseE (_, e1) | LenE e1 | DotE (e1, _)
  | SubE (e1, _, _) -> collect_fcalls_exp iter_binds env e1
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2)
  | CompE (e1, e2) | MemE (e1, e2)
  | CatE (e1, e2) | IdxE (e1, e2) -> collect_fcalls_exp iter_binds env e1 @ collect_fcalls_exp iter_binds env e2
  | TupE exps | ListE exps -> List.concat_map (collect_fcalls_exp iter_binds env) exps
  | SliceE (e1, e2, e3) -> collect_fcalls_exp iter_binds env e1 @ collect_fcalls_exp iter_binds env e2 @ collect_fcalls_exp iter_binds env e3
  | UpdE (e1, p, e2) 
  | ExtE (e1, p, e2) -> collect_fcalls_exp iter_binds env e1 @ collect_fcalls_path iter_binds env p @ collect_fcalls_exp iter_binds env e2
  | IterE (e1,( (iter, id_exp_pairs) as iterexp)) -> 
    collect_fcalls_exp (iterexp :: iter_binds) env e1 @ collect_fcalls_iter (iterexp :: iter_binds) env iter @
    List.concat_map (fun (_, exp) -> collect_fcalls_exp iter_binds env exp) id_exp_pairs
  | _ -> []

and collect_fcalls_iter iter_binds env i = 
  match i with
  | ListN (e1, _) -> collect_fcalls_exp iter_binds env e1
  | _ -> []
    
and collect_fcalls_arg iter_binds env a =
  match a.it with
  | ExpA exp -> collect_fcalls_exp iter_binds env exp
  | _ -> (* TODO - possibly need to go through all types of args *) 
    []

and collect_fcalls_prem iter_binds env p =
  match p.it with
  | IfPr e | RulePr (_, _, e) -> collect_fcalls_exp iter_binds env e
  | LetPr (e1, e2, _) -> collect_fcalls_exp iter_binds env e1 @ collect_fcalls_exp iter_binds env e2
  | IterPr (p', iterexp) -> collect_fcalls_prem (iterexp :: iter_binds) env p'
  | _ -> [] 

and collect_fcalls_path iter_binds env p =
  match p.it with
  | RootP -> []
  | IdxP (p, e) -> collect_fcalls_path iter_binds env p @ collect_fcalls_exp iter_binds env e
  | SliceP (p, e1, e2) -> collect_fcalls_path iter_binds env p @ collect_fcalls_exp iter_binds env e1 @ collect_fcalls_exp iter_binds env e2
  | DotP (p, _) -> collect_fcalls_path iter_binds env p

let create_fun_prem ids ((id, args, r_typ), iterexps, _) =
  let fresh_var = Utils.generate_var ids "" in
  let var_exp = VarE (fresh_var $ id.at) $$ id.at % r_typ in 
  let new_mixop = [] :: List.init (List.length args + 1) (fun _ -> []) in
  let exps = List.map get_exp_arg args in
  let r_typ_tup = (VarE ("_" $ id.at) $$ id.at % r_typ, r_typ) in 
  let tupt = TupT (List.map (fun e -> VarE ("_" $ id.at) $$ id.at % e.note, e.note) exps @ [r_typ_tup]) $ id.at in
  let tupe = TupE (exps @ [var_exp]) $$ id.at % tupt in 
  let rule_prem = RulePr (id, new_mixop, tupe) $ id.at in
  let new_var, typ, prem = List.fold_left (fun (var, typ, prem) (iter, id_exp_pairs) -> 
    let new_typ = IterT (typ, transform_typ_iter iter) $ id.at in
    let new_var = apply_iter_to_var var iter in
    let var_exp = VarE (new_var $ id.at) $$ id.at % new_typ in
    let new_id_exp_pairs = (var $ id.at, var_exp) :: id_exp_pairs in 
    (new_var, new_typ, IterPr (prem, (iter, new_id_exp_pairs)) $ id.at)
  ) (fresh_var, r_typ, rule_prem) iterexps in
  fresh_var, ExpB (new_var $ id.at, typ) $ id.at, prem

let create_call_map fcalls binds = 
  let fcalls' = Util.Lib.List.nub (fun ((id, args, _), iterexps, _) ((id', args', _), iterexps', _) -> 
    Eq.eq_id id id' &&
    Eq.eq_list Eq.eq_arg args args' &&
    Eq.eq_list Eq.eq_iterexp iterexps iterexps'
  ) fcalls in
  let ids = List.map get_bind_id binds in
  let ids', new_binds, new_prems = List.fold_left (fun acc fcall -> 
    let ids', binds', prems = acc in
    let new_var, bind, prem = create_fun_prem (ids @ ids') fcall in
    new_var :: ids', bind :: binds', prem :: prems
    ) ([], [], []) fcalls' 
  in
  let call_map = List.fold_left2 (fun map var_id ((fun_id, args, typ), _, iter_num) -> 
    let var_exp = VarE (var_id $ fun_id.at) $$ fun_id.at % typ in
    let call_exp = CallE (fun_id, args) $$ fun_id.at % typ in
    ExpMap.add call_exp (var_exp, iter_num) map
    ) ExpMap.empty (List.rev ids') fcalls'
  in
  call_map, new_binds, new_prems

let rec transform_iter call_map env i =
  match i with 
  | ListN (exp, id_opt) -> ListN (fst (transform_exp call_map env exp), id_opt)
  | _ -> i

and transform_typ call_map env t = 
  let it, iter_ids = (match t.it with
  | VarT (id, args) -> 
    let args', iter_ids_list = List.split (List.map (transform_arg call_map env) args) in
    VarT (id, args'), List.concat iter_ids_list
  | TupT exp_typ_pairs -> 
    let pairs, iter_ids_list = List.split (List.map (fun (e, t) -> 
      let e', iter_ids = transform_exp call_map env e in
      let t', iter_ids2 = transform_typ call_map env t in 
      (e', t'), iter_ids @ iter_ids2) exp_typ_pairs) in
    TupT pairs, List.concat iter_ids_list
  | IterT (typ, iter) -> 
    let typ', iter_ids = transform_typ call_map env typ in
    IterT (typ', transform_iter call_map env iter), iter_ids
  | typ -> typ, []
  ) in
  {t with it}, iter_ids

and transform_typ_normal call_map env t = fst (transform_typ call_map env t) 
and transform_exp call_map env e: (exp * (id * typ * int) list) = 
  let t_func = transform_exp call_map env in
  let it, iter_ids = (match e.it with
  | CaseE (m, e1) -> 
    let e1', iter_ids = t_func e1 in 
    CaseE (m, e1'), iter_ids
  | StrE fields -> 
    let fields', iter_ids = List.split (List.map (fun (a, e1) -> 
      let e1', iter_ids = t_func e1 in
      (a, e1'), iter_ids) fields) in
    StrE fields', List.concat iter_ids
  | UnE (unop, optyp, e1) -> 
    let e1', iter_ids = t_func e1 in 
    UnE (unop, optyp, e1'), iter_ids
  | BinE (binop, optyp, e1, e2) -> 
    let e1', iter_ids = t_func e1 in 
    let e2', iter_ids2 = t_func e2 in 
    BinE (binop, optyp, e1', e2'), iter_ids @ iter_ids2
  | CmpE (cmpop, optyp, e1, e2) -> 
    let e1', iter_ids = t_func e1 in 
    let e2', iter_ids2 = t_func e2 in 
    CmpE (cmpop, optyp, e1', e2'), iter_ids @ iter_ids2
  | TupE (exps) -> 
    let exps', iters_ids = List.split (List.map t_func exps) in
    TupE exps', List.concat iters_ids 
  | ProjE (e1, n) -> 
    let e1', iter_ids = t_func e1 in
    ProjE (e1', n), iter_ids
  | UncaseE (e1, m) -> 
    let e1', iter_ids = t_func e1 in
    UncaseE (e1', m), iter_ids
  | OptE (Some e1) -> 
    let e1', iter_ids = t_func e1 in
    OptE (Some e1'), iter_ids
  | TheE e1 ->
    let e1', iter_ids = t_func e1 in
    TheE e1', iter_ids
  | DotE (e1, a) -> 
    let e1', iter_ids = t_func e1 in
    DotE (e1', a), iter_ids
  | CompE (e1, e2) -> 
    let e1', iter_ids = t_func e1 in 
    let e2', iter_ids2 = t_func e2 in 
    CompE (e1', e2'), iter_ids @ iter_ids2
  | ListE exps ->
    let exps', iters_ids = List.split (List.map t_func exps) in
    ListE exps', List.concat iters_ids 
  | LiftE e1 -> 
    let e1', iter_ids = t_func e1 in
    LiftE e1', iter_ids
  | MemE (e1, e2) -> 
    let e1', iter_ids = t_func e1 in 
    let e2', iter_ids2 = t_func e2 in 
    MemE (e1', e2'), iter_ids @ iter_ids2
  | LenE e1 -> 
    let e1', iter_ids = t_func e1 in
    LenE e1', iter_ids
  | CatE (e1, e2) -> 
    let e1', iter_ids = t_func e1 in 
    let e2', iter_ids2 = t_func e2 in 
    CatE (e1', e2'), iter_ids @ iter_ids2
  | IdxE (e1, e2) -> 
    let e1', iter_ids = t_func e1 in 
    let e2', iter_ids2 = t_func e2 in 
    IdxE (e1', e2'), iter_ids @ iter_ids2
  | SliceE (e1, e2, e3) -> 
    let e1', iter_ids = t_func e1 in 
    let e2', iter_ids2 = t_func e2 in 
    let e3', iter_ids3 = t_func e3 in
    SliceE (e1', e2', e3'), iter_ids @ iter_ids2 @ iter_ids3
  | UpdE (e1, p, e2) -> 
    let e1', iter_ids = t_func e1 in  
    let p', iter_ids2 = transform_path call_map env p in
    let e2', iter_ids3 = t_func e2 in
    UpdE (e1', p', e2'), iter_ids @ iter_ids2 @ iter_ids3
  | ExtE (e1, p, e2) -> 
    let e1', iter_ids = t_func e1 in 
    let p', iter_ids2 = transform_path call_map env p in
    let e2', iter_ids3 = t_func e2 in
    ExtE (e1', p', e2'), iter_ids @ iter_ids2 @ iter_ids3
  | CallE (id, args) -> 
    let e' = {e with it = CallE (fun_prefix ^ id.it $ id.at, args)} in
    begin match (ExpMap.find_opt e' call_map) with 
    | Some (e', 0) -> e'.it, [] 
    | Some ({it = VarE id; note; _} as e', n) -> e'.it, [(id, note, n - 1)] 
    | _ -> 
      let args', iter_ids_list = List.split (List.map (transform_arg call_map env) args) in
      CallE (id, args'), List.concat iter_ids_list
    end 
  | IterE (e1, (iter, id_exp_pairs)) -> 
    let e1', iter_ids = t_func e1 in
    let free_vars = (Free.free_exp e1').varid in 
    let new_id_exp_pairs = List.map (fun (id, typ, _) -> 
      let itert = IterT (typ, transform_typ_iter iter) $ typ.at in
      (id, VarE (apply_iter_to_var id.it iter $ id.at) $$ id.at % itert)
    ) iter_ids in
    let new_iter_ids = List.filter_map (fun (id, typ, num) -> 
      if num = 0 then None else 
      let itert = IterT (typ, transform_typ_iter iter) $ typ.at in
      Some (apply_iter_to_var id.it iter $ id.at, itert, num - 1)
    ) iter_ids in
    let id_exp_pairs_filtered, more_iter_ids = List.split (List.filter_map (fun (id, iter_e) -> 
      if not (Free.Set.mem id.it free_vars) then None else
      let iter_e', iter_ids = t_func iter_e in
      Some ((id, iter_e'), iter_ids)
      ) id_exp_pairs) 
    in
    IterE (e1', (transform_iter call_map env iter, new_id_exp_pairs @ id_exp_pairs_filtered)), 
      new_iter_ids @ List.concat more_iter_ids
  | CvtE (e1, nt1, nt2) -> 
    let e1', iter_ids = t_func e1 in
    CvtE (e1', nt1, nt2), iter_ids
  | SubE (e1, t1, t2) -> 
    let e1', iter_ids = t_func e1 in
    let t1', iter_ids2 = transform_typ call_map env t1 in
    let t2', iter_ids3 = transform_typ call_map env t2 in
    SubE (e1', t1', t2'), iter_ids @ iter_ids2 @ iter_ids3
  | exp -> exp, []) in 
  {e with it}, iter_ids


and transform_path call_map env path = 
  let it, iter_ids = (match path.it with
  | RootP -> RootP, []
  | IdxP (p, e1) -> 
    let p', iter_ids = transform_path call_map env p in
    let e1', iter_ids2 = transform_exp call_map env e1 in
    IdxP (p', e1'), iter_ids @ iter_ids2
  | SliceP (p, e1, e2) -> 
    let p', iter_ids = transform_path call_map env p in
    let e1', iter_ids2 = transform_exp call_map env e1 in
    let e2', iter_ids3 = transform_exp call_map env e2 in 
    SliceP (p', e1', e2'), iter_ids @ iter_ids2 @ iter_ids3
  | DotP (p, a) -> 
    let p', iter_ids = transform_path call_map env p in
    DotP (p', a), iter_ids
  ) in
  {path with it}, iter_ids
and transform_exp_normal call_map env e = fst (transform_exp call_map env e)
and transform_sym call_map env s = 
  let it, iter_ids = (match s.it with
  | VarG (id, args) -> 
    let args', iter_ids_list = List.split (List.map (transform_arg call_map env) args) in
    VarG (id, args'), List.concat iter_ids_list
  | SeqG syms -> 
    let syms', iter_ids_list = List.split (List.map (transform_sym call_map env) syms) in
    SeqG syms', List.concat iter_ids_list
  | AltG syms -> 
    let syms', iter_ids_list = List.split (List.map (transform_sym call_map env) syms) in
    AltG syms', List.concat iter_ids_list
  | RangeG (syml, symu) -> 
    let syml', iter_ids = transform_sym call_map env syml in 
    let symu', iter_ids2 = transform_sym call_map env symu in 
    RangeG (syml', symu'), iter_ids @ iter_ids2
  | IterG (sym, (iter, id_exp_pairs)) -> 
    let sym', iter_ids = transform_sym call_map env sym in 
    IterG (sym', (transform_iter call_map env iter, 
      List.map (fun (id, exp) -> (id, fst (transform_exp call_map env exp))) id_exp_pairs)
    ), iter_ids
  | AttrG (e, sym) -> 
    let e', iter_ids = transform_exp call_map env e in 
    let sym', iter_ids2 = transform_sym call_map env sym in
    AttrG (e', sym'), iter_ids @ iter_ids2
  | sym -> sym, [] 
  ) in
  {s with it}, iter_ids

and transform_arg call_map env a: arg * (id * typ * int) list =
  let it, iter_ids = (match a.it with
  | ExpA exp -> 
    let exp', iter_ids = transform_exp call_map env exp in 
    ExpA exp', iter_ids
  | TypA typ -> 
    let typ', iter_ids = transform_typ call_map env typ in 
    TypA typ', iter_ids
  | DefA id -> DefA id, []
  | GramA sym -> 
    let sym', iter_ids = transform_sym call_map env sym in
    GramA sym', iter_ids
  ) in
  {a with it}, iter_ids

and transform_bind env b =
  (match b.it with
  | ExpB (id, typ) -> ExpB (id, transform_typ_normal ExpMap.empty env typ)
  | TypB id -> TypB id
  | DefB (id, params, typ) -> DefB (id, List.map (transform_param ExpMap.empty env) params, transform_typ_normal ExpMap.empty env typ)
  | GramB (id, params, typ) -> GramB (id, List.map (transform_param ExpMap.empty env) params, transform_typ_normal ExpMap.empty env typ)
  ) $ b.at 
  
and transform_param call_map env p =
  (match p.it with
  | ExpP (id, typ) -> ExpP (id, transform_typ_normal call_map env typ)
  | TypP id -> TypP id
  | DefP (id, params, typ) -> DefP (id, List.map (transform_param call_map env) params, transform_typ_normal call_map env typ)
  | GramP (id, typ) -> GramP (id, transform_typ_normal call_map env typ)
  ) $ p.at 

let rec transform_prem call_map env prem = 
  let it, iter_ids = match prem.it with
  | RulePr (id, m, e) -> 
    let e', iter_ids = transform_exp call_map env e in
    RulePr (id, m, e'), iter_ids
  | IfPr e -> 
    let e', iter_ids = transform_exp call_map env e in
    IfPr e', iter_ids
  | LetPr (e1, e2, ids) -> 
    (* TODO - properly handle this if it actually gets used *)
    let e1', iter_ids = transform_exp call_map env e1 in
    let e2', iter_ids2 = transform_exp call_map env e2 in
    LetPr (e1', e2', ids), iter_ids @ iter_ids2
  | ElsePr -> ElsePr, []
  | IterPr (prem1, (iter, id_exp_pairs)) -> 
    let prem1', iter_ids = transform_prem call_map env prem1 in
    let free_vars = (Free.free_prem prem1').varid in 
    let new_id_exp_pairs = List.map (fun (id, typ, _) -> 
      let itert = IterT (typ, transform_typ_iter iter) $ typ.at in
      (id, VarE (apply_iter_to_var id.it iter $ id.at) $$ id.at % itert)
    ) iter_ids in
    let new_iter_ids = List.filter_map (fun (id, typ, num) -> 
      if num = 0 then None else 
      let itert = IterT (typ, transform_typ_iter iter) $ typ.at in
      Some (apply_iter_to_var id.it iter $ id.at, itert, num - 1)
    ) iter_ids in
    let id_exp_pairs_filtered, more_iter_ids = List.split (List.filter_map (fun (id, iter_e) -> 
      if not (Free.Set.mem id.it free_vars) then None else
      let iter_e' , iter_ids = transform_exp call_map env iter_e in
      Some ((id, iter_e'), iter_ids)
      ) id_exp_pairs) in
    IterPr (prem1', (transform_iter call_map env iter, new_id_exp_pairs @ id_exp_pairs_filtered)), 
      new_iter_ids @ List.concat more_iter_ids
  | NegPr p -> 
    let p', iter_ids = transform_prem call_map env p in
    NegPr p', iter_ids
  in 
  {prem with it}, iter_ids

and transform_prem_normal call_map env prem = fst (transform_prem call_map env prem)

let transform_rule env rule = 
  (match rule.it with
  | RuleD (id, binds, m, exp, prems) -> 
    let fcalls = collect_fcalls_exp [] env exp @ List.concat_map (collect_fcalls_prem [] env) prems in
    let call_map, new_binds, new_prems = create_call_map fcalls binds in
    RuleD (id.it $ no_region, 
    List.map (transform_bind env) (binds @ new_binds), 
    m, 
    transform_exp_normal call_map env exp, 
    List.map (transform_prem_normal call_map env) (new_prems @ prems))
  ) $ rule.at

let transform_clause env clause = 
  (match clause.it with
  | DefD (binds, args, exp, prems) -> 
    let fcalls = collect_fcalls_exp [] env exp @ List.concat_map (collect_fcalls_prem [] env) prems in
    let call_map, new_binds, new_prems = create_call_map fcalls binds in
    DefD ( 
    List.map (transform_bind env) (binds @ new_binds), 
    args, 
    transform_exp_normal call_map env exp, 
    List.map (transform_prem_normal call_map env) (new_prems @ prems))
  ) $ clause.at

let transform_prod env prod = 
  match prod.it with
  | ProdD (binds, sym, exp, prems) -> 
    let fcalls = collect_fcalls_exp [] env exp @ List.concat_map (collect_fcalls_prem [] env) prems in
    let call_map, new_binds, new_prems = create_call_map fcalls binds in    
    ProdD (List.map (transform_bind env) (binds @ new_binds), 
    sym, 
    transform_exp_normal call_map env exp, 
    List.map (transform_prem_normal call_map env) (new_prems @ prems)) $ prod.at

let is_exp_param param = 
  match param.it with
  | ExpP _ -> true
  | _ -> false

let rec has_sub_exp e = 
  match e.it with
  | SubE _ -> true
  | StrE fields -> List.exists (fun (_a, e1) -> has_sub_exp e1) fields
  | UnE (_, _, e1) | CvtE (e1, _, _) | LiftE e1 | TheE e1 | OptE (Some e1) 
  | ProjE (e1, _) | UncaseE (e1, _)
  | CaseE (_, e1) | LenE e1 | DotE (e1, _) -> has_sub_exp e1
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2)
  | CompE (e1, e2) | MemE (e1, e2)
  | CatE (e1, e2) | IdxE (e1, e2) -> has_sub_exp e1 || has_sub_exp e2
  | TupE exps | ListE exps -> List.exists has_sub_exp exps
  | SliceE (e1, e2, e3) -> has_sub_exp e1 || has_sub_exp e2 || has_sub_exp e3
  | UpdE (e1, p, e2) 
  | ExtE (e1, p, e2) -> has_sub_exp e1 || has_sub_exp_path p || has_sub_exp e2
  | CallE (_id, args) -> List.exists has_sub_exp_arg args
  | IterE (e1, (_, id_exp_pairs)) -> has_sub_exp e1 || List.exists (fun (_, exp) -> has_sub_exp exp) id_exp_pairs
  | _ -> false

and has_sub_exp_arg a = 
  match a.it with
  | ExpA e -> has_sub_exp e 
  | _ -> false

and has_sub_exp_path p = 
  match p.it with
  | RootP -> false
  | IdxP (p, e) -> has_sub_exp_path p || has_sub_exp e
  | SliceP (p, e1, e2) -> has_sub_exp_path p || has_sub_exp e1 || has_sub_exp e2
  | DotP (p, _) -> has_sub_exp_path p

let rec utilizes_rel_def env e = 
  match e.it with
  | CallE (id, args) -> StringSet.mem id.it env.rel_set || List.exists (utilizes_rel_def_arg env) args
  | StrE fields -> List.exists (fun (_a, e1) -> utilizes_rel_def env e1) fields
  | UnE (_, _, e1) | CvtE (e1, _, _) | LiftE e1 | TheE e1 | OptE (Some e1) 
  | ProjE (e1, _) | UncaseE (e1, _)
  | CaseE (_, e1) | LenE e1 | DotE (e1, _)
  | SubE (e1, _, _) -> utilizes_rel_def env e1
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2)
  | CompE (e1, e2) | MemE (e1, e2)
  | CatE (e1, e2) | IdxE (e1, e2) -> utilizes_rel_def env e1 || utilizes_rel_def env e2
  | TupE exps | ListE exps -> List.exists (utilizes_rel_def env) exps
  | SliceE (e1, e2, e3) -> utilizes_rel_def env e1 || utilizes_rel_def env e2 || utilizes_rel_def env e3
  | UpdE (e1, p, e2) 
  | ExtE (e1, p, e2) -> utilizes_rel_def env e1 || utilizes_rel_def_path env p || utilizes_rel_def env e2
  | IterE (e1, (_, id_exp_pairs)) -> utilizes_rel_def env e1 || List.exists (fun (_, exp) -> utilizes_rel_def env exp) id_exp_pairs
  | _ -> false

and utilizes_rel_def_arg env a = 
  match a.it with
  | ExpA e -> utilizes_rel_def env e 
  | _ -> false

and utilizes_rel_def_path env p = 
  match p.it with
  | RootP -> false
  | IdxP (p, e) -> utilizes_rel_def_path env p || utilizes_rel_def env e
  | SliceP (p, e1, e2) -> utilizes_rel_def_path env p || utilizes_rel_def env e1 || utilizes_rel_def env e2
  | DotP (p, _) -> utilizes_rel_def_path env p

let collect_list_length_vars () : StringSet.t ref * (module Iter.Arg) =
  let module Arg = 
    struct
      include Iter.Skip 
      let acc = ref StringSet.empty
      let visit_exp exp =
        match exp.it with
        | IterE (_, (ListN ({it = VarE id; _}, _), [_])) ->
          acc := StringSet.add id.it !acc
        | _ -> ()
    end
  in Arg.acc, (module Arg)

let must_be_relation env id params clauses = 
  let listn_set, (module Arg : Iter.Arg) = collect_list_length_vars () in
  assert (!listn_set = StringSet.empty);
  let module Acc = Iter.Make(Arg) in
  (* Current limitation of relations - can only have standard types. 
     No type parameters or higher order functions *)
  List.for_all is_exp_param params && 
  (* Limitation - functions used as def ids cannot be relations *)
  not (StringSet.mem id.it env.def_arg_set) && 
  List.exists (fun c -> match c.it with 
  | DefD (binds, args, exp, prems) -> 
    Acc.args args;
    (* Can't have subtyping matching *)
    List.exists has_sub_exp_arg args || 
    (* Premises might not be decidable *)
    prems <> [] || 
    (* Functions that have function calls transformed to relations must also be relations *)
    utilizes_rel_def env exp ||
    (* Checking if equality binding is active *)
    fst (List.fold_left (fun (acc_bool, free_set) arg -> 
      let free_vars = Free.free_arg arg in
      (acc_bool || Free.inter free_vars free_set <> Free.empty, Free.union free_vars free_set)
    ) (false, Free.empty) args) ||
    (* There are more binded variables than utilized in the arguments *)
    let bounded_vars = Free.free_list Free.bound_bind binds in
    let free_vars = Free.free_list Free.free_arg args in
    Free.diff bounded_vars free_vars <> Free.empty || 
    (* HACK - dealing with list of a specified length with relations instead of functions *)
    !listn_set <> StringSet.empty
  ) clauses


let cvt_def_to_rel env id params r_typ clauses = 
  let get_param_typ p = 
    match p.it with
    | ExpP (_, t) -> t
    | _ -> assert false
  in
  let types = List.map get_param_typ params @ [r_typ] in 
  let tupt = TupT (List.map (fun t -> (VarE ("_" $ id.at) $$ id.at % t), t) types) $ id.at in
  let new_mixop = [] :: List.init (List.length params + 1) (fun _ -> []) in
  let rules = List.mapi (fun i clause -> 
    match clause.it with
    | DefD (binds, args, exp, prems) -> 
      let exps = List.map get_exp_arg args in
      let fcalls = collect_fcalls_exp [] env exp @ List.concat_map (collect_fcalls_prem [] env) prems in
      let call_map, new_binds, new_prems = create_call_map fcalls binds in
      let tupe = TupE (exps @ [transform_exp_normal call_map env exp]) $$ id.at % tupt in
      RuleD (fun_prefix ^ id.it ^ "_case_" ^ Int.to_string i $ id.at, binds @ new_binds, new_mixop, tupe, List.map (transform_prem_normal call_map env) (new_prems @ prems)) $ id.at
    ) clauses 
  in
  RelD (fun_prefix ^ id.it $ id.at, new_mixop, tupt, rules)

let rec transform_def (env : env) def = 
  let must_be_rel_def d =
    match d.it with
    | DecD (id, params, _, clauses) -> must_be_relation env id params clauses
    | _ -> false
  in
  let has_exp_params d =
    match d.it with
    | DecD (_, params, _, _) -> List.for_all is_exp_param params
    | _ -> false
  in
  (match def.it with
  | RelD (id, m, typ, rules) -> 
    RelD (id, m, typ, List.map (transform_rule env) rules)
  | DecD (id, params, typ, clauses) when must_be_relation env id params clauses -> 
    env.rel_set <- StringSet.add id.it env.rel_set;
    cvt_def_to_rel env id params typ clauses
  | DecD (id, params, typ, clauses) -> 
    DecD (id, params, typ, List.map (transform_clause env) clauses)
  | RecD defs when List.exists must_be_rel_def defs && List.for_all has_exp_params defs -> 
    List.iter (fun d -> match d.it with
    | DecD (id, _, _, _) -> env.rel_set <- StringSet.add id.it env.rel_set
    | _ -> () 
    ) defs;
    RecD (List.map (transform_def env) defs)
  | RecD defs -> RecD (List.map (transform_def env) defs)
  | GramD (id, params, typ, prods) -> GramD (id, params, typ, List.map (transform_prod env) prods)
  | d -> d
  ) $ def.at

let collect_def_args (): StringSet.t ref * (module Iter.Arg) =
  let module Arg = 
    struct
      include Iter.Skip 
      let acc = ref StringSet.empty
      let visit_arg arg =
        match arg.it with
        | DefA id -> acc := StringSet.add id.it !acc
        | _ -> ()
    end
  in Arg.acc, (module Arg)

let transform (il : script): script =
  let env = empty_env in 
  env.env <- Il.Env.env_of_script il;
  let acc, (module Arg : Iter.Arg) = collect_def_args () in
  let module Acc = Iter.Make(Arg) in
  List.iter Acc.def il;
  env.def_arg_set <- !acc;
  List.map (transform_def env) il
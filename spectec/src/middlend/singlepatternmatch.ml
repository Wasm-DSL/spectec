(*

In this pass we remove pattern-matchings from two variables.

Imagine two datatypes A = Aone | Atwo | … | Aonehundred and B = Bone | Btwo | … | Bonehundred 

We would replace the following function:

f : A -> B -> C 
f Aone Bone = Cwhatever
f Atwo Btwo = Csomething

(which in proof assistants like Isabelle would explode in size as isabelle adds cases like f Aone Btwo = undefined etc for all ten thousand combinations) with three functions

fAone : B -> C
f Bone = Cwhatever

fAtwo : B -> C
f Btwo = Csomething

f : A -> B -> C
f Aone x = fAone x
f Atwo x = fAtwo x

Here, Isabelle would add 99 cases to fAone, 99 cases to fAtwo and 98 cases to f, instead of the 9998 cases it would otherwise have added to the old f

Known issue: this can introduce redunt pattern-matching cases!

 *)

let limit = 100 (* max number of cases we can tolerate *)

open Il.Ast
open Util.Source
open Xl.Mixop

let error at msg = Util.Error.error at "Single-patternmatch pass" msg

module MixopMap = Map.Make(struct type t = unit mixop let compare = compare end) 
module StringMap = Map.Make(String)
type datatypes = (typ list * typ) MixopMap.t StringMap.t (* map from type names to maps from constructor names to arg types *)

(* Helpers: recursivity: *)


let rec is_recursive_exp id e =
  match e.it with
  | VarE id' -> List.mem id'.it id
  | BoolE _ 
    | NumE _
    | TextE _
    | OptE None -> false
  | UnE (_, _, e)
    | ProjE (e, _)
    | CaseE (_, e)
    | UncaseE (e, _)
    | OptE (Some e)
    | TheE e
    | DotE (e, _)
    | LiftE e
    | LenE e
    | CvtE (e, _, _) -> is_recursive_exp id e
  | BinE (_, _, e1, e2)
    | CmpE (_, _, e1, e2)
    | CompE (e1, e2)
    | MemE (e1, e2)
    | CatE (e1, e2)
    | IdxE (e1, e2) -> is_recursive_exp id e1 || is_recursive_exp id e2
  | SliceE (e1, e2, e3)
    | IfE (e1, e2, e3) -> is_recursive_exp id e1 || is_recursive_exp id e2 || is_recursive_exp id e3
  | TupE es
    | ListE es -> List.exists (is_recursive_exp id) es
  | StrE es -> List.exists (is_recursive_exp id) (List.map snd es)
  | UpdE (e1, p, e2)
    | ExtE (e1, p, e2) -> is_recursive_exp id e1 || is_recursive_exp id e2 || is_recursive_path id p
  | CallE (id', args) -> List.mem id'.it id || List.exists (is_recursive_arg id) args
  | IterE (e, ite) -> is_recursive_exp id e || is_recursive_iterexp id ite
  | SubE (e, t1, t2) -> is_recursive_exp id e || is_recursive_typ id t1 || is_recursive_typ id t2

and is_recursive_typ id typ =
  match typ.it with
  | VarT (_, args) -> List.exists (is_recursive_arg id) args
  | BoolT | NumT _ | TextT -> false
  | TupT ts -> List.exists (is_recursive_typ id) (List.map snd ts)
  | IterT (t, i) -> is_recursive_typ id t || is_recursive_iter id i

and is_recursive_iter id = function
  | ListN (e, _) -> is_recursive_exp id e
  | _ -> false

and is_recursive_arg id arg =
  match arg.it with
  | ExpA e -> is_recursive_exp id e
  | TypA t -> is_recursive_typ id t
  | DefA _ -> false
  | GramA s -> is_recursive_sym id s

and is_recursive_sym id sym =
  match sym.it with
  | VarG (_, args) -> List.exists (is_recursive_arg id) args
  | NumG _
    | TextG _
    | EpsG -> false
  | SeqG syms 
    | AltG syms -> List.exists (is_recursive_sym id) syms
  | RangeG (sym1, sym2) -> is_recursive_sym id sym1 || is_recursive_sym id sym2
  | IterG (s, ite) -> is_recursive_sym id s || is_recursive_iterexp id ite
  | AttrG (e, s) -> is_recursive_exp id e || is_recursive_sym id s

and is_recursive_iterexp id = function
  | (it, es) -> is_recursive_iter id it || List.exists (is_recursive_exp id) (List.map snd es)

and is_recursive_path id path =
  match path.it with
  | RootP -> false
  | IdxP (p, e) -> is_recursive_path id p || is_recursive_exp id e
  | SliceP (p, e1, e2) -> is_recursive_path id p || is_recursive_exp id e1 || is_recursive_exp id e2
  | DotP (p, _) -> is_recursive_path id p
    

let is_recursive_clause id clause =
  match clause.it with
  | DefD (_, _, e, _) -> is_recursive_exp id e

let rec is_recursive id def =
  match def.it with
  | DecD (_, _, _, clauses) ->
     List.exists (is_recursive_clause id) clauses
  | RecD defs -> List.exists (is_recursive id) defs
  | _ -> error def.at "generated defs should only be decs and recs"

(* helpers: substitution *)

let rec subst_exp x v e =
  let f x = { e with it = x } in
  let g = subst_exp x v in
  match e.it with
  | VarE y when y.it = x -> v
  | VarE _ 
    | BoolE _
    | NumE _
    | TextE _
    | OptE None -> e
  | UnE (a, b, e) -> f (UnE (a, b, g e))
  | BinE (a, b, e1, e2) -> f (BinE (a, b, g e1, g e2))
  | CmpE (a, b, e1, e2) -> f (CmpE (a, b, g e1, g e2))
  | TupE es -> f (TupE (List.map g es))
  | ProjE (e, i) -> f (ProjE (g e, i))
  | CaseE (a, e) -> f (CaseE (a, g e))
  | UncaseE (e, a) -> f (UncaseE (g e, a))
  | OptE (Some e) -> f (OptE (Some (g e)))
  | TheE e -> f (TheE (g e))
  | StrE es -> f (StrE (List.map (fun (a, e) -> (a, g e)) es))
  | DotE (e, a) -> f (DotE (g e, a))
  | CompE (e1, e2) -> f (CompE (g e1, g e2))
  | ListE es -> f (ListE (List.map g es))
  | LiftE e -> f (LiftE (g e))
  | MemE (e1, e2) -> f (MemE (g e1, g e2))
  | LenE e -> f (LenE (g e))
  | CatE (e1, e2) -> f (CatE (g e1, g e2))
  | IdxE (e1, e2) -> f (IdxE (g e1, g e2)) 
  | SliceE (e1, e2, e3) -> f (SliceE (g e1, g e2, g e3)) 
  | UpdE (e1, p, e2) -> f (UpdE (g e1, subst_path x v p, g e2))
  | ExtE (e1, p, e2) -> f (ExtE (g e1, subst_path x v p, g e2))
  | IfE (e1, e2, e3) -> f (IfE (g e1, g e2, g e3))
  | CallE (id, args) -> f (CallE (id, List.map (subst_arg x v) args))
  | IterE (e, ite) -> f (IterE (g e, subst_iterexp x v ite))
  | CvtE (e, a, b) -> f (CvtE (g e, a, b))
  | SubE (e, t1, t2) -> f (SubE (g e, subst_typ x v t1, subst_typ x v t2))

and subst_typ x v t =
  match t.it with
  | VarT (id, args) -> { t with it = VarT (id, List.map (subst_arg x v) args) }
  | BoolT
    | NumT _
    | TextT -> t
  | TupT l -> { t with it = TupT (List.map (fun (a, t) -> (a, subst_typ x v t)) l) }
  | IterT (t, i) -> { t with it = IterT (subst_typ x v t, subst_iter x v i) }

and subst_iter x v = function
  | Opt -> Opt
  | List -> List
  | List1 -> List1
  | ListN (e, i) -> ListN (subst_exp x v e, i)

and subst_iterexp x v (i, l) = (subst_iter x v i, List.map (fun (i, e) -> (i, subst_exp x v e)) l)

and subst_arg x v a =
  match a.it with
  | ExpA e -> { a with it = ExpA (subst_exp x v e) }
  | TypA t -> { a with it = TypA (subst_typ x v t) }
  | DefA _ -> a
  | GramA s -> { a with it = GramA (subst_sym x v s) }

and subst_sym x v s =
  match s.it with
  | VarG (i, args) -> { s with it = VarG (i, List.map (subst_arg x v) args) }
  | NumG _
    | TextG _
    | EpsG -> s     
  | SeqG syms -> { s with it = SeqG (List.map (subst_sym x v) syms) }
  | AltG syms -> { s with it = AltG (List.map (subst_sym x v) syms) }
  | RangeG (s1, s2) -> { s with it = RangeG (subst_sym x v s1, subst_sym x v s2) }
  | IterG (sym, ite) -> { s with it = IterG (subst_sym x v sym, subst_iterexp x v ite) }
  | AttrG (e, sym) -> { s with it = AttrG (subst_exp x v e, subst_sym x v sym) }

and subst_path x v p =
  match p.it with
  | RootP -> p              
  | IdxP (path, e) -> { p with it = IdxP (subst_path x v path, subst_exp x v e) }
  | SliceP (path, e1, e2) -> { p with it = SliceP (subst_path x v path, subst_exp x v e1, subst_exp x v e2) }
  | DotP (path, a) -> { p with it = DotP (subst_path x v path, a) }



(* other helpers *)

let is_typ_param x =
  match x.it with
  | TypP _ -> true
  | _ -> false
let is_typ_arg x =
  match x.it with
  | TypA _ -> true
  | _ -> false
let has_prems c = 
  let only_otherwise prems =
    match prems with
    | [{it = ElsePr; _}] -> true
    | _ -> false
  in
  match c.it with
  | DefD (_, _, _, prems) -> prems <> [] && not (only_otherwise prems)

let transform_case_tup e = 
  match e.it with
  | TupE exps -> exps
  | _ -> [e]

let transform_case_typ t =
  match t.it with
  | TupT typs -> List.map snd typs
  | _ -> [t]

let package_case_tup l at typ =
  match l with
  | [e] -> e
  | _ -> TupE l $$ (at, typ)

let rec get_arg_types = function
  | (op, (t, _, _), _) :: q ->
     MixopMap.add ((* to_string *) op) (transform_case_typ t, t) (get_arg_types q)
  | [] -> MixopMap.empty

let rec get_constr_strings exp =
  match exp.it with
  | CaseE (op, arg) ->
     let args = transform_case_tup arg in
     let suffs = List.map get_constr_strings args |> List.flatten in
     [(* to_string *) op] :: List.map (fun suff -> (* to_string *) op :: suff) suffs
  | _ -> []

let inspect_clause_constr_strings clause =
  match clause.it with
  | DefD (_, args, _, _) ->
     List.map (fun arg ->
         match arg.it with
         | ExpA exp -> get_constr_strings exp
         | _ -> []) args 

let rec count_cases (datatypes : datatypes) typ constructor_strings =
  (* may overcount if datatypes share constructor names but that is fine *)
  match typ.it with
  | VarT (typid, _) ->
     if StringMap.mem typid.it datatypes then
       let cases = StringMap.find typid.it datatypes in
       if constructor_strings = [] then 1
       else
         MixopMap.fold (fun casename (argtypes, _) total ->
             let constructor_strings = List.filter_map (function
                                           | t :: t' :: q when t = casename -> Some (t' :: q)
                                           | _ -> None) constructor_strings in
             if constructor_strings = [] then total + 1 else
               total + (List.map (fun typ -> count_cases datatypes typ constructor_strings)
                          argtypes |> List.fold_left ( * ) 1)) cases 0 
     else 1
  | _ -> 1

let inspect_clause_depth dummy_arglist clauses =
  List.fold_left (fun acc clause ->
      match clause.it with
      | DefD (_, args, _, _) ->
         List.map2 (fun (n, seen_catchall) arg ->
             if seen_catchall then (n, true) else
               match arg.it with
               | ExpA { it = CaseE _ ; _ } -> (n + 1, false)
               | _ -> (n, true)) acc args) (List.map (fun _ -> (0, false)) dummy_arglist) clauses |> List.map fst

let rec find_deepest = function
  | [] -> 0, 0
  | n :: q -> let i, v = find_deepest q in
              if n >= v then 0, n
              else i + 1, v

let rec get_nth i = function
  | [] -> failwith "list too short"
  | t :: q -> if i = 0 then t else get_nth (i - 1) q

let rec replace_nth i l = function
  | [] -> failwith "list too short"
  | t :: q -> if i = 0 then l @ q else t :: replace_nth (i - 1) l q

(* let insert_clause op clause newclauses =
  let l = if MixopMap.mem op newclauses then MixopMap.find op newclauses else [] in
  MixopMap.add op (clause :: l) newclauses *)

(* let rec separate_clauses newclauses casei clauses =
  match clauses with
  | clause :: q ->
     begin match clause.it with
     | DefD (quants, args, exp, prems) ->
        let argi = get_nth casei args in
        match argi.it with
        | ExpA expi ->
           begin match expi.it with
           | CaseE (op, e) ->
              let es = transform_case_tup e in
              let es = List.map (fun e -> {argi with it = ExpA e}) es in
              let newargs = replace_nth casei es args in
              let newclause = { clause with it = DefD (quants, newargs, exp, prems) } in
              separate_clauses (insert_clause op newclause newclauses) casei q
           | _ -> newclauses, clauses
           end
        | _ -> failwith "this argument should be an expression"
     end
  | _ -> newclauses, [] *)

let generate_dummy_exps typs at =
  List.mapi (fun i t ->
                 VarE ("constructor_parameter_" ^ string_of_int i $ at) $$ (at, t)) typs 

let rec generate_args params : arg list =
  List.map (fun param ->
      let at = param.at in
      match param.it with 
      | ExpP (id, t) -> (ExpA (VarE id $$ (at, t)) $ at) 
      | TypP id -> (TypA (VarT (id, []) $ at) $ at) 
      | DefP (id,_,_) -> (DefA id $ at)
      | GramP (id, params, _) -> (GramA (VarG (id, generate_args params) $ at) $ at) 
    ) params 

let generate_dummy_args l at =
  List.map (fun e -> ExpA e $ at) (generate_dummy_exps l at)
let generate_dummy_params l at =
  let es = generate_dummy_exps l at in
  List.map (fun e ->
      match e.it with
      | VarE id -> ExpP (id, e.note) $ e.at
      | _ -> error e.at "dummy exps are always vars") es
        

let generate_split_clauses clauses casei op paramtyps packagedparamtyps =
  List.filter_map (fun clause ->
      match clause.it with
      | DefD (quants, args, exp, prems) ->
         let argi = get_nth casei args in
         match argi.it with
         | ExpA e ->
            begin match e.it with 
            | VarE x ->
               Some (DefD (generate_dummy_params paramtyps clause.at @ quants,
                           replace_nth casei (generate_dummy_args paramtyps clause.at) args,
                           subst_exp x.it ((CaseE (op, package_case_tup (generate_dummy_exps paramtyps clause.at) e.at packagedparamtyps) $$ (e.at, e.note))) exp,
                           prems) $ clause.at)
            | CaseE (op', e) when to_string op = to_string op' ->
               let es = transform_case_tup e in
               let es = List.map (fun e -> {argi with it = ExpA e}) es in
               let newargs = replace_nth casei es args in
               Some { clause with it = DefD (quants, newargs, exp, prems) }
            | CaseE _  ->
               None
            | _ -> error e.at "this pattern-matching case should be a constructor or a variable"
            end
         | _ -> error argi.at "this pattern-matching case should be on expression arguments"
    ) clauses

let get_rec_names defs =
  List.filter_map (fun def ->
      match def.it with
      | DecD (id, _, _, _) -> Some id.it
      | _ -> None) defs

let is_catchall cl =
  match cl.it with
  | DefD (_, args, _, _) ->
     List.for_all (fun arg ->
         match arg.it with
         | ExpA e ->
            begin match e.it with
            | VarE _ -> true
            | _ -> false end
         | _ -> true) args

let rec stop_at_first_catchall = function
  | [] -> []
  | cl :: _ when is_catchall cl -> [cl]
  | t :: q -> t :: stop_at_first_catchall q

let rec transform_def (datatypes : datatypes) rec_names def =
  match def.it with
  | TypD (id, _, [{it = InstD (_, _, {it = VariantT typcases; _}); _}]) -> 
     StringMap.add id.it (get_arg_types typcases) datatypes, [def]
  | DecD (_, params, _, [{it = DefD (quants, args, _, _); _}])
       when List.for_all is_typ_param params && List.for_all is_typ_arg args && List.for_all is_typ_param quants -> 
     datatypes, [def]
   | DecD (_, _, _, []) ->
      datatypes, [def]
   | DecD (_, _, _, clauses) when List.exists has_prems clauses ->
      datatypes, [def]
   | DecD (id, params, typ, clauses) ->
      let constructor_strings =
        List.fold_left (fun constructor_strings clause ->
            List.map2 (@) (inspect_clause_constr_strings clause) constructor_strings) (List.map (fun _ -> []) params) clauses in
      let estimate_of_size = List.map2 (fun paramtyp constructor_strings ->
                                 match paramtyp.it with
                                 | ExpP (_, paramtyp) ->
                                    count_cases datatypes paramtyp constructor_strings
                                 | _ -> 1) params constructor_strings
                             |> List.fold_left ( * ) 1 in
      (*      Printf.printf "function %s has size %d\n" id.it estimate_of_size; *)
     if estimate_of_size <= limit then datatypes, [def] else
      let pattern_match_depths = inspect_clause_depth params clauses in
      let casei, depth = find_deepest pattern_match_depths in
      if depth = 0 then
        datatypes, [{ def with it = DecD (id, params, typ, [List.hd clauses])}]
      else
        (*        let case_clauses, catchall_clauses = separate_clauses MixopMap.empty casei clauses in *)
        let splittypid = get_nth casei params in
        let splittypid, splittyp = match splittypid.it with
          | ExpP (_, ({it = VarT (id, _) ; _} as t)) -> id.it, t
          | _ -> error splittypid.at "chosen case should be a datatype" in
        let splittypparams = StringMap.find splittypid datatypes in
        let new_defs, toplevelclauses =
          MixopMap.fold (fun op (paramtyps, packaged_paramtyps) (new_defs, toplevelclauses) ->
              let split_clauses = generate_split_clauses clauses casei op paramtyps packaged_paramtyps in
              let split_clauses = stop_at_first_catchall split_clauses in
              match split_clauses with
              | [] -> new_defs, toplevelclauses
              | _ -> (DecD ({ id with it = id.it ^ "_" ^ to_string op },
                            replace_nth casei
                              (List.mapi (fun i t -> ExpP (to_string op ^ "_argument_" ^ string_of_int i $ id.at, t) $ id.at) paramtyps) params,
                            typ,
                            split_clauses) $ def.at) :: new_defs,
                     (DefD (replace_nth casei (generate_dummy_params paramtyps id.at) params,
                            replace_nth casei
                              [ExpA
                                 (CaseE
                                    (op,
                                     package_case_tup (
                                         generate_dummy_exps paramtyps id.at) id.at packaged_paramtyps) $$ (id.at, splittyp)) $ id.at]
                              (generate_args params),
                            CallE ({id with it = id.it ^ "_" ^ to_string op},
                                   replace_nth casei
                                     (generate_dummy_args paramtyps id.at)
                                     (generate_args params)) $$ (id.at, typ),
                            []) $ id.at) :: toplevelclauses
            ) splittypparams ([], []) in
        let new_defs = List.map (fun def -> snd (transform_def datatypes rec_names def)) new_defs |> List.flatten in
        let topleveldef =
          DecD (id, params, typ, toplevelclauses) $ def.at in
        let yes_rec, not_rec = List.partition (is_recursive (if rec_names = [] then [id.it] else rec_names)) new_defs in
        begin match yes_rec with
        | [] -> datatypes, new_defs @ [topleveldef]
        | _ -> datatypes, not_rec @ [RecD (yes_rec @ [topleveldef]) $ def.at]
        end
   | RecD defs ->
      let rec_names = rec_names @ get_rec_names defs in
      let datatypes, defs = List.fold_left (fun (datatypes, defs) def ->
                                let datatypes, def = transform_def datatypes rec_names def in
                                datatypes, def :: defs) (datatypes, []) defs in
      datatypes, [{ def with it = RecD (List.flatten (List.rev defs)) }]
   | _  -> datatypes, [def]

let transform script =
  let _, script = List.fold_left (fun (datatypes, defs) def ->
                      let datatypes, def = transform_def datatypes [] def in
                      datatypes, def :: defs) (StringMap.empty, []) script in
  List.flatten (List.rev script)

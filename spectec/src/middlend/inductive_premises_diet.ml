(*

  This breaks down inductives where a rule has too many premises. E.g. if the rule goes

  premise1 ==>
  premise2 ==>
  ...
  premise50 ==>
  conclusion

  We replace with new definitions
  premise1 ==>
  ...
  premise8 ==>
  partial_conclusion1

  premise9 ==>
  ...
  premise16 ==>
  partial_conclusion2

  etc
  and
  partial_conclusion1 ==>
  partial_conclusion2 ==>
  ...
  partial_conclusion8 ==>
  conclusion


SKIPS RECURSIVE DEFINITIONS AND ANYTHING WITH LET PREMISES
  
 *)



let max_premises = 50

open Il.Ast
open Util.Source
open Xl.Mixop  

let sqrt n = int_of_float (Float.sqrt (float_of_int n))

let rec make_packets i packet_size = function
  | [] -> []
  | l when i = packet_size -> [] :: make_packets 0 packet_size l
  | t :: q -> match make_packets (i + 1) packet_size q with
              | pack :: packs -> (t :: pack) :: packs
              | [] -> [[t]]

let partial_name rule_id i =
  rule_id.it ^ "_partial_" ^ string_of_int i $
    rule_id.at

let rec smart_merge l1 l2 =
  match l1, l2 with
  | [], _ -> l2
  | _, [] -> l1
  | (i1, t1) :: q1, (i2, t2) :: q2 ->
     if i1 < i2 then (i1, t1) :: smart_merge q1 l2
     else if i1 = i2 then (i1, t1) :: smart_merge q1 q2
     else (i2, t2) :: smart_merge l1 q2

let rec remove to_remove = function
  | [] -> []
  | (id, t) :: q -> if List.mem id.it to_remove then remove to_remove q
                    else (id, t) :: remove to_remove q

let rec fvars_arg (arg : arg) =
  match arg.it with
  | ExpA e -> fvars_exp e
  | TypA t -> fvars_typ t
  | DefA _ -> []
  | GramA s -> fvars_sym s

and fvars_sym sym =
  match sym.it with
  | VarG (_, args) -> List.flatten (List.map fvars_arg args)
  | NumG _
  | TextG _
  | EpsG -> []        
  | SeqG syms 
  | AltG syms -> List.flatten (List.map fvars_sym syms)
  | RangeG (s1, s2) -> smart_merge (fvars_sym s1) (fvars_sym s2)
  | IterG (s, (iter, ps)) ->
     let to_remove = List.map (fun (x, _) -> x.it) ps in
     let to_remove = match iter with | ListN (_, Some i) -> i.it :: to_remove | _ -> to_remove in
     fvars_sym s |> remove to_remove
  | AttrG (e, s) -> smart_merge (fvars_exp e) (fvars_sym s)

and fvars_typ t =
  match t.it with
  | VarT (_, args) -> List.flatten (List.map fvars_arg args)
  | BoolT 
  | NumT _
  | TextT -> []
  | TupT ts -> List.flatten (List.map (fun (_, t) -> fvars_typ t) ts)
  | IterT (t, _) -> fvars_typ t

and fvars_exp exp =
  match exp.it with
  | VarE i -> [ i, exp.note ]
  | BoolE _
    | NumE _
    | OptE None
    | TextE _ -> []
  | ProjE (e, _)
    | CvtE (e,_,_)
    | CaseE (_, e)
    | OptE (Some e)
    | TheE e
    | UncaseE (e,_)
    | LiftE e
    | DotE (e,_)
    | LenE e
    | UnE (_,_,e) -> fvars_exp e
  | BinE (_,_,e1,e2)
    | CompE (e1, e2)
    | MemE (e1, e2)
    | IdxE (e1, e2)
    | CatE (e1, e2)
    | CmpE (_,_,e1,e2) -> smart_merge (fvars_exp e1) (fvars_exp e2)
  | ListE es
    | TupE es -> List.flatten (List.map fvars_exp es)
  | StrE es -> List.flatten (List.map (fun (_,e) -> fvars_exp e) es)
  | IfE (e1, e2, e3)
    | SliceE (e1, e2, e3) -> smart_merge (smart_merge (fvars_exp e1) (fvars_exp e2)) (fvars_exp e3)
  | ExtE (e1, p, e2) 
    | UpdE (e1, p, e2) -> smart_merge (smart_merge (fvars_exp e1) (fvars_path p)) (fvars_exp e2)
  | CallE (_, args) -> List.flatten (List.map fvars_arg args)
  | IterE (e, (iter, ps)) ->
     let to_remove = List.map (fun (x, _) -> x.it) ps in
     let to_remove = match iter with | ListN (_, Some i) -> i.it :: to_remove | _ -> to_remove in
     fvars_exp e |> remove to_remove
  | SubE (e, t1, t2) -> smart_merge (smart_merge (fvars_exp e) (fvars_typ t1)) (fvars_typ t2)

and fvars_path path =
  match path.it with
  | RootP -> []
  | IdxP (p,e) -> smart_merge (fvars_path p) (fvars_exp e)
  | SliceP (p, e1, e2) -> smart_merge (smart_merge (fvars_path p) (fvars_exp e1)) (fvars_exp e2)
  | DotP (p, _) -> fvars_path p






let rec fvars_prem prem =
  match prem.it with
  | RulePr (_, args, _, exp) -> smart_merge (List.flatten (List.map fvars_arg args)) (fvars_exp exp)
  | IfPr exp -> fvars_exp exp 
  | LetPr (_,_,_) -> failwith "let premise found" 
  | ElsePr -> []
  | IterPr (p, (iter, ps)) ->
     let to_remove = List.map (fun (x, _) -> x.it) ps in
     let to_remove = match iter with | ListN (_, Some i) -> i.it :: to_remove | _ -> to_remove in
     fvars_prem p |> remove to_remove
  | NegPr p -> fvars_prem p
 


(* TODO: find all free vars in the premises and add them as args so that a free var present in different packets must agree with one another *)
(* TODO: add a declaration or something? To clear validation *)

let expand_tuple_type typ newtyps =
  if newtyps = [] then typ else
  match typ.it with
  | TupT fsttyps -> TupT (fsttyps @ newtyps) $ typ.at
  | _ -> TupT (("inductive_unique_param" $ no_region, typ) :: newtyps) $ typ.at
let expand_tuple_exp exp newexps newtype =
  if newexps = [] then exp else
  match exp.it with
  | TupE fstexps -> TupE (fstexps @ newexps) $$ (exp.at, newtype)
  | _ -> TupE (exp :: newexps) $$ (exp.at, newtype)

let flatten_tuple_exp exp =
  match exp.it with
  | TupE exps -> exps
  | _ -> [exp]

let is_let prem =
  match prem.it with
  | LetPr _ -> true
  | _ -> false

let transform_rule a b typ rule =
  match rule.it with
  | RuleD (rule_id, quants, mixop, exp, prems) ->
     let nb_prems = List.length prems in
     if nb_prems <= max_premises || List.exists is_let prems then rule, [] (* leave rule untouched, no new declarations *)
     else let nb_prems_per_partial = min max_premises (sqrt nb_prems) in
          let prems_packeted = make_packets 0 nb_prems_per_partial prems in
          let fvars = List.flatten (List.map fvars_prem prems) in
          let to_remove = List.map (fun (i, _) -> i.it) (fvars_exp exp) in
          let fvars = remove to_remove fvars in
          let newmixop = match mixop with
            | Seq l -> Seq (l @ List.map (fun _ -> Arg ()) fvars)
            | _ -> failwith "should be a seq mixop" in
          let newb = match b with
            | Seq l -> Seq (l @ List.map (fun _ -> Arg ()) fvars)
            | _ -> failwith "should be a seq mixop" in
          let newexps = List.map (fun (x,t) ->
                            VarE x $$ (rule_id.at, t)
                         ) fvars in
          let newtype = expand_tuple_type typ fvars in
          let newdecls = List.mapi (fun i prems ->
                             RelD (partial_name rule_id i, a, newb,
                                   newtype,
                                   [RuleD (rule_id.it ^ "_partial_premise" $ rule_id.at, quants, newmixop,
                                           expand_tuple_exp exp newexps newtype, prems)
                               $ rule.at])
                             $ rule_id.at)
                           prems_packeted in
          let newprems = List.mapi (fun i _ -> RulePr (
                                                   partial_name rule_id i,
                                                   [],
                                                   newb,
                                                   expand_tuple_exp exp newexps newtype
                                                 )
                                                   $ rule.at) prems_packeted in
          RuleD (rule_id, quants, mixop, exp, newprems) $ rule.at , newdecls

let rec collectr = function
  | [] -> [], []
  | (a, b) :: q -> let aas, bbs = collectr q in
                   a :: aas, b @ bbs

let transform_decl decl =
  match decl.it with
  | RelD (id, a, b, typ, rules) ->
     let new_rules, new_decls = collectr (List.map (transform_rule a b typ) rules) in
     new_decls @ [RelD (id, a, b, typ, new_rules) $ decl.at ]
  | _ -> [decl]

let transform script =
  List.flatten (List.map transform_decl script)
       

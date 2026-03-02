(*
This transformation totalizes partial functions.

Partial functions are recognized by the partial flag hint (for now, inference
would be possible).

The declarations are changed:

 * the return type is wrapped in the option type `?`
 * all clauses rhs' are wrapped in the option type injection `?(…)`
 * a catch-all clause is added returning `null`

All calls to such functions are wrapped in option projection `THE e`.

*)

open Util
open Source
open Il.Ast
open Il.Walk
open Il

(* Errors *)

let _error at msg = Error.error at "totality" msg

(* Environment *)

module S = Set.Make(String)

type env =
  { mutable partial_funs : S.t;
  }

let new_env () : env =
  { partial_funs = S.empty;
  }

let is_partial (env : env) (id : id) = S.mem id.it env.partial_funs

let register_partial (env : env) (id :id) =
  env.partial_funs <- S.add id.it env.partial_funs

(* Transformation *)

(* The main transformation case *)
let t_exp env exp =
  match exp.it with
  | CallE (f, _) when is_partial env f ->
    {exp with it = TheE {exp with note = IterT (exp.note, Opt) $ exp.at}}
  | _ -> exp

let f_exp env subst exp =
  match exp.it with
  | TheE ({ it = CallE (f, _); _} as exp') when is_partial env f ->
    let id = (Fresh.fresh_varid "iter_val") $ exp'.at  in 
    subst := (id, exp') :: !subst;
    { exp' with it = VarE id }
  | _ -> exp

let fix_partial_funcs env exp = 
  match exp.it with
    (* If there is a call in the root of the RHS then just return that *)
  | TheE ({ it = CallE (f, _); _} as exp') when is_partial env f ->
    exp'
  | _ ->
    (* Apply transformation to wrap an option iteration on the rhs *)
    let eps_ref = ref [] in 
    let t = { base_transformer with transform_exp = f_exp env eps_ref } in
    let t_e = transform_exp t exp in 
    if !eps_ref = [] then 
      { exp with it = OptE (Some exp); note = IterT (exp.note, Opt) $ exp.at } 
    else 
      { exp with it = IterE (t_e, (Opt, !eps_ref)); note = IterT (exp.note, Opt) $ exp.at }  

let has_catch_all clauses = 
  List.exists (fun clause ->
    let DefD (_, args, _, _) = clause.it in
    List.for_all (fun a -> 
      match a.it with
      | ExpA {it = VarE _; _} -> true
      | TypA _ | DefA _ -> true
      | _ -> false 
    ) args
  ) clauses

let rec t_def env d = 
  let t = { base_transformer with transform_exp = t_exp env } in
  match d.it with
  | RecD defs -> RecD (List.map (t_def env) defs) $ d.at
  | DecD (id, params, typ, clauses) ->
    let params' = List.map (transform_param t) params in
    let typ' = transform_typ t typ in
    let clauses' = List.map (transform_clause t) clauses in
    if is_partial env id then
      let typ'' = IterT (typ', Opt) $ no_region in
      let clauses'' = List.map (fun clause -> match clause.it with
        DefD (quants, lhs, rhs, prems) ->
          { clause with
            it = DefD (List.map (transform_param t) quants, lhs, fix_partial_funcs env rhs, prems) }
        ) clauses' in
      let params, args = List.mapi (fun i param -> match param.it with
        | ExpP (_, typI) ->
          let x = ("x" ^ string_of_int i) $ no_region in
          [ExpP (x, typI) $ x.at], ExpA (VarE x $$ no_region % typI) $ no_region
        | TypP id -> [TypP id $ no_region], TypA (VarT (id, []) $ no_region) $ no_region
        | DefP (id, _, _) -> [], DefA id $ no_region
        | GramP (id, _, _) -> [], GramA (VarG (id, []) $ no_region) $ no_region
        ) params' |> List.split in
      let catch_all = DefD (List.concat params, args,
        OptE None $$ no_region % typ'', [ElsePr $ no_region]) $ no_region in
      let last_c = if has_catch_all clauses'' then [] else [catch_all] in
      DecD (id, params', typ'', clauses'' @ last_c) $ d.at
    else
      DecD (id, params', typ', clauses') $ d.at
  | _ -> transform_def t d

let is_partial_hint hint = hint.hintid.it = "partial"

let register_hints env def =
  match def.it with
  | HintD {it = DecH (id, hints); _} when List.exists is_partial_hint hints ->
    register_partial env id
  | _ -> ()

let transform (defs : script) =
  let env = new_env () in
  List.iter (register_hints env) defs;
  List.map (t_def env) defs

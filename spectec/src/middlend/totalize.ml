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

(* Errors *)

let _error at msg = Source.error at "totalize" msg

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
let totalize_exp env e =
  match e.it with
  | CallE (f, _) when is_partial env f ->
    {e with it = TheE {e with note = IterT (e.note, Opt) $ e.at}}
  | _ -> e

let totalize_def env d =
  match d.it with
  | DecD (id, typ1, typ2, clauses) when is_partial env id ->
      let typ2' = IterT (typ2, Opt) $ no_region in
      let clauses' = List.map (fun clause -> match clause.it with
        DefD (binds, lhs, rhs, prems) ->
          { clause with
            it = DefD (binds, lhs, OptE (Some rhs) $$ no_region % typ2', prems) }
        ) clauses in
      let x = "x" $ no_region in
      let catch_all = DefD ([(x, typ1, [])], VarE x $$ no_region % typ1,
        OptE None $$ no_region % typ2', []) $ no_region in
      {d with it = DecD (id, typ1, typ2', clauses' @ [ catch_all ])}
  | _ -> d

let is_partial_hint hint = hint.hintid.it = "partial"

let register_hints env def =
  match def.it with
  | HintD {it = DecH (id, hints); _} when List.exists is_partial_hint hints ->
    register_partial env id
  | _ -> ()

let transform (defs : script) =
  let env = new_env () in
  List.iter (register_hints env) defs;
  Traverse.reader ~exp:totalize_exp ~def:totalize_def env defs

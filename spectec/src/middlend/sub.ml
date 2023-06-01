(*
This transformation replaces SubE expressions with explicit subtype injection
functions.

 1. It traverses all expressions and finds out which type pairs
    occur in SubE expressions
    - all type pairs mentioned in SubE expressions
    - for all variant types: list of constructors
    - for all alias types: right hand side of the alias

 2. It traverses all definitions to collect information about variant types and
    type aliases (assuming only such types occur in type aliases).

 3. It generates explicit injection functions for pairs, and put them in the
 right spot (after both types are defined, but outside `RecD` groups)

 4. It replaces occurrences of SubE with a suitable CallE

Step 1 and 4 are done together, and step 2 and 3

This pass assumes that there is no name shadowing in the type definitions.

*)

open Util
open Source
open Il.Ast

(* Errors *)

let error at msg = Source.error at "subtype elimination" msg

(* Environment *)

module M = Map.Make(String)
module S = Set.Make(struct
  type t = id * id
  let compare (t1, t2) (t3, t4) = compare (t1.it, t2.it) (t3.it, t4.it)
end)

(*
The environment consist of:
  * Which constructors the type has (and their non-aliased concrete type)
  * Which SubE type pairs have been observed, but not yet generated
*)
type env =
  { mutable typ : (id * typcase list) M.t;
    mutable pairs : S.t
  }

let new_env () : env =
  { typ = M.empty;
    pairs = S.empty;
  }

let lookup (env : env) (id : id) : id * typcase list =
  match M.find_opt id.it env.typ with
  | None -> error id.at ("unknown type `" ^ id.it ^ "`")
  | Some t -> t

let register_variant (env : env) (id : id) (cases : typcase list) =
  if M.mem id.it env.typ then
    error id.at ("duplicate declaration for type `" ^ id.it ^ "`")
  else
    env.typ <- M.add id.it (id, cases) env.typ

let register_alias (env : env) (id : id) (id2 : id) =
  match M.find_opt id2.it env.typ with
  | Some type_info ->
    env.typ <- M.add id.it type_info env.typ
  | None -> () (* Not an alias of a variant type *)

let injection_name (sub : id) (sup : id) = sup.it ^ "_" ^ sub.it $ no_region

let var_of_typ typ = match typ.it with
  | VarT id -> id
  | _ -> error typ.at ("Non-variable type expression not supported:\n" ^ Il.Print.string_of_typ typ)

(* Step 1 and 4: Collect SubE occurrences, and replace with function *)

(* The main transformation case *)
let transform_exp env exp =
  match exp.it with
  | SubE (e, sub_ty, sup_ty) ->
    let sub = var_of_typ sub_ty in
    let sup = var_of_typ sup_ty in
    env.pairs <- S.add (sub, sup) env.pairs;
    { exp with it = CallE (injection_name sub sup, e)}
  | _ -> exp

(* Step 2 and 3: Traverse definitions, collect type information, insert as soon as possible *)

let rec add_type_info env (def : def) = match def.it with
  | RecD defs -> List.iter (add_type_info env) defs
  | SynD (id, deftyp) ->
    begin match deftyp.it with
    | VariantT cases -> register_variant env id cases
    | AliasT {it = VarT id2; _} -> register_alias env id id2
    | _ -> ()
    end
  | _ ->()

let is_ready env (t1, t2) = M.mem t1.it env.typ && M.mem t2.it env.typ

(* Returns type pairs that are defined now, and removes them from the env *)
let ready_pairs (env : env) =
  let (ready, todo) = S.partition (is_ready env) env.pairs in
  env.pairs <- todo;
  S.elements ready


let insert_injections env (def : def) : def list =
  add_type_info env def;
  let pairs = ready_pairs env in
  [ def ] @
  List.map (fun (sub, sup) ->
    let name = injection_name sub sup in
    let sub_ty = VarT sub $ no_region in
    let sup_ty = VarT sup $ no_region in
    let (real_id, cases) = lookup env sub in
    let clauses = List.map (fun (a, arg_typ, _hints) ->
      match arg_typ.it with
      | TupT ts ->
        let binds = List.mapi (fun i arg_typ_i -> ("x" ^ string_of_int i $ no_region, arg_typ_i, [])) ts in
        let xes = List.map (fun (x, arg_typ_i, _) -> VarE x $$ no_region % arg_typ_i) binds in
        let xe = TupE xes $$ no_region % arg_typ in
        DefD (binds,
          CaseE (a, xe) $$ no_region % (VarT real_id $ no_region),
          CaseE (a, xe) $$ no_region % sup_ty, []) $ no_region
      | _ ->
        let x = "x" $ no_region in
        let xe = VarE x $$ no_region % arg_typ in
        DefD ([(x, arg_typ, [])],
          CaseE (a, xe) $$ no_region % (VarT real_id $ no_region),
          CaseE (a, xe) $$ no_region % sup_ty, []) $ no_region
      ) cases in
    DecD (name, sub_ty, sup_ty, clauses) $ no_region
  ) pairs


let transform (defs : script) =
  let env = new_env () in
  let defs' = Traverse.reader ~exp:transform_exp env defs in
  let defs'' = List.concat_map (insert_injections env) defs' in
  S.iter (fun (sub, sup) -> error sub.at ("left-over subtype coercion " ^ sub.it ^ " <: " ^ sup.it)) env.pairs;
  defs''


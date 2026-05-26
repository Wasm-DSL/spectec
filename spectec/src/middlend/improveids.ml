open Il.Ast
open Il
open Il.Walk
open Util.Source
(* open Util *)
open Xl.Atom
open Xl

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

type env = {
  mutable atom_str_set : StringSet.t;
  il_env : Il.Env.t;
}

let make_prefix = "mk_"
let var_prefix = "v_"
let fun_prefix = "fun_"
let res_prefix = "r_"

type id_type = 
  | Var         (* Variables *)
  | Userdef     (* Types and relations *)
  | Funcdef     (* function definitions *)
  | Atoms       (* Type constructors *)

let empty_info typ_id: region * Xl.Atom.info = (no_region, {def = typ_id; case = ""})

(* Id transformation *)
let transform_id' (env : env) (id_type : id_type) (s : text) = 
  let change_id s' = 
    String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | '#' -> '_'
     | c -> c
    ) s'
    (* This suffixes any '*' with '_lst' and '?' with '_opt' for clarity *)
    |> Str.global_replace (Str.regexp {|\(*\)|}) "_lst"
    |> Util.Lib.String.replace "?" "_opt"
  in
  let s' = change_id s in
  match id_type with
  (* Leave naming hole as is *)
  | _ when s' = "_" -> s' 
  | Var when Il.Env.mem_typ env.il_env (s' $ no_region) 
    || Il.Env.mem_rel env.il_env (s' $ no_region) 
    || Il.Env.mem_def env.il_env (s' $ no_region) 
    || StringSet.mem s' env.atom_str_set -> (var_prefix ^ s')
  | Funcdef when Il.Env.mem_typ env.il_env (s' $ no_region) 
    || Il.Env.mem_rel env.il_env (s' $ no_region) 
    || StringSet.mem s' env.atom_str_set -> (fun_prefix ^ s')
  | Userdef when StringSet.mem s' env.atom_str_set -> (res_prefix ^ s')
  (* Checking whether an id is an int - if so, put a reserved prefix *)
  | _ when Option.is_some (int_of_string_opt s') -> (res_prefix ^ s')
  | _ -> s'

let t_var_id env id = transform_id' env Var id.it $ id.at
let t_def_id env id = transform_id' env Funcdef id.it $ id.at
let t_user_def_id env id = transform_id' env Userdef id.it $ id.at
let t_atom_id env id = transform_id' env Atoms id.it $ id.at
let transform_rule_id env rule_id rel_id = 
  match rule_id.it with
  | "" -> make_prefix ^ rel_id.it
  | _ -> transform_id' env Atoms rule_id.it

let is_atomid a = 
  match a.it with
  | Atom _ -> true
  | _ -> false

let has_atom_hole m =
  match m with
  | [{it = Atom "_"; _}] -> true
  | _ -> false

let register_atom_id env s =
  env.atom_str_set <- StringSet.add s env.atom_str_set

(* Atom functions *)
let transform_atom env typ_id a = 
  match a.it with
  | Atom s -> 
    register_atom_id env (t_atom_id env (s $ a.at)).it;
    Atom (t_atom_id env (s $ a.at)).it $$ a.at % a.note
  | _ -> 
    register_atom_id env (make_prefix ^ typ_id);
    Atom (make_prefix ^ typ_id) $$ a.at % a.note

(* Atom transformation where there might be other atom constructs, leave them be *)
let transform_atom' env a = 
  match a.it with
  | Atom s -> 
    register_atom_id env (t_atom_id env (s $ a.at)).it;
    Atom (t_atom_id env (s $ a.at)).it $$ a.at % a.note
  | _ -> a

let transform_mixop env typ_id (m : mixop) =
  let m' = List.map (fun inner_m -> List.filter is_atomid inner_m) (Mixop.flatten m) in
  let len = List.length m' in 
  match m' with
  | _ when List.for_all (fun l -> l = [] || has_atom_hole l) m' -> 
    register_atom_id env (make_prefix ^ typ_id);
    let atom = Xl.Mixop.Atom (Atom (make_prefix ^ typ_id) $$ empty_info typ_id) in
    Xl.Mixop.(Seq (atom :: List.init (len - 1) (fun _ -> Arg ())))
  | _ -> Xl.Mixop.map_atoms (transform_atom' env) m


let rec check_iteration_naming e iterexp = 
  match e.it, iterexp with
  | VarE id, (_, [(id', _)]) -> Eq.eq_id id id'
  | IterE (e, ((_, [(_, {it = VarE id; _})]) as i)), (_, [(id', _)]) -> 
    Eq.eq_id id id' && check_iteration_naming e i
  | _ -> false 

and t_exp env e = 
  (match e.it with
  | CaseE (m, e1) -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env e.note) in
    CaseE(transform_mixop env id m, e1)
  | StrE fields -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env e.note) in
    StrE (List.map (fun (a, e1) -> (transform_atom env id a, e1)) fields)
  | UncaseE (e1, m) -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env e.note) in
    UncaseE (e1, transform_mixop env id m)
  | DotE (e1, a) -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env e1.note) in
    DotE (e1, transform_atom env id a)
  (* Special case for iteration naming - just use the variable it is iterating on *)
  | IterE (e, ((_, [(_, {it = VarE id''; _})]) as iterexp)) when check_iteration_naming e iterexp -> 
    VarE (t_var_id env id'')
  | exp -> exp
  ) $$ e.at % e.note

and t_path env path = 
  (match path.it with
  | DotP (p, a) -> 
    let id = Print.string_of_typ_name (Eval.reduce_typ env.il_env p.note) in
    DotP (p, transform_atom env id a)
  | p -> p
  ) $$ path.at % path.note

let t_inst tf env id inst = 
  (match inst.it with
  | InstD (quants, args, deftyp) -> InstD (List.map (transform_param tf) quants, List.map (transform_arg tf) args, 
    (match deftyp.it with 
    | AliasT typ -> AliasT (transform_typ tf typ)
    | StructT typfields -> StructT (List.map (fun (a, (typ, c_quants, prems), hints) ->
        (transform_atom env id.it a, 
        (transform_typ tf typ, List.map (transform_param tf) c_quants, List.map (transform_prem tf) prems), hints)  
      ) typfields)
    | VariantT typcases -> 
      VariantT (List.map (fun (m, (typ, c_quants, prems), hints) -> 
        (transform_mixop env id.it m, 
        (transform_typ tf typ, List.map (transform_param tf) c_quants, List.map (transform_prem tf) prems), hints)  
      ) typcases)
    ) $ deftyp.at
  )
  ) $ inst.at

let transform_rule tf env rel_id rule = 
  (match rule.it with
  | RuleD (id, quants, m, exp, prems) -> 
    RuleD (transform_rule_id env id rel_id $ id.at, 
    List.map (transform_param tf) quants, 
    m, 
    transform_exp tf exp, 
    List.map (transform_prem tf) prems
  )
  ) $ rule.at

let is_wf_hint hintid = hintid.it = Undep.wf_hint_id
let transform_el_exp env hintid e = 
  (match e.it with
  | El.Ast.VarE (id, args) when is_wf_hint hintid -> El.Ast.VarE (t_user_def_id env id, args)
  | e' -> e'
  ) $ e.at

let transform_hintdef env hintdef = 
  let t_hint h = 
    { h with hintexp = transform_el_exp env h.hintid h.hintexp} 
  in
  let t_hints hs = List.map t_hint hs in
  let h = match hintdef.it with
  | TypH (id, hints) -> TypH (t_user_def_id env id, t_hints hints)
  | RelH (id, hints) -> RelH (t_user_def_id env id, t_hints hints)
  | DecH (id, hints) -> DecH (t_user_def_id env id, t_hints hints)
  | GramH (id, hints) -> GramH (t_user_def_id env id, t_hints hints)
  | RuleH (id, rid, hints) -> 
    RuleH (t_user_def_id env id, transform_rule_id env rid id $ rid.at, t_hints hints)
  in
  { hintdef with it = h }

let rec t_def env def = 
  let tf = { base_transformer with 
    transform_exp = t_exp env;
    transform_path = t_path env;
    transform_var_id = t_var_id env;
    transform_typ_id = t_user_def_id env;
    transform_rel_id = t_user_def_id env;
    transform_def_id = t_def_id env;
  } in
  (match def.it with
  | TypD (id, params, insts) -> 
    TypD (t_user_def_id env id, 
    List.map (transform_param tf) params |> Utils.improve_ids_params, 
    List.map (t_inst tf env id) insts)
  | RelD (id, params, m, typ, rules) -> 
    RelD (t_user_def_id env id,
    List.map (transform_param tf) params |> Utils.improve_ids_params,
    m, transform_typ tf typ,
    List.map (transform_rule tf env id) rules)
  | DecD (id, params, typ, clauses) -> 
    DecD (t_def_id env id, 
    List.map (transform_param tf) params |> Utils.improve_ids_params, 
    transform_typ tf typ, 
    List.map (transform_clause tf) clauses)
  | GramD (id, params, typ, prods) -> 
    GramD (id, 
    List.map (transform_param tf) params |> Utils.improve_ids_params, 
    transform_typ tf typ, 
    List.map (transform_prod tf) prods)
  | RecD defs -> RecD (List.map (t_def env) defs)
  | HintD hintdef -> HintD (transform_hintdef env hintdef)
  ) $ def.at

let create_env il = {
  atom_str_set = StringSet.empty;
  il_env = Env.env_of_script il
}

let transform (il : script): script =
  let env = create_env il in 
  List.map (t_def env) il
open Il.Ast
open Util.Source
open Il.Walk
open Il
open Xl

module StringMap = Map.Make(String)

type env = {
  mutable disamb_map: (string * string) list StringMap.t;
  mutable il_env: Il.Env.t
}

let new_env () = {
  disamb_map = StringMap.empty;
  il_env = Il.Env.empty
}

let empty_info: region * Xl.Atom.info = (no_region, {def = ""; case = ""})

let env_ref: env ref = ref (new_env ())

let _print_env () =
  List.iter (fun (typ_id, ss) ->
    print_endline "Entry: ";
    print_endline ("Type id: " ^ typ_id);
    print_endline (String.concat " " (List.map (fun (base_id, _) -> base_id) ss))
  ) (StringMap.bindings !env_ref.disamb_map)

let error at msg = Util.Error.error at "Rocq Generation" msg

let (let*) = Option.bind

let register_id typ_id base_id id = 
  !env_ref.disamb_map <- StringMap.update typ_id (fun opt -> 
    match opt with
    | Some ss -> Some ((base_id, id) :: ss)
    | None -> Some [(base_id, id)]
  ) !env_ref.disamb_map

let is_atomid a =
  match a.it with
  | Atom.Atom _ -> true
  | _ -> false

let get_atom_id a = 
  match a.it with
  | Atom.Atom s -> s
  | _ -> ""

let get_mixop_s m = 
  String.concat "" (List.map (
      fun atoms -> String.concat "" (List.filter is_atomid atoms |> List.map get_atom_id)) m
  ) 

let t_atom_opt typ_id a =
  match a.it with
  | Atom.Atom s ->
    let* ss = StringMap.find_opt typ_id !env_ref.disamb_map in 
    let* _, s' = List.find_opt (fun (base_s, _) -> s = base_s) ss in
    Some {a with it = Atom.Atom s'}
  | _ -> Some a 

let t_atom typ_id a =
  match (t_atom_opt typ_id a) with
  | Some a -> a
  | _ -> assert false
  (* | None -> error a.at "Could not find modified atom id" *)

let t_mixop typ_id m = 
  match m with
  | [a] :: tail when List.for_all ((=) []) tail -> [t_atom typ_id a] :: tail 
  | _ ->
    let s = get_mixop_s m in
    let new_atom = Atom.Atom s $$ empty_info in
    [[t_atom typ_id new_atom]]
  (* List.map (fun atoms -> List.map (t_atom typ_id) atoms) m *)

let t_exp e = 
  match e.it with
  | CaseE (m, e') ->
    let name = Il.Print.string_of_typ_name (Il.Eval.reduce_typ !env_ref.il_env e.note) in
    {e with it = CaseE (t_mixop name m, e')}
  | StrE fields -> 
    let name = Il.Print.string_of_typ_name (Il.Eval.reduce_typ !env_ref.il_env e.note) in
    let fields' = List.map (fun (a, e') -> (t_atom name a, e')) fields in
    {e with it = StrE fields'}
  | DotE (e', a) ->
    let name = Il.Print.string_of_typ_name (Il.Eval.reduce_typ !env_ref.il_env e'.note) in
    {e with it = DotE (e', t_atom name a)}
  | _ -> e

let t_path p = 
  match p.it with
  | DotP (p', a) ->
    let name = Il.Print.string_of_typ_name (Il.Eval.reduce_typ !env_ref.il_env p'.note) in
    {p with it = DotP (p', t_atom name a)}
  | _ -> p

let rec t_rule_new rel_id base_r_id r_id = 
  let new_id = rel_id ^ "__" ^ r_id in
  let lst = StringMap.bindings !env_ref.disamb_map in 
  begin match (List.find_opt (fun (_, ss) -> List.exists (fun (_, s') -> r_id = s') ss) lst) with
  | Some _ -> t_rule_new rel_id base_r_id new_id
  | None when 
    Il.Env.mem_typ !env_ref.il_env (r_id $ no_region) || 
    Il.Env.mem_def !env_ref.il_env (r_id $ no_region) -> 
    t_rule_new rel_id base_r_id new_id
  | None ->  
    register_id rel_id base_r_id r_id;
    r_id
  end

let rec t_atom_new typ_id base_a a =
  match base_a.it, a.it with
  | Atom.Atom base_s, Atom.Atom s -> 
    let lst = StringMap.bindings !env_ref.disamb_map in 
    begin match (List.find_opt (fun (_, ss) -> List.exists (fun (_, s') -> s = s') ss) lst) with
    | Some _ -> 
      t_atom_new typ_id base_a {a with it = Xl.Atom.Atom (typ_id ^ "_" ^ s)}
    | None when 
      Il.Env.mem_typ !env_ref.il_env (s $ no_region) ||
      Il.Env.mem_def !env_ref.il_env (s $ no_region)  ->
      t_atom_new typ_id base_a {a with it = Xl.Atom.Atom (typ_id ^ "_" ^ s)}
    | None ->  
      register_id typ_id base_s s;
      {a with it = Atom.Atom s}
    end
  | _-> a

let t_mixop_new typ_id m = 
  match m with
  | [a] :: tail when List.for_all ((=) []) tail -> [t_atom_new typ_id a a] :: tail 
  | _ -> 
    let s = get_mixop_s m in 
    let new_atom = Atom.Atom s $$ empty_info in
    [[t_atom_new typ_id new_atom new_atom]]


  (* List.map (fun atoms -> List.map (fun a -> t_atom_new typ_id a a) atoms) m *)
    
let t_inst t typ_id inst = 
  let InstD (binds, args, deftyp) = inst.it in
  let deftyp' = match deftyp.it with
  | VariantT typcases -> VariantT (List.map (fun (m, (binds', typ, prems), h) -> 
    (t_mixop_new typ_id m, 
    (List.map (transform_bind t) binds', transform_typ t typ, List.map (transform_prem t) prems), 
    h)
  ) typcases)
  | StructT typfields -> StructT (List.map (fun (a, (binds', typ, prems), h) -> 
    (t_atom_new typ_id a a, (List.map (transform_bind t) binds', transform_typ t typ, List.map (transform_prem t) prems), h)
  ) typfields)
  | AliasT typ -> AliasT (transform_typ t typ) in
  { inst with it = InstD (List.map (transform_bind t) binds, List.map (transform_arg t) args, {deftyp with it = deftyp'})} 

let rec t_def def = 
  let t = { base_transformer with transform_path = t_path; transform_exp = t_exp } in
  match def.it with
  | TypD (typ_id, params, insts) -> 
    { def with it = TypD (typ_id, List.map (transform_param t) params, List.map (t_inst t typ_id.it) insts) }
  | RecD defs -> { def with it = RecD (List.map t_def defs) }
  | RelD (id, m, typ, rules) -> 
    { def with it = RelD (id, m, typ, 
    List.map (fun rule ->
      let RuleD (r_id, binds, m, exp, prems) = rule.it in
      { rule with it = RuleD ((t_rule_new id.it r_id.it r_id.it) $ r_id.at, 
      List.map (transform_bind t) binds, m, transform_exp t exp, List.map (transform_prem t) prems) }
    ) rules) }
  | _ -> transform_def t def

(* Remove overlaps created by sub expansion *)
let remove_overlapping_clauses clauses = 
  Util.Lib.List.nub (fun clause clause' -> match clause.it, clause'.it with
  | DefD (_, args, exp, _), DefD (_, args', exp', _) -> 
    let reduced_exp = Eval.reduce_exp !env_ref.il_env exp in 
    let reduced_exp' = Eval.reduce_exp !env_ref.il_env exp' in 
    Eq.eq_list Eq.eq_arg args args' && Eq.eq_exp reduced_exp reduced_exp'
  ) clauses

let rec rem_overlap_def def = 
  match def.it with
  | DecD (id, params, typ, clauses) -> {def with it = DecD (id, params, typ, remove_overlapping_clauses clauses)}
  | RecD defs -> {def with it = RecD (List.map rem_overlap_def defs)}
  | _ -> def  

let transform il =
  !env_ref.il_env <- Il.Env.env_of_script il;
  List.map rem_overlap_def il |>
  List.map t_def
open Util.Source
open Ast


(* Data Structure *)

module Map = Map.Make(String)

type subst = {varid : exp Map.t; typid : typ Map.t}
type t = subst

let empty = {varid = Map.empty; typid = Map.empty}

let mem_varid s id = Map.mem id.it s.varid
let mem_typid s id = Map.mem id.it s.typid

let add_varid s id e = if id.it = "_" then s else {s with varid = Map.add id.it e s.varid}
let add_typid s id t = if id.it = "_" then s else {s with typid = Map.add id.it t s.typid}

let union s1 s2 =
  { varid = Map.union (fun _ _e1 e2 -> Some e2) s1.varid s2.varid;
    typid = Map.union (fun _ _t1 t2 -> Some t2) s1.typid s2.typid;
  }

let remove_varid' s id' = {s with varid = Map.remove id' s.varid}
let remove_varids s ids' =
  Free.Set.(fold (fun id' s -> remove_varid' s id') ids' s)


(* Helpers *)

let subst_opt subst_x s xo = Option.map (subst_x s) xo
let subst_list subst_x s xs = List.map (subst_x s) xs

let rec subst_list_dep subst_x bound_x s = function
  | [] -> []
  | x::xs ->
    subst_x s x :: subst_list_dep subst_x bound_x (remove_varids s (bound_x x).Free.varid) xs


(* Identifiers *)

let subst_varid s id =
  match Map.find_opt id.it s.varid with
  | None -> id
  | Some {it = VarE id'; _} -> id'
  | Some _ -> raise (Invalid_argument "subst_varid")


(* Iterations *)

let rec subst_iter s iter =
  match iter with
  | Opt | List | List1 -> iter
  | ListN (e, id_opt) -> ListN (subst_exp s e, subst_opt subst_varid s id_opt)


(* Types *)

and subst_typ s t =
  (*
  Printf.eprintf "[il.subst_typ] %s\n%!" (Print.string_of_typ t);
  *)
  (match t.it with
  | VarT (id, args) ->
    (match Map.find_opt id.it s.typid with
    | None -> VarT (id, List.map (subst_arg s) args)
    | Some t' -> assert (args = []); t'.it  (* We do not support higher-order substitutions yet *)
    )
  | BoolT | NumT _ | TextT -> t.it
  | TupT xts -> TupT (subst_list_dep subst_typbind Free.bound_typbind s xts)
  | IterT (t1, iter) -> IterT (subst_typ s t1, subst_iter s iter)
  ) $ t.at

and subst_typbind s (id, t) =
  (id, subst_typ s t)

and subst_deftyp s dt =
  (match dt.it with
  | AliasT t -> AliasT (subst_typ s t)
  | NotationT (op, t) -> NotationT (op, subst_typ s t)
  | StructT tfs -> StructT (subst_list subst_typfield s tfs)
  | VariantT tcs -> VariantT (subst_list subst_typcase s tcs)
  ) $ dt.at

and subst_typfield s (atom, (binds, t, prems), hints) =
  (atom, (binds, subst_typ s t, subst_list subst_prem s prems), hints)
and subst_typcase s (atom, (binds, t, prems), hints) =
  (atom, (binds, subst_typ s t, subst_list subst_prem s prems), hints)


(* Expressions *)

and subst_exp s e =
  (match e.it with
  | VarE id ->
    (match Map.find_opt id.it s.varid with
    | None -> VarE id
    | Some e' -> e'.it
    )
  | BoolE _ | NatE _ | TextE _ -> e.it
  | UnE (op, e1) -> UnE (op, subst_exp s e1)
  | BinE (op, e1, e2) -> BinE (op, subst_exp s e1, subst_exp s e2)
  | CmpE (op, e1, e2) -> CmpE (op, subst_exp s e1, subst_exp s e2)
  | IdxE (e1, e2) -> IdxE (subst_exp s e1, subst_exp s e2)
  | SliceE (e1, e2, e3) -> SliceE (subst_exp s e1, subst_exp s e2, subst_exp s e3)
  | UpdE (e1, p, e2) -> UpdE (subst_exp s e1, subst_path s p, subst_exp s e2)
  | ExtE (e1, p, e2) -> ExtE (subst_exp s e1, subst_path s p, subst_exp s e2)
  | StrE efs -> StrE (subst_list subst_expfield s efs)
  | DotE (e1, atom) -> DotE (subst_exp s e1, atom)
  | CompE (e1, e2) -> CompE (subst_exp s e1, subst_exp s e2)
  | LenE e1 -> LenE (subst_exp s e1)
  | TupE es -> TupE (subst_list subst_exp s es)
  | MixE (op, e1) -> MixE (op, subst_exp s e1)
  | CallE (id, args) -> CallE (id, subst_list subst_arg s args)
  | IterE (e1, iterexp) -> IterE (subst_exp s e1, subst_iterexp s iterexp)
  | ProjE (e1, i) -> ProjE (subst_exp s e1, i)
  | OptE eo -> OptE (subst_opt subst_exp s eo)
  | TheE e -> TheE (subst_exp s e)
  | ListE es -> ListE (subst_list subst_exp s es)
  | CatE (e1, e2) -> CatE (subst_exp s e1, subst_exp s e2)
  | CaseE (a, e1) -> CaseE (a, subst_exp s e1)
  | SubE (e1, t1, t2) -> SubE (subst_exp s e1, subst_typ s t1, subst_typ s t2)
  ) $$ e.at % subst_typ s e.note

and subst_expfield s (atom, e) = (atom, subst_exp s e)

and subst_path s p =
  (match p.it with
  | RootP -> RootP
  | IdxP (p1, e) -> IdxP (subst_path s p1, subst_exp s e)
  | SliceP (p1, e1, e2) ->
    SliceP (subst_path s p1, subst_exp s e1, subst_exp s e2)
  | DotP (p1, atom) -> DotP (subst_path s p1, atom)
  ) $$ p.at % subst_typ s p.note

and subst_iterexp s (iter, ids) =
  (* TODO: This is assuming expressions in s are closed. *)
  (subst_iter s iter, List.filter (fun id -> not (mem_varid s id)) ids)


(* Premises *)

and subst_prem s prem =
  (match prem.it with
  | RulePr (id, op, e) -> RulePr (id, op, subst_exp s e)
  | IfPr e -> IfPr (subst_exp s e)
  | ElsePr -> ElsePr
  | IterPr (prem1, iterexp) -> IterPr (subst_prem s prem1, subst_iterexp s iterexp)
  | LetPr (e1, e2, ids) -> LetPr (subst_exp s e1, subst_exp s e2, ids)
  ) $ prem.at


(* Definitions *)

and subst_arg s a =
  (match a.it with
  | ExpA e -> ExpA (subst_exp s e)
  | TypA t -> TypA (subst_typ s t)
  ) $ a.at

and subst_param s p =
  (match p.it with
  | ExpP (id, t) -> ExpP (id, subst_typ s t)
  | TypP id -> TypP id
  ) $ p.at


(* Optimizations *)

let subst_typ s t = if s = empty then t else subst_typ s t
let subst_deftyp s dt = if s = empty then dt else subst_deftyp s dt
let subst_exp s e = if s = empty then e else subst_exp s e
let subst_prem s pr = if s = empty then pr else subst_prem s pr
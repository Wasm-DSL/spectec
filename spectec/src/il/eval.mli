open Ast

type env = Env.t
type subst = Subst.t

val (let*) : subst option -> (subst -> subst option) -> subst option

val reduce_exp : env -> exp -> exp
val reduce_typ : env -> typ -> typ
val reduce_typdef : env -> typ -> deftyp
val reduce_arg : env -> arg -> arg

val equiv_functyp : env -> param list * typ -> param list * typ -> bool
val equiv_typ : env -> typ -> typ -> bool
val sub_typ : env -> typ -> typ -> bool

exception Irred (* indicates that argument is not normalised enough to decide *)

(* When set (default), a clause or instance whose match is undecidable is
   treated as a non-match; when unset, exhausting all clauses is an error. *)
val assume_coherent_matches : bool ref

(* When set, a clause or instance whose match is undecidable leaves the
   application stuck instead of being skipped. Skipping assumes clauses do not
   overlap, which fails for pipelines that keep overlapping catch-all clauses
   (e.g. after totalize on dependent IL). *)
val allow_stuck_applications : bool ref

val match_iter : env -> subst -> iter -> iter -> subst option (* raises Irred *)
val match_exp : env -> subst -> exp -> exp -> subst option (* raises Irred *)
val match_typ : env -> subst -> typ -> typ -> subst option (* raises Irred *)
val match_arg : env -> subst -> arg -> arg -> subst option (* raises Irred *)

val match_list :
  (env -> subst -> 'a -> 'a -> subst option) ->
  env -> subst -> 'a list -> 'a list -> subst option

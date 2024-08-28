open Ast

type env = Env.t
type subst = Subst.t

val is_normal_exp : exp -> bool
val is_head_normal_exp : exp -> bool

val (let*) : subst option -> (subst -> subst option) -> subst option

val reduce_exp : env -> exp -> exp
val reduce_typ : env -> typ -> typ
val reduce_typdef : env -> typ -> deftyp
val reduce_arg : env -> arg -> arg
val reduce_prems : env -> prem list -> bool option

val equiv_functyp : env -> param list * typ -> param list * typ -> bool
val equiv_typ : env -> typ -> typ -> bool
val sub_typ : env -> typ -> typ -> bool

exception Irred (* indicates that argument is not normalised enough to decide *)

val match_iter : env -> subst -> iter -> iter -> subst option (* raises Irred *)
val match_exp : env -> subst -> exp -> exp -> subst option (* raises Irred *)
val match_typ : env -> subst -> typ -> typ -> subst option (* raises Irred *)
val match_arg : env -> subst -> arg -> arg -> subst option (* raises Irred *)

val match_list :
  (env -> subst -> 'a -> 'a -> subst option) ->
  env -> subst -> 'a list -> 'a list -> subst option

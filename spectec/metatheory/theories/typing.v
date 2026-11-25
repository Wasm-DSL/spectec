From Stdlib Require Import List String.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax env subst utils semantics.
Import ListNotations.
Open Scope env_scope.

(* Typing of declarations and scripts (doc/semantics/il/6-typing.spectec).
   The typing of types, expressions, premises, etc. is in semantics.v. *)

(* As for clauses, the conclusion may use what the premises bind *)
Inductive ok_rule : il_env -> il_rule -> il_typ -> Prop :=
  | okr_rule : forall env qs e prs t env',
    ok_params env qs ->
    ok_prems (env @@ paramenv qs) prs env' ->
    ok_exp (env @@ paramenv qs @@ env') e t ->
    ok_rule env (qs, e, prs) t
.

Inductive ok_prod : il_env -> il_prod -> il_typ -> Prop :=
  | okpd_rule : forall env qs g e prs t t' env',
    ok_params env qs ->
    ok_sym (env @@ paramenv qs) g t' ->
    ok_prems (env @@ paramenv qs) prs env' ->
    ok_exp (env @@ paramenv qs @@ env') e t ->
    ok_prod env (qs, g, e, prs) t
.

(* E |- dec : OK -| E'   where E' holds only the new bindings *)
Inductive ok_def : il_env -> il_def -> il_env -> Prop :=
  | okdf_typ : forall env x ps insts,
    ok_params env ps ->
    List.Forall (fun inst => ok_inst env inst ps) insts ->
    ok_def env (TypD x ps insts) (single_envtyp x ps insts)
  | okdf_rel : forall env x ps t rules,
    ok_params env ps ->
    List.Forall (fun rule => ok_rule (env @@ paramenv ps) rule t) rules ->
    ok_def env (RelD x ps t rules) (single_rel x ps t rules)
  | okdf_fun : forall env x ps t clauses,
    ok_params env ps ->
    List.Forall (fun clause => ok_clause (env @@ paramenv ps) clause ps t) clauses ->
    ok_def env (DecD x ps t clauses) (single_def x ps t clauses)
  | okdf_gram : forall env x ps t prods,
    ok_params env ps ->
    List.Forall (fun prod => ok_prod (env @@ paramenv ps) prod t) prods ->
    ok_def env (GramD x ps t prods) (single_gram x ps t prods)
  | okdf_rec : forall env env' defs,
    ok_defs (env @@ env') defs env' ->
    ok_def env (RecD defs) env'

with ok_defs : il_env -> list il_def -> il_env -> Prop :=
  | okdfs_nil : forall env,
    ok_defs env [] env_empty
  | okdfs_cons : forall env d1 defs env1 env',
    ok_def env d1 env1 ->
    ok_defs (env @@ env1) defs env' ->
    ok_defs env (d1 :: defs) (env1 @@ env')
.

Inductive ok_script : script -> Prop :=
  | okscript : forall defs env,
    ok_defs env_empty defs env ->
    ok_script defs
.

From Stdlib Require Import List String.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax env subst numerics utils semantics.
Import ListNotations.

(* Multi-step reduction and equivalence (doc/semantics/il/5-reduction.spectec).
   The single-step relations and type reduction are in semantics.v.
   A failing step (None) makes the whole reduction fail. *)

Inductive reduce_exp : store -> il_exp -> option il_exp -> Prop :=
  | re_refl : forall s e, reduce_exp s e (Some e)
  | re_step : forall s e e' oe,
    step_exp s e (Some e') ->
    reduce_exp s e' oe ->
    reduce_exp s e oe
  | re_fail : forall s e,
    step_exp s e None ->
    reduce_exp s e None
.

Inductive eq_exp : store -> il_exp -> il_exp -> Prop :=
  | eqe_rule : forall s e1 e2 e',
    reduce_exp s e1 (Some e') ->
    reduce_exp s e2 (Some e') ->
    eq_exp s e1 e2
.

Inductive reduce_arg : store -> il_arg -> option il_arg -> Prop :=
  | ra_refl : forall s a, reduce_arg s a (Some a)
  | ra_step : forall s a a' oa,
    step_arg s a (Some a') ->
    reduce_arg s a' oa ->
    reduce_arg s a oa
  | ra_fail : forall s a,
    step_arg s a None ->
    reduce_arg s a None
.

Inductive eq_arg : store -> il_arg -> il_arg -> Prop :=
  | eqa_rule : forall s a1 a2 a',
    reduce_arg s a1 (Some a') ->
    reduce_arg s a2 (Some a') ->
    eq_arg s a1 a2
.

Inductive reduce_param : store -> il_param -> option il_param -> Prop :=
  | rpa_refl : forall s p, reduce_param s p (Some p)
  | rpa_step : forall s p p' op,
    step_param s p (Some p') ->
    reduce_param s p' op ->
    reduce_param s p op
  | rpa_fail : forall s p,
    step_param s p None ->
    reduce_param s p None
.

Inductive reduce_prems : store -> list il_prem -> option (list il_prem) -> Prop :=
  | rp_refl : forall s ps, reduce_prems s ps (Some ps)
  | rp_step : forall s ps sbst ps' ops,
    step_prems s ps sbst (Some ps') ->
    reduce_prems s ps' ops ->
    reduce_prems s ps ops
  | rp_fail : forall s ps sbst,
    step_prems s ps sbst None ->
    reduce_prems s ps None
.

Inductive eq_prems : store -> list il_prem -> list il_prem -> Prop :=
  | eqp_rule : forall s ps1 ps2 ps',
    reduce_prems s ps1 (Some ps') ->
    reduce_prems s ps2 (Some ps') ->
    eq_prems s ps1 ps2
.

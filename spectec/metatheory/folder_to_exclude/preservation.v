From Stdlib Require Import List String Reals.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype rat ssrint.
From MetaSpectec Require Import syntax subst env numerics utils reduction typing.
Import ListNotations.
Check step_typ_ind'.
Lemma step_typ_confluent : forall s t t' t'',
  step_typ s t t' ->
  step_typ s t t'' ->
  exists c,
    reduce_typ s t' c /\ reduce_typ s t'' c.
Proof. 
  move=> s t t' t'' HStep HStep2.
  induction HStep; inversion HStep2; subst; (try (eexists; discriminate)).
  - injection H as ?; subst. destruct (n == n0) eqn:Heq. 
    (* - move/eqP: Heq => Heq. exists (VarT x (update (update ags n a') n a')). split; subst. 
      - econstructor. 2: apply rt_refl. econstructor. 
      - econstructor. 2: apply rt_refl. 
        econstructor. 
        eapply nth_error_impl_size in H as H2.

    - eapply rt_step. 2: apply rt_refl. 
      destruct (Nat.eqb n n0) eqn:Heq. unfold update.
      - subst. erewrite -> update_nth_error. reflexivity. apply H. 
    - eapply rt_step. 2: apply rt_refl.
      econstructor. *)
Admitted.

Lemma reduce_step_cat : forall s t t' t'',
  reduce_typ s t t' ->
  step_typ s t' t'' ->
  reduce_typ s t t''.
Proof.
  move=> s t t' t'' H.
  induction H; subst; move=> H2.
  - eapply rt_step; eauto. apply rt_refl.
  - econstructor. apply H. apply IHreduce_typ. apply H2.
Qed.

Lemma reduce_typ_trans : forall s t t' t'' ,
  reduce_typ s t t' -> 
  reduce_typ s t' t'' ->
  reduce_typ s t t''.
Proof. 
  move=> s t t' t'' H H2. 
  induction H; subst; auto.
  induction H2; subst; auto.
  - eapply rt_step; eauto.
  - apply IHreduce_typ0. 
    - apply H.
    - eapply reduce_step_cat in H0. 2: apply H1. apply H0.
    - move=> HH. apply IHreduce_typ. eapply rt_step; eauto.
Qed.

Lemma reduce_typ_confluent : forall s t a b,
  reduce_typ s t a ->
  reduce_typ s t b ->
  exists c,
    reduce_typ s a c /\ reduce_typ s b c.
Proof.
  move=> s t a b HReduce HReduce1.
  induction HReduce.
  - exists b. split. apply HReduce1. apply rt_refl.
  - induction HReduce1.
    - apply IHHReduce. eapply rt_step.
Admitted.

Lemma eq_typ_refl : forall s t,
  eq_typ s t t.
Proof.
  move=> s t.
  eapply eq_typ_rule.
  apply rt_refl.
  apply rt_refl.
  reflexivity.
Qed.

Lemma eq_typ_sym : forall s t t',
  eq_typ s t t' -> eq_typ s t' t.
Proof.
  move=> s t t' Heq.
  inversion Heq; subst.
  eapply eq_typ_rule.
  apply H0.
  apply H.
  reflexivity.
Qed.

Lemma eq_typ_trans : forall s t t' t'',
  eq_typ s t t' ->
  eq_typ s t' t'' ->
  eq_typ s t t''.
Proof.
  move=> s t t' t'' Heq1 Heq2.
  inversion Heq1; subst.
  inversion Heq2; subst.
  eapply reduce_typ_confluent in H0. 2: apply H1.
  destruct H0 as [c [HR1 HR2]].
  eapply (reduce_typ_trans _ _ _ _ H) in HR2.
  eapply (reduce_typ_trans _ _ _ _ H2) in HR1.
  econstructor.
  apply HR2.
  apply HR1.
  reflexivity.
Qed.

Theorem exp_preservation: forall env e e' t,
  ok_exp env e t ->
  step_exp (env_to_store env) e e' ->
  ok_exp env e' t.
Proof.
  move=> env e e' t HType HReduce.
  induction HReduce.
  (* UnopE ctx *)
  - inversion HType; subst.
    (* Unop Bool *)
    - apply oke_unop_bool. 
      eapply IHHReduce. 
      eauto.
    (* Unop Num *)
    - eapply oke_unop_num with (nt := nt); eauto.
      inversion H4; subst.
      eapply IHHReduce.
      eauto.
    (* Conv *)
    - inversion H0; subst.  
Admitted.

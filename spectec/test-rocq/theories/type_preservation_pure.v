
From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Import ListNotations.
Require Import Lia.

Opaque instrtype_sub.

Goal forall i : nat, i + 1 <= 2 ^ 32 - 1 -> i <= 2 ^ 32 - 1.
Proof.
  intros i H.
	apply: (leq_trans _ H).
  by rewrite leq_addr.
Qed.

Ltac resolve_wfness :=
	lazymatch goal with
	| H : Instrs_ok2 _ _ _ _ |- _ =>
		let wfc := fresh "HWfC" in
		let wfs := fresh "HWfS" in
		let wfai := fresh "HWfAI" in
		let wf := fresh "HWf" in 
		apply ainstrs_ok_context_store_wf in H as wf; destruct wf as [wfc [wfs wfai]]
	| H : Instr_ok2 _ _ _ _ |- _ =>
		let wfc := fresh "HWfC" in
		let wfs := fresh "HWfS" in
		let wfai := fresh "HWfAI" in
		let wf := fresh "HWf" in 
		apply ainstr_ok_context_store_wf in H as wf; destruct wf as [wfc [wfs wfai]]
	end
.


Lemma Step_pure__nop_preserves : forall v_S v_C v_ft,
	Instrs_ok2 v_S v_C [(admininstr_NOP )] v_ft ->
	Step_pure [(admininstr_NOP )] [] ->
	Instrs_ok2 v_S v_C [] v_ft.
Proof.
	move => v_S v_C v_ft HType _.
	resolve_wfness.
	invert_ais_typing.
	resolve_all_pt.
	resolve_subtyping.
	construct_ais_typing.
	auto.
Qed.

Lemma Step_pure__drop_preserves : forall v_S v_C (v_val : wasm.val) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_val v_val); (admininstr_DROP )] v_ft ->
	Step_pure [(admininstr_val v_val); (admininstr_DROP )] [] ->
	Instrs_ok2 v_S v_C [] v_ft.
Proof.
	move => v_S v_C v_val v_ft HType HReduce.
	resolve_wfness.
	invert_ais_typing.
	resolve_all_pt.

	join_subtyping_eq Hsub Hsub0.

	construct_ais_typing.
	resolve_subtyping.
	auto.
Qed.

Lemma Step_pure__select_preserves_helper : forall v_S v_C (v_val_1 : wasm.val) (v_val_2 : wasm.val) (v_c : num_) v_t v_ft,
	Instrs_ok2 v_S v_C [(admininstr_val v_val_1);(admininstr_val v_val_2);(admininstr_CONST I32 (v_c));(admininstr_SELECT v_t)] v_ft ->
	Instrs_ok2 v_S v_C [(admininstr_val v_val_1)] v_ft /\
	Instrs_ok2 v_S v_C [(admininstr_val v_val_2)] v_ft.
Proof.
	move => v_S v_C v_val_1 v_val_2 v_c v_t v_ft HType.
	resolve_wfness.
  invert_ais_typing.
	resolve_all_pt.

	join_subtyping_ge Hsub Hsub0.
	join_subtyping_ge Hsubi Hsub2.

	destruct v_t.
	{ (* Some *)
		destruct l.
		{ (* Some [] *)
			contradiction.
		}
		destruct l.
		{ (* Some [e] *)
			extract_premise.
			join_subtyping_eq Hsubi0 Hsub1.
			split;
			construct_ais_typing;
			eapply construct_ai_val; eauto.
			{
				eapply Val_ok_non_bot in HValok as Hnonbot;
				eapply (valtype_sub_non_bot _ _ Hsubv) in Hnonbot;
				by subst.
			}
			{
				eapply Val_ok_non_bot in HValok0 as Hnonbot;
				eapply (valtype_sub_non_bot _ _ Hsubv0) in Hnonbot;
				by subst.
			}
		}
		destruct Hai.
	}
	{ (* None *)
		extract_premise.
		join_subtyping_eq Hsubi0 Hsub1.
		split;
		construct_ais_typing;
		eapply construct_ai_val; eauto.
		{
			eapply Val_ok_non_bot in HValok as Hnonbot;
			eapply (valtype_sub_non_bot _ _ Hsubv) in Hnonbot;
			by subst.
		}
		{
			eapply Val_ok_non_bot in HValok0 as Hnonbot;
			eapply (valtype_sub_non_bot _ _ Hsubv0) in Hnonbot;
			by subst.
		}
	}
Qed.

Lemma Step_pure__select_true_preserves : forall v_S v_C (v_val_1 : wasm.val) (v_val_2 : wasm.val) (v_c : num_) v_t v_ft,
	Instrs_ok2 v_S v_C [(admininstr_val v_val_1);(admininstr_val v_val_2);(admininstr_CONST I32 (v_c));(admininstr_SELECT v_t)] v_ft ->
	Step_pure [(admininstr_val v_val_1);(admininstr_val v_val_2);(admininstr_CONST I32 (v_c));(admininstr_SELECT v_t)] [(admininstr_val v_val_1)] ->
	Instrs_ok2 v_S v_C [(admininstr_val v_val_1)] v_ft.
Proof.
	move=> v_S v_C v_val_1 v_val_2 v_c v_t v_ft HType HReduce.
	apply Step_pure__select_preserves_helper in HType as [H1 _].
	auto.
Qed.

Lemma Step_pure__select_false_preserves : forall v_S v_C (v_val_1 : wasm.val) (v_val_2 : wasm.val) (v_c : num_) v_t v_ft,
	Instrs_ok2 v_S v_C [(admininstr_val v_val_1);(admininstr_val v_val_2);(admininstr_CONST I32 (v_c));(admininstr_SELECT v_t)] v_ft ->
	Step_pure [(admininstr_val v_val_1);(admininstr_val v_val_2);(admininstr_CONST I32 (v_c));(admininstr_SELECT v_t)] [(admininstr_val v_val_2)] ->
	Instrs_ok2 v_S v_C [(admininstr_val v_val_2)] v_ft.
Proof.
	move=> v_S v_C v_val_1 v_val_2 v_c v_t v_ft HType HReduce.
	apply Step_pure__select_preserves_helper in HType as [_ H2].
	auto.
Qed.

Lemma Step_pure__if_preserves_helper : forall v_S v_C (v_c : num_) (v_bt: blocktype) (v_instrs_1 : (list instr)) (v_instrs_2 : (list instr)) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c);(admininstr_IFELSE v_bt v_instrs_1 v_instrs_2)] v_ft ->
	(Instrs_ok2 v_S v_C [(admininstr_BLOCK v_bt v_instrs_1)] v_ft /\
	Instrs_ok2 v_S v_C [(admininstr_BLOCK v_bt v_instrs_2)] v_ft).
Proof.
	move => v_S v_C v_c v_bt v_instrs_1 v_instrs_2 v_ft HType.
	resolve_wfness.
	inv_Forall HWfAI.
	invert_ais_typing.
	resolve_all_pt.

	join_subtyping_le Hsub0 Hsub.
	try rewrite sizecat_size2 in Hsubi.
	inversion HP0.
	split;
	construct_ais_typing;
	eapply (plain) with (v_instr := BLOCK v_bt _); eauto;
	econstructor; auto; econstructor; eauto.
Qed.

Lemma Step_pure__if_true_preserves : forall v_S v_C (v_c : num_) (v_bt: blocktype) (v_instrs_1 : (list instr)) (v_instrs_2 : (list instr)) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c);(admininstr_IFELSE v_bt v_instrs_1 v_instrs_2)] v_ft ->
	Step_pure [(admininstr_CONST I32 v_c);(admininstr_IFELSE v_bt v_instrs_1 v_instrs_2)] [(admininstr_BLOCK v_bt v_instrs_1)] ->
	Instrs_ok2 v_S v_C [(admininstr_BLOCK v_bt v_instrs_1)] v_ft.
Proof.
	move => v_S v_C v_c v_bt v_instrs_1 v_instrs_2 v_ft HType HReduce.
	eapply (Step_pure__if_preserves_helper) in HType.
	by destruct HType.
Qed.

Lemma Step_pure__if_false_preserves : forall v_S v_C (v_c : num_) (v_bt: blocktype) (v_instrs_1 : (list instr)) (v_instrs_2 : (list instr)) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c);(admininstr_IFELSE v_bt v_instrs_1 v_instrs_2)] v_ft ->
	Step_pure [(admininstr_CONST I32 v_c);(admininstr_IFELSE v_bt v_instrs_1 v_instrs_2)] [(admininstr_BLOCK v_bt v_instrs_2)] ->
	Instrs_ok2 v_S v_C [(admininstr_BLOCK v_bt v_instrs_2)] v_ft.
Proof.
	move => v_S v_C v_c v_bt v_instrs_1 v_instrs_2 v_ft HType HReduce.
	eapply (Step_pure__if_preserves_helper) in HType.
	by destruct HType.
Qed.

Lemma Step_pure__label_vals_preserves : forall v_S v_C (v_n : n) (v_instrs : (list instr)) (v_val : (list wasm.val)) v_ft,
	Instrs_ok2 v_S v_C [(LABEL_ v_n v_instrs (map admininstr_val v_val))] v_ft ->
	Step_pure [(LABEL_ v_n v_instrs (map admininstr_val v_val))] (map admininstr_val v_val) ->
	Instrs_ok2 v_S v_C (map admininstr_val v_val) v_ft.
Proof.
	move => v_S v_C v_n v_instrs v_val v_ft HType HReduce.
	resolve_wfness.
	invert_ais_typing.
	resolve_all_pt.
	invert_ais_typing.

	join_subtyping_trans Hsub0 Hsub.
	clear Hsub.
	construct_ais_typing; eauto.
	
	Unshelve. 
	apply HWfC.
	apply HWfS.
Qed.

Lemma Step_pure__br_zero_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val' : (list wasm.val)) (v_val : (list wasm.val)) v_admininstr v_ft,
	Instrs_ok2 v_S v_C [(LABEL_ v_n v_instr' ((((map admininstr_val v_val') ++ (map admininstr_val v_val)) ++ [admininstr_BR (mk_uN 0)]) ++ v_admininstr))] v_ft ->
	(|v_val| = v_n) ->
	Instrs_ok2 v_S v_C ((map admininstr_val v_val) ++ (map admininstr_instr v_instr')) v_ft.
Proof.
	move => v_S v_C v_n v_instr' v_val' v_val v_admininstr v_ft HType Hlength.
	resolve_wfness.
	repeat rewrite -catA in HType.
	invert_ais_typing.
	resolve_all_pt.
	invert_ais_typing.
	resolve_all_pt.
	list_to_seq.
	rewrite lookup_label_0 /= in H4; subst.

	eapply Forall2_length in HValsok0 as HLeneq.
	join_subtyping_le Hsub1 Hsub2.
	eapply construct_ais_subtyping.
	2: eapply Hsub.

	construct_ais_typing.
	{
		assert (([] :-> t0) <ti: ([] :-> t0)). { eapply instrtype_sub_refl. }
		eapply construct_ais_vals; eauto.
	}

	eapply construct_ais_subtyping.
	apply H1.
	by eapply instrtype_sub_iff_resulttype_sub'.
Qed.

Lemma Step_pure__br_succ_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val : (list wasm.val)) (v_l : labelidx) v_admininstr v_ft,
	Instrs_ok2 v_S v_C [(LABEL_ v_n v_instr' (((map admininstr_val v_val) ++ [admininstr_BR (mk_uN ((v_l :> nat) + 1))]) ++ v_admininstr))] v_ft ->
	Step_pure [(LABEL_ v_n v_instr' (((map admininstr_val v_val) ++ [admininstr_BR (mk_uN ((v_l :> nat) + 1))]) ++ v_admininstr))] ((map admininstr_val v_val) ++ [(admininstr_BR v_l)]) ->
	Instrs_ok2 v_S v_C ((map admininstr_val v_val) ++ [(admininstr_BR v_l)]) v_ft.
Proof.
	move => v_S v_C v_n v_instr' v_val v_l v_admininstr v_ft HType HReduce.
	resolve_wfness.
	repeat rewrite -catA in HType. 
	typing_inversion HType;
	simpl in Hai;
	extract_premise.
	typing_inversion H2.
	eapply construct_ais_instrtype_sub.
	eapply construct_ais_compose.
	{
		eapply construct_ais_vals'; eauto.
	}
	2: eapply Hsub. 

	rewrite -cat1s in H4.
	typing_inversion H4.
	typing_inversion H2;
	simpl in Hai;
	extract_premise.
	unfold_instrtype_sub Hsub0.
	subst.
	eapply construct_ais_subtyping.
	eapply construct_ais_typing_single.
	2: {
		eexists [], [], (ts ++ ts11_sub), extr0.
		split. auto.
		split. auto.
		split. eapply resulttype_sub_refl.
		split. eapply resulttype_sub_app; eauto.
		eapply resulttype_sub_refl.
	}
	eapply (plain _ _ (BR _)); eauto.


	assert (([extr: resulttype] @@ LABELS v_C) =
		(LABELS (prepend_label v_C extr))).
	{
	simpl. auto.
	}
	rewrite H.
	rewrite lookup_label_1.
	rewrite catA.
	constructor; eauto.
	{
		rewrite addn1 in H2.
		move/ltP in H2.
		apply/ltP.
		eapply Nat.succ_lt_mono in H2.
		by apply H2.
	}

	(* Wfness checks *)
	-
		inv_Forall HWfAI.
		inversion HP; subst.
		inv_Forall H8.
		inversion HP1; subst.
		econstructor.
		destruct v_l; simpl in *.
		inversion H4; subst.
		econstructor.
		apply: (leq_trans _ H8).
		by rewrite leq_addr.
	-
		inv_Forall HWfAI.
		inversion HP; subst.
		inv_Forall H7.
		inversion HP1; subst.
		econstructor.
		destruct v_l; simpl in *.
		inversion H3; subst.
		econstructor.
		apply: (leq_trans _ H7).
		by rewrite leq_addr.
Qed.

Lemma Step_pure__br_if_true_preserves : forall v_S v_C (v_c : num_) (v_l : labelidx) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c);(admininstr_BR_IF v_l)] v_ft ->
	Step_pure [(admininstr_CONST I32 v_c);(admininstr_BR_IF v_l)] [(admininstr_BR v_l)] ->
	Instrs_ok2 v_S v_C [(admininstr_BR v_l)] v_ft.
Proof.
	move => v_S v_C v_c v_l v_ft HType HReduce.
	resolve_wfness.
	typing_inversion HType.
	typing_inversion H1.
	typing_inversion H2.
	unfold_principal_typing Hai.
	unfold_principal_typing Hai0.
	destruct Hai0 as [t [He1 [H1 H2]]].
	destruct Hai as [Hwf Heq].
	inversion Heq; subst; clear Heq.
	
	inversion He1; subst; clear He1.
	eapply construct_ais_subtyping.
	eapply construct_ais_typing_single.
	
	eapply (plain _ _ (BR _)); eauto.
	eapply (br _ _ []); eauto.
	3: {
		eapply (instrtype_sub_compose1 _ _ _ _ _ _ _ Hsub) in Hsub0.
		rewrite cats0 in Hsub0.
		eapply Hsub0.
	}
	all:
		inv_Forall HWfAI;
		inversion HP0; subst;
		econstructor; eauto.
Qed.

Lemma Step_pure__br_if_false_preserves : forall v_S v_C (v_c : num_) (v_l : labelidx) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c);(admininstr_BR_IF v_l)] v_ft ->
	Step_pure [(admininstr_CONST I32 v_c);(admininstr_BR_IF v_l)] [] ->
	Instrs_ok2 v_S v_C [] v_ft.
Proof.
	move => v_S v_C v_c v_l v_ft HType HReduce.
	resolve_wfness.
	typing_inversion HType.
	typing_inversion H1.
	typing_inversion H2.
	unfold_principal_typing Hai.
	unfold_principal_typing Hai0.
	destruct Hai0 as [t [He1 [H1 H2]]].
	destruct Hai as [Hwf Heq].
	inversion Heq; subst; clear Heq.
	inversion He1; subst; clear He1.

	eapply (instrtype_sub_compose1 _ _ _ _ _ _ _ Hsub) in Hsub0.
	rewrite cats0 in Hsub0.
	eapply ais_empty_typing.
	split; auto.
	split; auto.
	unfold_instrtype_sub Hsub0; subst.
	apply resulttype_sub_app.
	auto.
	eapply resulttype_sub_trans; eauto.
Qed.

Lemma proj_identity : forall (A : eqType) a, mk_list A (proj_list_0 A a) = a.
Proof.
	destruct a.
	auto.
Qed.

Lemma Step_pure__br_table_lt_preserves : forall v_S v_C (v_i : num_) (v_l : (list labelidx)) (v_l' : labelidx) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_i);(admininstr_BR_TABLE v_l v_l')] v_ft ->
	Step_pure [(admininstr_CONST I32 v_i);(admininstr_BR_TABLE v_l v_l')] [(admininstr_BR (lookup_total v_l ((!(proj_num__0 v_i)) :> nat)))] ->
	((!(proj_num__0 v_i) :> nat) < Datatypes.length v_l) -> 
	Instrs_ok2 v_S v_C [(admininstr_BR (lookup_total v_l (!(proj_num__0 v_i) :> nat)))] v_ft.
Proof.
	move => v_S v_C v_i v_l v_l' v_ft HType HReduce H.
	resolve_wfness.
	inv_Forall HWfAI.

	typing_inversion HType.

	typing_inversion H2.
	unfold_principal_typing Hai.
	typing_inversion H1.

	destruct Hai as [t [t' [v_t [H1 [H2 [H3 [H4 H5]]]]]]].
	inversion H1; subst; clear H1.

	
	unfold_principal_typing Hai0.
	destruct Hai0 as [Hwf Hai0].
	inversion Hai0; subst; clear Hai0.
	
	rewrite catA in Hsub.
	eapply (instrtype_sub_compose1 _ _ _ _ _ _ _ Hsub0) in Hsub.
	rewrite cats0 in Hsub.

	eapply construct_ais_subtyping.
	eapply construct_ais_typing_single.
	eapply (plain _ _ (BR _)); eauto.
	eapply (br _ _ t _ t'); eauto.
	{
		simpl.
		unfold lookup_total.
	  eapply Forall_nth in H2.
		rewrite <- nth_is_same_as_seq_nth.
	  eapply H2.
	  by apply/ltP.
	}
	{
		inversion HP0; subst.
		econstructor.
		eapply Forall_size in H6.
		2: apply H.
		apply H6.
	}
	{ 
		inversion HP0; subst.
		econstructor.
		eapply Forall_size in H6.
		2: apply H.
		apply H6.
	}
	eapply (instrtype_sub_trans _ ((t ++ v_t) :-> t')).
	{
	  exists [], [], (t ++ v_t), t'.
	  do 4 split; auto. 2: eapply resulttype_sub_refl.
	  eapply resulttype_sub_app. eapply resulttype_sub_refl.
	  eapply (Forall_nth) in H3.
	  unfold Resulttype_subtype.
	  rewrite proj_identity.
		rewrite nth_is_same_as_seq_nth in H3.
	  eapply H3.
	  by apply/ltP.
	}
	auto.
Qed.

Lemma Step_pure__br_table_ge_preserves : forall v_S v_C (v_i : num_) (v_l : (list labelidx)) (v_l' : labelidx) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_i);(admininstr_BR_TABLE v_l v_l')] v_ft ->
	Step_pure [(admininstr_CONST I32 v_i);(admininstr_BR_TABLE v_l v_l')] [(admininstr_BR v_l')] ->
	(List.length v_l <= (!(proj_num__0 v_i) :> nat)) ->
	Instrs_ok2 v_S v_C [(admininstr_BR v_l')] v_ft.
Proof.
	move => v_S v_C v_i v_l v_l' v_ft HType HReduce H.
	resolve_wfness.
	typing_inversion HType.

	typing_inversion H2.
	unfold_principal_typing Hai.
	destruct Hai as [t [t' [v_t [H'' [H' [H3 [H4 H5]]]]]]].
	inversion H''; subst; clear H''.
	
	typing_inversion H1.
	unfold_principal_typing Hai.
	destruct Hai as [Hwf Hai].
	inversion Hai; subst; clear Hai.
	rewrite catA in Hsub.
	eapply (instrtype_sub_compose1 _ _ _ _ _ _ _ Hsub0) in Hsub.
	rewrite cats0 in Hsub.

	eapply construct_ais_subtyping.
	eapply (construct_ais_typing_single).
	eapply (plain _ _ (BR _)); eauto.
	eapply (br _ _ t _ t'); eauto.
	1, 2:
		inv_Forall HWfAI;
		inversion HP0; subst;
		econstructor; eauto.
	eapply (instrtype_sub_trans _ ((t ++ v_t) :-> t')).
	{
	  exists [], [], (t ++ v_t), t'.
	  do 4 split; auto. 2: eapply resulttype_sub_refl.
	  eapply resulttype_sub_app. eapply resulttype_sub_refl.
	  unfold Resulttype_subtype.
	  rewrite proj_identity.
	  eapply H5.
	}
	auto.
Qed.

Lemma Step_pure__frame_vals_preserves : forall v_S v_C (v_n : n) (v_f : frame) (v_val : (list wasm.val)) v_ft,
	Instrs_ok2 v_S v_C [(FRAME_ v_n v_f (map admininstr_val v_val))] v_ft ->
	Step_pure [(FRAME_ v_n v_f (map admininstr_val v_val))] (map admininstr_val v_val) ->
	Instrs_ok2 v_S v_C (map admininstr_val v_val) v_ft.
Proof.
	move => v_S v_C v_n v_f v_val v_ft HType HReduce.
	resolve_wfness.
	typing_inversion HType.
	simpl in Hai;
	extract_premise.
	inversion H2; subst.
	eapply construct_ais_instrtype_sub.
	eapply construct_ais_vals'; eauto.
	eauto.
Qed.

Lemma Step_pure__return_frame_preserves : forall v_S v_C (v_n : n) (v_f : frame) (v_val' : (list wasm.val)) (v_val : (list wasm.val)) v_admininstr v_ft,
	Instrs_ok2 v_S v_C [(FRAME_ v_n v_f ((((map admininstr_val v_val') ++ (map admininstr_val v_val)) ++ [(admininstr_RETURN )]) ++ v_admininstr))] v_ft ->
	Step_pure [(FRAME_ v_n v_f ((((map admininstr_val v_val') ++ (map admininstr_val v_val)) ++ [(admininstr_RETURN )]) ++ v_admininstr))] (map admininstr_val v_val) ->
	(|v_val| = v_n) ->
	Instrs_ok2 v_S v_C (map admininstr_val v_val) v_ft.
Proof.
	move => v_S v_C v_n v_f v_val' v_val v_admininstr v_ft HType HReduce HLength.
	resolve_wfness.
	repeat rewrite -catA in HType.
	typing_inversion HType.
	simpl in Hai.
	extract_premise.
	list_to_seq.
	inversion H2; subst; clear H2.
	eapply construct_ais_instrtype_sub.
	2: apply Hsub.

	typing_inversion H0.
	typing_inversion H6.
	rewrite -cat1s in H7.
	typing_inversion H7.

	typing_inversion H6.
	simpl in Hai.
	extract_premise.
	(* inversion H10; subst; clear H10.
	(* simpl in H9. *)
	(* rewrite H3 in H9. *)
	eq_to_prop.
	rewrite H6 in H11.
	inversion H11; subst; clear H11.
	eapply app_inv_tail in H; subst.
	(* clear H6 *)
	vals_typing_inversion H0.
	(* unfold _append, Append_Option, option_append in H6. *)
	(* inversion H3; subst; clear H3. *)

	eapply construct_ais_instrtype_sub.
	eapply construct_ais_vals.
	- eauto. eauto.
	- by eapply instrtype_sub_refl.
	- by eapply Hforall.

	eapply (instrtype_sub_compose_le _ _ _ _ _ _ _ _ Hsub1) in Hsub0
	  as [Hsub0 Hsub2].
	2: {
		eapply Forall2_length in Hforall.
		list_to_seq.
		rewrite H0 in Hforall.
		auto.
		
	}
	eapply instrtype_sub_trans.
	{
		eapply instrtype_sub_iff_resulttype_sub in Hsub2.
		eauto.
	}
	auto. *)
Admitted.

Lemma Step_pure__return_label_preserves : forall v_S v_C (v_n : n) (v_instr' : (list instr)) (v_val : (list wasm.val)) v_admininstr v_ft,
	Instrs_ok2 v_S v_C [(LABEL_ v_n v_instr' (((map admininstr_val v_val) ++ [(admininstr_RETURN )]) ++ v_admininstr))] v_ft ->
	Step_pure [(LABEL_ v_n v_instr' (((map admininstr_val v_val) ++ [(admininstr_RETURN )]) ++ v_admininstr))] ((map admininstr_val v_val) ++ [(admininstr_RETURN )]) ->
	Instrs_ok2 v_S v_C ((map admininstr_val v_val) ++ [(admininstr_RETURN )]) v_ft.
Proof.
	move => v_S v_C v_n v_instr' v_val v_admininstr v_ft HType HReduce.
	resolve_wfness.
	repeat rewrite -catA in HType.
	typing_inversion HType.
	simpl in Hai; extract_premise; subst.
	typing_inversion H2.
	rewrite -cat1s in H3.
	typing_inversion H3.
	typing_inversion H2.
	simpl in Hai; extract_premise; subst.
	inversion H5; subst; clear H5.
	simpl in H6.
	rewrite H2 in H6.
	eq_to_prop.
	inversion H6; subst; clear H6.
	eapply app_inv_tail in H; subst.
	unfold_instrtype_sub Hsub0; subst.

	eapply construct_ais_instrtype_sub.
	2: eapply Hsub.
	eapply construct_ais_compose with (t2s := (ts_sub ++ extr1 ++ t_lst)).
	{
		eapply construct_ais_instrtype_sub.
		eapply construct_ais_vals'; eauto.
		eapply instrtype_sub_iff_resulttype_sub.
		eapply resulttype_sub_app; eauto.
	}
	eapply construct_ais_instrtype_sub.
	eapply construct_ais_typing_single.
	2: by eapply instrtype_sub_refl.
	eapply plain with (v_instr := RETURN); eauto.
	rewrite catA.
	econstructor; eauto.
	eq_to_prop.
	auto.
Qed.

Lemma Step_pure__unop_val_preserves : forall v_S v_C v_t v_c_1 v_unop v_c v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST v_t v_c_1);(admininstr_UNOP v_t v_unop)] v_ft ->
	Step_pure [(admininstr_CONST v_t v_c_1);(admininstr_UNOP v_t v_unop)] [(admininstr_CONST v_t v_c)] ->
	wf_admininstr (admininstr_CONST v_t v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST v_t v_c)] v_ft.
Proof.
	move => v_S v_C t v unop_op v_c tf HType HReduce Hwfc.
	resolve_wfness.
	typing_inversion HType.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H1.
	unfold_principal_typing Hai.
	destruct Hai as [Hwf Hai].
	inversion Hai; subst; clear Hai.

	eapply construct_ais_subtyping.
	eapply construct_ais_typing_single.
	inversion Hwfc; subst; clear Hwfc.
	eapply (plain _ _ (CONST _ _)); eauto.
	apply const; eauto.
	econstructor; eauto.
	econstructor; eauto.
	eapply instrtype_sub_compose; eauto.
Qed.
 
Lemma Step_pure__binop_val_preserves : forall v_S v_C v_t v_c_1 v_c_2 v_binop v_c v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST v_t v_c_1);(admininstr_CONST v_t v_c_2);(admininstr_BINOP v_t v_binop)] v_ft ->
	Step_pure [(admininstr_CONST v_t v_c_1);(admininstr_CONST v_t v_c_2);(admininstr_BINOP v_t v_binop)] [(admininstr_CONST v_t v_c)] ->
	wf_admininstr (admininstr_CONST v_t v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST v_t v_c)] v_ft.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_binop v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
  typing_inversion HType.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H1.
	unfold_principal_typing Hai.
	destruct Hai as [Hwf1 Hai].
	inversion Hai; subst; clear Hai.
	typing_inversion H0.
	unfold_principal_typing Hai.
	destruct Hai as [Hwf2 Hai].
	inversion Hai; subst; clear Hai.
	eapply (instrtype_sub_compose1 _ _ [valtype_numtype v_t] _ _ _ _ Hsub0) in Hsub.
	rewrite cats0 in Hsub.

	eapply construct_ais_subtyping.
	eapply construct_ais_typing_single.
	eapply (plain _ _ (CONST _ _)); eauto.
	constructor; eauto.
	- econstructor; eauto.
		inversion Hwfc; eauto.
	- econstructor; eauto.
		inversion Hwfc; eauto.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma Step_pure__testop_preserves : forall v_S v_C v_t v_c_1 v_testop (v_c : num_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST v_t v_c_1);(admininstr_TESTOP v_t v_testop)] v_ft ->
	Step_pure [(admininstr_CONST v_t v_c_1);(admininstr_TESTOP v_t v_testop)] [(admininstr_CONST I32 v_c)] ->
	wf_admininstr (admininstr_CONST I32 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c)] v_ft.
Proof.
	move => v_S v_C t v unop_op v_c tf HType HReduce Hwfc.
	resolve_wfness.
	typing_inversion HType.
	typing_inversion H1.
	unfold_principal_typing Hai.
	destruct Hai as [Hwf Hai].
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.

	eapply construct_ais_subtyping.
	eapply construct_ais_typing_single.
	eapply (plain _ _ (CONST _ _)); eauto.
	constructor; eauto.
	- econstructor; eauto.
		inversion Hwfc; eauto.
	- econstructor; eauto.
		inversion Hwfc; eauto.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma Step_pure__relop_preserves : forall v_S v_C v_t v_c_1 v_c_2 v_relop (v_c : num_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST v_t v_c_1);(admininstr_CONST v_t v_c_2);(admininstr_RELOP v_t v_relop)] v_ft ->
	Step_pure [(admininstr_CONST v_t v_c_1);(admininstr_CONST v_t v_c_2);(admininstr_RELOP v_t v_relop)] [(admininstr_CONST I32 v_c)] ->
	wf_admininstr (admininstr_CONST I32 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c)] v_ft.
Proof.
	move => v_S v_C v_t v_c_1 v_c_2 v_relop v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	typing_inversion HType.
	typing_inversion H1.
	unfold_principal_typing Hai.
	destruct Hai as [Hwf Hai].
	inversion Hai; subst; clear Hai.
	typing_inversion H0.
	unfold_principal_typing Hai.
	destruct Hai as [Hwf2 Hai].
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	eapply (instrtype_sub_compose1 _ _ [valtype_numtype v_t] _ _ _ _ Hsub) in Hsub1.
	rewrite cats0 in Hsub1.

	eapply construct_ais_subtyping.
	eapply construct_ais_typing_single.
	eapply (plain _ _ (CONST _ _)); eauto.
	constructor; eauto.
	- econstructor; eauto.
		inversion Hwfc; eauto.
	- econstructor; eauto.
		inversion Hwfc; eauto.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma Step_pure__cvtop_val_preserves : forall v_S v_C v_t_1 v_c_1 v_t_2 v_cvtop v_c v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST v_t_1 v_c_1);(admininstr_CVTOP v_t_2 v_t_1 v_cvtop)] v_ft ->
	Step_pure [(admininstr_CONST v_t_1 v_c_1);(admininstr_CVTOP v_t_2 v_t_1 v_cvtop)] [(admininstr_CONST v_t_2 v_c)] ->
	wf_admininstr (admininstr_CONST v_t_2 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST v_t_2 v_c)] v_ft.
Proof.
	move => v_S v_C v_t_1 v_c_1 v_t_2 v_cvtop v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	typing_inversion HType.
	typing_inversion H2.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H1.
	unfold_principal_typing Hai.
	destruct Hai as [Hwf Hai].
	inversion Hai; subst; clear Hai.

	eapply construct_ais_subtyping.
	eapply construct_ais_typing_single.
	eapply (plain _ _ (CONST _ _)); eauto.
	constructor; eauto.
	- econstructor; eauto.
		inversion Hwfc; eauto.
	- econstructor; eauto.
		inversion Hwfc; eauto.
	eapply instrtype_sub_compose; eauto.
Qed.

Lemma Step_pure__local_tee_preserves : forall v_S v_C (v_val : wasm.val) (v_x : idx) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_val v_val);(admininstr_LOCAL_TEE v_x)] v_ft ->
	Step_pure [(admininstr_val v_val);(admininstr_LOCAL_TEE v_x)] [(admininstr_val v_val);(admininstr_val v_val);(admininstr_LOCAL_SET v_x)] ->
	Instrs_ok2 v_S v_C [(admininstr_val v_val);(admininstr_val v_val);(admininstr_LOCAL_SET v_x)] v_ft.
Proof.
	move => v_S v_C v_val v_x v_ft HType HReduce.
	resolve_wfness.
	invert_ais_typing.
	resolve_all_pt.

	join_subtyping_eq Hsub Hsub0.
	eapply (Val_ok_non_bot) in HValok as Hnonbot.
	eapply valtype_sub_non_bot in Hsubv.
	2: exact Hnonbot.
	subst.
	remember (lookup_total (context_LOCALS v_C) (proj_uN_0 v_x)) as t.

	construct_ais_typing.
	{
		eapply construct_ais_instrtype_sub.
		eapply construct_ais_typing_single.
		- eapply construct_ai_val; eauto.
		- eauto.
	}
	{
		eapply construct_ais_instrtype_sub.
		eapply construct_ais_typing_single.
		- eapply construct_ai_val; eauto.
		- rewrite -{1}(cats0 v_ft1).
		  eapply instrtype_sub_add_same.
	}
	eapply construct_ais_instrtype_sub.
	eapply construct_ais_typing_single.
	{
		inv_Forall HWfAI.
		inversion HP0; subst; clear HP0.
		eapply plain with (v_instr := LOCAL_SET _); eauto.
		econstructor; eauto.
		- econstructor; eauto.
		- econstructor; eauto.
	}
	rewrite -{2}(cats0 v_ft1).
	subst.
	eapply instrtype_sub_add_same.
Qed.

Lemma Step_pure__ref_is_null_helper : forall v_S v_C v_rt v_ft v_n,
	Instrs_ok2 v_S v_C [(admininstr_instr (REF_NULL v_rt)); admininstr_REF_IS_NULL] v_ft ->
	Step_pure [(admininstr_instr (REF_NULL v_rt)); admininstr_REF_IS_NULL] [admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))] ->
	(v_n = 1) \/ (v_n = 0) ->
	Instrs_ok2 v_S v_C [admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n))] v_ft.
Proof.
	move => v_S v_C v_rt v_ft v_n HType HReduce HDisj.
	resolve_wfness.
	typing_inversion HType.
	typing_inversion H1.
	unfold_principal_typing Hai.
	inversion Hai; subst; clear Hai.
	typing_inversion H2.
	unfold_principal_typing Hai.
	destruct Hai as [rt Ht].
	inversion Ht; subst; clear Ht.
	eapply (instrtype_sub_compose_le _ _ _ [] _ _ _ _ Hsub) in Hsub0
	  as [Hsub0 Hsub1].
	2: auto.
	eapply construct_ais_instrtype_sub.
	eapply construct_ais_typing_single.
	2: eapply Hsub0.
	eapply plain with (v_instr := CONST _ _); eauto.
	constructor; eauto.
	+ destruct HDisj; subst; econstructor; eauto; econstructor; eauto.
		- econstructor; econstructor; eauto.
		- econstructor; econstructor; eauto.
	+ destruct HDisj; subst; econstructor; eauto; econstructor; eauto.
		- econstructor; econstructor; eauto.
		- econstructor; econstructor; eauto.
Qed.

Lemma Step_pure__ref_is_null_true_preserves : forall v_S v_C v_rt v_ft,
	Instrs_ok2 v_S v_C [admininstr_REF_NULL v_rt: admininstr; admininstr_REF_IS_NULL] v_ft ->
	Step_pure [admininstr_REF_NULL v_rt: admininstr; admininstr_REF_IS_NULL] [admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1))] ->
	Instrs_ok2 v_S v_C [admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1))] v_ft.
Proof.
	intros.
	apply Step_pure__ref_is_null_helper with (v_n := 1) in H; eauto.
Qed.

Lemma Step_pure__ref_is_null_false_preserves : forall v_S v_C v_rt v_ft,
	Instrs_ok2 v_S v_C [admininstr_ref v_rt; admininstr_REF_IS_NULL] v_ft ->
	Step_pure [admininstr_ref v_rt; admininstr_REF_IS_NULL] [admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))] ->
	Instrs_ok2 v_S v_C [admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))] v_ft.
Proof.
	move => v_S v_C v_rt v_ft HType HReduce.
	resolve_wfness.
	destruct v_rt; simpl in *.
	- 
		(* REF_NULL *)
		apply Step_pure__ref_is_null_helper with (v_n := 0) in HType; eauto.
	- (* REF_FUNC_ADDR *)
		typing_inversion HType.
		typing_inversion H1.
		unfold_principal_typing Hai.
		destruct Hai as [functype Ht].
		inversion Ht; subst; clear Ht.
		typing_inversion H2.
		unfold_principal_typing Hai.
		destruct Hai as [rt Ht].
		inversion Ht; subst; clear Ht.
		injection H as ?; subst.
		eapply (instrtype_sub_compose_le _ _ _ [] _ _ _ _ Hsub) in Hsub0
	  as [Hsub0 Hsub1].
		2: auto.
		eapply construct_ais_instrtype_sub.
		eapply construct_ais_typing_single.
		2: eapply Hsub0.
		eapply plain with (v_instr := CONST _ _); eauto.
		constructor; eauto.
		1,2:
		econstructor; econstructor; eauto;
		econstructor; econstructor; eauto.
	- typing_inversion HType.
		typing_inversion H1.
		unfold_principal_typing Hai.
		typing_inversion H2.
		unfold_principal_typing Hai0.
		destruct Hai0 as [rt Ht].
		inversion Ht; subst; clear Ht.
		injection Hai as ?; subst.
		eapply (instrtype_sub_compose_le _ _ _ [] _ _ _ _ Hsub) in Hsub0
	  as [Hsub0 Hsub1].
		2: auto.
		eapply construct_ais_instrtype_sub.
		eapply construct_ais_typing_single.
		2: eapply Hsub0.
		eapply plain with (v_instr := CONST _ _); eauto.
		constructor; eauto.
		all: 
			econstructor; econstructor; eauto;
			econstructor; econstructor; eauto.
Qed.

(* Preservation of Instrs_ok2 under pure steps *)

Theorem t_pure_preservation: forall v_s v_ais v_ais' v_C tf,
    Instrs_ok2 v_s v_C v_ais tf ->
    Step_pure v_ais v_ais' ->
    Instrs_ok2 v_s v_C v_ais' tf.
Proof.
	move => v_s v_ais v_ais' v_C tf HType HReduce.
	resolve_wfness.
	eapply Step_pure_is_wf in HReduce as HWfAI'; eauto.
	inversion HReduce; subst.
	all: eq_to_prop; subst; inv_Forall HWfAI'; try by eapply construct_ais_trap.
	- eapply Step_pure__nop_preserves; eauto.
	- eapply Step_pure__drop_preserves; eauto.
	- eapply Step_pure__select_true_preserves; eauto.
	- eapply Step_pure__select_false_preserves; eauto.
	- eapply Step_pure__if_true_preserves; eauto.
	- eapply Step_pure__if_false_preserves; eauto.
	- eapply Step_pure__label_vals_preserves; eauto.
	- eapply Step_pure__br_zero_preserves; eauto.
	- eapply Step_pure__br_succ_preserves; eauto.
	- eapply Step_pure__br_if_true_preserves; eauto.
	- eapply Step_pure__br_if_false_preserves; eauto.
	- eapply Step_pure__br_table_lt_preserves; eauto.
	- eapply Step_pure__br_table_ge_preserves; eauto.
	- eapply Step_pure__frame_vals_preserves; eauto.
	- eapply Step_pure__return_frame_preserves; eauto.
	- eapply Step_pure__return_label_preserves; eauto.
	- eapply Step_pure__unop_val_preserves; eauto. 
	- eapply Step_pure__binop_val_preserves; eauto.
	- eapply Step_pure__testop_preserves; eauto.
	- eapply Step_pure__relop_preserves; eauto.
	- eapply Step_pure__cvtop_val_preserves; eauto.
	- eapply Step_pure__ref_is_null_true_preserves; eauto.
	- eapply Step_pure__ref_is_null_false_preserves; eauto.
	24: eapply Step_pure__local_tee_preserves; eauto.
	(* The rest are all simd instructions *)
Admitted.
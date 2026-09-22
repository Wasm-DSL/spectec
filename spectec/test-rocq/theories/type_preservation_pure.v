
From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssrnat.
Import ListNotations.
Require Import Lia.

Opaque instrtype_sub.

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
	inversion HP0; subst.
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
	Instrs_ok2 v_S v_C [(LABEL_ v_n v_instr' (((map admininstr_val v_val) ++ [admininstr_BR (mk_uN ((v_l :> N) + 1)%BN)]) ++ v_admininstr))] v_ft ->
	Step_pure [(LABEL_ v_n v_instr' (((map admininstr_val v_val) ++ [admininstr_BR (mk_uN ((v_l :> N) + 1)%BN)]) ++ v_admininstr))] ((map admininstr_val v_val) ++ [(admininstr_BR v_l)]) ->
	Instrs_ok2 v_S v_C ((map admininstr_val v_val) ++ [(admininstr_BR v_l)]) v_ft.
Proof.
	move => v_S v_C v_n v_instr' v_val v_l v_admininstr v_ft HType HReduce.
	resolve_wfness.
	apply Step_pure_is_wf in HReduce as HWfGoal; eauto.
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
		apply/N.ltb_lt.
		move/N.ltb_lt in H2.
		rewrite cvt_succ' in H2.
		rewrite N.add_1_r in H2.
		eapply N.succ_lt_mono in H2.
		by apply H2.
	}

	(* Wfness checks *)
	all:
		inv_Forall HWfGoal;
		inversion HP; subst;
		econstructor; eauto.
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
	Step_pure [(admininstr_CONST I32 v_i);(admininstr_BR_TABLE v_l v_l')] [(admininstr_BR (lookup_total v_l ((!(proj_num__0 v_i)) :> N)))] ->
	((!(proj_num__0 v_i) :> N) <? | v_l |)%BN -> 
	Instrs_ok2 v_S v_C [(admininstr_BR (lookup_total v_l (!(proj_num__0 v_i) :> N)))] v_ft.
Proof.
	move => v_S v_C v_i v_l v_l' v_ft HType HReduce H.
	resolve_wfness.
	inv_Forall HWfAI.

	typing_inversion HType.

	typing_inversion H2.
	unfold_principal_typing Hai.
	typing_inversion H1.
	ineq_to_propH H.

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
	  eapply Forall_size in H2.
	  eapply H2.
		apply H.
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
	  eapply (Forall_size) in H3.
	  unfold Resulttype_subtype.
	  rewrite proj_identity.
	  eapply H3.
	  by apply H.
	}
	auto.
Qed.

Lemma Step_pure__br_table_ge_preserves : forall v_S v_C (v_i : num_) (v_l : (list labelidx)) (v_l' : labelidx) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_i);(admininstr_BR_TABLE v_l v_l')] v_ft ->
	Step_pure [(admininstr_CONST I32 v_i);(admininstr_BR_TABLE v_l v_l')] [(admininstr_BR v_l')] ->
	Instrs_ok2 v_S v_C [(admininstr_BR v_l')] v_ft.
Proof.
	move => v_S v_C v_i v_l v_l' v_ft HType HReduce.
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
	inversion H10; subst; clear H10.
	(* simpl in H9. *)
	(* rewrite H3 in H9. *)
	eq_to_prop.
	unfold prepend_return in H11. simpl in H11.
	rewrite H6 in H11.
	inversion H11; subst; clear H11.
	eapply app_inv_tail in H; subst.
	(* clear H6 *)
	vals_typing_inversion H0.
	unfold _append, Append_Option, option_append in H6.
	inversion H6; subst; clear H6.

	eapply construct_ais_instrtype_sub.
	eapply construct_ais_vals.
	- eauto. eauto.
	- by eapply instrtype_sub_refl.
	- by eapply Hforall.

	eapply (instrtype_sub_compose_le _ _ _ _ _ _ _ _ Hsub1) in Hsub0
	  as [Hsub0 Hsub2].
	2: {
		eapply Forall2_seq_size in Hforall.
		rewrite H3 in Hforall.
		auto.	
	}
	eapply instrtype_sub_trans.
	{
		eapply instrtype_sub_iff_resulttype_sub in Hsub2.
		eauto.
	}
	apply instrtype_sub_refl.
Qed.

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
	(v_n = 1%num) \/ (v_n = 0%num) ->
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
	apply Step_pure__ref_is_null_helper with (v_n := 1%num) in H; eauto.
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
		apply Step_pure__ref_is_null_helper with (v_n := 0%num) in HType; eauto.
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

(* ---------------------------------------------------------------------- *)
(* Typing inversion for the SIMD administrative instructions.              *)
(* ai_principal_typing has no case for them (it yields True), so we go     *)
(* through Instr_ok directly instead.                                      *)
(* ---------------------------------------------------------------------- *)

Lemma ais_single_plain_typing_inversion : forall v_S v_C (v_instr : instr) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr v_instr)] (t1s :-> t2s) ->
	exists t1s_sup t2s_sub,
		Instr_ok v_C v_instr (t1s_sup :-> t2s_sub) /\
		((t1s_sup :-> t2s_sub) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C v_instr t1s t2s HType.
	apply ais_single_typing_inversion' in HType as [t1s_sup [t2s_sub [HType Hsub]]].
	apply ai_typing_inversion' in HType.
	by exists t1s_sup, t2s_sub.
Qed.

Lemma vconst_result_typing : forall v_S v_C c,
	wf_store v_S -> wf_context v_C ->
	wf_admininstr (admininstr_VCONST V128 c) ->
	Instr_ok2 v_S v_C (admininstr_VCONST V128 c) ([] :-> [valtype_V128]).
Proof.
	move => v_S v_C c HS HC Hwf.
	inversion Hwf; subst.
	eapply (plain _ _ (VCONST V128 c)); eauto.
	- by apply: vconst; eauto; econstructor; eauto.
	- by econstructor; eauto.
Qed.

Lemma const_result_typing : forall v_S v_C nt c,
	wf_store v_S -> wf_context v_C ->
	wf_admininstr (admininstr_CONST nt c) ->
	Instr_ok2 v_S v_C (admininstr_CONST nt c) ([] :-> [valtype_numtype nt]).
Proof.
	move => v_S v_C nt c HS HC Hwf.
	inversion Hwf; subst.
	eapply (plain _ _ (CONST nt c)); eauto.
	- by apply: const; eauto; econstructor; eauto.
	- by econstructor; eauto.
Qed.

Lemma ais_vconst_typing_inversion : forall v_S v_C c t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 c)] (t1s :-> t2s) ->
	(([] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C c t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VCONST V128 c)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_const_typing_inversion : forall v_S v_C nt c t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_CONST nt c)] (t1s :-> t2s) ->
	(([] :-> [valtype_numtype nt]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C nt c t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (CONST nt c)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

(* ---------------------------------------------------------------------- *)
(* Typing inversion for each SIMD instruction *)
(* ---------------------------------------------------------------------- *)

Lemma ais_vvunop_typing_inversion : forall v_S v_C (v_op : wasm.vvunop) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VVUNOP V128 v_op))] (t1s :-> t2s) ->
	(([valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VVUNOP V128 v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vvbinop_typing_inversion : forall v_S v_C (v_op : wasm.vvbinop) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VVBINOP V128 v_op))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VVBINOP V128 v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vvternop_typing_inversion : forall v_S v_C (v_op : wasm.vvternop) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VVTERNOP V128 v_op))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_V128; valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VVTERNOP V128 v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vvtestop_typing_inversion : forall v_S v_C (v_op : wasm.vvtestop) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VVTESTOP V128 v_op))] (t1s :-> t2s) ->
	(([valtype_V128] :-> [valtype_I32]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VVTESTOP V128 v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vunop_typing_inversion : forall v_S v_C (sh : wasm.shape) (v_op : wasm.vunop_) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VUNOP sh v_op))] (t1s :-> t2s) ->
	(([valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VUNOP sh v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vbinop_typing_inversion : forall v_S v_C (sh : wasm.shape) (v_op : wasm.vbinop_) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VBINOP sh v_op))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VBINOP sh v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vtestop_typing_inversion : forall v_S v_C (sh : wasm.shape) (v_op : wasm.vtestop_) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VTESTOP sh v_op))] (t1s :-> t2s) ->
	(([valtype_V128] :-> [valtype_I32]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VTESTOP sh v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vrelop_typing_inversion : forall v_S v_C (sh : wasm.shape) (v_op : wasm.vrelop_) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VRELOP sh v_op))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VRELOP sh v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vshiftop_typing_inversion : forall v_S v_C (sh : wasm.ishape) (v_op : wasm.vshiftop_) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VSHIFTOP sh v_op))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_I32] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VSHIFTOP sh v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vbitmask_typing_inversion : forall v_S v_C (sh : wasm.ishape) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VBITMASK sh))] (t1s :-> t2s) ->
	(([valtype_V128] :-> [valtype_I32]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VBITMASK sh)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vswizzle_typing_inversion : forall v_S v_C (sh : wasm.ishape) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VSWIZZLE sh))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VSWIZZLE sh)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vshuffle_typing_inversion : forall v_S v_C (sh : wasm.ishape) (i_lst : seq wasm.laneidx) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VSHUFFLE sh i_lst))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh i_lst t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VSHUFFLE sh i_lst)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vsplat_typing_inversion : forall v_S v_C (sh : wasm.shape) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VSPLAT sh))] (t1s :-> t2s) ->
	(([(valtype_numtype (shunpack sh))] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VSPLAT sh)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vextract_lane_typing_inversion : forall v_S v_C (sh : wasm.shape) (sx_opt : option wasm.sx) (i : wasm.laneidx) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VEXTRACT_LANE sh sx_opt i))] (t1s :-> t2s) ->
	(([valtype_V128] :-> [(valtype_numtype (shunpack sh))]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh sx_opt i t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VEXTRACT_LANE sh sx_opt i)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vreplace_lane_typing_inversion : forall v_S v_C (sh : wasm.shape) (i : wasm.laneidx) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VREPLACE_LANE sh i))] (t1s :-> t2s) ->
	(([valtype_V128; (valtype_numtype (shunpack sh))] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh i t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VREPLACE_LANE sh i)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vextunop_typing_inversion : forall v_S v_C (sh_1 sh_2 : wasm.ishape) (v_op : wasm.vextunop_) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VEXTUNOP sh_1 sh_2 v_op))] (t1s :-> t2s) ->
	(([valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh_1 sh_2 v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VEXTUNOP sh_1 sh_2 v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vextbinop_typing_inversion : forall v_S v_C (sh_1 sh_2 : wasm.ishape) (v_op : wasm.vextbinop_) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VEXTBINOP sh_1 sh_2 v_op))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh_1 sh_2 v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VEXTBINOP sh_1 sh_2 v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vnarrow_typing_inversion : forall v_S v_C (sh_1 sh_2 : wasm.ishape) (v_sx : wasm.sx) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VNARROW sh_1 sh_2 v_sx))] (t1s :-> t2s) ->
	(([valtype_V128; valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh_1 sh_2 v_sx t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VNARROW sh_1 sh_2 v_sx)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

Lemma ais_vcvtop_typing_inversion : forall v_S v_C (sh_1 sh_2 : wasm.shape) (v_op : wasm.vcvtop) t1s t2s,
	Instrs_ok2 v_S v_C [(admininstr_instr (VCVTOP sh_1 sh_2 v_op))] (t1s :-> t2s) ->
	(([valtype_V128] :-> [valtype_V128]) <ti: (t1s :-> t2s)).
Proof.
	move => v_S v_C sh_1 sh_2 v_op t1s t2s HType.
	apply (ais_single_plain_typing_inversion _ _ (VCVTOP sh_1 sh_2 v_op)) in HType
		as [t1s_sup [t2s_sub [HI Hsub]]].
	by inversion HI; subst.
Qed.

(* ---------------------------------------------------------------------- *)
(* Generic preservation lemmas for `n operands + one operator' *)
(* ---------------------------------------------------------------------- *)

Lemma vec_preserves_1 : forall v_S v_C (a op res : admininstr) t_a t_out v_ft,
	Instrs_ok2 v_S v_C [a; op] v_ft ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [a] (t1s :-> t2s) ->
		(([] :-> [t_a]) <ti: (t1s :-> t2s))) ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [op] (t1s :-> t2s) ->
		(([t_a] :-> [t_out]) <ti: (t1s :-> t2s))) ->
	Instr_ok2 v_S v_C res ([] :-> [t_out]) ->
	Instrs_ok2 v_S v_C [res] v_ft.
Proof.
	move => v_S v_C a op res t_a t_out v_ft HType Hinva Hinvop Hres.
	destruct_functypes.
	typing_inversion HType.
	apply Hinva in H1. apply Hinvop in H2.
	eapply construct_ais_subtyping.
	- by apply: construct_ais_typing_single; exact Hres.
	- by eapply instrtype_sub_compose; eauto.
Qed.

Lemma vec_preserves_2 : forall v_S v_C (a b op res : admininstr) t_a t_b t_out v_ft,
	Instrs_ok2 v_S v_C [a; b; op] v_ft ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [a] (t1s :-> t2s) ->
		(([] :-> [t_a]) <ti: (t1s :-> t2s))) ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [b] (t1s :-> t2s) ->
		(([] :-> [t_b]) <ti: (t1s :-> t2s))) ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [op] (t1s :-> t2s) ->
		(([t_a; t_b] :-> [t_out]) <ti: (t1s :-> t2s))) ->
	Instr_ok2 v_S v_C res ([] :-> [t_out]) ->
	Instrs_ok2 v_S v_C [res] v_ft.
Proof.
	move => v_S v_C a b op res t_a t_b t_out v_ft HType Hinva Hinvb Hinvop Hres.
	destruct_functypes.
	apply (ais_seq_typing_inversion _ _ [b; op] a) in HType as [t3s [HT1 Ha]].
	apply (ais_seq_typing_inversion _ _ [op] b) in HT1 as [t4s [Hop Hb]].
	apply Hinva in Ha. apply Hinvb in Hb. apply Hinvop in Hop.
	eapply (instrtype_sub_compose1 _ _ [t_a] _ _ _ _ Hb) in Hop.
	rewrite cats0 in Hop.
	eapply construct_ais_subtyping.
	- by apply: construct_ais_typing_single; exact Hres.
	- by eapply instrtype_sub_compose; eauto.
Qed.

Lemma vec_preserves_3 : forall v_S v_C (a b c op res : admininstr) t_a t_b t_c t_out v_ft,
	Instrs_ok2 v_S v_C [a; b; c; op] v_ft ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [a] (t1s :-> t2s) ->
		(([] :-> [t_a]) <ti: (t1s :-> t2s))) ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [b] (t1s :-> t2s) ->
		(([] :-> [t_b]) <ti: (t1s :-> t2s))) ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [c] (t1s :-> t2s) ->
		(([] :-> [t_c]) <ti: (t1s :-> t2s))) ->
	(forall t1s t2s, Instrs_ok2 v_S v_C [op] (t1s :-> t2s) ->
		(([t_a; t_b; t_c] :-> [t_out]) <ti: (t1s :-> t2s))) ->
	Instr_ok2 v_S v_C res ([] :-> [t_out]) ->
	Instrs_ok2 v_S v_C [res] v_ft.
Proof.
	move => v_S v_C a b c op res t_a t_b t_c t_out v_ft
		HType Hinva Hinvb Hinvc Hinvop Hres.
	destruct_functypes.
	apply (ais_seq_typing_inversion _ _ [b; c; op] a) in HType as [t3s [HT1 Ha]].
	apply (ais_seq_typing_inversion _ _ [c; op] b) in HT1 as [t4s [HT2 Hb]].
	apply (ais_seq_typing_inversion _ _ [op] c) in HT2 as [t5s [Hop Hc]].
	apply Hinva in Ha. apply Hinvb in Hb. apply Hinvc in Hc. apply Hinvop in Hop.
	eapply (instrtype_sub_compose1 _ _ [t_a; t_b] _ _ _ _ Hc) in Hop.
	rewrite cats0 in Hop.
	eapply (instrtype_sub_compose1 _ _ [t_a] _ _ _ _ Hb) in Hop.
	rewrite cats0 in Hop.
	eapply construct_ais_subtyping.
	- by apply: construct_ais_typing_single; exact Hres.
	- by eapply instrtype_sub_compose; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Preservation for each SIMD reduction rule *)
(* ---------------------------------------------------------------------- *)

Lemma Step_pure__vvunop_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (v_op : wasm.vvunop) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VVUNOP V128 v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VVUNOP V128 v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vvunop_typing_inversion _ _ v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vvbinop_preserves : forall v_S v_C (v_c_1 v_c_2 : wasm.vec_) (v_op : wasm.vvbinop) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VVBINOP V128 v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VVBINOP V128 v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vconst_typing_inversion _ _ v_c_2).
	- exact: (ais_vvbinop_typing_inversion _ _ v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vvternop_preserves : forall v_S v_C (v_c_1 v_c_2 v_c_3 : wasm.vec_) (v_op : wasm.vvternop) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VCONST V128 v_c_3); (admininstr_VVTERNOP V128 v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VCONST V128 v_c_3); (admininstr_VVTERNOP V128 v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 v_c_3 v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_3 _ _ _ _ _ _ _ valtype_V128 valtype_V128 valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vconst_typing_inversion _ _ v_c_2).
	- exact: (ais_vconst_typing_inversion _ _ v_c_3).
	- exact: (ais_vvternop_typing_inversion _ _ v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vvtestop_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (v_op : wasm.vvtestop) (v_c : wasm.num_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VVTESTOP V128 v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VVTESTOP V128 v_op)] [(admininstr_CONST I32 v_c)] ->
	wf_admininstr (admininstr_CONST I32 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 (valtype_numtype I32) _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vvtestop_typing_inversion _ _ v_op).
	- by apply: const_result_typing.
Qed.

Lemma Step_pure__vunop_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (sh : wasm.shape) (v_op : wasm.vunop_) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VUNOP sh v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VUNOP sh v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 sh v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vunop_typing_inversion _ _ sh v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vbinop_val_preserves : forall v_S v_C (v_c_1 v_c_2 : wasm.vec_) (sh : wasm.shape) (v_op : wasm.vbinop_) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VBINOP sh v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VBINOP sh v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 sh v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vconst_typing_inversion _ _ v_c_2).
	- exact: (ais_vbinop_typing_inversion _ _ sh v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vtestop_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (sh : wasm.shape) (v_op : wasm.vtestop_) (v_c : wasm.num_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VTESTOP sh v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VTESTOP sh v_op)] [(admininstr_CONST I32 v_c)] ->
	wf_admininstr (admininstr_CONST I32 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 sh v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 (valtype_numtype I32) _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vtestop_typing_inversion _ _ sh v_op).
	- by apply: const_result_typing.
Qed.

Lemma Step_pure__vrelop_preserves : forall v_S v_C (v_c_1 v_c_2 : wasm.vec_) (sh : wasm.shape) (v_op : wasm.vrelop_) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VRELOP sh v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VRELOP sh v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 sh v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vconst_typing_inversion _ _ v_c_2).
	- exact: (ais_vrelop_typing_inversion _ _ sh v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vshiftop_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (v_c_2 : wasm.num_) (sh : wasm.ishape) (v_op : wasm.vshiftop_) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_CONST I32 v_c_2); (admininstr_VSHIFTOP sh v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_CONST I32 v_c_2); (admininstr_VSHIFTOP sh v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 sh v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 (valtype_numtype I32) valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_const_typing_inversion _ _ I32 v_c_2).
	- exact: (ais_vshiftop_typing_inversion _ _ sh v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vbitmask_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (sh : wasm.ishape) (v_c : wasm.num_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VBITMASK sh)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VBITMASK sh)] [(admininstr_CONST I32 v_c)] ->
	wf_admininstr (admininstr_CONST I32 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 sh v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 (valtype_numtype I32) _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vbitmask_typing_inversion _ _ sh).
	- by apply: const_result_typing.
Qed.

Lemma Step_pure__vswizzle_preserves : forall v_S v_C (v_c_1 v_c_2 : wasm.vec_) (sh : wasm.ishape) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VSWIZZLE sh)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VSWIZZLE sh)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 sh v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vconst_typing_inversion _ _ v_c_2).
	- exact: (ais_vswizzle_typing_inversion _ _ sh).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vshuffle_preserves : forall v_S v_C (v_c_1 v_c_2 : wasm.vec_) (sh : wasm.ishape) (i_lst : seq wasm.laneidx) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VSHUFFLE sh i_lst)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VSHUFFLE sh i_lst)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 sh i_lst v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vconst_typing_inversion _ _ v_c_2).
	- exact: (ais_vshuffle_typing_inversion _ _ sh i_lst).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vsplat_preserves : forall v_S v_C (v_Lnn : wasm.Lnn) (v_c_1 : wasm.num_) (v_N : wasm.res_N) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_CONST (unpack v_Lnn) v_c_1); (admininstr_VSPLAT (X v_Lnn (mk_dim v_N)))] v_ft ->
	Step_pure [(admininstr_CONST (unpack v_Lnn) v_c_1); (admininstr_VSPLAT (X v_Lnn (mk_dim v_N)))] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_Lnn v_c_1 v_N v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ (valtype_numtype (unpack v_Lnn)) valtype_V128 _ HType).
	- exact: (ais_const_typing_inversion _ _ (unpack v_Lnn) v_c_1).
	- exact: (ais_vsplat_typing_inversion _ _ (X v_Lnn (mk_dim v_N))).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vreplace_lane_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (v_Lnn : wasm.Lnn) (v_c_2 : wasm.num_) (v_N : wasm.res_N) (i : wasm.laneidx) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_CONST (unpack v_Lnn) v_c_2); (admininstr_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_CONST (unpack v_Lnn) v_c_2); (admininstr_VREPLACE_LANE (X v_Lnn (mk_dim v_N)) i)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_Lnn v_c_2 v_N i v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 (valtype_numtype (unpack v_Lnn)) valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_const_typing_inversion _ _ (unpack v_Lnn) v_c_2).
	- exact: (ais_vreplace_lane_typing_inversion _ _ (X v_Lnn (mk_dim v_N)) i).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vextunop_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (sh_1 sh_2 : wasm.ishape) (v_op : wasm.vextunop_) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VEXTUNOP sh_1 sh_2 v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VEXTUNOP sh_1 sh_2 v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 sh_1 sh_2 v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vextunop_typing_inversion _ _ sh_1 sh_2 v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vextbinop_preserves : forall v_S v_C (v_c_1 v_c_2 : wasm.vec_) (sh_1 sh_2 : wasm.ishape) (v_op : wasm.vextbinop_) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VEXTBINOP sh_1 sh_2 v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VEXTBINOP sh_1 sh_2 v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 sh_1 sh_2 v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vconst_typing_inversion _ _ v_c_2).
	- exact: (ais_vextbinop_typing_inversion _ _ sh_1 sh_2 v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vnarrow_preserves : forall v_S v_C (v_c_1 v_c_2 : wasm.vec_) (sh_1 sh_2 : wasm.ishape) (v_sx : wasm.sx) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VNARROW sh_1 sh_2 v_sx)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCONST V128 v_c_2); (admininstr_VNARROW sh_1 sh_2 v_sx)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 v_c_2 sh_1 sh_2 v_sx v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_2 _ _ _ _ _ _ valtype_V128 valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vconst_typing_inversion _ _ v_c_2).
	- exact: (ais_vnarrow_typing_inversion _ _ sh_1 sh_2 v_sx).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vcvtop_preserves : forall v_S v_C (v_c_1 : wasm.vec_) (sh_1 sh_2 : wasm.shape) (v_op : wasm.vcvtop) (v_c : wasm.vec_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1); (admininstr_VCVTOP sh_1 sh_2 v_op)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1); (admininstr_VCVTOP sh_1 sh_2 v_op)] [(admininstr_VCONST V128 v_c)] ->
	wf_admininstr (admininstr_VCONST V128 v_c) ->
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c)] v_ft.
Proof.
	move => v_S v_C v_c_1 sh_1 sh_2 v_op v_c v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 valtype_V128 _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- exact: (ais_vcvtop_typing_inversion _ _ sh_1 sh_2 v_op).
	- by apply: vconst_result_typing.
Qed.

Lemma Step_pure__vextract_lane_num_preserves :
	forall v_S v_C (v_c_1 : wasm.vec_) (nt : wasm.numtype) (v_N : wasm.res_N)
		(i : wasm.laneidx) (v_c_2 : wasm.num_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1);
		(admininstr_VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1);
		(admininstr_VEXTRACT_LANE (X (lanetype_numtype nt) (mk_dim v_N)) None i)]
		[(admininstr_CONST nt v_c_2)] ->
	wf_admininstr (admininstr_CONST nt v_c_2) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST nt v_c_2)] v_ft.
Proof.
	move => v_S v_C v_c_1 nt v_N i v_c_2 v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 (valtype_numtype nt) _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- (* (shunpack (X (lanetype_numtype nt) _)) = (unpack (lanetype_numtype nt)) = nt *)
		destruct nt;
		exact: (ais_vextract_lane_typing_inversion _ _
			(X (lanetype_numtype _) (mk_dim v_N)) None i).
	- by apply: const_result_typing.
Qed.

Lemma Step_pure__vextract_lane_pack_preserves :
	forall v_S v_C (v_c_1 : wasm.vec_) (pt : wasm.packtype) (v_N : wasm.res_N)
		(v_sx : wasm.sx) (i : wasm.laneidx) (v_c_2 : wasm.num_) v_ft,
	Instrs_ok2 v_S v_C [(admininstr_VCONST V128 v_c_1);
		(admininstr_VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i)] v_ft ->
	Step_pure [(admininstr_VCONST V128 v_c_1);
		(admininstr_VEXTRACT_LANE (X (lanetype_packtype pt) (mk_dim v_N)) (Some v_sx) i)]
		[(admininstr_CONST I32 v_c_2)] ->
	wf_admininstr (admininstr_CONST I32 v_c_2) ->
	Instrs_ok2 v_S v_C [(admininstr_CONST I32 v_c_2)] v_ft.
Proof.
	move => v_S v_C v_c_1 pt v_N v_sx i v_c_2 v_ft HType HReduce Hwfc.
	resolve_wfness.
	eapply (vec_preserves_1 _ _ _ _ _ valtype_V128 (valtype_numtype I32) _ HType).
	- exact: (ais_vconst_typing_inversion _ _ v_c_1).
	- (* (shunpack (X (lanetype_packtype pt) _)) = (unpack (lanetype_packtype pt)) = I32 *)
		destruct pt;
		exact: (ais_vextract_lane_typing_inversion _ _
			(X (lanetype_packtype _) (mk_dim v_N)) (Some v_sx) i).
	- by apply: const_result_typing.
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
	- eapply Step_pure__vvunop_preserves; eauto.
	- eapply Step_pure__vvbinop_preserves; eauto.
	- eapply Step_pure__vvternop_preserves; eauto.
	- eapply Step_pure__vvtestop_preserves; eauto.
	- eapply Step_pure__vunop_preserves; eauto.
	- eapply Step_pure__vbinop_val_preserves; eauto.
	- eapply Step_pure__vtestop_preserves; eauto.
	- eapply Step_pure__vtestop_preserves; eauto.
	- eapply Step_pure__vrelop_preserves; eauto.
	- eapply Step_pure__vshiftop_preserves; eauto.
	- eapply Step_pure__vbitmask_preserves; eauto.
	- eapply Step_pure__vswizzle_preserves; eauto.
	- eapply Step_pure__vshuffle_preserves; eauto.
	- eapply Step_pure__vsplat_preserves; eauto.
	- eapply Step_pure__vextract_lane_num_preserves; eauto.
	- eapply Step_pure__vextract_lane_pack_preserves; eauto.
	- eapply Step_pure__vreplace_lane_preserves; eauto.
	- eapply Step_pure__vextunop_preserves; eauto.
	- eapply Step_pure__vextbinop_preserves; eauto.
	- eapply Step_pure__vnarrow_preserves; eauto.
	- eapply Step_pure__vcvtop_preserves; eauto.
	- eapply Step_pure__vcvtop_preserves; eauto.
	- eapply Step_pure__vcvtop_preserves; eauto.
Qed.

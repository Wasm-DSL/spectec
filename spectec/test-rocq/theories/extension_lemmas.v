From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping type_preservation_pure.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Import ListNotations.

Lemma invert_opt_map_some {T U : Type} : forall (f : T -> U) (i : T),
	option_map f (Some i) = Some (f i).
Proof. move=> i; eauto. Qed.

Lemma invert_opt_map_none {T U : Type} : forall (f : T -> U), 
	option_map f None = None.
Proof. eauto. Qed.

Lemma s_invert_funcs: forall s,
	Store_ok s ->
	exists fts,
	List.Forall2 (fun f t =>
		exists minst v_func,
		(f = {| funcinst_TYPE := t;
			funcinst_MODULE := minst;
			CODE := v_func |})
			(* May add more here *)
	) (store_FUNCS s) fts.
Proof.
	move => s HSt.
	inversion HSt.
	eq_to_prop.
	rewrite H11 /=.
	clear -H6.
	exists functype_lst.

	move : funcinst_lst H6.
	induction functype_lst; move => funcinst_lst HFok.
	{
		inversion HFok; subst; auto.
	}
	destruct funcinst_lst; inversion HFok; subst; auto.
	econstructor.
	{
		inversion H2; subst.
		by exists v_moduleinst, v_func.
	}
	by eapply IHfunctype_lst.
Qed.

Lemma s_invert_globals: forall s,
	Store_ok s ->
	exists gts,
	List.Forall2 (fun g t =>
		exists v_mut v_vt v_v,
		(g = {| globalinst_TYPE := t;
			VALUE := v_v |}) /\
		(t = (mk_globaltype v_mut (v_vt : valtype))) /\
		(Val_ok s v_v (v_vt : valtype))
	) (store_GLOBALS s) gts.
Proof.
	move => s HSt.
	inversion HSt.
	eq_to_prop.
	rewrite {2}H11 /=.
	clear -H0.
	exists globaltype_lst.
	
	move : globalinst_lst H0.
	induction globaltype_lst; move => globalinst_lst HGok.
	{
		inversion HGok; subst; auto.
	}
	destruct globalinst_lst; inversion HGok; subst; auto.
	econstructor.
	{
		inversion H2; eq_to_prop; subst.
		by exists v_mut, t, v_val.
	}
	by eapply IHglobaltype_lst.
Qed.

Lemma s_invert_mems: forall s,
	Store_ok s ->
	exists mts,
	List.Forall2 (fun m t =>
		exists b_lst v_n v_m,
		let l := option_map (fun m => mk_uN m) v_m in
		(m = {| meminst_TYPE := t; BYTES := b_lst |}) /\
		(t = (PAGE (mk_limits (mk_uN v_n) l))) /\
		(v_n = (List.length b_lst) / (64 * Ki)) /\
		List.Forall (fun (m : nat) => (v_n <= m <= 2 ^ 16)) (option_to_list v_m)
	) (store_MEMS s) mts.
Proof.
	move => s HSt.
	inversion HSt.
	eq_to_prop.
	rewrite H11 /store_MEMS.
	clear -H2.
	exists memtype_lst.
	
	move : meminst_lst H2.
	induction memtype_lst; move => meminst_lst HMok.
	{
		inversion HMok; subst; auto.
	}
	destruct meminst_lst; inversion HMok; subst; auto.
	econstructor.
	{
		inversion H2; subst; clear H2.
		inversion H; subst; clear H.
		inversion H6; subst; clear H6.
		destruct m_opt0; destruct m_opt; try discriminate.
		- injection H2 as ?; subst.
			simpl in H11.
			exists b_lst, v_n, (Some m0).
			eq_to_prop.
			split; auto.
			split; auto.
			split; auto.
			list_to_seq.
			rewrite H0.

			rewrite mulnE.
			rewrite Nat.div_mul; auto.
			rewrite /Ki -mulnE; discriminate.
		-
			exists b_lst, v_n, None.
			eq_to_prop.
			split; auto.
			split; auto.
			split; auto.
			list_to_seq.
			rewrite H0.

			rewrite mulnE.
			rewrite Nat.div_mul; auto.
			rewrite /Ki -mulnE; discriminate.
	}
	by eapply IHmemtype_lst.
Qed.

Lemma s_invert_tables: forall s,
	Store_ok s ->
	exists tbts,
	List.Forall2 (fun tb tbt =>
		exists ref_lst v_m rt,
		let l := option_map (fun m => mk_uN m) v_m in
		(tb = {| tableinst_TYPE := tbt;
			REFS := ref_lst |}) /\
		(tbt = (mk_tabletype
			(mk_limits (mk_uN (List.length ref_lst)) l) rt)) /\
		(Tabletype_ok tbt) /\
		List.Forall (fun (ref_lst : ref) => (Ref_ok s ref_lst rt)) (ref_lst)
	) (store_TABLES s) tbts.
Proof.
	move => s HSt.
	inversion HSt.
	eq_to_prop.

	rewrite {2}H11 /=.
	clear -H4.

	exists tabletype_lst.
	move : tableinst_lst H4.
	induction tabletype_lst; move => tableinst_lst HTok.
	{
		inversion HTok; subst; auto.
	}
	destruct tableinst_lst; inversion HTok; subst; auto.
	econstructor.
	{
		inversion H2; subst.
		eq_to_prop.
		exists ref_lst, m_opt, rt.
		split; eauto.
		split.
		- 
			list_to_seq.
			rewrite -H1.
			reflexivity.
		split; eauto.
	}
	by eapply IHtabletype_lst.
Qed.

Lemma se_invert_funcs: forall s s',
	Extend_store s s' ->
	holds_upto (λ a : nat, a < | store_FUNCS s |) (| store_FUNCS s |) ->
  holds_upto (λ a : nat, a < | store_FUNCS s' |) (| store_FUNCS s |) ->
	holds_upto (λ (a : nat), Extend_funcinst ((store_FUNCS s) [| a |]) ((store_FUNCS s') [| a |])) (|store_FUNCS s|).
Proof.
	move => s s' HSe.
	inversion HSe; subst.
	auto.
Qed.

Lemma se_invert_tables: forall s s',
  Extend_store s s' ->
  holds_upto (λ a : nat, a < | store_TABLES s |) (| store_TABLES s |) ->
  holds_upto (λ a : nat, a < | store_TABLES s' |) (| store_TABLES s |) ->
  holds_upto (λ a : nat, Extend_tableinst ((store_TABLES s) [|a|]) ((store_TABLES s') [|a|])) (| store_TABLES s |).
Proof.
	move => s s' HSe.
	inversion HSe; subst.
	auto.
Qed.

Lemma se_invert_mems: forall s s',
	Extend_store s s' ->
	holds_upto (λ a : nat, a < | store_MEMS s |) (| store_MEMS s |) ->
  holds_upto (λ a : nat, a < | store_MEMS s' |) (| store_MEMS s |) ->
  holds_upto (λ a : nat, Extend_meminst ((store_MEMS s) [|a|]) ((store_MEMS s') [|a|])) (| store_MEMS s |).
Proof.
	move => s s' HSe.
	inversion HSe; subst.
	auto.
Qed.

Lemma se_invert_store_globals: forall s s',
	Extend_store s s' ->
	holds_upto (λ a : nat, a < | store_GLOBALS s |) (| store_GLOBALS s |) ->
  holds_upto (λ a : nat, a < | store_GLOBALS s' |) (| store_GLOBALS s |) ->
  holds_upto (λ a : nat, Extend_globalinst ((store_GLOBALS s) [|a|]) ((store_GLOBALS s') [|a|])) (| store_GLOBALS s |).
Proof.
	move => s s' HSe.
	inversion HSe; subst.
	auto.
Qed.

Lemma se_invert_elems: forall s s',
  Extend_store s s' ->
  holds_upto (λ a : nat, a < | store_ELEMS s |) (| store_ELEMS s |) ->
  holds_upto (λ a : nat, a < | store_ELEMS s' |) (| store_ELEMS s |) ->
  holds_upto (λ a : nat, Extend_eleminst ((store_ELEMS s) [|a|]) ((store_ELEMS s') [|a|])) (| store_ELEMS s |).
Proof.
	move => s s' HSe.
	inversion HSe; subst.
	auto.
Qed.

Lemma se_invert_datas: forall s s',
  Extend_store s s' ->
  holds_upto (λ a : nat, a < | store_DATAS s |) (| store_DATAS s |) ->
  holds_upto (λ a : nat, a < | store_DATAS s' |) (| store_DATAS s |) ->
  holds_upto (λ a : nat, Extend_datainst ((store_DATAS s) [|a|]) ((store_DATAS s') [|a|])) (| store_DATAS s |).
Proof.
	move => s s' HSe.
	inversion HSe; subst.
	auto.
Qed.

Lemma limits_sub_refl: forall lim,
	wf_limits lim ->
	Limits_sub lim lim.
Proof.
	move=> lim HWf.
	destruct lim.
	destruct v_u32.
	destruct u32_opt.
	- destruct u.
	  rewrite -invert_opt_map_some.
	  apply max; eauto.
	  econstructor; eauto.
	- econstructor; eauto.
Qed.

Lemma limits_sub_trans: forall lim lim' lim'',
	Limits_sub lim lim' ->
	Limits_sub lim' lim'' ->
	Limits_sub lim lim''.
Proof.
	move=> lim lim' lim'' Hsub Hsub'.
	inversion Hsub; inversion Hsub'; clear Hsub; clear Hsub'; subst; try discriminate.
	- injection H9 as ?; subst.
	  econstructor; eauto.
		eapply leq_trans; eauto.
		destruct m_2_opt0; eauto.
		apply Forall_cons; eauto.
		destruct m_2_opt; try discriminate.
		simpl in H4.
		injection H4 as ?; subst.
		inversion H6; subst.
		inversion H0; subst.
		eapply leq_trans; eauto.
	-
		injection H8 as ?.
		rewrite H4.
		econstructor; eauto.
		eapply leq_trans; eauto.
		rewrite -H4.
		apply H7.
	-
		injection H7 as ?; subst.
		econstructor; eauto.
		eapply leq_trans; eauto.
Qed.

Lemma externtype_sub_refl: forall xt, 
	wf_externtype xt ->
	Externtype_sub xt xt.
Proof.
	move=> xt HWf.
	destruct xt; econstructor; eauto.
	- apply mk_Functype_sub.
	- apply mk_Globaltype_sub.
	- destruct v_tabletype. 
		inversion HWf; subst. 
		apply mk_Tabletype_sub; eauto. 
		inversion H0; subst.
		by apply limits_sub_refl.
	- destruct v_memtype.
		inversion HWf; subst.
		apply mk_Memtype_sub; eauto.
		inversion H0; subst.
		by apply limits_sub_refl.
Qed.

Lemma externtype_sub_trans: forall xt xt' xt'',
	Externtype_sub xt xt' ->
	Externtype_sub xt' xt'' ->
	Externtype_sub xt xt''.
Proof.
	move=> xt xt' xt'' Hsub Hsub'.
	inversion Hsub; inversion Hsub'; subst; try discriminate.
	- injection H7 as ?; subst.
		inversion H; subst.
		inversion H4; subst.
		exact Hsub.
	- injection H7 as ?; subst.
		inversion H; subst.
		inversion H4; subst.
		exact Hsub.
	-
		injection H7 as ?; subst.
		inversion H; subst.
		inversion H4; subst.
		econstructor; eauto.
		econstructor; eauto.
		eapply limits_sub_trans; eauto.
	-
		injection H7 as ?; subst.
		inversion H; subst.
		inversion H4; subst.
		econstructor; eauto.
		econstructor; eauto.
		eapply limits_sub_trans; eauto.
Qed.

Lemma externtype_global_eq: forall gt gt',
	Externtype_sub (GLOBAL gt) (GLOBAL gt') ->
	gt = gt'.
Proof.
	move=> gt gt' HSub.
	inversion HSub; subst.
	inversion H1; subst; eauto.
Qed.

Lemma externtype_func_eq: forall ft ft',
	Externtype_sub (FUNC ft) (FUNC ft') ->
	ft = ft'.
Proof.
	move=> ft ft' HSub.
	inversion HSub; subst.
	inversion H1; subst; eauto.
Qed.

Lemma minst_invert_functypes: forall v_S minst C C',
	Moduleinst_ok v_S minst C ->
	inst_match C C' ->
	(context_TYPES C') = (TYPES minst).
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; inversion Him; subst; auto.
Qed.

Lemma minst_invert_funcs: forall v_S minst C C',
	Moduleinst_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun fa ft => 
		exists minst1 v_func ft',
		(fa < (size (store_FUNCS v_S))) /\
		((lookup_total (store_FUNCS v_S) fa) =
			{| funcinst_TYPE := ft'; funcinst_MODULE := minst1; CODE := v_func |}) /\
	 	Externtype_sub (FUNC ft') (FUNC ft)
	) (FUNCS minst) (context_FUNCS C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H3 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H3; eauto.
	econstructor; eauto.
	
	clear -H.
	
	dependent induction H.
	-	eq_to_prop.
		destruct v_funcinst.
		repeat eexists; eauto.
		apply externtype_sub_refl; eauto.
	- 
		inversion H0; subst.
		specialize (IHExternaddr_ok _ _ erefl erefl) as [minst [v_func [ft' [? [? ?]]]]].
		exists minst, v_func, ft'.
		repeat split; eauto.
		eapply externtype_sub_trans; eauto.
Qed.

Lemma minst_invert_tables: forall v_S minst C C',
	Moduleinst_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun tba tbt => 
		exists tbr tbt',
		(tba < (size (store_TABLES v_S))) /\
		((lookup_total (store_TABLES v_S) tba) =
			{| tableinst_TYPE := tbt'; REFS := tbr |}) /\
		Externtype_sub (TABLE tbt') (TABLE tbt)
	) (TABLES minst) (context_TABLES C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H7 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H7; eauto.
	econstructor; eauto.
	clear -H.
	
	dependent induction H.
	-	eq_to_prop.
		destruct v_tableinst.
		exists REFS, tableinst_TYPE.
		repeat split; eauto.
		+ apply externtype_sub_refl; eauto.
	- 
		inversion H0; subst.
		specialize (IHExternaddr_ok _ _ erefl erefl) as [tbr [tbt' IH]].
		destruct IH as [? [? ?]].
		
		exists tbr, tbt'.
		repeat split; eauto.
		eapply externtype_sub_trans; eauto.
Qed.

Lemma minst_invert_globals: forall v_S minst C C',
	Moduleinst_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun ga gt => 
		exists gt' v_val,
		(ga < (size (store_GLOBALS v_S))) /\
		((lookup_total (store_GLOBALS v_S) ga) =
			{| globalinst_TYPE := gt'; VALUE := v_val |}) /\
		Externtype_sub (GLOBAL gt') (GLOBAL gt)
	) (GLOBALS minst) (context_GLOBALS C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H1 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H1; eauto.
	econstructor; eauto.

	clear -H.
	dependent induction H.
	-
		eq_to_prop.
		destruct v_globalinst.
		exists globalinst_TYPE, VALUE.
		repeat split; eauto.
		apply externtype_sub_refl; eauto.
	-
		inversion H0; subst.
		specialize (IHExternaddr_ok _ _ erefl erefl) as [gt' [v_val [? [? ?]]]].
		exists gt', v_val.
		repeat split; eauto.
		eapply externtype_sub_trans; eauto.
Qed.

Lemma minst_invert_mems: forall v_S minst C C',
	Moduleinst_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun ma mt => 
		exists v_mt b_lst,
		(ma < (size (store_MEMS v_S))) /\
		((lookup_total (store_MEMS v_S) ma) = {| meminst_TYPE := v_mt; BYTES := b_lst |}) /\
		((Externtype_sub (MEM v_mt) (MEM mt)))
	) (MEMS minst) (context_MEMS C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H5 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H5; eauto.
	econstructor; eauto.

	clear -H.
	dependent induction H.
	-
		eq_to_prop.
		destruct v_meminst.
		exists meminst_TYPE, BYTES.
		repeat split; eauto.
		by apply externtype_sub_refl.
	-
		inversion H0; subst.
		specialize (IHExternaddr_ok _ _ erefl erefl) as [v_mt [b_lst [? [? ?]]]].
		exists v_mt, b_lst.
		repeat split; eauto.
		eapply externtype_sub_trans; eauto.
Qed.

Lemma minst_invert_elems: forall v_S minst C C',
	Moduleinst_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun ea et => 
		exists ref_lst,
		(ea < (size (store_ELEMS v_S))) /\
		(List.Forall (fun (ref_lst : ref) => (Ref_ok v_S ref_lst et)) (ref_lst)) /\
		((lookup_total (store_ELEMS v_S) ea) = {| eleminst_TYPE := et; eleminst_REFS := ref_lst |})
	) (ELEMS minst) (context_ELEMS C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H13 H14 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.
	simpl.

	move : context_ELEMS H14.
	induction elemaddr_lst; move => context_ELEMS Heok. inversion Heok; subst; auto.
	destruct context_ELEMS. by inversion Heok.
	econstructor.
	{
		inversion Heok; subst.
		inversion H2; subst.
		inversion H13; subst.
		eexists ref_lst.
		split; auto.
	}
	eapply IHelemaddr_lst. by inversion H13.
	by inversion Heok.
Qed.

Lemma minst_invert_datas: forall v_S minst C C',
	Moduleinst_ok v_S minst C ->
	inst_match C C' ->
	((size (DATAS minst) = (size (context_DATAS C')))) /\
	List.Forall (fun da => 
		exists b_lst,
		(da < (size (store_DATAS v_S))) /\
		((lookup_total (store_DATAS v_S) da) = {| datainst_BYTES := b_lst |})
	) (DATAS minst).
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	split.
	{
		eq_to_prop; list_to_seq.
		by destruct v_C'; inversion Him; destruct_all; simpl in *; subst.
	}
	clear - H10 H11 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	dependent induction H11; eauto.
	econstructor; eauto.
	-
		inversion H10; subst.
		inversion H; subst.
		exists b_lst; eauto.
	-
		inversion H10; subst.
		eapply IHForall2; eauto.
Qed.

Ltac invert_funcs :=
	match goal with
	| H: Extend_store ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "Hleq" in
		let v2 := fresh "Hleq" in
		eapply se_invert_funcs in H'
			as [v1 v2]
	| _ : _ |- _ => idtac
	end.

Ltac invert_tables :=
	match goal with
	| H: Extend_store ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "Hleq" in
		let v2 := fresh "Hleq" in
		eapply se_invert_tables in H'
			as [v1 v2]
	| _ : _ |- _ => idtac
	end.

Ltac invert_mems :=
	match goal with
	| H: Extend_store ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "Hleq" in
		let v2 := fresh "Hleq" in
		eapply se_invert_mems in H'
			as [v1 v2]
	| _ : _ |- _ => idtac
	end.

Ltac invert_elems :=
	match goal with
	| H: Extend_store ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "Hleq" in
		let v2 := fresh "Hleq" in
		eapply se_invert_elems in H'
			as [v1 v2]
	| _ : _ |- _ => idtac
	end.

Ltac invert_datas :=
	match goal with
	| H: Extend_store ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "Hleq" in
		let v2 := fresh "Hleq" in
		eapply se_invert_datas in H'
			as [v1 v2]
	| _ : _ |- _ => idtac
	end.

Ltac invert_storeok H :=
  match type of H with
  | Store_ok ?s =>
		let HGLen    := fresh "HGLen" in
		let HGlobal  := fresh "HGlobal" in
		let HMLen    := fresh "HMLen" in
		let HMem     := fresh "HMem" in
		let HTLen    := fresh "HTLen" in
		let HTable   := fresh "HTable" in
		let HFLen    := fresh "HFLen" in
		let HFunc    := fresh "HFunc" in
		let HDLen    := fresh "HDLen" in
		let HData    := fresh "HData" in
		let HELen    := fresh "HELen" in
		let HElem    := fresh "HElem" in
		let HSeq     := fresh "HSeq" in
		let HWfStore := fresh "HWfStore" in
		let HWfMem   := fresh "HWfMem" in
		let HWfTable := fresh "HWfTable" in
		let HWfStore':= fresh "HWfStore" in
		inversion H as
			[ ? ? ? ? ? ? ? ? ? ? ? ? ?
				HGLen HGlobal HMLen HMem
				HTLen HTable HFLen HFunc
				HDLen HData HELen HElem
				HSeq
				HWfStore HWfMem HWfTable HWfStore'
			];
		eq_to_prop;
		subst
  end.

Ltac invert_moduleinstok H :=
  match type of H with
  | Moduleinst_ok ?s ?m ?C =>
		let HFunctypeOk      := fresh "HFunctypeOk" in
		let HGlobalLen       := fresh "HGlobalLen" in
		let HGlobal          := fresh "HGlobalExtOk" in
		let HFuncLen         := fresh "HFuncLen" in
		let HFunc            := fresh "HFunc" in
		let HMemLen          := fresh "HMemLen" in
		let HMem             := fresh "HMemExtOk" in
		let HTableLen        := fresh "HTableLen" in
		let HTable           := fresh "HTableExtOk" in
		let HExport          := fresh "HExport" in
		let HDataLen         := fresh "HDataLen" in
		let HDataBound       := fresh "HDataBound" in
		let HData            := fresh "HDataInstOk" in
		let HElemLen         := fresh "HElemLen" in
		let HElemBound       := fresh "HElemBound" in
		let HElem            := fresh "HElemInstOk" in
		let HDisjointExports := fresh "HDisjointExports" in
		let HAddrLen         := fresh "HAddrLen" in
		let HExportAddr      := fresh "HExportAddr" in
		let HWfStore         := fresh "HWfStore" in
		let HWfModuleinst    := fresh "HWfModuleinst" in
		let HWfContext       := fresh "HWfContext" in
		let HWfGlobalTypes   := fresh "HWfGlobalTypes" in
		let HWfFuncTypes     := fresh "HWfFuncTypes" in
		let HWfMemTypes      := fresh "HWfMemTypes" in
		let HWfTableTypes    := fresh "HWfTableTypes" in
		inversion H as
			[ ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?
				HFunctypeOk
				HGlobalLen HGlobal
				HFuncLen HFunc
				HMemLen HMem
				HTableLen HTable
				HExport
				HDataLen HDataBound HData
				HElemLen HElemBound HElem
				HDisjointExports
				HAddrLen
				HExportAddr
				HWfStore
				HWfModuleinst
				HWfContext
				HWfGlobalTypes
				HWfFuncTypes
				HWfMemTypes
				HWfTableTypes
			];
		eq_to_prop;
		subst
  end.

Ltac invert_extend_store H :=
  match type of H with
  | Extend_store ?s ?s' =>
      let HGlobalsBound      := fresh "HGlobalsBound" in
      let HGlobalsBound'     := fresh "HGlobalsBound'" in
      let HGlobalsExtend     := fresh "HGlobalsExtend" in

      let HMemsBound         := fresh "HMemsBound" in
      let HMemsBound'        := fresh "HMemsBound'" in
      let HMemsExtend        := fresh "HMemsExtend" in

      let HTablesBound       := fresh "HTablesBound" in
      let HTablesBound'      := fresh "HTablesBound'" in
      let HTablesExtend      := fresh "HTablesExtend" in

      let HFuncsBound        := fresh "HFuncsBound" in
      let HFuncsBound'       := fresh "HFuncsBound'" in
      let HFuncsExtend       := fresh "HFuncsExtend" in

      let HDatasBound        := fresh "HDatasBound" in
      let HDatasBound'       := fresh "HDatasBound'" in
      let HDatasExtend       := fresh "HDatasExtend" in

      let HElemsBound        := fresh "HElemsBound" in
      let HElemsBound'       := fresh "HElemsBound'" in
      let HElemsExtend       := fresh "HElemsExtend" in

      let HWfStore           := fresh "HWfStore" in
      let HWfStore'          := fresh "HWfStore'" in

      inversion H as
        [ ? ?
          HGlobalsBound
          HGlobalsBound'
          HGlobalsExtend

          HMemsBound
          HMemsBound'
          HMemsExtend

          HTablesBound
          HTablesBound'
          HTablesExtend

          HFuncsBound
          HFuncsBound'
          HFuncsExtend

          HDatasBound
          HDatasBound'
          HDatasExtend

          HElemsBound
          HElemsBound'
          HElemsExtend

          HWfStore
          HWfStore'
        ];
			eq_to_prop;
      subst
  end.

Lemma lookup_global: forall v_a v_C v_C' v_mut v_vt v_S minst,
	(v_a < (size (context_GLOBALS v_C'))) ->
	lookup_total (context_GLOBALS v_C') v_a = mk_globaltype v_mut v_vt ->
	Moduleinst_ok v_S minst v_C ->
	inst_match v_C v_C' ->
	Store_ok v_S ->
	(Val_ok v_S (VALUE (lookup_total 
		(store_GLOBALS v_S) (lookup_total (GLOBALS minst) v_a))) (v_vt : valtype)).
Proof.
	move => v_a v_C v_C' v_mut v_vt v_S minst HLength HLookup HMIT Him HST.

	invert_storeok HST.
	invert_moduleinstok HMIT.
	simpl in *; rewrite /lookup_total in HLookup.
	clear - HMIT HLength HLookup Him HGlobalExtOk HGlobal.
	eapply minst_invert_globals in HMIT; eauto.
	inversion Him; destruct_all; simpl in *; subst; clear Him.

	eapply Forall2_size2 in HMIT as [HLen HForall].
	eapply HForall in HLength as [gt' [v_val [HBound [HLookup' HSub]]]].
	eapply externtype_global_eq in HSub; subst.
	eapply Forall2_size in HGlobal as [HLen' HForall'].

	eapply HForall' in HBound as HGinstOk.
	inversion HGinstOk as [???? HGlobTyp HValok HWfStore HWfGlobInst HEq1 HEq2 HEq3]; eq_to_prop; subst.
	rewrite /lookup_total in HLookup'.
	rewrite HLookup' in HEq2.
	injection HEq2 as HEq2; subst.
	rewrite -HEq2 in HLookup.
	injection HLookup as ?; subst.
	rewrite /lookup_total.
	rewrite HLookup'.
	apply HValok.
Qed.

Lemma bt_inversion : forall v_S v_C v_C' r_v_f (b_lstt: blocktype) ts1 ts2 bt1 bt2,
	Moduleinst_ok v_S (frame_MODULE r_v_f) v_C ->
	Blocktype_ok v_C' b_lstt (ts1 :-> ts2) ->
	fun_blocktype (mk_state v_S r_v_f) b_lstt = (bt1 :-> bt2) ->
	inst_match v_C v_C' ->
	(ts1 = bt1 /\ ts2 = bt2).
Proof.
	move=> v_S v_C v_C' r_v_f b_lstt ts1 ts2 bt1 bt2 HM HB Hf Him.
	invert_moduleinstok HM.
	unfold inst_match in Him.
	simpl in *; subst.
	unfold fun_blocktype in Hf;
	destruct b_lstt.
	{
		destruct valtype_opt;
		inversion Hf; subst;
		inversion HB; subst; auto.
	}
	unfold fun_type in Hf.
	inversion HB; eq_to_prop; subst.
	destruct r_v_f; simpl in *; subst.
	decompH Him.
	rewrite H5 in Hf.
	injection Hf as ?; subst.
	eauto.
Qed.

Lemma tc_func_reference2: forall v_S v_C minst idx tf v_type,
  lookup_total (TYPES minst) idx = funcinst_TYPE v_type ->
  Moduleinst_ok v_S minst v_C ->
  lookup_total (context_TYPES v_C) idx = tf ->
  tf = funcinst_TYPE v_type.
Proof.
	move => v_S v_C minst idx tf v_type H HMinst H1.
	inversion HMinst. subst. simpl in *. auto.
Qed.


Lemma store_typed_exterval_types: forall v_S v_f v_a,
	v_a < size (store_FUNCS v_S) ->
	lookup_total (store_FUNCS v_S) v_a = v_f ->
	Store_ok v_S ->
	Externaddr_ok v_S (externaddr_FUNC v_a) (FUNC (funcinst_TYPE v_f)).
Proof.
	move => v_S v_f v_a HLength H HST.
	(* inversion HST; eq_to_prop; subst; simpl in *. *)
	invert_storeok HST.
	
	apply Forall2_size in HFunc; destruct HFunc as [HFLen' HForall].
	apply HForall in HLength as HFunc.
	inversion HFunc; subst.
	rewrite /lookup_total.
	rewrite -H.
	eapply Externaddr_ok__func; eq_to_prop; eauto.
	econstructor.
Qed.

Lemma global_extension_refl_0: forall g,
	wf_globalinst g ->
	Extend_globalinst g g.
Proof.
	move => g HWf.
	destruct g.
	destruct globalinst_TYPE.
	econstructor; eauto.
	eq_to_prop.
	by right.
Qed.

Lemma extend_meminst_refl_0: forall m,
	wf_meminst m ->
	Extend_meminst m m.
Proof.
	move => m HWf.
	destruct m.
	destruct meminst_TYPE.
	destruct v_limits.
	destruct v_u32.
	destruct u32_opt.
	- destruct u.
		rewrite -invert_opt_map_some.
		econstructor; eauto.
	- erewrite <- invert_opt_map_none.
		econstructor; eauto.
Qed.

Lemma extend_tableinst_refl_0: forall t,
	wf_tableinst t ->
	Extend_tableinst t t.
Proof.
	move => t HWf.
	destruct t.
	destruct tableinst_TYPE.
	destruct v_limits.
	destruct v_u32.
	destruct u32_opt.
	- destruct u.
		rewrite -invert_opt_map_some.
		econstructor; eauto.
	- erewrite <- invert_opt_map_none.
		econstructor; eauto.
Qed.

Lemma extend_eleminst_refl_0: forall g,
	Extend_eleminst g g.
Proof.
	move => g.
	destruct g.
	econstructor.
	eq_to_prop.
	by left.
Qed.

Lemma extend_datainst_refl_0: forall d,
	wf_datainst d ->
	Extend_datainst d d.
Proof.
	move => d HWf.
	destruct d.
	econstructor; eauto.
	eq_to_prop.
	by left.
Qed.


(* Lemma Extend_funcinst_refl0: forall f,
	wf_funcinst f ->
	Extend_funcinst f f.
Proof.
	move => f ?.
	destruct f.
	econstructor; eauto.
Qed.

Lemma Extend_funcinst_refl: forall f,
	Forall2 (fun v s => Extend_funcinst v s) f f.
Proof.
	move => f.
	induction f => //.
	apply Forall2_cons_iff. split.
	- econstructor.
	- apply IHf.
Qed.

Lemma table_extension_refl0: forall t,
	Extend_tableinst t t.
Proof.
	move => t.
	destruct t => //.
	destruct tableinst_TYPE, v_limits.
	assert (exists n, option_map (mk_uN) n = u32_opt).
	{
		destruct u32_opt.
		- destruct u. exists (Some i); eauto.
		- exists None; eauto.
	}
	destruct H as [n H]; subst.
	econstructor.
	auto.
Qed.

Lemma table_extension_refl: forall t,
	Forall2 (fun v s => Extend_tableinst v s) t t.
Proof.
	move => t.
	induction t => //.
	apply Forall2_cons_iff. split.
	- eapply table_extension_refl0.
	- apply IHt.
Qed.



Lemma Extend_meminst_refl: forall m,
	Forall2 (fun v s => Extend_meminst v s) m m.
Proof.
	move => m.
	induction m => //.
	apply Forall2_cons_iff. split.
	- by eapply Extend_meminst_refl0.
	- apply IHm.
Qed.


Lemma global_extension_refl: forall g,
	Forall2 (fun v s => Extend_globalinst v s) g g.
Proof.
	move => g.
	induction g.
	- econstructor.
	- econstructor.
	  + destruct a.
	    destruct globalinst_TYPE.
	  	econstructor.
			eq_to_prop.
			by right.
	  + by eapply IHg.
Qed.



Lemma elem_extension_refl: forall g,
	Forall2 (fun v s => Extend_eleminst v s) g g.
Proof.
	move => g.
	induction g.
	- econstructor.
	- econstructor.
	  + by eapply elem_extension_refl0.
	  + by eapply IHg.
Qed.

Lemma data_extension_refl0: forall d,
	Extend_datainst d d.
Proof.
	move => g.
	destruct g.
	econstructor.
	eq_to_prop.
	by left.
Qed.

Lemma data_extension_refl: forall d,
	Forall2 (fun v s => Extend_datainst v s) d d.
Proof.
	move => g.
	induction g.
	- econstructor.
	- econstructor.
	  + by eapply data_extension_refl0.
	  + by eapply IHg.
Qed. *)

(* Lemma Extend_store_refl: forall s,
    Extend_store s s.
Proof.
  move => s.
  eapply (mk_Extend_store s s
  (store_FUNCS s) (store_GLOBALS s) (store_TABLES s) (store_MEMS s)  (store_ELEMS s) (store_DATAS s)
  (store_FUNCS s) [] (store_GLOBALS s) [] (store_TABLES s) [] (store_MEMS s) []  (store_ELEMS s) [] (store_DATAS s) [] ); eauto;
  repeat (try by rewrite -> cats0).
	all: eq_to_prop.
	+ destruct s; eauto.
	+ repeat rewrite -> cats0. destruct s; eauto.
  + by apply Extend_funcinst_refl.
  + by apply table_extension_refl.
  + by apply Extend_meminst_refl.
  + by apply global_extension_refl.
  + by apply elem_extension_refl.
  + by apply data_extension_refl.
Qed. *)

(* Lemma holds_upto_test: forall (n : nat) (f : nat -> Prop),
	holds_upto (fun i => i < n) n ->
	n != 0.
Proof.
	move=> 

Lemma holds_uptol: forall (n : nat) (f : nat -> Prop),
	holds_upto f n ->
	(exists n', f n').
Proof.
	move=> n f Hholds.
	unfold holds_upto in Hholds.
	induction n.
	-
		unfold holds_upto in Hholds. simpl in Hholds. *)


Lemma holds_upto_lookup: forall (n : nat) (f : nat -> Prop) (i : nat),
	i < n ->
	holds_upto f n ->
	f i.
Proof.
	move=> n f i HBound HHolds.
	unfold holds_upto in HHolds.
	eapply Forall_size with (i := i) in HHolds; eauto.
	-
		apply nth_iota with (p := 0) (m := 0) in HBound as Hnth.
		rewrite Hnth in HHolds.
		apply HHolds.
	- rewrite size_iota; eauto.
Qed.


(* Lemma holds_upto_lt : forall (n n' : nat),
	n != 0 ->
	holds_upto (fun k => k < n') n ->
	n < n'.
Proof.
  move=> n n' Hzero H.
  rewrite /holds_upto in H.


	induction n; eauto.


Qed. *)

Lemma Externaddr_invert_funcs: forall s exta ext,
	Externaddr_ok s (externaddr_FUNC exta) (FUNC ext) ->
	exists xt v_funcinst,
	(exta < (|(store_FUNCS s)|))%N /\
	(((store_FUNCS s)[| exta |]) == v_funcinst) /\
	(xt = (FUNC (funcinst_TYPE v_funcinst))) /\
	(wf_externtype (FUNC (funcinst_TYPE v_funcinst))) /\
	Externtype_sub xt (FUNC ext).
Proof.
	move=> s exta ext HExt.
	dependent induction HExt; eq_to_prop.
	- exists (FUNC (funcinst_TYPE v_funcinst)), ((store_FUNCS s) [| exta |]).
		subst.
		repeat split; eauto.
		apply externtype_sub_refl; eauto.
	-
		inversion H; subst.
		specialize (IHHExt _ _ erefl erefl) as [xt [v_funcinst [? [? [? [? ?]]]]]].
		exists xt, v_funcinst.
		repeat split; eauto.
		eapply externtype_sub_trans; eauto.
Qed.

Lemma Externaddr_invert_tables: forall s exta ext,
	Externaddr_ok s (externaddr_TABLE exta) (TABLE ext) ->
	exists xt v_tableinst,
	(exta < (|(store_TABLES s)|))%N /\
	(((store_TABLES s)[| exta |]) == v_tableinst) /\
	(xt = (TABLE (tableinst_TYPE v_tableinst))) /\
	(wf_externtype (TABLE (tableinst_TYPE v_tableinst))) /\
	Externtype_sub xt (TABLE ext).
Proof.
	move=> s exta ext HExt.
	dependent induction HExt; eq_to_prop.
	- exists (TABLE (tableinst_TYPE v_tableinst)), ((store_TABLES s) [| exta |]).
		subst.
		repeat split; eauto.
		apply externtype_sub_refl; eauto.
	-
		inversion H; subst.
		specialize (IHHExt _ _ erefl erefl) as [xt [v_funcinst [? [? [? [? ?]]]]]].
		exists xt, v_funcinst.
		repeat split; eauto.
		eapply externtype_sub_trans; eauto.
Qed.

Lemma Externaddr_invert_mems: forall s exta ext,
	Externaddr_ok s (externaddr_MEM exta) (MEM ext) ->
	exists xt v_meminst,
	(exta < (|(store_MEMS s)|))%N /\
	(((store_MEMS s)[| exta |]) == v_meminst) /\
	(xt = (MEM (meminst_TYPE v_meminst))) /\
	(wf_externtype (MEM (meminst_TYPE v_meminst))) /\
	Externtype_sub xt (MEM ext).
Proof.
	move=> s exta ext HExt.
	dependent induction HExt; eq_to_prop.
	- exists (MEM (meminst_TYPE v_meminst)), ((store_MEMS s) [| exta |]).
		subst.
		repeat split; eauto.
		apply externtype_sub_refl; eauto.
	-
		inversion H; subst.
		specialize (IHHExt _ _ erefl erefl) as [xt [v_funcinst [? [? [? [? ?]]]]]].
		exists xt, v_funcinst.
		repeat split; eauto.
		eapply externtype_sub_trans; eauto.
Qed.

Lemma Externaddr_invert_globals: forall s exta ext,
	Externaddr_ok s (externaddr_GLOBAL exta) (GLOBAL ext) ->
	exists xt v_globalinst,
	(exta < (|(store_GLOBALS s)|))%N /\
	(((store_GLOBALS s)[| exta |]) == v_globalinst) /\
	(xt = (GLOBAL (globalinst_TYPE v_globalinst))) /\
	(wf_externtype (GLOBAL (globalinst_TYPE v_globalinst))) /\
	Externtype_sub xt (GLOBAL ext).
Proof.
	move=> s exta ext HExt.
	dependent induction HExt; eq_to_prop.
	- exists (GLOBAL (globalinst_TYPE v_globalinst)), ((store_GLOBALS s) [| exta |]).
		subst.
		repeat split; eauto.
		apply externtype_sub_refl; eauto.
	-
		inversion H; subst.
		specialize (IHHExt _ _ erefl erefl) as [xt [v_funcinst [? [? [? [? ?]]]]]].
		exists xt, v_funcinst.
		repeat split; eauto.
		eapply externtype_sub_trans; eauto.
Qed.
	
Lemma Extend_store_ref: forall v_S v_S' v_t v_val,
	Extend_store v_S v_S' ->
	Ref_ok v_S v_val v_t ->
	Ref_ok v_S' v_val v_t.
Proof.
	move => v_S v_S' v_t v_val Hs Hv1.
	invert_extend_store Hs.
	clear - Hv1 HFuncsBound HFuncsBound' HFuncsExtend HWfStore'.
	inversion Hv1; subst.
	- econstructor; eauto.
	- econstructor; eauto.
		apply Externaddr_invert_funcs in H; destruct H as [xt [funcinst [HABound [Heq [HWfStore [HWfExt HExtSub]]]]]]; 
		eq_to_prop; subst.
		inversion HExtSub; subst.
		apply externtype_func_eq in HExtSub; subst.
		+ 
			eapply (holds_upto_lookup _ _ _ HABound) in HFuncsExtend. simpl in HFuncsExtend.
			eapply (holds_upto_lookup _ _ _ HABound) in HFuncsBound'. simpl in HFuncsBound'.
			inversion HFuncsExtend; subst; eauto.
			econstructor; eq_to_prop; eauto.  
			unfold holds_upto in HFuncsExtend.
			rewrite -H in H1.
			apply H1.
	- econstructor; eauto.
Qed.

Lemma Extend_store_refs: forall v_S v_S' v_ts v_vals,
	Extend_store v_S v_S' ->
	List.Forall2 (fun v_t v_val => Ref_ok v_S v_val v_t) (v_ts) (v_vals) ->
	List.Forall2 (fun v_t v_val => Ref_ok v_S' v_val v_t) (v_ts) (v_vals).
Proof.
	move => v_S v_S' v_t v_val Hs Hv1.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply Extend_store_ref; eauto.
Qed.

Lemma Extend_store_refs': forall v_S v_S' v_t v_refs,
	Extend_store v_S v_S' ->
	List.Forall (fun v_ref => Ref_ok v_S v_ref v_t) v_refs ->
	List.Forall (fun v_ref => Ref_ok v_S' v_ref v_t) v_refs.
Proof.
	move => v_S v_S' v_t v_refs Hs Hv1.
	eapply List.Forall_impl.
	2: eauto.
	move => t v.
	simpl in v.
	eapply Extend_store_ref; eauto.
Qed.

Lemma Extend_store_val: forall v_S v_S' v_t v_val,
	Extend_store v_S v_S' ->
	Val_ok v_S v_val v_t ->
	Val_ok v_S' v_val v_t.
Proof.
	move => v_S v_S' v_t v_val Hs Hv1.
	invert_extend_store Hs.
	clear - Hs Hv1 HFuncsBound HFuncsBound' HFuncsExtend HWfStore'.

	inversion Hv1; subst; try by constructor.
	econstructor; eauto.
	eapply Extend_store_ref; eauto.
Qed.

Lemma Extend_store_vals: forall v_S v_S' v_t v_val,
	Extend_store v_S v_S' ->
	Vals_ok v_S v_val v_t ->
	Vals_ok v_S' v_val v_t.
Proof.
	rewrite /Vals_ok.
	move => v_S v_S' v_t v_val Hs Hv1.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply Extend_store_val; eauto.
Qed.

Lemma config_same: forall s f ais s' f' ais',
	(mk_config (mk_state s f) ais) = (mk_config (mk_state s' f') ais') ->
	s = s' /\ f = f' /\ ais = ais'.
Proof.
	move => s f ais s' f' ais' H.
	injection H as H1 => //=.
Qed.

Lemma config_same2: forall s f ais s' f' ais',
	s = s' /\ f = f' /\ ais = ais' ->
 	(mk_config (mk_state s f) ais) = (mk_config (mk_state s' f') ais').
Proof.
	move => s f ais s' f' ais' [? [? ?]].
	f_equal => //=. f_equal => //=.
Qed.

Lemma iota_snoc (start n : nat) :
  iota start (S n) = iota start n ++ [start + n].
Proof.
  move: start.
  induction n as [ |n IH]; move=> start; simpl.
  - by rewrite addn0.
  -
    replace (start + S n) with (S start + n).
		rewrite -IH.
    + reflexivity.
    + rewrite addnS.
		 	rewrite addSn.
			reflexivity.
Qed.

Lemma holds_upto_S (P : nat -> Prop) (n : nat) :
  holds_upto P (S n) <->
  holds_upto P n /\ P n.
Proof.
  unfold holds_upto.
  rewrite iota_snoc.
  rewrite Forall_app.
	rewrite add0n.
	
  split; move=> H; destruct H; eauto.
	inversion H0; subst; eauto.
Qed.

Theorem holds_upto_all
  (P : nat -> Prop)
  (H0 : P 0)
  (HS : forall n, P n -> P (S n)) :
  forall n, holds_upto P n.
Proof.
  intro n.

  enough (holds_upto P n /\ P n) as [H _].
  { exact H. }

  induction n as [ |n [Hupto HPn]].
  - split.
    + unfold holds_upto.
      simpl.
      constructor.
    + exact H0.

  - split.
    + apply holds_upto_S.
      split.
      * exact Hupto.
      * exact HPn.
    + apply HS.
      exact HPn.
Qed.

Theorem holds_upto_all_strong
	(P : nat -> Prop)
	(Hstep : forall n, holds_upto P n -> P n) :
  forall n, holds_upto P n.
Proof.
  induction n as [ |n IH].
  - unfold holds_upto.
    simpl.
    constructor.
  - apply holds_upto_S.
    split.
    + exact IH.
    + apply Hstep.
      exact IH.
Qed.

Theorem holds_upto_all_strong'
	(P : nat -> Prop)
	(m : nat)
	(Hstep : forall n, holds_upto P n -> n < m -> P n) :
  holds_upto P m.
Proof.
  induction m as [ | m IH].
  - unfold holds_upto.
    simpl.
    constructor.
  - apply holds_upto_S.
    split.
    + eapply IH. move=> n H' H''. apply Hstep; eauto.
    + apply Hstep.
      eapply IH. move=> n H' H''. eapply Hstep; eauto.
			eauto.
Qed.


Lemma holds_upto_lt: forall (n : nat) (n' : nat),
	holds_upto (fun k => k < n') n ->
	n <= n'.
Proof.
	move=> n n' HHolds.
	destruct n; eauto.
	rewrite holds_upto_S in HHolds; destruct HHolds; eauto.
Qed.

Lemma list_update_func_subst: forall {X : Type} {Y : Inhabited X} (l: list X) e i f,
	i < | l | ->
	(l [| i |]) = e ->
  ((list_update_func l i f) [| i |]) = f e.
Proof.
	move=> X Y l e i f HBound H.
	move: i HBound H.
	induction l; try discriminate.
	move=> i HBound H.
	destruct i.
	- by rewrite -H.
	- simpl. by rewrite IHl.
Qed.

Lemma list_update_func_unchanged: forall {X : Type} {Y : Inhabited X} (l: list X) e i n f,
	i < | l | ->
	n < | l | ->
	i != n ->
	(l [| n |]) = e ->
  ((list_update_func l i f) [| n |]) = e.
Proof.
	move=> X Y l e i n f HBound HBound' Hneq H.
	move: n i HBound HBound' H Hneq.
	induction l; try discriminate.
	move=> n i HBound HBound' H Hneq.
	destruct i; destruct n; try discriminate.
	-  by rewrite -H.
	- by rewrite -H.
	- simpl. by rewrite IHl.
Qed.

Lemma global_set_global_extension: forall v_g v_g' v_idx v_valtype v_val_0 v_val_1,
	Forall wf_globalinst v_g ->
	wf_val v_val_1 ->
	(v_idx < size v_g) ->
	lookup_total v_g v_idx = 
		{| globalinst_TYPE := mk_globaltype (Some MUT) v_valtype; VALUE := v_val_0 |} ->
	v_g' = (list_update_func v_g v_idx (fun g => g <| VALUE := v_val_1 |> )) ->
	holds_upto (fun a => Extend_globalinst (v_g [|a|]) (v_g' [|a|])) (|v_g|).
Proof.
	move => v_g v_g' v_i v_valtype v_val_0 v_val_1 HWfglob HWfval' HLength HLookup Heq.

	eapply holds_upto_all_strong'.
	move => n HHolds HBound.
	case E: (v_i == n).
	- move/eqP in E; subst.
		rewrite HLookup.
		eapply Forall_size in HWfglob; eauto.
		eapply list_update_func_subst with (f := [eta set VALUE (fun=> v_val_1)]) in HLookup as H; eauto.
		rewrite H.
		simpl.
		econstructor; eauto.
		- rewrite /lookup_total in HLookup. rewrite HLookup in HWfglob. exact HWfglob.
		- econstructor; eauto.
	- 
		remember (v_g [|n|]) as e.
		symmetry in Heqe.
		-
			eapply list_update_func_unchanged with (i := v_i) (f := [eta set VALUE (fun=> v_val_1)]) in Heqe as HLookup'; eauto; subst.
			rewrite HLookup'.
			apply global_extension_refl_0.
			eapply Forall_size in HWfglob; eauto.
		- apply/eqP.
			move/eqP in E.
			eauto.
Qed.

Lemma forall_preserved_bytes: forall lst i j bytes,
	Forall wf_byte bytes ->
	Forall wf_byte lst ->
	Forall wf_byte (list_slice_update lst i j bytes).
Proof.
	move=> lst i j bytes HWfbytes HWflst.
	move: i j bytes HWfbytes.
	induction lst; auto.
	move=> i j bytes HWfbytes.
	inversion HWflst; subst.
	specialize (IHlst H2).
	destruct i; destruct bytes; destruct j; simpl; econstructor; eauto.
	- inversion HWfbytes; subst; eauto.
	- eapply IHlst. inversion HWfbytes; eauto.
Qed.

Lemma store_none_mem_extension: forall v_ms v_ms' v_idx v_mt b_lst v_l v_n v_nb,
	Forall wf_byte v_nb ->
	Forall wf_meminst v_ms -> 
	(v_idx < size v_ms) ->
	lookup_total v_ms v_idx = {| meminst_TYPE := v_mt; BYTES := b_lst |} ->
	v_ms' = (list_update_func v_ms v_idx
		(λ m, m <| BYTES :=
		list_slice_update (BYTES m) v_l v_n v_nb |>)) ->
	holds_upto (λ v, Extend_meminst (v_ms [| v |]) (v_ms' [| v |])) (|v_ms|).
Proof.
	move => v_ms v_ms' v_idx v_mt b_lst v_l v_n v_nb HWfbytes HWfmem HLength HLookup HEq.
	eapply holds_upto_all_strong'.
	move=> n HHolds HBound.
	case E: (v_idx == n).
	- move/eqP in E; subst.
		rewrite HLookup.
		eapply Forall_size in HWfmem; eauto.
		rewrite /lookup_total in HLookup.
		rewrite HLookup in HWfmem.
		eapply list_update_func_subst with (f := (λ m : meminst, m <| BYTES := list_slice_update (BYTES m) v_l v_n v_nb |>)) in HLookup as H; eauto.
		rewrite H.
		simpl.
		destruct v_mt.
		destruct v_limits.
		destruct v_u32.
		destruct u32_opt.
		+ destruct u.
		  rewrite -invert_opt_map_some.
			econstructor; eauto.
			- rewrite list_slice_update_length. eauto.
			- inversion HWfmem; subst.
				econstructor; eauto.
				eapply forall_preserved_bytes; eauto.
		+ erewrite <- invert_opt_map_none; eauto.
			econstructor; eauto.
			- rewrite list_slice_update_length. eauto.
			- inversion HWfmem; subst.
				econstructor; eauto.
				eapply forall_preserved_bytes; eauto.  
	- remember (v_ms [|n|]) as e.
		symmetry in Heqe.
		-
			eapply list_update_func_unchanged with (i := v_idx) (f := (λ m : meminst, m <| BYTES := list_slice_update (BYTES m) v_l v_n v_nb |>)) in Heqe as HLookup'; eauto; subst.
			rewrite HLookup'.
			apply extend_meminst_refl_0; eauto.
			eapply Forall_size in HWfmem; eauto.
		- apply/eqP.
			move/eqP in E.
			eauto.
Qed.

Lemma invert_meminst: forall v_i v_j_opt v_b,
	wf_meminst {| meminst_TYPE := PAGE (mk_limits v_i v_j_opt); BYTES := v_b |} ->
	wf_uN 32 v_i /\ 
	Forall (fun v_j => wf_uN 32 v_j) v_j_opt /\
	Forall (wf_byte) v_b.
Proof.
	move=> v_i v_j_opt v_b Hwf.
	inversion Hwf; subst.
	inversion H1; subst.
	inversion H0; subst; eauto.
Qed. 

Lemma repeat_forall: forall (A : Type) P (k : A) n,
	P k ->
	Forall P (repeat k n).
Proof.
	move=> A P k n HP.
	induction n; eauto.
	apply Forall_cons; eauto.
Qed.

Lemma memory_grow_mem_extension: forall v_ms v_ms' v_idx b_lst v_i v_n v_j_opt,
	Forall wf_meminst v_ms ->
	Forall wf_meminst v_ms' ->
	(v_idx < size v_ms) ->
	lookup_total v_ms v_idx = {| meminst_TYPE := PAGE (mk_limits
				(mk_uN v_i)
				(v_j_opt)); BYTES := b_lst |} ->
	Forall (fun v_j => v_i + v_n <= proj_uN_0 v_j) v_j_opt ->
	v_ms' = (list_update_func v_ms v_idx
			(fun=> {|
			meminst_TYPE := PAGE (mk_limits
				(mk_uN (v_i + v_n)) (v_j_opt));
			BYTES := b_lst ++ repeat (mk_byte 0) (v_n * (64 * Ki))
		|})) ->
	holds_upto (λ v, Extend_meminst (v_ms [| v |]) (v_ms' [| v |])) (|v_ms|).
Proof.
	move=> v_ms v_ms' v_idx b_lst v_i v_n v_j_opt HWfmem HWfmem' HLength HLookup HLimit HEq.
	eapply holds_upto_all_strong'.
	move=> n HHolds HBound.
	case E: (v_idx == n).
	- move/eqP in E; subst.
		rewrite HLookup.
		eapply Forall_size in HWfmem; eauto.
		eapply Forall_size with (i := n) in HWfmem'.
		rewrite /lookup_total in HLookup.
		rewrite HLookup in HWfmem.
		eapply list_update_func_subst with (f := (fun=> {|
			meminst_TYPE := PAGE (mk_limits
				(mk_uN (v_i + v_n)) (v_j_opt));
			BYTES := b_lst ++ repeat (mk_byte 0) (v_n * (64 * Ki))
		|})) in HLookup as H; eauto.
		rewrite H.
		rewrite /lookup_total in H.
		rewrite H in HWfmem'.
		destruct v_j_opt.
		+ destruct u.
		  rewrite -invert_opt_map_some.
			econstructor; eauto.
			- apply leq_addr.
			- rewrite size_cat. apply leq_addr.
		+ erewrite <- invert_opt_map_none; eauto.
			econstructor; eauto.
			- apply leq_addr.
			- rewrite size_cat. apply leq_addr.
			- by rewrite list_update_length_func.
	- remember (v_ms [|n|]) as e.
		symmetry in Heqe.
		eapply list_update_func_unchanged with (i := v_idx) (f := (fun=> {|
			meminst_TYPE := PAGE (mk_limits
				(mk_uN (v_i + v_n)) (v_j_opt));
			BYTES := b_lst ++ repeat (mk_byte 0) (v_n * (64 * Ki))
		  |})) in Heqe as HLookup'; eauto; subst.
		-	
			rewrite HLookup'.
			apply extend_meminst_refl_0; eauto.
			eapply Forall_size in HWfmem; eauto.
		- apply/eqP.
			move/eqP in E.
			eauto.
Qed.

Lemma table_set_table_extension: forall v_tbs v_tbs' v_idx tbt tbr v_i v_tbr,
	Forall wf_tableinst v_tbs ->
	(v_idx < size v_tbs) ->
	lookup_total v_tbs v_idx = 
		{| tableinst_TYPE := tbt; REFS := tbr |} ->
	v_tbs' = (list_update_func v_tbs v_idx
			(fun tb => tb <| REFS :=
				list_update_func (REFS tb) v_i (fun=> v_tbr) |> )) ->
	holds_upto (fun v => Extend_tableinst (v_tbs [| v |]) (v_tbs' [| v |])) (|v_tbs|).
Proof.
	move => v_tbs v_tbs' v_idx tbt tbr v_i v_tbr HWftab HLength HLookup Heq.
	eapply holds_upto_all_strong'.
	move=> n HHolds HBound.
	case E: (v_idx == n).
	- move/eqP in E; subst.
		rewrite HLookup.
		eapply Forall_size in HWftab; eauto.
		eapply list_update_func_subst with (f := 
			(fun tb => tb <| REFS :=
				list_update_func (REFS tb) v_i (fun=> v_tbr) |> 
		)) in HLookup as H; eauto.
		rewrite H.
		rewrite /lookup_total in HLookup.
		rewrite HLookup in HWftab.

		destruct tbt.
		destruct v_limits.
		destruct v_u32.
		destruct u32_opt.
		- destruct u.
			rewrite -invert_opt_map_some.
			econstructor; eauto.
			- by rewrite list_update_length_func.
			- econstructor. inversion HWftab; subst; eauto.
		- erewrite <- invert_opt_map_none; eauto.
			econstructor; eauto.
			- by rewrite list_update_length_func.
			- econstructor. inversion HWftab; subst; eauto.
	- remember (v_tbs [|n|]) as e.
		symmetry in Heqe.
		eapply list_update_func_unchanged with (i := v_idx) (f :=
			(fun tb => tb <| REFS :=
				list_update_func (REFS tb) v_i (fun=> v_tbr) |> 
		)) in Heqe as HLookup'; eauto; subst.
		- rewrite HLookup'.
			eapply extend_tableinst_refl_0.
			eapply Forall_size in HWftab; eauto.
		- apply/eqP.
			move/eqP in E.
			eauto.
Qed.

Lemma table_grow_table_extension: forall v_tbs v_tbs' v_idx j ref rt v_n tbr,
	Forall wf_tableinst v_tbs ->
	Forall wf_tableinst v_tbs' ->
	(v_idx < length v_tbs) ->
	lookup_total v_tbs v_idx = 
		{| tableinst_TYPE := mk_tabletype (mk_limits
					(mk_uN (size tbr) ) j) rt;
		REFS := tbr |} ->
	v_tbs' = (list_update_func v_tbs	v_idx
			(fun=> {|
				tableinst_TYPE := mk_tabletype (mk_limits
					(mk_uN (size tbr + v_n)) j) rt;
				REFS := tbr ++ repeat ref v_n
		|})) ->
	holds_upto (fun v => Extend_tableinst (v_tbs [| v |]) (v_tbs' [| v |])) (|v_tbs|).
Proof.
	move => v_tbs v_tbs' v_idx j ref rt v_n tbr HWftab HWftab' HLength HLookup Heq.
	eapply holds_upto_all_strong'.
	move=> n HHolds HBound.
	case E: (v_idx == n).
	- move/eqP in E; subst.
		rewrite HLookup.
		eapply Forall_size in HWftab; eauto.
		eapply Forall_size with (i := n) in HWftab'; eauto.
		eapply list_update_func_subst with (f := 
			(fun=> {|
				tableinst_TYPE := mk_tabletype (mk_limits
					(mk_uN (size tbr + v_n)) j) rt;
				REFS := tbr ++ repeat ref v_n
		|})) in HLookup as H; eauto.
		rewrite H.
		rewrite /lookup_total in HLookup.
		rewrite /lookup_total in H.

		rewrite HLookup in HWftab.
		rewrite H in HWftab'.

		destruct j.
		- destruct u.
			rewrite -invert_opt_map_some.
			econstructor; eauto.
			- apply leq_addr.
			- rewrite size_cat. apply leq_addr.
		- erewrite <- invert_opt_map_none; eauto.
			econstructor; eauto.
			- apply leq_addr.
			- rewrite size_cat. apply leq_addr.
			- by rewrite list_update_length_func.
	- remember (v_tbs [|n|]) as e.
		symmetry in Heqe.
		eapply list_update_func_unchanged with (i := v_idx) (f :=
			(fun=> {|
				tableinst_TYPE := mk_tabletype (mk_limits
					(mk_uN (size tbr + v_n)) j) rt;
				REFS := tbr ++ repeat ref v_n
		|})) in Heqe as HLookup'; eauto; subst.
		- rewrite HLookup'.
			eapply extend_tableinst_refl_0.
			eapply Forall_size in HWftab; eauto.
		- apply/eqP.
			move/eqP in E.
			eauto.
Qed.

Lemma elem_drop_elem_extension: forall es es' idx,
	(idx < size es) ->
	es' = (list_update_func es idx
			[eta set eleminst_REFS (fun=> [])]) ->
	holds_upto (λ v , Extend_eleminst (es [| v |]) (es' [| v |])) (|es|).
Proof.
	move => es es' idx HLength Heq.
	eapply holds_upto_all_strong'.
	move=> n HHolds HBound.
	case E: (idx == n).
	- move/eqP in E; subst.
	  remember (es [| n |]) as e.
		symmetry in Heqe.
		eapply list_update_func_subst with (f := 
			[eta set eleminst_REFS (fun=> [])]
		) in Heqe as H; eauto.
		rewrite H.
		destruct e. simpl.
		econstructor.
		apply/orP.
		by right.
	- remember (es [|n|]) as e.
		symmetry in Heqe.
		eapply list_update_func_unchanged with (i := idx) (f :=
			[eta set eleminst_REFS (fun=> [])]
		) in Heqe as HLookup'; eauto; subst.
		+ rewrite HLookup'.
			eapply extend_eleminst_refl_0; eauto.
		+ apply/eqP.
			move/eqP in E.
			eauto.
Qed.

Lemma data_drop_data_extension: forall ds ds' idx,
	Forall wf_datainst ds ->
	(idx < size ds) ->
	ds' = (list_update_func ds idx [eta set datainst_BYTES (fun=> [])]) ->
	holds_upto (λ v , Extend_datainst (ds [| v |]) (ds' [| v |])) (|ds|).
Proof.
	move=> ds ds' idx HWfdata HLength Heq.
	eapply holds_upto_all_strong'.
	move=> n HHolds HBound.
	eapply Forall_size in HWfdata; eauto.
	case E: (idx == n).
	- move/eqP in E; subst.
	
	  remember (ds [| n |]) as e.
		symmetry in Heqe.
		eapply list_update_func_subst with (f := 
			[eta set datainst_BYTES (fun=> [])]
		) in Heqe as H; eauto.
		rewrite H.
		destruct e. simpl.
		rewrite /lookup_total in Heqe.
		rewrite Heqe in HWfdata.
		econstructor; eauto.
		+ apply/orP.
			by right.
		+ econstructor; eauto. 
	- remember (ds [|n|]) as e.
		symmetry in Heqe.
		eapply list_update_func_unchanged with (i := idx) (f :=
			[eta set datainst_BYTES (fun=> [])]
		) in Heqe as HLookup'; eauto; subst.
		+ rewrite HLookup'.
			eapply extend_datainst_refl_0; eauto.
		+ apply/eqP.
			move/eqP in E.
			eauto.
Qed.

Lemma update_global_unchanged: forall v_S v_S' func v_idx,
	v_S' = v_S <| store_GLOBALS := list_update_func (store_GLOBALS v_S) v_idx func |> ->
	store_FUNCS v_S = store_FUNCS v_S' /\
	store_TABLES v_S = store_TABLES v_S' /\
	length (store_GLOBALS v_S) = length (store_GLOBALS v_S') /\
	store_MEMS v_S = store_MEMS v_S' /\
	store_ELEMS v_S = store_ELEMS v_S' /\
	store_DATAS v_S = store_DATAS v_S'.
Proof. 
	move => v_S v_S' func v_idx H.
	subst.
	destruct v_S; simpl.
	repeat split; eauto.
	by erewrite <- list_update_length_func.
Qed.

Lemma ltn_leq_trans n m p : m < n → n <= p → m < p.
Proof.
	move=> H H'.
	rewrite /lt; apply: leq_trans; eauto.
Qed.
	
Lemma addrs_store_funcs_extension: forall v_S v_S' v_funcaddr v_ft,
	wf_store v_S' ->
	Externaddr_ok v_S (externaddr_FUNC v_funcaddr) (FUNC v_ft) ->
	holds_upto (fun v => v < | store_FUNCS v_S' |) (|(store_FUNCS v_S)|) ->
  holds_upto (fun v => Extend_funcinst ((store_FUNCS v_S) [|v|]) ((store_FUNCS v_S') [|v|])) (|(store_FUNCS v_S)|) ->
  Externaddr_ok v_S' (externaddr_FUNC v_funcaddr) (FUNC v_ft).
Proof.
	move => v_S v_S' v_funcaddr v_ft HWfstore HOk HHoldsBound HHolds.

	eapply Externaddr_invert_funcs in HOk as [xt [v_funcinst [HLength [HLookup [Hxt [HWfxt HSub]]]]]].
	inversion HSub; subst.
	clear H1 H0.
	apply externtype_func_eq in HSub; subst.
	injection H2 as ?; subst.
	eq_to_prop; subst.
	eapply holds_upto_lt in HHoldsBound.
	econstructor; eauto.
	- eapply ltn_leq_trans; eauto.
	- eapply holds_upto_lookup in HHolds; eauto.
		inversion HHolds; subst.
		eauto.
Qed.

(* TODO improve this lemma proof later*)
Lemma addrs_tables_extension: forall v_S v_S' v_tableaddr tabletype,
	wf_store v_S' ->
  Externaddr_ok v_S (externaddr_TABLE v_tableaddr) (TABLE tabletype) ->
	holds_upto (fun v => v < | store_TABLES v_S' |) (|(store_TABLES v_S)|) ->
  holds_upto (fun v => Extend_tableinst ((store_TABLES v_S) [|v|]) ((store_TABLES v_S') [|v|])) (|(store_TABLES v_S)|) ->
  Externaddr_ok v_S' (externaddr_TABLE v_tableaddr) (TABLE tabletype).
Proof.
	move => v_S v_S' v_tableaddr tabletype HWfStore HOk HHoldsBound HHolds.

	eapply Externaddr_invert_tables in HOk as [xt [v_tableinst [HLength [HLookup [Hxt [HWfxt HSub]]]]]].
	
	eapply holds_upto_lookup in HHolds; eauto.
	eq_to_prop.
	inversion HHolds; subst.
	inversion H4; subst.
	inversion HSub; subst.
	
	eapply Externaddr_ok__sub with (xt' := TABLE (tableinst_TYPE ((store_TABLES v_S') [|v_tableaddr|]))); eauto.

	eapply holds_upto_lt in HHoldsBound.
	eapply Externaddr_ok__table; eauto.
	- eapply ltn_leq_trans; eauto.
	- rewrite -H0; simpl. econstructor; eauto.
	- econstructor; eauto. 
		inversion H8; subst.
		rewrite -H in H5; simpl in H5.
		injection H5 as ?; subst.
		inversion H6; subst.
		inversion H7; subst.
		+ rewrite -H0.
			econstructor; eauto.
			destruct m_opt.
			- econstructor; eauto.
				+ eapply leq_trans; eauto.
				+ simpl in H14.
				injection H14 as ?; subst.
				apply H16.
			- destruct m_2_opt; try discriminate. 
		+
			rewrite -H0.
			econstructor; eauto.
			destruct m_opt; try discriminate.
			econstructor; eauto.
			+ eapply leq_trans; eauto.
		+ rewrite -H0; econstructor; eauto.
		+ rewrite -H0; econstructor; eauto.
Qed.

Lemma addrs_store_globals_extension: forall v_S v_S' v_globaladdr globaltype,
	wf_store v_S' ->
  Externaddr_ok v_S (externaddr_GLOBAL v_globaladdr) (GLOBAL globaltype) ->
	holds_upto (fun v => v < | store_GLOBALS v_S' |) (|(store_GLOBALS v_S)|) ->
  holds_upto (fun v => Extend_globalinst ((store_GLOBALS v_S) [|v|]) ((store_GLOBALS v_S') [|v|])) (|(store_GLOBALS v_S)|) ->
  Externaddr_ok v_S' (externaddr_GLOBAL v_globaladdr) (GLOBAL globaltype).
Proof.
	move => v_S v_S' v_globaladdr globaltype HWfStore HOk HHoldsBound HHolds.
	eapply Externaddr_invert_globals in HOk as [xt [v_globalinst [HLength [HLookup [Hxt [HWfxt HSub]]]]]].

	inversion HSub; subst.
	clear H0 H1 H2 H3.
	eapply externtype_global_eq in HSub; subst.

	eapply Externaddr_ok__sub with (xt' := GLOBAL (globalinst_TYPE ((store_GLOBALS v_S') [|v_globaladdr|]))); eauto.
	- eq_to_prop; subst.
		eapply holds_upto_lt in HHoldsBound.
		econstructor; eauto.
		- eapply ltn_leq_trans; eauto.
		- eapply holds_upto_lookup in HHolds; eauto.
			inversion HHolds; subst.
			inversion H3; subst.
			econstructor; eauto.
	- eapply holds_upto_lookup in HHolds; eauto.
		inversion HHolds.
		eq_to_prop; subst.
		rewrite -H.
		simpl.
		econstructor; econstructor; eauto.
	- econstructor; eauto. 
Qed.

Lemma addrs_mems_extension: forall v_S v_S' v_memaddr memtype,
	wf_store v_S' ->
  Externaddr_ok v_S (externaddr_MEM v_memaddr) (MEM memtype) ->
	holds_upto (fun v => v < | store_MEMS v_S' |) (|(store_MEMS v_S)|) ->
  holds_upto (fun v => Extend_meminst ((store_MEMS v_S) [|v|]) ((store_MEMS v_S') [|v|])) (|(store_MEMS v_S)|) ->
  Externaddr_ok v_S' (externaddr_MEM v_memaddr) (MEM memtype).
Proof.
	move => v_S v_S' v_memaddr memtype HWfStore HOk HHoldsBound HHolds.

	eapply Externaddr_invert_mems in HOk as [xt [v_meminst [HLength [HLookup [Hxt [HWfxt HSub]]]]]].
	
	eapply holds_upto_lookup in HHolds; eauto.
	eq_to_prop.
	inversion HHolds; subst.
	inversion H4; subst.
	inversion HSub; subst.
	
	eapply Externaddr_ok__sub with (xt' := MEM (meminst_TYPE ((store_MEMS v_S') [|v_memaddr|]))); eauto.

	eapply holds_upto_lt in HHoldsBound.
	eapply Externaddr_ok__mem; eauto.
	- eapply ltn_leq_trans; eauto.
	- rewrite -H0; simpl. econstructor; eauto.
	- econstructor; eauto. 
		inversion H9; subst.
		rewrite -H in H5; simpl in H5.
		injection H5 as ?; subst.
		inversion H6; subst.
		inversion H7; subst.
		+ rewrite -H0.
			econstructor; eauto.
			destruct m_opt.
			- econstructor; eauto.
				+ eapply leq_trans; eauto.
				+ simpl in H14.
				injection H14 as ?; subst.
				apply H16.
			- destruct m_2_opt; try discriminate. 
		+
			rewrite -H0.
			econstructor; eauto.
			destruct m_opt; try discriminate.
			econstructor; eauto.
			+ eapply leq_trans; eauto.
			+ inversion H7; subst; eauto.
		+ rewrite -H0; econstructor; eauto.
		+ rewrite -H0; econstructor; eauto.
Qed.

Lemma addrss_store_funcs_extension: forall v_S v_S' v_funcaddrs tcf,
	wf_store v_S' ->
  Forall2 (fun v s => Externaddr_ok v_S (externaddr_FUNC v) (FUNC s)) v_funcaddrs tcf ->
	holds_upto (fun v => v < | store_FUNCS v_S' |) (|(store_FUNCS v_S)|) ->
  holds_upto (fun v => Extend_funcinst ((store_FUNCS v_S) [|v|]) ((store_FUNCS v_S') [|v|])) (|(store_FUNCS v_S)|) ->
  Forall2 (fun v s => Externaddr_ok v_S' (externaddr_FUNC v) (FUNC s)) v_funcaddrs tcf.
Proof.
	move => v_S v_S' v_funcaddrs.
	move: v_S v_S'.
	induction v_funcaddrs;
	move => v_S v_S' tcf HWfStore HOk HHoldsBound HHolds => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (addrs_store_funcs_extension v_S) => //.
	- eapply IHv_funcaddrs; eauto. inversion HOk; eauto.
Qed. 	

Lemma addrss_tables_extension: forall v_S v_S' v_tableaddrs tcf,
	wf_store v_S' ->
  Forall2 (fun v s => Externaddr_ok v_S (externaddr_TABLE v) (TABLE s)) v_tableaddrs tcf ->
	holds_upto (fun v => v < | store_TABLES v_S' |) (|(store_TABLES v_S)|) ->
  holds_upto (fun v => Extend_tableinst ((store_TABLES v_S) [|v|]) ((store_TABLES v_S') [|v|])) (|(store_TABLES v_S)|) ->
  Forall2 (fun v s => Externaddr_ok v_S' (externaddr_TABLE v) (TABLE s)) v_tableaddrs tcf.
Proof.
	move => v_S v_S' v_tableaddrs.
	move: v_S v_S'.
	induction v_tableaddrs;
	move => v_S v_S' tcf HWfStore HOk HHoldsBound HHolds => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (addrs_tables_extension v_S) => //.
	- eapply IHv_tableaddrs; eauto. inversion HOk; eauto.
Qed. 	

Lemma addrss_store_globals_extension: forall v_S v_S' v_globaladdrs tcf,
	wf_store v_S' ->
  Forall2 (fun v s => Externaddr_ok v_S (externaddr_GLOBAL v) (GLOBAL s)) v_globaladdrs tcf ->
	holds_upto (fun v => v < | store_GLOBALS v_S' |) (|(store_GLOBALS v_S)|) ->
  holds_upto (fun v => Extend_globalinst ((store_GLOBALS v_S) [|v|]) ((store_GLOBALS v_S') [|v|])) (|(store_GLOBALS v_S)|) ->
  Forall2 (fun v s => Externaddr_ok v_S' (externaddr_GLOBAL v) (GLOBAL s)) v_globaladdrs tcf.
Proof.
	move => v_S v_S' v_globaladdrs.
	move: v_S v_S'.
	induction v_globaladdrs;
	move => v_S v_S' tcf HWfStore HOk HHoldsBound HHolds => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	apply Forall2_cons_iff. split.
	- inversion HOk; subst.
	  apply (addrs_store_globals_extension v_S) => //.
	- eapply IHv_globaladdrs; eauto. inversion HOk; eauto.
Qed.


Lemma addrss_mems_extension: forall v_S v_S' v_memaddrs tcf,
	wf_store v_S' ->
	Forall2 (fun v s => Externaddr_ok v_S (externaddr_MEM v) (MEM s)) v_memaddrs tcf ->
	holds_upto (fun v => v < | store_MEMS v_S' |) (|(store_MEMS v_S)|) ->
  holds_upto (fun v => Extend_meminst ((store_MEMS v_S) [|v|]) ((store_MEMS v_S') [|v|])) (|(store_MEMS v_S)|) ->
  Forall2 (fun v s => Externaddr_ok v_S' (externaddr_MEM v) (MEM s)) v_memaddrs tcf.
Proof.
	move => v_S v_S' v_memaddrs.
	move: v_S v_S'.
	induction v_memaddrs;
	move => v_S v_S' tcf HWfStore HOk HHoldsBound HHolds => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	apply Forall2_cons_iff. split.
	- inversion HOk; subst.
	  apply (addrs_mems_extension v_S) => //.
	- eapply IHv_memaddrs; eauto. inversion HOk; eauto.
Qed.

Lemma Extend_store_exts: forall v_S v_S' v_exportinst,
	Extend_store v_S v_S' ->
	Forall (Exportinst_ok v_S) v_exportinst -> 
	Forall (Exportinst_ok v_S') v_exportinst.
Proof.
	move => v_S v_S' v_exportinst.
	move: v_S v_S'.
	induction v_exportinst;
	move => v_S v_S' Hext HOk => //=.
	subst. inversion HOk. 
	apply Forall_cons_iff. split.
	-	inversion H1.
		subst.
		invert_extend_store Hext.
		eapply mk_Exportinst_ok with (xt := xt); eauto.
		eq_to_prop.
		pose proof H3 as Hextok.
		dependent induction H3; subst.
		+ eapply addrs_store_globals_extension; simpl; eauto. 
		+ eapply addrs_mems_extension; simpl; eauto.
		+ eapply addrs_tables_extension; simpl; eauto.
		+ eapply addrs_store_funcs_extension; simpl; eauto.
		+ eapply Externaddr_ok__sub with (xt := xt); eauto.
	- eapply IHv_exportinst; eauto.
Qed.

Lemma Extend_store_eleminst: forall v_S v_S' a t,
	Extend_store v_S v_S' ->
	Eleminst_ok v_S a t ->
	Eleminst_ok v_S' a t.
Proof.
	move => s s' x t HSt Het.

	inversion Het; subst.
	econstructor.

	induction ref_lst; auto.
	inversion H; subst; auto.
	econstructor.
	{
		eapply Extend_store_ref; eauto.
	}
	2: by inversion HSt.
	eapply IHref_lst; eauto.
	by inversion Het.
Qed.

Lemma Extend_store_eleminsts': forall v_S v_S' aa ts,
	Extend_store v_S v_S' ->
	Forall (λ a , a < size (store_ELEMS v_S)) aa ->
	Forall2 (λ a t, Eleminst_ok v_S (lookup_total (store_ELEMS v_S) a) t) aa ts ->
	Forall (λ a , a < size (store_ELEMS v_S')) aa /\
	Forall2 (λ a t, Eleminst_ok v_S' (lookup_total (store_ELEMS v_S') a) t) aa ts.
Proof.
	move => s s' aa ts HS HLen He.
	destruct s, s'.
	invert_extend_store HS; simpl in *.
	clear - He HElemsBound' HElemsExtend HLen HS HWfStore'; subst.
	split.
	{
		eapply Forall_impl.
		2: eapply HLen.
		simpl.
		move => a HLena.
		eapply holds_upto_lt in HElemsBound'.
		eapply ltn_leq_trans; eauto. 
	}
	move : ts HLen He HElemsBound' HElemsExtend.
	induction aa; move => ts HLen He HElemsBound' HElemsExtend. inversion He; subst; auto.
	destruct ts; inversion He; subst.
	constructor.
	{
		inversion HLen; subst.
		eapply holds_upto_lookup with (i := a) in HElemsExtend; eauto.
		inversion HElemsExtend as [? ? ? Href Heq1 Heq2]; subst.

		remember (store_ELEMS0 [|a|]) as inst.
		inversion H2 as [? ? ? HRefOks HWfstore Heq3 Heq4]; subst.

		rewrite -Heq4 in Heq1.
		injection Heq1 as ?; subst.

		econstructor; eauto.
		eq_to_propH Href.
		destruct Href; move/eqP in H; subst.
		- eapply Extend_store_refs'; eauto.
		- econstructor.	
	}
	eapply IHaa; auto.
	by inversion HLen.
Qed.

Lemma Extend_store_eleminsts: forall v_S v_S' aa ts,
	Extend_store v_S v_S' ->
	Forall2 (λ a t, Eleminst_ok v_S a t) aa ts ->
	Forall2 (λ a t, Eleminst_ok v_S' a t) aa ts.
Proof.
	move => s s' aa ts HS He.
	induction He; auto.
	econstructor; auto.
	invert_elems.
	inversion H; subst.
	econstructor.
	induction H0; auto.
	econstructor.
	- eapply Extend_store_ref; eauto.
	- eapply IHForall. by inversion H.
	- by inversion HS.
Qed.

Lemma Extend_store_datainsts': forall v_S v_S' aa ts,
	Extend_store v_S v_S' ->
	Forall (λ a , a < size (store_DATAS v_S)) aa ->
	Forall2 (λ a t, Datainst_ok v_S (lookup_total (store_DATAS v_S) a) t) aa ts ->
	Forall (λ a, a < size (store_DATAS v_S')) aa /\
	Forall2 (λ a t, Datainst_ok v_S' (lookup_total (store_DATAS v_S') a) t) aa ts.
Proof.
	move => v_S v_S' aa ts HS HLen Hds.
	
	split.
	{
		invert_extend_store HS.
		eapply Forall_impl.
		2: eapply HLen.
		simpl.
		move => a HLena.
		eapply holds_upto_lt in HDatasBound'.
		eapply ltn_leq_trans; eauto. 
	}

	move : v_S ts HLen Hds HS.
	induction aa; move => v_S ts HLen Hds HS; destruct ts; try by inversion Hds.

	inversion Hds; subst.
	econstructor.
	{
		inversion H2; subst.
		inversion HLen; subst.

		invert_extend_store HS.
		eapply holds_upto_lookup with (i := a) in HDatasExtend; eauto.
		inversion HDatasExtend; subst.
		econstructor; eauto.
	}

	eapply IHaa; eauto.
	by inversion HLen.
Qed.

Lemma Extend_store_datainsts: forall v_S v_S' aa ts,
	Extend_store v_S v_S' ->
	Forall2 (λ a t, Datainst_ok v_S a t) aa ts ->
	Forall2 (λ a t, Datainst_ok v_S' a t) aa ts.
Proof.
	move => s s' aa ts HS He.
	induction He; auto.
	econstructor; auto.

	invert_extend_store HS.
	inversion H; subst.
	econstructor; eauto.
Qed.

Lemma Extend_store_moduleinst: forall v_S v_S' v_i v_C,
    Extend_store v_S v_S' ->
    Moduleinst_ok v_S v_i v_C ->
    Moduleinst_ok v_S' v_i v_C.
Proof.
	move => v_S v_S' v_i v_C HStoreExtension HMIT.
	invert_extend_store HStoreExtension.
	invert_moduleinstok HMIT. eq_to_prop; subst.
	assert (
		Forall (λ a , a < Datatypes.length (store_ELEMS v_S')) elemaddr_lst /\
		Forall2 (λ a t, Eleminst_ok v_S' (lookup_total (store_ELEMS v_S') a) t) elemaddr_lst elemtype_lst) as [HElemLen' HElem].
	{
	  eapply Extend_store_eleminsts'; eauto.
	}
	assert (
		Forall (λ a , a < Datatypes.length (store_DATAS v_S')) dataaddr_lst /\
		Forall2 (λ a t, Datainst_ok v_S' (lookup_total (store_DATAS v_S') a) t) dataaddr_lst datatype_lst) as [HDataLen' HData].
	{
	  eapply Extend_store_datainsts'; eauto.
	}
	subst.
	apply mk_Moduleinst_ok; eq_to_prop; auto.
	- eapply addrss_store_globals_extension; simpl; eauto.
	- eapply addrss_store_funcs_extension; simpl; eauto.
	- eapply addrss_mems_extension; simpl; eauto.
	- eapply addrss_tables_extension; simpl; eauto.
	- eapply Extend_store_exts; simpl; eauto.
Qed.

Lemma Extend_store_funcinst: forall s s' v t,
	Extend_store s s' ->
	Funcinst_ok s v t ->
	Funcinst_ok s' v t.
Proof.
	move => s s' v t HS H.
	inversion H; subst.
	invert_extend_store HS.
	econstructor; eauto.
	eapply Extend_store_moduleinst; eauto.
Qed.

Lemma Extend_store_funcinsts: forall s s' vs ts,
	Extend_store s s' ->
	Forall2 (λ v t, Funcinst_ok s v t) vs ts ->
	Forall2 (λ v t, Funcinst_ok s' v t) vs ts.
Proof.
	move => s s' vs ts HS H.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H1.
	eapply Extend_store_funcinst; eauto.
Qed.

Lemma Extend_store_globalinst: forall s s' v t,
	Extend_store s s' ->
	Globalinst_ok s v t ->
	Globalinst_ok s' v t.
Proof.
	move => s s' v t HS HG.
	inversion HG; subst.
	invert_extend_store HS.
	econstructor; eauto.
	eapply Extend_store_val; eauto.
Qed.

Lemma Extend_store_globalinsts: forall s s' vs ts,
	Extend_store s s' ->
	Forall2 (λ v t, Globalinst_ok s v t) vs ts ->
	Forall2 (λ v t, Globalinst_ok s' v t) vs ts.
Proof.
	move => s s' vs ts HS HG.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply Extend_store_globalinst; eauto.
Qed.

Lemma Extend_store_tableinst: forall s s' v t,
	Extend_store s s' ->
	Tableinst_ok s v t ->
	Tableinst_ok s' v t.
Proof.
	move => s s' v t HS HT.
	inversion HT; subst; clear HT.
	invert_extend_store HS.
	eq_to_prop; subst.
	econstructor; eauto.
	clear - H0 HS.
	
	induction H0; eauto.
	econstructor; auto.
	eapply Extend_store_ref; eauto.
Qed.

Lemma Extend_store_tableinsts: forall s s' vs ts,
	Extend_store s s' ->
	Forall2 (λ v t, Tableinst_ok s v t) vs ts ->
	Forall2 (λ v t, Tableinst_ok s' v t) vs ts.
Proof.
	move => s s' vs ts HS HG.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply Extend_store_tableinst; eauto.
Qed.

Lemma Extend_store_meminst: forall s s' v t,
	Extend_store s s' ->
	Meminst_ok s v t ->
	Meminst_ok s' v t.
Proof.
	move => s s' v t HS HT.
	invert_extend_store HS.
	inversion HT; subst; clear HT.
	econstructor; eauto.
Qed.

Lemma Extend_store_meminsts: forall s s' vs ts,
	Extend_store s s' ->
	Forall2 (λ v t, Meminst_ok s v t) vs ts ->
	Forall2 (λ v t, Meminst_ok s' v t) vs ts.
Proof.
	move => s s' vs ts HS HG.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply Extend_store_meminst; eauto.
Qed.

Lemma Extend_store_externaddrs_func: forall s s' fa ft,
	Extend_store s s' ->
	Externaddr_ok s (externaddr_FUNC fa) (FUNC ft) ->
	Externaddr_ok s' (externaddr_FUNC fa) (FUNC ft).
Proof.
	move => s s' fa ft HSe HEa.
	invert_extend_store HSe.
	eapply addrs_store_funcs_extension; eauto.
Qed.

Scheme ais_ok_ind' := Induction for Instrs_ok2 Sort Prop
	with
	 Expr_ok2_ind' := Induction for Expr_ok2 Sort Prop
	with
	 ai_ok_ind' := Induction for Instr_ok2 Sort Prop.

Lemma Extend_store_ais: forall s s' c ais ft,
	Extend_store s s' ->
	Store_ok s ->
	Store_ok s' ->
	Instrs_ok2 s c ais ft ->
	Instrs_ok2 s' c ais ft.
Proof.
	move => s s' c ais ft HSe HSt1 HSt2 HType.
	eapply ais_ok_ind' with
		(P := fun s c ais tf (_ : Instrs_ok2 s c ais tf) => forall s',
            Store_ok s ->
            Store_ok s' ->
            Extend_store s s' ->
            Instrs_ok2 s' c ais tf)
    	(P0 := fun s c ais ts (_ : Expr_ok2 s c ais ts) => forall s',
             Store_ok s ->
             Store_ok s' ->
             Extend_store s s' ->
             Expr_ok2 s' c ais ts)
    	(P1 := fun s c ai ts (_ : Instr_ok2 s c ai ts) => forall s',
             Store_ok s ->
             Store_ok s' ->
             Extend_store s s' ->
             Instr_ok2 s' c ai ts)
		in HType;
	try solve [
		intros; econstructor; eauto
	].
	{
		eapply HType; eauto.
	}
	{ (* Empty *)
		intros.
		invert_storeok H0.
		econstructor; eauto.
	}
	{ (* Instr *)
		intros.
		invert_storeok H1.
		eapply Instrs_ok2__instr; eauto.
	}
	{ (* Sequence *)
		intros.
		invert_storeok H2.
		eapply Instrs_ok2__seq; eauto.
	}
	{ (* Sub *)
		intros.
		invert_storeok H1.
		eapply Instrs_ok2__sub; eauto.
	}
	{ (* Frame *)
		intros.
		invert_storeok H1.
		eapply Instrs_ok2__frame; eauto.
	}
	{ (* Expr2 *)
		intros.
		invert_storeok H1.
		econstructor; eauto.
	}
	{ (* Plain *) 
		intros.
		invert_storeok H0.
		eapply plain; eauto.
	}
	{ (* Label *)
		intros. 
		invert_storeok H2.
		eapply label; eauto.
	}
	{ (* Frame instr *)
		intros.
		invert_storeok H1.
		eapply Instr_ok2__frame; eauto.
		inversion f0.
		econstructor; eauto.
		- eapply Extend_store_moduleinst; eauto.
		- eapply Extend_store_vals; eauto.
	}
	{ (* CALL ADDR *)
		intros.
		invert_storeok H0.
		econstructor; eauto.
		eapply Extend_store_externaddrs_func; eauto.
	}
	{ (* Ref *)
		intros.
		invert_storeok H0.
		econstructor; eauto.
		eapply Extend_store_ref; eauto.
	}
	{ (* TRAP *)
		intros.
		invert_storeok H0.
		econstructor; eauto.
	}
Qed.

Lemma size_repeat {A : Type}: forall (a : A) (n : nat),
	| List.repeat a n | = n.
Proof.
	move => a n.
	induction n; eauto.
	simpl.
	by rewrite IHn.
Qed.

Lemma construct_tableinsts: forall s ts t tba lim tbr i ref_lst,
	Forall2 (λ v t, Tableinst_ok s v t) (store_TABLES s) ts ->
	Ref_ok s ref_lst t ->
	lookup_total (store_TABLES s) tba =  {| tableinst_TYPE := mk_tabletype lim t; REFS := tbr |} ->
	Forall2 (λ v t, Tableinst_ok s v t)
		(list_update_func (store_TABLES s) tba
			(λ v_1 : tableinst, v_1 <| REFS :=
				list_update_func (REFS v_1) i (fun=> ref_lst)
			|>)) ts.
Proof.
	move => s ts t tba lim tbr i ref_lst Hold HRef HLookup.
	move : tba HLookup.
	induction Hold; auto; move => tba HLookup.
	destruct tba.
	{
		simpl.
		econstructor; auto.
		inversion H; subst.
		rewrite /lookup_total /= in HLookup.
		inversion HLookup; subst; clear HLookup.
		rewrite /= /set /=.
		econstructor; eq_to_prop; subst; eauto.
		2:
		{
			by rewrite list_update_length_func.
		}
		2:
		{
			econstructor; eauto.
		}
		clear IHHold H3 H H0 H4 H5.
		(* injection H0 as ?; subst. *)
		move : i.
		induction H1; auto.
		move => i.
		destruct i.
		{
			econstructor; auto.
		}
		rewrite /=.
		econstructor; auto.
	}
	simpl.
	econstructor; auto.
Qed.

Lemma construct_tableinsts_grow: forall s ts ref_lst t tba v_r j_opt v_n tbinsts,
	Forall wf_tableinst tbinsts ->
	Forall2 (λ v t, Tableinst_ok s v t) (store_TABLES s) ts ->
	Ref_ok s ref_lst t ->
	Forall (λ v_j, (size v_r + v_n) <= (v_j :> nat)) (option_to_list j_opt) ->
	lookup_total (store_TABLES s) tba = {|
		tableinst_TYPE := mk_tabletype (mk_limits
			(mk_uN (size v_r)) j_opt) t;
		REFS := v_r |} ->
	tbinsts = (list_update_func (store_TABLES s) tba
			(fun=> {|
				tableinst_TYPE := mk_tabletype (mk_limits
					(mk_uN (size v_r + v_n)) j_opt) t;
				REFS := v_r ++ repeat ref_lst v_n
			|})) ->
	Forall2 (λ v t, Tableinst_ok s v t) tbinsts
		(list_update_func ts tba (fun=> mk_tabletype (mk_limits
			(mk_uN (size v_r + v_n)) j_opt) t)).
Proof.
	move => s ts ref_lst t tba v_r j_opt v_n tbinsts HWftbinsts Hold HRef HRange HLookup HEq.
	subst.
	move : tba HLookup HRef HWftbinsts.
	induction Hold; move => tba HLookup HRef HWftbinsts; auto.
	destruct tba.
	{
		simpl.
		simpl in HWftbinsts.
		inv_Forall HWftbinsts.

		econstructor; auto.
		inversion H; subst.
		rewrite /lookup_total /= in HLookup.
		inversion HLookup; subst; clear HLookup.
		inversion HP; subst.
		{
		(* m_opt is Some *)
			
			econstructor; eq_to_prop; eauto.
			{
				econstructor; eauto.
				inversion H7; subst.
				inversion H8; subst.
				inversion H10; subst.
				destruct m_opt.
				all: 
					econstructor; eauto;
					inversion H11; subst;
					inversion H13; subst;
					inversion HRange; subst;
					econstructor; eauto;
					apply/andP; split; eauto.
			}


			{
				rewrite Forall_app.
				subst.
				
				split; auto.
				clear - HRef.
				induction v_n; auto.
				econstructor; auto. 
			}

			{
				rewrite size_cat.
				by rewrite size_repeat.
			}	
		}
	}
	simpl.
	econstructor; auto.
	eapply IHHold; eauto.
	simpl in HWftbinsts.
	inv_Forall HWftbinsts; eauto.
Qed.

Lemma construct_globalinsts: forall s ts ga v t v_old,
	Forall2 (λ v t, Globalinst_ok s v t) (store_GLOBALS s) ts ->
	lookup_total (store_GLOBALS s) ga = {| globalinst_TYPE := mk_globaltype (Some MUT) t; VALUE := v_old |} ->
	Val_ok s v t ->
	Forall2 (λ v t, Globalinst_ok s v t)
		(list_update_func (store_GLOBALS s) ga [eta set VALUE (fun=> v)]) ts.
Proof.
	move => s ts ga v t v_old Hold HLookup HValok.
	move : ga HLookup HValok.
	induction Hold; auto; move => ga HLookup HValok.
	destruct ga.
	{
		simpl.
		econstructor; auto.
		inversion H; subst.
		rewrite /lookup_total /= in HLookup.
		inversion HLookup; subst.
		rewrite /set /=.
		econstructor; eauto.
		inversion HValok; subst; econstructor; eauto.
		inversion H4; subst; econstructor; eauto.
	}
	simpl.
	econstructor; auto.
Qed.

Lemma construct_meminsts: forall s ts ma v_mt b_lst v_i v_nb,
	Forall wf_byte v_nb ->
	Forall2 (λ v t, Meminst_ok s v t) (store_MEMS s) ts ->
	lookup_total (store_MEMS s) ma = {| meminst_TYPE := v_mt; BYTES := b_lst |} ->
	Forall2 (λ v t, Meminst_ok s v t)
		(list_update_func (store_MEMS s) ma
			(λ m, m <| BYTES :=
			list_slice_update (BYTES m) v_i (size v_nb) v_nb |>)) ts.
Proof.
	move => s ts ma v_mt b_lst v_i v_nb HWfbytes Hold HLookup.
	move : ma HLookup.
	induction Hold; auto; move => ma HLookup.
	destruct ma.
	{
		simpl.
		econstructor; auto.
		inversion H; subst.
		rewrite /lookup_total /= in HLookup.
		inversion HLookup; subst.
		rewrite /set /=.
		econstructor; eauto.
		eq_to_prop.
		rewrite list_slice_update_length; auto.

		(* Wfness *)
		inversion H3; subst.
		econstructor; eauto.
		eapply forall_preserved_bytes; eauto.
	}
	simpl.
	econstructor; auto.
Qed.

Lemma construct_meminsts_grow: forall s ts ma b_lst lim_old v_n v_j_opt minsts,
	Forall wf_meminst minsts ->
	Forall2 (λ v t, Meminst_ok s v t) (store_MEMS s) ts ->
	lookup_total (store_MEMS s) ma = {|
		meminst_TYPE := PAGE (mk_limits (lim_old) v_j_opt);
		BYTES := b_lst |} ->
	lim_old = size b_lst / (64 * Ki) ->
	Forall (fun (j : u32) => lim_old + v_n <= j) v_j_opt ->
	minsts = (list_update_func (store_MEMS s) ma
		(fun=> {| meminst_TYPE := PAGE (mk_limits (lim_old + v_n) v_j_opt);
			BYTES := b_lst ++ repeat (mk_byte 0) (v_n * (64 * Ki)) |})) ->
	Forall2 (λ (v : meminst) (t : memtype), Meminst_ok s v t)
		minsts
		(list_update_func ts ma (fun=> PAGE (mk_limits (lim_old + v_n) v_j_opt))).
Proof.
	move => s ts ma b_lst lim_old v_n v_j_opt minsts HWfminsts Hold HLookup HLim HRange HEq.
	subst.
	move : ma HLookup HRange HWfminsts.
	induction Hold; auto; move => ma HLookup HRange HWfminsts.
	destruct ma.
	{
		rewrite /list_update_func.
		econstructor; auto.
		rewrite /lookup_total /nth in HLookup.
		rewrite HLookup in H.
		remember (64 * Ki) as n.
		inversion H; clear H.
		subst.
		eq_to_prop.
		remember (64 * Ki) as n.
		assert (n <> 0). { subst. rewrite /Ki. discriminate. }
		list_to_seq.
		simpl in HWfminsts.
		inv_Forall HWfminsts.
		remember (64 * Ki) as n.
		inversion HP; subst.
		remember (64 * Ki) as n.
		econstructor; eq_to_prop; eauto.
		2: {
			rewrite size_cat H4 size_repeat.
			rewrite mulnDl.
			rewrite mulnE.
			rewrite Nat.div_mul; auto.
		}
		econstructor; eauto.
		admit.
		(* TODO - Find some way of showing lim_old + v_n <= 2 ^ 16 *)

(* 
		econstructor; eauto.
		{
			inversion H3; subst.
			remember (64 * Ki) as n.
			inversion H1; subst.
			admit.

		} *)

		(* econstructor; eauto. *)

		(* rewrite <- invert_opt_map_some.
		inversion H6; subst; clear H6.
		inversion H1; subst; clear H1.
		destruct m_opt; try discriminate; subst; eauto.
		injection H2 as ?; subst.
		inversion H6; subst; clear H6.
		move/andP in H2; destruct H2.
		econstructor.
		- eapply leq_trans in H1.
			apply H1.
			auto.
		- econstructor; eauto.
			apply/andP; split; auto. *)
	}
	econstructor; auto.
	eapply IHHold; eauto.
	simpl in HWfminsts.
	inv_Forall HWfminsts; eauto.
Admitted.

Lemma construct_datainsts: forall s da dt b_lst,
	Forall2 (fun v t => Datainst_ok s v t) (store_DATAS s) dt ->
	lookup_total (store_DATAS s) da = {| datainst_BYTES := b_lst |} ->
	Forall2 (fun v t => Datainst_ok s v t)
		(list_update_func (store_DATAS s) da [eta set datainst_BYTES (fun=> [])]) dt.
Proof.
	move => s da dt b_lst Hold HLookup.
	move : da HLookup.
	induction Hold; auto; move => da HLookup.
	destruct da.
	{
		rewrite /lookup_total /= in HLookup; subst.
		inversion H; subst.
		simpl.
		econstructor; auto.
		rewrite /set /=.
		by econstructor.
	}
	simpl.
	econstructor; auto.
Qed.

Lemma construct_eleminsts: forall s ts ea t ref,
	Forall2 (λ v t, Eleminst_ok s v t) (store_ELEMS s) ts ->
	lookup_total (store_ELEMS s) ea = {| eleminst_TYPE := t; eleminst_REFS := ref |} ->
	Forall2 (λ v t, Eleminst_ok s v t)
	(list_update_func (store_ELEMS s) ea [eta set eleminst_REFS (fun=> [])]) ts.
Proof.
	move => s ts ea t ref Hold HLookup.
	move : ea HLookup.
	induction Hold; auto; move => ea HLookup.
	destruct ea.
	{
		rewrite /lookup_total /= in HLookup; subst.
		inversion H; subst.
		simpl.
		econstructor; auto.
		rewrite /set /=.
		by econstructor.
	}
	simpl.
	econstructor; auto.
Qed.
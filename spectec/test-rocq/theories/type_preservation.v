
From Stdlib Require Import String List Unicode.Utf8 NArith Arith QArith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping type_preservation_pure extension_lemmas axioms.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Import ListNotations.

Lemma zero_is_well_formed: 
	wf_num_ I32 (mk_num__0 Inn_I32 (mk_uN 0)).
Proof.
	econstructor; eauto; econstructor; eauto.
Qed.

Definition num_default (nt : numtype) : num_ :=
	match nt with
		| I32 => mk_num__0 Inn_I32 (mk_uN 0%num)
		| I64 => mk_num__0 Inn_I64 (mk_uN 0%num)
		| F32 => mk_num__1 Fnn_F32 (fzero 32%num)
		| F64 => mk_num__1 Fnn_F64 (fzero 64%num)
	end
.

Lemma Qfloor_add_Z (q : Q) (z : Z) :
  Qround.Qfloor (q + inject_Z z) =
  (Qround.Qfloor q + z)%Z.
Proof.
  destruct q as [n d].
  simpl.
	repeat rewrite Z.mul_1_r.
	rewrite Pos.mul_1_r.
  rewrite Zdiv.Z_div_plus_full.
  reflexivity.
  discriminate.
Qed.

Lemma wf_context_app : forall C C',
	wf_context C ->
	wf_context C' ->
	wf_context (C @@ C').
Proof.
	move=> C C' HWfC HWfC'.
	destruct C; destruct C'. unfold _append. unfold Append_context. unfold _append_context; simpl.
	inversion HWfC; inversion HWfC'; subst.

	econstructor; apply Forall_app; split; eauto.
Qed.

Lemma wf_context_tab : forall n C,
	(n < |context_TABLES C|)%BN ->
	wf_context C ->
	wf_tabletype (context_TABLES C [| n |]).
Proof.
	move => n C HBound HWf.
	inversion HWf; subst; simpl in *.
	eapply Forall_size in H; eauto.
Qed.

Lemma wf_context_mem : forall n C,
	(n < |context_MEMS C|)%BN ->
	wf_context C ->
	wf_memtype (context_MEMS C [| n |]).
Proof.
	move => n C HBound HWf.
	inversion HWf; subst; simpl in *.
	eapply Forall_size in H0; eauto.
Qed.


(* 
Lemma num_default_is_well_formed: forall nt,
	wf_num_ nt (num_default nt).
Proof.
	move=> nt.
	destruct nt; econstructor; eq_to_prop; eauto.
	- econstructor; eauto.
	- econstructor; eauto.
	- econstructor. econstructor. unfold sizenn; unfold E. simpl. eauto.
	- econstructor. econstructor. unfold sizenn; unfold E; simpl. eauto.
Qed. *)

Lemma inst_t_context_local_empty: forall s i C,
	Moduleinst_ok s i C ->
  context_LOCALS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.

Lemma inst_t_context_labels_empty: forall s i C,
	Moduleinst_ok s i C ->
  LABELS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.

Lemma t_preservation_vs_type': forall s f ais s' f' ais' C C' t1s t2s,
	Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
	Store_ok s -> 
	Moduleinst_ok s (frame_MODULE f) C ->
	Vals_ok s (LOCALS f) (context_LOCALS C') ->
	inst_match C C' ->
	Instrs_ok2 s C' ais (t1s :-> t2s) ->
	Vals_ok s (LOCALS f') (context_LOCALS C').
Proof.
	move => s f ais s' f' ais' C C' t1s t2s HReduce HST HIT.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	move: C' t1s t2s.
	generalize dependent ais.
	generalize dependent ais'.

	induction HReduce;
	move => ais' Heqc1 ais Heqc2 C' t1s t2s HVals1 Hmatch HType;
	eq_to_prop;
	try (destruct z; subst);
	try (destruct z'; subst);
	try (apply config_same in Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]];
	apply config_same in Heqc2 as [Hafter1  [Hafter2  Hafter3]]);
	try (specialize (IHHReduce _ erefl _ erefl));
	subst; auto.

	{
		invert_ais_typing.
		resolve_all_pt.
		assert (Vals_ok s (LOCALS f') (context_LOCALS C') =
			Vals_ok s (LOCALS f') (context_LOCALS (prepend_label C' extr))).
		{
			destruct C'; auto.
		}
		rewrite H3.
		eapply IHHReduce; destruct C'; eauto.
	}
	{
		invert_ais_typing.
		eapply IHHReduce; eauto.
	}
	{
		invert_ais_typing.
		resolve_all_pt.
		join_subtyping_eq Hsub Hsub0.
		eapply Val_ok_non_bot in HValok as Hnonbot.
		eapply valtype_sub_non_bot in Hsubv; eauto.
		subst.

		destruct f. simpl.
		eapply Forall2_list_update_func2; eauto.
	}
Qed.

Lemma t_preservation_vs_type: forall s f ais s' f' ais' C C' t1s t2s,
  Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
  Store_ok s -> 
	Extend_store s s' ->
  Moduleinst_ok s (frame_MODULE f) C ->
	Vals_ok s (LOCALS f) (context_LOCALS C') ->
	inst_match C C' ->
  Instrs_ok2 s C' ais (t1s :-> t2s) ->
  Vals_ok s' (LOCALS f') (context_LOCALS C').
Proof.
	move => s f ais s' f' ais' C C' t1s t2s HReduce HST
		HStoreExt HMInst HValOK Him HType.
	eapply t_preservation_vs_type' in HValOK; eauto.
	eapply Extend_store_vals in HValOK; eauto.
Qed.

Lemma wf_tableinsts_preserves: forall s tbinsts tbts,
	Forall2 (fun v t => Tableinst_ok s v t) tbinsts tbts ->
	Forall wf_tableinst tbinsts ->
	Forall wf_tabletype tbts.
Proof.
	move=> s tbints tbts HTbOK HWfTbinsts.
	move: HWfTbinsts.
	dependent induction HTbOK; eauto.
	move=> HWfTbinsts.
	eapply Forall_cons.
	inversion H; eauto.
	eapply IHHTbOK.
	by inversion HWfTbinsts.
Qed.

Lemma wf_memoryinsts_preserves: forall s meminsts mts,
	Forall2 (fun v t => Meminst_ok s v t) meminsts mts ->
	Forall wf_meminst meminsts ->
	Forall wf_memtype mts.
Proof.
	move=> s meminsts mts HTbOK HWfmeminsts.
	move: HWfmeminsts.
	dependent induction HTbOK; eauto.
	move=> HWfmeminsts.
	eapply Forall_cons.
	inversion H; eauto.
	eapply IHHTbOK.
	by inversion HWfmeminsts.
Qed.


Lemma list_update_func_preserves_prop {A : Type} {_ : Inhabited A}: forall (l : seq A) (f : A -> A) (P : A -> Prop) (x : N),
	Forall P l ->
	P (f (l [| x |])) ->
	Forall P (list_update_func l x f).
Proof.
	move=> l f P x HForall HP.
	move: x HP.
	induction l; eauto.
	move=> x HP.
	inversion HForall; subst.
	destruct x using N.peano_ind; simpl.
	- econstructor; eauto.
	- resolve_Nsucc. simplNsuccH HP. econstructor; eauto.
Qed.

Lemma list_update_func_forall_inv {A : Type} {_ : Inhabited A}: forall (l : seq A) (f : A -> A) (P : A -> Prop) (x : N),
	(x < | l |)%BN ->
	Forall P (list_update_func l x f) ->
	P (f (l [| x |])).
Proof.
	move=> l f P x HBound HForall.
	move: x HBound HForall.
	induction l; eauto; try discriminate; move=> x HBound HForall.
	- apply N.nlt_0_r in HBound. by exfalso.
	(* inversion HForall; subst. *)
	destruct x using N.peano_ind; simpl.
	- inversion HForall; subst; eauto.
	- simplNsucc. simpl in HForall. eapply IHl; eauto.
		- 
			simplNsizecons HBound. 
			apply N.succ_lt_mono in HBound; eauto.
		-
			resolve_Nsucc.
			inversion HForall; subst; eauto.
Qed.
	
Lemma store_extension_reduce: forall s f ais s' f' ais' C C' tf,
	wf_config (mk_config (mk_state s f) ais) ->
	Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
	Moduleinst_ok s (frame_MODULE f) C ->
	Instrs_ok2 s C' ais tf ->
	inst_match C C' ->
	Store_ok s ->
	Extend_store s s' /\ Store_ok s'.
Proof.
	move => s f ais s' f' ais' C C' tf HWfConfig HReduce HIT HType HMatch HStore.
	eapply ainstrs_ok_context_store_wf in HType as HWf; destruct HWf as [HWfC [HWfS HWfAis]].
	eapply Step_is_wf in HReduce as HWfConfig'; eauto.
	clear HWfC HWfAis.

	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.

	assert (wf_store s') as HWfStore'. {
		subst.
		inversion HWfConfig'. inversion H1; subst; eauto. 
	} 
	generalize dependent C. generalize dependent C'.
	generalize dependent tf.
	generalize dependent ais. generalize dependent ais'. 
	generalize dependent f. generalize dependent f'.

	
	pose proof extend_func_refl as LemFuncSame.
	pose proof extend_mem_refl as LemMemSame.
	pose proof extend_table_refl as LemTableSame.
	pose proof extend_global_refl as LemGlobalSame.
	pose proof extend_elem_refl as LemElemSame.
	pose proof extend_data_refl as LemDataSame.
	pose proof Extend_store_refl as LemStoreSame.

	induction HReduce;
	move => v_f' v_f ais' Heqc2 ais Heqc1 tf C' HType C HIT HMatch;
	destruct tf as [[tf1] [tf2]].
	all: eq_to_prop; try (destruct z; 
	apply config_same in Heqc1; apply config_same in Heqc2; 
	destruct Heqc1 as [? [? ?]]; destruct Heqc2 as [? [? ?]];
	subst; try (split; eauto; by eapply Extend_store_refl; eauto)).
	{ (* Label Context *) 
		injection Heqc1 as ?; subst.
		injection Heqc2 as ?; subst.
		typing_inversion HType.
		unfold_principal_typing Hai.
		destruct_all.
		eapply IHHReduce; eauto.
	}
	{ (* Label Frame *)
		injection Heqc1 as ?; subst.
		injection Heqc2 as ?; subst.
		typing_inversion HType.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H2; subst; clear H2.
		inversion H3; subst; clear H3.
		eapply IHHReduce; eauto.
		resolve_inst_match;
		rewrite /Append_List_;
		rewrite cats0; eauto.
	}
	{ (* Label Seq *)
		injection Heqc1 as ?; subst.
		injection Heqc2 as ?; subst.
		subst.
		typing_inversion HType.
		typing_inversion H2.
		eapply IHHReduce; eauto.
	}
	{ (* Global Set *) 
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.
		join_subtyping_eq Hsub Hsub0.
		eapply Val_ok_non_bot in HValok as Hnonbot.
		eapply valtype_sub_non_bot in Hsubv; eauto.
		subst. clear Hsub Hsubi Hnonbot.

		rewrite /lookup_total.

		remember ((proj_uN_0 x)) as v_i.
		
		remember ((GLOBALS (frame_MODULE v_f)) [| v_i |]) as ga.
		remember  (s <| store_GLOBALS :=
			list_update_func (store_GLOBALS s) ga
			[eta set VALUE (fun=> v_val)] |>) as s'.

		assert (
			(ga < |(store_GLOBALS s)|)%BN /\
			exists v, lookup_total (store_GLOBALS s) ga =
				{| globalinst_TYPE := mk_globaltype (Some MUT) t; VALUE := v |})
			as [HLen [v_old HLookup]].
		{
			eapply minst_invert_globals in HIT; eauto.

			eapply Forall2_size2 in HIT.
			2: ineq_to_propH H1; apply H1.
			destruct_all.
			
			eapply externtype_global_eq in H5; subst.

			rewrite H0 in H4.
			split. auto.
			by exists extr0.
		}

		assert (Extend_store s s').
		{
			inversion HWfS; subst.
			remember ({|
				store_FUNCS := var_0_lst;
				store_GLOBALS := var_1_lst;
				store_TABLES := var_2_lst;
				store_MEMS := var_3_lst;
				store_ELEMS := var_4_lst;
				store_DATAS := var_5_lst
			|}) as s.
			assert (wf_val v_val). { inversion HValok; subst; eauto. inversion H6; subst; econstructor. }
			eapply mk_Extend_store; eq_to_prop; simpl; eauto; (try (rewrite update_holds_upto_lt; eapply holds_upto_lt_refl)).
			- rewrite list_update_length_func. rewrite update_holds_upto_lt; eapply holds_upto_lt_refl.
			- eapply global_set_global_extension; subst; eauto. 
			- eapply LemMemSame; subst; eauto.
			- eapply LemTableSame; subst; eauto.
			- eapply LemFuncSame; subst; eauto.
			- eapply LemDataSame; subst; eauto.
		}
		split; auto.
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst :=
				list_update_func (store_GLOBALS s)
					ga
					[eta set VALUE (fun=> v_val)])
			(tableinst_lst := tableinst_lst)
			(meminst_lst := meminst_lst)
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			(memtype_lst := memtype_lst)
			(functype_lst := functype_lst)
			(tabletype_lst := tabletype_lst)
			(datatype_lst := datatype_lst)
			(elemtype_lst := elemtype_lst)

			; 
			eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply Extend_store_funcinsts; eauto |
				eapply Extend_store_tableinsts; eauto |
				eapply Extend_store_globalinsts; eauto |
				eapply Extend_store_meminsts; eauto |
				eapply Extend_store_eleminsts; eauto |
				eapply Extend_store_datainsts; eauto |
				eauto].
		- rewrite {1}list_update_length_func; eauto.
		- {
			eapply construct_globalinsts; subst; eauto.
		}
	}
	{ (* Table Set *)
		rewrite /fun_table in H0.
		(* destruct_all; subst. *)
		(* simpl in H0. *)
		invert_ais_typing.
		resolve_all_pt.
		(* Opaque instrtype_sub. *)
		join_subtyping_ge Hsub Hsub0.
		join_subtyping_eq Hsubi Hsub1.
		eapply Ref_ok_non_bot in HRefok as Hnonbot.
		eapply valtype_sub_non_bot in Hsubv0; eauto.
		assert (extr = t).
		{
			destruct t; destruct extr; auto; discriminate.
		}
		subst. clear Hsub Hsubi Hnonbot Hsubv Hsubv0 Hsubi0.

		remember (!( proj_num__0 i) :> N) as v_i.
		remember (x :> N) as j.
		remember (((TABLES (frame_MODULE v_f)) [|(x :> N)|])) as tba.
		remember  (s <| store_TABLES :=
			list_update_func (store_TABLES s) tba
			(λ v_1 : tableinst, v_1
				<| REFS := list_update_func (REFS v_1) v_i (fun=> v_ref)
			|>) |>) as s'.

		assert (
			(tba < |(store_TABLES s)|)%BN /\
			exists v_lim_1 tbr,
				(Limits_sub v_lim_1 extr0) /\
				((lookup_total (store_TABLES s) tba) =
					{| tableinst_TYPE := (mk_tabletype v_lim_1 t); REFS := tbr |}))
			as [HLen [v_lim_1 [tbr [HLimSub HLookup]]]].
		{
			eapply minst_invert_tables in HIT; eauto.

			eapply Forall2_size2 in HIT.
			2: ineq_to_propH H1; apply H1.
			destruct HIT as [tbr [tbt' [HBound [HLookup Hext]]]].
			rewrite H3 in Hext.
			inversion Hext; subst.
			inversion H6; subst.
			split. auto.
			exists lim_1, tbr; eauto.
		}

		assert (Extend_store s s').
		{
			inversion HWfS; subst.
			remember ({|
				store_FUNCS := var_0_lst;
				store_GLOBALS := var_1_lst;
				store_TABLES := var_2_lst;
				store_MEMS := var_3_lst;
				store_ELEMS := var_4_lst;
				store_DATAS := var_5_lst
			|}) as s.
			eapply mk_Extend_store; eq_to_prop; simpl; eauto; (try (rewrite update_holds_upto_lt; eapply holds_upto_lt_refl)).
			- eapply LemGlobalSame; subst; eauto.
			- eapply LemMemSame; subst; eauto.
			- rewrite list_update_length_func. rewrite update_holds_upto_lt; by eapply holds_upto_lt_refl.
			- subst; rewrite {1}/set /=.
				eapply table_set_table_extension; eauto. reflexivity.
			- eapply LemFuncSame; subst; eauto.
			- eapply LemDataSame; subst; eauto.
		}
		split; auto.
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst := globalinst_lst)
			(tableinst_lst := list_update_func (store_TABLES s) tba
				(λ v_1 : tableinst, v_1 <| REFS :=
					list_update_func (REFS v_1) v_i (fun=> v_ref)
				|>))
			(meminst_lst := meminst_lst)
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			(memtype_lst := memtype_lst)
			(functype_lst := functype_lst)
			(tabletype_lst := tabletype_lst)
			(datatype_lst := datatype_lst)
			(elemtype_lst := elemtype_lst)
			; 
			eq_to_prop;
			auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply Extend_store_funcinsts; eauto |
				eapply Extend_store_tableinsts; eauto |
				eapply Extend_store_globalinsts; eauto |
				eapply Extend_store_meminsts; eauto |
				eapply Extend_store_eleminsts; eauto |
				eapply Extend_store_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func; eauto.
		- {
			eapply construct_tableinsts; subst; eauto.
		}
	}
	{ (* Table Grow *)
		rename H0 into HNotNone.
		rename H into HGrow.
		invert_ais_typing.
		unfold_principal_typing Hai.
		destruct Hai as [extr [lim [HTemp [HBound HLookup]]]].
		rewrite HTemp in Hsub0; clear HTemp.
		unfold_principal_typing Hai0.
		destruct Hai0 as [Hwfn HTemp2].
		rewrite HTemp2 in Hsub1; clear HTemp2.
		Opaque instrtype_sub.
		join_subtyping_ge Hsub Hsub1.
		join_subtyping_eq Hsubi Hsub0.
		eapply Ref_ok_non_bot in HRefok as Hnonbot.
		eapply valtype_sub_non_bot in Hsubv; eauto.
		assert (extr = t).
		{
			destruct extr, t; auto; discriminate.
		}
		subst. clear Hsub Hsubi Hnonbot Hsubv.
		rewrite /fun_table in HGrow.
		inversion HGrow as [????????? Heq Hadd Hlt HRes HWf1 HWf2| ]; eq_to_prop; subst.
		2: 
		{
			destruct HNotNone. reflexivity.
		}
		remember ((proj_uN_0 x)) as v_i.
		remember (((TABLES (frame_MODULE v_f)) [| v_i |])) as tba.
		remember ((mk_limits (mk_uN (|r'_lst| + v_n)%BN) j_opt))
			as v_limits_new.
		remember (({| tableinst_TYPE := mk_tabletype v_limits_new rt;
			REFS := r'_lst ++ list_repeat v_ref v_n |})) as v_ti.
		remember  (s <| store_TABLES := list_update_func (store_TABLES s) tba
					(fun=> v_ti) |>) as s'.

		assert (
			(tba < |(store_TABLES s)|)%BN /\
			(Forall (λ j : u32, (((| r'_lst |) + v_n)%BN <= (j :> N))%BN) j_opt) /\
			(t = rt) /\
			((lookup_total (store_TABLES s) tba) =
				{| tableinst_TYPE := mk_tabletype
					(mk_limits (mk_uN (|r'_lst|)) j_opt)
					t;
					REFS := r'_lst |}))
			as [HLen [HRange [tbr HLookup']]].
		{
			eapply minst_invert_tables in HIT; eauto.

			eapply Forall2_size2 in HIT.
			2: ineq_to_propH HBound; apply HBound.
			destruct HIT as [tbr [tbt' [HBound' [HLookup' HSub]]]].

			rewrite HLookup in HSub.
			inversion HSub; subst; clear H2 H3.
			inversion H1; subst; clear H4 H5 H1.
			rename H2 into HLimits.

			rewrite update_forall_le_u32 in Hlt.
			rewrite -Heq in HLookup'.
			injection HLookup' as ?; subst.

			split; auto.
			split; auto.
			split; auto.
		
			rewrite -Heq.

			eapply s_invert_tables in HStore as [tbts HTable].
			eapply Forall2_size in HTable.
			2: apply HBound'. 
			destruct HTable as [ref_lst [v_m [rt [HLookup'' [HLookup''' [HTbtok HRefsOK]]]]]].

			rewrite HLookup'' in Heq.
			injection Heq as ?; subst.
			rewrite -H in HLookup'''.
			injection HLookup''' as ?; subst; eauto.
		}
		
		assert (Extend_store s s').
		{
			inversion HWfS; subst.
			remember ({|
				store_FUNCS := var_0_lst;
				store_GLOBALS := var_1_lst;
				store_TABLES := var_2_lst;
				store_MEMS := var_3_lst;
				store_ELEMS := var_4_lst;
				store_DATAS := var_5_lst
			|}) as s.
			eapply mk_Extend_store; eq_to_prop; simpl; eauto; (try (rewrite update_holds_upto_lt; eapply holds_upto_lt_refl)).
			- eapply LemGlobalSame; subst; eauto.
			- eapply LemMemSame; subst; eauto.
			- rewrite list_update_length_func. rewrite update_holds_upto_lt; by eapply holds_upto_lt_refl.
			- subst.
				eapply table_grow_table_extension; eauto. 
				{
					clear -HWfConfig' HStore.
					inversion HWfConfig'; subst.
					inversion H1; subst.
					inversion H3; subst; eauto.
				}
			- eapply LemFuncSame; subst; eauto.
			- eapply LemDataSame; subst; eauto.
		}
		split; auto.
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst := globalinst_lst)
			(tableinst_lst := list_update_func (store_TABLES s) tba (fun=> v_ti))
			(meminst_lst := meminst_lst)
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			(tabletype_lst := list_update_func (tabletype_lst) tba (fun=>
				mk_tabletype
				(mk_limits (mk_uN (|r'_lst| + v_n)%BN) j_opt)
				rt
			))
			(memtype_lst := memtype_lst)
			(functype_lst := functype_lst)
			(datatype_lst := datatype_lst)
			(elemtype_lst := elemtype_lst)
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply Extend_store_funcinsts; eauto |
				eapply Extend_store_tableinsts; eauto |
				eapply Extend_store_globalinsts; eauto |
				eapply Extend_store_meminsts; eauto |
				eapply Extend_store_eleminsts; eauto |
				eapply Extend_store_datainsts; eauto |
				eauto
			].
		- rewrite !list_update_length_func  /=; eauto.
		- {
			eapply construct_tableinsts_grow; subst; eauto.
			{
				clear -HWfConfig'.
				inversion HWfConfig'; subst.
				inversion H1; subst.
				inversion H3; subst; eauto. 
			}
		}
		- { 
				clear -HWfConfig' H16 H5 HLen.
				simpl in HLen.

				inversion H16; subst.
				
				(* dependent induction H5; eauto. *)
				inversion HWfConfig'; subst.
				inversion H1; subst.
				inversion H3; subst.
				eapply (wf_tableinsts_preserves _ _ _ H5) in H8; eauto.
				clear -H8 H5 H18 HLen.
				eapply list_update_func_preserves_prop; eauto.
				eapply list_update_func_forall_inv in H18; eauto.
				inversion H18; subst; eauto.
		  }
	}
	{ (* Elem Drop *)
		(* destruct_all; subst. *)
		invert_ais_typing.
		resolve_all_pt.

		remember ((proj_uN_0 x)) as i.
		remember ((lookup_total (ELEMS (frame_MODULE v_f)) i)) as ea.
		remember  (s <| store_ELEMS :=
			list_update_func (store_ELEMS s) ea [eta set eleminst_REFS (fun=> [])] |>) as s'.

		assert (
			(ea < |(store_ELEMS s)|)%BN /\
			exists rt v_ref,
				((lookup_total (store_ELEMS s) ea) =
					{| eleminst_TYPE := rt; eleminst_REFS := v_ref |}) /\
				(List.Forall (fun (v_ref : ref) => (Ref_ok s v_ref rt)) (v_ref)))
			as [HLen [rt [v_ref [HLookup HRefok]]]].
		{
			eapply minst_invert_elems in HIT; eauto.

			eapply Forall2_size2 in HIT.
			2: ineq_to_propH H1; apply H1.
			destruct HIT as [ref_lst [HBound [HRefOKs HLookup]]].
			rewrite -Heqea in HLookup.
			rewrite -Heqea in HBound.
			split; auto.

			by exists ((context_ELEMS C') [| i |]), ref_lst.
		}

				
		assert (Extend_store s s').
		{
			inversion HWfS; subst.
			remember ({|
				store_FUNCS := var_0_lst;
				store_GLOBALS := var_1_lst;
				store_TABLES := var_2_lst;
				store_MEMS := var_3_lst;
				store_ELEMS := var_4_lst;
				store_DATAS := var_5_lst
			|}) as s.
			eapply mk_Extend_store; eq_to_prop; simpl; eauto; (try (rewrite update_holds_upto_lt; eapply holds_upto_lt_refl)).
			- eapply LemGlobalSame; subst; eauto.
			- eapply LemMemSame; subst; eauto.
			- eapply LemTableSame; subst; eauto.
			- eapply LemFuncSame; subst; eauto.
			- eapply LemDataSame; subst; eauto.
			- rewrite list_update_length_func. rewrite update_holds_upto_lt; by eapply holds_upto_lt_refl.
			- subst.
				eapply elem_drop_elem_extension; eauto.
		}
		split; auto.
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst := globalinst_lst)
			(tableinst_lst := tableinst_lst)
			(meminst_lst := meminst_lst)
			(eleminst_lst := list_update_func (store_ELEMS s) ea
				[eta set eleminst_REFS (fun=> [])])
			(datainst_lst := datainst_lst)
			(memtype_lst := memtype_lst)
			(functype_lst := functype_lst)
			(tabletype_lst := tabletype_lst)
			(datatype_lst := datatype_lst)
			(elemtype_lst := elemtype_lst)
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply Extend_store_funcinsts; eauto |
				eapply Extend_store_tableinsts; eauto |
				eapply Extend_store_globalinsts; eauto |
				eapply Extend_store_meminsts; eauto |
				eapply Extend_store_eleminsts; eauto |
				eapply Extend_store_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func; eauto.
		- eapply construct_eleminsts; subst; eauto.
	}
	{ (* Store None *)
		(* destruct_all; subst. *)
		invert_ais_typing.
		resolve_all_pt.

		simpl.

		assert (|nbytes_ nt c| = ((!( res_size (valtype_numtype nt))) / 8)%Q) as Heqlen.
		{
			(* fun_nbytes_ not implemented *)
			by eapply nbytes_len'.
		}

		remember ((proj_uN_0 (the (proj_num__0 i)))) as v_i.
		remember (proj_uN_0 (OFFSET ao)) as v_ao.
		remember (((MEMS (frame_MODULE v_f)) [| 0 |])) as ma.
		remember  (s <| store_MEMS :=
			list_update_func (store_MEMS s) ((MEMS (frame_MODULE v_f)) [|mk_uN 0 :> N|])
			(λ var_1 : meminst,
			var_1 <| BYTES :=
			list_slice_update (BYTES var_1) ((!( proj_num__0 i) :> N) + (OFFSET ao :> N))
			((the (res_size (valtype_numtype nt))) / 8%Q)%Q (nbytes_ nt c) |>) |>
		) as s'.

		assert (
			(ma < (|(store_MEMS s)|))%BN /\
			exists v_mt v_mt' v_b,
				((lookup_total (store_MEMS s) ma) =
					{| meminst_TYPE := v_mt; BYTES := v_b |}) /\
				((Memtype_sub v_mt v_mt'))
				)
			as [HLen [v_mt [v_mt' [v_b [HLookup HRefok]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.

			eapply Forall2_size2 in HIT.
			2: ineq_to_propH H2; apply H2.
			destruct HIT as [v_mt [b_lst [HBound [HLookup HSub]]]].
			rewrite -Heqma in HBound.
			split; auto.

			rewrite -Heqma in HLookup.
			inversion HSub; subst.
			by exists v_mt, (nth default_val (context_MEMS C') 0), b_lst.
		}

		assert (Extend_store s s').
		{
			inversion HWfS; subst.
			remember ({|
				store_FUNCS := var_0_lst;
				store_GLOBALS := var_1_lst;
				store_TABLES := var_2_lst;
				store_MEMS := var_3_lst;
				store_ELEMS := var_4_lst;
				store_DATAS := var_5_lst
			|}) as s.
			eapply mk_Extend_store; eq_to_prop; simpl; eauto; (try (rewrite update_holds_upto_lt; eapply holds_upto_lt_refl)).
			- eapply LemGlobalSame; subst; eauto.
			- rewrite list_update_length_func; rewrite update_holds_upto_lt; by eapply holds_upto_lt_refl.
			- eapply store_none_mem_extension with (v_nb := (nbytes_ nt c)); subst; eauto. eapply nbytes__is_wf; eauto.
			- eapply LemTableSame; subst; eauto.
			- eapply LemFuncSame; subst; eauto.
			- eapply LemDataSame; subst; eauto.
		}
		split; auto.
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst := globalinst_lst)
			(tableinst_lst := tableinst_lst)
			(meminst_lst := list_update_func (store_MEMS s) ((MEMS (frame_MODULE v_f)) [|mk_uN 0 :> N|])
			(λ var_1 : meminst,
			var_1 <| BYTES :=
			list_slice_update (BYTES var_1) ((!( proj_num__0 i) :> N) + (OFFSET ao :> N))
			((the (res_size (valtype_numtype nt))) / 8%Q)%Q (nbytes_ nt c) |>))
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			(memtype_lst := memtype_lst)
			(functype_lst := functype_lst)
			(tabletype_lst := tabletype_lst)
			(datatype_lst := datatype_lst)
			(elemtype_lst := elemtype_lst)
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply Extend_store_funcinsts; eauto |
				eapply Extend_store_tableinsts; eauto |
				eapply Extend_store_globalinsts; eauto |
				eapply Extend_store_meminsts; eauto |
				eapply Extend_store_eleminsts; eauto |
				eapply Extend_store_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func; eauto.
		- {
			rewrite -Heqlen.
			eapply construct_meminsts; subst; eauto.
			eapply nbytes__is_wf; eauto.
		}
	}
	{ (* Store Some *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		simpl.

		assert (|(ibytes_ v_n (wrap__ (the (res_size (valtype_Inn v_Inn))) v_n (the (proj_num__0 c))))| = (v_n / 8%Q)%Q)
			as Heqlen.
		{
			(* fun_ibytes_ wrap__ not implemented *)
			by eapply ibytes_len'.
		}

		remember ((proj_uN_0 (the (proj_num__0 i)))) as v_i.
		remember (proj_uN_0 (OFFSET ao)) as v_ao.
		remember ((lookup_total (MEMS (frame_MODULE v_f)) 0)) as ma.
		remember  (s <| store_MEMS :=
			list_update_func (store_MEMS s) ma
				(λ v_1,
				v_1 <| BYTES := list_slice_update (BYTES v_1) (v_i + v_ao) (v_n / 8%Q)%Q
				(ibytes_ v_n (wrap__ (the (res_size (valtype_Inn v_Inn))) v_n (the (proj_num__0 c)))) |>)	
		|> ) as s'.
		rewrite -Heqlen in Heqs'.

		assert (
			(ma < (|(store_MEMS s)|))%BN /\
			exists v_mt v_mt' v_b,
				((lookup_total (store_MEMS s) ma) =
					{| meminst_TYPE := v_mt; BYTES := v_b |}) /\
				((Memtype_sub v_mt v_mt'))
				)
			as [HLen [v_mt [v_mt' [v_b [HLookup HRefok]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.

			eapply Forall2_size2 in HIT.
			2: ineq_to_propH H3; apply H3.
			destruct HIT as [v_mt [b_lst [HBound [HLookup HSub]]]].
			rewrite -Heqma in HBound.
			split; auto.
			rewrite /lookup_total in HLookup.

			inversion HSub; subst.
			by exists v_mt, (nth default_val (context_MEMS C') 0), b_lst.
		}

		assert (Extend_store s s').
		{
			inversion HWfS; subst.
			remember ({|
				store_FUNCS := var_0_lst;
				store_GLOBALS := var_1_lst;
				store_TABLES := var_2_lst;
				store_MEMS := var_3_lst;
				store_ELEMS := var_4_lst;
				store_DATAS := var_5_lst
			|}) as s.
			eapply mk_Extend_store; eq_to_prop; simpl; eauto; (try (rewrite update_holds_upto_lt; eapply holds_upto_lt_refl)).
			- eapply LemGlobalSame; subst; eauto.
			- rewrite list_update_length_func; rewrite update_holds_upto_lt; by eapply holds_upto_lt_refl.
			- eapply store_none_mem_extension with (v_nb := (ibytes_ v_n (wrap__ (!( res_size (valtype_Inn v_Inn))) v_n (!( proj_num__0 c))))); subst; eauto. 
				{ 
				eapply ibytes__is_wf; eauto.
				eapply wrap___is_wf; eauto.
				inversion H2; eq_to_prop; subst; eauto; try discriminate.
				- destruct v_Inn; destruct v_Inn0; subst; try discriminate; eauto.
				- destruct v_Inn; destruct v_Fnn; try discriminate.
			}
			- eapply LemTableSame; subst; eauto.
			- eapply LemFuncSame; subst; eauto.
			- eapply LemDataSame; subst; eauto.
			- rewrite -Heqlen in HWfStore'; eauto. 
		}
		rewrite Heqlen in Heqs'.
		split; auto.
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst := globalinst_lst)
			(tableinst_lst := tableinst_lst)
			(meminst_lst := list_update_func (store_MEMS s) ma
				(λ v_1 : meminst,
				v_1 <| BYTES := list_slice_update
					(BYTES v_1)
					(v_i + v_ao)
					(v_n / 8%Q)%Q
					(ibytes_ v_n (wrap__ (the (res_size (valtype_Inn v_Inn))) v_n (the (proj_num__0 c)))) |>))
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			(memtype_lst := memtype_lst)
			(functype_lst := functype_lst)
			(tabletype_lst := tabletype_lst)
			(datatype_lst := datatype_lst)
			(elemtype_lst := elemtype_lst)
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply Extend_store_funcinsts; eauto |
				eapply Extend_store_tableinsts; eauto |
				eapply Extend_store_globalinsts; eauto |
				eapply Extend_store_meminsts; eauto |
				eapply Extend_store_eleminsts; eauto |
				eapply Extend_store_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func; eauto.
		- {
			rewrite -Heqlen.
			eapply construct_meminsts; subst; eauto.
			{ 
				eapply ibytes__is_wf; eauto.
				eapply wrap___is_wf; eauto.
				inversion H2; eq_to_prop; subst; eauto; try discriminate.
				- destruct v_Inn; destruct v_Inn0; subst; try discriminate; eauto.
				- destruct v_Inn; destruct v_Fnn; try discriminate.
			}
		}
	}
	(* SIMD instructions *)
	1-2: admit.
	{ (* Memory Grow *)
		rename H into HGrow.
		(* rename H2 into Hwfconfig2. *)
		rename H0 into HNotNone.
		clear H2.
		(* destruct_all; subst. *)
		invert_ais_typing.
		resolve_all_pt.
		remember (the (var_0)) as mi.

		clear Hsub Hsub0.

		remember (((MEMS (frame_MODULE v_f)) [| 0 |])) as ma.
		remember (s <| store_MEMS := list_update_func (store_MEMS s) ma (fun=> mi) |>) as s'.

		assert (
			(ma < (|store_MEMS s|))%BN /\
			exists v_mt' (lim_old : Q) v_j v_b,
				((Memtype_sub (PAGE (mk_limits (mk_uN lim_old) v_j)) v_mt')) /\
				(lookup_total (store_MEMS s) ma =
				{| meminst_TYPE := PAGE (mk_limits (mk_uN lim_old) v_j); BYTES := v_b |}) /\
				(mi =
				{| meminst_TYPE := PAGE (mk_limits (mk_uN (lim_old + v_n)%BN) v_j);
				BYTES := v_b ++ list_repeat (mk_byte 0) (v_n * (64 * Ki)%BN)%BN |}) /\
				(lim_old = pagediv v_b) /\
				Forall (fun j : u32 => ((lim_old + v_n)%Q <= (j :> N))%Q) v_j
				)
			as [HLen [v_mt' [lim_old [v_j [v_b [HMemsub [HLookup [HNew [HLimold HRange]]]]]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.
			eapply Forall2_size2 in HIT.
			2: ineq_to_propH H0; apply H0.
			destruct HIT as [v_mt [b_lst [HBound [HLookup HSub]]]].
			rewrite -Heqma in HBound HLookup.
			split; auto.

			eapply s_invert_mems in HStore as [mts HMem].
			eapply Forall2_size in HMem.
			2: apply HBound.
			destruct HMem as [b_lst' [v_n' [v_m [HLookup' [HEq [HEq' HForall']]]]]].
			rewrite HLookup' in HLookup.
			inversion HLookup; clear HLookup; subst.
			

			rewrite /fun_mem in HGrow; inversion HGrow; eq_to_prop; subst; clear HGrow.
			2: by destruct HNotNone.
			clear H5 H6.
			rewrite -H in HLookup'.

			injection HLookup' as ?; subst.

			exists (context_MEMS C' [| 0 |]),
				(pagediv b_lst),
				(option_map [eta mk_uN] v_m),
				(b_lst).
			ineq_to_propH H0.
			rewrite -H2 in HEq.
			
			inversion HEq; subst.
			inversion HSub; subst.
			rewrite -H2 in H6.
			split; auto.
			split; auto.
			split; auto.
			simpl.
			repeat rewrite Z.mul_1_r.
			rewrite Zdiv.Z_div_plus_full; try done.
			fold (Z.of_N (65536)).
			rewrite -Znat.N2Z.inj_div.
			rewrite -Znat.N2Z.inj_add.
			repeat rewrite Znat.N2Z.id.
			reflexivity.
			split; auto.

			destruct v_m; eauto.
			eapply Forall_cons; eauto.
			inversion H3; subst.
			move/Qle_bool_iff in H9.
			unfold pagediv.
			apply H9.
		}

		assert (Extend_store s s').
		{
			inversion HWfS; subst.
			remember ({|
				store_FUNCS := var_0_lst;
				store_GLOBALS := var_1_lst;
				store_TABLES := var_2_lst;
				store_MEMS := var_3_lst;
				store_ELEMS := var_4_lst;
				store_DATAS := var_5_lst
			|}) as s.
			eapply mk_Extend_store; eq_to_prop; simpl; eauto; (try (rewrite update_holds_upto_lt; eapply holds_upto_lt_refl)).
			- eapply LemGlobalSame; subst; eauto.
			- rewrite list_update_length_func; rewrite update_holds_upto_lt; by eapply holds_upto_lt_refl.
			- rewrite HNew. eapply memory_grow_mem_extension with (v_n := v_n); eauto.
				+ by rewrite Heqs.
				+ {
					clear -HWfConfig' HStore HNew.
					inversion HWfConfig'; subst.
					inversion H1; subst.
					inversion H3; subst; eauto.
					rewrite HNew in H12.
					apply H12.
				}
				+ apply pagediv_ge_0.
				+ rewrite -(Znat.N2Z.id v_n).
					rewrite -Znat.Z2N.inj_add.
					rewrite Qfloor_add_Z.
					rewrite (Znat.N2Z.id v_n).
					reflexivity.
					apply pagediv_ge_0_Z.
					apply Znat.N2Z.is_nonneg.

			- eapply LemTableSame; subst; eauto.
			- eapply LemFuncSame; subst; eauto.
			- eapply LemDataSame; subst; eauto.
		}
		split; auto.
		
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst := globalinst_lst)
			(tableinst_lst := tableinst_lst)
			(meminst_lst := list_update_func (store_MEMS s) ma
				(λ _,
				{| meminst_TYPE := PAGE (mk_limits (mk_uN (lim_old + v_n)%BN) (v_j));
				BYTES := v_b ++ list_repeat (mk_byte 0) (v_n * (64 * Ki)%BN)%BN |}))
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			(memtype_lst := list_update_func memtype_lst ma
				(λ _, PAGE (mk_limits (mk_uN (lim_old + v_n)%BN) (v_j))))
			(functype_lst := functype_lst)
			(tabletype_lst := tabletype_lst)
			(datatype_lst := datatype_lst)
			(elemtype_lst := elemtype_lst)
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply Extend_store_funcinsts; eauto |
				eapply Extend_store_tableinsts; eauto |
				eapply Extend_store_globalinsts; eauto |
				eapply Extend_store_meminsts; eauto |
				eapply Extend_store_eleminsts; eauto |
				eapply Extend_store_datainsts; eauto |
				eauto
			].
		- rewrite !list_update_length_func /=; eauto.
		- {
			eapply construct_meminsts_grow; subst; eauto.
			{
					clear -HWfConfig' HStore HNew.
					inversion HWfConfig'; subst.
					inversion H1; subst.
					inversion H3; subst; eauto.
					rewrite HNew in H12.
					apply H12.
			}
		}
		- by rewrite HNew.
		- {
			(* TODO - think about Wfness here - Is this correct? *)
			clear -HWfConfig' H16 H6 HLen HNew.
			simpl in HLen.

			inversion H16; subst.
			inversion HWfConfig'; subst.
			inversion H1; subst.
			inversion H3; subst.
			eapply (wf_memoryinsts_preserves _ _ _ H6) in H9; eauto.
			clear -H9 H6 H19 HLen HNew.
			eapply list_update_func_preserves_prop; eauto.
			eapply list_update_func_forall_inv in H19; eauto.
			rewrite HNew in H19.
			inversion H19; subst; eauto.
		}
		- {
			inversion HWfConfig'; subst.
			inversion H20; subst.
			by rewrite HNew in H22.			
		}
	}
	{ (* Data Drop *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		remember ((proj_uN_0 x)) as i.
		remember ((lookup_total (DATAS (frame_MODULE v_f)) i)) as da.
		remember (s <| store_DATAS :=
			list_update_func (store_DATAS s) da [eta set datainst_BYTES (fun=> [])] |>) as s'.

		assert (
			(|DATAS (frame_MODULE v_f)| = |(context_DATAS C')|) /\
			(da < (|(store_DATAS s)|))%BN /\
			exists v_b,
				((lookup_total (store_DATAS s) da) =
					{| datainst_BYTES := v_b |})
				)
			as [HCLen [HLen [v_b HLookup]]].
		{
			eapply minst_invert_datas in HIT; eauto.
			destruct_all.
			split. auto.

			eapply Forall_size in H3.
			2: {
				rewrite H2.
				ineq_to_propH H1; apply H1.
			}
			destruct_all.
			list_to_seq.
			split. by rewrite Heqda.
			exists extr.
			by rewrite Heqda.
		}

		assert (Extend_store s s').
		{
			inversion HWfS; subst.
			remember ({|
				store_FUNCS := var_0_lst;
				store_GLOBALS := var_1_lst;
				store_TABLES := var_2_lst;
				store_MEMS := var_3_lst;
				store_ELEMS := var_4_lst;
				store_DATAS := var_5_lst
			|}) as s.
			eapply mk_Extend_store; eq_to_prop; simpl; eauto; (try (rewrite update_holds_upto_lt; eapply holds_upto_lt_refl)).
			- eapply LemGlobalSame; subst; eauto.
			- eapply LemMemSame; subst; eauto.
			- eapply LemTableSame; subst; eauto.
			- eapply LemFuncSame; subst; eauto.
			- rewrite list_update_length_func; rewrite update_holds_upto_lt; apply holds_upto_lt_refl.
			- eapply data_drop_data_extension; subst; eauto.
		}
		split; auto.
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst := globalinst_lst)
			(tableinst_lst := tableinst_lst)
			(meminst_lst := meminst_lst)
			(eleminst_lst := eleminst_lst)
			(datainst_lst := list_update_func (store_DATAS s) da
				[eta set datainst_BYTES (fun=> [])])
			(memtype_lst := memtype_lst)
			(functype_lst := functype_lst)
			(tabletype_lst := tabletype_lst)
			(datatype_lst := datatype_lst)
			(elemtype_lst := elemtype_lst)
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply Extend_store_funcinsts; eauto |
				eapply Extend_store_tableinsts; eauto |
				eapply Extend_store_globalinsts; eauto |
				eapply Extend_store_meminsts; eauto |
				eapply Extend_store_eleminsts; eauto |
				eapply Extend_store_datainsts; eauto |
				eauto
			].
		- by rewrite list_update_length_func.
		- eapply construct_datainsts; subst; eauto.
	}
Admitted.

Lemma reduce_inst_unchanged: forall s f ais s' f' ais',
	Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
	frame_MODULE f = frame_MODULE f'.
Proof.
	move => s f ais s' f' ais' HReduce.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent ais. generalize dependent ais'.
	induction HReduce; try intros; try (induction z); try induction z'; try (apply config_same in Heqc1;
	apply config_same in Heqc2; destruct Heqc1 as [? [? ?]];
	destruct Heqc2 as [? [? ?]]; subst => //);
	eapply IHHReduce; eauto.
Qed.

Lemma t_read_preservation: forall v_s v_f v_ais v_ais' v_C v_C' t1s t2s,
	wf_config (mk_config (mk_state v_s v_f) v_ais) ->
	Step_read (mk_config (mk_state v_s v_f) v_ais) v_ais' ->
	Store_ok v_s ->
	Moduleinst_ok v_s (frame_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) (context_LOCALS v_C') (LOCALS v_f) ->
	inst_match v_C v_C' ->
	Instrs_ok2 v_s v_C' v_ais (t1s :-> t2s) ->
	Instrs_ok2 v_s v_C' v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_ais' v_C v_C' t1s t2s HWfConfig HReduce HST HIT1 HValOK Him HType.
	
	eapply Step_read_is_wf in HWfConfig as HWfais'; eauto.

	eapply ainstrs_ok_context_store_wf in HType as HWf; destruct HWf as [HWfC [HWfS HWfais]].
	move: v_C v_C' t1s t2s HIT1 HValOK Him HType HWfC.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	induction HReduce;
	move => v_C v_C' tx ty HIT1 HValOK Him HType HWfC; decomp; destruct z; try eauto;
	eq_to_prop;
	inv_Forall HWfais';
	try (apply config_same in Heqc1; destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; subst => //).
	all: try by eapply construct_ais_trap.
	{ (* Block *)
		typing_inversion HType.
		typing_inversion H2.
		simpl in Hai;
		extract_premise.
		vals_typing_inversion H1.

		assert (extr = t_1_lst /\ extr0 = t_2_lst) as [He1 He2]. {
			by eapply bt_inversion; eauto.
		}
		subst.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub0) in Hsub
		as [Hsubi Hsubs].
		2: {
			eapply Forall2_seq_size in Hforall.
			rewrite -H0 in Hforall. auto.
		}

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single with (ts1 := []) (ts2 := t_2_lst).
		2: auto.
		eapply label; eauto.
		{ 
			simpl. rewrite ais_empty_typing.
			split; auto.
			split; auto. 
			eapply resulttype_sub_refl. 
		}

		eapply construct_ais_compose.
		{
			eapply construct_ais_vals; eauto.
			- destruct v_C'; simpl. unfold _append. unfold Append_context. unfold _append_context. simpl.
				econstructor; eauto; inversion HWfC; subst; eauto.
			by eapply instrtype_sub_refl.
		}
		eapply construct_ais_instrtype_sub.
		{
			apply construct_instrs_from_ais; eauto.
		}
		by eapply instrtype_sub_iff_resulttype_sub'.
		econstructor; eauto.
	}
	{ (* Loop *)
		typing_inversion HType.
		typing_inversion H2.
		simpl in Hai;
		extract_premise.
		vals_typing_inversion H1.

		assert (extr = t_1_lst /\ extr0 = t_2_lst) as [He1 He2]. {
			by eapply bt_inversion; eauto.
		}
		subst.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub0) in Hsub
		as [Hsubi Hsubs].
		2: {
			eapply Forall2_seq_size in Hforall.
			rewrite -H0 in Hforall. auto.
		}

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single with (ts1 := []) (ts2 := t_2_lst).
		2: auto.
		eapply label; auto.
		{	
			simpl.
			eapply construct_ais_typing_single.
			inv_Forall HWfais.
			eapply plain with (v_instr := LOOP bt instr_lst); eauto.
			econstructor; eauto.
			- inversion HP0; subst; econstructor; eauto.
			- econstructor; eauto.
			- inversion HP0; subst; econstructor; eauto.
		}
		{
			eapply construct_ais_compose.
			{
				eapply construct_ais_vals; eauto.
				- destruct v_C'; simpl. unfold _append. unfold Append_context. unfold _append_context. simpl.
					econstructor; eauto; inversion HWfC; subst; eauto.
				eapply instrtype_sub_iff_resulttype_sub.
				eapply Hsubs.
			}
			eapply construct_ais_instrtype_sub.
			{
				apply construct_instrs_from_ais; eauto.
			}
			by eapply instrtype_sub_refl.
		}
		econstructor; eauto.
	}
	{ (* Call *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: eapply Hsub.
		Opaque instrtype_sub.
		eapply minst_invert_funcs in HIT1; eauto.
		eapply Forall2_size in HIT1.
		2: ineq_to_propH H; apply H.
		destruct_all.
		econstructor; eauto; try by econstructor.
		rewrite /fun_funcaddr.
		eapply externtype_func_eq in H5; subst.
		rewrite H0 in H4.		

		remember ({| funcinst_TYPE := extr :-> extr0; funcinst_MODULE := extr1; CODE := extr2 |}) as v_fi.
		assert (funcinst_TYPE v_fi = extr :-> extr0). { by subst. }
		rewrite -H3.

		econstructor; eq_to_prop; eauto; try by econstructor.
		ineq_to_prop.
		apply H2.
	}
	{ (* Call_indirect *)
		rewrite /fun_table /= in H H1.
		rewrite /fun_funcinst /= in H2.
		rewrite /fun_type /fun_funcinst /= in H3.

		invert_ais_typing.
		resolve_all_pt.
		join_subtyping_le Hsub0 Hsub.

		pose proof HIT1 as HIT1_0.
		eapply minst_invert_tables in HIT1; eauto.
		eapply Forall2_size2 in HIT1.
		2: ineq_to_propH H5; apply H5.
		destruct_all.

		eapply minst_invert_functypes in HIT1_0; eauto.
		rewrite -HIT1_0 H9 in H3.

		rewrite H11 /= in H H1.

		eapply s_invert_funcs in HST as [fts HFunc].
		ineq_to_propH H2.
		eapply Forall2_size in HFunc.
		2: apply H2.
		destruct_all.

		construct_ais_typing.
		econstructor; eauto; try by econstructor.

		rewrite H3.
		econstructor; eauto; try by econstructor.
		
		ineq_to_prop; eauto.
	}
	{ (* Call_addr *)
		typing_inversion HType.
		vals_typing_inversion H1.
		typing_inversion H3.
		simpl in Hai;
		extract_premise.
		eapply Externaddr_invert_funcs in H3;
		destruct H3 as [xt [v_funcinst [HBound [HEq [HEq' [HWfExt HExtSub]]]]]].
		eq_to_prop.
		inversion HExtSub; subst; clear H3 H8 H10 H9 ft_1.
		eapply externtype_func_eq in HExtSub; subst.

		unfold fun_funcinst in *.
		rewrite H0 in HExtSub.
		inversion HExtSub; subst; clear HExtSub.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub) in Hsub0
		as [Hsub0 Hsubs].
		2: {
			eapply Forall2_seq_size in Hforall.
			rewrite -H7 in Hforall.
			auto.
		}
		assert (v_ts = extr). {
			eapply Vals_ok_non_bot in Hforall as Hnonbot.
			eapply (resulttype_sub_non_bot _ _ Hnonbot) in Hsubs; subst.
			auto.
		}
		subst.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: eapply Hsub0.

		invert_storeok HST.
		eapply Forall2_size in HFunc.
		simpl in *.
		2: apply HBound.
		rewrite H0 in HFunc.
		inversion HFunc; subst.

		eapply Instr_ok2__frame with (C' := prepend_local C (extr ++ t_lst)); eauto; try by econstructor.
		3: { 
			econstructor; apply Forall_app; split; inversion H15; subst; eauto.
		}

		
		econstructor; eauto; try by econstructor.
		{
			eq_to_prop.
			repeat rewrite sizecat'.
			rewrite H7.
			rewrite N.add_cancel_l.
			f_equal.
			rewrite size_map; eauto.
		}
		{
			apply Forall2_app; eauto.

			clear -HWfS H2.
			induction t_lst => //=.
			apply Forall2_cons; eauto.
			-
				destruct a; simpl; try econstructor; eauto.
				- econstructor; econstructor; eq_to_prop; eauto; done.
				- econstructor; econstructor; eq_to_prop; eauto; done.
				- econstructor; econstructor; eq_to_prop; eauto; econstructor. econstructor. simpl. eauto.
				- econstructor; econstructor; eq_to_prop; eauto; econstructor. econstructor. simpl. eauto.
				-  econstructor; econstructor; eq_to_prop; eauto; econstructor.
				- fold (val_ref (ref_REF_NULL FUNCREF)).
					fold (valtype_reftype FUNCREF).
					econstructor; eauto.
					econstructor; eauto.
				- fold (val_ref (ref_REF_NULL EXTERNREF)).
					fold (valtype_reftype EXTERNREF).
					econstructor; eauto.
					econstructor; eauto.
				- inversion H2; subst. discriminate.
			- apply IHt_lst. by inversion H2.
		}

		inversion HP; subst; clear HP.
		assert (wf_context (prepend_return (prepend_local C (extr ++ t_lst)) extr0)) as HWfCNew. {
			repeat apply wf_context_app; try by econstructor; eauto.
			apply H15.
		}
		

		(* Expr_ok2 *)
		eapply mk_Expr_ok2 with (C := prepend_return (prepend_local C (extr ++ t_lst)) extr0); eauto.
		{
			inv_Forall H17.
			eapply construct_ais_typing_single.
			econstructor; eauto; try by econstructor.
			{
				simpl.
				eapply ais_empty_typing.
				split; eauto.
				split. apply HWfStore0.
				apply resulttype_sub_refl.
			}

			eapply construct_instrs_from_ais; eauto.
			inversion H13; subst.

			inversion H23; eq_to_prop; subst.
			unfold _append, Append_context, _append_context.
			simpl.
			unfold _append, Append_List_, Append_Option; simpl.
			unfold _append, Append_context, _append_context, _append, Append_List_, Append_Option, option_append in H12.
			simpl in H12.
			assert (injective (ListDef.map [eta LOCAL])) as map_local_inj.
			{
				eapply inj_map.
				unfold injective.
				move=> x1 x2 Hconstructor.
				by inversion Hconstructor.
			}
			eapply map_local_inj in H3; subst.
			auto.
		}
	}
	{ (* Ref_func *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise. subst.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: eapply Hsub.
		unfold fun_funcaddr in *; subst.
		eapply minst_invert_funcs in HIT1; eauto.
		eapply Forall2_size2 in HIT1 as HFunc.
		2: ineq_to_propH H1; apply H1.
		destruct_all.
		fold (admininstr_ref (REF_FUNC_ADDR ((FUNCS (frame_MODULE v_f)) [|x :> N|]))).
		fold (valtype_reftype (FUNCREF)).
		eapply Instr_ok2__ref; eauto.
		econstructor; eq_to_prop; eauto.
		econstructor; eauto; try by econstructor.
		- by ineq_to_prop.
		- econstructor.
	}
	{ (* Local_get *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise. subst.

		eapply Forall2_size in HValOK.
		2: ineq_to_propH H1; apply H1.

		destruct v_f; destruct v_C'; destruct v_C; destruct v_s;
		unfold inst_match in Him; destruct_all;
		subst; simpl in *; subst.
		invert_moduleinstok HIT1; eq_to_prop.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: eapply Hsub.
		inversion HValOK; subst; unfold admininstr_val.
		{ (* CONST case *)

			eapply plain with (v_instr := (CONST nt c_t)); eauto.
			econstructor; eauto.
			all: rewrite -H in HP; inversion HP; subst; econstructor; eauto.
		}
		{ (* VCONST case *)
			eapply plain with (v_instr := (VCONST vt c_t)); eauto.
			destruct vt.
			econstructor; eauto.
			all: rewrite -H in HP; inversion HP; subst; econstructor; eauto.
		}
		rewrite -H in HP.
		destruct r; inversion HP; subst.
		{ (* NULL case *)
			simpl.
			fold (admininstr_ref (ref_REF_NULL v_reftype)).
			constructor; eauto.
		}
		{ (* FUNC ADDR *)
			simpl.
			fold (admininstr_ref (REF_FUNC_ADDR v_funcaddr)).
			constructor; eauto.
		}
		{
			simpl.
			fold (admininstr_ref (REF_HOST_ADDR v_hostaddr)).
			constructor; eauto.
		}
	}
	{ (* Global_get *)
		rewrite /fun_global.
		invert_ais_typing.
		resolve_all_pt.

		eapply minst_invert_globals in HIT1; eauto.
		eapply Forall2_size2 in HIT1.
		2: ineq_to_propH H1; apply H1.
		destruct_all.

		rewrite H4 /=.

		eapply s_invert_globals in HST as [gts HGlobal2].
		eapply Forall2_size in HGlobal2.
		2: apply H2.

		destruct_all.
		rewrite H4 in H3.
		injection H3 as ?; subst.
		rewrite H7 in H4.

		apply externtype_global_eq in H5; subst.
		rewrite H0 in H5.
		rewrite H7 in H5.
		injection H5 as ?; subst.

		construct_ais_typing.
		by eapply construct_ai_val.
	}
	{ (* Table_get *)
		rewrite /fun_table /=.
		rewrite /fun_table in H.
		invert_ais_typing.
		resolve_all_pt.
		join_subtyping_eq Hsub0 Hsub.

		eapply minst_invert_tables in HIT1; eauto.
		eapply Forall2_size2 in HIT1.
		2: ineq_to_propH H2; apply H2.
		destruct_all.

		rewrite H6 /= in H.
		rewrite H6 /=.

		eapply s_invert_tables in HST as [tbts HTableinst].
		eapply Forall2_size in HTableinst.
		2: apply H3.
		destruct HTableinst as [ref_lst [v_m [rt [HLookup [HLookup' [HTbtok HRefok]]]]]].
		rewrite H6 in HLookup.
		injection HLookup as ?; subst.

		eapply Forall_size in HRefok; eauto.
		2: ineq_to_propH H; apply H.


		construct_ais_typing.
		eapply construct_ai_ref; eauto.

		rewrite H4 in H7.
		rewrite HLookup' in H7.
		inversion H7; subst; clear H7.
		inversion H9; subst; clear H9.
		apply HRefok.
	}
	{ (* Table_size *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise; subst.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: eapply Hsub.
		
		eapply plain with (v_instr := (CONST I32 (mk_num__0 Inn_I32 (mk_uN
		(|(REFS (fun_table (mk_state v_s v_f) x))|))))); eauto.
		econstructor; eauto.
		
		all: inversion HP; econstructor; eauto.
	}
	{ (* Table_fill *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.
		typing_inversion H1.

		simpl in Hai; extract_premise.

		typing_inversion H3.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.
		
		typing_inversion H2.
		simpl in Hai; extract_premise.
		rewrite -(cats0 [valtype_I32; t]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		simpl in Haifinal; extract_premise.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsubfinal
		as [Hsub2 Hsubs].
		2: auto.

		eapply ais_empty_typing.
		split; eauto.
		split; eauto.
		by eapply instrtype_sub_empty.
	}
	{ (* Table_fill succ *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hsub into Hsubfinal.
		rename Hai into Haifinal.
		typing_inversion H2.

		simpl in Hai; extract_premise.
		pose proof H4 as H4_0.

		typing_inversion H4.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		pose proof Hsub0 as Hsub0_0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.
		
		typing_inversion H3.
		simpl in Hai; extract_premise.
		rewrite -(cats0 [valtype_I32; t]) in Hsub0.
		pose proof Hsub1 as Hsub1_0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.
		rewrite cats0 in Hsub0.

		simpl in Haifinal; extract_premise.
		pose proof Hsubfinal as Hsubfinal_0.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsubfinal
		as [Hsub2 Hsubs].
		2: auto.

		unfold_instrtype_sub Hsub0.
		assert ([valtype_I32; t] = ts12_sup).
		{
			eapply resulttype_sub_non_bot.
			constructor. discriminate.
			constructor. eapply Val_ok_non_bot; eauto.
			constructor. auto.
		}
		eapply resulttype_sub_empty in Hsub4.
		subst.

		rewrite !cats0 in Hsub.

		pose proof Hsub as Hsub_0.
		unfold_instrtype_sub Hsub.
		eapply resulttype_sub_empty in Hsub4; subst.
		rewrite cats0 in Hsub_0.
		remember (mk_num__0 Inn_I32 (mk_uN ((!( proj_num__0 i) :> N) + 1)%BN)) as c.
		remember (mk_num__0 Inn_I32 (mk_uN (v_n - 1%num)%Z)) as n_const.
		assert ([admininstr_CONST I32 i; admininstr_val v_val; admininstr_TABLE_SET x;
			admininstr_CONST I32 c; admininstr_val v_val;
			admininstr_CONST I32 n_const; admininstr_TABLE_FILL x] =
			[admininstr_CONST I32 i; admininstr_val v_val; admininstr_TABLE_SET x] ++
			[admininstr_CONST I32 c; admininstr_val v_val;
			admininstr_CONST I32 n_const; admininstr_TABLE_FILL x]) as Happ. { auto. }

		rewrite Happ.
		rewrite !cats0.
		eapply construct_ais_compose.
		{
			eapply construct_ais_compose with
				(v_ais1 := [admininstr_CONST I32 i; admininstr_val v_val]).
			{
				eapply construct_ais_compose with
					(v_ais1 := [admininstr_CONST I32 i]).
				{
					eapply construct_ais_subtyping.
					eapply construct_ais_typing_single.
					2: eapply Hsub_0.
					eapply plain with (v_instr := (CONST I32 i)); eauto.
					econstructor; eauto. 
					econstructor; eauto.
					econstructor; eauto.
				}
				eapply H4_0.
			}
			inv_Forall Hrest0.
			inversion HP6; subst.

			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply plain with (v_instr := (TABLE_SET x)); eauto; try by econstructor.
			econstructor; eq_to_prop; eauto; try by econstructor.
			- ineq_to_prop. rewrite -H6. apply wf_context_tab; eauto.
			{
				eapply instrtype_sub_trans with (tf2 := ([valtype_I32; t] :-> [])).
				{
					eapply instrtype_sub_iff_resulttype_sub'.
					eapply resulttype_sub_app' with
					(ts1_sub := [valtype_I32; t])
					(ts1 := [valtype_I32; valtype_reftype extr])
					in Hsubs as [Hsubs1 Hsubs2]; auto.
				}
				by eapply instrtype_sub_add_same.
			}
		}
		eapply construct_ais_compose with
			(v_ais1 := [admininstr_CONST I32 c; admininstr_val v_val;
		admininstr_CONST I32 n_const]).
		{
			eapply construct_ais_compose with
			(v_ais1 := [admininstr_CONST I32 c; admininstr_val v_val]).
			{
				eapply construct_ais_compose with
			(v_ais1 := [admininstr_CONST I32 c]).
				{
					eapply construct_ais_subtyping.
					eapply construct_ais_typing_single.
					eapply plain with (v_instr := (CONST I32 c)); eauto.
					econstructor; eauto.
					- inv_Forall Hrest. by inversion HP8; econstructor.
					- inv_Forall Hrest. by inversion HP8; econstructor.
					- by eapply instrtype_sub_add_same.
				}
				eapply construct_ais_subtyping.
				eapply construct_ais_typing_single.
				eapply construct_ai_val; eauto.

				rewrite -(cats0 (ts_sub ++ [valtype_I32])).
				by eapply instrtype_sub_add_same.
			}
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply plain with (v_instr := (CONST I32
				n_const
			)); eauto.
			econstructor; eauto.
			- inv_Forall Hrest0. by inversion HP9; econstructor.
			- inv_Forall Hrest0. by inversion HP9; econstructor.
			rewrite -(cats0 ((ts_sub ++ [valtype_I32]) ++ [t])).
			by eapply instrtype_sub_add_same.
		}
		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		eapply plain with (v_instr := (TABLE_FILL x)); eauto.
		econstructor; eq_to_prop; eauto.
		- inv_Forall Hrest0. by inversion HP10; econstructor.
		- ineq_to_prop. rewrite -H6. apply wf_context_tab; eauto.
		- inv_Forall Hrest0. by inversion HP10; econstructor. 

		eapply instrtype_sub_trans.
		eapply Hsubfinal_0.

		eapply instrtype_sub_iff_resulttype_sub'.
		unfold_instrtype_sub Hsub1_0; eapply resulttype_sub_empty in Hsub4; subst.

		eapply resulttype_sub_app.
		2: eapply Hsub7.
		rewrite -catA; simpl.
		rewrite H5.
		by rewrite cats0.
	}
	{ (* Table_copy *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [valtype_I32; valtype_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		simpl in Haifinal; extract_premise.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub1) in Hsubfinal.

		eapply ais_empty_typing.
		split; eauto.
		split; eauto.
		by eapply instrtype_sub_empty.
	}
	{ (* Table_copy le *)
		invert_ais_typing.
		resolve_all_pt.

		join_subtyping_ge Hsub Hsub0.
		join_subtyping_ge Hsubi Hsub2.
		join_subtyping_eq Hsubi0 Hsub1.

		eapply construct_ais_subtyping; eauto.

		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := TABLE_GET y); eauto.
			econstructor; eq_to_prop; eauto.
			- by inversion HP1; econstructor.
			- ineq_to_prop. rewrite -H10. apply wf_context_tab; eauto.
			eexists [valtype_I32],[valtype_I32],[valtype_I32],[valtype_reftype extr].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := TABLE_SET x); eauto.
			econstructor; eq_to_prop; eauto.
			- inv_Forall Hrest1. by inversion HP7; econstructor.
			- ineq_to_prop. rewrite -H7. apply wf_context_tab; eauto.
			simpl.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP3.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP4.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.	
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP5.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := TABLE_COPY x y); eauto.
			econstructor; eq_to_prop; eauto.
			- by inversion HP6; econstructor.
			- ineq_to_prop. rewrite -H7. apply wf_context_tab; eauto.
			- ineq_to_prop. rewrite -H10. apply wf_context_tab; eauto.
		}
	}
	{ (* Table_copy gt *)
		invert_ais_typing.
		resolve_all_pt.

		join_subtyping_ge Hsub Hsub0.
		join_subtyping_ge Hsubi Hsub2.
		join_subtyping_eq Hsubi0 Hsub1.

		eapply construct_ais_subtyping; eauto.

		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP0.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := TABLE_GET y); eauto.
			econstructor; eq_to_prop; eauto.
			- by inversion HP1; econstructor.
			- ineq_to_prop. rewrite -H10. apply wf_context_tab; eauto.
			eexists [valtype_I32],[valtype_I32],[valtype_I32],[valtype_reftype extr].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := TABLE_SET x); eauto.
			econstructor; eq_to_prop; eauto.
			- by inversion HP2; econstructor.
			- ineq_to_prop. rewrite -H7. apply wf_context_tab; eauto.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP5.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := TABLE_COPY x y); eauto.
			econstructor; eq_to_prop; eauto.
			- by inversion HP6; econstructor.
			- ineq_to_prop. rewrite -H7. apply wf_context_tab; eauto.
			- ineq_to_prop. rewrite -H10. apply wf_context_tab; eauto.
		}
	}
	{ (* Table_init zero *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		simpl in Hai; extract_premise.
		rename Hsub into Hsubfinal.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [valtype_I32; valtype_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub1) in Hsubfinal.

		eapply ais_empty_typing.
		split; eauto.
		split; eauto.
		by eapply instrtype_sub_empty.
	}
	{ (* Table_init succ *)
		invert_ais_typing.
		resolve_all_pt.

		join_subtyping_ge Hsub Hsub0.
		join_subtyping_ge Hsubi Hsub2.
		join_subtyping_eq Hsubi0 Hsub1.

		pose proof HIT1 as HIT1_0.
		eapply minst_invert_elems in HIT1; eauto.
		eapply Forall2_size2 in HIT1.
		pose proof H8 as H8_0.
		2: ineq_to_propH H8; eapply H8.
		destruct_all.

		eapply minst_invert_tables in HIT1_0; eauto.
		eapply Forall2_size2 in HIT1_0.
		2: ineq_to_propH H3; apply H3.
		destruct_all.

		rewrite /fun_elem H14 /=.
		rewrite /fun_elem H14 /= in H.

		eapply Forall_size in H13; eauto.
		2: ineq_to_propH H; apply H.

		remember ((context_ELEMS v_C') [| proj_uN_0 y |])
			as e_t.
		remember ((extr [| proj_uN_0 (!(proj_num__0 i)) |]))
			as e_v.
		rewrite -Heqe_t in H13 H14.

		eapply construct_ais_subtyping; eauto.
		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
		}
		{
			instantiate (1 := [valtype_I32; valtype_reftype e_t]).
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			instantiate (2 := []).
			instantiate (1 := [valtype_reftype e_t]).
			2: {
				eexists [valtype_I32],[valtype_I32],[],[valtype_reftype e_t].
				split; auto.
				split; auto.
				split. eapply resulttype_sub_refl.
				split; eapply resulttype_sub_refl.
			}
			inversion H13.
			{	
				rewrite -H19 in H13.
				subst.
				econstructor; eauto.
			}
			{
				eapply Instr_ok2__ref; eauto.
				econstructor; eauto.
			}
			{
				eapply Instr_ok2__ref; eauto.
				econstructor; eauto.
			}
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := TABLE_SET x); eauto.
			econstructor; eq_to_prop; eauto.
			- by inversion HP1; econstructor.
			- ineq_to_prop. rewrite -H7. apply wf_context_tab; eauto. 
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP2.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP3.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP4.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := TABLE_INIT x y); eauto.
			econstructor; eq_to_prop; eauto.
			- by inversion HP5; econstructor.
			- ineq_to_prop. rewrite -H7. apply wf_context_tab; eauto. 
		}
	}
	{ (* Load None *)
		typing_inversion HType.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H4.
		destruct nt;
		simpl in Hai; extract_premise.
		all: eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		all: eapply construct_ais_subtyping; eauto.
		all: eapply construct_ais_typing_single; eauto.
		- eapply construct_instr_from_ai_single with (v_instr := (CONST I32 c)); eauto. 
			econstructor; eauto.
			by inversion HP; econstructor.
		- eapply construct_instr_from_ai_single with (v_instr := (CONST I64 c)); eauto. 
			econstructor; eauto.
			by inversion HP; econstructor.
		- eapply construct_instr_from_ai_single with (v_instr := (CONST F32 c)); eauto. 
			econstructor; eauto.
			by inversion HP; econstructor.
		- eapply construct_instr_from_ai_single with (v_instr := (CONST F64 c)); eauto. 
			econstructor; eauto.
			by inversion HP; econstructor.
	}
	{ (* Load Inn *)
		typing_inversion HType.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H4.
		destruct v_Inn;
		simpl in Hai; extract_premise.
		all: 
			eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0;
			eapply construct_ais_subtyping; eauto;
			eapply construct_ais_typing_single; eauto.
		- (* I32 case *)
			eapply construct_instr_from_ai_single with (v_instr := (CONST I32
				(mk_num__0 Inn_I32 (extend__ v_n 32 v_sx c)))); eauto.
			econstructor; eauto.
			by inversion HP; econstructor.
		- (* I64 case *)
			eapply construct_instr_from_ai_single with (v_instr := (CONST I64
				(mk_num__0 Inn_I64 (extend__ v_n 64 v_sx c)))); eauto.
			econstructor; eauto.
			by inversion HP; econstructor.
	}
	(* SIMD instructions *) 
	1-5: admit.
	{ (* Memory_size *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: eapply Hsub.
		eapply construct_instr_from_ai_single with
			(v_instr := (CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))); eauto.
		econstructor; eauto.
		by inversion HP; econstructor.
	}
	{ (* Memory_fill *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.

		typing_inversion H1.
		simpl in Hai; extract_premise.


		typing_inversion H3.
		typing_inversion H2.
		simpl in Hai; extract_premise.
		simpl in Haifinal; extract_premise.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [valtype_I32; t]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsubfinal
			as [Hsub2 Hsubs].
		2: eauto.

		eapply ais_empty_typing.
		split; eauto.
		split; eauto.
		by eapply instrtype_sub_empty.
	}
	{ (* Memory_fill succ *)
		invert_ais_typing.
		resolve_all_pt.

		join_subtyping_ge Hsub Hsub0.
		join_subtyping_ge Hsubi Hsub2.
		join_subtyping_eq Hsubi0 Hsub1.

		eapply Val_ok_non_bot in HValok as Hnonbot.
		eapply valtype_sub_non_bot in Hsubv0; eauto.
		subst.

		eapply construct_ais_subtyping; eauto.
		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_val; eauto.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr :=
				STORE I32 (Some (mk_sz 8)) memarg0); eauto.
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. } 
			rewrite Hnti.
			eapply store_pack; eauto.
			- ineq_to_prop. apply wf_context_mem; eauto.
			- inversion HP1; subst; econstructor; eauto.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP2.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_val; eauto.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP4.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := MEMORY_FILL); eauto.
			econstructor; eauto.
			- ineq_to_prop. apply wf_context_mem; eauto.
			- econstructor.
		}
	}
	{ (* Memory_copy *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		simpl in Haifinal; extract_premise.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [valtype_I32; valtype_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsubfinal
			as [Hsub2 Hsubs].
		2: eauto.

		eapply ais_empty_typing.
		split; eauto.
		split; eauto.
		by eapply instrtype_sub_empty.
	}
	{ (* Memory_copy le *)
		invert_ais_typing.
		resolve_all_pt.

		join_subtyping_ge Hsub Hsub0.
		join_subtyping_ge Hsubi Hsub2.
		join_subtyping_eq Hsubi0 Hsub1.

		eapply construct_ais_subtyping; eauto.
		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr :=
				LOAD I32 (Some (mk_loadop__0 Inn_I32
					(mk_loadop_Inn (mk_sz 8) U))) memarg0); eauto.
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			- ineq_to_prop. eapply wf_context_mem; eauto.
			- inversion HP1; subst; econstructor; eauto.

			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[valtype_I32],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr :=
				STORE I32 (Some (mk_sz 8)) memarg0); eauto.
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			- ineq_to_prop. eapply wf_context_mem; eauto.
			- inversion HP2; subst; econstructor; eauto.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP3.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP4.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP5.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := MEMORY_COPY); eauto.
			econstructor; eauto.
			- ineq_to_prop. eapply wf_context_mem; eauto.
			- by inversion HP6; econstructor.
		}
	}
	{ (* Memory_copy gt *)
		invert_ais_typing.
		resolve_all_pt.

		join_subtyping_ge Hsub Hsub0.
		join_subtyping_ge Hsubi Hsub2.
		join_subtyping_eq Hsubi0 Hsub1.

		eapply construct_ais_subtyping; eauto.
		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP. 
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP0.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr :=
				LOAD I32 (Some (mk_loadop__0 Inn_I32 
				(mk_loadop_Inn (mk_sz 8) U))) memarg0); eauto.
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			- ineq_to_prop; apply wf_context_mem; eauto.
			- inversion HP1; subst; econstructor; eauto.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[valtype_I32],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr :=
				STORE I32 (Some (mk_sz 8)) memarg0); eauto.
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			- ineq_to_prop; apply wf_context_mem; eauto.
			- inversion HP2; subst; econstructor; eauto.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP5.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr := MEMORY_COPY); eauto.
			econstructor; eauto.
			- ineq_to_prop; eapply wf_context_mem; eauto.
			- econstructor.
		}
	}
	{ (* Memory_init 0 *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.	
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		simpl in Haifinal; extract_premise.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [valtype_I32; valtype_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsubfinal
			as [Hsub2 Hsubs].
		2: eauto.

		eapply ais_empty_typing.
		split; eauto.
		split; eauto.
		by eapply instrtype_sub_empty.
	}
	{ (* Memory_init succ *)
		invert_ais_typing.
		resolve_all_pt.

		join_subtyping_ge Hsub Hsub0.
		join_subtyping_ge Hsubi Hsub2.
		join_subtyping_eq Hsubi0 Hsub1.

		eapply construct_ais_subtyping; eauto.
		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- inversion HP0; subst; econstructor; eauto.
				inversion H12; subst; eauto.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr :=
				STORE I32 (Some (mk_sz 8)) memarg0); eauto.
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			- ineq_to_prop; eapply wf_context_mem; eauto.
			- inversion HP1; subst; econstructor; eauto.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP2.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP3.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_subtyping.
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			- by inversion HP4.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_instr_from_ai_single with (v_instr :=
				MEMORY_INIT x); eauto.
			econstructor; eq_to_prop; eauto.
			- ineq_to_prop; eapply wf_context_mem; eauto.
			- by inversion HP5; econstructor.
		}
	}
Admitted.

Lemma step_moduleinst: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' v_tf,
	wf_config (mk_config (mk_state v_s v_f) v_ais) ->
	Step (mk_config (mk_state v_s v_f) v_ais)
		(mk_config (mk_state v_s' v_f') v_ais') ->
	Store_ok v_s ->
  Moduleinst_ok v_s (frame_MODULE v_f) v_C ->
	inst_match v_C v_C' ->
	Instrs_ok2 v_s v_C' v_ais v_tf ->
	Moduleinst_ok v_s' (frame_MODULE v_f') v_C.
Proof.
	move => s f ais s' f' ais' C C' tf HWf HReduce HStore HMi Him HType.
	erewrite <- reduce_inst_unchanged; eauto.
	eapply Extend_store_moduleinst; eauto.
	eapply store_extension_reduce; eauto.
Qed.


Lemma t_preservation_type: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' t1s t2s,
	wf_config (mk_config (mk_state v_s v_f) v_ais) ->
  Step (mk_config (mk_state v_s v_f) v_ais) (mk_config (mk_state v_s' v_f') v_ais') ->
  Store_ok v_s ->
  Store_ok v_s' ->
	Extend_store v_s v_s' -> 
  Moduleinst_ok v_s (frame_MODULE v_f) v_C ->
  Moduleinst_ok v_s' (frame_MODULE v_f) v_C ->
	Vals_ok v_s (LOCALS v_f) (context_LOCALS v_C')->
	inst_match v_C v_C' ->
  Instrs_ok2 v_s v_C' v_ais (t1s :-> t2s) ->
  Instrs_ok2 v_s' v_C' v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' t1s t2s HWf HReduce HST1 HST2 HSExt HIT1 HIT2 HValOK Him.
	move: v_C v_C' HIT1 HIT2 HValOK Him t1s t2s.
	eapply Step_is_wf in HWf as HWfconfig'; eauto.
	inversion HWfconfig' as [? ? HWfState HWfais']; subst.
	inversion HWfState as [? ? HWfS' HWfF']; subst.
	clear HWfconfig' HWfState.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	remember (mk_config (mk_state v_s' v_f') v_ais') as c2.
	generalize dependent v_ais.
	generalize dependent v_ais'.
	generalize dependent v_f.
	generalize dependent v_f'.
	dependent induction HReduce;
	move => r_v_f' HWfF' r_v_f v_ais' Heqc2 HWfais' v_ais Heqc1 v_C v_C' HIT1 HIT2 HValOK Him tx ty HType;
	apply ainstrs_ok_context_store_wf in HType as HWf'; destruct HWf' as [HWfC' [HWfS HWfais]];
	try (destruct z; subst);
	try (destruct z'; subst); try eauto;
	try (apply config_same in Heqc1; apply config_same in Heqc2; 
		destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; 
		destruct Heqc2 as [Hafter1 [Hafter2 Hafter3]]; subst => //);
	try (specialize (IHHReduce _ _ _ erefl _ erefl));
	try (by eapply construct_ais_trap);
	try solve [
		invert_ais_typing;
		resolve_all_pt;
		first [
			join_subtyping_ge Hsub Hsub1;
			join_subtyping_eq Hsubi Hsub0 |
			join_subtyping_ge Hsub Hsub0;
			join_subtyping_eq Hsubi Hsub1 |
			join_subtyping_eq Hsub Hsub0 |
			join_subtyping_eq Hsub0 Hsub |
			idtac
		];
		first [
			construct_ais_typing;
			eapply construct_ai_const_I32 |
			resolve_subtyping;
			construct_ais_typing;
			auto
		]
	].
	- (* Step_pure *) eapply t_pure_preservation; eauto.
	- (* Step_read *) eapply t_read_preservation with (v_ais := v_ais); eauto.
	{ (* Context Label *) 
		typing_inversion HType.
		unfold_principal_typing Hai; extract_premise.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: eapply Hsub.

		inversion H0; subst.
		inversion H6; subst.

		econstructor; eq_to_prop; eauto.
		- apply construct_instrs_from_ais; eauto. apply revert_to_instrs_from_ais in H1; eauto.
		- inv_Forall HWfais. inversion HP; subst. econstructor; eauto.
		- econstructor; eauto.
	}
	{ (* Context Frame *)
		invert_ais_typing.
		resolve_all_pt; subst.

		inversion H1; subst.
		inversion H2; subst.

		remember (prepend_local C t_lst) as C0_l.
		remember (prepend_return C0_l extr) as C0_lr.
		eapply inst_t_context_local_empty in H3 as HC1empty.

		assert (t_lst = context_LOCALS C0_lr) as Heqv_t.
		{
			subst.
			simpl.
			rewrite HC1empty.
			rewrite /_append /Append_List_.
			rewrite cat0s.
			by rewrite cats0.
		}
		
		assert (Vals_ok v_s' (LOCALS f'') t_lst).
		{
			fold (Vals_ok v_s val_lst t_lst) in H3.
			rewrite Heqv_t.
			subst.
			eapply t_preservation_vs_type; eauto.
			{
				simpl.
				rewrite HC1empty.
				rewrite /_append /Append_List_.
				rewrite cat0s.
				by rewrite cats0.
			}
			resolve_inst_match.
		}

		assert (Moduleinst_ok v_s' (frame_MODULE f'') C).
		{
			eapply step_moduleinst.
			2: apply HReduce.
			- econstructor; eauto. econstructor; eauto.
			- eauto.
			- eauto.
			2: apply H11.
			subst; resolve_inst_match.
		}

		inversion H0; subst.
		inversion H18; subst.

		construct_ais_typing.
		eapply Instr_ok2__frame with (C' := prepend_local C t_lst); eauto.
		- destruct f''. econstructor; eq_to_prop; eauto.
			+ apply Forall2_seq_size in H10; eauto.
		-
		eapply mk_Expr_ok2.
		eapply IHHReduce; eauto; simpl; try by subst.
		{
			erewrite <- reduce_inst_unchanged in H14; eauto.
			eauto.
		}
		{
			subst. simpl.
			rewrite HC1empty /_append /Append_List_.
			rewrite cat0s.
			rewrite cats0.
			simpl.
			auto.
		}
		(* Well-formedness*)
		- apply H20.
		- apply wf_context_app; eauto.
			+ econstructor; eauto.
		- apply wf_context_app; eauto.
		- apply H19.
		- apply wf_context_app; eauto.
		- econstructor; eauto.
		- econstructor; eauto.
	}
	{ (* Context Instrs *)
		invert_ais_typing.
		eapply ais_vals_typing_inversion in HType1
			as [v_ts [HSub HValsok]].
		inversion H0; subst.
		inversion H3; subst.

		construct_ais_typing.
		{
			eapply construct_ais_vals; eauto.
			eapply Extend_store_vals; eauto.
		}
		{
			eapply IHHReduce; eauto.
		}
		{
			eapply Extend_store_ais; eauto.
		}
	}
	{ (* Table grow *)
		invert_ais_typing.
		resolve_all_pt.
		eq_to_prop; subst.

		rewrite -(cats0 [valtype_reftype t]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub1.
		simpl in Hsub1.

		rewrite -(cat1s) in Hsub1.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub0.
		2: eauto.
		destruct Hsub0.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: apply H1.
		eapply construct_ai_const_I32; eauto.

		
		inversion H; eq_to_prop; subst; clear H; try (by case: H0).
		rewrite -H6; simpl.
		inversion H11; subst; clear H11.
		inversion H7; inversion H9; subst.
		inversion H14; subst.
		econstructor; eauto. 
		econstructor.
		eq_to_prop.
		destruct H12.
		split; ineq_to_prop.
		- apply N.le_0_l.
		- eapply N.le_le_add_le.
			+ instantiate (1 := v_n).
				apply N.le_0_l.
			+ eauto.
	}
	{ (* Table grow fail *)
		invert_ais_typing.
		resolve_all_pt.
		eq_to_prop; subst.

		rewrite -(cats0 [valtype_reftype t]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub1.
		simpl in Hsub1.

		rewrite -(cat1s) in Hsub1.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub0.
		2: eauto.
		destruct Hsub0.

		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: apply H2.
		eapply construct_ai_const_I32; eauto.
		
		inversion H; subst.
		+ econstructor; eauto.
			econstructor; eauto.
		+ econstructor; eauto.
			econstructor; eauto.
	}
	(* The rest are all SIMD instructions *)
	1-2: admit.
	{ (* Memory grow *)
		invert_ais_typing.
		resolve_all_pt.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub0) in Hsub.
		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: apply Hsub.
		eapply construct_ai_const_I32; eauto.

		inversion HWfais'; subst.
		inversion H8; subst.
		rewrite /fun_mem.
		apply H6.	
	}
	{ (* Memory Grow fail *)
		typing_inversion HType.
		
		typing_inversion H1.
		simpl in Hai; extract_premise.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		eapply construct_ais_subtyping.
		eapply construct_ais_typing_single.
		2: apply Hsub0.
		eapply construct_ai_const_I32; eauto.
		inversion H; subst.
		+ econstructor; eauto.
			econstructor; eauto.
		+ econstructor; eauto.
			econstructor; eauto.
	}
Admitted.


(* Ultimate goal of project *)				
Theorem t_preservation: forall c1 ts c2,
	Step c1 c2 ->
	Config_ok c1 ts ->
	Config_ok c2 ts.
Proof.
	move => c1 ts c2 HReduce HConfig1.
	destruct c1; destruct v_state as [store1 frame1].
	destruct c2; destruct v_state as [store2 frame2].
	(* Config_ok c1 *)
	inversion HConfig1; clear HConfig1.
	inversion H2; clear H2.

	rename H10 into HStore1.
	(* Store_ok store1 *)
	invert_storeok HStore1.
	rename H11 into HFrame1.
	(* Frame_ok store1 frame1 v_C *)
	inversion HFrame1; clear HFrame1.
	inversion H3; clear H3.
	rename H into HModuleInst1.
	rename H16 into HAIs1.
	(* Moduleinst_ok store1 v_moduleinst v_C0 *)
	inversion HModuleInst1.
	eq_to_prop;
	subst.

	remember {|
		store_FUNCS := funcinst_lst; store_GLOBALS := globalinst_lst; store_TABLES := tableinst_lst;
		store_MEMS := meminst_lst; store_ELEMS := eleminst_lst;	store_DATAS := datainst_lst
	|} as store1.
	remember {|
		TYPES := functype_lst0;
		FUNCS := funcaddr_lst;
		GLOBALS := globaladdr_lst;
		TABLES := tableaddr_lst;
		MEMS := memaddr_lst;
		ELEMS := elemaddr_lst;
		DATAS := dataaddr_lst;
		EXPORTS := exportinst_lst
	|} as v_moduleinst.
	remember {|
		LOCALS := val_lst;
		frame_MODULE := v_moduleinst
	|} as frame1.
	remember {|
		context_TYPES := functype_lst0;
		context_FUNCS := functype_F_lst;
		context_GLOBALS := globaltype_lst0;
		context_TABLES := tabletype_lst0;
		context_MEMS := memtype_lst0;
		context_ELEMS := elemtype_lst0;
		context_DATAS := datatype_lst0;
		context_LOCALS := [];
		LABELS := [];
		context_RETURN := None
	|} as v_C0.

	assert (Extend_store store1 store2 /\ Store_ok store2) as
	[HStore_extension HStore2].
	{
		apply (store_extension_reduce 
			store1  
			{|LOCALS := val_lst; frame_MODULE := v_moduleinst|} 
			admininstr_lst 
			store2
			frame2
			admininstr_lst0
			v_C0
			(upd_local_return v_C0
					(_append t_lst0 (context_LOCALS v_C0))
					(_append (option_map [eta (mk_list _)] None)
						(context_RETURN v_C0)))
			([] :-> (mk_list valtype t_lst)) 
			). all:  subst; auto.
		by resolve_inst_match.
	}
	apply reduce_inst_unchanged in HReduce as HModuleInst.
	destruct frame2 as [locals2 module2].
	simpl in HModuleInst.
	assert (Moduleinst_ok store2 v_moduleinst v_C0). {
		apply (Extend_store_moduleinst store1); eauto.
	}

	eapply Step_is_wf in H6 as HWfConfig'; eauto.

	eapply mk_Config_ok with (C := prepend_local v_C0 t_lst0); auto.
	rewrite Heqframe1 in HModuleInst; simpl in HModuleInst.
	econstructor; eauto.
	2,4 : inversion HWfConfig'; eauto.
	
	rewrite <- HModuleInst.

	assert (Vals_ok store2 locals2 t_lst0).
	apply (t_preservation_vs_type) with
		(C := v_C0)
		(C' :=
			{|
			context_TYPES := functype_lst0;
			context_FUNCS := functype_F_lst;
			context_GLOBALS := globaltype_lst0;
			context_TABLES := tabletype_lst0;
			context_MEMS := memtype_lst0;
			context_ELEMS := elemtype_lst0;
			context_DATAS := datatype_lst0;
			context_LOCALS := t_lst0;
			LABELS := [];
			context_RETURN := None
			|})
		(t1s := [])
		(t2s := (mk_list valtype t_lst))
		(s := store1)
		(f := frame1)
		(f' := {| LOCALS := locals2; frame_MODULE := module2 |})
		(ais := admininstr_lst)
		(ais' := admininstr_lst0)
		; eauto;
	try (subst; solve [
		auto |
		simpl; try rewrite cats0; auto |
		resolve_inst_match
	]).
	- subst. clear -HAIs1. 
		rewrite /_append /Append_context /_append_context in HAIs1; simpl in HAIs1. 
		rewrite /_append /Append_List_ in HAIs1.
		repeat rewrite cats0 in HAIs1.
		repeat rewrite cat0s in HAIs1.
		simpl in HAIs1.
		eapply HAIs1.

	eapply (mk_Frame_ok store2 locals2 v_moduleinst t_lst0 v_C0); eq_to_prop; eauto.
	by eapply Forall2_seq_size in H11.
	- inversion HWfConfig'; subst. inversion H19; subst; eauto.
	- inversion HWfConfig'; subst. inversion H19; subst; eauto.

	econstructor; eauto.

	(* Actual Typing proof *)
	eapply t_preservation_type with (v_s := store1); eauto.
	- subst; apply HModuleInst1.
	- subst; apply H10.
	- subst; simpl in *. by rewrite /_append /Append_List_ cats0 /=.
	by resolve_inst_match.
	- inversion HWfConfig'; subst; eauto. inversion H15; subst; eauto.
	- inversion HWfConfig'; subst; eauto.
Qed.
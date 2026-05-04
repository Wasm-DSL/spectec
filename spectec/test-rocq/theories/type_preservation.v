
From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
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
		| I32 => mk_num__0 Inn_I32 (mk_uN 0)
		| I64 => mk_num__0 Inn_I64 (mk_uN 0)
		| F32 => mk_num__1 Fnn_F32 (fzero 32)
		| F64 => mk_num__1 Fnn_F64 (fzero 64)
	end
.

Lemma num_default_is_well_formed: forall nt,
	wf_num_ nt (num_default nt).
Proof.
	move=> nt.
	destruct nt; econstructor; eq_to_prop; eauto.
	- econstructor; eauto.
	- econstructor; eauto.
	- econstructor. econstructor. unfold sizenn; unfold E. simpl. eauto.
	- econstructor. econstructor. unfold sizenn; unfold E; simpl. eauto.
Qed.

Lemma inst_t_context_local_empty: forall s i C,
	Module_instance_ok s i C ->
  context_LOCALS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.

Lemma inst_t_context_labels_empty: forall s i C,
	Module_instance_ok s i C ->
  LABELS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.

Lemma t_preservation_vs_type': forall s f ais s' f' ais' C C' t1s t2s,
	Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
	Store_ok s -> 
	Module_instance_ok s (frame_MODULE f) C ->
	Vals_ok s (LOCALS f) (context_LOCALS C') ->
	inst_match C C' ->
	Admin_instrs_ok s C' ais (t1s :-> t2s) ->
	Vals_ok s (LOCALS f') (context_LOCALS C').
Proof.
	move => s f ais s' f' ais' C C' t1s t2s HReduce HST HIT.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	move: C' t1s t2s.
	generalize dependent ais.
	generalize dependent ais'.

	induction HReduce => //;
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
		rewrite H.
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
	Store_extension s s' ->
    Module_instance_ok s (frame_MODULE f) C ->
	Vals_ok s (LOCALS f) (context_LOCALS C') ->
	inst_match C C' ->
    Admin_instrs_ok s C' ais (t1s :-> t2s) ->
    Vals_ok s' (LOCALS f') (context_LOCALS C').
Proof.
	move => s f ais s' f' ais' C C' t1s t2s HReduce HST
		HStoreExt HMInst HValOK Him HType.
	eapply t_preservation_vs_type' in HValOK; eauto.
	eapply store_extension_vals in HValOK; eauto.
Qed.

Lemma store_extension_reduce: forall s f ais s' f' ais' C C' tf,
	Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
	Module_instance_ok s (frame_MODULE f) C ->
	Admin_instrs_ok s C' ais tf ->
	inst_match C C' ->
	Store_ok s ->
	Store_extension s s' /\ Store_ok s'.
Proof.
	move => s f ais s' f' ais' C C' tf HReduce HIT HType HMatch HStore.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent C. generalize dependent C'.
	generalize dependent tf.
	generalize dependent ais. generalize dependent ais'. 
	generalize dependent f. generalize dependent f'.

	pose proof func_extension_refl as LemFuncSame.
	pose proof mem_extension_refl as LemMemSame.
	pose proof table_extension_refl as LemTableSame.
	pose proof global_extension_refl as LemGlobalSame.
	pose proof elem_extension_refl as LemElemSame.
	pose proof data_extension_refl as LemDataSame.
	pose proof store_extension_refl as LemStoreSame.

	induction HReduce;
	move => v_f' v_f ais' Heqc2 ais Heqc1 tf C' HType C HIT HMatch;
	destruct tf as [[tf1] [tf2]].
	all: eq_to_prop; try (destruct z; 
	apply config_same in Heqc1; apply config_same in Heqc2; 
	destruct Heqc1; destruct Heqc2;
	subst; try (split => //; eapply store_extension_refl; eauto)).
	{ (* Label Context *) 
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H in HType.
		typing_inversion HType.
		Opaque admininstr_instr.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H3; subst; clear H3.
		eapply IHHReduce; eauto.
	}
	{ (* Label Frame *)
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H0 in HType.
		typing_inversion HType.
		Opaque admininstr_instr.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H5; subst; clear H5.
		inversion H7; subst; clear H7.
		inversion H0; subst; clear H0.
		eapply IHHReduce; eauto.
		resolve_inst_match.
	}
	{ (* Label Seq *)
		injection Heqc1 as H1.
		injection Heqc2 as H2.
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

		remember ((proj_uN_0 x)) as v_i.
		remember ((lookup_total (GLOBALS (frame_MODULE v_f)) v_i)) as ga.
		remember  (s <| store_GLOBALS :=
			list_update_func (store_GLOBALS s) ga
			[eta set VALUE (fun=> v_val)] |>) as s'.

		assert (
			ga < Datatypes.length (store_GLOBALS s) /\
			exists v, lookup_total (store_GLOBALS s) ga =
				{| globalinst_TYPE := mk_globaltype (Some MUT_MUT) t; VALUE := v |})
			as [HLen [v_old HLookup]].
		{
			eapply minst_invert_globals in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in H0.
			list_to_seq.
			rewrite H0 in H3.
			inversion H3; subst; clear H3.
			rewrite /lookup_total in H4.

			split. auto.
			by exists extr1.
		}

		assert (Store_extension s s').
		{
			destruct s; destruct s'.
			eapply mk_Store_extension with
				(funcinst_2_lst := [])
				(tableinst_2_lst := [])
				(meminst_2_lst := [])
				(globalinst_2_lst := [])
				(eleminst_2_lst := [])
				(datainst_2_lst := [])
				(globalinst_1'_lst := store_GLOBALS0)
			; eq_to_prop; eauto.
			all: injection Heqs' as ?; subst.
			- by repeat rewrite cats0.
			- by rewrite list_update_length_func.
			- subst; eapply global_set_global_extension; eauto.
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
			; 
			eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto].
		- rewrite {1}list_update_length_func; eauto.
		- {
			eapply construct_globalinsts; subst; eauto.
		}
	}
	{ (* Table Set *)
		rewrite /fun_table in H.
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.
		Opaque instrtype_sub.
		join_subtyping_ge Hsub Hsub0.
		join_subtyping_eq Hsubi Hsub1.
		eapply Ref_ok_non_bot in HRefok as Hnonbot.
		eapply valtype_sub_non_bot in Hsubv0; eauto.
		assert (extr = t).
		{
			destruct t; destruct extr; auto; discriminate.
		}
		subst. clear Hsub Hsubi Hnonbot Hsubv Hsubv0.

		remember (!( proj_num__0 i) :> nat) as v_i.
		remember (x :> nat) as j.
		remember ((lookup_total (TABLES (frame_MODULE v_f)) j)) as tba.
		remember  (s <| store_TABLES :=
			list_update_func (store_TABLES s) tba
			(λ v_1 : tableinst, v_1
				<| REFS := list_update_func (REFS v_1) v_i (fun=> v_ref)
			|>) |>) as s'.

		assert (
			tba < Datatypes.length (store_TABLES s) /\
			exists v_lim_1 tbr,
				(Limits_sub v_lim_1 extr0) /\
				((lookup_total (store_TABLES s) tba) =
					{| tableinst_TYPE := (mk_tabletype v_lim_1 t); REFS := tbr |}))
			as [HLen [v_lim_1 [tbr [HLimSub HLookup]]]].
		{
			eapply minst_invert_tables in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H3.
			destruct_all.
			list_to_seq.
			rewrite /lookup_total in H5.
			rewrite H5 in H7.
			inversion H7; subst; clear H7.
			rewrite /lookup_total in H9.

			split. auto.
			by exists extr1, extr3.
		}

		assert (Store_extension s s').
		{
			destruct s; destruct s'.
			eapply mk_Store_extension with
				(funcinst_2_lst := [])
				(tableinst_2_lst := [])
				(meminst_2_lst := [])
				(globalinst_2_lst := [])
				(eleminst_2_lst := [])
				(datainst_2_lst := [])
				(tableinst_1'_lst := store_TABLES0)
			; eq_to_prop; eauto.
			all: inversion Heqs'; subst; clear Heqs'.
			- by repeat rewrite cats0.
			- by rewrite list_update_length_func.
			- subst; rewrite {1}/set /=.
				eapply table_set_table_extension; eauto.
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
			; 
			eq_to_prop;
			auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func; eauto.
		- {
			eapply construct_tableinsts; subst; eauto.
		}
	}
	{ (* Table Grow *)
		rename H0 into Hwfconfig.
		destruct_all; subst.
		invert_ais_typing.
		unfold_principal_typing Hai.
		rename H1 into Hwfconfig2.
		rename H2 into HNotNone.
		destruct Hai as [extr [lim [HTemp [H1 H2]]]].
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
		rewrite /fun_table in H.
		inversion H; eq_to_prop; subst.
		2: 
		{
			destruct HNotNone. reflexivity.
		}
		rename H4 into Hopt.

		remember ((proj_uN_0 x)) as v_i.
		remember ((lookup_total (TABLES (frame_MODULE v_f)) v_i)) as tba.
		remember ((mk_limits (mk_uN (Datatypes.length r'_lst + v_n)) j_opt))
			as v_limits_new.
		remember (({| tableinst_TYPE := mk_tabletype v_limits_new rt;
			REFS := r'_lst ++ repeat v_ref v_n |})) as v_ti.
		remember  (s <| store_TABLES := list_update_func (store_TABLES s) tba
					(fun=> v_ti) |>) as s'.

		assert (
			tba < Datatypes.length (store_TABLES s) /\
			(Forall (λ j : u32, (| r'_lst |) + v_n <= (j :> nat)) j_opt) /\
			(t = rt) /\
			((lookup_total (store_TABLES s) tba) =
				{| tableinst_TYPE := mk_tabletype
					(mk_limits (mk_uN (Datatypes.length r'_lst)) j_opt)
					t;
					REFS := r'_lst |}))
			as [HLen [HRange [tbr HLookup]]].
		{
			eapply minst_invert_tables in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in H0.
			rewrite /lookup_total in Heqtba.
			list_to_seq.
			rewrite -Heqtba in H1.
 
			rewrite /lookup_total in H2.
			rewrite H2 in H4.
			inversion H4; clear H4.
			rewrite /lookup_total in H6.
			rewrite Heqv_i in H6.
			rewrite H6 in H0.
			inversion H0; clear H0.

			split; auto.
			split; auto.
			split; auto.
			
			eapply s_invert_tables in HStore as [tbts HTable].
			apply Forall2_nth in HTable as [HLen HTable].
			subst.
			apply HTable in H1.
			destruct_all.
			rewrite /lookup_total.
			list_to_seq.
			rewrite H4 in H1.
			rewrite H1 in H6.
			inversion H6; subst; clear H6.
			rewrite H1; auto.
		}

		assert (Store_extension s s').
		{
			destruct s; destruct s';
			eapply mk_Store_extension with
				(funcinst_2_lst := [])
				(tableinst_2_lst := [])
				(meminst_2_lst := [])
				(globalinst_2_lst := [])
				(eleminst_2_lst := [])
				(datainst_2_lst := [])
				(tableinst_1'_lst := store_TABLES0)
			; eq_to_prop; eauto.
			all: inversion Heqs'; subst; clear Heqs'.
			- by repeat rewrite cats0.
			- by rewrite list_update_length_func.
			- subst.
				eapply table_grow_table_extension; eauto.
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
				(mk_limits (mk_uN (size r'_lst + v_n)) j_opt)
				rt
			))
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite !list_update_length_func  /=; eauto.
		- {
			eapply construct_tableinsts_grow; subst; eauto.
		}
	}
	{ (* Elem Drop *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		remember ((proj_uN_0 x)) as i.
		remember ((lookup_total (ELEMS (frame_MODULE v_f)) i)) as ea.
		remember  (s <| store_ELEMS :=
			list_update_func (store_ELEMS s) ea [eta set eleminst_REFS (fun=> [])] |>) as s'.

		assert (
			(ea < (size (store_ELEMS s))) /\
			exists rt v_ref,
				((lookup_total (store_ELEMS s) ea) =
					{| eleminst_TYPE := rt; eleminst_REFS := v_ref |}) /\
				(List.Forall (fun (v_ref : ref) => (Ref_ok s v_ref rt)) (v_ref)))
			as [HLen [rt [v_ref [HLookup HRefok]]]].
		{
			eapply minst_invert_elems in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in Heqea.
			list_to_seq.
			rewrite -Heqea in H1.
			split; auto.

			rewrite -Heqea in H4.
			by exists (nth default_val (context_ELEMS C') i), extr0.
		}

		assert (Store_extension s s').
		{
			destruct s; destruct s';
			eapply mk_Store_extension with
				(funcinst_2_lst := [])
				(tableinst_2_lst := [])
				(meminst_2_lst := [])
				(globalinst_2_lst := [])
				(eleminst_2_lst := [])
				(datainst_2_lst := [])
				(eleminst_1'_lst := store_ELEMS0)
			; eq_to_prop; eauto.
			all: inversion Heqs'; subst; clear Heqs'.
			- by repeat rewrite cats0.
			- by rewrite list_update_length_func.
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
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func; eauto.
		- eapply construct_eleminsts; subst; eauto.
	}
	{ (* Store None *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		simpl.

		assert (length (nbytes_ nt c) =
    (Nat.divmod (the (res_size (valtype_numtype nt))) 7 0 7).1)
			as Heqlen.
		{
			(* fun_nbytes_ not implemented *)
			by eapply nbytes_len.
		}

		remember ((proj_uN_0 (the (proj_num__0 i)))) as v_i.
		remember (proj_uN_0 (OFFSET ao)) as v_ao.
		remember ((lookup_total (MEMS (frame_MODULE v_f)) 0)) as ma.
		remember  (s <| store_MEMS :=
			list_update_func (store_MEMS s) ma
				(λ v_1,
				v_1 <| BYTES := list_slice_update (BYTES v_1) (v_i + v_ao) (Nat.divmod (the (res_size (valtype_numtype nt))) 7 0 7).1
				(nbytes_ nt c) |>)	
		|> ) as s'.

		assert (
			(ma < (List.length (store_MEMS s))) /\
			exists v_mt v_mt' v_b,
				((lookup_total (store_MEMS s) ma) =
					{| meminst_TYPE := v_mt; BYTES := v_b |}) /\
				((Memtype_sub v_mt v_mt'))
				)
			as [HLen [v_mt [v_mt' [v_b [HLookup HRefok]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H4.
			destruct_all.
			rewrite /lookup_total in Heqma.
			list_to_seq.
			rewrite -Heqma in H4.
			split; auto.
			rewrite /lookup_total in H10.

			rewrite -Heqma in H10.
			by exists extr, (nth default_val (context_MEMS C') 0), extr0.
		}

		assert (Store_extension s s').
		{
			destruct s; destruct s';
			eapply mk_Store_extension with
				(funcinst_2_lst := [])
				(tableinst_2_lst := [])
				(meminst_2_lst := [])
				(globalinst_2_lst := [])
				(eleminst_2_lst := [])
				(datainst_2_lst := [])
				(meminst_1'_lst := store_MEMS0)
			; eq_to_prop; eauto.
			all: inversion Heqs'; subst; clear Heqs'.
			- by repeat rewrite cats0.
			- by rewrite list_update_length_func.
			- eapply store_none_mem_extension; eauto.
		}
		split; auto.
		- by subst.

		inversion HStore.
		eapply mk_Store_ok with
			(funcinst_lst := funcinst_lst)
			(globalinst_lst := globalinst_lst)
			(tableinst_lst := tableinst_lst)
			(meminst_lst := list_update_func (store_MEMS s) ma
				(λ v_1 : meminst,
				v_1 <| BYTES := list_slice_update (BYTES v_1) (v_i + v_ao) (Nat.divmod (the (res_size (valtype_numtype nt))) 7 0 7).1
				(nbytes_ nt c) |>))
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func; eauto.
		- {
			rewrite -Heqlen.
			eapply construct_meminsts; subst; eauto.
		}
	}
	{ (* Store Some *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		simpl.

		assert (length (ibytes_ v_n (wrap__ (the (res_size (valtype_Inn v_Inn))) v_n (the (proj_num__0 c)))) = 
			(Nat.divmod v_n 7 0 7).1 )
			as Heqlen.
		{
			(* fun_ibytes_ wrap__ not implemented *)
			by eapply ibytes_len.
		}

		remember ((proj_uN_0 (the (proj_num__0 i)))) as v_i.
		remember (proj_uN_0 (OFFSET ao)) as v_ao.
		remember ((lookup_total (MEMS (frame_MODULE v_f)) 0)) as ma.
		remember  (s <| store_MEMS :=
			list_update_func (store_MEMS s) ma
				(λ v_1,
				v_1 <| BYTES := list_slice_update (BYTES v_1) (v_i + v_ao) (Nat.divmod v_n 7 0 7).1
				(ibytes_ v_n (wrap__ (the (res_size (valtype_Inn v_Inn))) v_n (the (proj_num__0 c)))) |>)	
		|> ) as s'.
		rewrite -Heqlen in Heqs'.

		assert (
			(ma < (List.length (store_MEMS s))) /\
			exists v_mt v_mt' v_b,
				((lookup_total (store_MEMS s) ma) =
					{| meminst_TYPE := v_mt; BYTES := v_b |}) /\
				((Memtype_sub v_mt v_mt'))
				)
			as [HLen [v_mt [v_mt' [v_b [HLookup HRefok]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H5.
			destruct_all.
			rewrite /lookup_total in Heqma.
			list_to_seq.
			rewrite -Heqma in H5.
			split; auto.

			rewrite -Heqma in H10.
			by exists extr, (nth default_val (context_MEMS C') 0), extr0.
		}

		assert (Store_extension s s').
		{
			destruct s; destruct s';
			eapply mk_Store_extension with
				(funcinst_2_lst := [])
				(tableinst_2_lst := [])
				(meminst_2_lst := [])
				(globalinst_2_lst := [])
				(eleminst_2_lst := [])
				(datainst_2_lst := [])
				(meminst_1'_lst := store_MEMS0)
			; eq_to_prop; eauto.
			all: inversion Heqs'; subst; clear Heqs'.
			- by repeat rewrite cats0.
			- by rewrite list_update_length_func.
			- eapply store_none_mem_extension; eauto.
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
					(Nat.divmod v_n 7 0 7).1
					(ibytes_ v_n (wrap__ (the (res_size (valtype_Inn v_Inn))) v_n (the (proj_num__0 c)))) |>))
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func; eauto.
		- {
			rewrite -Heqlen.
			eapply construct_meminsts; subst; eauto.
		}
	}
	(* SIMD instructions *)
	1-2: admit.
	{ (* Memory Grow *)
		rename H0 into Hwfconfig.
		rename H1 into Hwfconfig2.
		rename H2 into HNotNone.
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.
		simpl.
		remember (the (var_0)) as mi.

		clear Hsub Hsub0.

		remember ((lookup_total (MEMS (frame_MODULE v_f)) 0)) as ma.
		remember (s <| store_MEMS := list_update_func (store_MEMS s) ma (fun=> mi) |>) as s'.

		assert (
			(ma < (List.length (store_MEMS s))) /\
			exists v_mt' lim_old v_j v_b,
				((Memtype_sub (PAGE (mk_limits lim_old (Some v_j))) v_mt')) /\
				(lookup_total (store_MEMS s) ma =
					{| meminst_TYPE := PAGE (mk_limits lim_old (Some v_j)); BYTES := v_b |}) /\
				(mi =
					{| meminst_TYPE := PAGE (mk_limits (lim_old + v_n) (Some v_j));
					BYTES := v_b ++ repeat (mk_byte 0) (v_n * (64 * Ki)) |}) /\
				(lim_old = (length v_b) / (64 * Ki)) /\
				(lim_old + v_n <= v_j)
				)
			as [HLen [v_mt' [lim_old [v_j [v_b [HMemsub [HLookup [HNew [HLimold HRange]]]]]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.
			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H0.
			destruct_all.
			rewrite /lookup_total in Heqma.
			list_to_seq.
			rewrite -Heqma in H0 H5.
			split; auto.
			clear HIT.

			eapply s_invert_mems in HStore as [mts HMem].
			eapply Forall2_nth in HMem as [_ HForall].
			eapply HForall in H0.
			destruct_all.
			list_to_seq.
			rewrite /lookup_total H0 in H5.
			inversion H5; clear H5.
			clear HForall.
			
			rewrite /lookup_total.

			rewrite /fun_mem in H; inversion H; eq_to_prop; subst; clear H.
			2: by destruct HNotNone.
			rewrite H6 in H4.
			rewrite H6 in H0.

			rewrite /lookup_total /= H0 in H5.
			inversion H5; subst; clear H5.

			exists (nth default_val (context_MEMS C') 0),
				(mk_uN (Datatypes.length b_lst / (64 * Ki))),
				(mk_uN extr4),
				(b_lst).
			list_to_seq.
			inversion H12; eauto.
		}

		assert (Store_extension s s').
		{
			destruct s; destruct s';
			eapply mk_Store_extension with
				(funcinst_2_lst := [])
				(tableinst_2_lst := [])
				(meminst_2_lst := [])
				(globalinst_2_lst := [])
				(eleminst_2_lst := [])
				(datainst_2_lst := [])
				(meminst_1'_lst := store_MEMS0)
			; eq_to_prop; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			all: inversion Heqs'; subst; clear Heqs'.
			- by repeat rewrite cats0.
			- by rewrite list_update_length_func.
			- rewrite HNew. eapply memory_grow_mem_extension; eauto.
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
				{| meminst_TYPE := PAGE (mk_limits (lim_old + v_n) (Some v_j));
				BYTES := v_b ++ repeat (mk_byte 0) (v_n * (64 * Ki)) |}))
			(eleminst_lst := eleminst_lst)
			(datainst_lst := datainst_lst)
			(memtype_lst := list_update_func memtype_lst ma
				(λ _, PAGE (mk_limits (lim_old + v_n) (Some v_j))))
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- by rewrite HNew.
		- rewrite !list_update_length_func /=; eauto.
		- {
			eapply construct_meminsts_grow; subst; eauto.
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
			(List.length (DATAS (frame_MODULE v_f)) = (List.length (context_DATAS C'))) /\
			(da < (List.length (store_DATAS s))) /\
			exists v_b,
				((lookup_total (store_DATAS s) da) =
					{| datainst_BYTES := v_b |})
				)
			as [HCLen [HLen [v_b HLookup]]].
		{
			eapply minst_invert_datas in HIT; eauto.
			destruct_all.
			split. auto.

			eapply Forall_nth with (d := default_val) in H3.
			2: {
				instantiate (1 := i).
				rewrite H2.
				by move/ltP in H1.
			}
			destruct_all.
			list_to_seq.
			split. by rewrite Heqda.
			exists extr.
			by rewrite Heqda.
		}

		assert (Store_extension s s').
		{
			destruct s; destruct s';
			eapply mk_Store_extension with
				(funcinst_2_lst := [])
				(tableinst_2_lst := [])
				(meminst_2_lst := [])
				(globalinst_2_lst := [])
				(eleminst_2_lst := [])
				(datainst_2_lst := [])
				(datainst_1'_lst := store_DATAS0)
			; eq_to_prop; eauto.
			all: inversion Heqs'; subst; clear Heqs'.
			- by repeat rewrite cats0.
			- by rewrite list_update_length_func.
			- eapply data_drop_data_extension; eauto.
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
			; eq_to_prop; auto;
			try solve [subst; auto];
			try solve eauto;
			subst;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
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
    Step_read (mk_config (mk_state v_s v_f) v_ais) v_ais' ->
    Store_ok v_s ->
    Module_instance_ok v_s (frame_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) (context_LOCALS v_C') (LOCALS v_f) ->
	inst_match v_C v_C' ->
    Admin_instrs_ok v_s v_C' v_ais (t1s :-> t2s) ->
    Admin_instrs_ok v_s v_C' v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_ais' v_C v_C' t1s t2s HReduce HST.
	move: v_C v_C' t1s t2s.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	induction HReduce;
	move => v_C v_C' tx ty HIT1 HValOK Him HType; decomp; destruct z; try eauto;
	eq_to_prop;
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
			eapply Forall2_length in Hforall.
			list_to_seq.
			rewrite -H0 in Hforall. auto.
		}

		eapply construct_ais_typing_single with (ts1 := []) (ts2 := t_2_lst).
		2: auto.
		eapply label; auto.
		{ eapply instrs_empty_typing. eapply resulttype_sub_refl. }

		eapply construct_ais_compose.
		{
			eapply construct_ais_vals; eauto.
			by eapply instrtype_sub_refl.
		}
		eapply construct_ais_instrtype_sub.
		{
			eapply instrs.
			eapply H4.
		}
		by eapply instrtype_sub_iff_resulttype_sub'.
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
			eapply Forall2_length in Hforall.
			list_to_seq.
			rewrite -H0 in Hforall. auto.
		}

		eapply construct_ais_typing_single with (ts1 := []) (ts2 := t_2_lst).
		2: auto.
		eapply label; auto.
		{
			eapply construct_instrs_typing_single.
			2: {
				eapply instrtype_sub_refl.
			}
			econstructor. eauto. eauto.
		}
		{
			eapply construct_ais_compose.
			{
				eapply construct_ais_vals; eauto.
				eapply instrtype_sub_iff_resulttype_sub.
				eapply Hsubs.
			}
			eapply construct_ais_instrtype_sub.
			{
				eapply instrs.
				eapply H4.
			}
			by eapply instrtype_sub_refl.
		}
	}
	{ (* Call *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		Opaque instrtype_sub.
		eapply minst_invert_funcs in HIT1; eauto.
		eapply Forall2_nth2 in HIT1 as [HLen HFunc].
		eapply HFunc in H1.
		destruct_all.
		econstructor.
		rewrite /fun_funcaddr.
		
		rewrite /lookup_total; auto.
		rewrite /lookup_total in H2 H0.
		rewrite /lookup_total in H2.
		list_to_seq.
		econstructor; eq_to_prop; eauto.
		rewrite H0 in H2.
		eauto.
	}
	{ (* Call_indirect *)
		rewrite /fun_table /= in H0.
		rewrite /fun_table /lookup_total /= in H3.
		rewrite /fun_funcinst /= in H3.
		rewrite /fun_type /fun_funcinst /= in H4.

		invert_ais_typing.
		resolve_all_pt.
		join_subtyping_le Hsub0 Hsub.

		pose proof HIT1 as HIT1_0.
		eapply minst_invert_tables in HIT1; eauto.
		eapply Forall2_nth2 in HIT1 as [HLen HTable].
		eapply HTable in H6; clear HTable.
		destruct_all.

		eapply minst_invert_functypes in HIT1_0; eauto.
		rewrite -HIT1_0 H10 in H4.
		list_to_seq.

		rewrite /lookup_total in H4 H2 H0 H13.
		rewrite /fun_table /lookup_total in H2.
		rewrite H13 /= in H0 H2.

		eapply s_invert_funcs in HST as [fts HFunc].
		eapply Forall2_nth in HFunc as [HLen2 HFunc].
		pose proof H3 as H3_0.
		eapply HFunc in H3.
		destruct_all.

		construct_ais_typing.
		econstructor.
		econstructor; eauto.
		rewrite /lookup_total.
		eq_to_prop. list_to_seq.
		rewrite Hextr0.
		rewrite /lookup_total Hextr0 /= in H4.
		rewrite H4.
		eauto.
	}
	{ (* Call_addr *)
		typing_inversion HType.
		vals_typing_inversion H3.
		typing_inversion H5.
		simpl in Hai;
		extract_premise.

		inversion H5; eq_to_prop; subst; clear H5.
		unfold fun_funcinst in *.
		rewrite H2 in H10.
		inversion H10; subst; clear H10.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub) in Hsub0
		as [Hsub0 Hsubs].
		2: {
			eapply Forall2_length in Hforall.
			list_to_seq.
			rewrite -H6 in Hforall.
			auto.
		}
		assert (v_ts = extr). {
			eapply Vals_ok_non_bot in Hforall as Hnonbot.
			eapply (resulttype_sub_non_bot _ _ Hnonbot) in Hsubs; subst.
			auto.
		}
		subst.

		eapply construct_ais_typing_single.
		2: eapply Hsub0.
		eapply Admin_instr_ok__frame.
		2: auto.

		(* Thread_ok *)
		invert_funcs.
		inversion HST; eq_to_prop; subst.
		eapply Forall2_nth in H7 as [_ H7].
		simpl in *.
		eapply H7 in H9 as Hfiok.
		unfold lookup_total in H2.
		list_to_seq.
		rewrite H2 in Hfiok.
		inversion Hfiok; subst.

		eapply mk_Thread_ok with (C := ({|
			context_TYPES := [];
			context_FUNCS := [];
			context_GLOBALS := [];
			context_TABLES := [];
			context_MEMS := [];
			context_ELEMS := [];
			context_DATAS := [];
			context_LOCALS := extr ++ t_lst;
			LABELS := [];
			context_RETURN := None
			|} @@ C)).
		{
			eapply mk_Frame_ok with (t_lst := extr ++ t_lst); auto.
			{
				eq_to_prop.
				rewrite !size_cat.
				rewrite !size_map.
				auto.
			}
			subst.
			eapply Forall2_app; auto.
			clear H22 Hfiok H2 H24.
			induction H0.
			- simpl; eauto.
			eauto.
			rewrite map_cons.
			econstructor.
			{
				inversion H4; subst. destruct x0; try discriminate.
				inversion H0; subst; clear H0.
				all: try econstructor; try econstructor; try eapply num_default_is_well_formed.
				eapply Val_ok__reftype with (r := ref_REF_NULL _) (rt := FUNCREF); econstructor.
				eapply Val_ok__reftype with (r := ref_REF_NULL _) (rt := EXTERNREF); econstructor.
			}
			eapply IHForall2 ; eauto.
			- by inversion H4.
		}
		subst.
		eapply construct_ais_typing_single.
		2: eapply instrtype_sub_refl.
		econstructor.
		3: eauto.
		{
			eapply instrs_empty_typing; eapply resulttype_sub_refl.
		}
		subst.

		eapply instrs.

		inversion H24; eq_to_prop; subst.
		inversion H30; eq_to_prop; subst.
		inversion H23; eq_to_prop; subst.
		unfold _append, Append_context, _append_context, _append, Append_List_.
		simpl.
		unfold _append, Append_context, _append_context, _append, Append_List_ in H25.
		simpl in H25.
		rewrite !cats0 in H25.
		rewrite !cats0.
		assert (injective (ListDef.map [eta LOCAL])) as map_local_inj.
		{
			eapply inj_map.
			unfold injective.
			move=> x1 x2 Hconstructor.
			by inversion Hconstructor.
		}
		eapply map_local_inj in H18; subst.
		auto.
	}
	{ (* Ref_func *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise. subst.
		list_to_seq.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		unfold fun_funcaddr in *; subst.
		eapply minst_invert_funcs in HIT1; eauto.
		eapply Forall2_nth2 in HIT1 as [HLen HFunc].
		eapply HFunc in H1.
		destruct_all.
		list_to_seq.

		econstructor.
		econstructor; eq_to_prop; eauto.
	}
	{ (* Local_get *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise. subst.

		eapply Forall2_nth in HValOK as [HLength HValOK].

		destruct v_f; destruct v_C'; destruct v_C; destruct v_s;
		unfold inst_match in Him; destruct_all;
		subst; simpl in *; subst.
		eapply HValOK in H1.
		inversion HIT1; eq_to_prop; subst; simpl in *; subst.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		inversion H1; subst; unfold admininstr_val;
			unfold lookup_total in *.
		all: list_to_seq.
		{ (* CONST case *)
			rewrite -H2;
			rewrite -H.
			eapply Admin_instr_ok__instr with (v_instr := (CONST nt c_t)).
			econstructor; eauto.
			econstructor; eauto.
			by inversion H3.
		}
		{ (* VCONST case *)
			list_to_seq.
			rewrite -H2;
			rewrite -H3.
			eapply Admin_instr_ok__instr with (v_instr := (VCONST vt c_t)).
			destruct vt.
			econstructor.
		}
		rewrite -H; rewrite -H2.
		destruct r.
		{ (* NULL case *)
			simpl.
			inversion H3; subst.
			eapply Admin_instr_ok__instr with (v_instr := (REF_NULL rt)).
			constructor.
		}
		(* Rest of vals *)
		all:
			simpl;
			inversion H3; subst;
			econstructor; eauto.
	}
	{ (* Global_get *)
		rewrite /fun_global.
		invert_ais_typing.
		resolve_all_pt.

		eapply minst_invert_globals in HIT1; eauto.
		eapply Forall2_nth2 in HIT1 as [HLen HGlobal].
		eapply HGlobal in H1.
		destruct_all.

		rewrite /lookup_total.
		rewrite /lookup_total in H4.
		list_to_seq.
		rewrite H4 /=.

		eapply s_invert_globals in HST as [gts HGlobal2].
		eapply Forall2_nth in HGlobal2 as [HLen2 HGlobal2].
		eapply HGlobal2 in H1.
		destruct_all.
		rewrite H5 in H1. clear H5.
		rewrite /lookup_total H3 in H0.
		inversion H0; subst; clear H0.
		list_to_seq.
		rewrite H4 in H1. clear H4.
		inversion H1; subst; clear H1.

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
		eapply Forall2_nth2 in HIT1 as [HLen HTable].
		eapply HTable in H3; clear HTable.
		destruct_all.
		list_to_seq.

		rewrite H8 /= in H.
		rewrite H8 /=.

		eapply s_invert_tables in HST as [tbts HTableinst].
		eapply Forall2_nth in HTableinst as [HLen2 HTableinst].
		eapply HTableinst in H3; clear HTableinst.
		destruct_all.
		rewrite /lookup_total in H8.
		list_to_seq.
		rewrite H8 in H3.
		inversion H3; subst; clear H3.

		eapply Forall_nth' in H11; eauto.
		list_to_seq.
		rewrite /lookup_total in H5.
		rewrite -H12 in H9.
		inversion H9; subst; clear H9.
		rewrite H6 in H5.
		inversion H5; subst; clear H5.

		rewrite /lookup_total.
		construct_ais_typing.
		by eapply construct_ai_ref.
	}
	{ (* Table_size *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise; subst.
		
		eapply construct_ais_typing_single.
		2: eapply Hsub.
		
		eapply Admin_instr_ok__instr with (v_instr := (CONST I32 (mk_num__0 Inn_I32 (mk_uN
		(Datatypes.length (REFS (fun_table (mk_state v_s v_f) x))))))).
		econstructor.
		list_to_seq.
		simpl.
		econstructor; eauto. econstructor; eauto.
		inversion H; subst; eauto. 
		inversion H3; subst; eauto.
	}
	{ (* Table_fill *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.
		typing_inversion H2.

		simpl in Hai; extract_premise.

		typing_inversion H4.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.
		
		typing_inversion H3.
		simpl in Hai; extract_premise.
		rewrite -(cats0 [valtype_I32; t]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		simpl in Haifinal; extract_premise.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsubfinal
		as [Hsub2 Hsubs].
		2: auto.

		eapply ais_empty_typing.
		by eapply instrtype_sub_empty.
	}
	{ (* Table_fill succ *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hsub into Hsubfinal.
		rename Hai into Haifinal.
		typing_inversion H6.

		simpl in Hai; extract_premise.
		pose proof H8 as H8_0.

		typing_inversion H8.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		pose proof Hsub0 as Hsub0_0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.
		
		typing_inversion H7.
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
		remember (mk_num__0 Inn_I32 (mk_uN ((!( proj_num__0 i) :> nat) + 1))) as c.
		remember (mk_num__0 Inn_I32 (mk_uN (v_n - 1))) as n_const.
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
					eapply construct_ais_typing_single.
					2: eapply Hsub_0.
					eapply Admin_instr_ok__instr with (v_instr := (CONST I32 i)).
					econstructor. econstructor; eauto.
				}
				eapply H8_0.
			}
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := (TABLE_SET x)).
			econstructor; list_to_seq; eq_to_prop; eauto.
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
					eapply construct_ais_typing_single.
					eapply Admin_instr_ok__instr with (v_instr := (CONST I32 c)).
					econstructor. econstructor.
					- by inversion H4.
					- by eapply instrtype_sub_add_same.
				}
				eapply construct_ais_typing_single.
				eapply construct_ai_val. eauto.

				rewrite -(cats0 (ts_sub ++ [valtype_I32])).
				by eapply instrtype_sub_add_same.
			}
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := (CONST I32
				n_const
			)).
			econstructor.
			- econstructor. by inversion H5.
			rewrite -(cats0 ((ts_sub ++ [valtype_I32]) ++ [t])).
			by eapply instrtype_sub_add_same.
		}
		eapply construct_ais_typing_single.
		eapply Admin_instr_ok__instr with (v_instr := (TABLE_FILL x)).
		econstructor; eq_to_prop; eauto.

		eapply instrtype_sub_trans.
		eapply Hsubfinal_0.

		eapply instrtype_sub_iff_resulttype_sub'.
		unfold_instrtype_sub Hsub1_0; eapply resulttype_sub_empty in Hsub4; subst.

		eapply resulttype_sub_app.
		2: eapply Hsub7.
		rewrite -catA; simpl.
		rewrite H9.
		by rewrite cats0.
	}
	{ (* Table_copy *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.

		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H5.
		simpl in Hai; extract_premise.
		typing_inversion H4.
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
			eapply construct_ai_const_I32.
			- by inversion H4.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H3.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := TABLE_GET y).
			econstructor; eq_to_prop; eauto.
			eexists [valtype_I32],[valtype_I32],[valtype_I32],[valtype_reftype extr].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := TABLE_SET x).
			econstructor; eq_to_prop; eauto.
			simpl.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H6.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H7.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H8.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := TABLE_COPY x y).
			econstructor; eq_to_prop; eauto.
			simpl.
			eapply instrtype_sub_refl.
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
			eapply construct_ai_const_I32.
			- by inversion H5.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H6.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := TABLE_GET y).
			econstructor; eq_to_prop; eauto.
			eexists [valtype_I32],[valtype_I32],[valtype_I32],[valtype_reftype extr].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := TABLE_SET x).
			econstructor; eq_to_prop; eauto.
			simpl.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H7.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H8.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H9.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := TABLE_COPY x y).
			econstructor; eq_to_prop; eauto.
			simpl.
			eapply instrtype_sub_refl.
		}
	}
	{ (* Table_init zero *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		simpl in Hai; extract_premise.
		rename Hsub into Hsubfinal.

		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H5.
		simpl in Hai; extract_premise.
		typing_inversion H4.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [valtype_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [valtype_I32; valtype_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub1) in Hsubfinal.

		eapply ais_empty_typing.
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
		eapply Forall2_nth2 in HIT1 as [HLen HElem].
		pose proof H13 as H13_0.
		eapply HElem in H13.
		destruct_all.

		eapply minst_invert_tables in HIT1_0; eauto.
		eapply Forall2_nth2 in HIT1_0 as [HLen2 HTable].
		pose proof H3 as H3_0.
		eapply HTable in H3.
		destruct_all.

		clear HElem HTable.

		rewrite /lookup_total in H18.
		list_to_seq.
		rewrite /fun_elem /lookup_total H18 /=.
		rewrite /fun_elem /lookup_total H18 /= in H.

		eapply Forall_nth' in H17; eauto.

		remember (nth default_val (context_ELEMS v_C') (proj_uN_0 y))
			as e_t.
		remember ((nth default_val extr (proj_uN_0 (the (proj_num__0 i)))))
			as e_v.
		rewrite -Heqe_t in H19 H17.
		rewrite -Heqe_v.

		eapply construct_ais_subtyping; eauto.
		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H5.
			eapply instrtype_sub_refl.
		}
		{
			instantiate (1 := [valtype_I32; valtype_reftype e_t]).
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
			inversion H17.
			all: list_to_seq.
			{	
				rewrite -Heqe_v in H23; rewrite -H23.
				rewrite H22.
				eapply Admin_instr_ok__instr with (v_instr := REF_NULL e_t).
				econstructor.
			}
			{
				rewrite -Heqe_v in H20; rewrite -H20.
				eapply Admin_instr_ok__ref; eauto.
			}
			{
				rewrite -Heqe_v in H23; rewrite -H23.
				eapply ref_extern; eauto.
			}
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := TABLE_SET x).
			econstructor; eq_to_prop; eauto.
			rewrite /lookup_total in H12.
			rewrite H19 in H12.
			inversion H12; subst.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H6.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H7.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H8.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := TABLE_INIT x y).
			econstructor; eq_to_prop; eauto.
			- rewrite /lookup_total in H12.
				rewrite H19 in H12.
				inversion H12; subst; eauto.
			eapply instrtype_sub_refl.
		}
	}
	{ (* Load None *)
		typing_inversion HType.
		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H5.
		destruct nt;
		simpl in Hai; extract_premise.
		all: eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		
		all: eapply construct_ais_typing_single; eauto.
		- eapply Admin_instr_ok__instr with (v_instr := (CONST I32 c)). 
			econstructor. econstructor.
			by inversion H0.
		- eapply Admin_instr_ok__instr with (v_instr := (CONST I64 c)). 
			econstructor. econstructor.
			by inversion H0.
		- eapply Admin_instr_ok__instr with (v_instr := (CONST F32 c)). 
			econstructor. econstructor.
			by inversion H0.
		- eapply Admin_instr_ok__instr with (v_instr := (CONST F64 c)). 
			econstructor. econstructor.
			by inversion H0.
	}
	{ (* Load Inn *)
		typing_inversion HType.
		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H5.
		destruct v_Inn;
		simpl in Hai; extract_premise.
		all: 
			eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0;
			eapply construct_ais_typing_single; eauto.
		- (* I32 case *)
			eapply Admin_instr_ok__instr with (v_instr := (CONST I32
				(mk_num__0 Inn_I32 (extend__ v_n 32 v_sx c)))).
			econstructor.
			econstructor.
			by inversion H1.
		- (* I64 case *)
			eapply Admin_instr_ok__instr with (v_instr := (CONST I64
				(mk_num__0 Inn_I64 (extend__ v_n 64 v_sx c)))).
			econstructor.
			econstructor.
			by inversion H1.
	}
	(* SIMD instructions *) 
	1-5: admit.
	{ (* Memory_size *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		eapply Admin_instr_ok__instr with
			(v_instr := (CONST I32 (mk_num__0 Inn_I32 (mk_uN v_n)))).
		econstructor.
		econstructor.
		by inversion H.
	}
	{ (* Memory_fill *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.

		typing_inversion H2.
		simpl in Hai; extract_premise.


		typing_inversion H4.
		typing_inversion H3.
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
			eapply construct_ai_const_I32.
			- by inversion H3.
			eapply instrtype_sub_refl.
		}
		{
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
			eapply Admin_instr_ok__instr with (v_instr :=
				STORE I32 (Some (mk_sz 8)) memarg0).
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. } 
			rewrite Hnti.
			eapply store_pack; eauto.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H4.
			eapply instrtype_sub_refl.
		}
		{
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
			eapply construct_ai_const_I32.
			- by inversion H5.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := MEMORY_FILL).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
	}
	{ (* Memory_copy *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.

		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H5.
		simpl in Hai; extract_premise.
		typing_inversion H4.
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
			eapply instrtype_sub_refl.
		}
		{
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
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr :=
				LOAD I32 (Some (mk_loadop__0 Inn_I32
					(mk_loadop_Inn (mk_sz 8) U))) memarg0).
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			(* Well-formedness check *)
			- econstructor.
				econstructor.
				- econstructor; eauto. econstructor; eauto. econstructor; eauto.
				- eauto.
				- econstructor. econstructor. eauto.
				- econstructor. econstructor. eauto.
			simpl.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[valtype_I32],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr :=
				STORE I32 (Some (mk_sz 8)) memarg0).
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H7.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H8.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H9.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := MEMORY_COPY).
			econstructor; eauto.
			eapply instrtype_sub_refl.
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
			eapply construct_ai_const_I32.
			- by inversion H5. 
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H6.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr :=
				LOAD I32 (Some (mk_loadop__0 Inn_I32 
				(mk_loadop_Inn (mk_sz 8) U))) memarg0).
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			- (* Wellformedness check *)
				econstructor; econstructor; econstructor; eauto.
				econstructor; eauto.
				econstructor; eauto.
			simpl.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[valtype_I32],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr :=
				STORE I32 (Some (mk_sz 8)) memarg0).
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32; eauto.
			eapply instrtype_sub_refl.
		}
		{
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
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H10.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr := MEMORY_COPY).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
	}
	{ (* Memory_init 0 *)
		repeat rewrite -(cat1s _ (_ :: _)) in HType.	
		typing_inversion HType.
		rename Hai into Haifinal.
		rename Hsub into Hsubfinal.

		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H5.
		simpl in Hai; extract_premise.
		typing_inversion H4.
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
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H6.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr :=
				STORE I32 (Some (mk_sz 8)) memarg0).
			assert (I32 = numtype_Inn (Inn_I32)) as Hnti. { auto. }
			rewrite Hnti.
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H7.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H8.
			instantiate (1 := [valtype_I32; valtype_I32]).
			eexists [valtype_I32],[valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			- by inversion H9.
			instantiate (1 := [valtype_I32; valtype_I32; valtype_I32]).
			eexists [valtype_I32; valtype_I32],[valtype_I32; valtype_I32],[],[valtype_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply Admin_instr_ok__instr with (v_instr :=
				MEMORY_INIT x).
			econstructor; eq_to_prop; eauto.
			eapply instrtype_sub_refl.
		}
	}
Admitted.

Lemma step_moduleinst: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' v_tf,
	Step (mk_config (mk_state v_s v_f) v_ais)
		(mk_config (mk_state v_s' v_f') v_ais') ->
	Store_ok v_s ->
    Module_instance_ok v_s (frame_MODULE v_f) v_C ->
	inst_match v_C v_C' ->
	Admin_instrs_ok v_s v_C' v_ais v_tf ->
	Module_instance_ok v_s' (frame_MODULE v_f') v_C.
Proof.
	move => s f ais s' f' ais' C C' tf HReduce HStore HMi Him HType.
	erewrite <- reduce_inst_unchanged; eauto.
	eapply store_extension_moduleinst; eauto.
	eapply store_extension_reduce; eauto.
Qed.


Lemma t_preservation_type: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' t1s t2s,
  Step (mk_config (mk_state v_s v_f) v_ais) (mk_config (mk_state v_s' v_f') v_ais') ->
  Store_ok v_s ->
  Store_ok v_s' ->
	Store_extension v_s v_s' -> 
  Module_instance_ok v_s (frame_MODULE v_f) v_C ->
  Module_instance_ok v_s' (frame_MODULE v_f) v_C ->
	Vals_ok v_s (LOCALS v_f) (context_LOCALS v_C')->
	inst_match v_C v_C' ->
  Admin_instrs_ok v_s v_C' v_ais (t1s :-> t2s) ->
  Admin_instrs_ok v_s' v_C' v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' t1s t2s HReduce HST1 HST2 HSExt HIT1 HIT2 HValOK Him.
	move: v_C v_C' HIT1 HIT2 HValOK Him t1s t2s.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	remember (mk_config (mk_state v_s' v_f') v_ais') as c2.
	generalize dependent v_ais.
	generalize dependent v_ais'.
	generalize dependent v_f.
	generalize dependent v_f'.
	dependent induction HReduce;
	move => r_v_f' r_v_f v_ais' Heqc2 v_ais Heqc1 v_C v_C' HIT1 HIT2 HValOK Him tx ty HType;
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
	- (* Step_read *) eapply t_read_preservation; eauto.
	{ (* Context Label *) 
		typing_inversion HType.
		unfold_principal_typing Hai; extract_premise.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		econstructor; eq_to_prop; eauto.
	}
	{ (* Context Frame *)
		invert_ais_typing.
		resolve_all_pt; subst.

		inversion H1; subst.
		inversion H0; subst.

		remember ({|
			context_TYPES := [];
			context_FUNCS := [];
			context_GLOBALS := [];
			context_TABLES := [];
			context_MEMS := [];
			context_ELEMS := [];
			context_DATAS := [];
			context_LOCALS := t_lst;
			LABELS := [];
			context_RETURN := None
		|} @@ C0) as C0_l.
		remember ({|
			context_TYPES := [];
			context_FUNCS := [];
			context_GLOBALS := [];
			context_TABLES := [];
			context_MEMS := [];
			context_ELEMS := [];
			context_DATAS := [];
			context_LOCALS := [];
			LABELS := [];
			context_RETURN := Some (mk_list valtype extr)
		|} @@ C0_l) as C0_lr.
		eapply inst_t_context_local_empty in H as HC1empty.

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

		assert (Module_instance_ok v_s' (frame_MODULE f'') C0).
		{
			eapply step_moduleinst; eauto.
			subst; resolve_inst_match.
		}

		construct_ais_typing.
		econstructor; eauto.
		eapply mk_Thread_ok with (C := C0_l).
		{
			destruct f''.
			eapply reduce_inst_unchanged in HReduce.
			rewrite /= in HReduce; subst.
			eapply mk_Frame_ok; eauto.
			unfold Vals_ok in H4.
			by eapply Forall2_length in H4; eq_to_prop.
		}
		eapply IHHReduce; eauto; simpl; try by subst.
		{
			erewrite <- reduce_inst_unchanged in H5; eauto.
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
	}
	{ (* Context Instrs *)
		invert_ais_typing.
		eapply ais_vals_typing_inversion in HType1
			as [v_ts [HSub HValsok]].

		construct_ais_typing.
		{
			eapply construct_ais_vals; eauto.
			eapply store_extension_vals; eauto.
		}
		{
			eapply IHHReduce; eauto.
		}
		{
			eapply store_extension_ais; eauto.
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

		eapply construct_ais_typing_single.
		2: apply H3.
		eapply construct_ai_const_I32.

		inversion H1; subst; clear H.
		inversion H11; subst; clear H11.
		by inversion H9.
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

		eapply construct_ais_typing_single.
		2: apply H4.
		eapply construct_ai_const_I32.

		inversion H1; subst; clear H.
		inversion H10; subst; clear H10.
		by inversion H8.
	}
	(* The rest are all SIMD instructions *)
	1-2: admit.
	{ (* Memory grow *)
		invert_ais_typing.
		resolve_all_pt.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub0) in Hsub.
		eapply construct_ais_typing_single.
		2: apply Hsub.
		eapply construct_ai_const_I32.
		inversion H1; subst; clear H.
		inversion H10; subst; clear H10.
		by inversion H7.
	}
	{ (* Memory Grow fail *)
		typing_inversion HType.
		
		typing_inversion H2.
		simpl in Hai; extract_premise.

		typing_inversion H3.
		simpl in Hai; extract_premise.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		eapply construct_ais_typing_single.
		2: apply Hsub0.
		eapply construct_ai_const_I32.
		inversion H1; subst; clear H.
		inversion H8; subst; clear H8.
		by inversion H5.
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
	rename H3 into HStore1.
	rename H4 into HThread1.
	(* Store_ok store1 *)
	inversion HStore1.
	(* Thread_ok store1 None frame1 l (mk_list _ v_t) *)
	inversion HThread1; clear HThread1.
	rename H17 into HFrame1.
	(* Frame_ok store1 frame1 v_C *)
	inversion HFrame1; clear HFrame1.
	rename H17 into HModuleInst1.
	rename H22 into HAIs1.
	(* Module_instance_ok store1 v_moduleinst v_C0 *)
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
		context_FUNCS := functype'_lst;
		context_GLOBALS := globaltype_lst0;
		context_TABLES := tabletype_lst0;
		context_MEMS := memtype_lst0;
		context_ELEMS := reftype_lst0;
		context_DATAS := datatype_lst;
		context_LOCALS := [];
		LABELS := [];
		context_RETURN := None
	|} as v_C0.

	assert (Store_extension store1 store2 /\ Store_ok store2) as
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
					(_append t_lst1 (context_LOCALS v_C0))
					(_append (option_map [eta (mk_list _)] None)
						(context_RETURN v_C0)))
			([] :-> (mk_list valtype t_lst)) 
			). all:  subst; auto.
		by resolve_inst_match.
	}
	apply reduce_inst_unchanged in HReduce as HModuleInst.
	destruct frame2 as [locals2 module2].
	simpl in HModuleInst.
	assert (Module_instance_ok store2 v_moduleinst v_C0). {
		apply (store_extension_moduleinst store1); eauto.
	}

	apply mk_Config_ok; auto.
	rewrite Heqframe1 in HModuleInst; simpl in HModuleInst.
	rewrite <- HModuleInst.
	eapply mk_Thread_ok; auto.
	{
		assert (Vals_ok store2 locals2 t_lst1).
		apply (t_preservation_vs_type) with
			(C := v_C0)
			(C' :=
				{|
				context_TYPES := functype_lst0;
				context_FUNCS := functype'_lst;
				context_GLOBALS := globaltype_lst0;
				context_TABLES := tabletype_lst0;
				context_MEMS := memtype_lst0;
				context_ELEMS := reftype_lst0;
				context_DATAS := datatype_lst;
				context_LOCALS := t_lst1;
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

		eapply (mk_Frame_ok store2 locals2 v_moduleinst t_lst1 v_C0); eq_to_prop; eauto.
		by eapply Forall2_length in H0.
	}
	subst.

	(* Actual Typing proof *)
	eapply t_preservation_type; eauto.
	simpl in *.
	by rewrite /_append /Append_List_ cats0 /=.
	by resolve_inst_match.
Qed.
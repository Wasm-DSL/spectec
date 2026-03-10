
From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping type_preservation_pure extension_lemmas axioms.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Import ListNotations.

Lemma inst_t_context_local_empty: forall s i C,
	Module_instance_ok s i C ->
    C_LOCALS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.

Lemma inst_t_context_labels_empty: forall s i C,
	Module_instance_ok s i C ->
    C_LABELS C = [].
Proof.
	move => s i C HMInst. inversion HMInst => //=.
Qed.

Lemma t_preservation_vs_type': forall s f ais s' f' ais' C C' t1s t2s,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Store_ok s -> 
    Module_instance_ok s (F_MODULE f) C ->
	Vals_ok s (F_LOCALS f) (C_LOCALS C') ->
	inst_match C C' ->
    Admin_instrs_ok s C' ais (t1s :-> t2s) ->
    Vals_ok s (F_LOCALS f') (C_LOCALS C').
Proof.
	move => s f ais s' f' ais' C C' t1s t2s HReduce HST HIT.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	move: C' t1s t2s.
	generalize dependent ais.
	generalize dependent ais'.

	induction HReduce => //;
	move => ais' Heqc1 ais Heqc2 C' t1s t2s HVals1 Hmatch HType;
	try (destruct v_z; subst);
	try (destruct v_z'; subst);
	try (apply config_same in Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]];
		apply config_same in Heqc2 as [Hafter1  [Hafter2  Hafter3]]);
	try (specialize (IHHReduce _ erefl _ erefl));
	subst; auto.
	{
		invert_ais_typing.
		eapply IHHReduce; eauto.
	}
	{
		invert_ais_typing.
		resolve_all_pt.
		assert (Vals_ok s (F_LOCALS f') (C_LOCALS C') =
			Vals_ok s (F_LOCALS f') (C_LOCALS (prepend_label C' extr))).
		{
			destruct C'; auto.
		}
		rewrite H.
		eapply IHHReduce; destruct C'; eauto.
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
    Module_instance_ok s (F_MODULE f) C ->
	Vals_ok s (F_LOCALS f) (C_LOCALS C') ->
	inst_match C C' ->
    Admin_instrs_ok s C' ais (t1s :-> t2s) ->
    Vals_ok s' (F_LOCALS f') (C_LOCALS C').
Proof.
	move => s f ais s' f' ais' C C' t1s t2s HReduce HST
		HStoreExt HMInst HValOK Him HType.
	eapply t_preservation_vs_type' in HValOK; eauto.
	eapply store_extension_vals in HValOK; eauto.
Qed.

Lemma store_extension_reduce: forall s f ais s' f' ais' C C' tf,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Module_instance_ok s (F_MODULE f) C ->
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
	move => f' f ais' Heqc2 ais Heqc1 tf C' HType C HIT HMatch;
	destruct tf as [[tf1] [tf2]].
	all: try (destruct v_z; 
	apply config_same in Heqc1; apply config_same in Heqc2; 
	destruct Heqc1; destruct Heqc2;
	subst; try (split => //; eapply store_extension_refl; eauto)).
	{ (* Label Seq *)
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		subst.
		typing_inversion HType.
		typing_inversion H2.
		eapply IHHReduce; eauto.
	}
	{ (* Label Context *) 
		injection Heqc1 as H1.
		injection Heqc2 as H2.
		rewrite <- H in HType.
		typing_inversion HType.
		Opaque fun_coec_instr__admininstr.
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
		Opaque fun_coec_instr__admininstr.
		unfold_principal_typing Hai.
		destruct_all.
		inversion H5; subst; clear H5.
		inversion H7; subst; clear H7.
		inversion H0; subst; clear H0.
		eapply IHHReduce; eauto.
		resolve_inst_match.
	}
	{ (* Global Set *) 
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.
		join_subtyping_eq Hsub Hsub0.
		eapply Val_ok_non_bot in HValok as Hnonbot.
		eapply valtype_sub_non_bot in Hsubv; eauto.
		subst. clear Hsub Hsubi Hnonbot.

		remember ((fun_proj_uN_0 32 v_x)) as v_i.
		remember ((lookup_total (MODULE_GLOBALS (F_MODULE f)) v_i)) as ga.
		remember  (s <| GLOBALS :=
			list_update_func (GLOBALS s) ga
			[eta set GLOB_VALUE (fun=> v_val)] |>) as s'.

		assert (
			ga < Datatypes.length (GLOBALS s) /\
			exists v, lookup_total (GLOBALS s) ga =
				{| GLOB_TYPE := mk_globaltype (Some MUT) t; GLOB_VALUE := v |})
			as [HLen [v_old HLookup]].
		{
			eapply minst_invert_globals in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in H0.
			rewrite H0 in H3.
			inversion H3; subst; clear H3.
			rewrite /lookup_total in H4.

			split. auto.
			by exists extr1.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_globalinst_1' := GLOBALS s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst;
			eapply global_set_global_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst :=
				list_update_func (GLOBALS s)
					ga
					[eta set GLOB_VALUE (fun=> v_val)])
			(v_tableinst := v_tableinst)
			(v_meminst := v_meminst)
			(v_eleminst := v_eleminst)
			(v_datainst := v_datainst)
			; auto;
			try solve [subst; auto];
			try solve eauto;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func {1}H2; eauto.
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

		remember ((fun_proj_uN_0 32 v_i)) as i.
		remember ((fun_proj_uN_0 32 v_x)) as j.
		remember ((lookup_total (MODULE_TABLES (F_MODULE f)) j)) as tba.
		remember  (s <| TABLES :=
			list_update_func (TABLES s) tba
			(λ v_1 : tableinst, v_1
				<| TAB_REFS := list_update_func (TAB_REFS v_1) i (fun=> v_ref)
			|>) |>) as s'.

		assert (
			tba < Datatypes.length (TABLES s) /\
			exists v_lim_1 tbr,
				(Limits_sub v_lim_1 extr0) /\
				((lookup_total (TABLES s) tba) =
					{| TAB_TYPE := (mk_tabletype v_lim_1 t); TAB_REFS := tbr |}))
			as [HLen [v_lim_1 [tbr [HLimSub HLookup]]]].
		{
			eapply minst_invert_tables in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in H0.
			rewrite H0 in H3.
			inversion H3; subst; clear H3.
			rewrite /lookup_total in H5.

			split. auto.
			by exists extr1, extr3.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_tableinst_1' := TABLES s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst; rewrite {1}/set /=.
			eapply table_set_table_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst := v_globalinst)
			(v_tableinst := list_update_func (TABLES s) tba
				(λ v_1 : tableinst, v_1 <| TAB_REFS :=
					list_update_func (TAB_REFS v_1) i (fun=> v_ref)
				|>))
			(v_meminst := v_meminst)
			(v_eleminst := v_eleminst)
			(v_datainst := v_datainst)
			; auto;
			try solve [subst; auto];
			try solve eauto;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func {1}H3; eauto.
		- {
			eapply construct_tableinsts; subst; eauto.
		}
	}
	{ (* Table Grow *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.
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
		inversion H; subst.

		remember ((fun_proj_uN_0 32 v_x)) as i.
		remember ((lookup_total (MODULE_TABLES (F_MODULE f)) i)) as tba.
		remember ((mk_limits (mk_uN 32 (Datatypes.length v_r' + v_n)) v_j))
			as v_limits_new.
		remember (({| TAB_TYPE := mk_tabletype v_limits_new v_rt;
			TAB_REFS := v_r' ++ repeat v_ref v_n |})) as v_ti.
		remember  (s <| TABLES := list_update_func (TABLES s) tba
					(fun=> v_ti) |>) as s'.

		assert (
			tba < Datatypes.length (TABLES s) /\
			((Datatypes.length v_r' + v_n) <= v_j) /\
			(t = v_rt) /\
			((lookup_total (TABLES s) tba) =
				{| TAB_TYPE := mk_tabletype
					(mk_limits (mk_uN 32 (Datatypes.length v_r')) v_j)
					t;
					TAB_REFS := v_r' |}))
			as [HLen [HRange [tbr HLookup]]].
		{
			eapply minst_invert_tables in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in H0.
			rewrite H0 in H4.
			inversion H4; clear H4.
			rewrite -H10 in H8; rewrite -H10; clear H10.
			rewrite -H9 in H3; clear H9.

			rewrite /lookup_total in Heqtba.
			rewrite -Heqtba in H1.
			rewrite -Heqtba /lookup_total in H8.

			eapply s_invert_tables in HStore as [tbts HTable].
			pose proof H1 as H1_0.
			eapply Forall2_nth in HTable as [HLen HTable].
			eapply HTable in H1.
			destruct_all.

			rewrite H7 in H1.
			rewrite /lookup_total H1 in H2.
			inversion H2; clear H2.
			rewrite /lookup_total H1.
			rewrite H1 in H8.
			inversion H8; clear H8.

			split. subst; auto.
			inversion H; subst.
			inversion H17; subst; clear H17.
			rewrite -H9 in H18.
			auto.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_tableinst_1' := TABLES s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst; rewrite {1}/set /=.
			eapply table_grow_table_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst := v_globalinst)
			(v_tableinst := list_update_func (TABLES s) tba (fun=> v_ti))
			(v_meminst := v_meminst)
			(v_eleminst := v_eleminst)
			(v_datainst := v_datainst)
			(v_tabletype := list_update_func (v_tabletype) tba (fun=>
				mk_tabletype
				(mk_limits (mk_uN 32 (Datatypes.length v_r' + v_n)) v_j)
				v_rt
			))
			; auto;
			try solve [subst; auto];
			try solve eauto;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite !list_update_length_func /= {1}H4 /=; eauto.
		- {
			rewrite Heqv_ti Heqv_limits_new /=.
			eapply construct_tableinsts_grow; subst; eauto.
		}
	}
	{ (* Elem Drop *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		remember ((fun_proj_uN_0 32 v_x)) as i.
		remember ((lookup_total (MODULE_ELEMS (F_MODULE f)) i)) as ea.
		remember  (s <| ELEMS :=
			list_update_func (ELEMS s) ea [eta set ELEM_REFS (fun=> [])] |>) as s'.

		assert (
			(ea < (List.length (ELEMS s))) /\
			exists v_rt v_ref,
				((lookup_total (ELEMS s) ea) =
					{| ELEM_TYPE := v_rt; ELEM_REFS := v_ref |}) /\
				(List.Forall (fun (v_ref : ref) => (Ref_ok s v_ref v_rt)) (v_ref)))
			as [HLen [v_rt [v_ref [HLookup HRefok]]]].
		{
			eapply minst_invert_elems in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in Heqea.
			rewrite -Heqea in H1.
			split; auto.

			rewrite -Heqea in H4.
			by exists (ListDef.nth i (C_ELEMS C') default_val), extr0.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_eleminst_1' := ELEMS s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst; rewrite {1}/set /=.
			eapply elem_drop_elem_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst := v_globalinst)
			(v_tableinst := v_tableinst)
			(v_meminst := v_meminst)
			(v_eleminst := list_update_func (ELEMS s) ea
				[eta set ELEM_REFS (fun=> [])])
			(v_datainst := v_datainst)
			; auto;
			try solve [subst; auto];
			try solve eauto;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func {1}H2; eauto.
		- eapply construct_eleminsts; subst; eauto.
	}
	{ (* Store None *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		simpl.

		assert (length (fun_nbytes_ v_nt v_c) = 
			(Nat.divmod (the (fun_size v_nt)) 7 0 7).1 )
			as Heqlen.
		{
			(* fun_nbytes_ not implemented *)
			by eapply fun_nbytes_len.
		}

		remember ((fun_proj_uN_0 32 v_i)) as i.
		remember (fun_proj_uN_0 32 (OFFSET v_ao)) as ao.
		remember ((lookup_total (MODULE_MEMS (F_MODULE f)) 0)) as ma.
		remember  (s <| MEMS :=
			list_update_func (MEMS s) ma
				(λ v_1,
				v_1 <| MEM_BYTES := list_slice_update (MEM_BYTES v_1) (i + ao) (Nat.divmod (the (fun_size v_nt)) 7 0 7).1
				(fun_nbytes_ v_nt v_c) |>)	
		|> ) as s'.

		assert (
			(ma < (List.length (MEMS s))) /\
			exists v_mt v_mt' v_b,
				((lookup_total (MEMS s) ma) =
					{| MEM_TYPE := v_mt; MEM_BYTES := v_b |}) /\
				((Memtype_sub v_mt v_mt'))
				)
			as [HLen [v_mt [v_mt' [v_b [HLookup HRefok]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in Heqma.
			rewrite -Heqma in H1.
			split; auto.

			rewrite -Heqma in H5.
			by exists extr, (ListDef.nth 0 (C_MEMS C') default_val), extr0.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_meminst_1' := MEMS s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst; rewrite {1}/set /=.
			eapply store_none_mem_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst := v_globalinst)
			(v_tableinst := v_tableinst)
			(v_meminst := list_update_func (MEMS s) ma
				(λ v_1 : meminst,
				v_1 <| MEM_BYTES := list_slice_update (MEM_BYTES v_1) (i + ao) (Nat.divmod (the (fun_size v_nt)) 7 0 7).1
				(fun_nbytes_ v_nt v_c) |>))
			(v_eleminst := v_eleminst)
			(v_datainst := v_datainst)
			; auto;
			try solve [subst; auto];
			try solve eauto;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func {1}H3; eauto.
		- {
			rewrite -Heqlen.
			eapply construct_meminsts; subst; eauto.
		}
	}
	{ (* Store Some I32 *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		simpl.

		assert (length (fun_ibytes_ v_n (fun_wrap__ 32 v_n v_c)) = 
			(Nat.divmod v_n 7 0 7).1 )
			as Heqlen.
		{
			(* fun_ibytes_ fun_wrap__ not implemented *)
			by eapply fun_ibytes_32_len.
		}

		remember ((fun_proj_uN_0 32 v_i)) as i.
		remember (fun_proj_uN_0 32 (OFFSET v_ao)) as ao.
		remember ((lookup_total (MODULE_MEMS (F_MODULE f)) 0)) as ma.
		remember  (s <| MEMS :=
			list_update_func (MEMS s) ma
				(λ v_1,
				v_1 <| MEM_BYTES := list_slice_update (MEM_BYTES v_1) (i + ao) (Nat.divmod v_n 7 0 7).1
				(fun_ibytes_ v_n (fun_wrap__ 32 v_n v_c)) |>)	
		|> ) as s'.
		rewrite -Heqlen in Heqs'.

		assert (
			(ma < (List.length (MEMS s))) /\
			exists v_mt v_mt' v_b,
				((lookup_total (MEMS s) ma) =
					{| MEM_TYPE := v_mt; MEM_BYTES := v_b |}) /\
				((Memtype_sub v_mt v_mt'))
				)
			as [HLen [v_mt [v_mt' [v_b [HLookup HRefok]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in Heqma.
			rewrite -Heqma in H1.
			split; auto.

			rewrite -Heqma in H4.
			by exists extr, (ListDef.nth 0 (C_MEMS C') default_val), extr0.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_meminst_1' := MEMS s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst; rewrite {1}/set /=.
			eapply store_none_mem_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst := v_globalinst)
			(v_tableinst := v_tableinst)
			(v_meminst := list_update_func (MEMS s) ma
				(λ v_1 : meminst,
				v_1 <| MEM_BYTES := list_slice_update
					(MEM_BYTES v_1)
					(i + ao)
					(Datatypes.length (fun_ibytes_ v_n (fun_wrap__ 32 v_n v_c)))
					(fun_ibytes_ v_n (fun_wrap__ 32 v_n v_c)) |>))
			(v_eleminst := v_eleminst)
			(v_datainst := v_datainst)
			; auto;
			try solve [subst; auto];
			try solve eauto;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func {1}H2; eauto.
		- {
			eapply construct_meminsts; subst; eauto.
		}
	}
	{ (* Store Some I64 *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		simpl.

		assert (length (fun_ibytes_ v_n (fun_wrap__ 64 v_n v_c)) = 
			(Nat.divmod v_n 7 0 7).1 )
			as Heqlen.
		{
			(* fun_ibytes_ fun_wrap__ not implemented *)
			by eapply fun_ibytes_64_len.
		}

		remember ((fun_proj_uN_0 32 v_i)) as i.
		remember (fun_proj_uN_0 32 (OFFSET v_ao)) as ao.
		remember ((lookup_total (MODULE_MEMS (F_MODULE f)) 0)) as ma.
		remember  (s <| MEMS :=
			list_update_func (MEMS s) ma
				(λ v_1,
				v_1 <| MEM_BYTES := list_slice_update
				(MEM_BYTES v_1) (i + ao) (Nat.divmod v_n 7 0 7).1
				(fun_ibytes_ v_n (fun_wrap__ 64 v_n v_c)) |>)	
		|> ) as s'.
		rewrite -Heqlen in Heqs'.

		assert (
			(ma < (List.length (MEMS s))) /\
			exists v_mt v_mt' v_b,
				((lookup_total (MEMS s) ma) =
					{| MEM_TYPE := v_mt; MEM_BYTES := v_b |}) /\
				((Memtype_sub v_mt v_mt'))
				)
			as [HLen [v_mt [v_mt' [v_b [HLookup HRefok]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.

			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in Heqma.
			rewrite -Heqma in H1.
			split; auto.

			rewrite -Heqma in H4.
			by exists extr, (ListDef.nth 0 (C_MEMS C') default_val), extr0.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_meminst_1' := MEMS s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst; rewrite {1}/set /=.
			eapply store_none_mem_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst := v_globalinst)
			(v_tableinst := v_tableinst)
			(v_meminst := list_update_func (MEMS s) ma
				(λ v_1 : meminst,
				v_1 <| MEM_BYTES := list_slice_update
					(MEM_BYTES v_1)
					(i + ao)
					(Datatypes.length (fun_ibytes_ v_n (fun_wrap__ 64 v_n v_c)))
					(fun_ibytes_ v_n (fun_wrap__ 64 v_n v_c)) |>))
			(v_eleminst := v_eleminst)
			(v_datainst := v_datainst)
			; auto;
			try solve [subst; auto];
			try solve eauto;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite {1}list_update_length_func {1}H2; eauto.
		- {
			eapply construct_meminsts; subst; eauto.
		}
	}
	(* SIMD instructions *)
	1-5: admit.
	{ (* Memory Grow *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.
		simpl.

		clear Hsub Hsub0.

		remember ((lookup_total (MODULE_MEMS (F_MODULE f)) 0)) as ma.
		remember (s <| MEMS := list_update_func (MEMS s) ma (fun=> v_mi) |>) as s'.

		assert (
			(ma < (List.length (MEMS s))) /\
			exists v_mt' lim_old v_j v_b,
				((Memtype_sub (PAGE (mk_limits lim_old v_j)) v_mt')) /\
				(lookup_total (MEMS s) ma =
					{| MEM_TYPE := PAGE (mk_limits lim_old v_j); MEM_BYTES := v_b |}) /\
				(v_mi =
					{| MEM_TYPE := PAGE (mk_limits (lim_old + v_n) v_j);
					MEM_BYTES := v_b ++ repeat (mk_byte 0) (v_n * (64 * fun_Ki)) |}) /\
				(lim_old = (length v_b) / (64 * fun_Ki)) /\
				(lim_old + v_n <= v_j)
				)
			as [HLen [v_mt' [lim_old [v_j [v_b [HMemsub [HLookup [HNew [HLimold HRange]]]]]]]]].
		{
			eapply minst_invert_mems in HIT; eauto.
			eapply Forall2_nth2 in HIT as [_ HIT].
			eapply HIT in H1.
			destruct_all.
			rewrite /lookup_total in Heqma.
			rewrite -Heqma in H1 H4.
			split; auto.
			clear HIT.

			eapply s_invert_mems in HStore as [mts HMem].
			eapply Forall2_nth in HMem as [_ HForall].
			eapply HForall in H1.
			destruct_all.
			rewrite /lookup_total H1 in H4.
			inversion H4; clear H4.
			rewrite H10 in H1 H2; clear H10.
			rewrite H5 in H9.
			rewrite -H9 in H3; clear H9.
			rewrite H5 in H1.
			clear HForall.
			
			rewrite /lookup_total.

			rewrite /fun_mem in H; inversion H; subst; clear H.
			rewrite /lookup_total /= H1 in H4.
			inversion H4; subst; clear H4.

			exists (ListDef.nth 0 (C_MEMS C') default_val),
				(mk_uN 32 (Datatypes.length v_b / (64 * fun_Ki))),
				(mk_uN 32 extr4),
				(v_b).
			split. auto.
			split. auto.
			split. auto.
			split; auto.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_meminst_1' := MEMS s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst; rewrite {1}/set {2}/MEMS.
			eapply memory_grow_mem_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst := v_globalinst)
			(v_tableinst := v_tableinst)
			(v_meminst := list_update_func (MEMS s) ma
				(λ _,
				{| MEM_TYPE := PAGE (mk_limits (lim_old + v_n) v_j);
				MEM_BYTES := v_b ++ repeat (mk_byte 0) (v_n * (64 * fun_Ki)) |}))
			(v_eleminst := v_eleminst)
			(v_datainst := v_datainst)
			(v_memtype := list_update_func v_memtype ma
				(λ _, PAGE (mk_limits (lim_old + v_n) v_j)))
			; auto;
			try solve [subst; auto];
			try solve eauto;
			first [
				eapply store_extension_funcinsts; eauto |
				eapply store_extension_tableinsts; eauto |
				eapply store_extension_globalinsts; eauto |
				eapply store_extension_meminsts; eauto |
				eapply store_extension_eleminsts; eauto |
				eapply store_extension_datainsts; eauto |
				eauto
			].
		- rewrite !list_update_length_func {1}H3 /=; eauto.
		- {
			eapply construct_meminsts_grow; subst; eauto.
		}
	}
	{ (* Data Drop *)
		destruct_all; subst.
		invert_ais_typing.
		resolve_all_pt.

		remember ((fun_proj_uN_0 32 v_x)) as i.
		remember ((lookup_total (MODULE_DATAS (F_MODULE f)) i)) as da.
		remember (s <| DATAS :=
			list_update_func (DATAS s) da [eta set DATA_BYTES (fun=> [])] |>) as s'.

		assert (
			(List.length (MODULE_DATAS (F_MODULE f)) = (List.length (C_DATAS C'))) /\
			(da < (List.length (DATAS s))) /\
			exists v_b,
				((lookup_total (DATAS s) da) =
					{| DATA_BYTES := v_b |})
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
			split. by rewrite Heqda.
			exists extr.
			by rewrite Heqda.
		}

		assert (Store_extension s s').
		{
			eapply mk_Store_extension with
				(v_funcinst_2 := [])
				(v_tableinst_2 := [])
				(v_meminst_2 := [])
				(v_globalinst_2 := [])
				(v_eleminst_2 := [])
				(v_datainst_2 := [])
				(v_datainst_1' := DATAS s')
			; eauto;
			try solve [
				rewrite Heqs';
				by rewrite cats0 |
				by rewrite Heqs'; rewrite list_update_length_func
			].
			subst; rewrite {1}/set /=.
			eapply data_drop_data_extension; eauto.
		}
		split; auto.

		inversion HStore.
		eapply mk_Store_ok with
			(v_funcinst := v_funcinst)
			(v_globalinst := v_globalinst)
			(v_tableinst := v_tableinst)
			(v_meminst := v_meminst)
			(v_eleminst := v_eleminst)
			(v_datainst := list_update_func (DATAS s) da
				[eta set DATA_BYTES (fun=> [])])
			; auto;
			try solve [subst; auto];
			try solve eauto;
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
    F_MODULE f = F_MODULE f'.
Proof.
	move => s f ais s' f' ais' HReduce.
	remember (mk_config (mk_state s f) ais) as c1.
	remember (mk_config (mk_state s' f') ais') as c2.
	generalize dependent ais. generalize dependent ais'.
	induction HReduce; try intros; try (induction v_z); try induction v_z'; try (apply config_same in Heqc1;
	apply config_same in Heqc2; destruct Heqc1 as [? [? ?]];
	destruct Heqc2 as [? [? ?]]; subst => //);
	eapply IHHReduce; eauto.
Qed.

Lemma t_read_preservation: forall v_s v_f v_ais v_ais' v_C v_C' t1s t2s,
    Step_read (mk_config (mk_state v_s v_f) v_ais) v_ais' ->
    Store_ok v_s ->
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) (C_LOCALS v_C') (F_LOCALS v_f) ->
	inst_match v_C v_C' ->
    Admin_instrs_ok v_s v_C' v_ais (t1s :-> t2s) ->
    Admin_instrs_ok v_s v_C' v_ais' (t1s :-> t2s).
Proof.
	move => v_s v_f v_ais v_ais' v_C v_C' t1s t2s HReduce HST.
	move: v_C v_C' t1s t2s.
	remember (mk_config (mk_state v_s v_f) v_ais) as c1.
	induction HReduce;
	move => v_C v_C' tx ty HIT1 HValOK Him HType; decomp; destruct v_z; try eauto;
	try (apply config_same in Heqc1; destruct Heqc1 as [Hbefore1 [Hbefore2 Hbefore3]]; subst => //).
	all: try by eapply construct_ais_trap.
	{ (* Block *)
		typing_inversion HType.
		typing_inversion H2.
		simpl in Hai;
		extract_premise.
		vals_typing_inversion H1.

		assert (extr = v_t_1 /\ extr0 = v_t_2) as [He1 He2]. {
			by eapply bt_inversion; eauto.
		}
		subst.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub0) in Hsub
		as [Hsubi Hsubs].
		2: {
			eapply Forall2_length in Hforall.
			rewrite -H0 in Hforall. auto.
		}

		eapply construct_ais_typing_single with (ts1 := []) (ts2 := v_t_2).
		2: auto.
		eapply AI_ok_label; auto.
		{ eapply instrs_empty_typing. eapply resulttype_sub_refl. }

		eapply construct_ais_compose.
		{
			eapply construct_ais_vals; eauto.
			by eapply instrtype_sub_refl.
		}
		eapply construct_ais_instrtype_sub.
		{
			eapply AIs_ok_instrs.
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

		assert (extr = v_t_1 /\ extr0 = v_t_2) as [He1 He2]. {
			by eapply bt_inversion; eauto.
		}
		subst.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub0) in Hsub
		as [Hsubi Hsubs].
		2: {
			eapply Forall2_length in Hforall.
			rewrite -H0 in Hforall. auto.
		}

		eapply construct_ais_typing_single with (ts1 := []) (ts2 := v_t_2).
		2: auto.
		eapply AI_ok_label; auto.
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
				eapply AIs_ok_instrs.
				eapply H4.
			}
			by eapply instrtype_sub_refl.
		}
		eauto.
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
		econstructor; eauto.
		rewrite /lookup_total; auto.
		rewrite /lookup_total in H2 H0.
		rewrite H0 in H2.
		eauto.
	}
	{ (* Call_indirect *)
		rewrite /fun_table /= in H.
		rewrite /fun_table /lookup_total /= in H0.
		rewrite /fun_funcinst /= in H1.
		rewrite /fun_type /fun_funcinst /= in H2.

		invert_ais_typing.
		resolve_all_pt.
		join_subtyping_le Hsub0 Hsub.

		pose proof HIT1 as HIT1_0.
		eapply minst_invert_tables in HIT1; eauto.
		eapply Forall2_nth2 in HIT1 as [HLen HTable].
		eapply HTable in H3.
		destruct_all.

		eapply minst_invert_functypes in HIT1_0; eauto.
		rewrite -HIT1_0 H7 in H2.

		rewrite /lookup_total in H H10.
		rewrite H10 /= in H H0.

		eapply s_invert_funcs in HST as [fts HFunc].
		eapply Forall2_nth in HFunc as [HLen2 HFunc].
		pose proof H1 as H1_0.
		eapply HFunc in H1.
		destruct_all.

		construct_ais_typing.
		econstructor.
		econstructor; eauto.
		rewrite /lookup_total.
		rewrite Hextr0.
		rewrite /lookup_total Hextr0 /= in H2.
		rewrite H2.
		eauto.
	}
	{ (* Call_addr *)
		typing_inversion HType.
		vals_typing_inversion H1.
		typing_inversion H3.
		simpl in Hai;
		extract_premise.

		inversion H3; subst; clear H3.
		unfold fun_funcinst in *.
		rewrite H0 in H8.
		inversion H8; subst; clear H8.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub) in Hsub0
		as [Hsub0 Hsubs].
		2: {
			eapply Forall2_length in Hforall.
			rewrite H5 in Hforall.
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
		eapply AI_ok_frame.
		2: auto.

		(* Thread_ok *)
		invert_funcs.
		inversion HST; subst.
		eapply Forall2_nth in H4 as [_ H4].
		simpl in *.
		eapply H4 in H as Hfiok.
		unfold lookup_total in H0.
		rewrite H0 in Hfiok.
		inversion Hfiok; subst.

		eapply mk_Thread_ok with (v_C := ({|
			C_TYPES := [];
			C_FUNCS := [];
			C_GLOBALS := [];
			C_TABLES := [];
			C_MEMS := [];
			C_ELEMS := [];
			C_DATAS := [];
			C_LOCALS := extr ++ v_t;
			C_LABELS := [];
			C_RETURN := None
			|} @@ v_C0)).
		{
			eapply mk_Frame_ok with (v_t := extr ++ v_t); auto.
			{
				rewrite -!size_length.
				rewrite !size_cat.
				rewrite !size_map.
				auto.
			}
			subst.
			eapply Forall2_app; auto.
			clear H22 H0 Hfiok.
			induction v_t; eauto.
			simpl.
			econstructor.
			{
				destruct a; unfold fun_default_, the.
				all: try econstructor.
				
				eapply ok_reftype with (v_r := REF_NULL _) (v_rt := FUNCREF); econstructor.
				eapply ok_reftype with (v_r := REF_NULL _) (v_rt := EXTERNREF); econstructor.
				inversion H2; subst; contradiction.
			}
			eapply IHv_t; eauto.
			by inversion H2.
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

		eapply AIs_ok_instrs.

		inversion H22; subst.
		inversion H27; subst.
		inversion H21; subst.
		unfold _append, Append_context, _append_context, _append, Append_List_.
		simpl.
		unfold _append, Append_context, _append_context, _append, Append_List_ in H23.
		simpl in H23.
		rewrite !app_nil_r in H23.
		rewrite !app_nil_r.
		assert (injective (ListDef.map [eta LOCAL])) as map_local_inj.
		{
			eapply inj_map.
			unfold injective.
			move=> x1 x2 Hconstructor.
			by inversion Hconstructor.
		}
		eapply map_local_inj in H16; subst.
		auto.
	}
	{ (* Ref_func *)
		typing_inversion HType.
		simpl in Hai;
		extract_premise. subst.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		unfold fun_funcaddr in *; subst.
		eapply minst_invert_funcs in HIT1; eauto.
		eapply Forall2_nth2 in HIT1 as [HLen HFunc].
		eapply HFunc in H1.
		destruct_all.

		econstructor.
		econstructor; eauto.
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
		inversion HIT1; subst; simpl in *; subst.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		inversion H1; subst; unfold fun_coec_val__admininstr;
			unfold lookup_total in *.
		1,2:
			rewrite -H2;
			rewrite -H3.
		{
			eapply AI_ok_instr with (v_instr := (instr_CONST v_nt v_c_t)).
			econstructor.
		}
		{
			eapply AI_ok_instr with (v_instr := (instr_VCONST v_vt v_c_t)).
			destruct v_vt.
			econstructor.
		}
		rewrite -H; rewrite -H2.
		destruct v_r.
		{
			simpl.
			inversion H3; subst.
			eapply AI_ok_instr with (v_instr := (instr_REF_NULL v_rt)).
			constructor.
		}
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
		rewrite H4 /=.

		eapply s_invert_globals in HST as [gts HGlobal2].
		eapply Forall2_nth in HGlobal2 as [HLen2 HGlobal2].
		eapply HGlobal2 in H1.
		destruct_all.
		rewrite H5 in H1. clear H5.
		rewrite /lookup_total H3 in H0.
		inversion H0; subst; clear H0.
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
		eapply HTable in H1.
		destruct_all.

		rewrite H5 /= in H.
		rewrite H5 /=.

		eapply s_invert_tables in HST as [tbts HTableinst].
		eapply Forall2_nth in HTableinst as [HLen2 HTableinst].
		eapply HTableinst in H1.
		destruct_all.
		rewrite /lookup_total in H5.
		rewrite H5 in H1.
		inversion H1; subst; clear H1.

		eapply Forall_nth' in H8; eauto.
		rewrite /lookup_total in H0.
		rewrite H0 in H3.
		inversion H3; subst; clear H3.
		rewrite -H9 in H6.
		inversion H6; subst; clear H6.

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
		
		eapply AI_ok_instr with (v_instr := (instr_CONST I32 (mk_uN (fun_sizenn INN_I32)
		(Datatypes.length (TAB_REFS (fun_table (mk_state v_s v_f) v_x)))))).
		econstructor.
	}
	{ (* Table_fill *)
		typing_inversion HType.

		simpl in Hai; extract_premise.

		typing_inversion H4.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.
		
		typing_inversion H3.
		simpl in Hai; extract_premise.
		rewrite -(cats0 [VALTYPE_I32; t]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
		as [Hsub2 Hsubs].
		2: auto.

		eapply ais_empty_typing.
		by eapply instrtype_sub_empty.
	}
	{ (* Table_fill succ *)
		typing_inversion HType.

		simpl in Hai; extract_premise.
		pose proof H4 as H4_0.

		typing_inversion H4.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		pose proof Hsub0 as Hsub0_0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.
		
		typing_inversion H3.
		simpl in Hai; extract_premise.
		rewrite -(cats0 [VALTYPE_I32; t]) in Hsub0.
		pose proof Hsub1 as Hsub1_0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.
		rewrite cats0 in Hsub0.

		typing_inversion H2.
		simpl in Hai; extract_premise.
		pose proof Hsub2 as Hsub2_0.
		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
		as [Hsub2 Hsubs].
		2: auto.

		unfold_instrtype_sub Hsub0.
		assert ([VALTYPE_I32; t] = ts12_sup).
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

		assert ([AI_CONST I32 v_i; v_val: admininstr; AI_TABLE_SET v_x;
			AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1)); v_val: admininstr;
			AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (v_n - 1)); AI_TABLE_FILL v_x] =
			[AI_CONST I32 v_i; v_val: admininstr; AI_TABLE_SET v_x] ++
			[AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1)); v_val: admininstr;
			AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (v_n - 1)); AI_TABLE_FILL v_x]) as Happ. { auto. }

		rewrite Happ.
		rewrite !cats0.
		eapply construct_ais_compose.
		{
			eapply construct_ais_compose with
				(v_ais1 := [AI_CONST I32 v_i; v_val: admininstr]).
			{
				eapply construct_ais_compose with
					(v_ais1 := [AI_CONST I32 v_i]).
				{
					eapply construct_ais_typing_single.
					2: eapply Hsub_0.
					eapply AI_ok_instr with (v_instr := (instr_CONST I32 v_i)).
					econstructor.
				}
				eapply H4_0.
			}
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := (instr_TABLE_SET v_x)).
			econstructor. eauto. eauto.
			{
				eapply instrtype_sub_trans with (tf2 := ([VALTYPE_I32; t] :-> [])).
				{
					eapply instrtype_sub_iff_resulttype_sub'.
					eapply resulttype_sub_app' with
					(ts1_sub := [VALTYPE_I32; t])
					(ts1 := [VALTYPE_I32; extr: valtype])
					in Hsubs as [Hsubs1 Hsubs2]; auto.
				}
				by eapply instrtype_sub_add_same.
			}
		}
		eapply construct_ais_compose with
			(v_ais1 := [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1)); v_val: admininstr;
		AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (v_n - 1))]).
		{
			eapply construct_ais_compose with
			(v_ais1 := [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1)); v_val: admininstr]).
			{
				eapply construct_ais_compose with
			(v_ais1 := [AI_CONST I32 (mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1))]).
				{
					eapply construct_ais_typing_single.
					eapply AI_ok_instr with (v_instr := (instr_CONST I32
						(mk_uN (fun_sizenn INN_I32) (fun_proj_uN_0 32 v_i + 1))
					)).
					econstructor.
					by eapply instrtype_sub_add_same.
				}
				eapply construct_ais_typing_single.
				eapply construct_ai_val. eauto.

				rewrite -(cats0 (ts_sub ++ [VALTYPE_I32])).
				by eapply instrtype_sub_add_same.
			}
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := (instr_CONST I32
				(mk_uN (fun_sizenn INN_I32) (v_n - 1))
			)).
			econstructor.
			rewrite -(cats0 ((ts_sub ++ [VALTYPE_I32]) ++ [t])).
			by eapply instrtype_sub_add_same.
		}
		eapply construct_ais_typing_single.
		eapply AI_ok_instr with (v_instr := (instr_TABLE_FILL v_x)).
		econstructor; eauto.

		eapply instrtype_sub_trans.
		eapply Hsub2_0.

		eapply instrtype_sub_iff_resulttype_sub'.
		unfold_instrtype_sub Hsub1_0; eapply resulttype_sub_empty in Hsub4; subst.

		eapply resulttype_sub_app.
		2: eapply Hsub7.
		rewrite -catA; simpl.
		rewrite H2.
		by rewrite cats0.
	}
	{ (* Table_copy *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; VALTYPE_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub1) in Hsub2.

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
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_TABLE_GET v_y).
			econstructor; eauto.
			eexists [VALTYPE_I32],[VALTYPE_I32],[VALTYPE_I32],[extr: valtype].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_TABLE_SET v_x).
			econstructor; eauto.
			simpl.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32; VALTYPE_I32],[VALTYPE_I32; VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_TABLE_COPY v_x v_y).
			econstructor; eauto.
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
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_TABLE_GET v_y).
			econstructor; eauto.
			eexists [VALTYPE_I32],[VALTYPE_I32],[VALTYPE_I32],[extr: valtype].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_TABLE_SET v_x).
			econstructor; eauto.
			simpl.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32; VALTYPE_I32],[VALTYPE_I32; VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_TABLE_COPY v_x v_y).
			econstructor; eauto.
			simpl.
			eapply instrtype_sub_refl.
		}
	}
	{ (* Table_init zero *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; VALTYPE_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub1) in Hsub2.

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
		pose proof H3 as H3_0.
		eapply HElem in H3.
		destruct_all.

		eapply minst_invert_tables in HIT1_0; eauto.
		eapply Forall2_nth2 in HIT1_0 as [HLen2 HTable].
		pose proof H1 as H1_0.
		eapply HTable in H1.
		destruct_all.

		clear HElem HTable.

		rewrite /lookup_total in H6.
		rewrite /fun_elem /lookup_total H6 /=.
		rewrite /fun_elem /lookup_total H6 /= in H.

		eapply Forall_nth' in H5; eauto.

		remember (ListDef.nth (fun_proj_uN_0 32 v_y) (C_ELEMS v_C') default_val)
			as e_t.
		remember ((ListDef.nth (fun_proj_uN_0 32 v_i) extr default_val))
			as e_v.
		rewrite -Heqe_t in H5 H6.
		rewrite -Heqe_v.

		eapply construct_ais_subtyping; eauto.
		construct_ais_typing.
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			instantiate (1 := [VALTYPE_I32; e_t: valtype]).
			eapply construct_ais_typing_single.
			instantiate (2 := []).
			instantiate (1 := [e_t: valtype]).
			2: {
				eexists [VALTYPE_I32],[VALTYPE_I32],[],[e_t: valtype].
				split; auto.
				split; auto.
				split. eapply resulttype_sub_refl.
				split; eapply resulttype_sub_refl.
			}
			inversion H5.
			{
				eapply AI_ok_instr with (v_instr := instr_REF_NULL e_t).
				econstructor.
			}
			{
				eapply AI_ok_ref; eauto.
			}
			{
				eapply AI_ok_ref_extern; eauto.
			}
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_TABLE_SET v_x).
			econstructor; eauto.
			rewrite /lookup_total -Heqe_t.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32; VALTYPE_I32],[VALTYPE_I32; VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_TABLE_INIT v_x v_y).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
	}
	{ (* Load None *)
		typing_inversion HType.
		typing_inversion H1.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		destruct v_nt;
		simpl in Hai; extract_premise.
		all: eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		
		all: eapply construct_ais_typing_single; eauto.
		all: eapply AI_ok_instr with (v_instr := (instr_CONST _ v_c)).
		all: econstructor.
	}
	{ (* Load INN_I32 *)
		typing_inversion HType.
		typing_inversion H1.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		
		eapply construct_ais_typing_single; eauto.
		eapply AI_ok_instr with (v_instr := (instr_CONST INN_I32
			(fun_extend__ v_n (the (fun_size INN_I32)) v_sx v_c))).
		econstructor.
	}
	{ (* Load INN_I64 *)
		typing_inversion HType.
		typing_inversion H1.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.
		eapply (instrtype_sub_compose0 _ _ _ _ _ _ Hsub) in Hsub0.
		
		eapply construct_ais_typing_single; eauto.
		eapply AI_ok_instr with (v_instr := (instr_CONST INN_I64
			(fun_extend__ v_n (the (fun_size INN_I64)) v_sx v_c))).
		econstructor.
	}
	(* SIMD instructions *) 
	1-14: admit.
	{ (* Memory_size *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		eapply AI_ok_instr with
			(v_instr := (instr_CONST I32 (mk_uN (fun_sizenn INN_I32) v_n))).
		econstructor.
	}
	{ (* Memory_fill *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; t]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
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
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_val; eauto.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr :=
				instr_STORE INN_I32 (Some (mk_sz 8)) fun_memarg0).
			eapply instr_ok_store_pack; eauto.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_val; eauto.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32; VALTYPE_I32],[VALTYPE_I32; VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_MEMORY_FILL).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
	}
	{ (* Memory_copy *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; VALTYPE_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
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
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr :=
				instr_LOAD INN_I32 (Some (op_ INN_I32 (mk_sz 8) U)) fun_memarg0).
			econstructor; eauto.
			simpl.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[VALTYPE_I32],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr :=
				instr_STORE INN_I32 (Some (mk_sz 8)) fun_memarg0).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32; VALTYPE_I32],[VALTYPE_I32; VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_MEMORY_COPY).
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
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr :=
				instr_LOAD INN_I32 (Some (op_ INN_I32 (mk_sz 8) U)) fun_memarg0).
			econstructor; eauto.
			simpl.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[VALTYPE_I32],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr :=
				instr_STORE INN_I32 (Some (mk_sz 8)) fun_memarg0).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32; VALTYPE_I32],[VALTYPE_I32; VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr := instr_MEMORY_COPY).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
	}
	{ (* Memory_init 0 *)
		typing_inversion HType.
		simpl in Hai; extract_premise.

		typing_inversion H4.
		simpl in Hai; extract_premise.
		typing_inversion H3.
		simpl in Hai; extract_premise.
		typing_inversion H2.
		simpl in Hai; extract_premise.

		rewrite -(cats0 [VALTYPE_I32]) in Hsub.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub) in Hsub0.
		simpl in Hsub0.

		rewrite -(cats0 [VALTYPE_I32; VALTYPE_I32]) in Hsub0.
		eapply (instrtype_sub_compose2 _ _ _ _ _ _ _ Hsub0) in Hsub1.
		simpl in Hsub1.

		eapply (instrtype_sub_compose_eq _ _ _ _ _ _ _ Hsub1) in Hsub2
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
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr :=
				instr_STORE INN_I32 (Some (mk_sz 8)) fun_memarg0).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			eapply instrtype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32],[VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply construct_ai_const_I32.
			instantiate (1 := [VALTYPE_I32; VALTYPE_I32; VALTYPE_I32]).
			eexists [VALTYPE_I32; VALTYPE_I32],[VALTYPE_I32; VALTYPE_I32],[],[VALTYPE_I32].
			split; auto.
			split; auto.
			split. eapply resulttype_sub_refl.
			split; eapply resulttype_sub_refl.
		}
		{
			eapply construct_ais_typing_single.
			eapply AI_ok_instr with (v_instr :=
				instr_MEMORY_INIT v_x).
			econstructor; eauto.
			eapply instrtype_sub_refl.
		}
	}
Admitted.

Lemma step_moduleinst: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' v_tf,
	Step (mk_config (mk_state v_s v_f) v_ais)
		(mk_config (mk_state v_s' v_f') v_ais') ->
	Store_ok v_s ->
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
	inst_match v_C v_C' ->
	Admin_instrs_ok v_s v_C' v_ais v_tf ->
	Module_instance_ok v_s' (F_MODULE v_f') v_C.
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
    Module_instance_ok v_s (F_MODULE v_f) v_C ->
    Module_instance_ok v_s' (F_MODULE v_f) v_C ->
	Vals_ok v_s (F_LOCALS v_f) (C_LOCALS v_C')->
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
	try (destruct v_z; subst);
	try (destruct v_z'; subst); try eauto;
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
	{ (* Context Seq *)
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
	{ (* Context Label *) 
		typing_inversion HType.
		unfold_principal_typing Hai; extract_premise.

		eapply construct_ais_typing_single.
		2: eapply Hsub.
		econstructor; eauto.
	}
	{ (* Context Frame *)
		invert_ais_typing.
		resolve_all_pt; subst.

		inversion H1; subst.
		inversion H0; subst.

		remember ({|
			C_TYPES := [];
			C_FUNCS := [];
			C_GLOBALS := [];
			C_TABLES := [];
			C_MEMS := [];
			C_ELEMS := [];
			C_DATAS := [];
			C_LOCALS := v_t;
			C_LABELS := [];
			C_RETURN := None
		|} @@ v_C1) as v_C1_l.
		remember ({|
			C_TYPES := [];
			C_FUNCS := [];
			C_GLOBALS := [];
			C_TABLES := [];
			C_MEMS := [];
			C_ELEMS := [];
			C_DATAS := [];
			C_LOCALS := [];
			C_LABELS := [];
			C_RETURN := Some (mk_list valtype extr)
		|} @@ v_C1_l) as v_C1_lr.
		eapply inst_t_context_local_empty in H as HC1empty.

		assert (v_t = C_LOCALS v_C1_lr) as Heqv_t.
		{
			subst.
			simpl.
			rewrite HC1empty.
			by rewrite /_append /Append_List_ !app_nil_r.
		}
		
		assert (Vals_ok v_s' (F_LOCALS v_f'') v_t).
		{
			fold (Vals_ok v_s v_val v_t) in H3.
			rewrite Heqv_t.
			subst.
			eapply t_preservation_vs_type; eauto.
			{
				simpl.
				rewrite HC1empty.
				by rewrite /_append /Append_List_ !app_nil_r.
			}
			resolve_inst_match.
		}

		assert (Module_instance_ok v_s' (F_MODULE v_f'') v_C1).
		{
			eapply step_moduleinst; eauto.
			subst; resolve_inst_match.
		}

		construct_ais_typing.
		econstructor; eauto.
		eapply mk_Thread_ok with (v_C := v_C1_l).
		{
			destruct v_f''.
			eapply reduce_inst_unchanged in HReduce.
			rewrite /= in HReduce; subst.
			eapply mk_Frame_ok; eauto.
			by eapply Forall2_length in H4.
		}
		eapply IHHReduce; eauto; simpl; try by subst.
		{
			erewrite <- reduce_inst_unchanged in H5; eauto.
			eauto.
		}
		{
			subst. simpl.
			rewrite HC1empty /_append /Append_List_ app_nil_r.
			simpl.
			auto.
		}
	}
	(* The rest are all SIMD instructions *)
	1-5: admit.
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
	subst.

	remember {|
		FUNCS := v_funcinst; GLOBALS := v_globalinst; TABLES := v_tableinst;
		MEMS := v_meminst; ELEMS := v_eleminst;	DATAS := v_datainst
	|} as store1.
	remember {|
		MODULE_TYPES := v_functype0;
		MODULE_FUNCS := v_funcaddr;
		MODULE_GLOBALS := v_globaladdr;
		MODULE_TABLES := v_tableaddr;
		MODULE_MEMS := v_memaddr;
		MODULE_ELEMS := v_elemaddr;
		MODULE_DATAS := v_dataaddr;
		MODULE_EXPORTS := v_exportinst
	|} as v_moduleinst.
	remember {|
		F_LOCALS := v_val;
		F_MODULE := v_moduleinst
	|} as frame1.
	remember {|
		C_TYPES := v_functype0;
		C_FUNCS := v_functype';
		C_GLOBALS := v_globaltype0;
		C_TABLES := v_tabletype0;
		C_MEMS := v_memtype0;
		C_ELEMS := v_reftype0;
		C_DATAS := v_datatype;
		C_LOCALS := [];
		C_LABELS := [];
		C_RETURN := None
	|} as v_C0.

	assert (Store_extension store1 store2 /\ Store_ok store2) as
	[HStore_extension HStore2].
	{
		apply (store_extension_reduce 
			store1  
			{|F_LOCALS := v_val;F_MODULE := v_moduleinst|} 
			l
			store2
			frame2
			l0
			v_C0
			(upd_local_return v_C0
					(_append v_t1 (C_LOCALS v_C0))
					(_append (option_map [eta (mk_list _)] None)
						(C_RETURN v_C0)))
			([] :-> (mk_list valtype v_t)) 
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
		assert (Vals_ok store2 locals2 v_t1).
		apply (t_preservation_vs_type) with
			(C := v_C0)
			(C' :=
				{|
				C_TYPES := v_functype0;
				C_FUNCS := v_functype';
				C_GLOBALS := v_globaltype0;
				C_TABLES := v_tabletype0;
				C_MEMS := v_memtype0;
				C_ELEMS := v_reftype0;
				C_DATAS := v_datatype;
				C_LOCALS := v_t1;
				C_LABELS := [];
				C_RETURN := None
				|})
			(t1s := [])
			(t2s := (mk_list valtype v_t))
			(s := store1)
			(f := frame1)
			(f' := {| F_LOCALS := locals2; F_MODULE := module2 |})
			(ais := l)
			(ais' := l0)
			; eauto;
		try (subst; solve [
			auto |
			simpl; try rewrite cats0; auto |
			resolve_inst_match |
			subst; rewrite /_append /Append_context /_append_context
			/_append /Append_List_ (app_nil_r v_t1) in HAIs1; simpl in HAIs1; auto
		]).

		eapply (mk_Frame_ok store2 locals2 v_moduleinst v_C0 v_t1); eauto;
		by eapply Forall2_length in H0.
	}
	subst.

	(* Actual Typing proof *)
	eapply t_preservation_type; eauto.
	simpl in *.
	by rewrite /_append /Append_List_ app_nil_r /=.
	by resolve_inst_match.
Qed.
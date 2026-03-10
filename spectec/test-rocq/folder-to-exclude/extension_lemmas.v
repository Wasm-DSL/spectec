From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.
Require Import Stdlib.Program.Equality.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import RecordSetNotations.
From WasmSpectec Require Import wasm helper_lemmas helper_tactics typing_lemmas subtyping type_preservation_pure.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.
Import ListNotations.

Lemma Val_ok_store: forall f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 v t,
	Val_ok {| FUNCS := f1;
		GLOBALS := g1;
		TABLES := t1;
		MEMS := m1;
		ELEMS := e1;
		DATAS := d1 |} v t <->
	Val_ok {| FUNCS := f1;
		GLOBALS := g2;
		TABLES := t2;
		MEMS := m2;
		ELEMS := e2;
		DATAS := d2 |} v t.
Proof.
	assert (forall f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 v t,
		Val_ok {| FUNCS := f1;
			GLOBALS := g1;
			TABLES := t1;
			MEMS := m1;
			ELEMS := e1;
			DATAS := d1 |} v t ->
		Val_ok {| FUNCS := f1;
			GLOBALS := g2;
			TABLES := t2;
			MEMS := m2;
			ELEMS := e2;
			DATAS := d2 |} v t).
	{
		move => f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 v t HVal.
		inversion HVal; subst; econstructor.
		inversion H; subst; econstructor.
		inversion H0; subst; econstructor; eauto.
	}
	move => f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 v t.
	split; by eapply H.
Qed.

Lemma s_invert_funcs: forall s,
	Store_ok s ->
	exists fts,
	List.Forall2 (fun f t =>
		exists v_minst v_func,
		(f = {| FUNC_TYPE := t;
			FUNC_MODULE := v_minst;
			FUNC_CODE := v_func |})
			(* May add more here *)
	) (FUNCS s) fts.
Proof.
	move => s HSt.
	inversion HSt.
	rewrite H /=.
	clear -H1.
	exists v_functype.

	move : v_funcinst H1.
	induction v_functype; move => v_funcinst HFok.
	{
		inversion HFok; subst; auto.
	}
	destruct v_funcinst; inversion HFok; subst; auto.
	econstructor.
	{
		inversion H2; subst.
		by exists v_moduleinst, v_func.
	}
	by eapply IHv_functype.
Qed.

Lemma s_invert_globals: forall s,
	Store_ok s ->
	exists gts,
	List.Forall2 (fun g t =>
		exists v_mut v_vt v_v,
		(g = {| GLOB_TYPE := t;
			GLOB_VALUE := v_v |}) /\
		(t = (mk_globaltype v_mut (v_vt : valtype))) /\
		(Val_ok s v_v (v_vt : valtype))
	) (GLOBALS s) gts.
Proof.
	move => s HSt.
	inversion HSt.
	rewrite {2}H /=.
	clear -H3.
	exists v_globaltype.
	
	move : v_globalinst H3.
	induction v_globaltype; move => v_globalinst HGok.
	{
		inversion HGok; subst; auto.
	}
	destruct v_globalinst; inversion HGok; subst; auto.
	econstructor.
	{
		inversion H2; subst.
		by exists v_mut, v_vt, v_v.
	}
	by eapply IHv_globaltype.
Qed.

Lemma s_invert_mems: forall s,
	Store_ok s ->
	exists mts,
	List.Forall2 (fun m t =>
		exists v_b v_n v_m,
		(m = {| MEM_TYPE := t; MEM_BYTES := v_b |}) /\
		(t = (PAGE (mk_limits (mk_uN _ v_n) (mk_uN _ v_m)))) /\
		(v_n = (List.length v_b) / (64 * fun_Ki)) /\
		(v_n <= v_m) /\
		(v_m <= 2 ^ 16)
	) (MEMS s) mts.
Proof.
	move => s HSt.
	inversion HSt.
	rewrite H /MEMS.
	clear -H7.
	exists v_memtype.
	
	move : v_meminst H7.
	induction v_memtype; move => v_meminst HMok.
	{
		inversion HMok; subst; auto.
	}
	destruct v_meminst; inversion HMok; subst; auto.
	econstructor.
	{
		inversion H2; subst; clear H2.
		inversion H1; subst; clear H1.
		inversion H2; subst; clear H2.
		exists v_b, v_n, v_m.
		split; auto.
		split; auto.
		split; auto.
		rewrite H0.
		rewrite -mulnA.
		rewrite mulnE.
		rewrite Nat.div_mul; auto.
		rewrite /fun_Ki -mulnE; discriminate.
	}
	by eapply IHv_memtype.
Qed.

Lemma s_invert_tables: forall s,
	Store_ok s ->
	exists tbts,
	List.Forall2 (fun tb tbt =>
		exists v_ref v_m v_rt,
		(tb = {| TAB_TYPE := tbt;
			TAB_REFS := v_ref |}) /\
		(tbt = (mk_tabletype
			(mk_limits (mk_uN _ (List.length v_ref)) (mk_uN _ v_m)) v_rt)) /\
		(Tabletype_ok tbt) /\
		List.Forall (fun (v_ref : ref) => (Ref_ok s v_ref v_rt)) (v_ref)
	) (TABLES s) tbts.
Proof.
	move => s HSt.
	inversion HSt.

	rewrite {2}H /=.
	clear -H5.

	exists v_tabletype.
	move : v_tableinst H5.
	induction v_tabletype; move => v_tableinst HTok.
	{
		inversion HTok; subst; auto.
	}
	destruct v_tableinst; inversion HTok; subst; auto.
	econstructor.
	{
		inversion H2; subst.
		by exists v_ref, v_m, v_rt.
	}
	by eapply IHv_tabletype.
Qed.

Lemma se_invert_funcs: forall s s',
    Store_extension s s' ->
    exists fs' fs2,
        Forall2 (λ x x', Func_extension x x') (FUNCS s)
fs' /\
        FUNCS s' = fs' ++ fs2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
    exists v_funcinst_1', v_funcinst_2.
    auto.
Qed.

Lemma se_invert_tables: forall s s',
    Store_extension s s' ->
    exists tbs' tbs2,
        Forall2 (λ x x', Table_extension x x') (TABLES s)
tbs' /\
        TABLES s' = tbs' ++ tbs2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
    exists v_tableinst_1', v_tableinst_2.
    auto.
Qed.

Lemma se_invert_mems: forall s s',
    Store_extension s s' ->
    exists ms' ms2,
        Forall2 (λ x x', Mem_extension x x') (MEMS s)
ms' /\
        MEMS s' = ms' ++ ms2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
    exists v_meminst_1', v_meminst_2.
    auto.
Qed.

Lemma se_invert_globals: forall s s',
    Store_extension s s' ->
    exists gs' gs2,
        Forall2 (λ x x', Global_extension x x') (GLOBALS s)
gs' /\
        GLOBALS s' = gs' ++ gs2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
    exists v_globalinst_1', v_globalinst_2.
    auto.
Qed.

Lemma se_invert_elems: forall s s',
    Store_extension s s' ->
    exists es' es2,
        Forall2 (λ x x', Elem_extension x x') (ELEMS s)
es' /\
        ELEMS s' = es' ++ es2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
    exists v_eleminst_1', v_eleminst_2.
    auto.
Qed.

Lemma se_invert_datas: forall s s',
    Store_extension s s' ->
    exists ds' ds2,
        Forall2 (λ x x', Data_extension x x') (DATAS s)
ds' /\
        DATAS s' = ds' ++ ds2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
    exists v_datainst_1', v_datainst_2.
    auto.
Qed.

Lemma minst_invert_functypes: forall v_S v_minst C C',
	Module_instance_ok v_S v_minst C ->
	inst_match C C' ->
	(C_TYPES C') = (MODULE_TYPES v_minst).
Proof.
	move => v_S v_minst v_C v_C' HMi Him.
	inversion HMi; inversion Him; subst; auto.
Qed.

Lemma minst_invert_funcs: forall v_S v_minst C C',
	Module_instance_ok v_S v_minst C ->
	inst_match C C' ->
	List.Forall2 (fun fa ft => 
		exists v_minst1 v_func,
		(fa < (List.length (FUNCS v_S))) /\
		((lookup_total (FUNCS v_S) fa) =
			{| FUNC_TYPE := ft; FUNC_MODULE := v_minst1; FUNC_CODE := v_func |})
	) (MODULE_FUNCS v_minst) (C_FUNCS C').
Proof.
	move => v_S v_minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H1 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H1; eauto.
	econstructor; eauto.
	inversion H; subst; clear H.
	by exists v_minst, v_func.
Qed.

Lemma minst_invert_tables: forall v_S v_minst C C',
	Module_instance_ok v_S v_minst C ->
	inst_match C C' ->
	List.Forall2 (fun tba tbt => 
		exists rt lim lim' tbr,
		(tba < (List.length (TABLES v_S))) /\
		(tbt = (mk_tabletype lim' rt)) /\
		(Limits_sub lim lim') /\
		((lookup_total (TABLES v_S) tba) =
			{| TAB_TYPE := (mk_tabletype lim rt); TAB_REFS := tbr |})
	) (MODULE_TABLES v_minst) (C_TABLES C').
Proof.
	move => v_S v_minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H3 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H3; eauto.
	econstructor; eauto.
	inversion H; subst; clear H.
	inversion H6; subst; clear H6.
	by exists v_rt, v_lim_1, v_lim_2, v_ref.
Qed.

Lemma minst_invert_globals: forall v_S v_minst C C',
	Module_instance_ok v_S v_minst C ->
	inst_match C C' ->
	List.Forall2 (fun ga gt => 
		exists v_mut v_valtype v_val,
		(ga < (List.length (GLOBALS v_S))) /\
		(gt = (mk_globaltype v_mut v_valtype)) /\
		((lookup_total (GLOBALS v_S) ga) =
			{| GLOB_TYPE := (mk_globaltype v_mut v_valtype); GLOB_VALUE := v_val |})
	) (MODULE_GLOBALS v_minst) (C_GLOBALS C').
Proof.
	move => v_S v_minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H7 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H7; eauto.
	econstructor; eauto.
	inversion H; subst; clear H.
	by exists v_mut, v_valtype, v_val.
Qed.

Lemma minst_invert_mems: forall v_S v_minst C C',
	Module_instance_ok v_S v_minst C ->
	inst_match C C' ->
	List.Forall2 (fun ma mt => 
		exists v_mt v_b,
		(ma < (List.length (MEMS v_S))) /\
		((Memtype_sub v_mt mt)) /\
		((lookup_total (MEMS v_S) ma) = {| MEM_TYPE := v_mt; MEM_BYTES := v_b |})
	) (MODULE_MEMS v_minst) (C_MEMS C').
Proof.
	move => v_S v_minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H5 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H5; eauto.
	econstructor; eauto.
	inversion H; subst; clear H.
	by exists v_mt', v_b.
Qed.

Lemma minst_invert_elems: forall v_S v_minst C C',
	Module_instance_ok v_S v_minst C ->
	inst_match C C' ->
	List.Forall2 (fun ea et => 
		exists v_ref,
		(ea < (List.length (ELEMS v_S))) /\
		(List.Forall (fun (v_ref : ref) => (Ref_ok v_S v_ref et)) (v_ref)) /\
		((lookup_total (ELEMS v_S) ea) = {| ELEM_TYPE := et; ELEM_REFS := v_ref |})
	) (MODULE_ELEMS v_minst) (C_ELEMS C').
Proof.
	move => v_S v_minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H9 H10 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.
	simpl.

	move : C_ELEMS H10.
	induction v_elemaddr; move => C_ELEMS Heok. inversion Heok; subst; auto.
	destruct C_ELEMS. by inversion Heok.
	econstructor.
	{
		inversion Heok; subst.
		inversion H2; subst.
		inversion H9; subst.
		eexists v_ref.
		split; auto.
	}
	eapply IHv_elemaddr. by inversion H9.
	by inversion Heok.
Qed.

Lemma minst_invert_datas: forall v_S v_minst C C',
	Module_instance_ok v_S v_minst C ->
	inst_match C C' ->
	((List.length (MODULE_DATAS v_minst) = (List.length (C_DATAS C')))) /\
	List.Forall (fun da => 
		exists v_b,
		(da < (List.length (DATAS v_S))) /\
		((lookup_total (DATAS v_S) da) = {| DATA_BYTES := v_b |})
	) (MODULE_DATAS v_minst).
Proof.
	move => v_S v_minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	split.
	{
		by destruct v_C'; inversion Him; destruct_all; simpl in *; subst.
	}
	clear - H11 H12 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.
	simpl.

	move : H12.
	induction v_dataaddr; move => Hdok. inversion Hdok; subst; auto.
	econstructor.
	{
		inversion Hdok; subst.
		inversion H1; subst.
		inversion H11; subst.
		eexists v_b.
		split; auto.
	}
	eapply IHv_dataaddr. by inversion H11.
	by inversion Hdok.
Qed.

Ltac invert_funcs :=
	match goal with
	| H: Store_extension ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "fs'" in
		let v2 := fresh "fs2" in
		let v3 := fresh "Hfe" in
		let v4 := fresh "Hfeq" in
		eapply se_invert_funcs in H'
			as [v1 [v2 [v3 v4]]]
	| _ : _ |- _ => idtac
	end.

Ltac invert_tables :=
	match goal with
	| H: Store_extension ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "tbs'" in
		let v2 := fresh "tbs2" in
		let v3 := fresh "Htbe" in
		let v4 := fresh "Htbeq" in
		eapply se_invert_tables in H'
			as [v1 [v2 [v3 v4]]]
	| _ : _ |- _ => idtac
	end.

Ltac invert_mems :=
	match goal with
	| H: Store_extension ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "tbs'" in
		let v2 := fresh "tbs2" in
		let v3 := fresh "Htbe" in
		let v4 := fresh "Htbeq" in
		eapply se_invert_mems in H'
			as [v1 [v2 [v3 v4]]]
	| _ : _ |- _ => idtac
	end.

Ltac invert_elems :=
	match goal with
	| H: Store_extension ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "es'" in
		let v2 := fresh "es2" in
		let v3 := fresh "Hee" in
		let v4 := fresh "Heeq" in
		eapply se_invert_elems in H'
			as [v1 [v2 [v3 v4]]]
	| _ : _ |- _ => idtac
	end.

Ltac invert_datas :=
	match goal with
	| H: Store_extension ?s ?s' |- _ =>
		let H' := fresh "H'" in
		pose (H' := H);
		let v1 := fresh "ds'" in
		let v2 := fresh "ds2" in
		let v3 := fresh "Hde" in
		let v4 := fresh "Hdeq" in
		eapply se_invert_datas in H'
			as [v1 [v2 [v3 v4]]]
	| _ : _ |- _ => idtac
	end.


Lemma lookup_global: forall v_a v_C v_C' v_mut v_vt v_S v_minst,
	(v_a < (List.length (C_GLOBALS v_C'))) ->
	lookup_total (C_GLOBALS v_C') v_a = mk_globaltype v_mut v_vt ->
	Module_instance_ok v_S v_minst v_C ->
	inst_match v_C v_C' ->
	Store_ok v_S ->
	(Val_ok v_S (GLOB_VALUE (lookup_total 
		(GLOBALS v_S) (lookup_total (MODULE_GLOBALS v_minst) v_a))) (v_vt : valtype)).
Proof.
	move => v_a v_C v_C' v_mut v_vt v_S v_minst HLength HLookup HMIT Him HST.
	inversion HST; subst.
	inversion HMIT; subst.
	simpl in *; rewrite /lookup_total in HLookup.
	clear - HLength HLookup Him H3 H18.
	inversion Him; destruct_all; simpl in *; subst.

	eapply Forall2_nth in H18 as [Hl Hforall].
	rewrite -Hl in HLength.
	eapply Hforall
		in HLength as Heok.
	inversion Heok; subst; simpl in *.
	erewrite HLookup in H0; inversion H0; subst; clear H0.

	eapply Forall2_nth in H3 as [Hl2 Hforall2].
	eapply Hforall2
		in H2 as Hgok.
	inversion Hgok; subst; simpl in *; rewrite /lookup_total in H4.
	simpl in H4.
	erewrite H4 in H.
	rewrite H0 in H.
	inversion H; subst; clear H.

	by rewrite /lookup_total H4 => //.
Qed.

Lemma bt_inversion : forall v_S v_C v_C' r_v_f (v_bt: blocktype) ts1 ts2 bt1 bt2,
	Module_instance_ok v_S (F_MODULE r_v_f) v_C ->
	Blocktype_ok v_C' v_bt (ts1 :-> ts2) ->
	fun_blocktype (mk_state v_S r_v_f) v_bt = (bt1 :-> bt2) ->
	inst_match v_C v_C' ->
	(ts1 = bt1 /\ ts2 = bt2).
Proof.
	move=> v_S v_C v_C' r_v_f v_bt ts1 ts2 bt1 bt2 HM HB Hf Him.
	inversion HM; subst.
	unfold inst_match in Him.
	simpl in *; subst.
	unfold fun_blocktype in Hf;
	destruct v_bt.
	{
		destruct o;
		inversion Hf; subst;
		inversion HB; subst; auto.
	}
	unfold fun_type.
	inversion Hf; subst;
	inversion HB; subst.
	rewrite -H in H17; simpl in H17.
	destruct_all; subst.
	rewrite H22 in H17.
	by inversion H17.
Qed.

Lemma tc_func_reference2: forall v_S v_C v_minst idx tf v_type,
  lookup_total (MODULE_TYPES v_minst) idx = FUNC_TYPE v_type ->
  Module_instance_ok v_S v_minst v_C ->
  lookup_total (C_TYPES v_C) idx = tf ->
  tf = FUNC_TYPE v_type.
Proof.
	move => v_S v_C v_minst idx tf v_type H HMinst H1.
	inversion HMinst. subst. simpl in *. auto.
Qed.


Lemma store_typed_exterval_types: forall v_S v_f v_a,
	(v_a < List.length (FUNCS v_S))%coq_nat ->
	lookup_total (FUNCS v_S) v_a = v_f ->
    Store_ok v_S ->
    Externaddrs_ok v_S (EXTADDR_FUNC v_a) (EXT_FUNC (FUNC_TYPE v_f)).
Proof.
	move => v_S v_f v_a HLength H HST.
	inversion HST; subst; simpl in *.
	
	apply Forall2_lookup in H2; destruct H2.
	apply H0 in HLength as HFunc.
	simpl in *.
	inversion HFunc; subst; simpl in *.
	apply extaddr_ok_func with (v_minst := v_moduleinst) (v_func := v_func).
	- move/ltP: HLength => Hprop. auto.
	- simpl in *. auto.
Qed.

Lemma func_extension_refl0: forall f,
	Func_extension f f.
Proof.
	move => f.
	econstructor.
Qed.

Lemma func_extension_refl: forall f,
	Forall2 (fun v s => Func_extension v s) f f.
Proof.
	move => f.
	induction f => //.
	apply Forall2_cons_iff. split.
	- econstructor.
	- apply IHf.
Qed.

Lemma table_extension_refl0: forall t,
	Table_extension t t.
Proof.
	move => t.
	induction t => //.
	destruct TAB_TYPE, v_limits, v__.
	econstructor.
	auto.
Qed.

Lemma table_extension_refl: forall t,
	Forall2 (fun v s => Table_extension v s) t t.
Proof.
	move => t.
	induction t => //.
	apply Forall2_cons_iff. split.
	- eapply table_extension_refl0.
	- apply IHt.
Qed.

Lemma mem_extension_refl0: forall m,
	Mem_extension m m.
Proof.
	move => m.
	destruct m, MEM_TYPE, v_limits, v__.
	econstructor.
	auto.
Qed.

Lemma mem_extension_refl: forall m,
	Forall2 (fun v s => Mem_extension v s) m m.
Proof.
	move => m.
	induction m => //.
	apply Forall2_cons_iff. split.
	- by eapply mem_extension_refl0.
	- apply IHm.
Qed.

Lemma global_extension_refl_0: forall g,
	Global_extension g g.
Proof.
	move => g.
	destruct g.
	destruct GLOB_TYPE.
	econstructor.
	by right.
Qed.

Lemma global_extension_refl: forall g,
	Forall2 (fun v s => Global_extension v s) g g.
Proof.
	move => g.
	induction g.
	- econstructor.
	- econstructor.
	  + destruct a.
	    destruct GLOB_TYPE.
	  	econstructor.
		by right.
	  + by eapply IHg.
Qed.

Lemma elem_extension_refl0: forall g,
	Elem_extension g g.
Proof.
	move => g.
	destruct g.
	econstructor.
	by left.
Qed.

Lemma elem_extension_refl: forall g,
	Forall2 (fun v s => Elem_extension v s) g g.
Proof.
	move => g.
	induction g.
	- econstructor.
	- econstructor.
	  + by eapply elem_extension_refl0.
	  + by eapply IHg.
Qed.

Lemma data_extension_refl0: forall d,
	Data_extension d d.
Proof.
	move => g.
	destruct g.
	econstructor.
	by left.
Qed.

Lemma data_extension_refl: forall d,
	Forall2 (fun v s => Data_extension v s) d d.
Proof.
	move => g.
	induction g.
	- econstructor.
	- econstructor.
	  + by eapply data_extension_refl0.
	  + by eapply IHg.
Qed.

Lemma store_extension_refl: forall s,
    Store_extension s s.
Proof.
  move => s.
  eapply (mk_Store_extension s s
  (FUNCS s) (TABLES s) (MEMS s) (GLOBALS s) (ELEMS s) (DATAS s)
  (FUNCS s) [] (TABLES s) [] (MEMS s) [] (GLOBALS s) [] (ELEMS s) [] (DATAS s) [] ); eauto;
  repeat (try by rewrite -> cats0).
  + by apply func_extension_refl.
  + by apply table_extension_refl.
  + by apply mem_extension_refl.
  + by apply global_extension_refl.
  + by apply elem_extension_refl.
  + by apply data_extension_refl.
Qed.


Lemma funcinst_same: forall f1 f2,
	Forall2 (λ v_funcinst_1 v_funcinst_1' : funcinst, Func_extension v_funcinst_1 v_funcinst_1') f1 f2 ->
	f1 = f2.
Proof.
	move => f1 f2 Hfe.
	induction Hfe; eauto.
	by inversion H; subst.
Qed.

Lemma store_extension_ref: forall v_S v_S' v_t v_val,
	Store_extension v_S v_S' ->
	Ref_ok v_S v_val v_t ->
	Ref_ok v_S' v_val v_t.
Proof.
	move => v_S v_S' v_t v_val Hs Hv1.
	inversion Hs; subst.
	clear - Hv1 H12 H5.
	eapply funcinst_same in H12; subst.

	induction Hv1; try by constructor.
	econstructor.

	inversion H; subst; eauto; try econstructor.
	{
		rewrite H5.
		rewrite -size_length size_cat size_length.
		by eapply ltn_addr.
	}
	rewrite H5.
	rewrite -(lookup_app _ _ _ H3).
	eauto.
Qed.

Lemma store_extension_refs: forall v_S v_S' v_ts v_vals,
	Store_extension v_S v_S' ->
	List.Forall2 (fun v_t v_val => Ref_ok v_S v_val v_t) (v_ts) (v_vals) ->
	List.Forall2 (fun v_t v_val => Ref_ok v_S' v_val v_t) (v_ts) (v_vals).
Proof.
	move => v_S v_S' v_t v_val Hs Hv1.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply store_extension_ref; eauto.
Qed.

Lemma store_extension_val: forall v_S v_S' v_t v_val,
	Store_extension v_S v_S' ->
	Val_ok v_S v_val v_t ->
	Val_ok v_S' v_val v_t.
Proof.
	move => v_S v_S' v_t v_val Hs Hv1.
	inversion Hs; subst.
	clear - Hv1 H12 H5.
	eapply funcinst_same in H12; subst.

	induction Hv1; try by constructor.
	econstructor.

	inversion H; subst; eauto; try econstructor.
	inversion H0; subst; econstructor.
	- rewrite H5. rewrite -size_length size_cat.
		by eapply ltn_addr.
	- rewrite H5.
		rewrite /lookup_total -{1}app_cat.
		move/ltP in H4.
		rewrite (app_nth1 _ _ _ H4).
		rewrite /lookup_total in H6.
		eauto.
Qed.

Lemma store_extension_vals: forall v_S v_S' v_t v_val,
	Store_extension v_S v_S' ->
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
	eapply store_extension_val; eauto.
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

Lemma global_set_global_extension: forall v_g v_idx v_valtype v_val_0 v_val_1,
	(v_idx < length v_g) ->
	lookup_total v_g v_idx = 
		{| GLOB_TYPE := mk_globaltype (Some MUT) v_valtype; GLOB_VALUE := v_val_0 |} ->
	Forall2 (fun v s => Global_extension v s) v_g
		(list_update_func v_g v_idx (fun g => g <| GLOB_VALUE := v_val_1 |> )).
Proof.
	move => v_g v_i v_valtype v_val_0 v_val_1 HLength HLookup.
	move: v_g HLength HLookup.
	induction v_i.
	{ (* i = 0 *)
		move => v_g HLength HLookup.
		destruct v_g; auto.
		simpl.
		econstructor.
		{
			rewrite /lookup_total in HLookup.
			simpl in HLookup; subst.
			econstructor.
			by left.
		}
		eapply global_extension_refl.
	}
	move => v_g HLength HLookup.
	destruct v_g; auto.
	simpl.
	econstructor; try eapply global_extension_refl_0.
	by eapply IHv_i.
Qed.

Lemma store_none_mem_extension: forall v_ms v_idx v_mt v_b v_l v_n v_nb,
	(v_idx < length v_ms) ->
	lookup_total v_ms v_idx = {| MEM_TYPE := v_mt; MEM_BYTES := v_b |} ->
	Forall2 (λ v v', Mem_extension v v') v_ms
		(list_update_func v_ms v_idx
			(λ m, m <| MEM_BYTES :=
			list_slice_update (MEM_BYTES m) v_l v_n v_nb |>)).
Proof.
	move => v_ms v_idx v_mt v_b v_l v_n v_nb HLength HLookup.
	move : v_idx v_mt v_b v_l v_n v_nb HLength HLookup.
	induction v_ms; auto; move => v_idx v_mt v_b v_l v_n v_nb HLength HLookup.
	destruct v_idx; simpl.
	{
		econstructor.
		{
			destruct a; rewrite /set /=.
			destruct MEM_TYPE, v_limits, v__.
			econstructor.
			eauto.
		}
		eapply mem_extension_refl.
	}
	econstructor.
	eapply mem_extension_refl0.
	eapply IHv_ms; eauto.
Qed.

Lemma memory_grow_mem_extension: forall v_ms v_idx v_b v_i v_n v_j,
	(v_idx < length v_ms) ->
	lookup_total v_ms v_idx = {| MEM_TYPE := PAGE (mk_limits
				(mk_uN 32 v_i)
				v_j); MEM_BYTES := v_b |} ->
	v_i + v_n <= fun_proj_uN_0 32 v_j ->
	Forall2 (λ v v', Mem_extension v v') v_ms
		(list_update_func v_ms v_idx
			(fun=> {|
			MEM_TYPE := PAGE (mk_limits
				(mk_uN 32 (v_i + v_n)) v_j);
			MEM_BYTES := v_b ++ repeat (mk_byte 0) (v_n * (64 * fun_Ki))
		|})).
Proof.
	move => v_ms v_idx v_b v_i v_n v_j HLength HLookup HRange.
	move : v_idx v_b v_n v_j HLength HLookup HRange.
	induction v_ms; move => v_idx v_b v_n v_j HLength HLookup HRange; auto.
	destruct v_idx.
	{
		econstructor.
		{
			rewrite /lookup_total /ListDef.nth in HLookup.
			rewrite HLookup.
			destruct v_j.
			econstructor.
			simpl.
			by eapply leq_addr.
		}
		eapply mem_extension_refl.
	}
	simpl.
	econstructor.
	{
		eapply mem_extension_refl0.
	}
	eapply IHv_ms; auto.
Qed.

Lemma table_set_table_extension: forall v_tbs v_idx tbt tbr v_i v_tbr,
	(v_idx < length v_tbs) ->
	lookup_total v_tbs v_idx = 
		{| TAB_TYPE := tbt; TAB_REFS := tbr |} ->
	Forall2 (fun v v' => Table_extension v v') v_tbs
		(list_update_func v_tbs v_idx
			(fun tb => tb <| TAB_REFS :=
				list_update_func (TAB_REFS tb) v_i (fun=> v_tbr) |> )).
Proof.
	move => v_tbs v_i tbt tbr v_tbr HLength HLookup.
	move: v_tbs HLength HLookup.
	induction v_i.
	{ (* i = 0 *)
		move => v_tbs HLength HLookup.
		destruct v_tbs; auto.
		simpl.
		econstructor.
		{
			rewrite /lookup_total in HLookup.
			destruct t. simpl.
			rewrite /set /=.
			destruct TAB_TYPE, v_limits, v__.
			econstructor.
			auto.
		}
		eapply table_extension_refl.
	}
	move => v_tbs HLength HLookup.
	destruct v_tbs; auto.
	simpl.
	econstructor; try eapply table_extension_refl0.
	by eapply IHv_i.
Qed.

Lemma table_grow_table_extension: forall v_tbs v_idx j ref rt n tbr,
	(v_idx < length v_tbs) ->
	lookup_total v_tbs v_idx = 
		{| TAB_TYPE := mk_tabletype (mk_limits
					(mk_uN 32 (Datatypes.length tbr)) j) rt;
		TAB_REFS := tbr |} ->
	Forall2 (λ tb tb', Table_extension tb tb') v_tbs
		(list_update_func v_tbs	v_idx
			(fun=> {|
				TAB_TYPE := mk_tabletype (mk_limits
					(mk_uN 32 (Datatypes.length tbr + n)) j) rt;
				TAB_REFS := tbr ++ repeat ref n
		|})).
Proof.
	move => v_tbs v_idx j ref rt n tbr HLength HLookup.
	move: v_tbs HLength HLookup.
	induction v_idx.
	{
		move => v_tbs HLength HLookup.
		destruct v_tbs; auto.
		simpl.
		rewrite /lookup_total /= in HLookup.
		rewrite HLookup.
		econstructor.
		{
			destruct j.
			econstructor.
			simpl.
			eapply leq_addr.
		}
		eapply table_extension_refl.
	}
	move => v_tbs HLength HLookup.
	destruct v_tbs; auto.
	simpl.
	econstructor; try eapply table_extension_refl0.
	by eapply IHv_idx.
Qed.

Lemma elem_drop_elem_extension: forall es idx,
	(idx < length es) ->
	(Forall2 (λ v v' : eleminst, Elem_extension v v') es
		(list_update_func es idx
			[eta set ELEM_REFS (fun=> [])])).
Proof.
	move => es idx HLength.
	move : idx HLength.
	induction es; auto.
	move => idx HLength.
	destruct idx.
	{
		destruct a.
		econstructor.
		- econstructor. by right.
		- by eapply elem_extension_refl.
	}
	simpl.
	econstructor.
	- by eapply elem_extension_refl0.
	- by eapply IHes.
Qed.

Lemma data_drop_data_extension: forall ds idx,
	(idx < length ds) ->
	(Forall2 (λ v v', Data_extension v v') ds
		(list_update_func ds idx
			[eta set DATA_BYTES (fun=> [])])).
Proof.
	move => ds idx HLength.
	move : idx HLength.
	induction ds; auto.
	move => idx HLength.
	destruct idx.
	{
		destruct a.
		econstructor.
		- econstructor. by right.
		- by eapply data_extension_refl.
	}
	simpl.
	econstructor.
	- by eapply data_extension_refl0.
	- by eapply IHds.
Qed.

Lemma update_global_unchanged: forall v_S v_S' func v_idx,
	v_S' = v_S <| GLOBALS := list_update_func (GLOBALS v_S) v_idx func |> ->
	FUNCS v_S = FUNCS v_S' /\
	TABLES v_S = TABLES v_S' /\
	length (GLOBALS v_S) = length (GLOBALS v_S') /\
	MEMS v_S = MEMS v_S' /\
	ELEMS v_S = ELEMS v_S' /\
	DATAS v_S = DATAS v_S'.
Proof. 
	move => v_S v_S' func v_idx H.
	subst.
	destruct v_S; simpl.
	repeat split; eauto.
	by erewrite <- list_update_length_func.
Qed.

Lemma addrs_funcs_extension: forall v_S v_S' v_funcaddr v_funcinst_1' v_funcinst_2 v_ft,
	Externaddrs_ok v_S (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_ft) ->
	FUNCS v_S' = (v_funcinst_1' ++ v_funcinst_2) -> 
    Forall2 (fun v s => Func_extension v s) (FUNCS v_S) v_funcinst_1' ->
    Externaddrs_ok v_S' (EXTADDR_FUNC v_funcaddr) (EXT_FUNC v_ft).
Proof.
	move => v_S v_S' v_funcaddr v_funcinst_1' v_funcinst_2 v_ft HOk HApp Hext.
	inversion HOk. subst.
	apply Forall2_nth in Hext as [HLength Hext].
	eapply (Hext) in H2 as H4.
	eapply (extaddr_ok_func _ _ _ v_minst v_func).
	apply (length_app_lt) with (l':=(FUNCS v_S')) (l2':= v_funcinst_2) in HLength => //=.
	- apply/ltP.
	  eapply (Nat.lt_le_trans).
	  apply/ltP. by eapply H2.
	  eauto.
	- unfold lookup_total.
	  rewrite /lookup_total in H3.
		rewrite H3 in H4.
		rewrite HLength in H2.
		move/ltP in H2.
		apply app_nth1 with (l' := v_funcinst_2) (d := default_val) in H2.
		rewrite app_cat in H2.
		rewrite <- HApp in H2.
		rewrite H2.
		inversion H4; subst.
		auto.
Qed.

Lemma addrs_tables_extension: forall v_S v_S' v_tableaddr v_tableinst_1' v_tableinst_2 v_tabletype,
    Externaddrs_ok v_S (EXTADDR_TABLE v_tableaddr) (EXT_TABLE v_tabletype) ->
	TABLES v_S' = (v_tableinst_1' ++ v_tableinst_2) -> 
	Forall2 (fun v s => Table_extension v s) (TABLES v_S) v_tableinst_1' ->
    Externaddrs_ok v_S' (EXTADDR_TABLE v_tableaddr) (EXT_TABLE v_tabletype).
Proof.
	move => v_S v_S' v_tableaddr v_tableinst_1' v_tableinst_2 v_tabletype HOk HApp Hext.
	inversion HOk; subst.
	eapply Forall2_nth in Hext as [HLength Hforall].
	rewrite -!size_length in HLength.

	eapply Hforall in H1 as HExt.
	inversion HExt; subst.
	inversion H4; subst.
	inversion H5; subst.

	rewrite /lookup_total in H3.
	rewrite H3 in H.
	inversion H; subst; clear H.

	eapply extaddr_ok_table with
		(v_tt' := mk_tabletype (mk_limits v_n2 (mk_uN 32 v_n_12)) v_rt0)
		(v_ref := v_ref_2).
	{
		rewrite HApp.
		rewrite -size_length size_cat -HLength.
		by eapply ltn_addr.
	}
	{
		rewrite HApp /lookup_total.
		rewrite -size_length in H1.
		rewrite HLength in H1.
		move/ltP in H1.
		eapply app_nth1 with
		(d := default_val)
		(l' := v_tableinst_2)
		in H1.
		rewrite H1 /lookup_total.
		by rewrite -H0.
	}
	{
		inversion H4; subst.
		econstructor.
		destruct v_n2.
		econstructor.
		- eapply leq_trans. by eapply H6. by simpl in H2.
		- auto.
	}
Qed.

Lemma addrs_globals_extension: forall v_S v_S' v_globaladdr v_globalinst_1' v_globalinst_2 v_globaltype,
    Externaddrs_ok v_S (EXTADDR_GLOBAL v_globaladdr) (EXT_GLOBAL v_globaltype) ->
	GLOBALS v_S' = (v_globalinst_1' ++ v_globalinst_2) -> 
	Forall2 (fun v s => Global_extension v s) (GLOBALS v_S) v_globalinst_1' ->
    Externaddrs_ok v_S' (EXTADDR_GLOBAL v_globaladdr) (EXT_GLOBAL v_globaltype).
Proof.
	move => v_S v_S' v_globaladdr v_globalinst_1' v_globalinst_2 v_globaltype HOk HApp Hext.
	inversion HOk; subst.
	apply Forall2_lookup in Hext as [HLength Hext].
	move/ltP in H2.
	eapply Hext in H2 as HG.

	assert (v_globaladdr < Datatypes.length (GLOBALS v_S')).
	{
		rewrite HApp.
		rewrite -size_length size_cat.
		rewrite -!size_length in HLength.
		rewrite -HLength.
		eapply ltn_addr.
		by move/ltP in H2.
	}
	inversion HG; subst; destruct H4; subst.
	{
		econstructor; auto.
		{
			rewrite HApp /lookup_total.
			rewrite HLength in H2.
			eapply app_nth1 with
				(d := default_val)
				(l' := v_globalinst_2)
			in H2.
			rewrite H2.
			rewrite /lookup_total in H1.
			rewrite -H1.
			rewrite H3 in H0; inversion H0.
			eauto.
		}
	}
	{
		econstructor; auto.
		{
			rewrite HApp /lookup_total.
			rewrite HLength in H2.
			eapply app_nth1 with
				(d := default_val)
				(l' := v_globalinst_2)
			in H2.
			rewrite H2.
			rewrite /lookup_total in H1.
			rewrite -H1.
			rewrite H3 in H0; inversion H0.
			eauto.
		}
	}
Qed.

Lemma addrs_mems_extension: forall v_S v_S' v_memaddr v_meminst_1' v_meminst_2 v_memtype,
    Externaddrs_ok v_S (EXTADDR_MEM v_memaddr) (EXT_MEM v_memtype) ->
	MEMS v_S' = (v_meminst_1' ++ v_meminst_2) -> 
	Forall2 (fun v s => Mem_extension v s) (MEMS v_S) v_meminst_1' ->
    Externaddrs_ok v_S' (EXTADDR_MEM v_memaddr) (EXT_MEM v_memtype).
Proof.
	move => v_S v_S' v_memaddr v_meminst_1' v_meminst_2 v_memtype HOk HApp Hext.
	inversion HOk; subst.
	apply Forall2_lookup in Hext as [HLength Hext].
	move/ltP in H1.
	eapply Hext in H1 as HMe.
	inversion H4; subst.
	inversion H; subst.
	inversion HMe; subst.
	rewrite H3 in H5; inversion H5; subst; clear H5.

	eapply extaddr_ok_mem.
	{
		rewrite HApp.
		rewrite -size_length size_cat.
		rewrite -!size_length in HLength.
		rewrite -HLength.
		eapply ltn_addr.
		by move/ltP in H1.
	}
	{
		rewrite HApp /lookup_total.
		rewrite HLength in H1.
		eapply app_nth1 with
			(d := default_val)
			(l' := v_meminst_2)
		in H1.
		rewrite H1.
		rewrite /lookup_total in H6.
		rewrite -H6.
		eauto.
	}
	{
		econstructor.
		destruct v_n2.
		econstructor.
		- eapply leq_trans; eauto.
		- eauto.
	}
Qed.

Lemma addrss_funcs_extension: forall v_S v_S' v_funcaddrs v_funcinst_1' v_funcinst_2 tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (EXTADDR_FUNC v) (EXT_FUNC s)) v_funcaddrs tcf ->
	length (FUNCS v_S) = length v_funcinst_1' ->
	FUNCS v_S' = (v_funcinst_1' ++ v_funcinst_2) -> 
	Forall2 (fun v s => Func_extension v s) (FUNCS v_S) v_funcinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTADDR_FUNC v) (EXT_FUNC s)) v_funcaddrs tcf.
Proof.
	move => v_S v_S' v_funcaddrs v_funcinst_1' v_funcinst_2.
	move: v_S v_S'.
	induction v_funcaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	rewrite -app_cat in HApp.
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (addrs_funcs_extension v_S) with (v_funcinst_1' := v_funcinst_1') (v_funcinst_2 := v_funcinst_2) => //.
	- eapply IHv_funcaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed. 	

Lemma addrss_tables_extension: forall v_S v_S' v_tableaddrs v_tableinst_1' v_tableinst_2 tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (EXTADDR_TABLE v) (EXT_TABLE s)) v_tableaddrs tcf ->
	length (TABLES v_S) = length v_tableinst_1' ->
	TABLES v_S' = (v_tableinst_1' ++ v_tableinst_2) -> 
	Forall2 (fun v s => Table_extension v s) (TABLES v_S) v_tableinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTADDR_TABLE v) (EXT_TABLE s)) v_tableaddrs tcf.
Proof.
	move => v_S v_S' v_tableaddrs v_tableinst_1' v_tableinst_2.
	move: v_S v_S'.
	induction v_tableaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	rewrite -app_cat in HApp.
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (addrs_tables_extension v_S) with (v_tableinst_1' := v_tableinst_1') (v_tableinst_2 := v_tableinst_2) => //.
	- eapply IHv_tableaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed. 	

Lemma addrss_globals_extension: forall v_S v_S' v_globaladdrs v_globalinst_1' v_globalinst_2 tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (EXTADDR_GLOBAL v) (EXT_GLOBAL s)) v_globaladdrs tcf ->
	length (GLOBALS v_S) = length v_globalinst_1' ->
	GLOBALS v_S' = (v_globalinst_1' ++ v_globalinst_2) -> 
	Forall2 (fun v s => Global_extension v s) (GLOBALS v_S) v_globalinst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTADDR_GLOBAL v) (EXT_GLOBAL s)) v_globaladdrs tcf.
Proof.
	move => v_S v_S' v_globaladdrs v_globalinst_1' v_globalinst_2.
	move: v_S v_S'.
	induction v_globaladdrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	rewrite -app_cat in HApp.
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst.
	  apply (addrs_globals_extension v_S) with
	  	(v_globalinst_1' := v_globalinst_1') (v_globalinst_2 := v_globalinst_2) => //.
	- eapply IHv_globaladdrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed.


Lemma addrss_mems_extension: forall v_S v_S' v_memaddrs v_meminst_1' v_meminst_2 tcf,
	Forall2 (fun v s => Externaddrs_ok v_S (EXTADDR_MEM v) (EXT_MEM s)) v_memaddrs tcf ->
	length (MEMS v_S) = length v_meminst_1' ->
	MEMS v_S' = (v_meminst_1' ++ v_meminst_2) -> 
	Forall2 (fun v s => Mem_extension v s) (MEMS v_S) v_meminst_1' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (EXTADDR_MEM v) (EXT_MEM s)) v_memaddrs tcf.
Proof.
	move => v_S v_S' v_memaddrs v_meminst_1' v_meminst_2.
	move: v_S v_S'.
	induction v_memaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	rewrite -app_cat in HApp.
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst.
	  apply (addrs_mems_extension v_S) with
	  (v_meminst_1' := v_meminst_1') (v_meminst_2 := v_meminst_2) => //.
	- eapply IHv_memaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed.

Lemma store_extension_exts: forall v_S v_S' v_exportinst,
	Store_extension v_S v_S' ->
	Forall (Export_instance_ok v_S) v_exportinst -> 
	Forall (Export_instance_ok v_S') v_exportinst.
Proof.
	move => v_S v_S' v_exportinst.
	move: v_S v_S'.
	induction v_exportinst;
	move => v_S v_S' Hext HOk => //=.
	subst. inversion HOk. 
	apply Forall_cons_iff. split.
	-	inversion H1.
		subst.
		eapply mk_Export_instance_ok with (v_ext := v_ext).
		inversion Hext; decomp. 
		inversion H3; subst.
		+ eapply addrs_funcs_extension; eauto.
		+ eapply addrs_tables_extension; eauto.
		+ eapply addrs_mems_extension; eauto.
		+ eapply addrs_globals_extension; eauto.
	- eapply IHv_exportinst; eauto.
Qed.

Lemma store_extension_eleminst: forall v_S v_S' a t,
	Store_extension v_S v_S' ->
	Element_instance_ok v_S a t ->
	Element_instance_ok v_S' a t.
Proof.
	move => s s' x t HSt Het.

	invert_elems.
	inversion Het; subst.
	econstructor.

	induction v_ref; auto.
	inversion H; subst; auto.
	econstructor.
	{
		eapply store_extension_ref; eauto.
	}
	eapply IHv_ref; eauto.
	by inversion Het.
Qed.

Lemma store_extension_eleminsts': forall v_S v_S' aa ts,
	Store_extension v_S v_S' ->
	Forall (λ a , a < Datatypes.length (ELEMS v_S)) aa ->
	Forall2 (λ a t, Element_instance_ok v_S (lookup_total (ELEMS v_S) a) t) aa ts ->
	Forall (λ a , a < Datatypes.length (ELEMS v_S')) aa /\
	Forall2 (λ a t, Element_instance_ok v_S' (lookup_total (ELEMS v_S') a) t) aa ts.
Proof.
	move => s s' aa ts HS HLen He.
	destruct s, s'.
	inversion HS; subst; simpl in *.
	clear - He H9 H19 H20 HLen HS; subst.
	split.
	{
		eapply Forall_impl.
		2: eapply HLen.
		simpl.
		move => a HLena.
		rewrite -size_length size_cat.
		rewrite -!size_length in H19, HLena.
		rewrite -H19.
		by eapply ltn_addr.
	}
	move : ts HLen He H20 H19.
	induction aa; move => ts HLen He Hee HLeneq. inversion He; subst; auto.
	destruct ts; inversion He; subst.
	constructor.
	{
		inversion HLen; subst.
		rewrite HLeneq in H1.
		rewrite -(lookup_app _ _ _ H1).

		eapply Forall2_nth2 in Hee as [_ Hei].
		eapply Hei in H1.
		inversion H1; subst; clear H1.
		rewrite /lookup_total.

		inversion H2; subst.
		rewrite /lookup_total in H1.
		rewrite -H1 in H.
		inversion H; subst; clear H.
		rewrite -H0.
		econstructor.

		destruct H5; subst; auto.
		eapply Forall_impl.
		2: eapply H7.
		simpl.
		move => a0 HRef.
		eapply store_extension_ref; eauto.		
	}
	eapply IHaa; auto.
	by inversion HLen.
Qed.

Lemma store_extension_eleminsts: forall v_S v_S' aa ts,
	Store_extension v_S v_S' ->
	Forall2 (λ a t, Element_instance_ok v_S a t) aa ts ->
	Forall2 (λ a t, Element_instance_ok v_S' a t) aa ts.
Proof.
	move => s s' aa ts HS He.
	induction He; auto.
	econstructor; auto.
	invert_elems.
	inversion H; subst.
	econstructor.
	induction H0; auto.
	econstructor.
	- eapply store_extension_ref; eauto.
	- eapply IHForall. by inversion H.
Qed.

Lemma store_extension_datainsts': forall v_S v_S' aa,
	Store_extension v_S v_S' ->
	Forall (λ a , a < Datatypes.length (DATAS v_S)) aa ->
	Forall (λ a, Data_instance_ok v_S (lookup_total (DATAS v_S) a)) aa ->
	Forall (λ a , a < Datatypes.length (DATAS v_S')) aa /\
	Forall (λ a, Data_instance_ok v_S' (lookup_total (DATAS v_S') a)) aa.
Proof.
	move => v_S v_S' aa HS Hdl Hds.
	invert_datas.

	split.
	{
		eapply Forall_impl.
		2: eapply Hdl.
		simpl.
		move => a Hd.
		rewrite Hdeq -size_length size_cat.
		eapply ltn_addr.
		eapply Forall2_length in Hde.
		by rewrite Hde in Hd.
	}
	move : v_S Hdl Hds Hde Hdeq HS.
	induction aa; auto.
	move => v_S Hdl Hds Hde Hdeq HS.
	econstructor.
	{
		destruct (lookup_total (DATAS v_S') a).
		econstructor.
	}
	eapply IHaa; eauto.
	by inversion Hdl.
	by inversion Hds.
Qed.

Lemma store_extension_datainsts: forall v_S v_S' aa,
	Store_extension v_S v_S' ->
	Forall (λ a, Data_instance_ok v_S a) aa ->
	Forall (λ a, Data_instance_ok v_S' a) aa.
Proof.
	move => s s' aa HS He.
	induction He; auto.
	econstructor; auto.
	invert_elems.
	inversion H; subst.
	econstructor.
Qed.

Lemma store_extension_moduleinst: forall v_S v_S' v_i v_C,
    Store_extension v_S v_S' ->
    Module_instance_ok v_S v_i v_C ->
    Module_instance_ok v_S' v_i v_C.
Proof.
	move => v_S v_S' v_i v_C HStoreExtension HMIT.
	inversion HStoreExtension.
	inversion HMIT; decomp.
	subst.
	assert (
		Forall (λ a , a < Datatypes.length (ELEMS v_S')) v_elemaddr /\
		Forall2 (λ a t, Element_instance_ok v_S' (lookup_total (ELEMS v_S') a) t) v_elemaddr v_reftype) as [HElemLen HElem].
	{
	  eapply store_extension_eleminsts'; eauto.
	}
	assert (
		Forall (λ a , a < Datatypes.length (DATAS v_S')) v_dataaddr /\
		Forall (λ a, Data_instance_ok v_S' (lookup_total (DATAS v_S') a)) v_dataaddr) as [HDataLen HData].
	{
	  eapply store_extension_datainsts'; eauto.
	}
	apply mk_Module_instance_ok; auto.
	- eapply addrss_funcs_extension; eauto.
	- eapply addrss_tables_extension; eauto.
	- eapply addrss_mems_extension; eauto.
	- eapply addrss_globals_extension; eauto.
	- eapply store_extension_exts; eauto.
Qed.


Lemma store_extension_funcinst: forall s s' v t,
	Store_extension s s' ->
	Function_instance_ok s v t ->
	Function_instance_ok s' v t.
Proof.
	move => s s' v t HS H.
	inversion H; subst.
	econstructor; eauto.
	eapply store_extension_moduleinst; eauto.
Qed.

Lemma store_extension_funcinsts: forall s s' vs ts,
	Store_extension s s' ->
	Forall2 (λ v t, Function_instance_ok s v t) vs ts ->
	Forall2 (λ v t, Function_instance_ok s' v t) vs ts.
Proof.
	move => s s' vs ts HS H.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H1.
	eapply store_extension_funcinst; eauto.
Qed.

Lemma store_extension_globalinst: forall s s' v t,
	Store_extension s s' ->
	Global_instance_ok s v t ->
	Global_instance_ok s' v t.
Proof.
	move => s s' v t HS HG.
	inversion HG; subst.
	econstructor; eauto.
	eapply store_extension_val; eauto.
Qed.

Lemma store_extension_globalinsts: forall s s' vs ts,
	Store_extension s s' ->
	Forall2 (λ v t, Global_instance_ok s v t) vs ts ->
	Forall2 (λ v t, Global_instance_ok s' v t) vs ts.
Proof.
	move => s s' vs ts HS HG.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply store_extension_globalinst; eauto.
Qed.

Lemma store_extension_tableinst: forall s s' v t,
	Store_extension s s' ->
	Table_instance_ok s v t ->
	Table_instance_ok s' v t.
Proof.
	move => s s' v t HS HT.
	invert_tables.
	invert_funcs.
	inversion HT; subst; clear HT.
	econstructor; eauto.
	induction H2; auto.
	
	induction H1; auto.
	econstructor; auto.
	eapply store_extension_ref; eauto.
Qed.

Lemma store_extension_tableinsts: forall s s' vs ts,
	Store_extension s s' ->
	Forall2 (λ v t, Table_instance_ok s v t) vs ts ->
	Forall2 (λ v t, Table_instance_ok s' v t) vs ts.
Proof.
	move => s s' vs ts HS HG.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply store_extension_tableinst; eauto.
Qed.

Lemma store_extension_meminst: forall s s' v t,
	Store_extension s s' ->
	Memory_instance_ok s v t ->
	Memory_instance_ok s' v t.
Proof.
	move => s s' v t HS HT.
	invert_mems.
	inversion HT; subst; clear HT.
	econstructor; eauto.
Qed.

Lemma store_extension_meminsts: forall s s' vs ts,
	Store_extension s s' ->
	Forall2 (λ v t, Memory_instance_ok s v t) vs ts ->
	Forall2 (λ v t, Memory_instance_ok s' v t) vs ts.
Proof.
	move => s s' vs ts HS HG.
	eapply List.Forall2_impl.
	2: eauto.
	move => t v.
	simpl.
	move => H.
	eapply store_extension_meminst; eauto.
Qed.

Lemma store_extension_externaddrs_func: forall s s' fa ft,
	Store_extension s s' ->
	Externaddrs_ok s (EXTADDR_FUNC fa) (EXT_FUNC ft) ->
	Externaddrs_ok s' (EXTADDR_FUNC fa) (EXT_FUNC ft).
Proof.
	move => s s' fa ft HSe HEa.
	invert_funcs.
	eapply funcinst_same in Hfe; subst.
	inversion HEa; subst; clear HEa.
	econstructor.
	{
		rewrite Hfeq -size_length size_cat.
		by eapply ltn_addr.
	}
	{
		rewrite Hfeq.
		erewrite <- lookup_app; eauto.
	}
Qed.

Scheme ais_ok_ind' := Induction for Admin_instrs_ok Sort Prop
	with
	 thread_ok_ind' := Induction for Thread_ok Sort Prop
	with
	 ai_ok_ind' := Induction for Admin_instr_ok Sort Prop.

Lemma store_extension_ais: forall s s' c ais ft,
	Store_extension s s' ->
	Store_ok s ->
	Store_ok s' ->
	Admin_instrs_ok s c ais ft ->
	Admin_instrs_ok s' c ais ft.
Proof.
	move => s s' c ais ft HSe HSt1 HSt2 HType.
	eapply ais_ok_ind' with
		(P := fun s c ais tf (_ : Admin_instrs_ok s c ais tf) => forall s',
            Store_ok s ->
            Store_ok s' ->
            Store_extension s s' ->
            Admin_instrs_ok s' c ais tf)
    	(P0 := fun s rs f ais ts (_ : Thread_ok s rs f ais ts) => forall s',
             Store_ok s ->
             Store_ok s' ->
             Store_extension s s' ->
             Thread_ok s' rs f ais ts)
    	(P1 := fun s c ai ts (_ : Admin_instr_ok s c ai ts) => forall s',
             Store_ok s ->
             Store_ok s' ->
             Store_extension s s' ->
             Admin_instr_ok s' c ai ts)
		in HType;
	try solve [
		intros; econstructor; eauto
	].
	{
		eapply HType; eauto.
	}
	{
		intros.
		econstructor; eauto.
		destruct v_F, v_C.
		inversion f.
		econstructor; eauto.
		- eapply store_extension_moduleinst; eauto.
		- eapply store_extension_vals; eauto.
	}
	{
		intros.
		econstructor.
		eapply store_extension_externaddrs_func; eauto.
	}
	{
		intros.
		econstructor.
		eapply store_extension_externaddrs_func; eauto.
	}
Qed.

Lemma construct_tableinsts: forall s ts t tba lim tbr i v_ref,
	Forall2 (λ v t, Table_instance_ok s v t) (TABLES s) ts ->
	Ref_ok s v_ref t ->
	lookup_total (TABLES s) tba =  {| TAB_TYPE := mk_tabletype lim t; TAB_REFS := tbr |} ->
	Forall2 (λ v t, Table_instance_ok s v t)
		(list_update_func (TABLES s) tba
			(λ v_1 : tableinst, v_1 <| TAB_REFS :=
				list_update_func (TAB_REFS v_1) i (fun=> v_ref)
			|>)) ts.
Proof.
	move => s ts t tba lim tbr i v_ref Hold HRef HLookup.
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
		econstructor; eauto.
		{
			by rewrite list_update_length_func.
		}
		clear IHHold H3 H.
		move : i.
		induction H2; auto.
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

Lemma construct_tableinsts_grow: forall s ts v_ref t tba v_r v_j v_n,
	Forall2 (λ v t, Table_instance_ok s v t) (TABLES s) ts ->
	Ref_ok s v_ref t ->
	(Datatypes.length v_r + v_n) <= (fun_u32__nat v_j) ->
	lookup_total (TABLES s) tba ={|
		TAB_TYPE := mk_tabletype (mk_limits
			(mk_uN 32 (Datatypes.length v_r)) v_j) t;
		TAB_REFS := v_r |} ->
	Forall2 (λ v t, Table_instance_ok s v t)
		(list_update_func (TABLES s) tba
			(fun=> {|
				TAB_TYPE := mk_tabletype (mk_limits
					(mk_uN 32 (Datatypes.length v_r + v_n)) v_j) t;
				TAB_REFS := v_r ++ repeat v_ref v_n
			|}))
		(list_update_func ts tba (fun=> mk_tabletype (mk_limits
			(mk_uN 32 (Datatypes.length v_r + v_n)) v_j) t)).
Proof.
	move => s ts v_ref t tba v_r v_j v_n Hold HRef HRange HLookup.
	move : tba HLookup HRef.
	induction Hold; auto; move => tba HLookup HRef.
	destruct tba.
	{
		simpl.
		econstructor; auto.
		inversion H; subst.
		rewrite /lookup_total /= in HLookup.
		inversion HLookup; subst; clear HLookup.
		econstructor; eauto.
		{
			by rewrite length_app repeat_length.
		}
		{
			rewrite Forall_app.
			split; auto.
			clear - HRef H3.
			induction v_n; auto.
			econstructor; auto. 
		}
		inversion H3; subst; clear H3.
		econstructor.
		inversion H4; subst; clear H4.
		destruct_all.
		econstructor; auto.
	}
	simpl.
	econstructor; auto.
Qed.


Lemma construct_globalinsts: forall s ts ga v t v_old,
	Forall2 (λ v t, Global_instance_ok s v t) (GLOBALS s) ts ->
	lookup_total (GLOBALS s) ga = {| GLOB_TYPE := mk_globaltype (Some MUT) t; GLOB_VALUE := v_old |} ->
	Val_ok s v t ->
	Forall2 (λ v t, Global_instance_ok s v t)
		(list_update_func (GLOBALS s) ga [eta set GLOB_VALUE (fun=> v)]) ts.
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
	}
	simpl.
	econstructor; auto.
Qed.

Lemma construct_meminsts: forall s ts ma v_mt v_b v_i v_nb,
	Forall2 (λ v t, Memory_instance_ok s v t) (MEMS s) ts ->
	lookup_total (MEMS s) ma = {| MEM_TYPE := v_mt; MEM_BYTES := v_b |} ->
	Forall2 (λ v t, Memory_instance_ok s v t)
		(list_update_func (MEMS s) ma
			(λ m, m <| MEM_BYTES :=
			list_slice_update (MEM_BYTES m) v_i (length v_nb) v_nb |>)) ts.
Proof.
	move => s ts ma v_mt v_b v_i v_nb Hold HLookup.
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
		rewrite list_slice_update_length; auto.
	}
	simpl.
	econstructor; auto.
Qed.

Lemma construct_meminsts_grow: forall s ts ma v_b lim_old v_n v_j,
	Forall2 (λ v t, Memory_instance_ok s v t) (MEMS s) ts ->
	lookup_total (MEMS s) ma = {|
		MEM_TYPE := PAGE (mk_limits (lim_old) v_j);
		MEM_BYTES := v_b |} ->
	lim_old = Datatypes.length v_b / (64 * fun_Ki) ->
	lim_old + v_n <= v_j ->
	Forall2 (λ (v : meminst) (t : memtype), Memory_instance_ok s v t)
		(list_update_func (MEMS s) ma
		(fun=> {| MEM_TYPE := PAGE (mk_limits (lim_old + v_n) v_j);
			MEM_BYTES := v_b ++ repeat (mk_byte 0) (v_n * (64 * fun_Ki)) |}))
		(list_update_func ts ma (fun=> PAGE (mk_limits (lim_old + v_n) v_j))).
Proof.
	move => s ts ma v_b lim_old v_n v_j Hold HLookup HLim HRange.
	move : ma HLookup HRange.
	induction Hold; auto; move => ma HLookup HRange.
	destruct ma; simpl.
	{
		econstructor; auto.
		rewrite /lookup_total /= in HLookup.
		rewrite HLookup in H.
		destruct v_j.
		inversion H; clear H.
		subst.
		rewrite -mulnA in H4.
		remember (64 * fun_Ki) as n.
		assert (n <> 0). { subst. rewrite /fun_Ki. discriminate. }
		econstructor; eauto.
		{
			rewrite length_app H4 repeat_length.
			rewrite -!mulnA.
			rewrite mulnDl.
			rewrite mulnE.
			rewrite Nat.div_mul; auto.
		}
		econstructor.
		econstructor.
		split; auto.
		inversion H6; clear H6.
		inversion H1; clear H1.
		destruct H7 as [_ H7].
		auto.
	}
	econstructor; auto.
Qed.

Lemma construct_datainsts: forall s da v_b,
	Forall [eta Data_instance_ok s]
		(DATAS s) ->
	lookup_total (DATAS s) da = {| DATA_BYTES := v_b |} ->
	Forall [eta Data_instance_ok s]
		(list_update_func (DATAS s) da [eta set DATA_BYTES (fun=> [])]).
Proof.
	move => s da v_b Hold HLookup.
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
	Forall2 (λ v t, Element_instance_ok s v t) (ELEMS s) ts ->
	lookup_total (ELEMS s) ea = {| ELEM_TYPE := t; ELEM_REFS := ref |} ->
	Forall2 (λ v t, Element_instance_ok s v t)
	(list_update_func (ELEMS s) ea [eta set ELEM_REFS (fun=> [])]) ts.
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
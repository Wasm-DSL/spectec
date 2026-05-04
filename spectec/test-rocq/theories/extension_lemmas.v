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

Lemma Val_ok_store: forall f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 v t,
	Val_ok {| store_FUNCS := f1;
		store_GLOBALS := g1;
		store_TABLES := t1;
		store_MEMS := m1;
		store_ELEMS := e1;
		store_DATAS := d1 |} v t <->
	Val_ok {| store_FUNCS := f1;
		store_GLOBALS := g2;
		store_TABLES := t2;
		store_MEMS := m2;
		store_ELEMS := e2;
		store_DATAS := d2 |} v t.
Proof.
	assert (forall f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 v t,
		Val_ok {| store_FUNCS := f1;
			store_GLOBALS := g1;
			store_TABLES := t1;
			store_MEMS := m1;
			store_ELEMS := e1;
			store_DATAS := d1 |} v t ->
		Val_ok {| store_FUNCS := f1;
			store_GLOBALS := g2;
			store_TABLES := t2;
			store_MEMS := m2;
			store_ELEMS := e2;
			store_DATAS := d2 |} v t).
	{
		move => f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 v t HVal.
		inversion HVal; subst; econstructor; eauto.
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
	rewrite H /=.
	clear -H1.
	exists functype_lst.

	move : funcinst_lst H1.
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
	rewrite {2}H /=.
	clear -H3.
	exists globaltype_lst.
	
	move : globalinst_lst H3.
	induction globaltype_lst; move => globalinst_lst HGok.
	{
		inversion HGok; subst; auto.
	}
	destruct globalinst_lst; inversion HGok; subst; auto.
	econstructor.
	{
		inversion H2; eq_to_prop; subst.
		by exists v_mut, (valtype_vectype vt), v.
	}
	by eapply IHglobaltype_lst.
Qed.

Lemma s_invert_mems: forall s,
	Store_ok s ->
	exists mts,
	List.Forall2 (fun m t =>
		exists b_lst v_n v_m,
		(m = {| meminst_TYPE := t; BYTES := b_lst |}) /\
		(t = (PAGE (mk_limits (mk_uN v_n) (Some (mk_uN v_m))))) /\
		(v_n = (List.length b_lst) / (64 * Ki)) /\
		(v_n <= v_m) /\
		(v_m <= 2 ^ 16)
	) (store_MEMS s) mts.
Proof.
	move => s HSt.
	inversion HSt.
	eq_to_prop.
	rewrite H /store_MEMS.
	clear -H7.
	exists memtype_lst.
	
	move : meminst_lst H7.
	induction memtype_lst; move => meminst_lst HMok.
	{
		inversion HMok; subst; auto.
	}
	destruct meminst_lst; inversion HMok; subst; auto.
	econstructor.
	{
		inversion H2; subst; clear H2.
		inversion H1; subst; clear H1.
		inversion H2; subst; clear H2.
		exists b_lst, v_n, v_m.
		eq_to_prop.
		split; auto.
		split; auto.
		split; auto.
		list_to_seq.
		rewrite H0.
		rewrite -mulnA.
		rewrite mulnE.
		rewrite Nat.div_mul; auto.
		rewrite /Ki -mulnE; discriminate.
		injection H as ?; subst.
		destruct m_opt => //=.
		injection H2 as ?; subst.
		inversion H3; subst.
		eq_to_prop.
		eapply H5.
	}
	by eapply IHmemtype_lst.
Qed.

Lemma s_invert_tables: forall s,
	Store_ok s ->
	exists tbts,
	List.Forall2 (fun tb tbt =>
		exists ref_lst v_m rt,
		(tb = {| tableinst_TYPE := tbt;
			REFS := ref_lst |}) /\
		(tbt = (mk_tabletype
			(mk_limits (mk_uN (List.length ref_lst)) (Some (mk_uN v_m))) rt)) /\
		(Tabletype_ok tbt) /\
		List.Forall (fun (ref_lst : ref) => (Ref_ok s ref_lst rt)) (ref_lst)
	) (store_TABLES s) tbts.
Proof.
	move => s HSt.
	inversion HSt.
	eq_to_prop.

	rewrite {2}H /=.
	clear -H5.

	exists tabletype_lst.
	move : tableinst_lst H5.
	induction tabletype_lst; move => tableinst_lst HTok.
	{
		inversion HTok; subst; auto.
	}
	destruct tableinst_lst; inversion HTok; subst; auto.
	econstructor.
	{
		inversion H2; subst.
		eq_to_prop.
		exists ref_lst, v_m, rt; repeat split; eauto. 
		list_to_seq.
		rewrite -H0.
		apply H.
	}
	by eapply IHtabletype_lst.
Qed.

Lemma se_invert_funcs: forall s s',
    Store_extension s s' ->
    exists fs' fs2,
      Forall2 (λ x x', Func_extension x x') (store_FUNCS s) fs' /\
      store_FUNCS s' = fs' ++ fs2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
		eq_to_prop; subst.
    exists funcinst_1'_lst, funcinst_2_lst.
		auto.
Qed.

Lemma se_invert_tables: forall s s',
    Store_extension s s' ->
    exists tbs' tbs2,
        Forall2 (λ x x', Table_extension x x') (store_TABLES s)
tbs' /\
        store_TABLES s' = tbs' ++ tbs2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
		eq_to_prop; subst.
    exists tableinst_1'_lst, tableinst_2_lst.
    auto.
Qed.

Lemma se_invert_mems: forall s s',
    Store_extension s s' ->
    exists ms' ms2,
        Forall2 (λ x x', Mem_extension x x') (store_MEMS s)
ms' /\
        store_MEMS s' = ms' ++ ms2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
		eq_to_prop; subst.
    exists meminst_1'_lst, meminst_2_lst.
    auto.
Qed.

Lemma se_invert_store_globals: forall s s',
    Store_extension s s' ->
    exists gs' gs2,
        Forall2 (λ x x', Global_extension x x') (store_GLOBALS s)
gs' /\
        store_GLOBALS s' = gs' ++ gs2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
		eq_to_prop; subst.
    exists globalinst_1'_lst, globalinst_2_lst.
    auto.
Qed.

Lemma se_invert_elems: forall s s',
    Store_extension s s' ->
    exists es' es2,
        Forall2 (λ x x', Elem_extension x x') (store_ELEMS s)
es' /\
        store_ELEMS s' = es' ++ es2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
		eq_to_prop; subst.
    exists eleminst_1'_lst, eleminst_2_lst.
    auto.
Qed.

Lemma se_invert_datas: forall s s',
    Store_extension s s' ->
    exists ds' ds2,
        Forall2 (λ x x', Data_extension x x') (store_DATAS s)
ds' /\
        store_DATAS s' = ds' ++ ds2.
Proof.
    move => s s' HSe.
    inversion HSe; subst.
		eq_to_prop; subst.
    exists datainst_1'_lst, datainst_2_lst.
    auto.
Qed.

Lemma minst_invert_functypes: forall v_S minst C C',
	Module_instance_ok v_S minst C ->
	inst_match C C' ->
	(context_TYPES C') = (TYPES minst).
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; inversion Him; subst; auto.
Qed.

Lemma minst_invert_funcs: forall v_S minst C C',
	Module_instance_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun fa ft => 
		exists minst1 v_func,
		(fa < (List.length (store_FUNCS v_S))) /\
		((lookup_total (store_FUNCS v_S) fa) =
			{| funcinst_TYPE := ft; funcinst_MODULE := minst1; CODE := v_func |})
	) (FUNCS minst) (context_FUNCS C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H1 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H1; eauto.
	econstructor; eauto.
	inversion H; subst; clear H.
	eq_to_prop.
	by exists minst, v_func.
Qed.

Lemma minst_invert_tables: forall v_S minst C C',
	Module_instance_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun tba tbt => 
		exists rt lim lim' tbr,
		(tba < (List.length (store_TABLES v_S))) /\
		(tbt = (mk_tabletype lim' rt)) /\
		(Limits_sub lim lim') /\
		((lookup_total (store_TABLES v_S) tba) =
			{| tableinst_TYPE := (mk_tabletype lim rt); REFS := tbr |})
	) (TABLES minst) (context_TABLES C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H3 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H3; eauto.
	econstructor; eauto.
	inversion H; subst; clear H.
	inversion H6; subst; clear H6.
	eq_to_prop.
	by exists rt, lim_1, lim_2, ref_lst.
Qed.

Lemma minst_invert_globals: forall v_S minst C C',
	Module_instance_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun ga gt => 
		exists v_mut v_valtype v_val,
		(ga < (List.length (store_GLOBALS v_S))) /\
		(gt = (mk_globaltype v_mut v_valtype)) /\
		((lookup_total (store_GLOBALS v_S) ga) =
			{| globalinst_TYPE := (mk_globaltype v_mut v_valtype); VALUE := v_val |})
	) (GLOBALS minst) (context_GLOBALS C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H7 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H7; eauto.
	econstructor; eauto.
	inversion H; subst; clear H.
	eq_to_prop.
	by exists v_mut, v_valtype, v_val.
Qed.

Lemma minst_invert_mems: forall v_S minst C C',
	Module_instance_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun ma mt => 
		exists v_mt b_lst,
		(ma < (List.length (store_MEMS v_S))) /\
		((Memtype_sub v_mt mt)) /\
		((lookup_total (store_MEMS v_S) ma) = {| meminst_TYPE := v_mt; BYTES := b_lst |})
	) (MEMS minst) (context_MEMS C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H5 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.

	induction H5; eauto.
	econstructor; eauto.
	inversion H; subst; clear H.
	eq_to_prop.
	by exists mt', b_lst.
Qed.

Lemma minst_invert_elems: forall v_S minst C C',
	Module_instance_ok v_S minst C ->
	inst_match C C' ->
	List.Forall2 (fun ea et => 
		exists ref_lst,
		(ea < (List.length (store_ELEMS v_S))) /\
		(List.Forall (fun (ref_lst : ref) => (Ref_ok v_S ref_lst et)) (ref_lst)) /\
		((lookup_total (store_ELEMS v_S) ea) = {| eleminst_TYPE := et; eleminst_REFS := ref_lst |})
	) (ELEMS minst) (context_ELEMS C').
Proof.
	move => v_S minst v_C v_C' HMi Him.
	inversion HMi; subst; clear HMi.
	clear - H9 H10 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.
	simpl.

	move : context_ELEMS H10.
	induction elemaddr_lst; move => context_ELEMS Heok. inversion Heok; subst; auto.
	destruct context_ELEMS. by inversion Heok.
	econstructor.
	{
		inversion Heok; subst.
		inversion H2; subst.
		inversion H9; subst.
		eexists ref_lst.
		split; auto.
	}
	eapply IHelemaddr_lst. by inversion H9.
	by inversion Heok.
Qed.

Lemma minst_invert_datas: forall v_S minst C C',
	Module_instance_ok v_S minst C ->
	inst_match C C' ->
	((List.length (DATAS minst) = (List.length (context_DATAS C')))) /\
	List.Forall (fun da => 
		exists b_lst,
		(da < (List.length (store_DATAS v_S))) /\
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
	clear - H11 H12 Him.
	destruct v_C'; rewrite /inst_match in Him; destruct_all; simpl in *; subst.
	simpl.

	move : H12.
	induction dataaddr_lst; move => Hdok. inversion Hdok; subst; auto.
	econstructor.
	{
		inversion Hdok; subst.
		inversion H1; subst.
		inversion H11; subst.
		eexists b_lst.
		split; auto.
	}
	eapply IHdataaddr_lst. by inversion H11.
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


Lemma lookup_global: forall v_a v_C v_C' v_mut v_vt v_S minst,
	(v_a < (List.length (context_GLOBALS v_C'))) ->
	lookup_total (context_GLOBALS v_C') v_a = mk_globaltype v_mut v_vt ->
	Module_instance_ok v_S minst v_C ->
	inst_match v_C v_C' ->
	Store_ok v_S ->
	(Val_ok v_S (VALUE (lookup_total 
		(store_GLOBALS v_S) (lookup_total (GLOBALS minst) v_a))) (v_vt : valtype)).
Proof.
	move => v_a v_C v_C' v_mut v_vt v_S minst HLength HLookup HMIT Him HST.
	inversion HST; eq_to_prop; subst.
	inversion HMIT; eq_to_prop; subst.
	simpl in *; rewrite /lookup_total in HLookup.
	clear - HLength HLookup Him H3 H18.
	inversion Him; destruct_all; simpl in *; subst.
	list_to_seq.


	eapply Forall2_nth in H18 as [Hl Hforall].
	rewrite -Hl in HLength.
	eapply Hforall
		in HLength as Heok.
	inversion Heok; eq_to_prop; subst; simpl in *.
	rewrite nth_is_same_as_seq_nth in H0.
	erewrite HLookup in H0; inversion H0; subst; clear H0.

	eapply Forall2_nth in H3 as [Hl2 Hforall2].
	eapply Hforall2
		in H2 as Hgok.
	inversion Hgok; subst; simpl in *; rewrite /lookup_total in H4.
	simpl in H4.
	list_to_seq.
	eq_to_prop.
	erewrite H4 in H.
	rewrite H0 in H.
	inversion H; subst; clear H.

	by rewrite /lookup_total H4 => //.
Qed.

Lemma bt_inversion : forall v_S v_C v_C' r_v_f (b_lstt: blocktype) ts1 ts2 bt1 bt2,
	Module_instance_ok v_S (frame_MODULE r_v_f) v_C ->
	Blocktype_ok v_C' b_lstt (ts1 :-> ts2) ->
	fun_blocktype (mk_state v_S r_v_f) b_lstt = (bt1 :-> bt2) ->
	inst_match v_C v_C' ->
	(ts1 = bt1 /\ ts2 = bt2).
Proof.
	move=> v_S v_C v_C' r_v_f b_lstt ts1 ts2 bt1 bt2 HM HB Hf Him.
	inversion HM; eq_to_prop; subst.
	unfold inst_match in Him.
	simpl in *; subst.
	unfold fun_blocktype in Hf;
	destruct b_lstt.
	{
		destruct valtype_opt;
		inversion Hf; subst;
		inversion HB; subst; auto.
	}
	unfold fun_type.
	inversion Hf; subst;
	inversion HB; subst.
	rewrite -H in H17; simpl in H17.
	destruct_all; subst.
	eq_to_propH H22.
	rewrite H22 in H17.
	by inversion H17.
Qed.

Lemma tc_func_reference2: forall v_S v_C minst idx tf v_type,
  lookup_total (TYPES minst) idx = funcinst_TYPE v_type ->
  Module_instance_ok v_S minst v_C ->
  lookup_total (context_TYPES v_C) idx = tf ->
  tf = funcinst_TYPE v_type.
Proof.
	move => v_S v_C minst idx tf v_type H HMinst H1.
	inversion HMinst. subst. simpl in *. auto.
Qed.


Lemma store_typed_exterval_types: forall v_S v_f v_a,
	(v_a < List.length (store_FUNCS v_S))%coq_nat ->
	lookup_total (store_FUNCS v_S) v_a = v_f ->
    Store_ok v_S ->
    Externaddrs_ok v_S (externaddr_FUNC v_a) (FUNC (funcinst_TYPE v_f)).
Proof.
	move => v_S v_f v_a HLength H HST.
	inversion HST; eq_to_prop; subst; simpl in *.
	
	apply Forall2_lookup in H2; destruct H2.
	apply H0 in HLength as HFunc.
	simpl in *.
	inversion HFunc; subst; simpl in *.
	apply Externaddrs_ok__func with (minst := v_moduleinst) (v_func := v_func).
	- move/ltP: HLength => Hprop. auto.
	- eq_to_prop. simpl in *. auto.
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
	destruct m, meminst_TYPE, v_limits.
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
	destruct globalinst_TYPE.
	econstructor.
	eq_to_prop.
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
	    destruct globalinst_TYPE.
	  	econstructor.
			eq_to_prop.
			by right.
	  + by eapply IHg.
Qed.

Lemma elem_extension_refl0: forall g,
	Elem_extension g g.
Proof.
	move => g.
	destruct g.
	econstructor.
	eq_to_prop.
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
	eq_to_prop.
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
  (store_FUNCS s) (store_GLOBALS s) (store_TABLES s) (store_MEMS s)  (store_ELEMS s) (store_DATAS s)
  (store_FUNCS s) [] (store_GLOBALS s) [] (store_TABLES s) [] (store_MEMS s) []  (store_ELEMS s) [] (store_DATAS s) [] ); eauto;
  repeat (try by rewrite -> cats0).
	all: eq_to_prop.
	+ destruct s; eauto.
	+ repeat rewrite -> cats0. destruct s; eauto.
  + by apply func_extension_refl.
  + by apply table_extension_refl.
  + by apply mem_extension_refl.
  + by apply global_extension_refl.
  + by apply elem_extension_refl.
  + by apply data_extension_refl.
Qed.


Lemma funcinst_same: forall f1 f2,
	Forall2 (λ v_funcinst_1 funcinst_1'_lst : funcinst, Func_extension v_funcinst_1 funcinst_1'_lst) f1 f2 ->
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
	inversion Hs; eq_to_prop; subst.
	clear - Hv1 H1 H2.
	eapply funcinst_same in H2; subst.

	inversion Hv1; subst; try by constructor.
	econstructor.

	inversion H; subst; eauto; try econstructor; eq_to_prop.
	{
		simpl in *.
		ineq_to_prop.
		by eapply ltsize.
	}
	rewrite -(lookup_app _ _ _ H4).
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
	inversion Hs; eq_to_prop; subst.
	clear - Hv1 H2 H1.
	eapply funcinst_same in H2; subst.

	inversion Hv1; subst; try by constructor.
	econstructor.

	inversion H; subst; eauto; try econstructor.
	inversion H0; subst; econstructor.
	- simpl in *. ineq_to_prop. by eapply ltsize.
	- eq_to_prop. simpl in *. 
		rewrite -(lookup_app _ _ _ H5).
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
		{| globalinst_TYPE := mk_globaltype (Some MUT_MUT) v_valtype; VALUE := v_val_0 |} ->
	Forall2 (fun v s => Global_extension v s) v_g
		(list_update_func v_g v_idx (fun g => g <| VALUE := v_val_1 |> )).
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
			eq_to_prop.
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

Lemma store_none_mem_extension: forall v_ms v_idx v_mt b_lst v_l v_n v_nb,
	(v_idx < length v_ms) ->
	lookup_total v_ms v_idx = {| meminst_TYPE := v_mt; BYTES := b_lst |} ->
	Forall2 (λ v v', Mem_extension v v') v_ms
		(list_update_func v_ms v_idx
			(λ m, m <| BYTES :=
			list_slice_update (BYTES m) v_l v_n v_nb |>)).
Proof.
	move => v_ms v_idx v_mt b_lst v_l v_n v_nb HLength HLookup.
	move : v_idx v_mt b_lst v_l v_n v_nb HLength HLookup.
	induction v_ms; auto; move => v_idx v_mt b_lst v_l v_n v_nb HLength HLookup.
	destruct v_idx; simpl.
	{
		econstructor.
		{
			destruct a; rewrite /set /=.
			destruct meminst_TYPE, v_limits.
			assert (exists n, option_map (mk_uN) n = u32_opt).
			{
				destruct u32_opt.
				- destruct u. exists (Some i); eauto.
				- exists None; eauto.
			}
			destruct H as [n H]; subst.
			econstructor.
			eauto.
		}
		eapply mem_extension_refl.
	}
	econstructor.
	eapply mem_extension_refl0.
	eapply IHv_ms; eauto.
Qed.

Lemma memory_grow_mem_extension: forall v_ms v_idx b_lst v_i v_n v_j,
	(v_idx < length v_ms) ->
	lookup_total v_ms v_idx = {| meminst_TYPE := PAGE (mk_limits
				(mk_uN v_i)
				(Some v_j)); BYTES := b_lst |} ->
	v_i + v_n <= proj_uN_0 v_j ->
	Forall2 (λ v v', Mem_extension v v') v_ms
		(list_update_func v_ms v_idx
			(fun=> {|
			meminst_TYPE := PAGE (mk_limits
				(mk_uN (v_i + v_n)) (Some v_j));
			BYTES := b_lst ++ repeat (mk_byte 0) (v_n * (64 * Ki))
		|})).
Proof.
	move => v_ms v_idx b_lst v_i v_n v_j HLength HLookup HRange.
	move : v_idx b_lst v_n v_j HLength HLookup HRange.
	induction v_ms; move => v_idx b_lst v_n v_j HLength HLookup HRange; auto.
	destruct v_idx.
	{
		econstructor.
		{
			rewrite /lookup_total /ListDef.nth in HLookup.
			simpl in HLookup.
			rewrite HLookup.
			destruct v_j.
			rewrite <- invert_opt_map_some.
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
		{| tableinst_TYPE := tbt; REFS := tbr |} ->
	Forall2 (fun v v' => Table_extension v v') v_tbs
		(list_update_func v_tbs v_idx
			(fun tb => tb <| REFS :=
				list_update_func (REFS tb) v_i (fun=> v_tbr) |> )).
Proof.
	move => v_tbs v_i tbt tbr i v_tbr HLength HLookup.
	move: v_tbs i HLength HLookup.
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
			destruct tableinst_TYPE, v_limits.
			assert (exists n, option_map (mk_uN) n = u32_opt).
			{
				destruct u32_opt.
				- destruct u. exists (Some i); eauto.
				- exists None; eauto.
			}
			destruct H as [n H]; subst.
			econstructor; auto.
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
		{| tableinst_TYPE := mk_tabletype (mk_limits
					(mk_uN (size tbr) ) j) rt;
		REFS := tbr |} ->
	Forall2 (λ tb tb', Table_extension tb tb') v_tbs
		(list_update_func v_tbs	v_idx
			(fun=> {|
				tableinst_TYPE := mk_tabletype (mk_limits
					(mk_uN (size tbr + n)) j) rt;
				REFS := tbr ++ repeat ref n
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
			assert (exists n, option_map (mk_uN) n = j).
			{
				destruct j.
				- destruct u. exists (Some i); eauto.
				- exists None; eauto.
			}
			destruct H as [n' H]; subst.
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
			[eta set eleminst_REFS (fun=> [])])).
Proof.
	move => es idx HLength.
	move : idx HLength.
	induction es; auto.
	move => idx HLength.
	destruct idx.
	{
		destruct a.
		econstructor.
		- econstructor. eq_to_prop. by right.
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
			[eta set datainst_BYTES (fun=> [])])).
Proof.
	move => ds idx HLength.
	move : idx HLength.
	induction ds; auto.
	move => idx HLength.
	destruct idx.
	{
		destruct a.
		econstructor.
		- econstructor. eq_to_prop. by right.
		- by eapply data_extension_refl.
	}
	simpl.
	econstructor.
	- by eapply data_extension_refl0.
	- by eapply IHds.
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

Lemma addrs_store_funcs_extension: forall v_S v_S' v_funcaddr funcinst_1'_lst funcinst_2_lst v_ft,
	Externaddrs_ok v_S (externaddr_FUNC v_funcaddr) (FUNC v_ft) ->
	store_FUNCS v_S' = (funcinst_1'_lst ++ funcinst_2_lst) -> 
    Forall2 (fun v s => Func_extension v s) (store_FUNCS v_S) funcinst_1'_lst ->
    Externaddrs_ok v_S' (externaddr_FUNC v_funcaddr) (FUNC v_ft).
Proof.
	move => v_S v_S' v_funcaddr funcinst_1'_lst funcinst_2_lst v_ft HOk HApp Hext.
	inversion HOk. subst.
	apply Forall2_nth in Hext as [HLength Hext].
	eapply (Hext) in H2 as H4.
	eapply (Externaddrs_ok__func _ _ _ minst v_func).
	apply (length_app_lt) with (l':=(store_FUNCS v_S')) (l2':= funcinst_2_lst) in HLength => //=.
	- apply/ltP.
	  eapply (Nat.lt_le_trans).
	  apply/ltP. by eapply H2.
	  eauto.
	- unfold lookup_total.
	  rewrite /lookup_total in H3.
		eq_to_propH H3.
		list_to_seq.
		rewrite H3 in H4.
		rewrite HLength in H2.
		move/ltP in H2.
		apply app_nth1 with (l' := funcinst_2_lst) (d := default_val) in H2.
		rewrite app_cat in H2.
		rewrite <- HApp in H2.
		eq_to_prop.
		list_to_seq.
		rewrite H2.
		inversion H4; subst.
		auto.
Qed.

Lemma addrs_tables_extension: forall v_S v_S' v_tableaddr tableinst_1'_lst tableinst_2_lst tabletype_lst,
    Externaddrs_ok v_S (externaddr_TABLE v_tableaddr) (TABLE tabletype_lst) ->
	store_TABLES v_S' = (tableinst_1'_lst ++ tableinst_2_lst) -> 
	Forall2 (fun v s => Table_extension v s) (store_TABLES v_S) tableinst_1'_lst ->
    Externaddrs_ok v_S' (externaddr_TABLE v_tableaddr) (TABLE tabletype_lst).
Proof.
	move => v_S v_S' v_tableaddr tableinst_1'_lst tableinst_2_lst tabletype_lst HOk HApp Hext.
	inversion HOk; subst.
	eapply Forall2_nth in Hext as [HLength Hforall].

	eapply Hforall in H1 as HExt.
	inversion HExt; subst.
	inversion H4; subst.
	inversion H5; subst.

	rewrite /lookup_total in H3.
	list_to_seq; eq_to_prop.
	rewrite H3 in H.
	inversion H; subst; clear H.

	eapply Externaddrs_ok__table with
		(tt' := mk_tabletype (mk_limits n2 (Some (mk_uN n_12))) rt0)
		(ref_lst := ref_2_lst).
	{
		rewrite HApp.
		rewrite size_cat -HLength.
		by eapply ltn_addr.
	}
	{
		rewrite HApp /lookup_total.
		rewrite HLength in H1.
		move/ltP in H1.
		eapply app_nth1 with
		(d := default_val)
		(l' := tableinst_2_lst)
		in H1.
		list_to_seq; eq_to_prop.
		rewrite H1 /lookup_total.
		rewrite H10 in H0.
		by rewrite -H0.
	}
	{
		inversion H4; subst.
		econstructor.
		destruct n2.
		econstructor.
		- eapply leq_trans. by eapply H6. by simpl in H2.
		- auto.
	}
Qed.

Lemma addrs_store_globals_extension: forall v_S v_S' v_globaladdr globalinst_1_lst' globalinst_2_lst globaltype_lst,
    Externaddrs_ok v_S (externaddr_GLOBAL v_globaladdr) (GLOBAL globaltype_lst) ->
	store_GLOBALS v_S' = (globalinst_1_lst' ++ globalinst_2_lst) -> 
	Forall2 (fun v s => Global_extension v s) (store_GLOBALS v_S) globalinst_1_lst' ->
    Externaddrs_ok v_S' (externaddr_GLOBAL v_globaladdr) (GLOBAL globaltype_lst).
Proof.
	move => v_S v_S' v_globaladdr globalinst_1_lst' globalinst_2_lst globaltype_lst HOk HApp Hext.
	inversion HOk; subst.
	apply Forall2_lookup in Hext as [HLength Hext].
	move/ltP in H2.
	eapply Hext in H2 as HG.

	assert (v_globaladdr < Datatypes.length (store_GLOBALS v_S')).
	{
		rewrite HApp.
		rewrite -size_length size_cat.
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
				(l' := globalinst_2_lst)
			in H2.
			list_to_seq.
			rewrite H2.
			rewrite /lookup_total in H1.
			rewrite -H1.
			eq_to_prop.
			rewrite H3 in H0; inversion H0.
			eauto.
		}
	}
Qed.

Lemma addrs_mems_extension: forall v_S v_S' v_memaddr meminst_1_lst' meminst_2_lst memtype_lst,
    Externaddrs_ok v_S (externaddr_MEM v_memaddr) (MEM memtype_lst) ->
	store_MEMS v_S' = (meminst_1_lst' ++ meminst_2_lst) -> 
	Forall2 (fun v s => Mem_extension v s) (store_MEMS v_S) meminst_1_lst' ->
    Externaddrs_ok v_S' (externaddr_MEM v_memaddr) (MEM memtype_lst).
Proof.
	move => v_S v_S' v_memaddr meminst_1_lst' meminst_2_lst memtype_lst HOk HApp Hext.
	inversion HOk; subst.
	apply Forall2_lookup in Hext as [HLength Hext].
	move/ltP in H1.
	eapply Hext in H1 as HMe.
	inversion H4; subst.
	inversion H; subst.
	inversion HMe; subst.
	eq_to_propH H3.
	rewrite H3 in H5; inversion H5; subst; clear H5.

	eapply Externaddrs_ok__mem.
	{
		rewrite HApp.
		rewrite size_cat.
		rewrite -HLength.
		eapply ltn_addr.
		by move/ltP in H1.
	}
	{
		rewrite HApp /lookup_total.
		rewrite HLength in H1.
		eapply app_nth1 with
			(d := default_val)
			(l' := meminst_2_lst)
		in H1.
		list_to_seq.
		rewrite H1.
		rewrite /lookup_total in H6.
		rewrite -H6.
		eauto.
	}
	{
		econstructor.
		destruct n2.
		rewrite H10.
		econstructor.
		- eapply leq_trans; eauto.
		- eauto.
	}
Qed.

Lemma addrss_store_funcs_extension: forall v_S v_S' v_funcaddrs funcinst_1'_lst funcinst_2_lst tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (externaddr_FUNC v) (FUNC s)) v_funcaddrs tcf ->
	length (store_FUNCS v_S) = length funcinst_1'_lst ->
	store_FUNCS v_S' = (funcinst_1'_lst ++ funcinst_2_lst) -> 
	Forall2 (fun v s => Func_extension v s) (store_FUNCS v_S) funcinst_1'_lst ->
    Forall2 (fun v s => Externaddrs_ok v_S' (externaddr_FUNC v) (FUNC s)) v_funcaddrs tcf.
Proof.
	move => v_S v_S' v_funcaddrs funcinst_1'_lst funcinst_2_lst.
	move: v_S v_S'.
	induction v_funcaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	rewrite -app_cat in HApp.
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (addrs_store_funcs_extension v_S) with (funcinst_1'_lst := funcinst_1'_lst) (funcinst_2_lst := funcinst_2_lst) => //.
	- eapply IHv_funcaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed. 	

Lemma addrss_tables_extension: forall v_S v_S' v_tableaddrs tableinst_1'_lst tableinst_2_lst tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (externaddr_TABLE v) (TABLE s)) v_tableaddrs tcf ->
	length (store_TABLES v_S) = length tableinst_1'_lst ->
	store_TABLES v_S' = (tableinst_1'_lst ++ tableinst_2_lst) -> 
	Forall2 (fun v s => Table_extension v s) (store_TABLES v_S) tableinst_1'_lst ->
    Forall2 (fun v s => Externaddrs_ok v_S' (externaddr_TABLE v) (TABLE s)) v_tableaddrs tcf.
Proof.
	move => v_S v_S' v_tableaddrs tableinst_1'_lst tableinst_2_lst.
	move: v_S v_S'.
	induction v_tableaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	rewrite -app_cat in HApp.
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst. apply (addrs_tables_extension v_S) with (tableinst_1'_lst := tableinst_1'_lst) (tableinst_2_lst := tableinst_2_lst) => //.
	- eapply IHv_tableaddrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed. 	

Lemma addrss_store_globals_extension: forall v_S v_S' v_globaladdrs globalinst_1_lst' globalinst_2_lst tcf,
    Forall2 (fun v s => Externaddrs_ok v_S (externaddr_GLOBAL v) (GLOBAL s)) v_globaladdrs tcf ->
	length (store_GLOBALS v_S) = length globalinst_1_lst' ->
	store_GLOBALS v_S' = (globalinst_1_lst' ++ globalinst_2_lst) -> 
	Forall2 (fun v s => Global_extension v s) (store_GLOBALS v_S) globalinst_1_lst' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (externaddr_GLOBAL v) (GLOBAL s)) v_globaladdrs tcf.
Proof.
	move => v_S v_S' v_globaladdrs globalinst_1_lst' globalinst_2_lst.
	move: v_S v_S'.
	induction v_globaladdrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	rewrite -app_cat in HApp.
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst.
	  apply (addrs_store_globals_extension v_S) with
	  	(globalinst_1_lst' := globalinst_1_lst') (globalinst_2_lst := globalinst_2_lst) => //.
	- eapply IHv_globaladdrs. inversion HOk. apply H4. apply Hlength. apply HApp. apply Hext.
Qed.


Lemma addrss_mems_extension: forall v_S v_S' v_memaddrs meminst_1_lst' meminst_2_lst tcf,
	Forall2 (fun v s => Externaddrs_ok v_S (externaddr_MEM v) (MEM s)) v_memaddrs tcf ->
	length (store_MEMS v_S) = length meminst_1_lst' ->
	store_MEMS v_S' = (meminst_1_lst' ++ meminst_2_lst) -> 
	Forall2 (fun v s => Mem_extension v s) (store_MEMS v_S) meminst_1_lst' ->
    Forall2 (fun v s => Externaddrs_ok v_S' (externaddr_MEM v) (MEM s)) v_memaddrs tcf.
Proof.
	move => v_S v_S' v_memaddrs meminst_1_lst' meminst_2_lst.
	move: v_S v_S'.
	induction v_memaddrs;
	move => v_S v_S' tcf HOk Hlength HApp Hext => //=; destruct tcf => //=; simpl in HOk;
	try (apply Forall2_length in HOk; discriminate).
	rewrite -app_cat in HApp.
	subst.
	apply Forall2_cons_iff. split.
	- inversion HOk; subst.
	  apply (addrs_mems_extension v_S) with
	  (meminst_1_lst' := meminst_1_lst') (meminst_2_lst := meminst_2_lst) => //.
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
		eapply mk_Export_instance_ok with (ext := ext).
		inversion Hext; decomp.
		eq_to_prop. 
		inversion H3; subst.
		+ eapply addrs_store_funcs_extension; simpl; eauto.
		+ eapply addrs_tables_extension; simpl; eauto.
		+ eapply addrs_mems_extension; simpl; eauto.
		+ eapply addrs_store_globals_extension; simpl; eauto.
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

	induction ref_lst; auto.
	inversion H; subst; auto.
	econstructor.
	{
		eapply store_extension_ref; eauto.
	}
	eapply IHref_lst; eauto.
	by inversion Het.
Qed.

Lemma store_extension_eleminsts': forall v_S v_S' aa ts,
	Store_extension v_S v_S' ->
	Forall (λ a , a < Datatypes.length (store_ELEMS v_S)) aa ->
	Forall2 (λ a t, Element_instance_ok v_S (lookup_total (store_ELEMS v_S) a) t) aa ts ->
	Forall (λ a , a < Datatypes.length (store_ELEMS v_S')) aa /\
	Forall2 (λ a t, Element_instance_ok v_S' (lookup_total (store_ELEMS v_S') a) t) aa ts.
Proof.
	move => s s' aa ts HS HLen He.
	destruct s, s'.
	inversion HS; eq_to_prop; subst; simpl in *.
	injection H0 as ?; subst.
	injection H as ? ; subst.
	clear - He H9 H10 HLen HS; subst.
	split.
	{
		
		eapply Forall_impl.
		2: eapply HLen.
		simpl.
		move => a HLena.
		rewrite -size_length size_cat.
		rewrite -H9.
		rewrite -size_length in HLena.
		by eapply ltn_addr.
	}
	move : ts HLen He H9 H10.
	induction aa; move => ts HLen He HLeneq Hee. inversion He; subst; auto.
	destruct ts; inversion He; subst.
	constructor.
	{
		inversion HLen; subst.
		rewrite -size_length in H1.
		rewrite HLeneq in H1.
		rewrite -(lookup_app _ _ _ H1).

		eapply Forall2_nth2 in Hee as [_ Hei].
		eapply Hei in H1.
		inversion H1; subst; clear H1.
		rewrite /lookup_total.

		inversion H2; subst.
		rewrite /lookup_total in H1.
		list_to_seq.
		rewrite -H1 in H.
		inversion H; subst; clear H.
		rewrite -H0.
		econstructor.
		eq_to_prop.

		destruct H5; eq_to_prop; subst; auto.
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
	Forall (λ a , a < Datatypes.length (store_DATAS v_S)) aa ->
	Forall (λ a, Data_instance_ok v_S (lookup_total (store_DATAS v_S) a)) aa ->
	Forall (λ a , a < Datatypes.length (store_DATAS v_S')) aa /\
	Forall (λ a, Data_instance_ok v_S' (lookup_total (store_DATAS v_S') a)) aa.
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
		destruct (lookup_total (store_DATAS v_S') a).
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
	inversion HMIT; decomp; eq_to_prop.
	assert (
		Forall (λ a , a < Datatypes.length (store_ELEMS v_S')) elemaddr_lst /\
		Forall2 (λ a t, Element_instance_ok v_S' (lookup_total (store_ELEMS v_S') a) t) elemaddr_lst reftype_lst) as [HElemLen HElem].
	{
	  eapply store_extension_eleminsts'; eauto.
	}
	assert (
		Forall (λ a , a < Datatypes.length (store_DATAS v_S')) dataaddr_lst /\
		Forall (λ a, Data_instance_ok v_S' (lookup_total (store_DATAS v_S') a)) dataaddr_lst) as [HDataLen HData].
	{
	  eapply store_extension_datainsts'; eauto.
	}
	subst.
	apply mk_Module_instance_ok; eq_to_prop; auto.
	- eapply addrss_store_funcs_extension; simpl; eauto.
	- eapply addrss_tables_extension; simpl; eauto.
	- eapply addrss_mems_extension; simpl; eauto.
	- eapply addrss_store_globals_extension; simpl; eauto.
	- eapply store_extension_exts; simpl; eauto.
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
	eq_to_prop; subst.
	econstructor; eauto.
	clear - H1 HS.
	
	induction H1; eauto.
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
	Externaddrs_ok s (externaddr_FUNC fa) (FUNC ft) ->
	Externaddrs_ok s' (externaddr_FUNC fa) (FUNC ft).
Proof.
	move => s s' fa ft HSe HEa.
	invert_funcs.
	eapply funcinst_same in Hfe; subst.
	inversion HEa; eq_to_prop; subst; clear HEa.
	econstructor.
	{
		rewrite Hfeq size_cat.
		by eapply ltn_addr.
	}
	{
		eq_to_prop.
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
		destruct F, C.
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

Lemma construct_tableinsts: forall s ts t tba lim tbr i ref_lst,
	Forall2 (λ v t, Table_instance_ok s v t) (store_TABLES s) ts ->
	Ref_ok s ref_lst t ->
	lookup_total (store_TABLES s) tba =  {| tableinst_TYPE := mk_tabletype lim t; REFS := tbr |} ->
	Forall2 (λ v t, Table_instance_ok s v t)
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
		{
			by rewrite list_update_length_func.
		}
		clear IHHold H3 H.
		injection H0 as ?; subst.
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

Lemma construct_tableinsts_grow: forall s ts ref_lst t tba v_r j_opt v_n,
	Forall2 (λ v t, Table_instance_ok s v t) (store_TABLES s) ts ->
	Ref_ok s ref_lst t ->
	Forall (λ v_j, (Datatypes.length v_r + v_n) <= (v_j :> nat)) (option_to_list j_opt) ->
	lookup_total (store_TABLES s) tba = {|
		tableinst_TYPE := mk_tabletype (mk_limits
			(mk_uN (size v_r)) j_opt) t;
		REFS := v_r |} ->
	Forall2 (λ v t, Table_instance_ok s v t)
		(list_update_func (store_TABLES s) tba
			(fun=> {|
				tableinst_TYPE := mk_tabletype (mk_limits
					(mk_uN (size v_r + v_n)) j_opt) t;
				REFS := v_r ++ repeat ref_lst v_n
			|}))
		(list_update_func ts tba (fun=> mk_tabletype (mk_limits
			(mk_uN (size v_r + v_n)) j_opt) t)).
Proof.
	move => s ts ref_lst t tba v_r j_opt v_n Hold HRef HRange HLookup.
	move : tba HLookup HRef.
	induction Hold; auto; move => tba HLookup HRef.
	destruct tba.
	{
		simpl.
		econstructor; auto.
		inversion H; subst.
		rewrite /lookup_total /= in HLookup.
		inversion HLookup; subst; clear HLookup.
		destruct j_opt.
		{
		(* j_opt is Some *)
			destruct u.
			econstructor; eq_to_prop; eauto.
			{
				by rewrite size_cat repeat_size.
			}

			all: injection H0 as ?; subst.
			{
				rewrite Forall_app.
				subst.
				
				split; auto.
				clear - HRef H3.
				induction v_n; auto.
				econstructor; auto. 
			}
			inversion H3; subst; clear H3.
			econstructor.
			inversion H4; subst; clear H4.
			destruct m_opt; try discriminate; subst; eauto.
			inversion H7; subst.
			injection H3 as ?; subst.
			destruct_all.
			list_to_seq.
			move/andP in H6; destruct H6. 
			inversion HRange; subst.
			econstructor; auto.
			- eapply leq_trans in H3. 
				apply H3.
				apply H9.
			- econstructor; eauto.
				apply/andP; split; eauto.
		}
		(* j_opt is None *)
		{
			eq_to_prop.
			injection H0 as ?; subst.
			inversion H4.
		}
	}
	simpl.
	econstructor; auto.
Qed.


Lemma construct_globalinsts: forall s ts ga v t v_old,
	Forall2 (λ v t, Global_instance_ok s v t) (store_GLOBALS s) ts ->
	lookup_total (store_GLOBALS s) ga = {| globalinst_TYPE := mk_globaltype (Some MUT_MUT) t; VALUE := v_old |} ->
	Val_ok s v t ->
	Forall2 (λ v t, Global_instance_ok s v t)
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
		eq_to_propH H0; injection H0 as ?; subst.
		eauto.
	}
	simpl.
	econstructor; auto.
Qed.

Lemma construct_meminsts: forall s ts ma v_mt b_lst v_i v_nb,
	Forall2 (λ v t, Memory_instance_ok s v t) (store_MEMS s) ts ->
	lookup_total (store_MEMS s) ma = {| meminst_TYPE := v_mt; BYTES := b_lst |} ->
	Forall2 (λ v t, Memory_instance_ok s v t)
		(list_update_func (store_MEMS s) ma
			(λ m, m <| BYTES :=
			list_slice_update (BYTES m) v_i (length v_nb) v_nb |>)) ts.
Proof.
	move => s ts ma v_mt b_lst v_i v_nb Hold HLookup.
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
	}
	simpl.
	econstructor; auto.
Qed.

Lemma construct_meminsts_grow: forall s ts ma b_lst lim_old v_n v_j,
	Forall2 (λ v t, Memory_instance_ok s v t) (store_MEMS s) ts ->
	lookup_total (store_MEMS s) ma = {|
		meminst_TYPE := PAGE (mk_limits (lim_old) (Some v_j));
		BYTES := b_lst |} ->
	lim_old = Datatypes.length b_lst / (64 * Ki) ->
	lim_old + v_n <= v_j ->
	Forall2 (λ (v : meminst) (t : memtype), Memory_instance_ok s v t)
		(list_update_func (store_MEMS s) ma
		(fun=> {| meminst_TYPE := PAGE (mk_limits (lim_old + v_n) (Some v_j));
			BYTES := b_lst ++ repeat (mk_byte 0) (v_n * (64 * Ki)) |}))
		(list_update_func ts ma (fun=> PAGE (mk_limits (lim_old + v_n) (Some v_j)))).
Proof.
	move => s ts ma b_lst lim_old v_n v_j Hold HLookup HLim HRange.
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
		remember (64 * Ki) as n.
		eq_to_prop.
		assert (n <> 0). { subst. rewrite /Ki. discriminate. }
		injection H2 as ?; subst.
		list_to_seq.
		econstructor; eq_to_prop; eauto.
		{
			rewrite size_cat H4 repeat_size.
			rewrite -!mulnA.
			rewrite mulnDl.
			rewrite mulnE.
			rewrite Nat.div_mul; auto.
		}
		econstructor.
		rewrite <- invert_opt_map_some.
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
			apply/andP; split; auto.
	}
	econstructor; auto.
Qed.

Lemma construct_datainsts: forall s da b_lst,
	Forall [eta Data_instance_ok s]
		(store_DATAS s) ->
	lookup_total (store_DATAS s) da = {| datainst_BYTES := b_lst |} ->
	Forall [eta Data_instance_ok s]
		(list_update_func (store_DATAS s) da [eta set datainst_BYTES (fun=> [])]).
Proof.
	move => s da b_lst Hold HLookup.
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
	Forall2 (λ v t, Element_instance_ok s v t) (store_ELEMS s) ts ->
	lookup_total (store_ELEMS s) ea = {| eleminst_TYPE := t; eleminst_REFS := ref |} ->
	Forall2 (λ v t, Element_instance_ok s v t)
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
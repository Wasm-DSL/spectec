From Stdlib Require Import String List Unicode.Utf8 NArith Arith QArith Lia.
From RecordUpdate Require Import RecordSet.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
(* TODO: Is Notation global? *)
(* TODO: Is Coercion global? *)
From WasmSpectec Require Import wasm.

From WasmSpectec Require Import helper_lemmas helper_tactics typing_lemmas extension_lemmas subtyping axioms.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.

(* NOTE: Naming conventions:
         1. type for types
         2. type__constructor for types with multiple constructors
         3. type__ for types with a single constructor *)

(* NOTE: Comment out below to display coercions in proof state *)
(* Set Printing Coercions. *)
(* NOTE: Comment out below to display parentheses in proof state *)
(* Set Printing Parentheses. *)

Lemma cat_nil : forall T (s1 s2 : seq T),
  (s1 ++ s2) = [] <-> s1 = [] /\ s2 = [].
Proof.
  move => T s1 s2. split.
  - by case: s1; case s2.
  - by move => [-> ->].
Qed.

Lemma length_size: forall T T' (s1: seq T) (s2: seq T'),
    length s1 = length s2 <-> size s1 = size s2.
Proof. done. Qed.

Lemma LOCAL_injective: injective LOCAL.
Proof.
  move=> x y H.
  by injection H as ?.
Qed.

Lemma default_not_none: forall ts,
  Forall (fun t => t != BOT) ts ->
  Forall (fun t => default_ t != None) ts.
Proof.
  move => ts HForall.
  induction HForall => //=.
  apply Forall_cons; eauto.
  destruct x; try discriminate; eauto.
Qed.

Lemma wf_config_app : forall s ais ais',
  wf_config (mk_config s (ais ++ ais')) <->
  (wf_config (mk_config s ais) /\ wf_config (mk_config s ais')).
Proof.
  move=> s ais ais'.
  split.
  - move=> H.
    inversion H; subst.
    apply Forall_app in H3; destruct H3.
    split; econstructor; eauto.
  - move=> [H1 H2].
    inversion H1; subst.
    inversion H2; subst.
    econstructor; eauto.
    apply Forall_app; eauto.
Qed.

Definition is_const (e : admininstr) : bool :=
  match e with
  | admininstr_CONST _ _ => true
  | admininstr_VCONST _ _ => true
  | admininstr_REF_NULL _ => true
  | admininstr_REF_FUNC_ADDR _ => true
  | admininstr_REF_HOST_ADDR _ => true
  | _ => false
  end.

Definition const_list (es : list admininstr) : bool :=
  List.forallb is_const es.

Lemma v_to_e_const: forall vs,
    const_list (map admininstr_val vs).
Proof.
  move => vs. elim: vs => //=.
  move => v vs Hconst.
  case v => //=.
Qed.

(* NOTE: const_list es is coerced into proposition by is_true *)
Definition terminal_form (es : list admininstr) :=
  const_list es \/ es = [admininstr_TRAP].

Lemma const_list_cat: forall vs1 vs2,
    const_list (vs1 ++ vs2) = const_list vs1 && const_list vs2.
Proof.
  move => vs1 vs2.
  repeat rewrite cat_app.
  rewrite /const_list.
  by rewrite List.forallb_app.
Qed.

Lemma const_list_concat: forall vs1 vs2,
    const_list vs1 ->
    const_list vs2 ->
    const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2 Hconst1 Hconst2.
  rewrite const_list_cat.
  apply/andP => //=.
Qed.

Lemma const_list_split: forall vs1 vs2,
    const_list (vs1 ++ vs2) ->
    const_list vs1 /\
    const_list vs2.
Proof.
  move => vs1 vs2 Hconst.
  rewrite const_list_cat in Hconst.
  by move/andP in Hconst.
Qed.

Lemma const_es_exists: forall es,
    const_list es ->
    {vs | es = map admininstr_val vs}.
Proof.
  induction es => //=.
  - by exists [].
  - move => HConst.
    move/andP in HConst. destruct HConst as [? HConst].
    destruct a => //=;
    apply IHes in HConst as [vs ->].
    + by exists (val_CONST v_numtype n :: vs).
    + by exists (val_VCONST v_vectype v :: vs).
    + by exists (val_REF_NULL v_reftype :: vs).
    + by exists (val_REF_FUNC_ADDR v_funcaddr :: vs).
    + by exists (val_REF_HOST_ADDR v_hostaddr :: vs).
Qed.

(* TODO: Rename this lemma more appropriately *)
(* TODO: There may be an equivalent lemma in ssreflect *)
Lemma map_eq_nil {A B : Type} (f : A -> B) (l : seq A) :
  map f l = [] -> l = [].
Proof.
  case: l => //=.
Qed.

(* TODO: Rename this lemma more appropriately *)
(* TODO: There may be an equivalent lemma in ssreflect *)
Lemma map_neq_nil {A B : Type} (f: A -> B) (l: seq A) :
  map f l <> [] → l <> [].
Proof.
  case: l => //=.
Qed.

(* MEMO: reduce_simple -> Step_pure *)
(* MEMO: rs_trap -> step_trap_vals *)
Lemma reduce_trap_left: forall vs,
    const_list vs ->
    vs <> [] ->
    Step_pure (vs ++ [admininstr_TRAP]) [admininstr_TRAP].
Proof.
  move => vs HConst H.
  apply const_es_exists in HConst as [vcs ->].
  eapply trap_vals with (val_lst := vcs) (admininstr_lst := []) => //=.
  eq_to_prop.
  left.
  eq_to_prop. 
  by apply/map_neq_nil: H.
Qed.

(* TODO: Rename this lemma more appropriately *)
Lemma v_e_trap: forall vs es,
    const_list vs ->
    vs ++ es = [admininstr_TRAP] ->
    vs = [] /\ es = [admininstr_TRAP].
Proof.
  move => vs es HConst H.
  destruct vs => //=.
  destruct vs => //=. destruct es => //=.
  simpl in H. inversion H. by subst.
Qed.

(* TODO: Rename this lemma more appropriately *)
Lemma concat_cancel_last: forall {X:Type} (l1 l2: seq X) (e1 e2:X),
    l1 ++ [e1] = l2 ++ [e2] ->
    l1 = l2 /\ e1 = e2.
Proof.
  move => X l1 l2 e1 e2 H.
  assert (rev (l1 ++ [e1]) = rev (l2 ++ [e2])); first by rewrite H.
  repeat rewrite rev_cat in H0. inversion H0.
  rewrite - (revK l1). rewrite H3. split => //. by apply revK.
Qed.

(* TODO: Rename this lemma more appropriately *)
Lemma extract_list1 : forall {X:Type} (es: seq X) (e1 e2:X),
    es ++ [e1] = [e2] ->
    es = [] /\ e1 = e2.
Proof.
  move => X es e1 e2 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma v_to_e_cat: forall vs1 vs2,
    map admininstr_val vs1 ++ map admininstr_val vs2 =
    map admininstr_val (vs1 ++ vs2).
Proof.
  move => vs1. elim: vs1 => //=.
  - move => a l IH vs2. by rewrite IH.
Qed.

Lemma be_to_e_cat: forall bes1 bes2,
    map admininstr_instr bes1 ++ map admininstr_instr bes2 =
    map admininstr_instr (bes1 ++ bes2).
Proof.
  move => bes1. elim: bes1 => //=.
  - move => a l IH bes2. by rewrite IH.
Qed.

Lemma to_e_list_cat: forall bes1 bes2,
    map admininstr_instr (bes1 ++ bes2) = 
    map admininstr_instr bes1 ++ map admininstr_instr bes2.
Proof.
  induction bes1 => //.
  move => bes2. simpl. by f_equal.
Qed.

(* TODO: Move this to the top of this file *)
Lemma cat_split: forall {X: Type} (l l1 l2: seq X),
    l = l1 ++ l2 ->
    l1 = take (size l1) l /\
    l2 = drop (size l1) l.
Proof.
  move => X l l1.
  generalize dependent l.
  induction l1 => //=; move => l l2 HCat; subst => //=.
  - split. by rewrite take0. by rewrite drop0.
  - edestruct IHl1.
    instantiate (1 := l2). eauto.
    split => //.
    by f_equal.
Qed.

Lemma terminal_form_v_e: forall vs es,
    const_list vs ->
    terminal_form (vs ++ es) ->
    terminal_form es.
Proof.
  move => vs es HConst HTerm.
  unfold terminal_form in HTerm.
  destruct HTerm.
  - unfold terminal_form. left.
    apply const_list_split in H. by destruct H.
  - destruct vs => //=.
    + simpl in H. subst. unfold terminal_form. by right.
    + destruct vs => //=. destruct es => //=.
      simpl in H. inversion H. by subst.
Qed.

Definition typeof (val_lst : wasm.val): valtype :=
	match val_lst with
		| val_CONST t _ => valtype_numtype t
		| val_VCONST t _ => valtype_vectype t
		| val_REF_NULL t => valtype_reftype t
		| val_REF_FUNC_ADDR _ => valtype_FUNCREF
		| val_REF_HOST_ADDR _ => valtype_EXTERNREF
		end.

Lemma typeof_append: forall ts t vs,
    map typeof vs = ts ++ [t] ->
    (* TODO: Perhaps this might suffice like typeof_cat below *)
    (* exists vs' v,
      map typeof vs' = ts /\
      typeof v = t *)
    exists v,
      vs = take (size ts) vs ++ [v] /\
      map typeof (take (size ts) vs) = ts /\
      typeof v = t.
Proof.
  move => ts t vs HMapType.
  apply cat_split in HMapType.
  destruct HMapType.
  rewrite -map_take in H.
  rewrite -map_drop in H0.
  destruct (drop (size ts) vs) eqn:HDrop => //=.
  destruct l => //=.
  inversion H0. subst.
  exists v.
  split => //.
  rewrite -HDrop. by rewrite cat_take_drop.
Qed.

Lemma typeof_cat: forall ts1 ts2 vs,
  map typeof vs = ts1 ++ ts2 ->
  exists vs1 vs2,
    vs = vs1 ++ vs2 /\
    map typeof vs1 = ts1 /\
    map typeof vs2 = ts2.
Proof.
  move => + ts2.
  elim/last_ind: ts2 => [ | ts2' t IH].
  - move => ts1 vs H.
    exists vs, [].
    split; try split => //=.
    + by rewrite cats0.
    + by rewrite cats0 in H.
  - move => ts1 vs H.
    rewrite -cats1 catA in H *.
    move/typeof_append: H => [v [Hvs [H1 H2]]].
    move/(_ ts1 (take (size (ts1 ++ ts2')) vs) H1): IH => [vs1 [vs2 [Hvs' [IH1 IH2]]]].
    exists vs1, (vs2 ++ [v]). 
    split; try split => //=.
    - by rewrite catA -Hvs'.
    - rewrite 2!cats1 map_rcons. by congr rcons.
Qed.

(* Ltac invert_wf_val_forall Hwf :=
  match type of Hwf with
  | List.Forall wf_val [_; _; _] =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let v3 := fresh "v3" in 
    let v4 := fresh "v4" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let vcs3 := fresh "vcs3" in
    let vcs4 := fresh "vcs4" in 
    case: Hwf => H Hwf //=;
    case: vcs1 H Hwf => [ | v2 vcs2] H Hwf //=;
    case: vcs2 H Hwf => [ | v3 vcs3] H Hwf //=;
    case: vcs3 H Hwf => [ | v4 vcs4] H Hwf //=;
  (* | map typeof ?vcs = [_; _] =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let v3 := fresh "v3" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let vcs3 := fresh "vcs3" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    case: vcs H Hwf => [ | v1 vcs1] H Hwf //=;
    case: vcs1 H Hwf => [ | v2 vcs2] H Hwf //=;
    case: vcs2 H Hwf => [ | v3 vcs3] H Hwf //=;
    case: H => Ht1 Ht2
  | map typeof ?vcs = [_] =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let Ht1 := fresh "Ht1" in
    case: vcs H Hwf => [ | v1 vcs1] H Hwf //=;
    case: vcs1 H Hwf => [ | v2 vcs2] H Hwf //=;
    case: H => Ht1
  | map typeof ?vcs = [] =>
    let v1 := fresh "v1" in 
    let vcs1 := fresh "vcs1" in
    (* NOTE: This performs injection on Hts : [seq typeof i  | i <- vcs] = [t1] *)
    case: vcs H Hwf => [ | v1 vcs1] H Hwf //= *)
  end. *)

(* NOTE: Given Hts : [seq typeof i  | i <- vcs] = [t],
         generates equalities on elements of vcs like [v1] = [t] and typeof v1 = t *)
Ltac invert_typeof_vcs H Hwf HWfConfig := 
  match type of H with
  | seq.map typeof ?vcs = [_; _; _] =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let v3 := fresh "v3" in 
    let v4 := fresh "v4" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let vcs3 := fresh "vcs3" in
    let vcs4 := fresh "vcs4" in 
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    let Ht3 := fresh "Ht3" in
    case: vcs H Hwf HWfConfig => [ | v1 vcs1] H Hwf HWfConfig //=;
    case: vcs1 H Hwf HWfConfig => [ | v2 vcs2] H Hwf HWfConfig //=;
    case: vcs2 H Hwf HWfConfig => [ | v3 vcs3] H Hwf HWfConfig //=;
    case: vcs3 H Hwf HWfConfig => [ | v4 vcs4] H Hwf HWfConfig //=;
    case: H => Ht1 Ht2 Ht3
  | seq.map typeof ?vcs = [_; _] =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let v3 := fresh "v3" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let vcs3 := fresh "vcs3" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    case: vcs H Hwf HWfConfig => [ | v1 vcs1] H Hwf HWfConfig //=;
    case: vcs1 H Hwf HWfConfig => [ | v2 vcs2] H Hwf HWfConfig //=;
    case: vcs2 H Hwf HWfConfig => [ | v3 vcs3] H Hwf HWfConfig //=;
    case: H => Ht1 Ht2

  | seq.map typeof ?vcs = [] =>
    let v1 := fresh "v1" in 
    let vcs1 := fresh "vcs1" in
    (* NOTE: This performs injection on Hts : [seq typeof i  | i <- vcs] = [t1] *)
    case: vcs H Hwf HWfConfig => [ | v1 vcs1] H Hwf HWfConfig //=
  | seq.map typeof ?vcs = [_] =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let Ht1 := fresh "Ht1" in
    case: vcs H Hwf HWfConfig => [ | v1 vcs1] H Hwf HWfConfig //=;
    case: vcs1 H Hwf HWfConfig => [ | v2 vcs2] H Hwf HWfConfig //=;
    case: H => Ht1
  end.



Lemma invert_typeof_I32: forall v,
  typeof v = valtype_I32 ->
  wf_val v ->
  exists v',
    admininstr_val v = (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN v'))).
Proof.
  move => v Ht Hwf.
  destruct v; rewrite /typeof in Ht; try by discriminate.
  - destruct v_numtype; try discriminate.
    inversion Hwf; subst. inversion H0; eq_to_prop; subst.
    - destruct v_Inn; try discriminate. 
      destruct var_x.
      by exists i.
    - destruct v_Fnn; by discriminate.
  - destruct v_vectype; by discriminate.
  - destruct v_reftype; by discriminate.
Qed.

Lemma invert_typeof_I64: forall v,
  typeof v = valtype_I64 ->
  wf_val v ->
  exists v',
    admininstr_val v = (admininstr_CONST I64 (mk_num__0 Inn_I64 (mk_uN v'))).
Proof.
  move => v Ht Hwf.
  destruct v; rewrite /typeof in Ht; try by discriminate.
  - destruct v_numtype; try discriminate.
    inversion Hwf; subst. inversion H0; eq_to_prop; subst.
    - destruct v_Inn; try discriminate. 
      destruct var_x.
      by exists i.
    - destruct v_Fnn; by discriminate.
  - destruct v_vectype; by discriminate.
  - destruct v_reftype; by discriminate.
Qed.

Lemma invert_typeof_numtype: forall v (t: numtype),
  typeof v = (valtype_numtype t) ->
  exists (n: num_),
    admininstr_val v = (admininstr_CONST t n).
Proof.
  move => v t Ht.
  destruct v; rewrite /typeof in Ht; try by destruct t; discriminate.
  {
    destruct v_numtype; simpl in Ht; destruct t; try discriminate;
    exists n; auto.
  }
  - destruct v_vectype; destruct t; discriminate.
  - destruct v_reftype; destruct t; discriminate.
Qed.

Lemma invert_typeof_numtype_wf: forall v (t: numtype),
  typeof v = (valtype_numtype t) ->
  wf_val v ->
  exists (n: num_),
    admininstr_val v = (admininstr_CONST t n) /\ wf_num_ t n.
Proof.
  move => v t Ht Hwf.
  destruct v; rewrite /typeof in Ht; try by destruct t; discriminate.
  - destruct v_numtype; simpl in Ht; destruct t; try discriminate;
      (exists n; split; first by []); by inversion Hwf.
  - destruct v_vectype; destruct t; discriminate.
  - destruct v_reftype; destruct t; discriminate.
Qed.


Lemma invert_typeof_V128: forall v,
  typeof v = valtype_V128 ->
  wf_val v ->
  exists (c: vec_),
    admininstr_val v = (admininstr_VCONST V128 c) /\
    wf_uN (!(res_size (valtype_vectype V128))) c.
Proof.
  move => v Ht Hwf.
  destruct v; rewrite /typeof in Ht; try discriminate.
  - by destruct v_numtype; discriminate.
  - destruct v_vectype; simpl in Ht.
    exists v; split; first by [].
    by inversion Hwf.
  - by destruct v_reftype; discriminate.
Qed.

Lemma invert_typeof_reftype: forall v (t: reftype),
  typeof v = (valtype_reftype t) ->
  ( admininstr_val v = (admininstr_REF_NULL t) ) \/
  ( exists x,
    admininstr_val v = (admininstr_REF_FUNC_ADDR x) \/
    admininstr_val v = (admininstr_REF_HOST_ADDR x) 
    ).
Proof.
  move => v t Ht.
  destruct v; rewrite /typeof in Ht.
  {
    destruct v_numtype; simpl in Ht; destruct t; try discriminate.
  }
  {
    destruct v_vectype; simpl in Ht; destruct t; try discriminate.
  }
  {
    left.
    destruct v_reftype, t; try discriminate; auto.
  }
  {
    right.
    exists v_funcaddr.
    left. auto.
  }
  {
    right.
    exists v_hostaddr.
    right. auto.
  }
Qed.

Lemma invert_typeof_reftype': forall v (t: reftype),
  typeof v = (valtype_reftype t) ->
  ( exists r,
    admininstr_val v = admininstr_ref r).
Proof.
  move => v t Ht.
  destruct v; rewrite /typeof in Ht.
  {
    destruct v_numtype; simpl in Ht; destruct t; try discriminate.
  }
  {
    destruct v_vectype; simpl in Ht; destruct t; try discriminate.
  }
  {
    destruct v_reftype, t; try discriminate.
    - by exists (ref_REF_NULL FUNCREF).
    - by exists (ref_REF_NULL EXTERNREF).
  }
  {
    by exists (REF_FUNC_ADDR v_funcaddr).
  }
  {
    by exists (REF_HOST_ADDR v_hostaddr).
  }
Qed.

Definition instr_eqb v1 v2 : bool := instr_eq_dec v1 v2.
Definition eqinstrP : Equality.axiom instr_eqb :=
  eq_dec_Equality_axiom instr instr_eq_dec.

Lemma list_slice_size : forall {T : Type} (bs : seq T) i j,
  ((i + j)%BN <= |bs|)%BN ->
  |list_slice bs i j| = j.
Proof.
  move => T bs.
  elim: bs => [ | b bs' IH].
  - move => /= i j H.
    rewrite (N.le_0_r) in H.
    rewrite N.eq_add_0 in H; destruct H; eauto.
  - move => /= i j H.
    destruct i using N.peano_ind; destruct j using N.peano_ind; eauto; try clear IHj; try clear IHi.
    - resolve_Nsucc. simpl. rewrite cvt_succ'. congr N.succ. apply IH.
      rewrite cvt_succ' in H.
      simpl in H.
      by apply N.succ_le_mono in H.
    - destruct i; eauto.
    - 
      rewrite N.add_succ_l in H.
      rewrite cvt_succ' in H.
      apply N.succ_le_mono in H.

      specialize (IH i (N.succ j) H).
      resolve_Nsucc.
      destruct j; eauto. 
Qed.

(* NOTE: Mutual induction principle used in t_progress_be *)
Scheme Instr_ok_ind' := Induction for Instr_ok Sort Prop
  with Instrs_ok_ind' := Induction for Instrs_ok Sort Prop.

Definition br_reduce es := 
  exists vcs l es',
  es = map admininstr_val vcs ++ [admininstr_BR l] ++ es'.

Definition return_reduce es :=
  exists vcs es',
  es = map admininstr_val vcs ++ [admininstr_RETURN] ++ es'.

(* NOTE: We could define this as ~ (br_reduce es) *)
Definition not_lf_br es :=
  forall vcs l es',
  es <> map admininstr_val vcs ++ [admininstr_BR l] ++ es'.

(* NOTE: We could define this as ~ (return_reduce es) *)
Definition not_lf_return es :=
  forall vcs es',
  es <> map admininstr_val vcs ++ [admininstr_RETURN] ++ es'.

(* TODO: Define this in wasm.v *)
Fixpoint split_vals (es : seq admininstr) : seq (wasm.val) * seq admininstr :=
  match es with
  | (admininstr_CONST t v) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((val_CONST t v) :: vs', es'')
  | (admininstr_VCONST t v) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((val_VCONST t v) :: vs', es'')
  | (admininstr_REF_NULL t) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((val_REF_NULL t) :: vs', es'')
  | (admininstr_REF_FUNC_ADDR t) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((val_REF_FUNC_ADDR t) :: vs', es'')
  | (admininstr_REF_HOST_ADDR t) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((val_REF_HOST_ADDR t) :: vs', es'')
  | _ => ([], es)
  end.

Lemma split_vals_inverse : forall vs es es',
  split_vals es = (vs, es') ->
  es = map admininstr_val vs ++ es'.
Proof.
  move => vs es es' H.
  move: vs es' H.
  elim: es => [ | e es' IH].
  - move => vs es' H.
    case: H => Hvs Hes'.
    by rewrite -Hvs -Hes'.
  - (* TODO: Use case tactic instead *)
    destruct e;
    try (move => vs es'' H;
         case: H => Hvs Hes'';
         by rewrite -Hvs -Hes'').
    all: move => vs es'' H;
    case Ees': (split_vals es') => [svs ses];
    rewrite /= Ees' in H;
    case: H => Hvs Hes'';
    move/IH: Ees' => {}IH;
    by rewrite -Hvs -Hes'' IH /=.
Qed.

Lemma split_vals_prefix : forall vs e es,
  (~is_const e) ->
  split_vals (map admininstr_val vs ++ [e] ++ es) = (vs, [e] ++ es).
Proof.
  move => vs e es H.
  elim: vs => [ | v vs'].
  - case: e H => //=.
  - case: v => /=.
    1,2,3: move => t'.
    1,2,4,5: move => v'.
    all: move => IH;
    by rewrite IH.
Qed.

Lemma br_reduce_decidable : forall es,
  decidable (br_reduce es).
Proof.
  rewrite /decidable /br_reduce.
  move => es.
  case Ees: (split_vals es) => [vs es'].
  case Ees': es' => [ | e es''].
  - right. move => [vcs [l [es''' Hcontra]]].
    rewrite Hcontra in Ees.
    rewrite (split_vals_prefix vcs (admininstr_BR l) es''') in Ees; last by [].
    case: Ees => Hvs Hes'.
    by rewrite Ees' in Hes'.
  - (* TODO: Use case tactic instead *)
    destruct e;
    try (right;
         move => [vcs [li [es''' Hcontra]]];
         rewrite Hcontra in Ees;
         rewrite (split_vals_prefix vcs (admininstr_BR li) es''') in Ees; last by [];
         case: Ees => Hvs Hes';
         by rewrite Ees' in Hes').
    all: left.
    exists vs, v_labelidx, es''.
    rewrite /= -Ees'.
    by rewrite (split_vals_inverse _ _ _ Ees).
Qed.

Lemma return_reduce_decidable : forall es,
  decidable (return_reduce es).
Proof.
  rewrite /decidable /return_reduce.
  move => es.
  case Ees: (split_vals es) => [vs es'].
  case Ees': es' => [ | e es''].
  - right. move => [vcs [es''' Hcontra]].
    rewrite Hcontra in Ees.
    rewrite (split_vals_prefix vcs (admininstr_RETURN) es''') in Ees; last by [].
    case: Ees => Hvs Hes'.
    by rewrite Ees' in Hes'.
  - (* TODO: Use case tactic instead *)
    destruct e;
    try (right;
         move => [vcs [es''' Hcontra]];
         rewrite Hcontra in Ees;
         rewrite (split_vals_prefix vcs (admininstr_RETURN) es''') in Ees; last by [];
         case: Ees => Hvs Hes';
         by rewrite Ees' in Hes').
    left. exists vs, es''.
    rewrite /= -Ees'.
    by rewrite (split_vals_inverse _ _ _ Ees).
Qed.

Lemma not_br_reduce_not_lf_br : forall es,
  ~ (br_reduce es) -> not_lf_br es.
Proof.
  rewrite /br_reduce /not_lf_br.
  move => es H1 vcs l es' H2.
  apply: H1. by exists vcs, l, es'. 
Qed.

Lemma not_return_reduce_not_lf_return : forall es,
  ~ (return_reduce es) -> not_lf_return es.
Proof.
  rewrite /return_reduce /not_lf_return.
  move => es H1 vcs es' H2.
  apply: H1. by exists vcs, es'.
Qed.

Lemma not_lf_br_singleton : forall e l,
  not_lf_br [e] -> e <> admininstr_BR l.
Proof.
  move => e l H Hcontra.
  rewrite Hcontra /not_lf_br in H.
  by move/(_ [] l []): H => H.
Qed.

Lemma not_lf_return_singleton : forall e,
  not_lf_return [e] -> e <> admininstr_RETURN.
Proof.
  move => e H Hcontra.
  rewrite Hcontra /not_lf_return in H.
  by move/(_ [] []): H => H.
Qed.

Lemma not_lf_br_right : forall es1 es2,
  not_lf_br (es1 ++ es2) -> 
  not_lf_br es1.
Proof.
  rewrite /not_lf_br.
  move => es1 es2 Hnotbr vcs l es' Hcontra.
  move/(_ vcs l (es' ++ es2)): Hnotbr => Hnotbr.
  rewrite Hcontra -2!catA in Hnotbr.
  by apply: Hnotbr.
Qed.

Lemma not_lf_br_left : forall es1 es2,
  const_list es1 ->
  not_lf_br (es1 ++ es2) -> 
  not_lf_br es2.
Proof.
  rewrite /not_lf_br.
  move => es1 es2 Hconst Hnotbr vcs l es' Hcontra.
  move/const_es_exists: Hconst => [vs1 Hvs1].
  move/(_ (vs1 ++ vcs) l es'): Hnotbr => Hnotbr.
  by rewrite Hvs1 Hcontra -v_to_e_cat -catA in Hnotbr.
Qed.

Lemma not_lf_return_right : forall es1 es2,
  not_lf_return (es1 ++ es2) -> 
  not_lf_return es1.
Proof.
  rewrite /not_lf_return.
  move => es1 es2 Hnotret vcs es' Hcontra.
  move/(_ vcs (es' ++ es2)): Hnotret => Hnotret.
  rewrite Hcontra -2!catA in Hnotret.
  by apply: Hnotret.
Qed.

Lemma not_lf_return_left : forall es1 es2,
  const_list es1 ->
  not_lf_return (es1 ++ es2) -> 
  not_lf_return es2.
Proof.
  rewrite /not_lf_return.
  move => es1 es2 Hconst Hnotret vcs es' Hcontra.
  move/const_es_exists: Hconst => [vs1 Hvs1].
  move/(_ (vs1 ++ vcs) es'): Hnotret => Hnotret.
  by rewrite Hvs1 Hcontra -v_to_e_cat -catA in Hnotret.
Qed.

Lemma Forall2_Val_ok_is_same_as_map: forall v_S v_t1 v_local_vals,
	Forall2 (fun v s => Val_ok v_S s v) v_t1 v_local_vals ->
	seq.map typeof v_local_vals = v_t1.
Proof.
	move => s v_t1 v_local_vals Hforall2.
  generalize dependent v_local_vals.
  induction v_t1; move => v_local_vals H; destruct v_local_vals => //=; inversion H.
  subst. f_equal. 
  - inversion H3 => //=.
    inversion H0 => //=.
  - by apply IHv_t1.
Qed.

Lemma frame_t_context_local_types: forall s f C,
  Frame_ok s f C ->
  context_LOCALS C = map typeof (LOCALS f).
Proof.
  move => s i C Hframe.
  inversion Hframe as [? ? ? ? ? Hmod ? Hval].
  inversion Hmod => //=.
  rewrite /_append /Append_List_ cats0.
  by eapply Forall2_Val_ok_is_same_as_map in Hval.
Qed.

Lemma frame_t_context_label_empty: forall s f C,
  Frame_ok s f C ->
  LABELS C = [].
Proof.
  move => s i C Hframe.
  inversion Hframe as [? ? ? ? ? Hmod ? Hval].
  by inversion Hmod.
Qed.


Lemma wf_forall_admin_val : forall v_lst,
  List.Forall (fun v => wf_val v) v_lst <->
  List.Forall (fun a => wf_admininstr a) (seq.map (fun v => admininstr_val v) v_lst).
Proof.
  move=> v_lst.
  split; move=> HForall.
  - induction HForall => //=.
    apply Forall_cons; eauto.
    inversion H; subst; econstructor; eauto.
  - induction v_lst => //=.
    apply Forall_cons.
    + inversion HForall; subst.
      destruct a; inversion H1; econstructor; eauto.
    + eapply IHv_lst; eauto.
      by inversion HForall.
Qed.

Lemma wf_forall_admin : forall i_lst,
  List.Forall (fun i => wf_instr i) i_lst ->
  List.Forall (fun a => wf_admininstr a) (seq.map (fun i => admininstr_instr i) i_lst).
Proof.
  move=> i_lst HForall.
  induction HForall => //=.
  econstructor; eauto.
  apply wf_admininstr_instr; eauto.
Qed.


Lemma wf_config_label : forall s n bes es,
  wf_config (mk_config s [LABEL_ n bes es]) ->
  wf_config (mk_config s es) /\ wf_config (mk_config s (seq.map admininstr_instr bes)).
Proof.
  move=> s n bes es HWf.
  inversion HWf; subst.
  inv_Forall H2.
  inversion HP; subst.
  apply wf_forall_admin in H2.
  eapply config_case_0 in H2; eauto.
  eapply config_case_0 in H4; eauto.
Qed.

Lemma wf_config_frame : forall s f' n f es,
  wf_config (mk_config (mk_state s f') [FRAME_ n f es]) ->
  wf_config (mk_config (mk_state s f') es) /\ wf_config (mk_config (mk_state s f) es).
Proof.
  move=> s f' n f es HWf.
  inversion HWf; subst.
  inv_Forall H2.
  inversion HP; subst.
  
  eapply config_case_0 in H4 as HL; eauto.
  inversion H1; subst.
  eapply state_case_0 in H2; eauto.
  eapply (config_case_0 _ _ H2) in H4; eauto.
Qed.

Lemma frame_t_context_return_empty: forall s f C,
	Frame_ok s f C ->
  context_RETURN C = None.
Proof.
  move => s i C Hframe.
  inversion Hframe as [? ? ? ? ? Hmod ? Hval].
  by inversion Hmod.
Qed.

(* TODO: Duplicate of admin_composition_typing_single? *)
Lemma Admin_instrs_ok_cons : forall s C es e ts1 ts2,
  Instrs_ok2 s C ([e] ++ es) (ts1 :-> ts2) ->
  exists ts ts1' ts2' ts3,
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Instrs_ok2 s C [e] (ts1' :-> ts3) /\
    Instrs_ok2 s C es (ts3 :-> ts2').
Proof.
  move => s C es e ts1 ts2 Hadmin.
  eapply ais_seq_typing_inversion in Hadmin as [t3s [H1 H2]].
  exists [], ts1, ts2, t3s.
  split. auto.
  split. auto.
  split; auto.
Qed.
    
(* TODO: Duplicate ofadmin_composition_typing?  *)
Lemma Admin_instrs_ok_cat : forall s C es1 es2 ts1 ts2,
  Instrs_ok2 s C (es1 ++ es2) (ts1 :-> ts2) -> 
  exists ts ts1' ts2' ts3,
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Instrs_ok2 s C es1 (ts1' :-> ts3) /\
    Instrs_ok2 s C es2 (ts3 :-> ts2').
Proof.
  move => s C es1 es2 ts1 ts2 Hadmin.
  move: s C es2 ts1 ts2 Hadmin.
  (* NOTE: Induction on list es2 in reverse direction 
           which works better with Instrs_ok2__seq and Admin_instrs_ok_cons *)
  elim: es1 => [ | es1' e2 IH].
  - move => s C es2 ts1 ts2 Hadmin.
    apply ainstrs_ok_context_store_wf in Hadmin as HWf; destruct HWf as [HWfC [HWfS HWfais]].
    exists [], ts1, ts2, ts1.
    do ! split => //=.
    + rewrite -[ts1]cats0.
      apply: Instrs_ok2__frame; eauto.
      by apply: Instrs_ok2__empty.
  - move => s C es2 ts1 ts2 Hadmin.
    apply ainstrs_ok_context_store_wf in Hadmin as HWf; destruct HWf as [HWfC [HWfS HWfais]].
    inv_Forall HWfais.
    rewrite -cat1s in Hadmin *.
    rewrite -catA in Hadmin *.
    move/Admin_instrs_ok_cons: Hadmin => [ts [ts1' [ts2' [ts3 [Ets1 [Ets2 [Hadmin1 Hadmin2]]]]]]].
    move/(_ s C es2 ts3 ts2' Hadmin2): IH => [ts' [ts1'' [ts2'' [ts3' [Ets1' [Ets2' [Hadmin1' Hadmin2']]]]]]].
    move/(Instrs_ok2__frame _ _ _ ts'): Hadmin1' => Hadmin1'. rewrite -Ets1' in Hadmin1'.
    move/(Instrs_ok2__frame _ _ _ ts'): Hadmin2' => Hadmin2'. rewrite -Ets2' in Hadmin2'.
    specialize (Hadmin1' HWfS HWfC Hrest).
    specialize (Hadmin2' HWfS HWfC HP2).
    move: (Instrs_ok2__seq _ _ _ _ _ _ ts3 Hadmin1 Hadmin1') => {}Hadmin1'.
    exists ts, ts1', ts2', (ts' ++ ts3').
    subst.
    split; eauto.
Qed.

Lemma Admin_instrs_ok_all : forall s C es ts1 ts2,
  Instrs_ok2 s C es (ts1 :-> ts2) -> 
  (* TODO: Rewrite with all *)
  forall e, e \in es -> exists ts1' ts2', Instr_ok2 s C e (ts1' :-> ts2').
Proof.
  (* TODO: Make use of `+` elsewhere *)
  move => + + es.
  elim: es => [ | e' es'].
  - move => s C ts1 ts2 Hadmin e Hin.
    by rewrite in_nil in Hin.
  - move => IH s C ts1 ts2 Hadmin e Hin.
    rewrite in_cons in Hin.
    rewrite -cat1s in Hadmin.
    move/Admin_instrs_ok_cons: Hadmin => [ts [ts1' [ts2' [ts3 [Ets1 [Ets2 [Hadmin1 Hadmin2]]]]]]].
    move/orP: Hin => [Hin1 | Hin2].
    + move/eqP: Hin1 => Hin1.
      rewrite Hin1.
      apply ais_single_typing_inversion' in Hadmin1; destruct Hadmin1 as [t1s_sup [t2s_sub [HType HSub]]].
      by exists t1s_sup, t2s_sub.
    + move/IH: Hadmin2 => {}IH. 
      by move/(_ e Hin2): IH => IH.
Qed.

Lemma s_typing_lf_br' : forall s f C es t1s t2s l,
  (* NOTE: Here rs should not be None unlike s_typing_lf_return
           because we not only use s_typing_lf_br in t_progress to reject top-level occurrences of br
           but also to reject occurrences of br directly within frame t_progress_e *)
  Frame_ok s f C ->
  Instrs_ok2 s C es (t1s :-> t2s) ->
  Forall (fun e => e <> admininstr_BR l) es.
Proof.
  move => s f C es t1s t2s l Hframe Hadmin.

  move: t1s t2s Hadmin.

  induction es => //=.
  move=> t1s t2s Hadmin. 
  apply Forall_cons.
  - move=> H.
    clear IHes.
    rewrite -cat1s in Hadmin.
    apply ais_seq_typing_inversion in Hadmin; destruct Hadmin as [t3s [HType1 HType2]].
    destruct a; try discriminate.
    injection H as ?; subst.
    fold (admininstr_instr (BR l)) in HType2.
    apply revert_to_instr_from_ai in HType2.
    apply instrs_single_typing_inversion in HType2; destruct HType2 as [t1s_sup [t2s_sub [HType2 HSub]]].

    inversion HType2; subst.
    apply frame_t_context_label_empty in Hframe.
    rewrite Hframe in H2.
    ineq_to_prop.
    by apply N.nlt_0_r in H2.

  - rewrite -cat1s in Hadmin.
    apply ais_seq_typing_inversion in Hadmin; destruct Hadmin as [t3s [HType1 HType2]].
    eapply IHes; eauto.
Qed.


Lemma s_typing_lf_br : forall s f C rt es t1s t2s l,
  (* NOTE: Here rs should not be None unlike s_typing_lf_return
           because we not only use s_typing_lf_br in t_progress to reject top-level occurrences of br
           but also to reject occurrences of br directly within frame t_progress_e *)
  Frame_ok s f C ->
  Instrs_ok2 s (prepend_return C rt) es (t1s :-> t2s) ->
  Forall (fun e => e <> admininstr_BR l) es.
Proof.
  move => s f C rt es t1s t2s l Hframe Hadmin.

  move: t1s t2s Hadmin.

  induction es => //=.
  move=> t1s t2s Hadmin. 
  apply Forall_cons.
  - move=> H.
    clear IHes.
    rewrite -cat1s in Hadmin.
    apply ais_seq_typing_inversion in Hadmin; destruct Hadmin as [t3s [HType1 HType2]].
    destruct a; try discriminate.
    injection H as ?; subst.
    fold (admininstr_instr (BR l)) in HType2.
    apply revert_to_instr_from_ai in HType2.
    apply instrs_single_typing_inversion in HType2; destruct HType2 as [t1s_sup [t2s_sub [HType2 HSub]]].

    inversion HType2; subst.
    apply frame_t_context_label_empty in Hframe.
    rewrite Hframe in H2.
    ineq_to_prop.
    by apply N.nlt_0_r in H2.

  - rewrite -cat1s in Hadmin.
    apply ais_seq_typing_inversion in Hadmin; destruct Hadmin as [t3s [HType1 HType2]].
    eapply IHes; eauto.
Qed.

Lemma s_typing_lf_return : forall s f C es t1s t2s,
  Frame_ok s f C ->
  Instrs_ok2 s C es (t1s :-> t2s) ->
  Forall (fun e => e <> admininstr_RETURN) es.
Proof.
  move=> s f C es t1s t2s Hframe.
  move: t1s t2s.
  induction es => //=.
  move=> t1s t2s Hadmin.
  apply Forall_cons.
  - move=> Heq.
    rewrite -cat1s in Hadmin.
    apply ais_seq_typing_inversion in Hadmin; destruct Hadmin as [t3s [HType1 HType2]].
    destruct a; try discriminate.
    fold (admininstr_instr (RETURN)) in HType2.
    apply revert_to_instr_from_ai in HType2.
    apply instrs_single_typing_inversion in HType2; destruct HType2 as [t1s_sup [t2s_sub [HType2 HSub]]].

    inversion HType2; eq_to_prop; subst.
    apply frame_t_context_return_empty in Hframe.
    rewrite Hframe in H1. 
    discriminate.
  - rewrite -cat1s in Hadmin.
    apply ais_seq_typing_inversion in Hadmin; destruct Hadmin as [t3s [HType1 HType2]].
    eapply IHes; eauto.
Qed.

Lemma s_typing_not_lf_br' : forall s f C es t1s t2s,
  Frame_ok s f C ->
  Instrs_ok2 s C es (t1s :-> t2s) ->
  not_lf_br es.
Proof.
  move => s f C es t1s t2s Hframe Hadmin vcs l es' Hcontra.
  eapply s_typing_lf_br' in Hadmin as Hes; eauto.
  clear Hframe Hadmin.
  instantiate (1:= l) in Hes.

  move: es es' Hes Hcontra.
  induction vcs; move=> es es' Hes Hcontra.
  - simpl in Hcontra; subst.
    inversion Hes; subst.
    by specialize (H1 erefl).
  - destruct es => //=.
    inversion Hes as [ | ? ? HP HP1]; subst.
    specialize (IHvcs es es' HP1).
    eapply IHvcs => //=.
    by inversion Hcontra.
Qed.

Lemma s_typing_not_lf_br : forall s f C rt es t1s t2s,
  Frame_ok s f C ->
  Instrs_ok2 s (prepend_return C rt) es (t1s :-> t2s) ->
  not_lf_br es.
Proof.
  move => s f C rt es t1s t2s Hframe Hadmin vcs l es' Hcontra.
  eapply s_typing_lf_br in Hadmin as Hes; eauto.
  clear Hframe Hadmin.
  instantiate (1:= l) in Hes.

  move: es es' Hes Hcontra.
  induction vcs; move=> es es' Hes Hcontra.
  - simpl in Hcontra; subst.
    inversion Hes; subst.
    by specialize (H1 erefl).
  - destruct es => //=.
    inversion Hes as [ | ? ? HP HP1]; subst.
    specialize (IHvcs es es' HP1).
    eapply IHvcs => //=.
    by inversion Hcontra.
Qed.

Lemma s_typing_not_lf_return : forall s f C es t1s t2s,
  Frame_ok s f C ->
  Instrs_ok2 s C es (t1s :-> t2s) ->
  not_lf_return es.
Proof.
  move => s f C es t1s t2s Hframe Hadmin vcs es' Hcontra.
  eapply s_typing_lf_return in Hadmin as Hes; eauto.
  clear Hframe Hadmin.

  move: es es' Hes Hcontra.
  induction vcs; move=> es es' Hes Hcontra.
  - simpl in Hcontra; subst.
    inversion Hes; subst.
    by specialize (H1 erefl).
  - destruct es => //=.
    inversion Hes as [ | ? ? HP HP1]; subst.
    specialize (IHvcs es es' HP1).
    eapply IHvcs => //=.
    by inversion Hcontra.
Qed.

Lemma size_eq1_cat: forall A (l1 l2 l1' l2': list A),
  |l1'| = |l2'| ->
  l1' ++ l1 = l2' ++ l2 ->
  l1' = l2' /\ l1 = l2.
Proof.
  move=> A l1 l2 l1' l2' Hsize Hcat.

  apply sizeN_inj in Hsize.
  have Htake: take (size l1') (l1' ++ l1) = take (size l1') (l2' ++ l2).
  { by rewrite Hcat. }

  rewrite take_size_cat in Htake; eauto.
  rewrite Hsize take_size_cat in Htake; eauto.
  split; auto.

  have Hdrop: drop (size l1') (l1' ++ l1) = drop (size l1') (l2' ++ l2).
  { by rewrite Hcat. }
  
  rewrite drop_size_cat // in Hdrop.
  by rewrite Hsize drop_size_cat // in Hdrop.
Qed.

Lemma br_reduce_extract_vs : forall s C ts2 ts es,
  (* TODO: This first premise is equal to br_reduce with l applied to it
           We could make br_reduce parameterised by l *)
  (exists vcs es',
    es = map admininstr_val vcs ++ [admininstr_BR (mk_uN 0)] ++ es') -> 
  Instrs_ok2 s C es ([] :-> ts2) -> 
  lookup_total (LABELS C) 0 = ts ->
  (exists vcs1 vcs2 es',
    es = map admininstr_val vcs1 ++ map admininstr_val vcs2
      ++ [admininstr_BR (mk_uN 0)] ++ es' /\
    |vcs2| = |ts|).
Proof.
  move => s C ts2 ts es Hbr Hadmin Hlookup.
  move: Hbr => [vcs [es' Hbr]].
  rewrite Hbr catA in Hadmin.

  move/Admin_instrs_ok_cat: Hadmin => [ts' [ts1' [ts2' [ts3 [Ets1 [Ets2 [Hadmin1 Hadmin2]]]]]]].
  symmetry in Ets1. move/cat_nil: Ets1 => [Ets' Ets1'].
  rewrite ?{}Ets' ?{}Ets1' /= in Ets2 Hadmin1. rewrite -{}Ets2 in Hadmin2.
  move => {ts' ts1' ts2'}.

  move/Admin_instrs_ok_cat: Hadmin1 => [ts' [ts1' [ts2' [ts3' [Ets1 [Ets2 [Hadmin1 Hadmin1']]]]]]].
  symmetry in Ets1. move/cat_nil: Ets1 => [Ets' Ets1'].
  rewrite ?{}Ets' ?{}Ets1' /= in Ets2 Hadmin1. rewrite -{}Ets2 in Hadmin1'.
  move => {ts' ts1' ts2'}.

  move: Hadmin1 Hadmin1' Hadmin2 => Hadmin1 Hadmin2 Hadmin3.

  invert_ais_typing.
  resolve_all_pt.
  eapply instrtype_sub_iff_resulttype_sub in Hsub.
  eapply Vals_ok_non_bot in HValsok as Hnonbot.
  eapply resulttype_sub_non_bot in Hsub; eauto.
  subst t.
  unfold_instrtype_sub Hsub0; subst.
  eapply (resulttype_sub_app _ _ _ _ Hsub) in Hsub1.
  eapply resulttype_sub_non_bot in Hsub1; eauto.
  eapply size_eq1_cat in Hsub1 as [Hts H2].
  2: { by inversion Hsub; eq_to_prop. }
  subst ts_sub ts11_sub.
  rewrite catA in HValsok.
  eapply Forall2_seq_size in HValsok.
  apply sizeN_inj in HValsok.
  rewrite size_cat in HValsok.
  assert (|(ts ++ extr)| <= |vcs|)%BN.
  {
    apply cvt_ssrnat_to_N_le.
    rewrite -HValsok.
    eapply leq_addr.
  }

  exists (take (size (ts ++ extr)) vcs), (drop (size (ts ++ extr)) vcs), es'.
  split.
  - by rewrite !catA -map_cat cat_take_drop.
  - f_equal.
    rewrite size_drop.
    
    rewrite -HValsok.
    rewrite add_sub' /=.
    by destruct (lookup_total (LABELS C) 0).
Qed.

Lemma return_reduce_extract_vs : forall s C ts2 t es,
  (* TODO: This first premise is equal to return_reduce *)
  (exists vcs es',
    es = map admininstr_val vcs ++ [admininstr_RETURN] ++ es') -> 
  Instrs_ok2 s C es ([] :-> ts2) -> 
  context_RETURN C = Some t ->
  (exists vcs1 vcs2 es',
    es = map admininstr_val vcs1 ++ map admininstr_val vcs2 ++ [admininstr_RETURN] ++ es' /\
    size vcs2 = size t).
Proof.
  move => s C ts2 t es Hret Hadmin Hlookup.
  move: Hret => [vcs [es' Hret]].
  rewrite Hret catA in Hadmin.

  move/Admin_instrs_ok_cat: Hadmin => [ts' [ts1' [ts2' [ts3 [Ets1 [Ets2 [Hadmin1 Hadmin2]]]]]]].
  symmetry in Ets1. move/cat_nil: Ets1 => [Ets' Ets1'].
  rewrite ?{}Ets' ?{}Ets1' /= in Ets2 Hadmin1. rewrite -{}Ets2 in Hadmin2.
  move => {ts' ts1' ts2'}.

  move/Admin_instrs_ok_cat: Hadmin1 => [ts' [ts1' [ts2' [ts3' [Ets1 [Ets2 [Hadmin1 Hadmin1']]]]]]].
  symmetry in Ets1. move/cat_nil: Ets1 => [Ets' Ets1'].
  rewrite ?{}Ets' ?{}Ets1' /= in Ets2 Hadmin1. rewrite -{}Ets2 in Hadmin1'.
  move => {ts' ts1' ts2'}.

  move: Hadmin1 Hadmin1' Hadmin2 => Hadmin1 Hadmin2 Hadmin3.

  invert_ais_typing.
  resolve_all_pt.
  eapply instrtype_sub_iff_resulttype_sub in Hsub.
  eapply Vals_ok_non_bot in HValsok as Hnonbot.
  eapply resulttype_sub_non_bot in Hsub; eauto.
  subst t0.
  unfold_instrtype_sub Hsub0; subst.
  eapply (resulttype_sub_app _ _ _ _ Hsub) in Hsub1.
  eapply resulttype_sub_non_bot in Hsub1; eauto.
  eapply size_eq1_cat in Hsub1 as [Hts H2].
  2: { by inversion Hsub; eq_to_prop. }
  subst ts_sub ts11_sub.
  rewrite catA in HValsok.
  eapply Forall2_seq_size in HValsok.
  apply sizeN_inj in HValsok.
  rewrite size_cat in HValsok.
  assert (|(ts ++ extr)| <= |vcs|)%BN.
  {
    apply cvt_ssrnat_to_N_le.
    rewrite -HValsok.
    eapply leq_addr.
  }

  exists (take (size (ts ++ extr)) vcs), (drop (size (ts ++ extr)) vcs), es'.
  split.
  - by rewrite !catA -map_cat cat_take_drop.
  - rewrite size_drop.
    rewrite -HValsok.
    rewrite add_sub' /=.
    rewrite Hlookup in H1.
    by inversion H1.
Qed.

Lemma lookup_types: forall s f C loc lab ret idx,
  Moduleinst_ok s (frame_MODULE f) C ->
  lookup_total (context_TYPES (upd_local_label_return C loc lab ret)) idx =
  lookup_total (TYPES (frame_MODULE f)) idx.
Proof.
  move => s f C loc lab ret idx HMinst.
  inversion HMinst.
  by rewrite /=.
Qed.

Lemma funcs_size: forall s f C loc lab ret,
  Moduleinst_ok s (frame_MODULE f) C ->
  |context_FUNCS (upd_local_label_return C loc lab ret)| = |FUNCS (frame_MODULE f)|.
Proof.
  move => s f C loc lab ret HMinst.
  inversion HMinst; eq_to_prop.
  by rewrite /=.
Qed.


Lemma admininstr_CONST_eq_arg: forall t i1 i2,
	admininstr_CONST t i1 = admininstr_CONST t i2 ->
	(i1 = i2).
Proof.
	move => t i1 i2 Hargeq.
  inversion Hargeq; eauto.
Qed.

Lemma typeof_non_bot: forall v,
  typeof v <> BOT.
Proof.
  destruct v; rewrite /typeof; try discriminate.
    - by destruct v_numtype.
    - by destruct v_vectype.
    - by destruct v_reftype.
Qed.

Lemma typeof_vals_non_bot: forall vs ts,
  map typeof vs = ts ->
  Forall (fun t => t <> BOT) ts.
Proof.
  move => vs ts.
  move : ts.
  induction vs.
  - move => ts Hts. by subst; auto.
  - move => ts Hts.
    simpl in Hts.
    rewrite -Hts.
    econstructor.
    + by eapply typeof_non_bot.
    + by eapply IHvs.
Qed.

Lemma unop_not_none: forall nt u n1,
    wf_num_ nt n1 ->
    wf_unop_ nt u ->
    fun_unop_ nt u n1 <> None.
Proof.
  move=> nt u n1 HWf HWfUnop HNeq.
  inversion HWf; inversion HWfUnop; eq_to_prop; subst; try discriminate.
  - destruct v_Inn; destruct v_Inn0; destruct var_x0; try discriminate.
  - destruct v_Fnn; destruct v_Inn; discriminate.
  - destruct v_Fnn; destruct v_Inn; discriminate.
  - destruct v_Fnn; destruct v_Fnn0; destruct var_x0; discriminate.
Qed.

(* ---- helpers about 2^N, wf_uN and signed_ ---- *)

Lemma two_pow_pos : forall (v_N : N), (0 < (2%num ^ v_N)%BN)%BN.
Proof. move => v_N. apply/N.neq_0_lt_0. by apply: N.pow_nonzero. Qed.

Lemma Zsub1_toN : forall (m : N), ((((m : Z) - (1%num : Z))%Z : N) = (m - 1)%BN).
Proof.
  case => [ |p] //.
  by rewrite -Znat.N2Z.inj_sub ?Znat.N2Z.id //; apply/N.neq_0_le_1.
Qed.

Lemma wf_uN_lt : forall v_N i, wf_uN v_N (mk_uN i) -> (i < (2%num ^ v_N)%BN)%BN.
Proof.
  move => v_N i H.
  inversion H; subst.
  match goal with | [ Hb : is_true (_ && _) |- _ ] => move/andP: Hb => [_ Hle] end.
  move/N.leb_spec0 in Hle.
  rewrite Zsub1_toN in Hle.
  have Hp := two_pow_pos v_N.
  lia.
Qed.

Lemma two_pow_succ : forall m : N, m <> 0%num ->
  ((2%num ^ m)%BN = (2 * (2%num ^ (m - 1)%BN))%BN).
Proof.
  move => m Hm.
  rewrite -N.pow_succ_r'.
  f_equal. lia.
Qed.

Lemma signed_total : forall (v_N : res_N) (i : N),
  (i < (2%num ^ v_N)%BN)%BN ->
  exists z, fun_signed_ v_N i z /\
            ((0 - ((2%num ^ (v_N - 1)%BN)%BN : Z))%Z <= z)%Z /\
            (z < ((2%num ^ (v_N - 1)%BN)%BN : Z))%Z.
Proof.
  move => v_N i Hlt.
  have Hp := two_pow_pos v_N.
  have Hp1 := two_pow_pos (v_N - 1)%BN.
  case E: ((i <? (2%num ^ (((v_N : Z) - (1%num : Z))%Z : N))%BN)%BN).
  - exists (i : Z).
    rewrite Zsub1_toN in E.
    move/N.ltb_spec0 in E.
    split; first by apply: fun_signed__case_0; rewrite Zsub1_toN; apply/N.ltb_spec0.
    split; lia.
  - exists ((i : Z) - ((2%num ^ v_N)%BN : Z))%Z.
    rewrite Zsub1_toN in E.
    move/N.ltb_spec0 in E.
    have Hge : ((2%num ^ (v_N - 1)%BN)%BN <= i)%BN by lia.
    have HN0 : v_N <> 0%num.
    { move => H0. rewrite H0 in Hlt Hge. simpl in Hlt, Hge. lia. }
    have Hd := two_pow_succ v_N HN0.
    split.
    + apply: fun_signed__case_1. apply/andP; split.
      * by apply/N.leb_spec0; rewrite Zsub1_toN.
      * by apply/N.ltb_spec0.
    + split; lia.
Qed.

Lemma invsigned_total: forall (v_N : res_N) z,
    ((0 - ((2%num ^ (v_N - 1)%BN)%BN : Z))%Z <= z)%Z ->
    (z < ((2%num ^ (v_N - 1)%BN)%BN : Z))%Z ->
    (exists ret, fun_inv_signed_ v_N z ret).
Proof.
  move => v_N z Hlo Hhi.
  case Ez: (0 <=? z)%Z.
  - move/Z.leb_spec0 in Ez.
    exists (z : N). apply: fun_inv_signed__case_0.
    rewrite Zsub1_toN.
    apply/andP; split; [by apply/Z.leb_spec0; lia | by apply/Z.ltb_spec0; lia].
  - apply Z.leb_gt in Ez.
    exists ((z + ((2%num ^ v_N)%BN : Z))%Z : N).
    apply: fun_inv_signed__case_1.
    rewrite Zsub1_toN.
    apply/andP; split; [by apply/Z.leb_spec0; lia | by apply/Z.ltb_spec0; lia].
Qed.

(* ---- bounds on integer truncating division ---- *)

Lemma Zquot_abs_le : forall a b p : Z, b <> 0%Z -> (0 <= p)%Z ->
  (Z.abs a <= p)%Z -> (Z.abs (Z.quot a b) <= p)%Z.
Proof.
  move => a b p Hb Hp Ha.
  rewrite -(Z.quot_abs a b Hb).
  have H1 : (1 <= Z.abs b)%Z by lia.
  have Hc := Z.quot_le_compat_l (Z.abs a) 1 (Z.abs b) (Z.abs_nonneg a) (conj Z.lt_0_1 H1).
  rewrite Z.quot_1_r in Hc. lia.
Qed.

Lemma Zquot_ge_inv : forall a b p : Z, b <> 0%Z -> (1 <= p)%Z ->
  (Z.abs a <= p)%Z -> (p <= Z.quot a b)%Z ->
  (b = 1%Z /\ a = p) \/ (b = (-1)%Z /\ a = (- p)%Z).
Proof.
  move => a b p Hb Hp Ha Hge.
  have Hcase : b = 1%Z \/ b = (-1)%Z \/ (2 <= Z.abs b)%Z by lia.
  case: Hcase => [Hb1 | [Hbm1 | Hb2]].
  - subst b. rewrite Z.quot_1_r in Hge. left. by split; lia.
  - subst b. right; split; first by [].
    have Hop : (Z.quot a (-1) = - (Z.quot a 1))%Z.
    { by rewrite -Z.quot_opp_r. }
    rewrite Hop Z.quot_1_r in Hge. lia.
  - exfalso.
    have Hb0 : (0 < Z.abs b)%Z by lia.
    have H1 := Z.quot_abs a b Hb.
    have H2 := Z.quot_le_compat_l (Z.abs a) 2 (Z.abs b) (Z.abs_nonneg a) (conj (ltac:(lia) : (0 < 2)%Z) Hb2).
    have H3 := Z.quot_le_mono (Z.abs a) p 2 (ltac:(lia) : (0 < 2)%Z) Ha.
    have H4 : (Z.quot p 2 < p)%Z by apply: Z.quot_lt; lia.
    lia.
Qed.

Lemma wf_uN_lt' : forall v_N (u : uN), wf_uN v_N u -> ((u :> N) < (2%num ^ v_N)%BN)%BN.
Proof. move => v_N [i] H. by apply: wf_uN_lt. Qed.

Lemma signed_nonzero : forall v_N i z, fun_signed_ v_N i z -> i <> 0%num -> z <> 0%Z.
Proof.
  move => v_N i z H Hi.
  inversion H; subst; first by lia.
  match goal with | [ Hb : is_true (_ && _) |- _ ] => move/andP: Hb => [_ Hlt] end.
  move/N.ltb_spec0 in Hlt. lia.
Qed.

Lemma idiv_total : forall (v_N : res_N) (v_sx : sx) (i1 i2 : uN),
  wf_uN v_N i1 -> wf_uN v_N i2 ->
  exists r, fun_idiv_ v_N v_sx i1 i2 r.
Proof.
  move => v_N v_sx i1 i2 Hw1 Hw2.
  case: v_sx; first by (eexists; apply: fun_idiv__case_1).
  destruct i2 as [n2].
  destruct n2 as [ |p2]; first by (eexists; apply: fun_idiv__case_2).
  have Hl1 := wf_uN_lt' _ _ Hw1.
  have Hl2 := wf_uN_lt' _ _ Hw2.
  destruct (signed_total v_N (i1 :> N) Hl1) as [z1 [Hs1 [Hlo1 Hhi1]]].
  destruct (signed_total v_N (mk_uN (N.pos p2) :> N) Hl2) as [z2 [Hs2 [Hlo2 Hhi2]]].
  have Hz2 : z2 <> 0%Z by apply: (signed_nonzero _ _ _ Hs2).
  set P := (2%num ^ (v_N - 1)%BN)%BN.
  have HPp := two_pow_pos (v_N - 1)%BN.
  rewrite -/P in HPp Hlo1 Hhi1 Hlo2 Hhi2.
  have HP1 : (1 <= (P : Z))%Z by lia.
  have Ha1 : (Z.abs z1 <= (P : Z))%Z by lia.
  case Hq: ((Z.quot z1 z2) <? (P : Z))%Z.
  - move/Z.ltb_spec0 in Hq.
    have Hab := Zquot_abs_le z1 z2 (P : Z) Hz2 (ltac:(lia)) Ha1.
    have [r Hr] : exists ret, fun_inv_signed_ v_N (truncz (inject_Z z1 / inject_Z z2)%Q) ret.
    { rewrite (truncz_quot _ _ Hz2). apply: invsigned_total; rewrite -/P; lia. }
    exists (Some (mk_uN r)).
    by eapply fun_idiv__case_4; eauto.
  - move/Z.ltb_ge in Hq.
    have Hinv := Zquot_ge_inv z1 z2 (P : Z) Hz2 HP1 Ha1 Hq.
    exists None.
    eapply fun_idiv__case_3; eauto.
    rewrite Zsub1_toN -/P.
    apply (proj2 (Qeq_bool_iff _ _)).
    case: Hinv => [[Hb Ha] | [Hb Ha]]; subst;
      by rewrite /Qeq /Qdiv /Qmult /Qinv /inject_Z /=; lia.
Qed.

Lemma irem_total : forall (v_N : res_N) (v_sx : sx) (i1 i2 : uN),
  wf_uN v_N i1 -> wf_uN v_N i2 ->
  exists r, fun_irem_ v_N v_sx i1 i2 r.
Proof.
  move => v_N v_sx i1 i2 Hw1 Hw2.
  case: v_sx; first by (eexists; apply: fun_irem__case_1).
  destruct i2 as [n2].
  destruct n2 as [ |p2]; first by (eexists; apply: fun_irem__case_2).
  have Hl1 := wf_uN_lt' _ _ Hw1.
  have Hl2 := wf_uN_lt' _ _ Hw2.
  destruct (signed_total v_N (i1 :> N) Hl1) as [z1 [Hs1 [Hlo1 Hhi1]]].
  destruct (signed_total v_N (mk_uN (N.pos p2) :> N) Hl2) as [z2 [Hs2 [Hlo2 Hhi2]]].
  have Hz2 : z2 <> 0%Z by apply: (signed_nonzero _ _ _ Hs2).
  set P := (2%num ^ (v_N - 1)%BN)%BN.
  have HPp := two_pow_pos (v_N - 1)%BN.
  rewrite -/P in HPp Hlo1 Hhi1 Hlo2 Hhi2.
  have Hrem : (z1 - (z2 * Z.quot z1 z2)%Z)%Z = Z.rem z1 z2.
  { have Hqr := Z.quot_rem' z1 z2. lia. }
  have Hbnd := Z.rem_bound_abs z1 z2 Hz2.
  have [r Hr] : exists ret,
      fun_inv_signed_ v_N (z1 - (z2 * (truncz (inject_Z z1 / inject_Z z2)%Q))%Z)%Z ret.
  { rewrite (truncz_quot _ _ Hz2) Hrem. apply: invsigned_total; rewrite -/P; lia. }
  exists (Some (mk_uN r)).
  eapply fun_irem__case_3; eauto.
  by apply/andP; split; apply/eqP.
Qed.

Lemma ilt_total : forall v_N v_sx i1 i2, wf_uN v_N i1 -> wf_uN v_N i2 ->
  exists r, fun_ilt_ v_N v_sx i1 i2 r.
Proof.
  move => v_N v_sx i1 i2 Hw1 Hw2.
  case: v_sx; first by (eexists; apply: fun_ilt__case_0).
  have [z1 [Hs1 _]] := signed_total v_N (i1 :> N) (wf_uN_lt' _ _ Hw1).
  have [z2 [Hs2 _]] := signed_total v_N (i2 :> N) (wf_uN_lt' _ _ Hw2).
  by eexists; eapply fun_ilt__case_1; eauto.
Qed.

Lemma igt_total : forall v_N v_sx i1 i2, wf_uN v_N i1 -> wf_uN v_N i2 ->
  exists r, fun_igt_ v_N v_sx i1 i2 r.
Proof.
  move => v_N v_sx i1 i2 Hw1 Hw2.
  case: v_sx; first by (eexists; apply: fun_igt__case_0).
  have [z1 [Hs1 _]] := signed_total v_N (i1 :> N) (wf_uN_lt' _ _ Hw1).
  have [z2 [Hs2 _]] := signed_total v_N (i2 :> N) (wf_uN_lt' _ _ Hw2).
  by eexists; eapply fun_igt__case_1; eauto.
Qed.

Lemma ile_total : forall v_N v_sx i1 i2, wf_uN v_N i1 -> wf_uN v_N i2 ->
  exists r, fun_ile_ v_N v_sx i1 i2 r.
Proof.
  move => v_N v_sx i1 i2 Hw1 Hw2.
  case: v_sx; first by (eexists; apply: fun_ile__case_0).
  have [z1 [Hs1 _]] := signed_total v_N (i1 :> N) (wf_uN_lt' _ _ Hw1).
  have [z2 [Hs2 _]] := signed_total v_N (i2 :> N) (wf_uN_lt' _ _ Hw2).
  by eexists; eapply fun_ile__case_1; eauto.
Qed.

Lemma ige_total : forall v_N v_sx i1 i2, wf_uN v_N i1 -> wf_uN v_N i2 ->
  exists r, fun_ige_ v_N v_sx i1 i2 r.
Proof.
  move => v_N v_sx i1 i2 Hw1 Hw2.
  case: v_sx; first by (eexists; apply: fun_ige__case_0).
  have [z1 [Hs1 _]] := signed_total v_N (i1 :> N) (wf_uN_lt' _ _ Hw1).
  have [z2 [Hs2 _]] := signed_total v_N (i2 :> N) (wf_uN_lt' _ _ Hw2).
  by eexists; eapply fun_ige__case_1; eauto.
Qed.

Ltac num_shapes Hb Hn1 Hn2 :=
  inversion Hb; inversion Hn1; inversion Hn2; eq_to_prop; subst;
  repeat match goal with
  | [ i : Inn |- _ ] => destruct i
  | [ i : Fnn |- _ ] => destruct i
  end;
  try discriminate.

Lemma binop_total: forall nt b n1 n2,
    wf_num_ nt n1 -> wf_num_ nt n2 -> wf_binop_ nt b ->
    (exists lst, fun_binop_ nt b n1 n2 lst).
Proof.
  move => nt b n1 n2 Hn1 Hn2 Hb.
  num_shapes Hb Hn1 Hn2.
  all: match goal with | [ x : binop_Inn |- _ ] => destruct x | [ x : binop_Fnn |- _ ] => destruct x end.
  all: try (by (eexists; econstructor)).
  all: match goal with
  | [ |- exists _, fun_binop_ _ (mk_binop__0 _ (DIV ?sx)) (mk_num__0 _ ?a) (mk_num__0 _ ?b) _ ] =>
      have [r Hr] := idiv_total _ sx a b ltac:(eassumption) ltac:(eassumption);
      eexists; econstructor; exact: Hr
  | [ |- exists _, fun_binop_ _ (mk_binop__0 _ (REM ?sx)) (mk_num__0 _ ?a) (mk_num__0 _ ?b) _ ] =>
      have [r Hr] := irem_total _ sx a b ltac:(eassumption) ltac:(eassumption);
      eexists; econstructor; exact: Hr
  end.
Qed.

Lemma relop_total: forall nt r n1 n2,
    wf_num_ nt n1 -> wf_num_ nt n2 -> wf_relop_ nt r ->
    (exists c, fun_relop_ nt r n1 n2 c).
Proof.
  move => nt r n1 n2 Hn1 Hn2 Hr.
  num_shapes Hr Hn1 Hn2.
  all: match goal with | [ x : relop_Inn |- _ ] => destruct x | [ x : relop_Fnn |- _ ] => destruct x end.
  all: try (by (eexists; econstructor)).
  all: match goal with
  | [ |- exists _, fun_relop_ _ (mk_relop__0 _ (LT ?sx)) (mk_num__0 _ ?a) (mk_num__0 _ ?b) _ ] =>
      have [c Hc] := ilt_total _ sx a b ltac:(eassumption) ltac:(eassumption);
      eexists; econstructor; exact: Hc
  | [ |- exists _, fun_relop_ _ (mk_relop__0 _ (GT ?sx)) (mk_num__0 _ ?a) (mk_num__0 _ ?b) _ ] =>
      have [c Hc] := igt_total _ sx a b ltac:(eassumption) ltac:(eassumption);
      eexists; econstructor; exact: Hc
  | [ |- exists _, fun_relop_ _ (mk_relop__0 _ (LE ?sx)) (mk_num__0 _ ?a) (mk_num__0 _ ?b) _ ] =>
      have [c Hc] := ile_total _ sx a b ltac:(eassumption) ltac:(eassumption);
      eexists; econstructor; exact: Hc
  | [ |- exists _, fun_relop_ _ (mk_relop__0 _ (GE ?sx)) (mk_num__0 _ ?a) (mk_num__0 _ ?b) _ ] =>
      have [c Hc] := ige_total _ sx a b ltac:(eassumption) ltac:(eassumption);
      eexists; econstructor; exact: Hc
  end.
Qed.

Lemma cvtop_total: forall nt1 nt2 cvt c1,
    wf_num_ nt1 c1 -> wf_cvtop__ nt1 nt2 cvt ->
    (exists c2, fun_cvtop__ nt1 nt2 cvt c1 c2).
Proof.
  move => nt1 nt2 cvt c1 Hc1 Hcvt.
  inversion Hcvt; inversion Hc1; eq_to_prop; subst.
  all: repeat match goal with
  | [ H : wf_cvtop__Inn_1_Inn_2 _ _ _ |- _ ] => inversion H; subst; clear H
  | [ H : wf_cvtop__Inn_1_Fnn_2 _ _ _ |- _ ] => inversion H; subst; clear H
  | [ H : wf_cvtop__Fnn_1_Inn_2 _ _ _ |- _ ] => inversion H; subst; clear H
  | [ H : wf_cvtop__Fnn_1_Fnn_2 _ _ _ |- _ ] => inversion H; subst; clear H
  end.
  all: repeat match goal with
  | [ i : Inn |- _ ] => destruct i
  | [ i : Fnn |- _ ] => destruct i
  end.
  all: try discriminate.
  all: try (by (eexists; econstructor)).
Qed.

Lemma binop_before : forall nt b n1 n2,
    wf_num_ nt n1 -> wf_num_ nt n2 -> wf_binop_ nt b ->
    fun_binop__before_fun_binop__case_38 nt b n1 n2.
Proof.
  move => nt b n1 n2 Hn1 Hn2 Hb.
  num_shapes Hb Hn1 Hn2.
  all: match goal with | [ x : binop_Inn |- _ ] => destruct x | [ x : binop_Fnn |- _ ] => destruct x end.
  all: simpl.
  all: econstructor.
  all: exact: None.
Qed.

Lemma binop_not_none: forall nt b n1 n2 lst,
    wf_num_ nt n1 ->
    wf_num_ nt n2 ->
    wf_binop_ nt b ->
    fun_binop_ nt b n1 n2 lst ->
    lst <> None.
Proof.
  move => nt b n1 n2 lst Hn1 Hn2 Hb Hf.
  inversion Hf; subst; try discriminate.
  exfalso. match goal with | [ H : ~ _ |- _ ] => apply H end.
  by apply: binop_before.
Qed.

Lemma relop_before : forall nt r n1 n2,
    wf_num_ nt n1 -> wf_num_ nt n2 -> wf_relop_ nt r ->
    fun_relop__before_fun_relop__case_24 nt r n1 n2.
Proof.
  move => nt r n1 n2 Hn1 Hn2 Hr.
  num_shapes Hr Hn1 Hn2.
  all: match goal with | [ x : relop_Inn |- _ ] => destruct x | [ x : relop_Fnn |- _ ] => destruct x end.
  all: simpl.
  all: econstructor.
  all: try exact: None.
  all: try exact: (mk_uN 0%num).
Qed.

Lemma relop_not_none: forall nt r n1 n2 c,
    wf_num_ nt n1 ->
    wf_num_ nt n2 ->
    wf_relop_ nt r ->
    fun_relop_ nt r n1 n2 c ->
    c <> None.
Proof.
  move => nt r n1 n2 c Hn1 Hn2 Hr Hf.
  inversion Hf; subst; try discriminate.
  exfalso. match goal with | [ H : ~ _ |- _ ] => apply H end.
  by apply: relop_before.
Qed.

Lemma cvtop_before : forall nt1 nt2 cvt c1,
    wf_num_ nt1 c1 -> wf_cvtop__ nt1 nt2 cvt ->
    fun_cvtop___before_fun_cvtop___case_36 nt1 nt2 cvt c1.
Proof.
  move => nt1 nt2 cvt c1 Hc1 Hcvt.
  inversion Hcvt; inversion Hc1; eq_to_prop; subst.
  all: repeat match goal with
  | [ H : wf_cvtop__Inn_1_Inn_2 _ _ _ |- _ ] => inversion H; subst; clear H
  | [ H : wf_cvtop__Inn_1_Fnn_2 _ _ _ |- _ ] => inversion H; subst; clear H
  | [ H : wf_cvtop__Fnn_1_Inn_2 _ _ _ |- _ ] => inversion H; subst; clear H
  | [ H : wf_cvtop__Fnn_1_Fnn_2 _ _ _ |- _ ] => inversion H; subst; clear H
  end.
  all: repeat match goal with
  | [ i : Inn |- _ ] => destruct i
  | [ i : Fnn |- _ ] => destruct i
  end.
  all: try discriminate.
  all: simpl.
  all: econstructor.
  all: try exact: None.
  all: try exact: (mk_uN 0%num).
  all: by [].
Qed.

Lemma cvtop_not_none: forall nt1 nt2 cvt c1 c2,
    wf_num_ nt1 c1 ->
    wf_cvtop__ nt1 nt2 cvt ->
    fun_cvtop__ nt1 nt2 cvt c1 c2 ->
    c2 <> None.
Proof.
  move => nt1 nt2 cvt c1 c2 Hc1 Hcvt Hf.
  inversion Hf; subst; try discriminate.
  exfalso. match goal with | [ H : ~ _ |- _ ] => apply H end.
  by apply: cvtop_before.
Qed.

Lemma testop_not_none: forall nt t n1,
    wf_num_ nt n1 ->
    wf_testop_ nt t ->
    fun_testop_ nt t n1 <> None.
Proof.
  move => nt t n1 Hn1 Ht.
  inversion Ht; inversion Hn1; eq_to_prop; subst.
  all: repeat match goal with
  | [ i : Inn |- _ ] => destruct i
  | [ i : Fnn |- _ ] => destruct i
  end.
  all: try discriminate.
  all: match goal with | [ x : testop_Inn |- _ ] => destruct x end.
  all: by [].
Qed.


Lemma invsigned_total_32m1 : exists ret, fun_inv_signed_ 32 (0 - 1)%Z ret.
Proof.
  apply: invsigned_total; by vm_compute.
Qed.

Lemma Forall_list_slice : forall {T : Type} (P : T -> Prop) (l : seq T) (i j : N),
  List.Forall P l -> List.Forall P (list_slice l i j).
Proof.
  move => T P l.
  induction l; move => i j H; first by [].
  inversion H; subst.
  destruct i; destruct j; simpl; try by [].
  - by econstructor; eauto.
  - by apply: IHl.
Qed.

Lemma mem_bytes_wf : forall (ms : seq meminst) (k : N),
  List.Forall wf_meminst ms -> List.Forall wf_byte (BYTES (ms [| k |])).
Proof.
  move => ms k Hall.
  case E: ((k <? (|ms|))%BN).
  - move/N.ltb_spec0 in E.
    have H : wf_meminst (ms [|k|]) by (eapply Forall_size; eauto).
    by inversion H.
  - move/N.ltb_ge in E.
    rewrite /lookup_total nth_default; first by [].
    apply/leP. lia.
Qed.

Lemma wf_config_mem_bytes : forall s f ais (x : memidx),
  wf_config (mk_config (mk_state s f) ais) ->
  List.Forall wf_byte (BYTES (fun_mem (mk_state s f) x)).
Proof.
  move => s f ais x H.
  inversion H; subst.
  match goal with | [ Hs : wf_state _ |- _ ] => inversion Hs; subst end.
  match goal with | [ Hs : wf_store _ |- _ ] => inversion Hs; subst end.
  by apply: mem_bytes_wf.
Qed.


Lemma mk_uN_eta : forall (u : uN), mk_uN ((u :> N)) = u.
Proof. by case. Qed.

Lemma packnum_not_none : forall (lt : lanetype) (c : num_),
  wf_num_ (unpack lt) c -> (packnum_ lt c) != None.
Proof.
  move => lt c Hwf.
  destruct lt; simpl; try by [].
  all: inversion Hwf; subst; eq_to_prop; subst.
  all: try (by destruct v_Fnn).
  all: by destruct v_Inn.
Qed.

Lemma lanes_nth_wf : forall (lt : lanetype) (v_N : N) (c : vec_) (k : N),
  wf_shape (X lt (mk_dim v_N)) ->
  wf_uN 128 c ->
  (k < v_N)%BN ->
  wf_lane_ lt ((lanes_ (X lt (mk_dim v_N)) c) [| k |]).
Proof.
  move => lt v_N c k Hsh Hc Hk.
  have Hall := lanes__is_wf (X lt (mk_dim v_N)) c _ Hsh Hc (eqxx _).
  have H := Forall_size _ _ Hall k.
  rewrite lanes_len in H. by apply: H.
Qed.

Lemma add_sub_parens: forall n1 (n2 : N) n3,
    (n3 <= n2)%Z ->
    (n1 + (n2 - n3)%Z)%BN = ((n1 + n2)%BN - n3)%Z.
Proof.
  intros. lia.
Qed.

Lemma call_indirect_progress: forall s f v_i x y,
  proj_num__0 v_i != None ->
  exists es, Step (mk_config (mk_state s f) ([:: admininstr_CONST I32 v_i] ++ [:: admininstr_CALL_INDIRECT x y]))
    (mk_config (mk_state s f) es).
Proof.
  move=> s f v_i x y HNone.
  case E3: (proj_uN_0 (!(proj_num__0 v_i)) <? | (REFS (fun_table (mk_state s f) x))|)%BN.
  case E1: (lookup_total (REFS (fun_table (mk_state s f) x)) (proj_uN_0 (!(proj_num__0 v_i)))) => [ | a | ].
  { (* Case when a is REF_NULL *)
    exists [admininstr_TRAP].
    eapply read.
    eapply call_indirect_trap.
    move => HContra.
    remember (admininstr_CONST I32 v_i) as instr_i.
    inversion HContra.
    rewrite Heqinstr_i in H0.
    eapply admininstr_CONST_eq_arg in H0; subst.
    eq_to_prop.
    rewrite E1 in H5; discriminate.
    Unshelve.
    exact Inhabited__uN.
    exact Inhabited__uN.
    exact Inhabited__ref.
  }
  case E4: (a <? |(fun_funcinst (mk_state s f))|)%BN.
  case E2: (fun_type (mk_state s f) y == funcinst_TYPE (lookup_total (fun_funcinst (mk_state s f)) a)).

  { (* True case *)
    exists [CALL_ADDR a].
    eapply read.
    eapply call_indirect_call; eauto.
    - eq_to_prop; eauto.
      Unshelve.
      exact Inhabited_funcinst.
  }
  (* False cases *)
  all: exists [admininstr_TRAP].
  all: apply read; apply call_indirect_trap.
  all: move=> HContra.
  all: inversion HContra; eq_to_prop; subst.
  {
    rewrite E1 in H5.
    injection H5 as ?; subst.
    move/eqP in E2.
    contradiction.
  }
  {
    rewrite E1 in H5.
    injection H5 as ?; subst.
    rewrite H6 in E4.
    discriminate.
  }
  {
    rewrite E1 in H5.
    inversion H5.
  }
  {
    rewrite H3 in E3.
    discriminate.
  }
Qed.
       
(* TODO: Two major facts to be proven:
         1. v_n in admininstr_LABEL is equal to the length of types in
            LABELS of context used to validate admininstr_BR inside the label
         2. if vcs ++ admininstr_BR is well-typed then length of vcs must be
            greater than or equal to the length of types in LABELS of context
            used to validate vcs ++ admininstr_BR *)

(* MEMO: be_typing -> Instrs_ok *)
(* MEMO: f.(f_inst) -> f.(frame_MODULE) *)
(* TODO: Reorder premises in consistent order *)
Lemma t_progress_be: forall s C C' f vcs bes tf ts1 ts2 lab ret,
  wf_config (mk_config (mk_state s f) (map admininstr_val vcs ++ map admininstr_instr bes)) ->
  Instrs_ok C bes tf ->
  List.Forall wf_val vcs ->
  tf = (ts1 :-> ts2) ->
  C = (upd_local_label_return C' (map typeof f.(LOCALS)) lab ret) ->
  Moduleinst_ok s f.(frame_MODULE) C' ->
  map typeof vcs = ts1 ->
  Store_ok s ->
  not_lf_br (map admininstr_instr bes) ->
  not_lf_return (map admininstr_instr bes) ->
  const_list (map admininstr_instr bes) \/
  exists s' f' es', Step (mk_config (mk_state s f) (map admininstr_val vcs ++ map admininstr_instr bes)) (mk_config (mk_state s' f') es').
Proof.
  move => s C C' f vcs bes tf ts1 ts2 lab ret HWf Hinstrs.
  move: s f C' vcs ts1 ts2 lab ret HWf.
  apply Instrs_ok_ind' with 
    (P := fun C be tf (Hinstr : Instr_ok C be tf) => 
      forall s f C' vcs ts1 ts2 lab ret,
      wf_config (mk_config (mk_state s f) (map admininstr_val vcs ++ map admininstr_instr [be])) ->
      List.Forall (fun e => wf_val e) vcs ->
      tf = (ts1 :-> ts2) ->
      C = (upd_local_label_return C' (map typeof f.(LOCALS)) lab ret) ->
      Moduleinst_ok s f.(frame_MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br (map admininstr_instr [be]) ->
      not_lf_return (map admininstr_instr [be]) ->
      const_list (map admininstr_instr [be]) \/
      exists s' f' es', Step (mk_config (mk_state s f) (map admininstr_val vcs ++ map admininstr_instr [be])) (mk_config (mk_state s' f') es'))
    (P0 := fun C bes tf (Hinstrs : Instrs_ok C bes tf) =>
      forall s f C' vcs ts1 ts2 lab ret,
      wf_config (mk_config (mk_state s f) (map admininstr_val vcs ++ map admininstr_instr bes)) ->
      List.Forall (fun e => wf_val e) vcs ->
      tf = (ts1 :-> ts2) ->
      C = (upd_local_label_return C' (map typeof f.(LOCALS)) lab ret) ->
      Moduleinst_ok s f.(frame_MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br (map admininstr_instr bes) ->
      not_lf_return (map admininstr_instr bes) ->
      const_list (map admininstr_instr bes) \/
      exists s' f' es', Step (mk_config (mk_state s f) (map admininstr_val vcs ++ map admininstr_instr bes)) (mk_config (mk_state s' f') es'))
      => // {C bes tf Hinstrs}.
  { (* Instr_ok__nop *)
    move => C HwfC Hwfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* TODO: Can we get rid of ++ [] in exists? *)
    right. exists s, f, ([]).
    injection Htf as ?; subst.
    apply map_eq_nil in Hts; subst.
    apply pure.
    apply Step_pure__nop.
  }
  { (* Instr_ok__unreachable *)
    move => C ts1 ts2 HWfC HWfinstr.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    simpl.
    (* TODO: Can we get rid of ++ [] in exists? *)
    case Hvcs: vcs => [ | vc' vcs'].
    - right. exists s, f, [admininstr_TRAP].
      apply: pure. apply Step_pure__unreachable.
    -
      right. exists s, f, (map admininstr_val vcs ++ [admininstr_TRAP] ++ []).
      assert (Step (mk_config (mk_state s f) [admininstr_UNREACHABLE]) (mk_config (mk_state s f) [admininstr_TRAP])). {
        apply: pure. apply: Step_pure__unreachable.
      }
      apply wf_config_app in HWfConfig; destruct HWfConfig.
      apply Step_is_wf in H as HWf; eauto.
      rewrite -Hvcs.
      apply ctxt_instrs with
        (admininstr_lst := [admininstr_UNREACHABLE]); eauto.
      subst; done.
  }
  { (* Instr_ok__drop *)
    move => C t HWfC HWfinstr.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    (* TODO: Replace injection in other places with case
              e.g. injection Htf => _ Htf1. rewrite -{}Htf1 in Hts. *)
    (* TODO: Use invert_typeof_vcs in t_progress_e too. *)
    case: Htf => Htf1 _. rewrite -Htf1 in Hts.
    invert_typeof_vcs Hts HWfVals HWfConfig.
    exists s, f, [].
    apply: pure.
    by apply: Step_pure__drop.
  }
  { (* Instr_ok__select Some *)
    move => C t HWfC HWfinstr.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht3 as [n3 Ht3]; eauto. rewrite /= in Ht3. rewrite Ht3.
    destruct v3; try discriminate.
    injection Ht3 as ?; subst.
    case: n3 HP1 HWfConfig => [ | n3'] HP1 HWfConfig.
    - exists s, f, ([admininstr_val v2]).
      apply: pure.
      apply: select_false; eauto.
    - exists s, f, ([admininstr_val v1]).
      apply: pure.
      apply: select_true; eauto.
  }
  { (* Instr_ok__select None*)
    move => C t t' nt vt HVsub Hteq HWfC HWfinstr.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht3 as [n3 Ht3]; eauto. rewrite /= in Ht3. rewrite Ht3.
    destruct v3; try discriminate.
    injection Ht3 as ?; subst.   
    case: n3 HP1 HWfConfig => [ | n3'] HP1 HWfConfig.
    - exists s, f, (map admininstr_val [v2]).
      apply: pure.
      apply: select_false; eauto.
    - exists s, f, (map admininstr_val [v1]).
      apply: pure.
      apply: select_true; eauto.
  }
  { (* Instr_ok__block *)
    move => C bt bes vt1 vt2 HBok HType IHH HWfC HWfinstr HWfC'.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. exists s, f,
      [LABEL_ (|vt2|) [] (map admininstr_val vcs ++ (map admininstr_instr bes))].
    case: Htf => Htf1 _. rewrite -Htf1 in Hts.
    apply: read.
    eapply Step_read__block with
      (z := (mk_state s f))
      (val_lst := vcs)
      (bt := bt)
      (instr_lst := bes)
      (v_n := |vt2|)
      (t_1_lst := vt1)
      (t_2_lst := vt2)
      ; eq_to_prop; eauto.
    + rewrite /fun_blocktype. inversion HBok; subst.
      * by destruct valtype_opt; eauto.
      * rewrite /fun_type.
        erewrite <- lookup_types; eauto.
    + f_equal; by rewrite -Hts size_map.
  }
  { (* Instr_ok__loop *)
    move => C bt bes vt1 vt2 HBok HType IHH HWfC HWfinstr HWfC'.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. exists s, f,
      [LABEL_ (|vt1|) [(LOOP bt bes)] (map admininstr_val vcs ++ (map admininstr_instr bes))].
    case: Htf => Htf1 _. rewrite -Htf1 in Hts.
    apply: read.
    eapply Step_read__loop with
      (z := (mk_state s f))
      (val_lst := vcs)
      (bt := bt)
      (instr_lst := bes)
      (k := |vt1|)
      (t_1_lst := vt1)
      (t_2_lst := vt2)
      ; eq_to_prop; eauto.
    + rewrite /fun_blocktype. inversion HBok; subst.
      * by destruct valtype_opt; eauto.
      * rewrite /fun_type.
        erewrite <- lookup_types; eauto.
    + f_equal; by rewrite -Hts size_map.
  }
  { (* Instr_ok__if *)
    move => C bt bes1 bes2 vt1 vt2 HBok HType IHH HType2 IHH2 HWfC HWfinstr HWfC'.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts.
    eapply typeof_append in Hts as [v [Hvcs [Hvs1 Hvs2]]].
    rewrite Hvcs in HWfVals.
    apply Forall_app in HWfVals; destruct HWfVals.
    inversion H0; subst; clear H0 H4.
    
    eapply invert_typeof_I32 in Hvs2 as [n Heqv]; eauto.
    rewrite Hvcs map_cat /= Heqv -catA.

    destruct v; try discriminate.
    unfold admininstr_val in Heqv; injection Heqv as ?; subst.
    clear Hvcs.
    case: n H3 => [ | n'] H3.
    - case Hvt1s: vt1 => [ | vt1' vt1s].
      + exists s, f, [admininstr_BLOCK bt bes2].
        rewrite Hvt1s in Hvs1.
        apply map_eq_nil in Hvs1. rewrite Hvs1.
        apply pure. by apply: if_false.
      +
        exists s, f, ((map admininstr_val (take (size vt1) vcs)) ++
          [admininstr_BLOCK bt bes2]).
        assert (Step (mk_config (mk_state s f) ([:: admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0))] ++
          [:: admininstr_IFELSE bt bes1 bes2])) (mk_config (mk_state s f)
          [:: admininstr_BLOCK bt bes2])) as HStep. {
          apply: pure.
          by apply: if_false.
        }
        apply Step_is_wf in HStep as HWf; eauto.
        rewrite -(cats0 [admininstr_BLOCK bt bes2])
                -(cats0 ([admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0%num))] ++ [admininstr_IFELSE bt bes1 bes2])).
        rewrite -Hvt1s.
        eapply ctxt_instrs; eauto.
        rewrite Hvt1s.
        apply f_equal with (f := size) in Hvs1.
        rewrite Hvt1s in Hvs1.
        rewrite size_map in Hvs1.
        destruct vcs.
        + discriminate.
        + done.
        
      1, 2:
        apply wf_config_app in HWfConfig; destruct HWfConfig;
        inversion H1; subst; clear H1;
        inversion H3; subst;
        econstructor; eauto;
        apply Forall_app; split; eauto;
        econstructor; eauto; econstructor; eauto.
    - case Hvt1s: vt1 => [ | vt1' vt1s].
      + exists s, f, [admininstr_BLOCK bt bes1].
        rewrite Hvt1s in Hvs1.
        apply map_eq_nil in Hvs1. rewrite Hvs1.
        apply pure. by apply: if_true.
      +
        exists s, f, ((map admininstr_val (take (size vt1) vcs)) ++
          [admininstr_BLOCK bt bes1]).
        rewrite -(cats0 [admininstr_BLOCK bt bes1])
                -(cats0 ([admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (N.pos n')))] ++ [admininstr_IFELSE bt bes1 bes2])).
        rewrite -Hvt1s.
        eapply ctxt_instrs; eauto.
        - apply: pure.
          by apply: if_true.
        -
          rewrite Hvt1s.
          apply f_equal with (f := size) in Hvs1.
          rewrite Hvt1s in Hvs1.
          rewrite size_map in Hvs1.
          destruct vcs.
          + discriminate.
          + done.
        - apply wf_config_app in HWfConfig; destruct HWfConfig.
          inversion H1; subst; clear H1.
          inversion H3; subst.
          econstructor; eauto.
          apply Forall_app; split; eauto.
          econstructor; eauto; econstructor; eauto; econstructor; eauto.
        - apply wf_config_app in HWfConfig; destruct HWfConfig.
          inversion H1; subst; clear H1.
          econstructor; eauto.
          apply Forall_cons; eauto.
          inversion H6; subst; eauto.
          inversion H4; subst.
          econstructor; eauto.
  }
  { (* Instr_ok__br *)
    move => C l ts1 ts ts2 Hlablen Hlablookup HWfC HWfinstr.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    move/not_lf_br_singleton: Hnotbr => Hnotbr.
    by move/(_ l): Hnotbr.
  }
  { (* Instr_ok__br_if *)
    move => C l ts Hlen Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]].
    rewrite Hvcs in HWfVals.
    apply Forall_app in HWfVals; destruct HWfVals.
    inversion H0; subst; clear H0 H4.
    eapply invert_typeof_I32 in Ht1 as [n Heqv]; eauto.
    rewrite Hvcs map_cat /= Heqv -catA.
    rewrite Hvcs map_cat /= Heqv -catA in HWfConfig.
    rewrite -(cats0 ([admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n))] ++ [admininstr_BR_IF l])).
    destruct v1; try discriminate.
    unfold admininstr_val in Heqv; injection Heqv as ?; subst.
    clear Hvcs.
    case: n H3 HWfConfig => [ | n'] H3 HWfConfig.
    all: apply wf_config_app in HWfConfig; destruct HWfConfig;
      apply wf_config_app in H1; destruct H1.
    + destruct ts.
      - exists s, f, []. simpl.
        apply pure.
        destruct vcs; by eapply br_if_false.
      - exists s, f, (map admininstr_val (take (size (v :: ts)) vcs)
          ++ [] ++ []).
        eapply ctxt_instrs; eauto.
        - eapply pure.
          by eapply br_if_false.
        - destruct vcs => //=.
        - apply wf_config_app; split; eauto.
        - inversion H0; subst; econstructor; eauto.
        
    + destruct ts.
      - exists s, f, [admininstr_BR l].
        apply pure.
        destruct vcs; by eapply br_if_true.
      - exists s, f, (map admininstr_val (take (size (v :: ts)) vcs)
          ++ [(admininstr_BR l)] ++ []).
        eapply ctxt_instrs; eauto.
        - eapply pure.
          by eapply br_if_true.
        - destruct vcs => //=.
        - apply wf_config_app; split; eauto.
        - inversion H2; subst; econstructor; eauto.
          inversion H7; subst.
          inversion H8; subst.
          apply Forall_cons; eauto.
          econstructor; eauto.
  }
  { (* Instr_ok__br_table *)
    move => C ls lN ts1 ts ts2 HlenlN Hlenls HlookuplN Hlookupls HWfC HWfinstr.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    rewrite catA in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]].
    rewrite Hvcs in HWfVals.
    apply Forall_app in HWfVals; destruct HWfVals.
    inversion H0; subst; clear H0 H4.
    eapply invert_typeof_I32 in Ht1 as [n Heqv]; eauto.
    rewrite Hvcs map_cat /= Heqv -catA.
    rewrite Hvcs map_cat /= Heqv -catA in HWfConfig.
    apply wf_config_app in HWfConfig; destruct HWfConfig as [HWfConfig1 HWfConfig2].
    rewrite -(cats0 ([admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n))] ++ [admininstr_BR_TABLE ls lN])).
    destruct v1; try discriminate.
    unfold admininstr_val in Heqv; injection Heqv as ?; subst.
    case Hv1: (n <? |ls|)%BN.
    + destruct (ts1 ++ ts).
      - exists s, f, [admininstr_BR (lookup_total ls n)]. simpl.
        apply pure.
        destruct vcs; by eapply br_table_lt.
      -
        exists s, f, (map admininstr_val (take (size (v :: l)) vcs)
                      ++ [admininstr_BR (lookup_total ls n)] ++ []).
        assert ( Step (mk_config (mk_state s f) ([:: admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n))] ++
          [:: admininstr_BR_TABLE ls lN])) (mk_config (mk_state s f) [:: admininstr_BR (ls [|n|])])) as HPure. {
          eapply pure.
          by eapply br_table_lt.
        }
        apply Step_is_wf in HPure as HWfConfig'; eauto.
        eapply ctxt_instrs; eauto.
        destruct vcs => //=.
      
    + destruct (ts1 ++ ts).
      - exists s, f, [admininstr_BR lN].
        apply pure.
        destruct vcs; apply br_table_ge; eauto.
        1, 2: eapply N.ltb_ge in Hv1;
          unfold N_geb;
          by apply/N.leb_spec0.
      - exists s, f, (map admininstr_val (take (size (v :: l)) vcs)
                      ++ [admininstr_BR lN] ++ []).
        assert (Step (mk_config (mk_state s f) ([:: admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n))]
                                                  ++ [:: admininstr_BR_TABLE ls lN]))
                (mk_config (mk_state s f) [:: admininstr_BR lN])) as HPure. {
          eapply pure.
          eapply br_table_ge; eauto.
          eapply N.ltb_ge in Hv1.
          unfold N_geb.
          by apply/N.leb_spec0.
        }
        apply Step_is_wf in HPure as HWfConfig'; eauto.
        eapply ctxt_instrs; eauto.
        destruct vcs => //=.
  }
  { (* Instr_ok__call *)
    move => C x ts1 ts2 Haddr Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* TODO: Can we get rid of ++ [] in exists? *)
    right.
    destruct vcs.
    {
      exists s, f, [CALL_ADDR ((fun_funcaddr (mk_state s f)) [|(x :> N)|])].
      apply: read. apply: Step_read__call.
      rewrite /fun_funcaddr.
      rewrite Hcontext in Haddr.
      erewrite <- funcs_size; eauto.
    }
    exists s, f, (map admininstr_val (v :: vcs) ++ [CALL_ADDR ((fun_funcaddr (mk_state s f)) [|(x :> N)|])] ++ []).
    (* TODO: Can we get rid of these rewrites? *)
    rewrite -[map admininstr_val (v :: vcs) ++ _]cats0 -catA.
    apply wf_config_app in HWfConfig; destruct HWfConfig as [HWfConfig1 HWfConfig2].
    assert (Step (mk_config (mk_state s f) [:: admininstr_CALL x])
              (mk_config (mk_state s f) [:: CALL_ADDR ((fun_funcaddr (mk_state s f)) [|x :> N|])])) as HRead. {
      apply: read. apply: Step_read__call.
      rewrite /fun_funcaddr.
      rewrite Hcontext in Haddr.
      erewrite <- funcs_size; eauto.
    }
    apply Step_is_wf in HRead as HWfConfig'; eauto.
    apply ctxt_instrs with
      (admininstr_lst := [admininstr_CALL x]); eauto.
  }
  { (* Instr_ok__call_indirect *)
    move => C x y ts1 ts2 lim HSizex HLookupx HSizey HLookupy HWfC HWfinstr HWfTabType.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]].
    rewrite Hvcs in HWfVals.
    apply Forall_app in HWfVals; destruct HWfVals.
    inversion H0; subst; clear H0 H4.
    eapply invert_typeof_I32 in Ht1 as [n Heqv]; eauto.
    remember (mk_num__0 Inn_I32 (mk_uN n)) as v_i.
    rewrite Hvcs map_cat /= Heqv -catA.
    rewrite Hvcs map_cat /= Heqv -catA in HWfConfig.
    apply wf_config_app in HWfConfig; destruct HWfConfig as [HWfCf1 HWfCf2].
    rewrite -(cats0 ([admininstr_CONST I32 v_i] ++ [admininstr_CALL_INDIRECT x y])).
    eapply minst_invert_tables
      with (C' := C')
      in Hmod.
    2: {
      subst;
      resolve_inst_match.
    }
    eapply Forall2_size2 in Hmod.
    2: ineq_to_prop; apply HSizex.
    assert (proj_num__0 v_i != None) as HNone. {
      rewrite Heqv_i. done.
    }
    pose proof (call_indirect_progress s f v_i x y HNone) as [es HStep].

    destruct ts1.
    {
      exists s, f, es.
      destruct vcs; apply HStep.
    }
    apply Step_is_wf in HStep as HWfConfig'; eauto.
    exists s, f, (map admininstr_val (take (size (v :: ts1)) vcs) ++ es ++ []).
    apply ctxt_instrs; eauto.
    destruct vcs => //=.
  }
  { (* Instr_ok__return *)
    move => C ts1 ts ts2 Hretts HWfC HWfinstr.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by move/not_lf_return_singleton: Hnotret.
  }
  { (* Instr_ok__const *)
    move => C t vc HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left.
  }
  { (* Instr_ok__unop *)
    move => C t unop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    eapply invert_typeof_numtype in Ht1 as [n Heqv1].
    rewrite Heqv1.
    case Eunop: (fun_unop_ t unop n) => [ c | ].
    + case Ec: c => [ | c' l ]; subst.
      +
        exists s, f, [admininstr_TRAP].
        apply: pure.
        apply: unop_trap; eq_to_prop; rewrite Eunop; eauto. discriminate.
      + exists s, f, [admininstr_CONST t c'].
        apply: pure.
        apply: unop_val.
        * by rewrite Eunop.
        * rewrite Eunop. eq_to_prop. discriminate.
        * rewrite Eunop. by apply mem_head.
      + destruct v1; unfold admininstr_val in Heqv1; try discriminate.
        injection Heqv1 as ?; subst.
        inversion HWfVals; subst; clear HWfVals H2.
        inversion H1; subst. inversion HWfinstr; subst.
        eapply unop_not_none in H2; eauto. done.
  }
  { (* Instr_ok__binop *)
    move => C t binop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.

    inv_Forall HWfVals.
    have [n1 [Heqv1 Hwf1]] := invert_typeof_numtype_wf _ _ Ht1 HP.
    rewrite Heqv1.
    have [n2 [Heqv2 Hwf2]] := invert_typeof_numtype_wf _ _ Ht2 HP0.
    rewrite Heqv2.
    have Hwfb : wf_binop_ t binop by inversion HWfinstr.
    pose proof (binop_total t binop n1 n2 Hwf1 Hwf2 Hwfb) as [lst_opt HBinop].
    case Ebinop: lst_opt => [ a | ].
    + case Elst: a => [ | a' as'].
      + exists s, f, [admininstr_TRAP].
        apply: pure.
        apply: binop_trap; eauto.
        - rewrite Ebinop. done.
        - eq_to_prop; subst. done.
       
      + exists s, f, [admininstr_CONST t a'].
        apply: pure.
        apply: binop_val; eauto.
        * rewrite Ebinop. rewrite Elst. done.
        * rewrite Ebinop; done.
        * rewrite Ebinop. rewrite Elst. by apply mem_head.

      + eapply binop_not_none in HBinop; eauto.
        done.
  }
  { (* Instr_ok__testop *)
    move => C t testop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    eapply invert_typeof_numtype in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    move Etestop: (fun_testop_ t testop n1) => c.
    case ENone: c => [ c' | ].
    -
      exists s, f, [admininstr_CONST I32 c'].
      apply: pure.
      apply: Step_pure__testop.
      + subst. rewrite ENone. apply/eqP. discriminate.
      + subst. rewrite ENone. done.
    - subst.
      inversion HWfinstr; subst.
      inv_Forall HWfVals.
      destruct v1; unfold admininstr_val in Heqv1; try discriminate.
      injection Heqv1 as ?; subst.
      inversion HP; subst.
      eapply testop_not_none in H0; eauto.
      done.
  }
  { (* Instr_ok__relop *)
    move => C t relop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. 
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.

    inv_Forall HWfVals.
    have [n1 [Heqv1 Hwf1]] := invert_typeof_numtype_wf _ _ Ht1 HP.
    rewrite Heqv1.
    have [n2 [Heqv2 Hwf2]] := invert_typeof_numtype_wf _ _ Ht2 HP0.
    rewrite Heqv2.
    have Hwfr : wf_relop_ t relop by inversion HWfinstr.
    pose proof (relop_total t relop n1 n2 Hwf1 Hwf2 Hwfr) as [c Hrelop].
    case ENone: c => [ c' | ].
    - exists s, f, [admininstr_CONST I32 c'].
      apply: pure.
      apply: Step_pure__relop; eauto.
      - rewrite ENone. apply/eqP; discriminate.
      - rewrite ENone. done.

    - subst.
      eapply relop_not_none in Hrelop; eauto.
      done.
  }
  { (* Instr_ok__cvtop *)
    move => C t2' t1' cvtop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.

    inv_Forall HWfVals.
    have [n1 [Heqv1 Hwf1]] := invert_typeof_numtype_wf _ _ Ht1 HP.
    rewrite Heqv1.
    have Hwfc : wf_cvtop__ t1' t2' cvtop by inversion HWfinstr.
    pose proof (cvtop_total t1' t2' cvtop n1 Hwf1 Hwfc) as [n2 Hcvtop].
    case ENone: n2 => [ c' | ].
    - 
      case Ecvtop: c' => [ | c].
      + exists s, f, [admininstr_TRAP].
        apply: pure.
        apply: cvtop_trap; eauto; subst; done.
      + exists s, f, [admininstr_CONST t2' c].
        apply: pure.
        apply: cvtop_val; eauto.
        * rewrite ENone. by rewrite Ecvtop.
        * rewrite ENone; done.
        * rewrite ENone. rewrite Ecvtop. by apply mem_head.

    - subst.
      eapply cvtop_not_none in Hcvtop; eauto.
      done.
  }
  { (* Instr_ok__ref_null *)
    move => C rt HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left.
  }
  { (* Instr_ok__ref_func *)
    move => C x ft Hxrange Heft HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    rewrite Hcontext in Hxrange.
    eapply funcs_size in Hmod.
    erewrite Hmod in Hxrange.
    exists s, f, ([admininstr_REF_FUNC_ADDR (lookup_total (fun_funcaddr (mk_state s f))
      (proj_uN_0 x))]).
    apply: read.
    apply Step_read__ref_func.
    by rewrite /fun_funcaddr.
  }
  { (* Instr_ok__ref_is_null *)
    move => C rt HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    eapply invert_typeof_reftype in Ht1 as [Hnull | Hnonnull].
    - exists s, f, ([(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 1)))]).
      apply: pure.
      assert (admininstr_val v1 = admininstr_ref (ref_REF_NULL rt)).
      {
        auto.
      }
      rewrite H.
      by eapply ref_is_null_true.
    - exists s, f, ([(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN 0)))]).
      apply: pure.
      destruct Hnonnull as [x [Hf | Hh]].
      {
        assert (admininstr_val v1 =
          admininstr_ref (REF_FUNC_ADDR x)).
        {
          auto.
        }
        rewrite H.
        eapply ref_is_null_false.
        move => HContra.
        inversion HContra; eq_to_prop; subst.
        inversion H0.
      }
      {
        assert (admininstr_val v1 =
          admininstr_ref (REF_HOST_ADDR x)).
        {
          auto.
        }
        rewrite H.
        eapply ref_is_null_false.
        move => HContra.
        inversion HContra; eq_to_prop; subst.
        inversion H0.
      }
  }
  (* SIMD *)

  { (* Instr_ok__vconst *)
    move => C c HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left.
  }
  { (* Instr_ok__vvunop *)
    move => C v_vvunop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    inv_Forall HWfVals.
    have [c1 [Heqv1 Hwf1]] := invert_typeof_V128 _ Ht1 HP.
    rewrite Heqv1.
    exists s, f, [admininstr_VCONST V128 (vvunop_ V128 v_vvunop c1)].
    apply: pure.
    by apply: Step_pure__vvunop.
  }
  { (* Instr_ok__vvbinop *)
    move => C v_vvbinop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    inv_Forall HWfVals.
    have [c1 [Heqv1 Hwf1]] := invert_typeof_V128 _ Ht1 HP.
    have [c2 [Heqv2 Hwf2]] := invert_typeof_V128 _ Ht2 HP0.
    rewrite Heqv1 Heqv2.
    exists s, f, [admininstr_VCONST V128 (vvbinop_ V128 v_vvbinop c1 c2)].
    apply: pure.
    by apply: Step_pure__vvbinop.
  }
  { (* Instr_ok__vvternop *)
    move => C v_vvternop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    inv_Forall HWfVals.
    have [c1 [Heqv1 Hwf1]] := invert_typeof_V128 _ Ht1 HP.
    have [c2 [Heqv2 Hwf2]] := invert_typeof_V128 _ Ht2 HP0.
    have [c3 [Heqv3 Hwf3]] := invert_typeof_V128 _ Ht3 HP1.
    rewrite Heqv1 Heqv2 Heqv3.
    exists s, f, [admininstr_VCONST V128 (vvternop_ V128 v_vvternop c1 c2 c3)].
    apply: pure.
    by apply: Step_pure__vvternop.
  }
  { (* Instr_ok__vvtestop *)
    move => C v_vvtestop HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    inv_Forall HWfVals.
    have [c1 [Heqv1 Hwf1]] := invert_typeof_V128 _ Ht1 HP.
    rewrite Heqv1.
    destruct v_vvtestop.
    exists s, f, [admininstr_CONST I32
      (mk_num__0 Inn_I32 (ine_ (!(res_size valtype_V128)) c1 (mk_uN 0)))].
    apply: pure.
    by apply: Step_pure__vvtestop.
  }
  (* VUNOP / VBINOP / VTESTOP / VRELOP / VSHIFTOP / VBITMASK / VSWIZZLE /
     VSHUFFLE.

     All eight reduce through `lanes_`, and every one of their Step_pure rules
     needs the lanes of the operand in one *particular* injection of the
     generated `lane_` union (`proj_lane__0` for numtype lanes, `proj_lane__1`
     for packed lanes, `proj_lane__2` for `Jnn` lanes).  The only fact
     available about `lanes_` (which is an Axiom) is `lanes__is_wf`, and
     `wf_lane_ (lanetype_Jnn Jnn_I32) l` is satisfied both by
     `mk_lane__0 I32 c` and by `mk_lane__2 Jnn_I32 c` - the spectec subtyping
     between `num_`/`pack_`/`iN` and `lane_` is not preserved by the Coq
     encoding.  So `proj_lane__2 l <> None` is not derivable, and no axiom can
     repair it: `vextract_lane_num` wants the `mk_lane__0` form of the very
     same list that `vtestop_true` wants in `mk_lane__2` form. *)
  1-8: admit.
  { (* Instr_ok__vsplat *)
    move => C sh HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    inv_Forall HWfVals.
    destruct sh as [Lnn dm]; destruct dm as [Ndim].
    have Hwfsh : wf_shape (X Lnn (mk_dim Ndim)) by inversion HWfinstr.
    have [c1 [Heqv1 Hwf1]] := invert_typeof_numtype_wf _ _ Ht1 HP.
    rewrite Heqv1.
    have Hpk := packnum_not_none Lnn c1 Hwf1.
    exists s, f, [admininstr_VCONST V128
      (inv_lanes_ (X Lnn (mk_dim Ndim)) (list_repeat (!(packnum_ Lnn c1)) Ndim))].
    apply: pure.
    by apply: Step_pure__vsplat.
  }

  (* VEXTRACT_LANE.  Two independent obstacles:
     - `wf_instr (VEXTRACT_LANE sh sx_opt i)` (instr_case_34) states
       `(fun_lanetype sh == lanetype_numtype nt) <-> (sx_opt == None)` for a
       *universally* quantified `nt`.  Taking `sh = X lanetype_I32 d`,
       `sx_opt = Some U` and `nt = I64` satisfies it, yet neither
       `vextract_lane_num` (needs `sx_opt = None`) nor `vextract_lane_pack`
       (needs a packed shape) applies.
     - even for `sx_opt = None` the rule needs the i-th lane in the
       `mk_lane__0` injection, which `lanes__is_wf` does not give (see the
       note on the previous eight cases). *)
  1: admit.
  { (* Instr_ok__vreplace_lane *)
    move => C sh i Hrange HWfC HWfdim HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfVals HWfConfig.
    inv_Forall HWfVals.
    destruct sh as [Lnn dm]; destruct dm as [Ndim].
    have Hwfsh : wf_shape (X Lnn (mk_dim Ndim)) by inversion HWfinstr.
    have [c1 [Heqv1 Hwf1]] := invert_typeof_V128 _ Ht1 HP.
    have [c2 [Heqv2 Hwf2]] := invert_typeof_numtype_wf _ _ Ht2 HP0.
    rewrite Heqv1 Heqv2.
    have Hpk := packnum_not_none Lnn c2 Hwf2.
    exists s, f, [admininstr_VCONST V128
      (inv_lanes_ (X Lnn (mk_dim Ndim))
        (list_update_func (lanes_ (X Lnn (mk_dim Ndim)) c1) (i :> N)
          (fun _ : lane_ => (!(packnum_ Lnn c2)))))].
    apply: pure.
    by apply: Step_pure__vreplace_lane.
  }

  (* VEXTUNOP / VEXTBINOP / VNARROW / VCVTOP: same `lane_`-injection obstacle
     as the eight cases above - `fun_vextunop__`, `fun_vextbinop__`,
     `fun_vnarrow`-style rules and `vcvtop_*` all require
     `proj_lane__2`/`proj_lane__1` of the operand's lanes to be `Some`. *)
  1-4: admit.
  { (* Instr_ok__local_get *)
    move => C x t Hlen Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    exists s, f, (map admininstr_val [fun_local (mk_state s f) x]).
    apply: read.
    by apply: Step_read__local_get.
  }
  { (* Instr_ok__local_set *)
    move => C x t Hlen Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    case Estate: (with_local (mk_state s f) x v1) => [s' f'].
    exists s', f', [].
    rewrite -Estate.
    by apply: Step__local_set.
  }
  { (* Instr_ok__local_tee *)
    move => C x t Hlen Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    exists s, f, [admininstr_val v1; admininstr_val v1; admininstr_LOCAL_SET x].
    apply: pure.
    by apply: Step_pure__local_tee.
  }
  { (* Instr_ok__global_get *)
    move => C x t mut Hlen Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    exists s, f, (map admininstr_val [VALUE (fun_global (mk_state s f) x)]).
    apply: read.
    by apply: Step_read__global_get.
  }
  { (* Instr_ok__global_set *)
    move => C x t Hlen Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    (* TODO: Does set/pose tactic support destructuring? *)
    case Estate: (with_global (mk_state s f) x v1) => [s' f'].
    exists s', f', [].
    rewrite -Estate.
    by apply: Step__global_set.
  }
  { (* Instr_ok__table_get *)
    move => C x rt lim Hlen Hlookup HWfC HWfinstr HWfTabType.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n Heqv]; eauto.
    rewrite Heqv.
    case Es : (n <? (|(REFS (fun_table (mk_state s f) x))|))%BN.
    - exists s, f, [(admininstr_ref (lookup_total (REFS (fun_table (mk_state s f) x)) n))].
      eapply read.
      by eapply table_get_val.
    - exists s, f, [admininstr_TRAP].
      eapply read.
      eapply table_get_trap; eauto.
      simpl.
      eapply N.ltb_ge in Es.
      unfold N_geb.
      by apply/N.leb_spec0.
  }
  { (* Instr_ok__table_set *)
    move => C x rt lim Hlen Hlookup HWfC HWfinstr HWfTabType.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    eapply invert_typeof_reftype' in Ht2 as [r2 Heqv2].
    rewrite Heqv2.
    case Es : (n1 <? (|REFS (fun_table (mk_state s f) x)|))%BN.
    - case Estate: (with_table (mk_state s f) x n1 r2) => [s' f'].
      exists s', f', [].
      rewrite -Estate.
      by eapply table_set_val.
    - exists s, f, [admininstr_TRAP].
      eapply table_set_trap; eauto.
      eapply N.ltb_ge in Es.
      unfold N_geb.
      by apply/N.leb_spec0.
  }
  { (* Instr_ok__table_size *)
    move => C x lim rt Hlen Hlookup HWfC HWfinstr HWfTabType.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    eapply minst_invert_tables
      with (C' := C) 
      in Hmod.
    2: {
      subst. by resolve_inst_match.
    }
    eapply Forall2_size2 in Hmod.
    2: ineq_to_prop; apply Hlen.
    destruct Hmod as [tbr [tbt [HRange [HLookup HSub]]]].
    exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (|tbr|))))].
    eapply read.
    eapply Step_read__table_size.
    by rewrite /fun_table HLookup /=.
  }
  { (* Instr_ok__table_grow *)
    (* Always fail *)
    move => C x rt lim Hlen Hlookup HWfC HWfinstr HWfTabType.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    eapply invert_typeof_reftype' in Ht1 as [r1 Heqv1].
    rewrite Heqv1.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2]; eauto.
    rewrite Heqv2.

    pose proof invsigned_total_32m1 as [r Hunsigned].
    exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN r)))].
    by eapply table_grow_fail.
  }
  { (* Instr_ok__table_fill *)
    move => C x rt lim Hlen Hlookup HWfC HWfinstr HWfTabType.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    eapply invert_typeof_reftype' in Ht2 as [r2 Heqv2].
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3]; eauto.
    rewrite Heqv3.
    case Hs: ((n1 + n3) >?
      (| (REFS (fun_table (mk_state s f) x))|))%BN.
    {
      exists s, f, [admininstr_TRAP].
      eapply read.
      by eapply table_fill_trap.
    }
    destruct n3 using N.peano_ind.
    {
      exists s, f, [].
      eapply read.
      eapply table_fill_zero; eauto.
      subst; simpl.
      eapply N.ltb_ge in Hs.
      by apply/N.leb_spec0.
    }
    {
      clear IHn3.
      exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n1))); (admininstr_val v2);
      (admininstr_TABLE_SET x); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n1 + 1))));
      (admininstr_val v2); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n3)));
      (admininstr_TABLE_FILL x)].
      assert (n3 = ((N.succ n3) - 1)%Z).
      { rewrite Z.sub_1_r.
        rewrite Znat.N2Z.inj_succ.
        rewrite Z.pred_succ.
        by rewrite Znat.N2Z.id.
      }
      eapply read.
      rewrite {2}H.
      eapply table_fill_succ; eauto.
      - apply/eqP. apply N.neq_succ_0.
      - simpl. eapply N.ltb_ge in Hs.
        by apply/N.leb_spec0.
    }
  }
  { (* Instr_ok__table_copy *)
    move => C x1 x2 lim1 rt lim2 Hlenx1 Hlookupx1 Hlenx2 Hlookupx2 HWfC HWfinstr HWfTabType1 HWfTabType2.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2]; eauto.
    rewrite Heqv2.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3]; eauto.
    rewrite Heqv3.
    case Hs: (((n2 + n3) >? (|(REFS (fun_table (mk_state s f) x2))|))%BN ||
      ((n1 + n3) >? (|(REFS (fun_table (mk_state s f) x1))|))%BN).
    {
      exists s, f, [admininstr_TRAP].
      eapply read.
      eapply table_copy_trap; eauto.
    }
    destruct n3 using N.peano_ind.
    {
      exists s, f, [].
      eapply read.
      eapply table_copy_zero; eauto.
      apply orb_false_elim in Hs; destruct Hs.
      unfold N_gtb in H.
      unfold N_gtb in H0.
      eapply N.ltb_ge in H.
      eapply N.ltb_ge in H0.
      subst.
      apply/andP; split; ineq_to_prop; eauto.
    }
    case Hle: ((n1 <=? n2)%BN).
    {
      exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n1))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n2)));
                    (admininstr_TABLE_GET x2); (admininstr_TABLE_SET x1); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n1 + 1))));
                    (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n2 + 1)))); (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n3)));
                    (admininstr_TABLE_COPY x1 x2)].
      eapply read.
      assert (n3 = ((N.succ n3) - 1)%Z).
      { rewrite Z.sub_1_r.
        rewrite Znat.N2Z.inj_succ.
        rewrite Z.pred_succ.
        by rewrite Znat.N2Z.id.
      }
      rewrite {2}H.
      eapply table_copy_le; eauto.
      - apply/eqP. apply N.neq_succ_0.
      - apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
        unfold N_gtb in HB0.
        unfold N_gtb in HB1.
        eapply N.ltb_ge in HB0.
        eapply N.ltb_ge in HB1.
        subst.
        apply/andP; split; ineq_to_prop; eauto.
    }
    {
      exists s, f, [
        (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n1 + n3))));
        (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n2 + n3))));
        (admininstr_TABLE_GET x2);
        (admininstr_TABLE_SET x1);
        (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n1)));
        (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n2)));
        (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n3)));
        (admininstr_TABLE_COPY x1 x2)].

      assert (n3 = ((N.succ n3) - 1)%Z).
      { rewrite Z.sub_1_r.
        rewrite Znat.N2Z.inj_succ.
        rewrite Z.pred_succ.
        by rewrite Znat.N2Z.id.
      }
      rewrite {2 3 4}H.
      eapply read.
      rewrite add_sub_parens.
      rewrite add_sub_parens.
      
      eapply table_copy_gt; eauto.
      - simpl. apply N.leb_gt in Hle. by apply/N.ltb_lt.
      - apply/eqP. apply N.neq_succ_0.
      - apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
        unfold N_gtb in HB0.
        unfold N_gtb in HB1.
        eapply N.ltb_ge in HB0.
        eapply N.ltb_ge in HB1.
        subst.
        apply/andP; split; ineq_to_prop; eauto.
      all: rewrite Z.one_succ;
        rewrite Znat.N2Z.inj_succ;
        rewrite -Z.succ_le_mono;
        apply Znat.N2Z.is_nonneg.
    }
  }
  { (* Instr_ok__table_init *)
    move => C x1 x2 lim1 rt Hlenx1 Hlookupx1 Hlenx2 Hlookupx2 HWfC HWfinstr HWfTabType.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2]; eauto.
    rewrite Heqv2.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3]; eauto.
    rewrite Heqv3.
    case Hs: (((n2 + n3) >? (|(eleminst_REFS (fun_elem (mk_state s f) x2))|))%BN
      || ((n1 + n3) >? (|(REFS (fun_table (mk_state s f) x1))|))%BN).
    {
      exists s, f, [admininstr_TRAP].
      eapply read.
      eapply table_init_trap; eauto.
    }
    destruct n3 using N.peano_ind.
    {
      exists s, f, [].
      eapply read.
      eapply table_init_zero; eauto.
      apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
      unfold N_gtb in HB0.
      unfold N_gtb in HB1.
      eapply N.ltb_ge in HB0.
      eapply N.ltb_ge in HB1.
      subst.
      apply/andP; split; ineq_to_prop; eauto.
    }
    {
      clear IHn3.
      exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n1)));
        (admininstr_ref (lookup_total (eleminst_REFS (fun_elem (mk_state s f) x2)) n2));
        (admininstr_TABLE_SET x1);
        (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n1 + 1))));
        (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n2 + 1))));
        (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n3)));
        (admininstr_TABLE_INIT x1 x2)].
      eapply read.
      assert (n3 = ((N.succ n3) - 1)%Z).
      { rewrite Z.sub_1_r.
        rewrite Znat.N2Z.inj_succ.
        rewrite Z.pred_succ.
        by rewrite Znat.N2Z.id.
      }
      rewrite {2}H.
      eapply table_init_succ; eauto.
      {
        simpl.
        eapply Bool.orb_false_elim in Hs as [Hs1 _].
        simpl in Hs1.
        remember (| (eleminst_REFS (lookup_total (store_ELEMS s)
          (lookup_total (ELEMS (frame_MODULE f)) (proj_uN_0 x2))))|) as num.
        rewrite N.add_succ_r in Hs1.
        unfold N_gtb in Hs1.
        move/N.ltb_ge in Hs1.
        apply N.le_succ_l in Hs1.
        pose proof (N.le_add_r n2 n3).
        ineq_to_prop.
        eapply N.le_lt_trans; eauto.
      }
      {
        apply/eqP. apply N.neq_succ_0.
      }
      {
        apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
        unfold N_gtb in HB0.
        unfold N_gtb in HB1.
        eapply N.ltb_ge in HB0.
        eapply N.ltb_ge in HB1.
        subst.
        apply/andP; split; ineq_to_prop; eauto.
      }
    }
  }
  { (* Instr_ok__elem_drop *)
    move => C x rt Hlen Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    case Estate: (with_elem (mk_state s f) x []) => [s' f'].
    exists s', f', [].
    rewrite -Estate.
    by apply: Step__elem_drop.
  }
  { (* Instr_ok__memory_size *)
    move => C mt Hlen Hlookup HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    (* TODO: This pose tactic cannot infer Inh_nat for some reason *)
    (* pose addr := (lookup_total (MODULE_MEMS (frame_MODULE f)) 0). *)
    pose addr := (@lookup_total N Inh_nat (MEMS (frame_MODULE f)) 0).
    invert_storeok Hstore.
    remember (upd_local_label_return C' [seq typeof i | i <- LOCALS f] lab ret) as C.
    have {}HeqC : context_MEMS C = context_MEMS C'.
    { rewrite HeqC. by case: C' HeqC Hmod => *. }
    have {}Haddr : (addr <? | meminst_lst |)%BN.
    { invert_moduleinstok Hmod.
      rewrite /addr /=.
      rewrite -H0 => //=.
      move/Forall2_size2: HMemExtOk => HMemOk.
      ineq_to_propH Hlen; subst.
      destruct C; simpl in HeqC; simpl in Hlen.
      rewrite HeqC in Hlen.
      eapply HMemOk in Hlen as Hexta.
      eapply Externaddr_invert_mems in Hexta as [xt [meminst [HBound [HLookup [HEq HSub]]]]].
      ineq_to_prop.
      apply HBound.
    }
    remember ({|
              store_FUNCS := funcinst_lst;
              store_GLOBALS := globalinst_lst;
              store_TABLES := tableinst_lst;
              store_MEMS := meminst_lst;
              store_ELEMS := eleminst_lst;
              store_DATAS := datainst_lst
            |}) as s.
    have {}Hmem : Meminst_ok s (lookup_total meminst_lst addr) (lookup_total memtype_lst addr).
    {
      move/Forall2_size: HMem => HMem.
      move/(_ addr): HMem => HMem.
      ineq_to_propH Haddr.
      by move/(_ Haddr): HMem => {}HMem.
    }
    inversion Hmem.
    exists s, f, [admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (v_n)))].
    apply: read.
    apply: Step_read__memory_size.
    eq_to_prop.
    rewrite /addr in H.
    subst. simpl.
    rewrite  /fun_mem -H H2.
    by rewrite N.mul_assoc.
    (* wfness *)
    econstructor; eauto.
  }
  { (* Instr_ok__memory_grow *)
    move => C mt Hlen Hlookup HWfC HWMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    set meminst1 := (fun_mem (mk_state s f) (mk_uN 0)).
    (* TODO: Does set/pose tactic support destructuring? *)
    case Ememinst1: meminst1 => [[[limn1 limm1]] bs1].
    pose meminst2 := {|
      meminst_TYPE := (PAGE (mk_limits (mk_uN ((proj_uN_0 limn1) + n1)%BN) limm1));
      BYTES := (bs1 ++ list_repeat (mk_byte 0) (n1 * (64 * Ki)))
      |}.
    (* TODO: Does set/pose tactic support destructuring? *)
    case Estate: (with_meminst (mk_state s f) (mk_uN 0) meminst2) => [s' f'].
    (* NOTE: We could just use step_memory_grow_fail but
              we assume we can alway grow memory when it does not exceed predefined maximum size *)

    pose proof invsigned_total_32m1 as [r Hunsigned].
    exists s, f, [admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN r))].
    apply: memory_grow_fail; eauto.
  }
  { (* Instr_ok__memory_fill *)
    move => C mt Hlen Hlookup HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2]; eauto.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3]; eauto.
    rewrite Heqv3.

    case Hs: ((n1 + n3) >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
    {
      exists s, f, [admininstr_TRAP].
      eapply read.
      by eapply memory_fill_trap.
    }
    destruct n3 using N.peano_ind.
    {
      exists s, f, [].
      eapply read.
      eapply memory_fill_zero; eauto.
      apply N.ltb_ge in Hs.
      ineq_to_prop.
      apply Hs.
    }
    {
      exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n1))));
      (admininstr_val v2);
      (admininstr_STORE I32 (Some (mk_sz 8)) memarg0);
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n1 + 1))));
      (admininstr_val v2);
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n3))));
      admininstr_MEMORY_FILL].
      eapply read.
      assert (n3 = ((N.succ n3) - 1)%Z).
      { rewrite Z.sub_1_r.
        rewrite Znat.N2Z.inj_succ.
        rewrite Z.pred_succ.
        by rewrite Znat.N2Z.id.
      }
      rewrite {2}H.
      eapply memory_fill_succ; eauto.
      - apply/eqP. apply N.neq_succ_0.
      - simpl.
        apply N.ltb_ge in Hs.
        ineq_to_prop.
        apply Hs.
    }
  }
  { (* Instr_ok__memory_copy *)
    move => C mt Hlen Hlookup HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2]; eauto.
    rewrite Heqv2.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3]; eauto.
    rewrite Heqv3.

    case Hs: (((n2 + n3) >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN
      || ((n1 + n3) >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN).
    {
      exists s, f, [admininstr_TRAP].
      eapply read.
      eapply memory_copy_trap; eauto.
      econstructor; eauto.
    }
    destruct n3 using N.peano_ind.
    {
      exists s, f, [].
      eapply read.
      eapply memory_copy_zero; eauto.
      apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
      unfold N_gtb in HB0.
      unfold N_gtb in HB1.
      eapply N.ltb_ge in HB0.
      eapply N.ltb_ge in HB1.
      subst.
      apply/andP; split; ineq_to_prop; eauto.
    }
    case Hle: (n1 <=? n2)%BN.
    {
      exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN  n1)));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n2)));
      (admininstr_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) memarg0);
      (admininstr_STORE I32 (Some (mk_sz 8)) memarg0);
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n1 + 1))));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n2 + 1))));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n3)));
                    admininstr_MEMORY_COPY].
      assert (n3 = ((N.succ n3) - 1)%Z).
      { rewrite Z.sub_1_r.
        rewrite Znat.N2Z.inj_succ.
        rewrite Z.pred_succ.
        by rewrite Znat.N2Z.id.
      }
      rewrite {2}H.
      eapply read.
      eapply memory_copy_le; eauto.
      - apply/eqP. apply N.neq_succ_0.
      - apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
        unfold N_gtb in HB0.
        unfold N_gtb in HB1.
        eapply N.ltb_ge in HB0.
        eapply N.ltb_ge in HB1.
        subst.
        apply/andP; split; ineq_to_prop; eauto.
    }
    {
      exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (((n1 + n3))))));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n2 + n3))));
      (admininstr_LOAD I32 (Some (mk_loadop__0 Inn_I32 (mk_loadop_Inn (mk_sz 8) U))) memarg0);
      (admininstr_STORE I32 (Some (mk_sz 8)) memarg0);
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n1)));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n2)));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n3)));
      admininstr_MEMORY_COPY].
      eapply read.
      assert (n3 = ((N.succ n3) - 1)%Z).
      { rewrite Z.sub_1_r.
        rewrite Znat.N2Z.inj_succ.
        rewrite Z.pred_succ.
        by rewrite Znat.N2Z.id.
      }
      rewrite {2 3 4}H.
      rewrite add_sub_parens.
      rewrite add_sub_parens.
      eapply memory_copy_gt; eauto.
      - apply N.leb_gt in Hle. ineq_to_prop. apply Hle.
      - apply/eqP. apply N.neq_succ_0.
      - apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
        unfold N_gtb in HB0.
        unfold N_gtb in HB1.
        eapply N.ltb_ge in HB0.
        eapply N.ltb_ge in HB1.
        subst.
        apply/andP; split; ineq_to_prop; eauto.
      all: rewrite Z.one_succ;
        rewrite Znat.N2Z.inj_succ;
        rewrite -Z.succ_le_mono;
        apply Znat.N2Z.is_nonneg.
    }
  }
  { (* Instr_ok__memory_init *)
    move => C x mt Hlen Hlookup HRange HData HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2]; eauto.
    rewrite Heqv2.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3]; eauto.
    rewrite Heqv3.

    case Hs: (((n2 + n3) >? (|(datainst_BYTES (fun_data (mk_state s f) x))|))%BN
      || ((n1 + n3 >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN)).
    {
      exists s, f, [admininstr_TRAP].
      eapply read.
      eapply memory_init_trap; eauto.
      econstructor; eauto.
    }
    destruct n3 using N.peano_ind.
    {
      exists s, f, [].
      eapply read.
      eapply memory_init_zero; eauto.
      apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
      unfold N_gtb in HB0.
      unfold N_gtb in HB1.
      eapply N.ltb_ge in HB0.
      eapply N.ltb_ge in HB1.
      subst.
      apply/andP; split; ineq_to_prop; eauto.
    }
    {
      exists s, f, [(admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n1)));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (proj_byte_0 (lookup_total (datainst_BYTES (fun_data (mk_state s f) x)) n2)))));
      (admininstr_STORE I32 (Some (mk_sz 8)) memarg0);
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n1 + 1))));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN (n2 + 1))));
      (admininstr_CONST I32 (mk_num__0 Inn_I32 (mk_uN n3)));
      (admininstr_MEMORY_INIT x)].
      eapply read.
      assert (n3 = ((N.succ n3) - 1)%Z).
      { rewrite Z.sub_1_r.
        rewrite Znat.N2Z.inj_succ.
        rewrite Z.pred_succ.
        by rewrite Znat.N2Z.id.
      }
      rewrite {2}H.
      eapply memory_init_succ; eauto.
      {
        simpl.
        eapply Bool.orb_false_elim in Hs as [Hs1 _].
        simpl in Hs1.
        remember (|(datainst_BYTES (lookup_total (store_DATAS s) (lookup_total (DATAS (frame_MODULE f)) (proj_uN_0 x))))|) as num.
        rewrite N.add_succ_r in Hs1.
        unfold N_gtb in Hs1.
        move/N.ltb_ge in Hs1.
        apply N.le_succ_l in Hs1.
        pose proof (N.le_add_r n2 n3).
        ineq_to_prop.
        eapply N.le_lt_trans; eauto.
      }
      {
        apply/eqP; apply N.neq_succ_0.
      }
      {
        apply orb_false_elim in Hs; destruct Hs as [HB0 HB1].
        unfold N_gtb in HB0.
        unfold N_gtb in HB1.
        eapply N.ltb_ge in HB0.
        eapply N.ltb_ge in HB1.
        subst.
        apply/andP; split; ineq_to_prop; eauto.
      }
    }
  }
  { (* Instr_ok__data_drop *)
    move => C x HRange Hlookup HWfC HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    case Estate: (with_data (mk_state s f) x []) => [s' f'].
    exists s', f', [].
    rewrite -Estate.
    by eapply Step__data_drop.
  }
  { (* Instr_ok__load None *)
    move => C nt memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    case Hs: (((n1 + (proj_uN_0 (OFFSET memarg))) +
    ((((the (res_size (valtype_numtype nt)))) / (8)) : Q)) >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
    + exists s, f, [admininstr_TRAP].
      eapply read.
      eapply load_num_trap; eauto.
      econstructor; eauto.

    + (* in bounds: read the value back out of the byte slice *)
      do 3 eexists.
      eapply read.
      eapply load_num_val; try by [].
      apply/eqP; apply: nbytes_inv.
      apply: list_slice_size.
      rewrite /N_gtb in Hs. move/N.ltb_ge in Hs. by apply: Hs.
    Unshelve.
    apply Inh_nat.  
  }
  { (* Instr_ok__load INN *)
    move => C v_Inn M sx memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    case Hs: (((n1 + (proj_uN_0 (OFFSET memarg)))%BN + (((M) / (8)) : Q))%BN >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
    + exists s, f, [admininstr_TRAP].
      eapply read.
      eapply load_pack_trap; eauto.
      econstructor; eauto.

    + (* in bounds: read the value back out of the byte slice *)
      do 3 eexists.
      eapply read.
      eapply load_pack_val; try by [].
      1: by destruct v_Inn.
      apply/eqP; apply: ibytes_inv.
      apply: list_slice_size.
      rewrite /N_gtb in Hs. move/N.ltb_ge in Hs. by apply: Hs.
  }
  { (* Instr_ok__store None *)
    move => C nt memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    eapply invert_typeof_numtype in Ht2 as [n2 Heqv2]; eauto.
    rewrite Heqv2.
    case Hs: (((n1 + (proj_uN_0 (OFFSET memarg))) + ((((the (res_size (valtype_numtype nt))) : Q) / (8 : Q)) : Q))
      >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
    + exists s, f, [admininstr_TRAP].
      by eapply store_num_trap; eauto.

    + do 3 eexists.
      eapply (store_num_val (mk_state s f)); eauto.
    Unshelve.
    apply Inh_nat.  
  }
  { (* Instr_ok__store INN *)
    move => C Inn M memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    case Hs: (((n1 + (proj_uN_0 (OFFSET memarg))) + (((M) / (8)) : Q))
      >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
    {
      exists s, f, [admininstr_TRAP].
      destruct Inn.
      {
        eapply invert_typeof_I32 in Ht2 as [n2 Heqv2]; eauto.
        assert (I32 = numtype_Inn Inn_I32). { auto. }
        rewrite H in Heqv2.
        rewrite Heqv2.
        eapply store_pack_trap; eauto.
        econstructor; eauto.
      }
      {
        eapply invert_typeof_I64 in Ht2 as [n2 Heqv2]; eauto.
        assert (I64 = numtype_Inn Inn_I64). { auto. }
        rewrite H in Heqv2.
        rewrite Heqv2.
        eapply store_pack_trap; eauto.
        econstructor; eauto.
      }
    }

    destruct Inn.
    {
      eapply invert_typeof_I32 in Ht2 as [n2 Heqv2]; eauto.
      assert (I32 = numtype_Inn Inn_I32). { auto. }
      rewrite H in Heqv2.
      rewrite Heqv2.
      do 3 eexists.
      eapply (store_pack_val (mk_state s f)); eauto.
    }
    {
      eapply invert_typeof_I64 in Ht2 as [n2 Heqv2]; eauto.
      assert (I64 = numtype_Inn Inn_I64). { auto. }
      rewrite H in Heqv2.
      rewrite Heqv2.
      do 3 eexists.
      eapply (store_pack_val (mk_state s f)); eauto.
    }
  }
    (* SIMD *)

  { (* Instr_ok__vload None *)
    move => C memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    case Hs: (((n1 + (proj_uN_0 (OFFSET memarg))) +
      ((((the (res_size valtype_V128))) / (8)) : Q)) >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
    + exists s, f, [admininstr_TRAP].
      eapply read.
      eapply vload_oob; eauto.
      econstructor; eauto.
    + do 3 eexists.
      eapply read.
      eapply Step_read__vload_val; try by [].
      apply/eqP; apply: vbytes_inv.
      apply: list_slice_size.
      rewrite /N_gtb in Hs. move/N.ltb_ge in Hs. by apply: Hs.
    Unshelve.
    apply Inh_nat.
  }


  (* VLOAD (SHAPEX_ ...) and VLOAD (SPLAT ...).  Both need the width operand
     of the load to be the size of some lane type - `jsize v_Jnn == v_M * 2`
     for SHAPEX_, `v_N == jsize v_Jnn` for SPLAT - but `wf_instr` for VLOAD
     (instr_case_58) constrains only the memarg, and neither typing rule
     bounds the width, so e.g. `VLOAD V128 (Some (SPLAT 7)) ao` is well-formed
     and typable with no reduction rule.  (Contrast VLOAD_LANE / VSTORE_LANE,
     whose `wf_sz` premise does pin the width to 8/16/32/64.) *)
  1-2: admit.
  { (* Instr_ok__vload ZERO *)
    move => C v_n memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    case Hs: (((n1 + (proj_uN_0 (OFFSET memarg))) + ((v_n / (8)) : Q))
      >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
    + exists s, f, [admininstr_TRAP].
      eapply read.
      eapply vload_zero_oob; eauto.
      econstructor; eauto.
    + have Hbnd : (((n1 + (proj_uN_0 (OFFSET memarg)))%BN + ((v_n / (8)) : Q))%BN
        <= (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
      { rewrite /N_gtb in Hs. by move/N.ltb_ge in Hs. }
      do 3 eexists.
      eapply read.
      eapply vload_zero_val; try by [].
      * apply/eqP; apply: ibytes_inv. by apply: list_slice_size.
      * eapply inv_ibytes__is_wf; last by apply: eqxx.
        apply: Forall_list_slice.
        by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).
  }


  { (* Instr_ok__vload_lane *)
    move => C v_n memarg laneidx mt Hlen Hlookup HLim Hidx HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    have [c1 [Heqv2 Hwf2]] := invert_typeof_V128 _ Ht2 HP0.
    rewrite Heqv1 Heqv2.
    case Hs: (((n1 + (proj_uN_0 (OFFSET memarg))) + ((v_n / (8)) : Q))
      >? (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
    + exists s, f, [admininstr_TRAP].
      eapply read.
      eapply vload_lane_oob; eauto.
      econstructor; eauto.
    + have Hbnd : (((n1 + (proj_uN_0 (OFFSET memarg)))%BN + ((v_n / (8)) : Q))%BN
        <= (|(BYTES (fun_mem (mk_state s f) (mk_uN 0)))|))%BN.
      { rewrite /N_gtb in Hs. by move/N.ltb_ge in Hs. }
      have Hwfk : wf_uN v_n (inv_ibytes_ v_n
        (list_slice (BYTES (fun_mem (mk_state s f) (mk_uN 0)))
          ((n1 + (proj_uN_0 (OFFSET memarg)))%BN) ((v_n / (8)) : Q))).
      { eapply inv_ibytes__is_wf; last by apply: eqxx.
        apply: Forall_list_slice.
        by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig). }
      have Hsz : wf_sz (mk_sz v_n) by inversion HWfinstr.
      have Hcases : v_n = 8%num \/ v_n = 16%num \/ v_n = 32%num \/ v_n = 64%num.
      { inversion Hsz; subst.
        match goal with
        | [ H : is_true (((_ || _) || _) || _) |- _ ] =>
          move/orP: H => [/orP [/orP [H|H]|H]|H]; move/eqP in H; auto
        end. }
      case: Hcases => [E | [E | [E | E]]]; subst v_n; do 3 eexists; eapply read;
        [ eapply (vload_lane_val (mk_state s f) _ _ _ _ _ _ _ Jnn_I8 16)
        | eapply (vload_lane_val (mk_state s f) _ _ _ _ _ _ _ Jnn_I16 8)
        | eapply (vload_lane_val (mk_state s f) _ _ _ _ _ _ _ Jnn_I32 4)
        | eapply (vload_lane_val (mk_state s f) _ _ _ _ _ _ _ Jnn_I64 2) ].
      all: first
        [ (apply/eqP; apply: ibytes_inv; apply: list_slice_size; by apply: Hbnd)
        | (eapply lane__case_2; [ by rewrite mk_uN_eta; apply: Hwfk | by [] ])
        | by []
        | by apply: eqxx
        | by (econstructor; vm_compute)
        | by (do 2 econstructor) ].
  }
  { (* Instr_ok__vstore *)
    move => C memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr.
    move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    inv_Forall HWfVals.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    rewrite Heqv1.
    have [c2 [Heqv2 Hwf2]] := invert_typeof_V128 _ Ht2 HP0.
    rewrite Heqv2.
    do 3 eexists.

    by eapply (vstore_val (mk_state s f)); eauto.
  }

  (* VSTORE_LANE: `vstore_lane_val` needs
     `proj_lane__2 ((lanes_ (X (lanetype_Jnn J) (mk_dim M)) c) [|j|]) <> None`,
     i.e. that lane in the `mk_lane__2` injection of the generated `lane_`
     union.  `lanes__is_wf` only gives `wf_lane_ (lanetype_Jnn J) l`, which is
     equally satisfied by `mk_lane__1`/`mk_lane__0`, so this is the same
     `lane_`-injection obstacle as the instruction cases above.  Everything
     else in the rule is now discharged (the Q premise reads as Qeq). *)
  1: admit.
  { (* Instrs_ok__empty *)
    move => C s.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left.
  }
  { (* Instrs_ok__seq *)
    move => C bes1 be2 ts1 ts2 ts3 Hinstrs1 IH1 Hinstr2 IH2 HWfC HWfinstrs1 HWfinstrs2.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Ets1 : ts1' = ts1 by case: Htf. rewrite Ets1 in Hts.
    rewrite -be_to_e_cat in Hnotbr Hnotret.
    case Hconst: (const_list (map admininstr_instr bes1)).
    + move/const_es_exists: (Hconst) => [vs1 Hvs1].
      have Hadmin1 : Instrs_ok2 s C (map admininstr_instr bes1) (ts1 :-> ts3).
      { invert_storeok Hstore. apply construct_instrs_from_ais; eauto. }
      have Heqtf2 : (ts3 :-> ts2) = (ts3 :-> ts2) by [].
      have Heqts2 : map typeof (vcs ++ vs1) = ts3.
      { rewrite Hvs1 in Hadmin1.
        eapply ais_vals_typing_inversion in Hadmin1
          as [ts [Hsub HVals]].
        unfold_instrtype_sub Hsub.
        eapply resulttype_sub_empty in Hsub1.
        rewrite Hsub1 cats0 in H. clear Hsub1.
        subst ts0.
        eapply typeof_vals_non_bot in Hts as Htsnonbot.
        eapply resulttype_sub_non_bot in Hsub0; eauto.
        subst ts0_sub.
        eapply Vals_ok_non_bot in HVals as HValsnonbot.
        eapply resulttype_sub_non_bot in Hsub2; eauto.
        subst ts12_sup.
        eapply Forall2_Val_ok_is_same_as_map in HVals.
        rewrite map_cat.
        rewrite HVals.
        rewrite Hts.
        by rewrite H0.
      }
      move: (not_lf_br_left _ _ Hconst Hnotbr) => Hnotbr2.
      move: (not_lf_return_left _ _ Hconst Hnotret) => Hnotret2.
      rewrite map_cat in HWfConfig.
      rewrite Hvs1 in HWfConfig.
      rewrite catA in HWfConfig.
      rewrite -map_cat in HWfConfig.
      apply wf_forall_admin in HWfinstrs1.
      rewrite Hvs1 in HWfinstrs1.
      rewrite -wf_forall_admin_val in HWfinstrs1.
      have HConj : Forall [eta wf_val] vcs  /\ Forall [eta wf_val] vs1 by split; assumption.
      rewrite -Forall_app in HConj.
      move: (IH2 s f C' (vcs ++ vs1) ts3 ts2 lab ret HWfConfig HConj Heqtf2 Hcontext Hmod Heqts2 Hstore Hnotbr2 Hnotret2) => {}IH2.
      case: IH2 => [Hconst2 | Hprog2].
      * left. rewrite -be_to_e_cat Hvs1.
        apply: const_list_concat => //=.
        by apply: v_to_e_const.
      * right.
        rewrite -v_to_e_cat -Hvs1 in Hprog2.
        by rewrite -catA be_to_e_cat in Hprog2.
    + have Heqtf1 : (ts1 :-> ts3) = (ts1 :-> ts3) by [].
      have Heqts1 := Ets1.
      move: (not_lf_br_right _ _ Hnotbr) => Hnotbr1.
      move: (not_lf_return_right _ _ Hnotret) => Hnotret1.
      rewrite map_cat in HWfConfig.
      rewrite catA in HWfConfig.
      apply wf_config_app in HWfConfig; destruct HWfConfig as [HWfC1 HWfC2].
      move: (IH1 s f C' vcs ts1 ts3 lab ret HWfC1 HWfVals Heqtf1 Hcontext Hmod Hts Hstore Hnotbr1 Hnotret1) => {}IH1.
      move: IH1 => [Hcontra | Hprog1]; first by move/negP: Hconst.
      right.
      move: Hprog1 => [s' [f' [es1' Hprog1]]].
      exists s', f', (es1' ++ map admininstr_instr be2).
      rewrite -be_to_e_cat catA.
      eapply Step_is_wf in Hprog1 as HWfStep; eauto.
      destruct be2.
      - repeat rewrite cats0. apply Hprog1.
      - apply ctxt_instrs with (val_lst := []); eauto.
  }
  { (* Instrs_ok__sub *)
    move => C bes ts1'' ts2'' ts1 ts2 HType IH2 HSub1 HSub2 HWfC HWfinstrs.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Ets1 : ts1' = ts1'' by case: Htf. rewrite Ets1 in Hts.
    eapply IH2; eauto.
    eapply typeof_vals_non_bot in Hts as Htsnonbot.
    eapply resulttype_sub_non_bot in HSub1; eauto.
    subst; eauto.
  }
  { (* Instrs_ok__frame *)
    move => C bes ts ts1 ts2 Hinstrs IH HWfC HWfinstrs.
    move => s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* NOTE: This should be named as Instrs_ok__weakening *)
    (* TODO: Get rid of duplicate proof *)
    have Heqtf : (ts1 :-> ts2) = (ts1 :-> ts2) by [].
    have Heqts : map typeof (drop (size ts) vcs) = ts1.
    { rewrite map_drop.
      injection Htf => Htf2 Htf1.
      rewrite -Hts in Htf1. by rewrite -Htf1 drop_cat ltnn subnn drop0. }
    rewrite -(cat_take_drop (size ts) vcs) in HWfConfig.
    rewrite map_cat in HWfConfig.
    rewrite -catA in HWfConfig.
    apply wf_config_app in HWfConfig; destruct HWfConfig as [HWfC1 HWfC2].
    rewrite -(cat_take_drop (size ts) vcs) in HWfVals.
    rewrite Forall_app in HWfVals; destruct HWfVals as [HWfV1 HWfV2].
    move: (IH s f C' (drop (length ts) vcs) ts1 ts2 lab ret HWfC2 HWfV2 Heqtf Hcontext Hmod Heqts Hstore Hnotbr Hnotret) => {}IH.
    have -> : vcs = (take (size ts) vcs ++ drop (size ts) vcs) by rewrite cat_take_drop.
    set vcs1 := take (size ts) vcs in IH *.
    set vcs2 := drop (size ts) vcs in IH *.
    case: IH => [Hconst | Hprog].
    + by left.
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (map admininstr_val vcs1 ++ es').
      rewrite -v_to_e_cat -catA.
      eapply Step_is_wf in IH as HWfStep; eauto.
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[map admininstr_val vcs2 ++ _]cats0.
      rewrite -[map admininstr_val vcs1 ++ es']cats0.
      rewrite -[(map admininstr_val vcs1 ++ es') ++ []]catA.
      destruct vcs1.
      - repeat rewrite cats0. apply IH.
      - apply ctxt_instrs with
        (admininstr_lst := map admininstr_val vcs2 ++ map admininstr_instr bes)
        (admininstr'_lst := es')
        (admininstr_1_lst := []); eauto. 
  }
Admitted.

(* TODO: Similar to admin_instrs_ok_eq *)
Lemma Instr_ok_Instrs_ok: forall C be ts1 ts2,
  Instr_ok C be (ts1 :-> ts2) -> Instrs_ok C [be] (ts1 :-> ts2).
Proof.
  move => C be ts1 ts2 Hinstr.
  apply instr_ok_context_wf in Hinstr as HWf; destruct HWf.
  apply Instrs_ok__instr; eauto.
Qed.

(* NOTE: Mutual induction principle used in t_progress_e *)
Scheme Instr_ok2_ind' := Induction for Instr_ok2 Sort Prop
  with Admin_instrs_ok_ind' := Induction for Instrs_ok2 Sort Prop
  with Expr_ok2_ind' := Induction for Expr_ok2 Sort Prop.

(* MEMO: admininstr_local -> Admininstr__FRAME_ *)
(* MEMO: e_typing -> Instrs_ok2 *)
(* MEMO: store_typing -> Store_ok *)
(* MEMO: reduce -> Step *)
(* MEMO: reduce -> Step_read *)
(* NOTE: lholed is no longer used in specifying opsem
         Use evaluation context E directly *)
(* TODO: Reorder premises in consistent order *)
Lemma t_progress_e: forall s C C' f vcs es tf ts1 ts2 lab ret,
  wf_config (mk_config (mk_state s f) (map admininstr_val vcs ++ es)) ->
  Instrs_ok2 s C es tf ->
  Forall wf_val vcs ->
  tf = (ts1 :-> ts2) ->
  C = (upd_local_label_return C' (map typeof f.(LOCALS)) lab ret) ->
  Moduleinst_ok s f.(frame_MODULE) C' ->
  map typeof vcs = ts1 ->
  Store_ok s ->
  not_lf_br es ->
  not_lf_return es ->
  terminal_form (map admininstr_val vcs ++ es) \/
  exists s' f' es', Step (mk_config (mk_state s f) (map admininstr_val vcs ++ es)) (mk_config (mk_state s' f') es').
Proof.
  move => s C C' f vcs es tf ts1 ts2 lab ret HWfConfig Hadmin.
  move: f C' vcs ts1 ts2 lab ret HWfConfig.
  apply Admin_instrs_ok_ind' with 
    (P := fun s C e tf (Hadmin : Instr_ok2 s C e tf) => 
      forall f C' vcs ts1 ts2 lab ret,
      wf_config (mk_config (mk_state s f) (map admininstr_val vcs ++ [e])) ->
      Forall wf_val vcs ->  
      tf = (ts1 :-> ts2) ->
      C = (upd_local_label_return C' (map typeof f.(LOCALS)) lab ret) ->
      Moduleinst_ok s f.(frame_MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br [e] ->
      not_lf_return [e] ->
      terminal_form (map admininstr_val vcs ++ [e]) \/
      exists s' f' es', Step (mk_config (mk_state s f) (map admininstr_val vcs ++ [e])) (mk_config (mk_state s' f') es'))
    (P0 := fun s C es tf (Hadmin : Instrs_ok2 s C es tf) => 
      forall f C' vcs ts1 ts2 lab ret,
      wf_config (mk_config (mk_state s f) (map admininstr_val vcs ++ es)) ->
      Forall wf_val vcs ->  
      tf = (ts1 :-> ts2) ->
      C = (upd_local_label_return C' (map typeof f.(LOCALS)) lab ret) ->
      Moduleinst_ok s f.(frame_MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br es ->
      not_lf_return es ->
      terminal_form (map admininstr_val vcs ++ es) \/
      exists s' f' es', Step (mk_config (mk_state s f) (map admininstr_val vcs ++ es)) (mk_config (mk_state s' f') es'))
    (P1 := fun s C es ts (Hthread : Expr_ok2 s C es ts) =>
      forall f C' ret,
      wf_config (mk_config (mk_state s f) es) ->         
      C = (upd_return C' ret) ->
      Frame_ok s f C' ->         
      Store_ok s ->
      not_lf_br es ->
      not_lf_return es ->
      (const_list es /\ |es| = |ts|) \/
      es = [admininstr_TRAP] \/
      exists s' f' es', Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')) 
    => // {s C es tf Hadmin}.
  { (* Instr_ok2__instr *)
    move => s C be ts1 ts2 Hinstr HWfS HWfC HWfinstr.
    move => f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Hinstrs: Instrs_ok C [be] (ts1 :-> ts2) by apply Instr_ok_Instrs_ok.
    pose Hprog := t_progress_be s C C' f vcs [be] (ts1 :-> ts2) ts1' ts2' lab ret HWfConfig Hinstrs HWfVals
                    Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: Hprog => [Hconst | Hprog].
    + left. rewrite /terminal_form.
      left. apply: const_list_concat => //=.
      by apply: v_to_e_const.
    + by right.
  }
  { (* Instr_ok2__label *)
    move => s C n bes es t1 t2 Hinstrs IH Hadmin IH' HWfS HWfC HWfinstr HWfC' Hsize.
    move => f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    case: (br_reduce_decidable es) => [Hbrred | Hnotbrred].
    + rewrite /br_reduce in Hbrred.
      move: Hbrred => [vcs' [l [es' Hes]]].
      destruct l.
      destruct i using N.peano_ind.
      * right.
        have Hexists : exists vcs es', es = map admininstr_val vcs ++ [admininstr_BR (mk_uN 0)] ++ es'. 
        { by exists vcs', es'. }
        have Hlookup : lookup_total (LABELS (_append {|
          context_TYPES := [];
          context_FUNCS := [];
          context_GLOBALS := [];
          context_TABLES := [];
          context_MEMS := [];
          context_ELEMS := [];
          context_DATAS := [];
          context_LOCALS := [];
          LABELS := [mk_list _ t2];
          context_RETURN := None
          |} C)) 0 = t2.
        { move => {Hadmin IH} /=.
          by rewrite /lookup_total /=. }
        move: (br_reduce_extract_vs _ _ _ _ _ Hexists Hadmin Hlookup) => Hextract.
        move: Hextract => [vcs1 [vcs2 [es'' [Hes' Hsize']]]].
        rewrite Hes'.
        exists s, f, (map admininstr_val vcs2 ++ map admininstr_instr bes).
        apply: pure.
        repeat rewrite catA.
        eapply br_zero; eq_to_prop; eauto.
        by rewrite Hsize' Hsize.
      * right. exists s, f, (map admininstr_val vcs' ++ [admininstr_BR (mk_uN i)]).
        rewrite -N.add_1_r in Hes.
        rewrite Hes.
        assert (i = ((mk_uN i) :> N)). { auto. }
        rewrite {1}H.
        repeat rewrite catA.
        apply: pure.
        eapply br_succ.
    + case: (return_reduce_decidable es) => [Hretred | Hnotretred].
      * rewrite /return_reduce in Hretred.
        move: Hretred => [vcs' [es' Hes]].
        right. exists s, f, (map admininstr_val vcs' ++ [admininstr_RETURN]).
        rewrite Hes.
        repeat rewrite catA.
        apply: pure.
        eapply return_label.
      * (* TODO: Can we simplify this? *)
        have Heqc : _append {|
          context_TYPES := [];
          context_FUNCS := [];
          context_GLOBALS := [];
          context_TABLES := [];
          context_MEMS := [];
          context_ELEMS := [];
          context_DATAS := [];
          context_LOCALS := [];
          LABELS := [mk_list _ t2];
          context_RETURN := None
          |} C = upd_local_label_return C' [seq typeof i  | i <- LOCALS f] ((mk_list _ t2) :: lab) ret.
          by rewrite Hcontext.
        have Heqtf : ([] :-> t1) = ([] :-> t1) by [].
        have Heqts : map typeof [] = [] by [].
        move/not_br_reduce_not_lf_br: Hnotbrred => Hnotbr'.
        move/not_return_reduce_not_lf_return: Hnotretred => Hnotret'.
        apply wf_config_label in HWfConfig as [HWfCL1 HWfCL2].
        move/(_ f C' [] [] (t1) ((mk_list _ t2) :: lab) ret HWfCL1 HWfVals Heqtf Heqc Hmod Heqts Hstore Hnotbr' Hnotret'): IH' => IH'.
        move => {Heqtf Heqc Hmod Heqts Hstore}.
        case: IH' => [Hterm | Hprog].
        { right. exists s, f, es.
          case: Hterm => /= [Hconst | Htrap].
          - move: (const_es_exists _ Hconst) => [vs Hvs]. rewrite Hvs.
            apply: pure.
            by apply: label_vals.
          - rewrite Htrap.
            apply: pure.
            by apply: trap_label. }
        { right. move: Hprog => [s' [f' [es' IH']]].
          exists s', f', [LABEL_ n bes es'].
          apply: ctxt_label; eauto.
          apply Step_is_wf in IH'; eauto.
        }
  }
  { (* Instr_ok2__frame *)
    move => s C n f es t C' HFrameOk HExprOk IH HWfS HWfC HWfC' HWfinstr HWfC'' Hsize.
    move => f' C'' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    case: (return_reduce_decidable es) => [Hretred | Hnotretred].
    + rewrite /return_reduce in Hretred.
      move: Hretred => [vcs' [es' Hes]].
      right.
      have Hexists : exists vcs es', es = map admininstr_val vcs ++ [admininstr_RETURN] ++ es'.
      { by exists vcs', es'. }
      inversion HExprOk as [? ? ? ? Hadmin HWfSExpr HWfCExpr HWfAdminI]; subst; clear HWfSExpr HWfCExpr. 
      have Hlookup : context_RETURN (_append {|
        context_TYPES := [];
        context_FUNCS := [];
        context_GLOBALS := [];
        context_TABLES := [];
        context_MEMS := [];
        context_ELEMS := [];
        context_DATAS := [];
        context_LOCALS := [];
        LABELS := [];
        context_RETURN := Some (mk_list _ t)
        |} C') = Some (mk_list _ t).
      { move => {Hadmin IH} /=.
        move/frame_t_context_return_empty: HFrameOk => Hret.
        by rewrite Hret. }
      move: (return_reduce_extract_vs _ _ _ _ _ Hexists Hadmin Hlookup) => Hextract.
      move: Hextract => [vcs1 [vcs2 [es'' [Hes' Hsize']]]].
      rewrite Hes'.
      exists s, f', (map admininstr_val vcs2).
      apply: pure.
      repeat rewrite catA.
      apply return_frame.
      by rewrite Hsize' Hsize.
      
    + inversion HExprOk; subst.
      move/not_return_reduce_not_lf_return: Hnotretred => Hnotret'.
      have HFrameOk' := HFrameOk. 
      move/s_typing_not_lf_br: HFrameOk => Hnotbr'.
      apply wf_config_frame in HWfConfig; destruct HWfConfig as [HWfFrame1 HWfFrame2].
      apply (Hnotbr' (mk_list _ t) es [] t) in H0 as Hnotbr''.
      assert (prepend_return C' t = upd_return C' (Some (mk_list _ t))). {
        unfold prepend_return; unfold upd_return.
        unfold set. destruct C'. simpl. reflexivity.
      }
      specialize (IH f C' (Some (mk_list _ t)) HWfFrame2 H HFrameOk' Hstore Hnotbr'' Hnotret').
      case: IH => [[Hconst Hlen] | [Htrap | Hprog]].
      + right. exists s, f', es.
        move: (const_es_exists _ Hconst) => [vs Hvs]. rewrite Hvs.
        apply: pure.
        apply: frame_vals.
        simpl in Hlen.
        eq_to_prop.
        apply f_equal with (f := size) in Hvs.
        rewrite size_map in Hvs.
        rewrite Hsize.
        rewrite -Hlen.
        f_equal.
        exact Hvs.
      + right. exists s, f', [admininstr_TRAP].
        rewrite Htrap.
        apply: pure.
        by apply: trap_frame.
      + right.
        inversion HWfinstr; subst.
        eapply (state_case_0 _ _ HWfS) in H5.
        eapply (config_case_0 _ _ H5) in H8.
        move: Hprog => [s' [f'' [es' Hprog]]].
        exists s', f', [FRAME_ n f'' es'].
        apply: ctxt_frame; eauto.
        eapply Step_is_wf in Hprog; eauto.
  }
  { (* Instr_ok2__call_addr *)
    (* NOTE: admininstr_CALL_ADDR corresponds to invoke instruction *)
    move => s C addr ts1 ts2 Hext HWfS HWfC HWfAIs HWfExtType.
    move => f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    injection Htf => _ Htf1. rewrite -{}Htf1 in Hts.
    eapply Externaddr_invert_funcs in Hext as [xt [funcinst [HBound [HLookup [HEq [HWf HSub]]]]]].
    inversion HSub; subst; apply externtype_func_eq in HSub.
    injection H2 as ?; subst.
    clear H1 H3 H0.
    case Hfuninst: funcinst => [ft minst func].
    eq_to_prop.
    case Hfunc: CODE HLookup => [x ls es] HLookup.
    pose ts := map (fun '(LOCAL t) => t) ls.
    pose f' := (
    {| LOCALS := (vcs ++ (map (fun (t: valtype) => the (default_ t)) ts)); frame_MODULE := minst |}
    ).
    pose f'' := (f' Inhabited__val).
    exists s, f, [FRAME_ (|ts2|) f'' [LABEL_ (|ts2|) [] (map admininstr_instr es)]].
    apply: read.
    assert (map (fun t => LOCAL t) ts = ls) as Hlocal.
    {
      clear -ts.
      rewrite /ts.
      induction ls; auto.
      simpl.
      simpl in ts.
      f_equal; auto.
      by destruct a.
    }
    rewrite Hfuninst in HSub.
    rewrite Hfuninst in HLookup.
    simpl in HSub.
    rewrite HSub in HLookup.
    instantiate (1 := funcinst) in Hfunc.
    rewrite Hfuninst in Hfunc; simpl in Hfunc.
    assert (Forall (fun t => default_ t != None) ts) as HNotNone.
    {
      rewrite -Hlocal in Hfunc.
      rewrite Hfunc in HLookup.
      clear Hlocal.
      invert_storeok Hstore.
      eapply Forall2_size in HFunc.
      2: apply HBound.
      rewrite HLookup in HFunc.
      inversion HFunc; subst.
      inversion H6; eq_to_prop; subst.
      apply inj_map in H0; subst.
      apply default_not_none; eauto.
      apply LOCAL_injective.
    }
    
    eapply call_addr with
      (t_lst := ts)
    ; eq_to_prop; ineq_to_prop; eauto. 
    {
      rewrite {1}Hlocal.
      apply Hfunc.
    }

    1,2,3 :
      inversion HWfS;
      rewrite -H4 in HBound; simpl in HBound;
      rewrite -H4 in HLookup; simpl in HLookup;
      eapply Forall_size in H; eauto;
      rewrite HLookup in H; inversion H.
    - exact H.
    - rewrite Hlocal. by rewrite -Hfunc.
    {
      econstructor; eauto.
      apply Forall_app; split; eauto.
      clear -HNotNone.
      induction HNotNone => //=.
      apply Forall_cons; eauto.
      eapply default__is_wf; eauto.
    }
    {
      by rewrite size_map.
    }
  }
  { (* Instr_ok2__ref *)
    move => s C ref rt HRefOk HWfS HWfC.
    move => f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    left.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.
    rewrite /terminal_form.
    destruct ref; by left.
  }
  { (* Instr_ok2__trap *)
    move => s C ts1 ts2 HWfS HWfC HWfinstr.
    move => f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: vcs Hts HWfConfig HWfVals => [ | vc vcs] Hts HWfConfig HWfVals //=.
    + left. rewrite /terminal_form. by right.
    + right. exists s, f, [admininstr_TRAP].
      apply: pure.
      rewrite -cat_cons.
      rewrite -{1}(cats0 [admininstr_TRAP]).
      assert (map admininstr_val (vc :: vcs) =
        admininstr_val (vc) :: map admininstr_val (vcs)).
      {
        auto.
      }
      rewrite -H.
      eapply trap_vals with
        (val_lst := vc :: vcs)
        (admininstr_lst := [])
        ; eauto.
  }
  { (* Admin_instrs_ok__empty *)
    move => s C HWfS HWfC.
    move => f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    left. rewrite cats0 /terminal_form.
    left. by apply: v_to_e_const.
  }
  { (* Instrs_ok2__seq *)
    move => s C es1 e2 ts1 ts2 ts3 Hadmin1 IH1 Hadmin2 IH2 HWfS HWfC HWfinstrs1 HWfinstrs2.
    move => f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Ets1 : ts1' = ts1 by case: Htf. rewrite Ets1 in Hts.
    case Hconst: (const_list es1).
    + move/const_es_exists: (Hconst) => [vs1 Hvs1].
      have Heqtf2 : (ts3 :-> ts2) = (ts3 :-> ts2) by [].
      have Heqts2 : map typeof (vcs ++ vs1) = ts3.
      { rewrite Hvs1 in Hadmin1.
        eapply ais_vals_typing_inversion in Hadmin1
          as [ts [Hsub HVals]].
        unfold_instrtype_sub Hsub.
        eapply resulttype_sub_empty in Hsub1.
        rewrite Hsub1 cats0 in H. clear Hsub1.
        subst ts0.
        eapply typeof_vals_non_bot in Hts as Htsnonbot.
        eapply resulttype_sub_non_bot in Hsub0; eauto.
        subst ts0_sub.
        eapply Vals_ok_non_bot in HVals as HValsnonbot.
        eapply resulttype_sub_non_bot in Hsub2; eauto.
        subst ts12_sup.
        eapply Forall2_Val_ok_is_same_as_map in HVals.
        rewrite map_cat Hts HVals.
        done.
      }
      move: (not_lf_br_left _ _ Hconst Hnotbr) => Hnotbr2.
      move: (not_lf_return_left _ _ Hconst Hnotret) => Hnotret2.
      rewrite Hvs1 in HWfConfig.
      rewrite catA in HWfConfig.
      rewrite -map_cat in HWfConfig.
      rewrite Hvs1 in HWfinstrs1.
      rewrite -wf_forall_admin_val in HWfinstrs1.
      have HConj : Forall [eta wf_val] vcs  /\ Forall [eta wf_val] vs1 by split; assumption.
      rewrite -Forall_app in HConj.
      move/(_ f C' (vcs ++ vs1) ts3 ts2 lab ret HWfConfig HConj Heqtf2 Hcontext Hmod Heqts2 Hstore Hnotbr2 Hnotret2): IH2 => IH2.
      case: IH2 => [Hterm2 | Hprog2].
      * case: Hterm2 => [Hconst2 | Htrap2].
        { left. left.
          by rewrite catA Hvs1 v_to_e_cat. }
        { left. right.
          rewrite map_cat in Htrap2.
          by rewrite -catA -Hvs1 in Htrap2.
        }
      * right. by rewrite catA Hvs1 v_to_e_cat.
    + have Heqtf1 : (ts1 :-> ts3) = (ts1 :-> ts3) by [].
      have Heqts1 := Ets1.
      move: (not_lf_br_right _ _ Hnotbr) => Hnotbr1.
      move: (not_lf_return_right _ _ Hnotret) => Hnotret1.
      rewrite catA in HWfConfig.
      apply wf_config_app in HWfConfig; destruct HWfConfig as [HWfC1 HWfC2].
      move/(_ f C' vcs ts1 ts3 lab ret HWfC1 HWfVals Heqtf1 Hcontext Hmod Hts Hstore Hnotbr1 Hnotret1): IH1 => IH1.
      have IH' := IH1.
      case: IH1 => [Hterm1 | Hprog1].
      * case: Hterm1 => [Hconst1 | Htrap1].
        { rewrite const_list_cat in Hconst1.
          move/andP: Hconst1 => [Hconst1 Hconst1'].
          by move/negP: Hconst. }
        { destruct e2 => //=.
          - rewrite cats0. apply IH'.
          right. move: (v_e_trap _ _ (v_to_e_const vcs) Htrap1) => [-> ->] //=.
          exists s, f, [admininstr_TRAP].
          apply: pure.
          rewrite -cat1s.
          eapply trap_vals with (val_lst := []).
          done.
        }
      * destruct e2. { rewrite cats0. apply IH'. }
          
        right. move: Hprog1 => [s' [f' [es1' Hprog1]]].
        exists s', f', (es1' ++ (a :: e2)).
        rewrite catA.
        apply ctxt_instrs with (val_lst := []); eauto.
        apply Step_is_wf in Hprog1; eauto.
  }
  { (* Instrs_ok2_sub *)
    move => s C es ts1'' ts2'' ts1 ts2 Hadmin IH HSub1 HSub2 HWfS HWfC HWfAIs.
    move => f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Ets1 : ts1'' = ts1' by case: Htf. subst ts1''.
    eapply IH; eauto.
    eapply typeof_vals_non_bot in Hts as Hnonbot.
    eapply resulttype_sub_non_bot in HSub1; eauto.
    by subst ts1'.
  }
  { (* Instrs_ok2__frame *)
    move => s C es ts ts1 ts2 Hadmin IH HWfS HWfC HWfAIs.
    move => f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* NOTE: This is equivalent to Instr_ok2__weakening but for Instrs_ok2 *)
    (* TODO: Get rid of duplicate proof *)
    have Heqtf : (ts1 :-> ts2) = (ts1 :-> ts2) by [].
    have Heqts : map typeof (drop (size ts) vcs) = ts1.
    { rewrite map_drop.
      injection Htf => Htf2 Htf1.
      rewrite -Hts in Htf1. by rewrite -Htf1 drop_cat ltnn subnn drop0. }
    rewrite -(cat_take_drop (size ts) vcs) in HWfConfig.
    rewrite map_cat in HWfConfig.
    rewrite -catA in HWfConfig.
    apply wf_config_app in HWfConfig; destruct HWfConfig as [HWfC1 HWfC2].
    rewrite -(cat_take_drop (size ts) vcs) in HWfVals.
    rewrite Forall_app in HWfVals; destruct HWfVals as [HWfV1 HWfV2].
    move/(_ f C' (drop (size ts) vcs) ts1 ts2 lab ret HWfC2 HWfV2 Heqtf Hcontext Hmod Heqts Hstore Hnotbr Hnotret): IH => IH.
    have -> : vcs = (take (size ts) vcs ++ drop (size ts) vcs) by rewrite cat_take_drop.
    set vcs1 := take (size ts) vcs in IH *.
    set vcs2 := drop (size ts) vcs in IH *.
    case: IH => [Hterm | Hprog].
    + case: Hterm => [Hconst | Htrap].
      * left. left.
        rewrite -v_to_e_cat -catA.
        apply const_list_concat => //=.
        by apply v_to_e_const.
      * rewrite -v_to_e_cat -catA Htrap.
        case: vcs1 => /= [ | vc1 vcs1].
        { left. by right. }
        { right. exists s, f, [admininstr_TRAP].
          apply: pure.
          apply trap_vals with (val_lst := (vc1 :: vcs1)).
          done.
        }
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (map admininstr_val vcs1 ++ es').
      rewrite -v_to_e_cat -catA.
      eapply Step_is_wf in IH as HWfStep; eauto.
      rewrite -[map admininstr_val vcs2 ++ _]cats0.
      rewrite -[map admininstr_val vcs1 ++ es']cats0.
      rewrite -[(map admininstr_val vcs1 ++ es') ++ []]catA.
      destruct vcs1.
      - repeat rewrite cats0. apply IH.
      apply ctxt_instrs with
        (admininstr_lst := map admininstr_val vcs2 ++ es)
        (admininstr'_lst := es')
        (admininstr_1_lst := []); eauto.
  }
  { (* Expr_ok2 *)
    move=> s C es ts Hadmin IH HWfS HWfC HWfAIs.
    move => f C' ret HWfConfig HEq HFrameOk Hstore Hnotbr Hnotret.
    inversion HFrameOk; subst.
    remember {| LOCALS := val_lst; frame_MODULE := v_moduleinst |} as f.
    remember {|
            context_TYPES := [::];
            context_FUNCS := [::];
            context_GLOBALS := [::];
            context_TABLES := [::];
            context_MEMS := [::];
            context_ELEMS := [::];
            context_DATAS := [::];
            context_LOCALS := t_lst;
            LABELS := [::];
            context_RETURN := None
      |} as C_tlst.
    pose proof (Forall_nil wf_val) as HNil.
    assert (upd_return (C_tlst @@ C0) ret = upd_local_label_return C0 [seq typeof i | i <- LOCALS f] [::] ret) as HEq'.
    {
      unfold upd_local_label_return; unfold upd_label; unfold upd_local; unfold upd_return.
      unfold set; subst; simpl.
      unfold _append; unfold Append_List_.
      assert (context_LOCALS C0 = []) as HLocals. { by inversion H. }
      repeat rewrite cat0s.
      rewrite HLocals.
      rewrite cats0.
      eapply frame_t_context_label_empty in HFrameOk; simpl in HFrameOk.
      unfold _append in HFrameOk; unfold Append_List_ in HFrameOk.
      rewrite cat0s in HFrameOk.
      rewrite HFrameOk.
      assert (t_lst = seq.map typeof val_lst) as HEq. {
        clear -H1.
        induction H1 => //=.
        inversion H; subst; simpl; f_equal.
        inversion H0; eauto.
      }
      by rewrite HEq.
    }
    assert ((frame_MODULE f) = v_moduleinst). { rewrite Heqf; eauto. }
    rewrite -H6 in H.
    specialize (IH f C0 [] [] ts [] ret HWfConfig HNil erefl HEq' H erefl Hstore Hnotbr Hnotret).
    simpl in IH.
    unfold terminal_form in IH.
    case: IH => [[Hconst | HTrap] | HProg].
    - left. split => //=.
      move/const_es_exists: Hconst => [vs Hvs].
      rewrite Hvs in Hadmin *.
      eapply ais_vals_typing_inversion in Hadmin as [v_ts [HSub HVals]].
      eapply instrtype_sub_iff_resulttype_sub in HSub.
      eapply Forall2_seq_size in HVals.
      assert (|v_ts| = |ts|) as HSizets. { by inversion HSub; eq_to_prop. }
      by rewrite size_map -HVals HSizets.
    - by right; left.
    - by right; right.
  }
Qed.

Theorem t_progress: forall s f es ts,
  Config_ok (mk_config (mk_state s f) es) ts ->
  terminal_form es \/
  exists s' f' es', Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es').
Proof.
  move => s f es ts Hconfig.
  (* TODO: inversion tactic can be replaced by case tactic
           by introducing equalities on dependent indices of the premise
           and rejecting contradictory cases manually *)
  inversion Hconfig as [? ? ? ? ? Hstate Hthread HWfC' HWfConfig HWfState]; subst.
  inversion Hstate as [? ? ? HStore HFrame HWfC'' HWfState']; subst.
  inversion Hthread as [? ? ? ? Hadmin HWfS HWfC HWfAIs]; subst.
  clear HWfS HWfC' HWfC'' HWfAIs HWfState HWfState'.
  (* TODO: apply with tactic can be replaced by apply: tactic *)
  eapply t_progress_e with
    (lab := []) (ret := None)
    (vcs := []) (ts1 := []) (ts2 := t_lst)
    (C' := upd_local_label_return C [] [] None) => //=.
  - move/frame_t_context_local_types: (HFrame) => Eloc.
    move/frame_t_context_label_empty: (HFrame) => Elab.
    move/frame_t_context_return_empty: (HFrame) => Eret.
    unfold upd_local_label_return.
    unfold upd_label. unfold upd_local. unfold upd_return.
    unfold set. simpl.
    rewrite -Elab -Eret -Eloc.
    destruct C; apply Hadmin.
  - inversion HFrame as [? ? ? ? ? Hmod] => {HFrame}.
    by inversion Hmod.
  - by apply (s_typing_not_lf_br' _ _ _ _ _ _ HFrame) in Hadmin.
  - by apply (s_typing_not_lf_return _ _ _ _ _ _ HFrame) in Hadmin.
Qed.

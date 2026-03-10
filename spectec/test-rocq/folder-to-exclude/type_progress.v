From Stdlib Require Import String List Unicode.Utf8 NArith Arith.
From RecordUpdate Require Import RecordSet.

Declare Scope wasm_scope.
Open Scope wasm_scope.
Import ListNotations.
Import RecordSetNotations.
(* TODO: Is Notation global? *)
(* TODO: Is Coercion global? *)
From WasmSpectec Require Import wasm.
From WasmSpectec Require Import helper_lemmas helper_tactics typing_lemmas extension_lemmas subtyping.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.

(* NOTE: Naming conventions:
         1. type for types
         2. type__constructor for types with multiple constructors
         3. type__ for types with a single constructor *)

(* NOTE: Comment out below to display coercions in proof state *)
(* Set Printing Coercions. *)
(* NOTE: Comment out below to display parentheses in proof state *)
(* Set Printing Parentheses. *)

(* TODO: Use SSReflect seq operations in generated coercions *)
Lemma map_map {A B : Type} (f : A -> B) (s : seq A) : List.map f s = map f s.
Proof. by []. Qed.

Lemma length_size {A : Type} (s : seq A) : Datatypes.length s = size s.
Proof. by []. Qed.

Lemma cat_app {A : Type} (s1 s2 : seq A) : List.app s1 s2 = cat s1 s2.
Proof. by []. Qed.

Lemma cat_nil : forall T (s1 s2 : seq T),
  (s1 ++ s2) = [] <-> s1 = [] /\ s2 = [].
Proof.
  move => T s1 s2. split.
  - by case: s1; case s2.
  - by move => [-> ->].
Qed.

Definition is_const (e : admininstr) : bool :=
  match e with
  | AI_CONST _ _ => true
  | AI_VCONST _ _ => true
  | AI_REF_NULL _ => true
  | AI_REF_FUNC_ADDR _ => true
  | AI_REF_HOST_ADDR _ => true
  | _ => false
  end.

Definition const_list (es : list admininstr) : bool :=
  List.forallb is_const es.

Lemma v_to_e_const: forall vs,
    const_list (map fun_coec_val__admininstr vs).
Proof.
  move => vs. elim: vs => //=.
  move => v vs Hconst.
  case v => //=.
Qed.

(* NOTE: const_list es is coerced into proposition by is_true *)
Definition terminal_form (es : list admininstr) :=
  const_list es \/ es = [AI_TRAP].

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
    {vs | es = map fun_coec_val__admininstr vs}.
Proof.
  induction es => //=.
  - by exists [].
  - move => HConst.
    move/andP in HConst. destruct HConst as [? HConst].
    destruct a => //=;
    apply IHes in HConst as [vs ->].
    + by exists (VAL_CONST v_numtype v_num_ :: vs).
    + by exists (VAL_VCONST v_vectype v_vec_ :: vs).
    + by exists (VAL_REF_NULL v_reftype :: vs).
    + by exists (VAL_REF_FUNC_ADDR v_funcaddr :: vs).
    + by exists (VAL_REF_HOST_ADDR v_hostaddr :: vs).
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
    Step_pure (vs ++ [AI_TRAP]) [AI_TRAP].
Proof.
  move => vs HConst H.
  apply const_es_exists in HConst as [vcs ->].
  eapply step_trap_vals with (v_val := vcs) (v_admininstr := []) => //=.
  left. by apply/map_neq_nil: H.
Qed.

(* TODO: Rename this lemma more appropriately *)
Lemma v_e_trap: forall vs es,
    const_list vs ->
    vs ++ es = [AI_TRAP] ->
    vs = [] /\ es = [AI_TRAP].
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
    map fun_coec_val__admininstr vs1 ++ map fun_coec_val__admininstr vs2 =
    map fun_coec_val__admininstr (vs1 ++ vs2).
Proof.
  move => vs1. elim: vs1 => //=.
  - move => a l IH vs2. by rewrite IH.
Qed.

Lemma be_to_e_cat: forall bes1 bes2,
    map fun_coec_instr__admininstr bes1 ++ map fun_coec_instr__admininstr bes2 =
    map fun_coec_instr__admininstr (bes1 ++ bes2).
Proof.
  move => bes1. elim: bes1 => //=.
  - move => a l IH bes2. by rewrite IH.
Qed.

Lemma to_e_list_cat: forall bes1 bes2,
    map fun_coec_instr__admininstr (bes1 ++ bes2) = 
    map fun_coec_instr__admininstr bes1 ++ map fun_coec_instr__admininstr bes2.
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

Definition typeof (v_val : wasm.val): valtype :=
	match v_val with
		| VAL_CONST t _ => t
		| VAL_VCONST t _ => t
		| VAL_REF_NULL t => t
		| VAL_REF_FUNC_ADDR _ => VALTYPE_FUNCREF
		| VAL_REF_HOST_ADDR _ => VALTYPE_EXTERNREF
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
  elim/last_ind: ts2 => [| ts2' t IH].
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

(* NOTE: Given Hts : [seq typeof i  | i <- vcs] = [t],
         generates equalities on elements of vcs like [v1] = [t] and typeof v1 = t *)
Ltac invert_typeof_vcs :=
  lazymatch goal with
  | H: map typeof ?vcs = [_; _; _] |- _ =>
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
    case: vcs H => [| v1 vcs1] H //=;
    case: vcs1 H => [| v2 vcs2] H //=;
    case: vcs2 H => [| v3 vcs3] H //=;
    case: vcs3 H => [| v4 vcs4] H //=;
    case: H => Ht1 Ht2 Ht3
  | H: map typeof ?vcs = [_; _] |- _ =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let v3 := fresh "v3" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let vcs3 := fresh "vcs3" in
    let Ht1 := fresh "Ht1" in
    let Ht2 := fresh "Ht2" in
    case: vcs H => [| v1 vcs1] H //=;
    case: vcs1 H => [| v2 vcs2] H //=;
    case: vcs2 H => [| v3 vcs3] H //=;
    case: H => Ht1 Ht2
  | H: map typeof ?vcs = [_] |- _ =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in 
    let vcs1 := fresh "vcs1" in
    let vcs2 := fresh "vcs2" in
    let Ht1 := fresh "Ht1" in
    case: vcs H => [| v1 vcs1] H //=;
    case: vcs1 H => [| v2 vcs2] H //=;
    case: H => Ht1
  | H: map typeof ?vcs = [] |- _ =>
    let v1 := fresh "v1" in 
    let vcs1 := fresh "vcs1" in
    (* NOTE: This performs injection on Hts : [seq typeof i  | i <- vcs] = [t1] *)
    case: vcs H => [| v1 vcs1] H //=
  end.

Lemma invert_typeof_I32: forall v,
  typeof v = VALTYPE_I32 ->
  exists v',
    fun_coec_val__admininstr v = (AI_CONST I32 (mk_uN 32 v')).
Proof.
  move => v Ht.
  destruct v; rewrite /typeof in Ht; try by discriminate.
  - destruct v_numtype; try discriminate.
    destruct v_num_.
    by exists v_i.
  - destruct v_vectype; by discriminate.
  - destruct v_reftype; by discriminate.
Qed.

Lemma invert_typeof_I64: forall v,
  typeof v = VALTYPE_I64 ->
  exists v',
    fun_coec_val__admininstr v = (AI_CONST I64 (mk_uN 64 v')).
Proof.
  move => v Ht.
  destruct v; rewrite /typeof in Ht; try by discriminate.
  - destruct v_numtype; try discriminate.
    destruct v_num_.
    by exists v_i.
  - destruct v_vectype; by discriminate.
  - destruct v_reftype; by discriminate.
Qed.

Lemma invert_typeof_numtype: forall v (t: numtype),
  typeof v = t ->
  exists (n: num_ t),
    fun_coec_val__admininstr v = (AI_CONST t n).
Proof.
  move => v t Ht.
  destruct v; rewrite /typeof in Ht; try by destruct t; discriminate.
  {
    destruct v_numtype; simpl in Ht; destruct t; try discriminate;
    exists v_num_; auto.
  }
  - destruct v_vectype; destruct t; discriminate.
  - destruct v_reftype; destruct t; discriminate.
Qed.

Lemma invert_typeof_reftype: forall v (t: reftype),
  typeof v = t ->
  ( fun_coec_val__admininstr v = (AI_REF_NULL t) ) \/
  ( exists x,
    fun_coec_val__admininstr v = (AI_REF_FUNC_ADDR x) \/
    fun_coec_val__admininstr v = (AI_REF_HOST_ADDR x) 
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
  typeof v = t ->
  ( exists r,
    fun_coec_val__admininstr v = fun_coec_ref__admininstr r).
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
    - by exists (REF_NULL FUNCREF).
    - by exists (REF_NULL EXTERNREF).
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
  i + j <= size bs ->
  size (list_slice bs i j) = j.
Proof.
  move => T bs.
  elim: bs => [| b bs' IH].
  - move => /= i j H.
    have H' := leq_addl i j.
    move: (leq_trans H' H) => {}H.
    rewrite (leqn0 j) in H.
    by move/eqP in H.
  - move => /= i j H.
    case: i H => [| i'] H; case: j H => [| j'] H //=.
    + congr S. by apply: IH.
    + apply: IH.
      rewrite -[i'.+1]addn1 -[(size bs').+1]addn1 in H.
      rewrite -addnA -[1 + j'.+1]addnC addnA in H.
      by rewrite (leq_add2r 1) in H.
Qed.

(* NOTE: Mutual induction principle used in t_progress_be *)
Scheme Instr_ok_ind' := Induction for Instr_ok Sort Prop
  with Instrs_ok_ind' := Induction for Instrs_ok Sort Prop.

Definition br_reduce es := 
  exists vcs l es',
  es = map fun_coec_val__admininstr vcs ++ [AI_BR l] ++ es'.

Definition return_reduce es :=
  exists vcs es',
  es = map fun_coec_val__admininstr vcs ++ [AI_RETURN] ++ es'.

(* NOTE: We could define this as ~ (br_reduce es) *)
Definition not_lf_br es :=
  forall vcs l es',
  es <> map fun_coec_val__admininstr vcs ++ [AI_BR l] ++ es'.

(* NOTE: We could define this as ~ (br_reduce es) *)
Definition not_lf_return es :=
  forall vcs es',
  es <> map fun_coec_val__admininstr vcs ++ [AI_RETURN] ++ es'.

(* TODO: Define this in wasm.v *)
Fixpoint split_vals (es : seq admininstr) : seq (wasm.val) * seq admininstr :=
  match es with
  | (AI_CONST t v) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((VAL_CONST t v) :: vs', es'')
  | (AI_VCONST t v) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((VAL_VCONST t v) :: vs', es'')
  | (AI_REF_NULL t) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((VAL_REF_NULL t) :: vs', es'')
  | (AI_REF_FUNC_ADDR t) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((VAL_REF_FUNC_ADDR t) :: vs', es'')
  | (AI_REF_HOST_ADDR t) :: es' =>
    let: (vs', es'') := split_vals es' in
    ((VAL_REF_HOST_ADDR t) :: vs', es'')
  | _ => ([], es)
  end.

Lemma split_vals_inverse : forall vs es es',
  split_vals es = (vs, es') ->
  es = map fun_coec_val__admininstr vs ++ es'.
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
  split_vals (map fun_coec_val__admininstr vs ++ [e] ++ es) = (vs, [e] ++ es).
Proof.
  move => vs e es H.
  elim: vs => [| v vs'].
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
  case Ees': es' => [| e es''].
  - right. move => [vcs [l [es''' Hcontra]]].
    rewrite Hcontra in Ees.
    rewrite (split_vals_prefix vcs (AI_BR l) es''') in Ees; last by [].
    case: Ees => Hvs Hes'.
    by rewrite Ees' in Hes'.
  - (* TODO: Use case tactic instead *)
    destruct e;
    try (right;
         move => [vcs [li [es''' Hcontra]]];
         rewrite Hcontra in Ees;
         rewrite (split_vals_prefix vcs (AI_BR li) es''') in Ees; last by [];
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
  case Ees': es' => [| e es''].
  - right. move => [vcs [es''' Hcontra]].
    rewrite Hcontra in Ees.
    rewrite (split_vals_prefix vcs (AI_RETURN) es''') in Ees; last by [].
    case: Ees => Hvs Hes'.
    by rewrite Ees' in Hes'.
  - (* TODO: Use case tactic instead *)
    destruct e;
    try (right;
         move => [vcs [es''' Hcontra]];
         rewrite Hcontra in Ees;
         rewrite (split_vals_prefix vcs (AI_RETURN) es''') in Ees; last by [];
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
  not_lf_br [e] -> e <> AI_BR l.
Proof.
  move => e l H Hcontra.
  rewrite Hcontra /not_lf_br in H.
  by move/(_ [] l []): H => H.
Qed.

Lemma not_lf_return_singleton : forall e,
  not_lf_return [e] -> e <> AI_RETURN.
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
	List.map typeof v_local_vals = v_t1.
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
  C_LOCALS C = map typeof (F_LOCALS f).
Proof.
	move => s i C Hframe.
  inversion Hframe as [? ? ? ? ? Hmod ? Hval].
  inversion Hmod => //=.
  rewrite /_append /Append_List_ cat_app cats0.
  by eapply Forall2_Val_ok_is_same_as_map in Hval.
Qed.

Lemma frame_t_context_label_empty: forall s f C,
	Frame_ok s f C ->
  C_LABELS C = [].
Proof.
  move => s i C Hframe.
  inversion Hframe as [? ? ? ? ? Hmod ? Hval].
  by inversion Hmod.
Qed.

Lemma frame_t_context_return_empty: forall s f C,
	Frame_ok s f C ->
  C_RETURN C = None.
Proof.
  move => s i C Hframe.
  inversion Hframe as [? ? ? ? ? Hmod ? Hval].
  by inversion Hmod.
Qed.

(* TODO: Duplicate of admin_composition_typing_single? *)
Lemma Admin_instrs_ok_rcons : forall s C es e ts1 ts2,
  Admin_instrs_ok s C (es ++ [e]) (ts1 :-> ts2) ->
  exists ts ts1' ts2' ts3,
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Admin_instrs_ok s C es (ts1' :-> ts3) /\
    Admin_instr_ok s C e (ts3 :-> ts2').
Proof.
  move => s C es e ts1 ts2 Hadmin.
  eapply ais_seq_typing_inversion in Hadmin as [t3s [H1 H2]].
  exists [], ts1, ts2, t3s.
  split. auto.
  split. auto.
  split. auto.
  by eapply ais_single_typing_inversion'.
Qed.
    
(* TODO: Duplicate ofadmin_composition_typing?  *)
Lemma Admin_instrs_ok_cat : forall s C es1 es2 ts1 ts2,
  Admin_instrs_ok s C (es1 ++ es2) (ts1 :-> ts2) -> 
  exists ts ts1' ts2' ts3,
    ts1 = ts ++ ts1' /\
    ts2 = ts ++ ts2' /\
    Admin_instrs_ok s C es1 (ts1' :-> ts3) /\
    Admin_instrs_ok s C es2 (ts3 :-> ts2').
Proof.
  move => s C es1 es2 ts1 ts2 Hadmin.
  move: s C es1 ts1 ts2 Hadmin.
  (* NOTE: Induction on list es2 in reverse direction 
           which works better with AIs_ok_seq and Admin_instrs_ok_rcons *)
  elim/last_ind: es2 => [| es2' e2 IH].
  - move => s C es1 ts1 ts2 Hadmin.
    exists [], ts1, ts2, ts2.
    do ! split => //=.
    + by rewrite cats0 in Hadmin.
    + rewrite -[ts2]cats0.
      apply: AIs_ok_frame.
      by apply: AIs_ok_empty.
  - move => s C es1 ts1 ts2 Hadmin.
    rewrite -cats1 catA in Hadmin *.
    move/Admin_instrs_ok_rcons: Hadmin => [ts [ts1' [ts2' [ts3 [Ets1 [Ets2 [Hadmin1 Hadmin2]]]]]]].
    move/(_ s C es1 ts1' ts3 Hadmin1): IH => [ts' [ts1'' [ts2'' [ts3' [Ets1' [Ets2' [Hadmin1' Hadmin2']]]]]]].
    move/(AIs_ok_frame _ _ _ ts'): Hadmin1' => Hadmin1'. rewrite -Ets1' in Hadmin1'.
    move/(AIs_ok_frame _ _ _ ts'): Hadmin2' => Hadmin2'. rewrite -Ets2' in Hadmin2'.
    move: (AIs_ok_seq _ _ _ e2 _ ts2' _ Hadmin2' Hadmin2) => {}Hadmin2'.
    exists ts, ts1', ts2', (ts' ++ ts3').
    by do ! split => //=.
Qed.

Lemma Admin_instrs_ok_all : forall s C es ts1 ts2,
  Admin_instrs_ok s C es (ts1 :-> ts2) -> 
  (* TODO: Rewrite with all *)
  forall e, e \in es -> exists ts1' ts2', Admin_instr_ok s C e (ts1' :-> ts2').
Proof.
  (* TODO: Make use of `+` elsewhere *)
  move => + + es.
  elim/last_ind: es => [| es' e'].
  - move => s C ts1 ts2 Hadmin e Hin.
    by rewrite in_nil in Hin.
  - move => IH s C ts1 ts2 Hadmin e Hin.
    rewrite mem_rcons in_cons in Hin.
    rewrite -cats1 in Hadmin.
    move/Admin_instrs_ok_rcons: Hadmin => [ts [ts1' [ts2' [ts3 [Ets1 [Ets2 [Hadmin1 Hadmin2]]]]]]].
    move/orP: Hin => [Hin1 | Hin2].
    + move/eqP: Hin1 => Hin1.
      rewrite Hin1.
      by exists ts3, ts2'.
    + move/IH: Hadmin1 => {}IH. 
      by move/(_ e Hin2): IH => IH.
Qed.

Lemma s_typing_lf_br : forall s rs f es ts l,
  (* NOTE: Here rs should not be None unlike s_typing_lf_return
           because we not only use s_typing_lf_br in t_progress to reject top-level occurrences of br
           but also to reject occurrences of br directly within frame t_progress_e *)
  Thread_ok s rs f es ts ->
  Forall (fun e => e <> AI_BR l) es.
Proof.
  move => s rs f es ts l Hthread.
  inversion Hthread as [? ? ? ? ? C Hframe Hadmin Hs Hrs Hf Hes Hts] => {Hthread} //=.
  rewrite ?{}Hs ?{}Hrs ?{}Hf ?{}Hes ?{}Hts in Hframe Hadmin.
  destruct ts.
  move/Admin_instrs_ok_all: Hadmin => Hadmin.
  elim: es Hadmin => [| e' es' IH] Hadmin; first by apply: Forall_nil.
  apply: Forall_cons.
  - move => Hcontra.
    have Hin : e' \in e' :: es'.
    { rewrite in_cons. apply/orP. by left. }
    move/(_ e' Hin): Hadmin => [ts1' [ts2' Hadmin]].
    rewrite Hcontra in Hadmin.
    move Ec: (_append {|
      C_TYPES := [];
      C_FUNCS := [];
      C_GLOBALS := [];
      C_TABLES := [];
      C_MEMS := [];
      C_LOCALS := [];
      C_LABELS := [];
      C_RETURN := rs
      |} C) Hadmin => C' Hadmin.
    move Ee: (AI_BR l) Hadmin => e Hadmin.
    move Etf: (ts1' :-> ts2') Hadmin => tf Hadmin.
    move: ts1' ts2' Hframe IH Ec Ee Etf.
    (* TODO: Avoid using destruct *)
    destruct e'; elim: s C' e tf / Hadmin => //= [
      s C' be tf Hinstr |
      s C' e ts' ts1 ts2 Hadmin IH' ].    
    (* NOTE: Deriving contradiction on C_LABELS C = [] *)
    + move => ts1' ts2' Hframe IH Ec Ee Etf.
      (* TODO: Avoid using destruct *)
      (* TODO: Extract this into a lemma for other instructions too? *)
      have Hbr : be = instr_BR l.
      { destruct be => //=.
        case El: (l == v_labelidx0); move/eqP: El => El.
        - by rewrite El.
        - by inversion Ee. }
      rewrite Hbr in Hinstr.
      inversion Hinstr.
      rewrite -Ec /= in H0.
      move/frame_t_context_label_empty: Hframe => Hlab.
      rewrite Hlab length_size /= in H0.
      by rewrite ltn0 in H0.
    + move => vt2 HType IHH HSub1 HSub2 HSub3.
      move => ts1' ts2' Hframe IH Ec Ee Etf.
      by eapply IHH => //=.
  - apply: IH. move => e Hin.
    have Hin' : e \in e' :: es'.
    { rewrite in_cons. apply/orP. by right. }
    by move/(_ e Hin'): Hadmin.
Qed.

Lemma s_typing_lf_return : forall s f es ts,
  Thread_ok s None f es ts ->
  Forall (fun e => e <> AI_RETURN) es.
Proof.
  move => s f es ts Hthread.
  inversion Hthread as [? ? ? ? ? C Hframe Hadmin Hs Hrs Hf Hes Hts] => {Hthread} //=.
  rewrite ?{}Hs ?{}Hrs ?{}Hf ?{}Hes ?{}Hts in Hframe Hadmin.
  destruct ts.
  move/Admin_instrs_ok_all: Hadmin => Hadmin.
  elim: es Hadmin => [| e' es' IH] Hadmin; first by apply: Forall_nil.
  apply: Forall_cons.
  - move => Hcontra.
    have Hin : e' \in e' :: es'.
    { rewrite in_cons. apply/orP. by left. }
    move/(_ e' Hin): Hadmin => [ts1' [ts2' Hadmin]].
    rewrite Hcontra in Hadmin.
    move Ec: (_append {|
      C_TYPES := [];
      C_FUNCS := [];
      C_GLOBALS := [];
      C_TABLES := [];
      C_MEMS := [];
      C_LOCALS := [];
      C_LABELS := [];
      C_RETURN := None
      |} C) Hadmin => C' Hadmin.
    move Ee: (AI_RETURN) Hadmin => e Hadmin.
    move Etf: (ts1' :-> ts2') Hadmin => tf Hadmin.
    move: ts1' ts2' Hframe IH Ec Ee Etf.
    (* TODO: Avoid using destruct *)
    destruct e'; elim: s C' e tf / Hadmin => //= [
      s C' be tf Hinstr |
      s C' e ts' ts1 ts2 Hadmin IH' ].    
    (* NOTE: Deriving contradiction on C_LABELS C = [] *)
    + move => ts1' ts2' Hframe IH Ec Ee Etf.
      (* TODO: Avoid using destruct *)
      (* TODO: Extract this into a lemma for other instructions too? *)
      have Hbr : be = instr_RETURN. { by destruct be => //=. }
      rewrite Hbr in Hinstr.
      inversion Hinstr.
      rewrite -Ec /= in H.
      move/frame_t_context_return_empty: Hframe => Hret.
      by rewrite Hret in H.
    + move => vt2 HType IHH HSub1 HSub2 HSub3.
      move => ts1' ts2' Hframe IH Ec Ee Etf.
      by apply: IHH => //=.
  - apply: IH. move => e Hin.
    have Hin' : e \in e' :: es'.
    { rewrite in_cons. apply/orP. by right. }
    by move/(_ e Hin'): Hadmin.
Qed.

Lemma s_typing_not_lf_br : forall s rs f es ts,
  Thread_ok s rs f es ts ->
  not_lf_br es.
Proof.
  move => s rs f es ts Hthread.
  move/s_typing_lf_br: Hthread => Hes.
  rewrite /not_lf_br. move => vcs l es' Hcontra.
  move: es es' Hes Hcontra.
  elim: vcs => /= [| vc vcs' IH].
  - move => es es' Hes Hcontra. 
    move/(_ l): Hes => Hes. rewrite Hcontra in Hes.
    by inversion Hes => //=.
  - move => es es' Hes Hcontra.
    case: es Hes Hcontra => // [e' es] Hes Hcontra.
    move/(_ es es'): IH => IH.
    apply: IH => //=.
    + move => l'. move/(_ l'): Hes => Hes.
      by inversion Hes.
    + by inversion Hcontra.
Qed.

Lemma s_typing_not_lf_return : forall s f es ts,
  Thread_ok s None f es ts ->
  not_lf_return es.
Proof.
  move => s f es ts Hthread.
  move/s_typing_lf_return: Hthread => Hes.
  rewrite /not_lf_return. move => vcs es' Hcontra.
  move: es es' Hes Hcontra.
  elim: vcs => /= [| vc vcs' IH].
  - move => es es' Hes Hcontra. 
    rewrite Hcontra in Hes.
    by inversion Hes => //=.
  - move => es es' Hes Hcontra.
    case: es Hes Hcontra => // [e' es] Hes Hcontra.
    move/(_ es es'): IH => IH.
    apply: IH => //=.
    + by inversion Hes.
    + by inversion Hcontra.
Qed.

Lemma size_eq1_cat: forall A (l1 l2 l1' l2': list A),
  size l1' = size l2' ->
  l1' ++ l1 = l2' ++ l2 ->
  l1' = l2' /\ l1 = l2.
Proof.
  move=> A l1 l2 l1' l2' Hsize Hcat.

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
    es = map fun_coec_val__admininstr vcs ++ [AI_BR 0] ++ es') -> 
  Admin_instrs_ok s C es ([] :-> ts2) -> 
  lookup_total (C_LABELS C) 0 = ts ->
  (exists vcs1 vcs2 es',
    es = map fun_coec_val__admininstr vcs1 ++ map fun_coec_val__admininstr vcs2
      ++ [AI_BR 0] ++ es' /\
    size vcs2 = size ts).
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
  2: { by inversion Hsub. }
  subst ts_sub ts11_sub.
  rewrite catA in HValsok.
  eapply Forall2_length in HValsok.
  rewrite !length_size size_cat in HValsok.
  assert (size (ts ++ extr) <= size vcs).
  {
    rewrite -HValsok.
    eapply leq_addr.
  }

  exists (take (size (ts ++ extr)) vcs), (drop (size (ts ++ extr)) vcs), es'.
  split.
  - by rewrite !catA -map_cat cat_take_drop.
  - rewrite size_drop.
    rewrite -HValsok.
    rewrite add_sub' /=.
    by destruct (lookup_total (C_LABELS C) 0).
Qed.

Lemma return_reduce_extract_vs : forall s C ts2 t es,
  (* TODO: This first premise is equal to return_reduce *)
  (exists vcs es',
    es = map fun_coec_val__admininstr vcs ++ [AI_RETURN] ++ es') -> 
  Admin_instrs_ok s C es ([] :-> ts2) -> 
  C_RETURN C = Some t ->
  (exists vcs1 vcs2 es',
    es = map fun_coec_val__admininstr vcs1 ++ map fun_coec_val__admininstr vcs2 ++ [AI_RETURN] ++ es' /\
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
  2: { by inversion Hsub. }
  subst ts_sub ts11_sub.
  rewrite catA in HValsok.
  eapply Forall2_length in HValsok.
  rewrite !length_size size_cat in HValsok.
  assert (size (ts ++ extr) <= size vcs).
  {
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
  Module_instance_ok s (F_MODULE f) C ->
  lookup_total (C_TYPES (upd_local_label_return C loc lab ret)) idx =
  lookup_total (MODULE_TYPES (F_MODULE f)) idx.
Proof.
  move => s f C loc lab ret idx HMinst.
  inversion HMinst.
  by rewrite /=.
Qed.

Lemma funcs_size: forall s f C loc lab ret,
  Module_instance_ok s (F_MODULE f) C ->
  size (C_FUNCS (upd_local_label_return C loc lab ret)) =
    size (MODULE_FUNCS (F_MODULE f)).
Proof.
  move => s f C loc lab ret HMinst.
  inversion HMinst.
  by rewrite /=.
Qed.

Parameter dummy_i32: {numtype & (num_ numtype)}.

Definition load_ai_const_pack (i: admininstr) : {t: numtype & (num_ t)} :=
  match i with
  | AI_CONST t i =>
      existT _ t i
  | _ => dummy_i32
  end.

Lemma ai_const_eq_arg: forall t i1 i2,
	AI_CONST t i1 = AI_CONST t i2 ->
	(i1 = i2).
Proof.
	move => t i1 i2 Hargeq.
	apply (f_equal load_ai_const_pack) in Hargeq.
	simpl in Hargeq.
	apply Eqdep_dec.inj_pair2_eq_dec in Hargeq; auto.
	decide equality.
Qed.

Lemma typeof_non_bot: forall v,
  typeof v <> VALTYPE_BOT.
Proof.
  destruct v; rewrite /typeof; try discriminate.
    - by destruct v_numtype.
    - by destruct v_vectype.
    - by destruct v_reftype.
Qed.

Lemma typeof_vals_non_bot: forall vs ts,
  map typeof vs = ts ->
  Forall (fun t => t <> VALTYPE_BOT) ts.
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

(* TODO: Two major facts to be proven:
         1. v_n in AI_LABEL is equal to the length of types in
            C_LABELS of context used to validate AI_BR inside the label
         2. if vcs ++ AI_BR is well-typed then length of vcs must be
            greater than or equal to the length of types in C_LABELS of context
            used to validate vcs ++ AI_BR *)

(* MEMO: be_typing -> Instrs_ok *)
(* MEMO: f.(f_inst) -> f.(F_MODULE) *)
(* TODO: Reorder premises in consistent order *)
Lemma t_progress_be: forall s C C' f vcs bes tf ts1 ts2 lab ret,
  Instrs_ok C bes tf ->
  tf = (ts1 :-> ts2) ->
  C = (upd_local_label_return C' (map typeof f.(F_LOCALS)) lab ret) ->
  Module_instance_ok s f.(F_MODULE) C' ->
  map typeof vcs = ts1 ->
  Store_ok s ->
  not_lf_br (map fun_coec_instr__admininstr bes) ->
  not_lf_return (map fun_coec_instr__admininstr bes) ->
  const_list (map fun_coec_instr__admininstr bes) \/
  exists s' f' es', Step (mk_config (mk_state s f) (map fun_coec_val__admininstr vcs ++ map fun_coec_instr__admininstr bes)) (mk_config (mk_state s' f') es').
Proof.
  move => s C C' f vcs bes tf ts1 ts2 lab ret Hinstrs.
  move: s f C' vcs ts1 ts2 lab ret.
  apply Instrs_ok_ind' with 
    (P := fun C be tf (Hinstr : Instr_ok C be tf) => 
      forall s f C' vcs ts1 ts2 lab ret,
      tf = (ts1 :-> ts2) ->
      C = (upd_local_label_return C' (map typeof f.(F_LOCALS)) lab ret) ->
      Module_instance_ok s f.(F_MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br (map fun_coec_instr__admininstr [be]) ->
      not_lf_return (map fun_coec_instr__admininstr [be]) ->
      const_list (map fun_coec_instr__admininstr [be]) \/
      exists s' f' es', Step (mk_config (mk_state s f) (map fun_coec_val__admininstr vcs ++ map fun_coec_instr__admininstr [be])) (mk_config (mk_state s' f') es'))
    (P0 := fun C bes tf (Hinstrs : Instrs_ok C bes tf) =>
      forall s f C' vcs ts1 ts2 lab ret,
      tf = (ts1 :-> ts2) ->
      C = (upd_local_label_return C' (map typeof f.(F_LOCALS)) lab ret) ->
      Module_instance_ok s f.(F_MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br (map fun_coec_instr__admininstr bes) ->
      not_lf_return (map fun_coec_instr__admininstr bes) ->
      const_list (map fun_coec_instr__admininstr bes) \/
      exists s' f' es', Step (mk_config (mk_state s f) (map fun_coec_val__admininstr vcs ++ map fun_coec_instr__admininstr bes)) (mk_config (mk_state s' f') es'))
      => // {C bes tf Hinstrs}.
  - (* Instr_ok__nop *)
    move => C.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* TODO: Can we get rid of ++ [] in exists? *)
    right. exists s, f, (map fun_coec_val__admininstr vcs ++ [] ++ []).
    apply step_ctxt_seq with
      (v_admininstr := [AI_NOP]).
    by apply: step_pure step_nop.
  - (* Instr_ok__unreachable *)
    move => C ts1 ts2.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* TODO: Can we get rid of ++ [] in exists? *)
    right. exists s, f, (map fun_coec_val__admininstr vcs ++ [AI_TRAP] ++ []).
    apply step_ctxt_seq with
      (v_admininstr := [AI_UNREACHABLE]).
    by apply: step_pure step_unreachable.
  - (* Instr_ok__drop *)
    move => C t.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    (* TODO: Replace injection in other places with case
              e.g. injection Htf => _ Htf1. rewrite -{}Htf1 in Hts. *)
    (* TODO: Use invert_typeof_vcs in t_progress_e too. *)
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    exists s, f, [].
    apply: step_pure.
    by apply: step_drop.
  - (* Instr_ok__select Some *)
    move => C t.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht3 as [n3 Ht3]. rewrite /= in Ht3. rewrite Ht3.
    clear Ht3.
    case: n3 => [| n3'].
    - exists s, f, (map fun_coec_val__admininstr [v2]).
      apply: step_pure.
      by apply: step_select_false.
    - exists s, f, (map fun_coec_val__admininstr [v1]).
      apply: step_pure.
      by apply: step_select_true.
  - (* Instr_ok__select None*)
    move => C t t' nt vt HVsub Hteq.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht3 as [n3 Ht3]. rewrite /= in Ht3. rewrite Ht3.
    clear Ht3.
    case: n3 => [| n3'].
    - exists s, f, (map fun_coec_val__admininstr [v2]).
      apply: step_pure.
      by apply: step_select_false.
    - exists s, f, (map fun_coec_val__admininstr [v1]).
      apply: step_pure.
      by apply: step_select_true.
  - (* Instr_ok__block *)
    move => C bt bes vt1 vt2 HBok HType IHH.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. exists s, f,
      [AI_LABEL_ (size vt2) [] (map fun_coec_val__admininstr vcs ++ (map fun_coec_instr__admininstr bes))].
    case: Htf => Htf1 _. rewrite -Htf1 in Hts.
    apply: step_read.
    eapply step_block with
      (v_z := (mk_state s f))
      (v_val := vcs)
      (v_bt := bt)
      (v_instr := bes)
      (v_n := (size vt2))
      (v_t_1 := vt1)
      (v_t_2 := vt2)
      ; eauto.
    + rewrite /fun_blocktype. inversion HBok; subst.
      * by destruct v_valtype; eauto.
      * rewrite /fun_type.
        erewrite <- lookup_types; eauto.
    + by rewrite -Hts length_size size_map.
  - (* Instr_ok__loop *)
    move => C bt bes vt1 vt2 HBok HType IHH.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. exists s, f,
      [AI_LABEL_ (size vt1) [(instr_LOOP bt bes)] (map fun_coec_val__admininstr vcs ++ (map fun_coec_instr__admininstr bes))].
    case: Htf => Htf1 _. rewrite -Htf1 in Hts.
    apply: step_read.
    eapply step_loop with
      (v_z := (mk_state s f))
      (v_val := vcs)
      (v_bt := bt)
      (v_instr := bes)
      (v_k := (size vt1))
      (v_t_1 := vt1)
      (v_t_2 := vt2)
      ; eauto.
    + rewrite /fun_blocktype. inversion HBok; subst.
      * by destruct v_valtype; eauto.
      * rewrite /fun_type.
        erewrite <- lookup_types; eauto.
    + by rewrite -Hts length_size size_map.
    + by rewrite -Hts length_size size_map.
  - (* Instr_ok__if *)
    move => C bt bes1 bes2 vt1 vt2 HBok HType IHH HType2 IHH2.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts.
    eapply typeof_append in Hts as [v [Hvcs [Hvs1 Hvs2]]].
    eapply invert_typeof_I32 in Hvs2 as [n Heqv].
    rewrite Hvcs map_cat /= Heqv -catA.
    clear Heqv.
    case: n => [| n'].
    - exists s, f, ((map fun_coec_val__admininstr (take (size vt1) vcs)) ++
        [AI_BLOCK bt bes2]).
      rewrite -(cats0 [AI_BLOCK bt bes2])
        -(cats0 ([AI_CONST I32 (mk_uN 32 0)] ++ [AI_IFELSE bt bes1 bes2])).
      eapply step_ctxt_seq.
      apply: step_pure.
      by apply: step_if_false.
    - exists s, f, ((map fun_coec_val__admininstr (take (size vt1) vcs)) ++
        [AI_BLOCK bt bes1]).
      rewrite -(cats0 [AI_BLOCK bt bes1])
        -(cats0 ([AI_CONST I32 (mk_uN 32 n'.+1)] ++ [AI_IFELSE bt bes1 bes2])).
      eapply step_ctxt_seq.
      apply: step_pure.
      by apply: step_if_true.
  - (* Instr_ok__br *)
    move => C l ts1 ts ts2 Hlablen Hlablookup.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    move/not_lf_br_singleton: Hnotbr => Hnotbr.
    by move/(_ l): Hnotbr.
  - (* Instr_ok__br_if *)
    move => C l ts Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]].
    eapply invert_typeof_I32 in Ht1 as [n Heqv].
    rewrite Hvcs map_cat /= Heqv -catA.
    rewrite -(cats0 ([AI_CONST I32 (mk_uN 32 n)] ++ [AI_BR_IF l])).
    clear Heqv.
    case: n => [| n'].
    + exists s, f, (map fun_coec_val__admininstr (take (size ts) vcs)
        ++ [] ++ []).
      eapply step_ctxt_seq.
      eapply step_pure.
      by eapply step_br_if_false.
    + exists s, f, (map fun_coec_val__admininstr (take (size ts) vcs)
        ++ [(AI_BR l)] ++ []).
      eapply step_ctxt_seq.
      eapply step_pure.
      by eapply step_br_if_true.
  - (* Instr_ok__br_table *)
    move => C ls lN ts1 ts ts2 HlenlN Hlenls HlookuplN Hlookupls.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    rewrite catA in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]].
    eapply invert_typeof_I32 in Ht1 as [n Heqv].
    rewrite Hvcs map_cat /= Heqv -catA.
    rewrite -(cats0 ([AI_CONST I32 (mk_uN 32 n)] ++ [AI_BR_TABLE ls lN])).
    case Hv1: (n < size ls).
    + exists s, f, (map fun_coec_val__admininstr (take (size (ts1 ++ ts)) vcs)
      ++ [AI_BR (lookup_total ls n)] ++ []).
      eapply step_ctxt_seq.
      eapply step_pure.
      by eapply step_br_table_lt.
    + exists s, f, (map fun_coec_val__admininstr (take (size (ts1 ++ ts)) vcs)
      ++ [AI_BR lN] ++ []).
      eapply step_ctxt_seq.
      eapply step_pure.
      eapply step_br_table_ge.
      by rewrite length_size leqNgt Hv1.
  - (* Instr_ok__call *)
    move => C x ts1 ts2 Haddr Hlookup.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* TODO: Can we get rid of ++ [] in exists? *)
    right. exists s, f, (map fun_coec_val__admininstr vcs ++ [AI_CALL_ADDR (lookup_total (fun_funcaddr (mk_state s f)) x)] ++ []).
    (* TODO: Can we get rid of these rewrites? *)
    rewrite -[map fun_coec_val__admininstr vcs ++ _]cats0 -catA.
    apply step_ctxt_seq with
      (v_admininstr := [AI_CALL x]).
    apply: step_read. apply: step_call.
    rewrite !length_size in Haddr *.
    rewrite /fun_funcaddr.
    rewrite Hcontext in Haddr.
    erewrite <- funcs_size; eauto.
  { (* Instr_ok__call_indirect *)
    move => C x y ts1 ts2 lim HSizex HLookupx HSizey HLookupy.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    (* TODO: Make use of typeof_append in t_progress_e too *)
    case: Htf => Htf1 _. rewrite -{}Htf1 in Hts.
    move/typeof_append: Hts => [v1 [Hvcs [Hts Ht1]]].
    eapply invert_typeof_I32 in Ht1 as [n Heqv].
    remember (mk_uN 32 n) as v_i.
    rewrite Hvcs map_cat /= Heqv -catA.
    rewrite -(cats0 ([AI_CONST I32 v_i] ++ [AI_CALL_INDIRECT x y])).
    eapply minst_invert_tables
      with (C' := C)
      in Hmod.
    2: {
      subst;
      resolve_inst_match.
    }
    eapply Forall2_nth2 in Hmod as [_ HTables].
    eapply HTables in HSizex as
      [rt [lim1 [lim2 [tbr [HRangex [HTabletype [_ HSLookupx]]]]]]].

    case E3: ((fun_proj_uN_0 32 v_i) < Datatypes.length (TAB_REFS (fun_table (mk_state s f) x))).
    case E1: (lookup_total (TAB_REFS (fun_table (mk_state s f) x)) (fun_proj_uN_0 32 v_i)) => [| a |].
    {
      exists s, f, (map fun_coec_val__admininstr (take (size ts1) vcs)
        ++ ([AI_TRAP] ++ []));
      eapply step_ctxt_seq;
      eapply step_read;
      eapply step_call_indirect_trap.
      move => HContra.
      remember (AI_CONST I32 v_i) as instr_i.
      inversion HContra.
      rewrite Heqinstr_i in H0.
      eapply ai_const_eq_arg in H0; subst.
      rewrite E1 in H4; discriminate.
      Unshelve.
      exact Inhabited__ref.
    }
    case E4: (a < Datatypes.length (fun_funcinst (mk_state s f))).
    case E2: (fun_type (mk_state s f) y == FUNC_TYPE (lookup_total (fun_funcinst (mk_state s f)) a)).
    {
      exists s, f, (map fun_coec_val__admininstr (take (size ts1) vcs)
        ++ ([AI_CALL_ADDR a] ++ [])).
      eapply step_ctxt_seq.
      eapply step_read.
      eapply step_call_indirect_call; eauto.
      by move/eqP in E2.
      Unshelve.
      exact Inhabited_funcinst.
    }
    all: move/ltP in E3;
      try move/ltP in E4;
      try move/eqP in E2.
    all: exists s, f, (map fun_coec_val__admininstr (take (size ts1) vcs)
        ++ ([AI_TRAP] ++ []));
      eapply step_ctxt_seq;
      eapply step_read;
      eapply step_call_indirect_trap.
    all: move => HContra.
    all: remember (AI_CONST I32 v_i) as instr_i.
    all: inversion HContra.
    all: rewrite Heqinstr_i in H0.
    all: eapply ai_const_eq_arg in H0; subst.
    {
      rewrite E1 in H4.
      inversion H4; subst; clear H4.
      contradiction.
    }
    {
      rewrite E1 in H4.
      inversion H4; subst; clear H4.
      move/ltP in H5.
      contradiction.
    }
    {
      rewrite E1 in H4.
      inversion H4; subst; clear H4.
    }
    {
      move/ltP in H3.
      contradiction.
    }
  }
  - (* Instr_ok__return *)
    move => C ts1 ts ts2 Hretts.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by move/not_lf_return_singleton: Hnotret.
  - (* Instr_ok__const *)
    move => C t vc.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left. 
  - (* Instr_ok__unop *)
    move => C t unop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_numtype in Ht1 as [n Heqv1].
    rewrite Heqv1.
    case Eunop: (fun_unop_ t unop n) => [ | c].
    + exists s, f, [AI_TRAP].
      apply: step_pure.
      by apply: step_unop_trap.
    + exists s, f, [AI_CONST t c].
      apply: step_pure.
      apply: step_unop_val.
      * by rewrite Eunop.
      * rewrite Eunop. by econstructor.
  - (* Instr_ok__binop *)
    move => C t binop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_numtype in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_numtype in Ht2 as [n2 Heqv2].
    rewrite Heqv2.
    case Ebinop: (fun_binop_ t binop n1 n2) => [| c].
    + exists s, f, [AI_TRAP].
      apply: step_pure.
      by apply: step_binop_trap.
    + exists s, f, [AI_CONST t c].
      apply: step_pure.
      apply: step_binop_val.
      * by rewrite Ebinop.
      * rewrite Ebinop. by econstructor.
  - (* Instr_ok__testop *)
    move => C t testop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_numtype in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    move Etestop: (fun_testop_ t testop n1) => c.
    exists s, f, [AI_CONST (INN_I32) c].
    apply: step_pure.
    by apply: step_testop.
  - (* Instr_ok__relop *)
    move => C t relop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right. 
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_numtype in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_numtype in Ht2 as [n2 Heqv2].
    rewrite Heqv2.
    move Erelop: (fun_relop_ t relop n1 n2) => c.
    exists s, f, [AI_CONST (INN_I32) c].
    apply: step_pure.
    by apply: step_relop.
  - (* Instr_ok__cvtop *)
    move => C t2' t1' cvtop.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_numtype in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    case Ecvtop: (fun_cvtop__ t1' t2' cvtop n1) => [| c].
    + exists s, f, [AI_TRAP].
      apply: step_pure.
      by apply: step_cvtop_trap.
    + exists s, f, [AI_CONST t2' c].
      apply: step_pure.
      apply: step_cvtop_val.
      * by rewrite Ecvtop.
      * rewrite Ecvtop. by econstructor.
  - (* Instr_ok__ref_null *)
    move => C rt.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left.
  - (* Instr_ok__ref_func *)
    move => C x ft Hxrange Heft.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    rewrite Hcontext in Hxrange.
    eapply funcs_size in Hmod.
    rewrite length_size in Hxrange.
    erewrite Hmod in Hxrange.
    exists s, f, ([AI_REF_FUNC_ADDR (lookup_total (fun_funcaddr (mk_state s f))
      (fun_proj_uN_0 32 x))]).
    apply: step_read.
    apply: step_ref_func.
    by rewrite /fun_funcaddr length_size.
  { (* Instr_ok__ref_is_null *)
    move => C rt.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_reftype in Ht1 as [Hnull | Hnonnull].
    - exists s, f, ([(AI_CONST I32 (mk_uN _ 1))]).
      apply: step_pure.
      assert (fun_coec_val__admininstr v1 = fun_coec_ref__admininstr (REF_NULL rt)).
      {
        auto.
      }
      rewrite H.
      by eapply step_ref_is_null_true.
    - exists s, f, ([(AI_CONST I32 (mk_uN _ 0))]).
      apply: step_pure.
      destruct Hnonnull as [x [Hf | Hh]].
      {
        assert (fun_coec_val__admininstr v1 =
          fun_coec_ref__admininstr (REF_FUNC_ADDR x)).
        {
          auto.
        }
        rewrite H.
        eapply step_ref_is_null_false.
        move => HContra.
        inversion HContra; subst.
        inversion H0.
      }
      {
        assert (fun_coec_val__admininstr v1 =
          fun_coec_ref__admininstr (REF_HOST_ADDR x)).
        {
          auto.
        }
        rewrite H.
        eapply step_ref_is_null_false.
        move => HContra.
        inversion HContra; subst.
        inversion H0.
      }
  }
  (* SIMD *)
  1-20: admit.
  - (* Instr_ok__local_get *)
    move => C x t Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    exists s, f, (map fun_coec_val__admininstr [fun_local (mk_state s f) x]).
    apply: step_read.
    by apply: step_local_get.
  - (* Instr_ok__local_set *)
    move => C x t Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    (* TODO: Does set/pose tactic support destructuring? *)
    case Estate: (fun_with_local (mk_state s f) x v1) => [s' f'].
    exists s', f', [].
    rewrite -Estate.
    by apply: step_local_set.
  - (* Instr_ok__local_tee *)
    move => C x t Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    exists s, f, [fun_coec_val__admininstr v1; fun_coec_val__admininstr v1; AI_LOCAL_SET x].
    apply: step_pure.
    by apply: step_local_tee.
  - (* Instr_ok__global_get *)
    move => C x t mut Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    exists s, f, (map fun_coec_val__admininstr [GLOB_VALUE (fun_global (mk_state s f) x)]).
    apply: step_read.
    by apply: step_global_get.
  - (* Instr_ok__global_set *)
    move => C x t Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    (* TODO: Does set/pose tactic support destructuring? *)
    case Estate: (fun_with_global (mk_state s f) x v1) => [s' f'].
    exists s', f', [].
    rewrite -Estate.
    by apply: step_global_set.
  - (* Instr_ok__table_get *)
    move => C x rt lim Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n Heqv].
    rewrite Heqv.
    case Es : (n < (List.length (TAB_REFS (fun_table (mk_state s f) x)))).
    - exists s, f, [((lookup_total (TAB_REFS (fun_table (mk_state s f) x)) n) : admininstr)].
      eapply step_read.
      by eapply step_table_get_val.
    - exists s, f, [AI_TRAP].
      eapply step_read.
      eapply step_table_get_trap.
      by rewrite leqNgt Es.
  - (* Instr_ok__table_set *)
    move => C x rt lim Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_reftype' in Ht2 as [r2 Heqv2].
    rewrite Heqv2.
    case Es : (n1 < (List.length (TAB_REFS (fun_table (mk_state s f) x)))).
    - case Estate: (fun_with_table (mk_state s f) x n1 r2) => [s' f'].
      exists s', f', [].
      rewrite -Estate.
      by eapply step_table_set_val.
    - exists s, f, [AI_TRAP].
      eapply step_table_set_trap.
      by rewrite leqNgt Es.
  - (* Instr_ok__table_size *)
    move => C x lim rt Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply minst_invert_tables
      with (C' := C) 
      in Hmod.
    2: {
      subst. by resolve_inst_match.
    }
    eapply Forall2_nth2 in Hmod as [_ HTable].
    eapply HTable in Hlen as [rt1 [lim1 [lim2 [tbr [HRange [HLookup [HLim HLookup2]]]]]]].
    exists s, f, [(AI_CONST I32 (mk_uN _ (length tbr)))].
    eapply step_read.
    eapply step_table_size.
    by rewrite /fun_table HLookup2 /=.
  - (* Instr_ok__table_grow *)
    (* Always fail *)
    move => C x rt lim Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_reftype' in Ht1 as [r1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2].
    rewrite Heqv2.
    exists s, f, [(AI_CONST I32 (mk_uN _ (fun_inv_signed_ 32 (0 - (1 : nat)))))].
    by eapply step_table_grow_fail.
  - (* Instr_ok__table_fill *)
    move => C x rt lim Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_reftype' in Ht2 as [r2 Heqv2].
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3].
    rewrite Heqv3.
    case Hs: ((n1 + n3) >
      (List.length (TAB_REFS (fun_table (mk_state s f) x)))).
    {
      exists s, f, [AI_TRAP].
      eapply step_read.
      by eapply step_table_fill_trap.
    }
    case Hn: (n3) => [| n3'].
    {
      exists s, f, [].
      eapply step_read.
      eapply step_table_fill_zero; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 0)) as instr_3.
      inversion HContra.
      rewrite Heqinstr_1 in H1.
      eapply ai_const_eq_arg in H1.
      rewrite Heqinstr_3 in H3.
      eapply ai_const_eq_arg in H3; subst.
      inversion H3; subst; clear H3.
      move/ltP in H0.
      move/ltP in Hs.
      by contradiction.
    }
    {
      exists s, f, [(AI_CONST I32 (mk_uN 32 n1)); (v2 : admininstr);
      (AI_TABLE_SET x); (AI_CONST I32 (mk_uN _ (n1 + 1)));
      (v2 : admininstr); (AI_CONST I32 (mk_uN _ (n3')));
      (AI_TABLE_FILL x)].
      assert (n3' = n3 - 1). { subst. by rewrite /subn /= Nat.sub_0_r. }
      eapply step_read.
      rewrite {2}H -{1}Hn.
      eapply step_table_fill_succ.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n3)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H1.
        eapply ai_const_eq_arg in H1.
        rewrite Heqinstr_3 in H4.
        eapply ai_const_eq_arg in H4; subst.
        discriminate.
      }
      {
        rewrite Heqinstr_1 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H4.
        eapply ai_const_eq_arg in H4; subst.
        injection H4 as H4.
        subst.
        simpl in *.
        move/ltP in H1.
        move/ltP in Hs.
        by contradiction.
      }
    }
  - (* Instr_ok__table_copy *)
    move => C x1 x2 lim1 rt lim2 Hlenx1 Hlookupx1 Hlenx2 Hlookupx2.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2].
    rewrite Heqv2.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3].
    rewrite Heqv3.
    case Hs: (((n2 + n3) > (List.length (TAB_REFS (fun_table (mk_state s f) x2)))) ||
      ((n1 + n3) > (List.length (TAB_REFS (fun_table (mk_state s f) x1))))).
    {
      exists s, f, [AI_TRAP].
      eapply step_read.
      eapply step_table_copy_trap.
      by move/orP in Hs.
    }
    case Hn: (n3) => [| n3'].
    {
      exists s, f, [].
      eapply step_read.
      eapply step_table_copy_zero; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 0)) as instr_3.
      inversion HContra.
      rewrite Heqinstr_1 in H1.
      rewrite Heqinstr_2 in H2.
      rewrite Heqinstr_3 in H3.
      eapply ai_const_eq_arg in H1; subst.
      eapply ai_const_eq_arg in H2; subst.
      eapply ai_const_eq_arg in H3; subst.
      inversion H3; subst.
      by move/orP in Hs.
    }
    case Hle: ((n1 <= n2)).
    {
      exists s, f, [(AI_CONST I32 (mk_uN 32 n1)); (AI_CONST I32 (mk_uN 32 n2)); (AI_TABLE_GET x2); (AI_TABLE_SET x1); (AI_CONST I32 (mk_uN _ (n1 + 1))); (AI_CONST I32 (mk_uN _ (n2 + 1))); (AI_CONST I32 (mk_uN _ (n3 - 1))); (AI_TABLE_COPY x1 x2)].
      rewrite -Hn.
      eapply step_read.
      eapply step_table_copy_le; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 n3)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H0.
        rewrite Heqinstr_2 in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H0; subst.
        eapply ai_const_eq_arg in H2; subst.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3.
      }
      rewrite Heqinstr_1 in H1.
      rewrite Heqinstr_2 in H2.
      rewrite Heqinstr_3 in H3.
      eapply ai_const_eq_arg in H1; subst.
      eapply ai_const_eq_arg in H2; subst.
      eapply ai_const_eq_arg in H3; subst.
      inversion H3; subst.
      by move/orP in Hs.
    }
    {
      exists s, f, [
        (AI_CONST I32 (mk_uN _ (n1 + n3 - 1)));
        (AI_CONST I32 (mk_uN _ (n2 + n3 - 1)));
        (AI_TABLE_GET x2);
        (AI_TABLE_SET x1);
        (AI_CONST I32 (mk_uN _ n1));
        (AI_CONST I32 (mk_uN _ n2));
        (AI_CONST I32 (mk_uN _ (n3 - 1)));
        (AI_TABLE_COPY x1 x2)].
      rewrite -Hn.
      eapply step_read.
      eapply step_table_copy_gt; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 n3)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H0.
        rewrite Heqinstr_2 in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H0; subst.
        eapply ai_const_eq_arg in H2; subst.
        eapply ai_const_eq_arg in H3; subst.
        simpl in H6.
        rewrite Hle in H6.
        discriminate.
      }
      {
        rewrite Heqinstr_1 in H0.
        rewrite Heqinstr_2 in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H0; subst.
        eapply ai_const_eq_arg in H2; subst.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3.
      }
      {
        rewrite Heqinstr_1 in H1.
        rewrite Heqinstr_2 in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H1; subst.
        eapply ai_const_eq_arg in H2; subst.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by move/orP in Hs.
      }
    }
  - (* Instr_ok__table_init *)
    move => C x1 x2 lim1 rt Hlenx1 Hlookupx1 Hlenx2 Hlookupx2.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2].
    rewrite Heqv2.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3].
    rewrite Heqv3.
    case Hs: (((n2 + n3) > (List.length (ELEM_REFS (fun_elem (mk_state s f) x2))))
      || ((n1 + n3) > (List.length (TAB_REFS (fun_table (mk_state s f) x1))))).
    {
      exists s, f, [AI_TRAP].
      eapply step_read.
      eapply step_table_init_trap.
      by move/orP in Hs.
    }
    case Hn: (n3) => [| n3'].
    {
      exists s, f, [].
      eapply step_read.
      eapply step_table_init_zero; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 0)) as instr_3.
      inversion HContra.
      rewrite Heqinstr_1 in H1.
      rewrite Heqinstr_2 in H2.
      rewrite Heqinstr_3 in H3.
      eapply ai_const_eq_arg in H1; subst.
      eapply ai_const_eq_arg in H2; subst.
      eapply ai_const_eq_arg in H3; subst.
      inversion H3; subst.
      by move/orP in Hs.
    }
    {
      rewrite -Hn.
      exists s, f, [(AI_CONST I32 (mk_uN _ n1));
        ((lookup_total (ELEM_REFS (fun_elem (mk_state s f) x2)) n2) : admininstr);
        (AI_TABLE_SET x1);
        (AI_CONST I32 (mk_uN _ (n1 + 1)));
        (AI_CONST I32 (mk_uN _ (n2 + 1)));
        (AI_CONST I32 (mk_uN _ (n3 - 1)));
        (AI_TABLE_INIT x1 x2)].
      eapply step_read.
      eapply step_table_init_succ; eauto.
      {
        simpl.
        eapply Bool.orb_false_elim in Hs as [Hs1 _].
        simpl in Hs1.
        remember (Datatypes.length (ELEM_REFS (lookup_total (ELEMS s)
          (lookup_total (MODULE_ELEMS (F_MODULE f)) (fun_proj_uN_0 32 x2))))) as num.
        rewrite Hn in Hs1.
        rewrite addnS in Hs1.
        rewrite ltnS in Hs1.
        move/negbT in Hs1.
        rewrite -ltnNge in Hs1.
        by apply: (leq_ltn_trans (leq_addr n3' n2)).
      }
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 n3)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H0.
        rewrite Heqinstr_2 in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H0; subst.
        eapply ai_const_eq_arg in H2; subst.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst.
      }
      rewrite Heqinstr_1 in H1.
      rewrite Heqinstr_2 in H2.
      rewrite Heqinstr_3 in H3.
      eapply ai_const_eq_arg in H1; subst.
      eapply ai_const_eq_arg in H2; subst.
      eapply ai_const_eq_arg in H3; subst.
      inversion H3; subst.
      by move/orP in Hs.
    }
  - (* Instr_ok__elem_drop *)
    move => C x rt Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case Estate: (fun_with_elem (mk_state s f) x []) => [s' f'].
    exists s', f', [].
    rewrite -Estate.
    by apply: step_elem_drop.
  - (* Instr_ok__memory_size *)
    move => C mt Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    (* TODO: This pose tactic cannot infer Inh_nat for some reason *)
    (* pose addr := (lookup_total (MODULE_MEMS (F_MODULE f)) 0). *)
    pose addr := (@lookup_total nat Inh_nat (MODULE_MEMS (F_MODULE f)) 0).
    inversion Hstore as [? ? ? ? meminsts ? ? ? ? ? memts ? Hs ? ? ? ? ? ? ? Hmem Hs'] => {Hs'}.
    have {}Hcontext : C_MEMS C = C_MEMS C'.
    { rewrite Hcontext. by case: C' Hcontext Hmod => *. }
    have {}Haddr : addr < size meminsts.
    { inversion Hmod as [? ? ? ? ? memaddrs ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hmemaddrs Hext ? ? ? ? ? ? ?  Hexp Hs' Hf HC'] => {Hexp Hs'}.
      rewrite /addr -Hf /=.
      rewrite Hcontext -HC' /= in Hlen.
      move/ltP in Hlen.
      move/Forall2_lookup2: Hmemaddrs => [_ Hmemaddrs].
      eapply Hmemaddrs in Hlen as Hexta.
      inversion Hexta as [| | ? ? ? ? ? Hlen' |].
      by rewrite Hs length_size /= in Hlen'. }
    have {}Hmem : Memory_instance_ok s (lookup_total meminsts addr) (lookup_total memts addr).
    { (* TODO: Use all2 instead *)
      move/Forall2_lookup: Hmem => [_ Hmem].
      move/(_ addr): Hmem => Hmem.
      move/ltP: Haddr => Haddr.
      rewrite length_size in Hmem.
      by move/(_ Haddr): Hmem => {}Hmem. }
    inversion Hmem as [? ? ? n ? ? Hlen' ? Hs' Hlookup' Hmt'] => {Hs' Hmt'}.
    exists s, f, [AI_CONST (INN_I32) (mk_uN _ n)].
    apply: step_read.
    apply: step_memory_size.
    rewrite length_size in Hlen'.
    rewrite /addr in Hlookup'.
    by rewrite length_size /fun_mem Hs -Hlookup' Hlen'.
  - (* Instr_ok__memory_grow *)
    move => C mt Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    set meminst1 := (fun_mem (mk_state s f) 0).
    (* TODO: Does set/pose tactic support destructuring? *)
    case Ememinst1: meminst1 => [[[limn1 limm1]] bs1].
    pose meminst2 := {|
      MEM_TYPE := (PAGE (mk_limits (mk_uN _ (limn1 + n1)) limm1));
      MEM_BYTES := (bs1 ++ repeat (mk_byte 0) (n1 * (64 * fun_Ki)))
      |}.
    (* TODO: Does set/pose tactic support destructuring? *)
    case Estate: (fun_with_meminst (mk_state s f) 0 meminst2) => [s' f'].
    (* NOTE: We could just use step_memory_grow_fail but
              we assume we can alway grow memory when it does not exceed predefined maximum size *)
    exists s, f, [AI_CONST INN_I32 (mk_uN _ (fun_inv_signed_ 32 (0 - 1)%coq_nat))].
    by apply: step_memory_grow_fail.
  - (* Instr_ok__memory_fill *)
    move => C mt Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2].
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3].
    rewrite Heqv3.

    case Hs: ((n1 + n3) > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0))))).
    {
      exists s, f, [AI_TRAP].
      eapply step_read.
      by eapply step_memory_fill_trap.
    }
    case Hn: (n3).
    {
      exists s, f, [].
      eapply step_read.
      eapply step_memory_fill_zero; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 0)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H1.
        eapply ai_const_eq_arg in H1.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by rewrite Hs in H0.
      }
    }
    {
      rewrite -Hn.
      exists s, f, [(AI_CONST I32 (mk_uN _ (n1)));
      (v2 : admininstr);
      (AI_STORE I32 (Some (mk_sz 8)) fun_memarg0);
      (AI_CONST I32 (mk_uN _ (n1 + 1)));
      (v2 : admininstr);
      (AI_CONST I32 (mk_uN _ (n3 - 1)));
      AI_MEMORY_FILL].
      eapply step_read.
      eapply step_memory_fill_succ; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n3)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H0.
        eapply ai_const_eq_arg in H0.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3.
      }
      {
        rewrite Heqinstr_1 in H1.
        eapply ai_const_eq_arg in H1.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by rewrite /= Hs in H0.
      }
    }
  - (* Instr_ok__memory_copy *)
    move => C mt Hlen Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2].
    rewrite Heqv2.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3].
    rewrite Heqv3.

    case Hs: (((n2 + n3) > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0)))))
      || ((n1 + n3) > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0)))))).
    {
      exists s, f, [AI_TRAP].
      eapply step_read.
      eapply step_memory_copy_trap.
      by move/orP in Hs.
    }
    case Hn: (n3).
    {
      exists s, f, [].
      eapply step_read.
      eapply step_memory_copy_zero; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 0)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H1.
        eapply ai_const_eq_arg in H1.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by move/orP in Hs.
      }
    }
    rewrite -Hn.
    case Hle: (n1 <= n2).
    {
      exists s, f, [(AI_CONST I32 (mk_uN _ n1));
      (AI_CONST I32 (mk_uN _ n2));
      (AI_LOAD I32 (Some (op_ _ (mk_sz 8) U)) fun_memarg0);
      (AI_STORE I32 (Some (mk_sz 8)) fun_memarg0);
      (AI_CONST I32 (mk_uN _ (n1 + 1)));
      (AI_CONST I32 (mk_uN _ (n2 + 1)));
      (AI_CONST I32 (mk_uN _ (n3 - 1)));
      AI_MEMORY_COPY].
      eapply step_read.
      eapply step_memory_copy_le; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 n3)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H0.
        eapply ai_const_eq_arg in H0.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3.
      }
      {
        rewrite Heqinstr_1 in H1.
        eapply ai_const_eq_arg in H1.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by move/orP in Hs.
      }
    }
    {
      exists s, f, [(AI_CONST I32 (mk_uN _ (((n1 + n3 - 1)))));
      (AI_CONST I32 (mk_uN _ (n2 + n3 - 1)));
      (AI_LOAD I32 (Some (op_ _ (mk_sz 8) U)) fun_memarg0);
      (AI_STORE I32 (Some (mk_sz 8)) fun_memarg0);
      (AI_CONST I32 (mk_uN _ n1));
      (AI_CONST I32 (mk_uN _ n2));
      (AI_CONST I32 (mk_uN _ (n3 - 1)));
      AI_MEMORY_COPY].
      eapply step_read.
      eapply step_memory_copy_gt; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 n3)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H0.
        eapply ai_const_eq_arg in H0.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by rewrite Hle in H4.
      }
      {
        rewrite Heqinstr_1 in H0.
        eapply ai_const_eq_arg in H0.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
      }
      {
        rewrite Heqinstr_1 in H1.
        eapply ai_const_eq_arg in H1.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by move/orP in Hs.
      }
    }
  - (* Instr_ok__memory_init *)
    move => C x mt Hlen Hlookup HRange HData.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_I32 in Ht2 as [n2 Heqv2].
    rewrite Heqv2.
    eapply invert_typeof_I32 in Ht3 as [n3 Heqv3].
    rewrite Heqv3.

    case Hs: (((n2 + n3) > (List.length (DATA_BYTES (fun_data (mk_state s f) x))))
      || ((n1 + n3 > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0))))))).
    {
      exists s, f, [AI_TRAP].
      eapply step_read.
      eapply step_memory_init_trap.
      by move/orP in Hs.
    }
    case Hn: (n3) => [| n3'].
    {
      exists s, f, [].
      eapply step_read.
      eapply step_memory_init_zero; eauto.
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 0)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H1.
        eapply ai_const_eq_arg in H1.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by move/orP in Hs.
      }
    }
    rewrite -Hn.
    {
      exists s, f, [(AI_CONST I32 (mk_uN _ n1));
      (AI_CONST I32 (mk_uN _ (fun_proj_byte_0 (lookup_total (DATA_BYTES (fun_data (mk_state s f) x)) n2))));
      (AI_STORE I32 (Some (mk_sz 8)) fun_memarg0);
      (AI_CONST I32 (mk_uN _ (n1 + 1)));
      (AI_CONST I32 (mk_uN _ (n2 + 1)));
      (AI_CONST I32 (mk_uN _ (n3 - 1)));
      (AI_MEMORY_INIT x)].
      eapply step_read.
      eapply step_memory_init_succ; eauto.
      {
        simpl.
        eapply Bool.orb_false_elim in Hs as [Hs1 _].
        simpl in Hs1.
        remember (Datatypes.length (DATA_BYTES (lookup_total (DATAS s) (lookup_total (MODULE_DATAS (F_MODULE f)) (fun_proj_uN_0 32 x))))) as num.
        rewrite Hn in Hs1.
        rewrite addnS in Hs1.
        rewrite ltnS in Hs1.
        move/negbT in Hs1.
        rewrite -ltnNge in Hs1.
        by apply: (leq_ltn_trans (leq_addr n3' n2)).
      }
      move => HContra.
      simpl in HContra.
      remember (AI_CONST I32 (mk_uN 32 n1)) as instr_1.
      remember (AI_CONST I32 (mk_uN 32 n2)) as instr_2.
      remember (AI_CONST I32 (mk_uN 32 n3)) as instr_3.
      inversion HContra.
      {
        rewrite Heqinstr_1 in H0.
        eapply ai_const_eq_arg in H0.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3.
      }
      {
        rewrite Heqinstr_1 in H1.
        eapply ai_const_eq_arg in H1.
        rewrite Heqinstr_2 in H2.
        eapply ai_const_eq_arg in H2.
        rewrite Heqinstr_3 in H3.
        eapply ai_const_eq_arg in H3; subst.
        inversion H3; subst; clear H3.
        by move/orP in Hs.
      }
    }
  - (* Instr_ok__data_drop *)
    move => C x HRange Hlookup.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case Estate: (fun_with_data (mk_state s f) x []) => [s' f'].
    exists s', f', [].
    rewrite -Estate.
    by eapply step_data_drop.
  - (* Instr_ok__load None *)
    move => C nt memarg mt Hlen Hlookup Hfunsize HLim.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    case Hs: (((n1 + (fun_proj_uN_0 32 (OFFSET memarg))) +
    ((((the (fun_size (nt)))) / (8)) : nat)) > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0))))).
    + exists s, f, [AI_TRAP].
      eapply step_read.
      eapply step_load_num_trap; eauto.
    + (* Need definition for fun_nbytes_ *)
      admit.
  - (* Instr_ok__load INN_I32 *)
    move => C M sx memarg mt Hlen Hlookup HLim.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    case Hs: (((n1 + (fun_proj_uN_0 32 (OFFSET memarg))) + (((M) / (8)) : nat)) > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0))))).
    + exists s, f, [AI_TRAP].
      eapply step_read.
      by eapply step_load_pack_trap_I32.
    + (* Need definition for fun_ibytes_ *)
      admit.
  - (* Instr_ok__load INN_I64 *)
    move => C M sx memarg mt Hlen Hlookup HLim.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    case Hs: (((n1 + (fun_proj_uN_0 32 (OFFSET memarg))) + (((M) / (8)) : nat)) > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0))))).
    + exists s, f, [AI_TRAP].
      eapply step_read.
      by eapply step_load_pack_trap_I64.
    + (* Need definition for fun_ibytes_ *)
      admit.
  - (* Instr_ok__store None *)
    move => C nt memarg mt Hlen Hlookup Hfunsize HLim.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    eapply invert_typeof_numtype in Ht2 as [n2 Heqv2].
    rewrite Heqv2.
    case Hs: (((n1 + (fun_proj_uN_0 32 (OFFSET memarg))) + ((((the (fun_size (nt : valtype))) : nat) / (8 : nat)) : nat))
      > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0))))).
    + exists s, f, [AI_TRAP].
      by eapply step_store_num_trap; eauto.
    + (* Need definition for fun_nbytes_ *)
      admit.
  - (* Instr_ok__store INN *)
    move => C Inn M memarg mt Hlen Hlookup HLim.
    move => s f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    eapply invert_typeof_I32 in Ht1 as [n1 Heqv1].
    rewrite Heqv1.
    case Hs: (((n1 + (fun_proj_uN_0 32 (OFFSET memarg))) + (((M) / (8)) : nat))
      > (List.length (MEM_BYTES (fun_mem (mk_state s f) (mk_uN _ 0))))).
    {
      exists s, f, [AI_TRAP].
      destruct Inn.
      {
        eapply invert_typeof_I32 in Ht2 as [n2 Heqv2].
        rewrite Heqv2.
        by eapply step_store_pack_trap_I32; eauto.
      }
      {
        eapply invert_typeof_I64 in Ht2 as [n2 Heqv2].
        rewrite Heqv2.
        by eapply step_store_pack_trap_I64; eauto.
      }
    }
    (* Need definition for fun_ibytes_ *)
    admit.
    (* SIMD *)
  1-6: admit.
  - (* Instrs_ok__empty *)
    move => C s.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    by left.
  - (* Instrs_ok__seq *)
    move => C bes1 be2 ts1 ts2 ts3 Hinstrs1 IH1 Hinstr2 IH2.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Ets1 : ts1' = ts1 by case: Htf. rewrite Ets1 in Hts.
    rewrite -be_to_e_cat in Hnotbr Hnotret.
    case Hconst: (const_list (map fun_coec_instr__admininstr bes1)).
    + move/const_es_exists: (Hconst) => [vs1 Hvs1].
      have Hadmin1 : Admin_instrs_ok s C (map fun_coec_instr__admininstr bes1) (ts1 :-> ts3).
      { by apply: AIs_ok_instrs. }
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
        rewrite map_map in HVals.
        by rewrite map_cat Hts HVals. }
      move: (not_lf_br_left _ _ Hconst Hnotbr) => Hnotbr2.
      move: (not_lf_return_left _ _ Hconst Hnotret) => Hnotret2.
      move: (IH2 s f C' (vcs ++ vs1) ts3 ts2 lab ret Heqtf2 Hcontext Hmod Heqts2 Hstore Hnotbr2 Hnotret2) => {}IH2.
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
      move: (IH1 s f C' vcs ts1 ts3 lab ret Heqtf1 Hcontext Hmod Hts Hstore Hnotbr1 Hnotret1) => {}IH1.
      move: IH1 => [Hcontra | Hprog1]; first by move/negP: Hconst.
      right.
      move: Hprog1 => [s' [f' [es1' Hprog1]]].
      exists s', f', (es1' ++ map fun_coec_instr__admininstr [be2]).
      rewrite -be_to_e_cat catA.
      by apply step_ctxt_seq with (v_val := []).
  - (* Instrs_ok__sub *)
    move => C bes ts1'' ts2'' ts1 ts2 HType IH2 HSub1 HSub2.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Ets1 : ts1' = ts1'' by case: Htf. rewrite Ets1 in Hts.
    eapply IH2; eauto.
    eapply typeof_vals_non_bot in Hts as Htsnonbot.
    eapply resulttype_sub_non_bot in HSub1; eauto.
    subst; eauto.
  - (* Instrs_ok__frame *)
    move => C bes ts ts1 ts2 Hinstrs IH.
    move => s f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* NOTE: This should be named as Instrs_ok__weakening *)
    (* TODO: Get rid of duplicate proof *)
    have Heqtf : (ts1 :-> ts2) = (ts1 :-> ts2) by [].
    have Heqts : map typeof (drop (length ts) vcs) = ts1.
    { rewrite map_drop.
      injection Htf => Htf2 Htf1.
      rewrite -Hts in Htf1. by rewrite -Htf1 drop_cat length_size ltnn subnn drop0. }
    move: (IH s f C' (drop (length ts) vcs) ts1 ts2 lab ret Heqtf Hcontext Hmod Heqts Hstore Hnotbr Hnotret) => {}IH.
    have -> : vcs = (take (size ts) vcs ++ drop (size ts) vcs) by rewrite cat_take_drop.
    rewrite {}length_size in IH.
    set vcs1 := take (size ts) vcs in IH *.
    set vcs2 := drop (size ts) vcs in IH *.
    case: IH => [Hconst | Hprog].
    + by left.
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (map fun_coec_val__admininstr vcs1 ++ es').
      rewrite -v_to_e_cat -catA.
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[map fun_coec_val__admininstr vcs2 ++ _]cats0.
      rewrite -[map fun_coec_val__admininstr vcs1 ++ es']cats0.
      rewrite -[(map fun_coec_val__admininstr vcs1 ++ es') ++ []]catA.
      by apply step_ctxt_seq with
        (v_admininstr := map fun_coec_val__admininstr vcs2 ++ map fun_coec_instr__admininstr bes)
        (v_admininstr' := es')
        (v_admininstr'' := []).
  (* TODO: These goals are shelved by Instr_ok__call_indirect for some reason *)
  Unshelve.
  - apply: Build_Inhabited.
    exact 0.
  - apply: Build_Inhabited.
    exact 0.
Admitted.

(* TODO: Similar to admin_instrs_ok_eq *)
Lemma Instr_ok_Instrs_ok: forall C be tf,
  Instr_ok C be tf -> Instrs_ok C [be] tf.
Proof.
  move => C be tf Hinstr.
  rewrite -[[be]]cat0s.
  case: tf Hinstr => [[ts1] [ts2]] Hinstr.
  apply instrs_ok_seq with (v_t_2 := ts1) => //=.
  eapply instrs_empty_typing.
  eapply resulttype_sub_refl.
Qed.

(* NOTE: Mutual induction principle used in t_progress_e *)
Scheme Admin_instr_ok_ind' := Induction for Admin_instr_ok Sort Prop
  with Admin_instrs_ok_ind' := Induction for Admin_instrs_ok Sort Prop
  with Thread_ok_ind' := Induction for Thread_ok Sort Prop.

(* MEMO: AI_local -> Admininstr__FRAME_ *)
(* MEMO: e_typing -> Admin_instrs_ok *)
(* MEMO: store_typing -> Store_ok *)
(* MEMO: reduce -> Step *)
(* MEMO: reduce -> Step_read *)
(* NOTE: lholed is no longer used in specifying opsem
         Use evaluation context E directly *)
(* TODO: Reorder premises in consistent order *)
Lemma t_progress_e: forall s C C' f vcs es tf ts1 ts2 lab ret,
  Admin_instrs_ok s C es tf ->
  tf = (ts1 :-> ts2) ->
  C = (upd_local_label_return C' (map typeof f.(F_LOCALS)) lab ret) ->
  Module_instance_ok s f.(F_MODULE) C' ->
  map typeof vcs = ts1 ->
  Store_ok s ->
  not_lf_br es ->
  not_lf_return es ->
  terminal_form (map fun_coec_val__admininstr vcs ++ es) \/
  exists s' f' es', Step (mk_config (mk_state s f) (map fun_coec_val__admininstr vcs ++ es)) (mk_config (mk_state s' f') es').
Proof.
  move => s C C' f vcs es tf ts1 ts2 lab ret Hadmin.
  move: f C' vcs ts1 ts2 lab ret.
  apply Admin_instrs_ok_ind' with 
    (P := fun s C e tf (Hadmin : Admin_instr_ok s C e tf) => 
      forall f C' vcs ts1 ts2 lab ret,
      tf = (ts1 :-> ts2) ->
      C = (upd_local_label_return C' (map typeof f.(F_LOCALS)) lab ret) ->
      Module_instance_ok s f.(F_MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br [e] ->
      not_lf_return [e] ->
      terminal_form (map fun_coec_val__admininstr vcs ++ [e]) \/
      exists s' f' es', Step (mk_config (mk_state s f) (map fun_coec_val__admininstr vcs ++ [e])) (mk_config (mk_state s' f') es'))
    (P0 := fun s C es tf (Hadmin : Admin_instrs_ok s C es tf) => 
      forall f C' vcs ts1 ts2 lab ret,
      tf = (ts1 :-> ts2) ->
      C = (upd_local_label_return C' (map typeof f.(F_LOCALS)) lab ret) ->
      Module_instance_ok s f.(F_MODULE) C' ->
      map typeof vcs = ts1 ->
      Store_ok s ->
      not_lf_br es ->
      not_lf_return es ->
      terminal_form (map fun_coec_val__admininstr vcs ++ es) \/
      exists s' f' es', Step (mk_config (mk_state s f) (map fun_coec_val__admininstr vcs ++ es)) (mk_config (mk_state s' f') es'))
    (P1 := fun s rs f es ts (Hthread : Thread_ok s rs f es ts) =>
      Store_ok s ->
      not_lf_br es ->
      not_lf_return es ->
      (const_list es /\ length es = length ts) \/
      es = [AI_TRAP] \/
      exists s' f' es', Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')) 
    => // {s C es tf Hadmin}.
  - (* Admin_instr_ok__instr *)
    move => s C be tf Hinstr.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Hinstrs: Instrs_ok C [be] tf by apply Instr_ok_Instrs_ok.
    pose Hprog := t_progress_be s C C' f vcs [be] tf ts1 ts2 lab ret Hinstrs Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: Hprog => [Hconst | Hprog].
    + left. rewrite /terminal_form.
      left. apply: const_list_concat => //=.
      by apply: v_to_e_const.
    + by right. 
  - (* Admin_instr_ok__trap *)
    move => s C ts1 ts2.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: vcs Hts => [| vc vcs] Hts //=.
    + left. rewrite /terminal_form. by right.
    + right. exists s, f, [AI_TRAP].
      apply: step_pure.
      rewrite -cat_cons.
      rewrite -{1}(cats0 [AI_TRAP]).
      assert (map fun_coec_val__admininstr (vc :: vcs) =
        fun_coec_val__admininstr (vc) :: map fun_coec_val__admininstr (vcs)).
      {
        auto.
      }
      rewrite -H.
      eapply step_trap_vals with
        (v_val := vc :: vcs)
        (v_admininstr := [])
        .
      by left. 
  - (* Admin_instr_ok__ref_host_addr *)
    move => s C addr.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    left.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    rewrite /terminal_form.
    by left.
  - (* Admin_instr_ok__ref_func_addr *)
    move => s C addr functype HEok.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    left.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    rewrite /terminal_form.
    by left.
  - (* Admin_instr_ok__call_addr *)
    (* NOTE: AI_CALL_ADDR corresponds to invoke instruction *)
    move => s C addr ts1 ts2 Hext.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    right.
    injection Htf => _ Htf1. rewrite -{}Htf1 in Hts.
    inversion Hext as [? ? ? inst func Haddr Hlookup Hs Ha Htf' | | | ] => //=.
    case Hfunc: func Hlookup => [x ls es] Hlookup.
    pose ts := map (fun '(LOCAL t) => t) ls.
    pose f' := (
    {| F_LOCALS := (vcs ++ (map (fun (t: valtype) => the (fun_default_ t)) ts)); F_MODULE := inst |}
    ).
    pose f'' := (f' Inhabited__val).
    exists s, f, [AI_FRAME_ (size ts2) f'' [AI_LABEL_ (size ts2) [] (map fun_coec_instr__admininstr es)]].
    apply: step_read.
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
    eapply step_call_addr with
      (v_t := ts)
    ; eauto.
    {
      by rewrite -{1}Hlocal.
    }
    {
      (* Problem in Spectec DSL *)
      admit.
    }
    {
      by rewrite -Hts !length_size size_map.
    }
  - (* Admin_instr_ok__label *)
    move => s C n bes es t1 t2 Hinstrs Hadmin IH Hsize.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: (br_reduce_decidable es) => [Hbrred | Hnotbrred].
    + rewrite /br_reduce in Hbrred.
      move: Hbrred => [vcs' [l [es' Hes]]].
      case: l Hes => [[| l']] Hes.
      * right.
        have Hexists : exists vcs es', es = map fun_coec_val__admininstr vcs ++ [AI_BR 0] ++ es'. 
        { by exists vcs', es'. }
        have Hlookup : lookup_total (C_LABELS (_append {|
          C_TYPES := [];
          C_FUNCS := [];
          C_GLOBALS := [];
          C_TABLES := [];
          C_MEMS := [];
          C_ELEMS := [];
          C_DATAS := [];
          C_LOCALS := [];
          C_LABELS := [mk_list _ t2];
          C_RETURN := None
          |} C)) 0 = t2.
        { move => {Hadmin IH} /=.
          by rewrite /lookup_total /=. }
        move: (br_reduce_extract_vs _ _ _ _ _ Hexists Hadmin Hlookup) => Hextract.
        move: Hextract => [vcs1 [vcs2 [es'' [Hes' Hsize']]]].
        rewrite Hes'.
        exists s, f, (map fun_coec_val__admininstr vcs2 ++ map fun_coec_instr__admininstr bes).
        apply: step_pure.
        eapply step_br_zero.
        rewrite length_size Hsize' Hsize.
        by case: t2 Hinstrs Hadmin IH Hsize Hsize' Hlookup.
      * right. exists s, f, (map fun_coec_val__admininstr vcs' ++ [AI_BR (mk_uN _ l')]).
        rewrite -(addn1 l') in Hes.
        rewrite Hes.
        apply: step_pure.
        by eapply step_br_succ with (v_l := (mk_uN 32 l')).
    + case: (return_reduce_decidable es) => [Hretred | Hnotretred].
      * rewrite /return_reduce in Hretred.
        move: Hretred => [vcs' [es' Hes]].
        right. exists s, f, (map fun_coec_val__admininstr vcs' ++ [AI_RETURN]).
        rewrite Hes.
        apply: step_pure.
        eapply step_return_label.
      * (* TODO: Can we simplify this? *)
        have Heqc : _append {|
          C_TYPES := [];
          C_FUNCS := [];
          C_GLOBALS := [];
          C_TABLES := [];
          C_MEMS := [];
          C_ELEMS := [];
          C_DATAS := [];
          C_LOCALS := [];
          C_LABELS := [mk_list _ t2];
          C_RETURN := None
          |} C = upd_local_label_return C' [seq typeof i  | i <- F_LOCALS f] ((mk_list _ t2) :: lab) ret.
          by rewrite Hcontext.
        have Heqtf : ([] :-> t1) = ([] :-> t1) by [].
        have Heqts : map typeof [] = [] by [].
        move/not_br_reduce_not_lf_br: Hnotbrred => Hnotbr'.
        move/not_return_reduce_not_lf_return: Hnotretred => Hnotret'.
        move/(_ f C' [] [] (t1) ((mk_list _ t2) :: lab) ret Heqtf Heqc Hmod Heqts Hstore Hnotbr' Hnotret'): IH => IH.
        move => {Heqtf Heqc Hmod Heqts Hstore}.
        case: IH => [Hterm | Hprog].
        { right. exists s, f, es.
          case: Hterm => /= [Hconst | Htrap].
          - move: (const_es_exists _ Hconst) => [vs Hvs]. rewrite Hvs.
            apply: step_pure.
            by apply: step_label_vals.
          - rewrite Htrap.
            apply: step_pure.
            by apply: step_trap_label. }
        { right. move: Hprog => [s' [f' [es' IH]]].
          exists s', f', [AI_LABEL_ n bes es'].
          by apply: step_ctxt_label. }
  - (* Admin_instr_ok__frame *)
    move => s C n f es t Hthread IH Hsize.
    move => f' C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs.
    case: (return_reduce_decidable es) => [Hretred | Hnotretred].
    + rewrite /return_reduce in Hretred.
      move: Hretred => [vcs' [es' Hes]].
      right.
      inversion Hthread as [? ? ? ? ? C'' Hframe Hadmin Hs Ht Hf Hes' Ht'].
      move => {Hs Ht Hf Hes' Ht'}.
      have Hexists : exists vcs es', es = map fun_coec_val__admininstr vcs ++ [AI_RETURN] ++ es'. 
      { by exists vcs', es'. }
      have Hlookup : C_RETURN (_append {|
        C_TYPES := [];
        C_FUNCS := [];
        C_GLOBALS := [];
        C_TABLES := [];
        C_MEMS := [];
        C_ELEMS := [];
        C_DATAS := [];
        C_LOCALS := [];
        C_LABELS := [];
        C_RETURN := Some (mk_list _ t)
        |} C'') = Some (mk_list _ t).
      { move => {Hadmin IH} /=.
        move/frame_t_context_return_empty: Hframe => Hret.
        by rewrite Hret. }
      move: (return_reduce_extract_vs _ _ _ _ _ Hexists Hadmin Hlookup) => Hextract.
      move: Hextract => [vcs1 [vcs2 [es'' [Hes' Hsize']]]].
      rewrite Hes'.
      exists s, f', (map fun_coec_val__admininstr vcs2).
      apply: step_pure.
      apply: step_return_frame.
      rewrite length_size Hsize' Hsize.
      by case: t Hthread IH Hsize Hsize' Hadmin Hlookup.
    + move/not_return_reduce_not_lf_return: Hnotretred => Hnotret'.
      move/s_typing_not_lf_br: Hthread => Hnotbr'.
      move/(_ Hstore Hnotbr' Hnotret'): IH => IH.
      case: IH => [[Hconst Hlen] | [Htrap | Hprog]].
      + right. exists s, f', es.
        move: (const_es_exists _ Hconst) => [vs Hvs]. rewrite Hvs.
        apply: step_pure.
        by apply: step_frame_vals.
      + right. exists s, f', [AI_TRAP].
        rewrite Htrap.
        apply: step_pure.
        by apply: step_trap_frame.
      + right. move: Hprog => [s' [f'' [es' Hprog]]].
        exists s', f', [AI_FRAME_ n f'' es'].
        by apply: step_ctxt_frame.
  - (* Admin_instr_ok__weakening *)
    move => s C e ts' ts1'' ts ts2'' ts1 ts2 Hadmin IH HSub HSub1 HSub2.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: Htf => Htf1 _. subst ts1'.
    have Heqtf : (ts1 :-> ts2) = (ts1 :-> ts2) by [].
    have Heqts : map typeof (drop (length ts) vcs) = ts1.
    {
      assert (size ts' = size ts) as Hsizets. { by inversion HSub. }
      symmetry in Htf1.
      eapply typeof_vals_non_bot in Htf1 as Hnonbot.
      eapply (resulttype_sub_app _ _ _ _ HSub) in HSub1.
      eapply resulttype_sub_non_bot in HSub1; eauto.
      rewrite map_drop length_size -Hsizets.
      rewrite Htf1 drop_cat ltnn subnn drop0.
      rewrite -(helper_lemmas.drop_size_cat ts' ts1'').
      rewrite -(helper_lemmas.drop_size_cat ts ts1).
      by rewrite Hsizets HSub1.
      }
    move/(_ f C' (drop (length ts) vcs) ts1 ts2 lab ret Heqtf Hcontext Hmod Heqts Hstore Hnotbr Hnotret): IH => IH.
    have -> : vcs = (take (size ts) vcs ++ drop (size ts) vcs) by rewrite cat_take_drop.
    rewrite length_size in IH.
    set vcs1 := take (size ts) vcs in IH *.
    set vcs2 := drop (size ts) vcs in IH *.
    case: IH => [Hterm | Hprog].
    + case: Hterm => [Hconst | Htrap].
      * left. left.
        (* TODO: v_to_e_cat should be used elsewhere when applying step_ctxt_seq *)
        rewrite -v_to_e_cat -catA.
        apply: const_list_concat => //=.
        by apply: v_to_e_const.
      * rewrite -v_to_e_cat -catA Htrap.
        case: vcs1 => [| vc1 vcs1] //=.
        -- left. by right.
        -- right. exists s, f, [AI_TRAP].
           apply: step_pure.
           assert (fun_coec_val__admininstr vc1 :: map fun_coec_val__admininstr vcs1
            = map fun_coec_val__admininstr (vc1 :: vcs1)) as Hmap.
            {
              auto.
            }
           rewrite -cat_cons Hmap.
           rewrite -{1}(cats0 [AI_TRAP]).
           eapply step_trap_vals with
            (v_val := (vc1 :: vcs1))
            (v_admininstr := []).
           by left.
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (map fun_coec_val__admininstr vcs1 ++ es').
      rewrite -v_to_e_cat -catA.
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[map fun_coec_val__admininstr vcs2 ++ _]cats0.
      rewrite -[map fun_coec_val__admininstr vcs1 ++ es']cats0.
      rewrite -[(map fun_coec_val__admininstr vcs1 ++ es') ++ []]catA.
      by apply step_ctxt_seq with
        (v_admininstr := map fun_coec_val__admininstr vcs2 ++ [e])
        (v_admininstr' := es')
        (v_admininstr'' := []).
  - (* Admin_instrs_ok__empty *)
    move => s C.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    left. rewrite cats0 /terminal_form.
    left. by apply: v_to_e_const.
  - (* AIs_ok_seq *)
    move => s C es1 e2 ts1 ts2 ts3 Hadmin1 IH1 Hadmin2 IH2.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
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
        rewrite map_map in HVals.
        by rewrite map_cat Hts HVals. }
      move: (not_lf_br_left _ _ Hconst Hnotbr) => Hnotbr2.
      move: (not_lf_return_left _ _ Hconst Hnotret) => Hnotret2.
      move/(_ f C' (vcs ++ vs1) ts3 ts2 lab ret Heqtf2 Hcontext Hmod Heqts2 Hstore Hnotbr2 Hnotret2): IH2 => IH2.
      case: IH2 => [Hterm2 | Hprog2].
      * case: Hterm2 => [Hconst2 | Htrap2].
        { left. left.
          by rewrite catA Hvs1 v_to_e_cat. }
        { left. right.
          move: (extract_list1 _ _ _ Htrap2) => [Hvcs He].
          rewrite catA Hvs1 v_to_e_cat Hvcs He /=. 
          by rewrite /terminal_form. }
      * right. by rewrite catA Hvs1 v_to_e_cat.
    + have Heqtf1 : (ts1 :-> ts3) = (ts1 :-> ts3) by [].
      have Heqts1 := Ets1.
      move: (not_lf_br_right _ _ Hnotbr) => Hnotbr1.
      move: (not_lf_return_right _ _ Hnotret) => Hnotret1.
      move/(_ f C' vcs ts1 ts3 lab ret Heqtf1 Hcontext Hmod Hts Hstore Hnotbr1 Hnotret1): IH1 => IH1.
      case: IH1 => [Hterm1 | Hprog1].
      * case: Hterm1 => [Hconst1 | Htrap1].
        { rewrite const_list_cat in Hconst1.
          move/andP: Hconst1 => [Hconst1 Hconst1'].
          by move/negP: Hconst. }
        { right. move: (v_e_trap _ _ (v_to_e_const vcs) Htrap1) => [-> ->] //=.
          exists s, f, [AI_TRAP].
          apply: step_pure.
          
          eapply step_trap_vals with (v_val := []). by right. }
      * right. move: Hprog1 => [s' [f' [es1' Hprog1]]].
        exists s', f', (es1' ++ [e2]).
        rewrite catA.
        by apply step_ctxt_seq with (v_val := []).
  - (* AIs_ok_sub *)
    move => s C es ts1'' ts2'' ts1 ts2 Hadmin IH HSub1 HSub2.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    have Ets1 : ts1'' = ts1' by case: Htf. subst ts1''.
    eapply IH; eauto.
    eapply typeof_vals_non_bot in Hts as Hnonbot.
    eapply resulttype_sub_non_bot in HSub1; eauto.
    by subst ts1'.
  - (* AIs_ok_frame *)
    move => s C es ts ts1 ts2 Hadmin IH.
    move => f C' vcs ts1' ts2' lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    (* NOTE: This is equivalent to Admin_instr_ok__weakening but for Admin_instrs_ok *)
    (* TODO: Get rid of duplicate proof *)
    have Heqtf : (ts1 :-> ts2) = (ts1 :-> ts2) by [].
    have Heqts : map typeof (drop (length ts) vcs) = ts1.
    { rewrite map_drop.
      injection Htf => Htf2 Htf1.
      rewrite -Hts in Htf1. by rewrite -Htf1 drop_cat length_size ltnn subnn drop0. }
    move/(_ f C' (drop (length ts) vcs) ts1 ts2 lab ret Heqtf Hcontext Hmod Heqts Hstore Hnotbr Hnotret): IH => IH.
    have -> : vcs = (take (size ts) vcs ++ drop (size ts) vcs) by rewrite cat_take_drop.
    rewrite {}length_size in IH.
    set vcs1 := take (size ts) vcs in IH *.
    set vcs2 := drop (size ts) vcs in IH *.
    case: IH => [Hterm | Hprog].
    + case: Hterm => [Hconst | Htrap].
      * left. left.
        rewrite -v_to_e_cat -catA.
        apply const_list_concat => //=.
        by apply v_to_e_const.
      * rewrite -v_to_e_cat -catA Htrap.
        case: vcs1 => /= [| vc1 vcs1].
        { left. by right. }
        { right. exists s, f, [AI_TRAP].
          apply: step_pure.
          apply step_trap_vals with (v_val := (vc1 :: vcs1)).
          by left. }
    + right. move: Hprog => [s' [f' [es' IH]]].
      exists s', f', (map fun_coec_val__admininstr vcs1 ++ es').
      rewrite -v_to_e_cat -catA.
      (* TODO: Can we get rid of these rewrites? *)
      rewrite -[map fun_coec_val__admininstr vcs2 ++ _]cats0.
      rewrite -[map fun_coec_val__admininstr vcs1 ++ es']cats0.
      rewrite -[(map fun_coec_val__admininstr vcs1 ++ es') ++ []]catA.
      by apply step_ctxt_seq with
        (v_admininstr := map fun_coec_val__admininstr vcs2 ++ es)
        (v_admininstr' := es')
        (v_admininstr'' := []).
  - (* Admin_instrs_ok__instrs *)
    (* NOTE: This is equivalent to Admin_instr_ok__instr but for Admin_instrs_ok *)
    (* TODO: Get rid of duplicate proof *)
    move => s C bes tf Hinstrs.
    move => f C' vcs ts1 ts2 lab ret Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    pose Hprog := t_progress_be s C C' f vcs bes tf ts1 ts2 lab ret Hinstrs Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret.
    case: Hprog => [Hconst | Hprog].
    + left. rewrite /terminal_form.
      left. apply: const_list_concat => //=.
      by apply: v_to_e_const.
    + by right. 
  - (* Thread_ok__ *)
    move => s rs f es ts C.
    move => Hframe Hadmin IH Hstore Hnotbr Hnotret.
    have Heqtf : ([] :-> ts) = ([] :-> ts) by [].
    have Heqts : map typeof [] = [] by [].
    move/frame_t_context_local_types: (Hframe) => Eloc.
    move/frame_t_context_label_empty: (Hframe) => Elab.
    move/frame_t_context_return_empty: (Hframe) => Eret.
    (* TODO: Can we simplify this? *)
    have Heqc : _append {|
        C_TYPES := [];
        C_FUNCS := [];
        C_GLOBALS := [];
        C_TABLES := [];
        C_MEMS := [];
        C_ELEMS := [];
        C_DATAS := [];
        C_LOCALS := [];
        C_LABELS := [];
        C_RETURN := rs
      |} C = upd_local_label_return (upd_local C []) [seq typeof i  | i <- F_LOCALS f] [] rs.
    { move => {IH Hframe Hadmin}.
      case: C Eloc Elab Eret => //= ? ? ? ? ? ? ? ? ? ? Eloc Elab Eret.
      rewrite Eloc Elab Eret.
      by case: rs. }
    have Hmod : Module_instance_ok s (F_MODULE f) (upd_local C []).
    { inversion Hframe as [? ? ? ? ? Hmod]. by inversion Hmod. }
    move/(_ f (upd_local C []) [] [] ts [] (rs) Heqtf Heqc Hmod Heqts Hstore Hnotbr Hnotret): IH => IH {Heqtf Heqc}.
    case: IH => /= [Hterm | Hprog].
    + case: Hterm => [Hconst | Htrap].
      * left. split => //=.
        move/const_es_exists: Hconst => [vs Hvs].
        rewrite Hvs in Hadmin *.
        eapply ais_vals_typing_inversion in Hadmin as [v_ts [HSub HVals]].
        eapply instrtype_sub_iff_resulttype_sub in HSub.
        eapply Forall2_length in HVals.
        rewrite !length_size in HVals.
        assert (size v_ts = size ts). { by inversion HSub. }
        by rewrite !length_size size_map -HVals H.
      * right. left. by rewrite Htrap.
    + right. by right.
Admitted.

Theorem t_progress: forall s f es ts,
  Config_ok (mk_config (mk_state s f) es) ts ->
  terminal_form es \/
  exists s' f' es', Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es').
Proof.
  move => s f es ts Hconfig.
  (* TODO: inversion tactic can be replaced by case tactic
           by introducing equalities on dependent indices of the premise
           and rejecting contradictory cases manually *)
  inversion Hconfig as [? ? ? ? Hstore Hthread]; subst.
  inversion Hthread as [? ? ? ? ? C Hframe Hadmin]; subst.
  (* TODO: apply with tactic can be replaced by apply: tactic *)
  eapply t_progress_e with
    (lab := []) (ret := None)
    (vcs := []) (ts1 := []) (ts2 := v_t)
    (C' := upd_local_label_return C [] [] None) => //=.
  - move/frame_t_context_local_types: (Hframe) => Eloc.
    move/frame_t_context_label_empty: (Hframe) => Elab.
    move/frame_t_context_return_empty: (Hframe) => Eret.
    by rewrite -Eloc -Elab -Eret.
  - inversion Hframe as [? ? ? ? ? Hmod] => {Hframe}.
    by inversion Hmod.
  - by move/s_typing_not_lf_br: Hthread. 
  - by move/s_typing_not_lf_return: Hthread.
Qed.

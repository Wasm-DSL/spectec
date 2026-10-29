(* Typing preservation: SpecTec instruction typing ([Instr_ok], [Instrs_ok])
   implies WasmCert's basic-instruction typing ([be_typing]) of the
   translation. *)

From Stdlib Require Import NArith ZArith QArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From Wasm Require Import datatypes operations typing subtyping typing_inversion.
From WasmSpectec Require wasm.
From WasmCertBridge Require Import translation.

Module S := WasmSpectec.wasm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope N_scope with num.

Scheme Instr_ok_mut := Induction for S.Instr_ok Sort Prop
  with Instrs_ok_mut := Induction for S.Instrs_ok Sort Prop.

Section Typing.

Context `{hfc : host_function_class}.

(** * Helper lemmas *)

Lemma coerce_u32 (x : S.uN) : @S.coerce S.uN N S.proj_uN_0_coercion x = tr_u32 x.
Proof. by case: x. Qed.

Lemma lookup_N_map {A B : Type} `{S.Inhabited A} (f : A -> B) (l : seq A) (n : N) :
  is_true (N.ltb n (N.of_nat (size l))) ->
  lookup_N (map f l) n = Some (f (S.lookup_total l n)).
Proof.
  move=> /N.ltb_spec0 Hn. rewrite /lookup_N /S.lookup_total.
  have : Nat.lt (N.to_nat n) (size l) by lia.
  elim: l (N.to_nat n) {Hn} => [|x l IH] [|k] /= Hk; try lia; first done.
  apply: IH. lia.
Qed.

Lemma tr_valtype_num (nt : S.numtype) :
  tr_valtype (S.valtype_numtype nt) = T_num (tr_numtype nt).
Proof. by case: nt. Qed.

Lemma tr_valtype_ref (rt : S.reftype) :
  tr_valtype (S.valtype_reftype rt) = T_ref (tr_reftype rt).
Proof. by case: rt. Qed.

Lemma tr_valtype_Inn (t : S.Inn) :
  tr_valtype (S.valtype_Inn t) = T_num (tr_numtype (S.numtype_Inn t)).
Proof. by case: t. Qed.

(* The context of a block body: one label is pushed, nothing else changes. *)
Lemma tr_context_label (C : S.context) (ts : S.resulttype) :
  tr_context (S._append
    {| S.context_TYPES := [::]; S.context_FUNCS := [::]; S.context_GLOBALS := [::];
       S.context_TABLES := [::]; S.context_MEMS := [::]; S.context_ELEMS := [::];
       S.context_DATAS := [::]; S.context_LOCALS := [::]; S.LABELS := [:: ts];
       S.context_RETURN := None |} C)
  = upd_label (tr_context C) ([:: tr_resulttype ts] ++ tc_labels (tr_context C)).
Proof. by case: C. Qed.

Lemma Blocktype_ok_tr C bt t1 t2 :
  S.Blocktype_ok C bt (S.mk_functype (S.mk_list _ t1) (S.mk_list _ t2)) ->
  expand_t (tr_context C) (tr_blocktype bt) = Some (Tf (map tr_valtype t1) (map tr_valtype t2)).
Proof.
  move=> H; inversion H; subst.
  - by destruct valtype_opt.
  - rewrite /= -coerce_u32 lookup_N_map; last by assumption.
    by match goal with Hb : is_true (_ == _) |- _ => move/eqP: Hb => -> end.
Qed.

Lemma Valtype_sub_tr t1 t2 :
  S.Valtype_sub t1 t2 -> value_subtyping (tr_valtype t1) (tr_valtype t2).
Proof. by case => t; rewrite /value_subtyping eqxx ?orbT. Qed.

Lemma Resulttype_sub_tr t1 t2 :
  S.Resulttype_sub (S.mk_list _ t1) (S.mk_list _ t2) ->
  values_subtyping (map tr_valtype t1) (map tr_valtype t2).
Proof.
  move=> H; inversion H; subst.
  elim: H3 => [|x y l l' Hxy _ IH] //=.
  by rewrite /values_subtyping /= (Valtype_sub_tr Hxy).
Qed.

Lemma Resulttype_sub_tr' t1 t2 :
  S.Resulttype_sub (S.mk_list _ t1) t2 ->
  values_subtyping (map tr_valtype t1) (tr_resulttype t2).
Proof. case: t2 => l. exact: Resulttype_sub_tr. Qed.

Lemma values_subtyping_refl ts : values_subtyping ts ts.
Proof. by elim: ts => //= t ts IH; rewrite /values_subtyping /= /value_subtyping eqxx. Qed.

Lemma In_iota_N (n : N) (k : nat) :
  is_true (N.ltb n (N.of_nat k)) -> List.In n (iota_N 0 k).
Proof.
  move=> /N.ltb_spec0 Hn. rewrite /iota_N.
  have -> : n = N.of_nat (N.to_nat n) by lia.
  apply: List.in_map. apply/List.in_seq. split; lia.
Qed.

(** Well-formedness of operators fixes their WasmCert side conditions. *)

Lemma wf_num_typeof nt c : S.wf_num_ nt c -> typeof_num (tr_num c) = tr_numtype nt.
Proof. by case => [nt' t x _ _ /eqP -> | nt' t x _ /eqP ->]; case: t x => [] []. Qed.

Lemma wf_unop_agree nt op : S.wf_unop_ nt op -> unop_type_agree (tr_numtype nt) (tr_unop op).
Proof. by case => [nt' t x /eqP -> | nt' t x /eqP ->]; case: t; case: x. Qed.

Lemma wf_binop_agree nt op : S.wf_binop_ nt op -> binop_type_agree (tr_numtype nt) (tr_binop op).
Proof. by case => [nt' t x /eqP -> | nt' t x /eqP ->]; case: t; case: x. Qed.

Lemma wf_relop_agree nt op : S.wf_relop_ nt op -> relop_type_agree (tr_numtype nt) (tr_relop op).
Proof. by case => [nt' t x /eqP -> | nt' t x /eqP ->]; case: t; case: x. Qed.

Lemma wf_testop_int nt op : S.wf_testop_ nt op -> is_int_t (tr_numtype nt).
Proof. by case => nt' t x /eqP ->; case: t. Qed.

Lemma wf_cvtop_valid nt1 nt2 op :
  S.wf_cvtop__ nt2 nt1 op ->
  cvtop_valid (tr_numtype nt1) (tr_cvtop op).1 (tr_numtype nt2) (tr_cvtop op).2.
Proof.
  move=> H; inversion H; subst;
  repeat match goal with Hb : is_true (_ == _) |- _ => move/eqP: Hb => Hb; subst end;
  match goal with Hx : _ |- _ => match type of Hx with
    | S.wf_cvtop__Inn_1_Inn_2 _ _ _ => inversion Hx
    | S.wf_cvtop__Inn_1_Fnn_2 _ _ _ => inversion Hx
    | S.wf_cvtop__Fnn_1_Inn_2 _ _ _ => inversion Hx
    | S.wf_cvtop__Fnn_1_Fnn_2 _ _ _ => inversion Hx end end; subst;
  repeat match goal with t : S.Inn |- _ => destruct t | t : S.Fnn |- _ => destruct t end;
  try (vm_compute; reflexivity);
  match goal with Hb : is_true ?b |- _ => vm_compute in Hb; discriminate end.
Qed.

Lemma Qle_N (x m d : N) : (0 < d)%num ->
  Qle_bool (inject_Z (Z.of_N x)) (inject_Z (Z.of_N m) / inject_Z (Z.of_N d)) -> (x * d <= m)%num.
Proof.
  move=> Hd /Qle_bool_iff. case: d Hd => [|p] Hd; first lia.
  rewrite /Qle /= => H. nia.
Qed.

Lemma Qlt_N (x m d : N) : (0 < d)%num ->
  is_true (S.Qlt_bool (inject_Z (Z.of_N x)) (inject_Z (Z.of_N m) / inject_Z (Z.of_N d))) ->
  (x * d < m)%num.
Proof.
  move=> Hd; rewrite /S.Qlt_bool => /negP H. case: d Hd H => [|p] Hd H; first lia.
  case: (N.lt_ge_cases (x * N.pos p) m) => // Hge. exfalso; apply: H.
  apply/Qle_bool_iff. rewrite /Qle /=. nia.
Qed.

Lemma Qle_N2 (x m d k : N) : (0 < d)%num ->
  Qle_bool (inject_Z (Z.of_N x)) (inject_Z (Z.of_N m) / inject_Z (Z.of_N d) * inject_Z (Z.of_N k)) ->
  (x * d <= m * k)%num.
Proof.
  move=> Hd /Qle_bool_iff. case: d Hd => [|p] Hd; first lia.
  rewrite /Qle /= => H. nia.
Qed.

Lemma Qeq_N (a b c : N) : (0 < c)%num ->
  Qeq_bool (inject_Z (Z.of_N a)) (inject_Z (Z.of_N b) / inject_Z (Z.of_N c)) -> (a * c = b)%num.
Proof.
  move=> Hc /Qeq_bool_iff. case: c Hc => [|p] Hc; first lia.
  rewrite /Qeq /= => H. nia.
Qed.

Lemma vload_pack_bound (a o m k : N) (x : sx) :
  (m = 8 \/ m = 16 \/ m = 32 \/ m = 64)%num -> (m * k * 2 = 128)%num -> (2 ^ a * 8 <= m * k)%num ->
  load_vec_bounds (LVA_extend (m, k) x) {| memarg_offset := o; memarg_align := a |}.
Proof.
  move=> Hm Hmk H. rewrite /load_vec_bounds. apply/N.leb_spec0.
  case: Hm => [?|[?|[?|?]]]; subst m; cbn [memarg_align];
  [change (8/8)%num with 1%num | change (16/8)%num with 2%num
  | change (32/8)%num with 4%num | change (64/8)%num with 8%num]; lia.
Qed.

Lemma div8_bound (a n : N) :
  (n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%num -> (2 ^ a * 8 <= n)%num -> (2 ^ a <=? n / 8)%num.
Proof.
  move=> Hn H. apply/N.leb_spec0.
  case: Hn => [?|[?|[?|?]]]; subst n;
  [change (8/8)%num with 1%num | change (16/8)%num with 2%num
  | change (32/8)%num with 4%num | change (64/8)%num with 8%num]; lia.
Qed.

Lemma wf_sz_cases n : S.wf_sz (S.mk_sz n) -> n = 8%num \/ n = 16%num \/ n = 32%num \/ n = 64%num.
Proof.
  move=> H; inversion H; subst.
  move: H1 => /orP [/orP [/orP [/eqP -> | /eqP ->] | /eqP ->] | /eqP ->]; auto.
Qed.

Lemma shape_unpack_tr sh : typeof_shape_unpacked (tr_shape sh) = tr_numtype (S.shunpack sh).
Proof. by case: sh => [[] []]. Qed.

Lemma shape_dim_tr sh : S.wf_shape sh -> shape_dim (tr_shape sh) = S.proj_dim_0 (S.fun_dim sh).
Proof.
  case=> lt d Hd /eqP; case: d Hd => n Hd; inversion Hd; subst.
  move: H0 => /orP [/orP [/orP [/orP [/eqP -> | /eqP ->] | /eqP ->] | /eqP ->] | /eqP ->];
  by case: lt.
Qed.

Lemma br_table_aux C ls t :
  List.Forall (fun l => is_true (N.ltb (S.proj_uN_0 l) (N.of_nat (size (S.LABELS C))))) ls ->
  List.Forall (fun l => S.Resulttype_sub (S.mk_list _ t) (S.lookup_total (S.LABELS C) (S.proj_uN_0 l))) ls ->
  List.Forall (fun i => exists ts', lookup_N (tc_labels (tr_context C)) i = Some ts' /\
                                   values_subtyping (map tr_valtype t) ts') (map tr_u32 ls).
Proof.
  elim: ls => [|l ls IH] //= H1 H2; inversion H1; inversion H2; subst.
  constructor; last by apply: IH.
  exists (tr_resulttype (S.lookup_total (S.LABELS C) (S.proj_uN_0 l))); split.
  - by rewrite /tr_u32 lookup_N_map.
  - exact: Resulttype_sub_tr'.
Qed.

Ltac lk := rewrite /= lookup_N_map; last by assumption.
Ltac rw_eqs := unfold tr_u32; repeat match goal with H : is_true (_ == _) |- _ => move/eqP: H => H; try rewrite H end.
Ltac inv_wf := match goal with H : S.wf_instr _ |- _ => inversion H; subst end.
Ltac sz_cases :=
  repeat match goal with
  | H : S.wf_loadop_ _ _ |- _ => inversion H; subst; clear H
  | H : S.wf_loadop_Inn _ _ |- _ => inversion H; subst; clear H
  | H : S.wf_vloadop_ _ _ |- _ => inversion H; subst; clear H
  | H : List.Forall _ (S.option_to_list (Some _)) |- _ => inversion H; subst; clear H
  | H : S.wf_sz (S.mk_sz _) |- _ =>
      let K := fresh in have K := wf_sz_cases H; clear H; case: K => [?|[?|[?|?]]]; subst
  end.

Theorem Instr_ok_tr : forall C i ft,
  S.Instr_ok C i ft -> be_typing (tr_context C) [:: tr_instr i] (tr_functype ft).
Proof.
  move=> C i ft H.
  induction H using Instr_ok_mut with
    (P0 := fun C ins ft _ => be_typing (tr_context C) (tr_instrs ins) (tr_functype ft)).
  all: cbn [S.coerce S.proj_uN_0_coercion S.proj_dim_0_coercion] in *.
  all: cbn [tr_instr tr_functype tr_resulttype map].
  - (* nop *) by apply: bet_nop.
  - (* unreachable *) by apply: bet_unreachable.
  - (* drop *) by apply: bet_drop.
  - (* select_expl *) by apply: bet_select_Some.
  - (* select_impl *)
    apply: bet_select_None. inversion v; subst => //.
    case/orP: i => /eqP ->; [by case: v_numtype | by case: v_vectype].
  - (* block *)
    rewrite tr_context_label in IHInstr_ok.
    eapply bet_block; [by apply: Blocktype_ok_tr | exact IHInstr_ok].
  - (* loop *)
    rewrite tr_context_label in IHInstr_ok.
    eapply bet_loop; [by apply: Blocktype_ok_tr | exact IHInstr_ok].
  - (* if *)
    rewrite map_cat. rewrite tr_context_label in IHInstr_ok IHInstr_ok0.
    eapply bet_if_wasm; [by apply: Blocktype_ok_tr | exact IHInstr_ok | exact IHInstr_ok0].
  - (* br *)
    rewrite map_cat. apply: bet_br. lk.
    by move: i0; case: (S.lookup_total _ _) => l' /= /eqP ->.
  - (* br_if *)
    rewrite map_cat. apply: bet_br_if. lk.
    by move: i0; case: (S.lookup_total _ _) => l' /= /eqP ->.
  - (* br_table *)
    rewrite !map_cat. apply: bet_br_table.
    apply/List.Forall_app; split; first exact: br_table_aux.
    apply: (br_table_aux (ls := [:: l'])); by constructor.
  - (* call *) apply: bet_call. lk. by rw_eqs.
  - (* call_indirect *)
    rewrite map_cat. eapply bet_call_indirect; first by lk; reflexivity.
    + by rw_eqs.
    + lk. by rw_eqs.
  - (* return *) rewrite map_cat. apply: bet_return. rewrite /=. by rw_eqs.
  - (* const *)
    rewrite tr_valtype_num. inv_wf. rewrite -(wf_num_typeof ltac:(eassumption)).
    by apply: bet_const_num.
  - (* unop *) rewrite tr_valtype_num. inv_wf. apply: bet_unop. eapply wf_unop_agree; eassumption.
  - (* binop *) rewrite tr_valtype_num. inv_wf. apply: bet_binop. eapply wf_binop_agree; eassumption.
  - (* testop *) rewrite tr_valtype_num. inv_wf. apply: bet_testop. eapply wf_testop_int; eassumption.
  - (* relop *) rewrite tr_valtype_num. inv_wf. apply: bet_relop. eapply wf_relop_agree; eassumption.
  - (* cvtop *) rewrite !tr_valtype_num. inv_wf. apply: bet_cvtop. eapply wf_cvtop_valid; eassumption.
  - (* ref_null *) rewrite tr_valtype_ref. by apply: bet_ref_null.
  - (* ref_func *)
    eapply bet_ref_func; first by lk; reflexivity.
    exact: In_iota_N.
  - (* ref_is_null *) rewrite tr_valtype_ref. by apply: bet_ref_is_null.
  - (* vconst *) by apply: bet_const_vec.
  - (* vvunop *) by apply: bet_vunop.
  - (* vvbinop *) apply: bet_vbinop. by rewrite /vbinop_valid; case: (_ == _).
  - (* vvternop *) by apply: bet_vternop.
  - (* vvtestop *) by apply: bet_vtestop.
  - (* vunop *) by apply: bet_vunop.
  - (* vbinop *) apply: bet_vbinop. by rewrite /vbinop_valid; case: (_ == _).
  - (* vtestop *) by apply: bet_vtestop.
  - (* vrelop *) apply: bet_vbinop. by rewrite /vbinop_valid; case: (_ == _).
  - (* vshiftop *) by apply: bet_vshiftop.
  - (* vbitmask *) by apply: bet_vtestop.
  - (* vswizzle *) apply: bet_vbinop. by rewrite /vbinop_valid; case: (_ == _).
  - (* vshuffle *)
    apply: bet_vbinop. rewrite /vbinop_valid; case: (_ == _) => //.
    inv_wf. match goal with H : is_true ((_ == S.mk_ishape _) && _) |- _ =>
      move: H => /andP [/eqP Hsh _] end. subst sh.
    have -> // : List.forallb (fun n => N.ltb n 32) (map tr_u32 i_lst) = true.
    apply/List.forallb_forall => n /List.in_map_iff [l [<- Hl]].
    move/List.Forall_forall: f => /(_ l Hl). by cbn.
  - (* vsplat *)
    rewrite tr_valtype_num -shape_unpack_tr. by apply: bet_splat_vec.
  - (* vextract_lane *)
    rewrite tr_valtype_num -shape_unpack_tr. inv_wf. apply: bet_extract_vec.
    by rewrite shape_dim_tr.
  - (* vreplace_lane *)
    rewrite tr_valtype_num -shape_unpack_tr. inv_wf. apply: bet_replace_vec.
    by rewrite shape_dim_tr.
  - (* vextunop *) by apply: bet_vunop.
  - (* vextbinop *) apply: bet_vbinop. by rewrite /vbinop_valid; case: (_ == _).
  - (* vnarrow *) apply: bet_vbinop. by rewrite /vbinop_valid; case: (_ == _).
  - (* vcvtop *) by apply: bet_vunop.
  - (* local_get *) apply: bet_local_get. lk. by rw_eqs.
  - (* local_set *) apply: bet_local_set. lk. by rw_eqs.
  - (* local_tee *) apply: bet_local_tee. lk. by rw_eqs.
  - (* global_get *) eapply bet_global_get; first by lk; reflexivity. by rw_eqs.
  - (* global_set *) eapply bet_global_set; first by lk; reflexivity.
    + by rw_eqs.
    + rw_eqs. by rewrite /is_mut /= eqxx.
  - (* table_get *)
    rewrite tr_valtype_ref. eapply bet_table_get; first by lk; reflexivity. by rw_eqs.
  - (* table_set *)
    rewrite tr_valtype_ref. eapply bet_table_set; first by lk; reflexivity. by rw_eqs.
  - (* table_size *) eapply bet_table_size. lk. reflexivity.
  - (* table_grow *)
    rewrite tr_valtype_ref. eapply bet_table_grow; first by lk; reflexivity. by rw_eqs.
  - (* table_fill *)
    rewrite tr_valtype_ref. eapply bet_table_fill; first by lk; reflexivity. by rw_eqs.
  - (* table_copy *)
    eapply bet_table_copy; first by lk; reflexivity.
    + by rw_eqs.
    + by lk; reflexivity.
    + by rw_eqs.
  - (* table_init *)
    eapply bet_table_init; first by lk; reflexivity.
    + by rw_eqs.
    + lk. by rw_eqs.
  - (* elem_drop *) eapply bet_elem_drop. lk. reflexivity.
  - (* memory_size *) eapply bet_memory_size. lk. reflexivity.
  - (* memory_grow *) eapply bet_memory_grow. lk. reflexivity.
  - (* memory_fill *) eapply bet_memory_fill. lk. reflexivity.
  - (* memory_copy *) eapply bet_memory_copy. lk. reflexivity.
  - (* memory_init *) eapply bet_memory_init; lk; reflexivity.
  - (* data_drop *) eapply bet_data_drop. lk. reflexivity.
  - (* load_val *)
    rewrite tr_valtype_num. eapply bet_load; first by lk; reflexivity.
    apply Qle_N in i2 => //. rewrite /load_store_t_bounds /tr_memarg /=.
    destruct nt; cbn in i2 |- *; apply/N.leb_spec0; rewrite /tr_u32; lia.
  - (* load_pack *)
    rewrite tr_valtype_Inn. eapply bet_load; first by lk; reflexivity.
    apply Qle_N in i1 => //. inv_wf; sz_cases;
      repeat match goal with t : S.Inn |- _ => destruct t end; cbn in *;
      try (match goal with Hb : _ |- _ => vm_compute in Hb; discriminate end);
      rewrite /load_store_t_bounds /tr_memarg /tr_u32 /= ?andbT; apply N.leb_le; lia.
  - (* store_val *)
    rewrite tr_valtype_num. eapply bet_store; first by lk; reflexivity.
    apply Qle_N in i2 => //. rewrite /load_store_t_bounds /tr_memarg /=.
    destruct nt; cbn in i2 |- *; apply/N.leb_spec0; rewrite /tr_u32; lia.
  - (* store_pack *)
    rewrite tr_valtype_Inn. eapply bet_store; first by lk; reflexivity.
    apply Qle_N in i1 => //. inv_wf.
    match goal with io : option S.Inn |- _ => destruct io as [i'|] end;
      last by match goal with Hi : (_ <-> _) |- _ => case: Hi => /(_ (eqxx _)) end.
    match goal with Hf : List.Forall2 _ _ _ |- _ => inversion Hf; subst end.
    match goal with Hb : is_true ((_ == S.numtype_Inn _) && _) |- _ =>
      move/andP: Hb => [/eqP Heq Hlt] end.
    have Hi' : i' = v_Inn by destruct i', v_Inn; try discriminate. subst i'.
    sz_cases;
      repeat match goal with t : S.Inn |- _ => destruct t end; cbn in *;
      try (vm_compute in Hlt; discriminate);
      rewrite /load_store_t_bounds /tr_memarg /tr_u32 /= ?andbT; apply N.leb_le; lia.
  - (* vload_val *)
    eapply bet_load_vec; first by lk; reflexivity.
    apply Qle_N in i2 => //. rewrite /load_vec_bounds /tr_memarg /tr_u32 /v128_size /=.
    cbn in i2. apply/N.leb_spec0. lia.
  - (* vload_pack *)
    eapply bet_load_vec; first by lk; reflexivity.
    apply Qle_N2 in i1 => //. inv_wf.
    match goal with H : List.Forall _ (S.option_to_list (Some _)) |- _ => inversion H; subst end.
    match goal with H : S.wf_vloadop_ _ _ |- _ => inversion H; subst end.
    match goal with Hb : is_true ((Qeq_bool _ _) && _) |- _ => move/andP: Hb => [Hq _] end.
    apply Qeq_N in Hq => //.
    apply: vload_pack_bound => //. exact: wf_sz_cases.
  - (* vload_splat *)
    eapply bet_load_vec; first by lk; reflexivity.
    apply Qle_N in i1 => //. inv_wf.
    match goal with H : List.Forall _ (S.option_to_list (Some _)) |- _ => inversion H; subst end.
    match goal with H : S.wf_vloadop_ _ _ |- _ => inversion H; subst end.
    apply: div8_bound => //. exact: wf_sz_cases.
  - (* vload_zero *)
    eapply bet_load_vec; first by lk; reflexivity.
    apply Qle_N in i1 => //. inv_wf.
    match goal with H : List.Forall _ (S.option_to_list (Some _)) |- _ => inversion H; subst end.
    match goal with H : S.wf_vloadop_ _ _ |- _ => inversion H; subst end.
    apply: div8_bound => //. exact: wf_sz_cases.
  - (* vload_lane *)
    inv_wf. have Hsz := wf_sz_cases H2.
    eapply bet_load_vec_lane; first by lk; reflexivity.
    apply Qle_N in i1 => //. rewrite /load_store_vec_lane_bounds /tr_memarg /tr_u32 /=.
    have Hn : (0 < v_n)%num by case: Hsz => [->|[->|[->|->]]].
    move/(Qlt_N Hn): i2 => i2.
    case: Hsz => [?|[?|[?|?]]]; subst v_n; (cbn in i1, i2 |- *;
      apply/andP; split; [apply/N.leb_spec0|apply/N.ltb_spec0]; lia).
  - (* vstore *)
    eapply bet_store_vec; first by lk; reflexivity.
    apply Qle_N in i2 => //. rewrite /store_vec_bounds /tr_memarg /tr_u32 /v128_size /=.
    cbn in i2. apply/N.leb_spec0. lia.
  - (* vstore_lane *)
    inv_wf. have Hsz := wf_sz_cases H2.
    eapply bet_store_vec_lane; first by lk; reflexivity.
    apply Qle_N in i1 => //. rewrite /load_store_vec_lane_bounds /tr_memarg /tr_u32 /=.
    have Hn : (0 < v_n)%num by case: Hsz => [->|[->|[->|->]]].
    move/(Qlt_N Hn): i2 => i2.
    case: Hsz => [?|[?|[?|?]]]; subst v_n; (cbn in i1, i2 |- *;
      apply/andP; split; [apply/N.leb_spec0|apply/N.ltb_spec0]; lia).
  - (* empty *) by apply: bet_empty.
  - (* instr *) exact: IHInstr_ok.
  - (* seq *) rewrite /tr_instrs map_cat. by eapply bet_composition'; eauto.
  - (* sub *)
    eapply bet_subtyping; first exact: IHInstr_ok.
    exists [::], [::], (map tr_valtype t'_1_lst), (map tr_valtype t'_2_lst).
    split; first done. split; first done. split; first done.
    by split; apply: Resulttype_sub_tr.
  - (* frame *) rewrite !map_cat. exact: bet_weakening.
Qed.

(* Instruction sequences: the non-mutual induction principle of [Instrs_ok]
   treats the [Instr_ok] premise as an ordinary hypothesis. *)
Theorem Instrs_ok_tr : forall C ins ft,
  S.Instrs_ok C ins ft -> be_typing (tr_context C) (tr_instrs ins) (tr_functype ft).
Proof.
  move=> C ins ft H. elim: H => {C ins ft}.
  - move=> *. by apply: bet_empty.
  - move=> C i t1 t2 Hi *. exact: (Instr_ok_tr Hi).
  - move=> C is1 is2 t1 t3 t2 _ IH1 _ IH2 *.
    rewrite /tr_instrs map_cat. exact: bet_composition' IH1 IH2.
  - move=> C ins t1' t2' t1 t2 _ IH Hs1 Hs2 *.
    eapply bet_subtyping; first exact: IH.
    exists [::], [::], (map tr_valtype t1'), (map tr_valtype t2').
    split; first done. split; first done. split; first done.
    by split; apply: Resulttype_sub_tr.
  - move=> C ins t t1 t2 _ IH *. cbn. rewrite !map_cat. exact: bet_weakening.
Qed.

End Typing.

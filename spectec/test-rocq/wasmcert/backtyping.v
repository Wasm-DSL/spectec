(* Typing reflection: WasmCert's basic-instruction typing ([be_typing]) implies
   SpecTec's instruction typing ([Instrs_ok]) of the back-translation
   ([backtranslation.v]).

   Together with [typing.v] (SpecTec typing implies WasmCert typing of the
   forward translation) and the round-trip lemmas of [backtranslation_props.v],
   this shows that the two type systems agree on Wasm 2.0 instructions
   ([Instrs_ok_iff]). *)

From Stdlib Require Import NArith ZArith QArith Lia List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
From Wasm Require Import datatypes datatypes_properties operations typing subtyping.
From WasmSpectec Require wasm.
From WasmCertBridge Require Import translation backtranslation backtranslation_props.
From WasmCertBridge Require typing.

Module S := WasmSpectec.wasm.
Module T := WasmCertBridge.typing.

(* The eqType instances of SpecTec's types, without its names. *)
Import (canonicals) WasmSpectec.wasm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope N_scope with num.

(** * Lookups *)

Lemma lookup_N_Some {A : Type} (l : seq A) n x :
  lookup_N l n = Some x -> (N.to_nat n < size l)%coq_nat /\ forall d, nth d l (N.to_nat n) = x.
Proof.
  rewrite /lookup_N. move: (N.to_nat n) => k.
  elim: l k => [|y l IH] [|k] //= H.
  - case: H => <-. split => //. lia.
  - case: (IH _ H) => Hk Hn. split => //. lia.
Qed.

Lemma lookup_map_of {A B : Type} `{S.Inhabited B} (f : A -> B) (l : seq A) n x :
  lookup_N l n = Some x ->
  is_true (N.ltb n (N.of_nat (size (map f l)))) /\ S.lookup_total (map f l) n = f x.
Proof.
  move=> Hl. case: (lookup_N_Some Hl) => Hn Hx. rewrite size_map. split; first by apply/N.ltb_spec0; lia.
  rewrite /S.lookup_total (nth_map x); last by apply/ltP.
  by rewrite Hx.
Qed.

Lemma lookup_olist {A B : Type} `{S.Inhabited B} (f : A -> option B) (l : seq A) (r : seq B) n x :
  olist f l = Some r -> lookup_N l n = Some x ->
  exists y, f x = Some y /\ is_true (N.ltb n (N.of_nat (size r))) /\ S.lookup_total r n = y.
Proof.
  move=> Hr Hx. case: (olist_lookup Hr Hx) => y [Hy Hry]. exists y. split => //.
  case: (lookup_N_Some Hry) => Hn Hry'. split; first by apply/N.ltb_spec0; lia.
  by rewrite /S.lookup_total Hry'.
Qed.

(** * Types *)

Lemma of_valtype_num t : of_valtype (T_num t) = S.valtype_numtype (of_numtype t).
Proof. by case: t. Qed.

Lemma of_valtype_ref t : of_valtype (T_ref t) = S.valtype_reftype (of_reftype t).
Proof. by case: t. Qed.

Lemma Valtype_sub_of t1 t2 : value_subtyping t1 t2 -> S.Valtype_sub (of_valtype t1) (of_valtype t2).
Proof. by rewrite /value_subtyping => /orP [/eqP -> | /eqP ->]; constructor. Qed.

Lemma Resulttype_sub_of ts1 ts2 :
  values_subtyping ts1 ts2 -> S.Resulttype_sub (of_resulttype ts1) (of_resulttype ts2).
Proof.
  rewrite /values_subtyping => H. constructor.
  - by rewrite !size_map (all2_size H).
  - elim: ts1 ts2 H => [|t1 ts1 IH] [|t2 ts2] //= /andP [H1 H2].
    constructor; [exact: Valtype_sub_of | exact: IH].
Qed.

Lemma Resulttype_sub_refl ts : S.Resulttype_sub (S.mk_list _ ts) (S.mk_list _ ts).
Proof.
  constructor => //. by elim: ts => //= t ts IH; constructor => //; constructor.
Qed.

Lemma Resulttype_sub_cat ts1 ts2 ts :
  S.Resulttype_sub (S.mk_list _ ts1) (S.mk_list _ ts2) ->
  S.Resulttype_sub (S.mk_list _ (ts1 ++ ts)) (S.mk_list _ (ts2 ++ ts)).
Proof.
  move=> H; inversion H as [? ? Hsz H2]; subst. constructor.
  - move/eqP: Hsz => Hsz. by rewrite !size_cat !Nat2N.inj_add Hsz.
  - apply: List.Forall2_app => //. by elim: ts => //= t ts IH; constructor => //; constructor.
Qed.

Lemma shunpack_of sh :
  S.valtype_numtype (of_numtype (typeof_shape_unpacked sh)) = S.valtype_numtype (S.shunpack (of_shape sh)).
Proof. by case: sh => [[]|[]]. Qed.

Lemma dim_of sh x :
  (x <? shape_dim sh)%num = true -> is_true (x <? S.proj_dim_0 (S.fun_dim (of_shape sh)))%num.
Proof. by case: sh => [[]|[]]. Qed.

Lemma wf_dim_of sh : S.wf_dim (S.fun_dim (of_shape sh)).
Proof. by case: sh => [[]|[]]; constructor. Qed.


Lemma sz_ok_cases n : sz_ok n -> n = 8%num \/ n = 16%num \/ n = 32%num \/ n = 64%num.
Proof.
  rewrite /sz_ok.
  by move=> /orP [/orP [/orP [/N.eqb_spec -> | /N.eqb_spec ->] | /N.eqb_spec ->] | /N.eqb_spec ->]; auto.
Qed.

Lemma div8_le w a : sz_ok w -> (2 ^ a <= w / 8)%num -> (2 ^ a * 8 <= w)%num.
Proof.
  case/sz_ok_cases => [->|[->|[->|->]]];
  [change (8/8)%num with 1%num | change (16/8)%num with 2%num
  | change (32/8)%num with 4%num | change (64/8)%num with 8%num]; lia.
Qed.

Lemma div128_lt w x : sz_ok w -> (x < 128 / w)%num -> (x * w < 128)%num.
Proof.
  case/sz_ok_cases => [->|[->|[->|->]]];
  [change (128/8)%num with 16%num | change (128/16)%num with 8%num
  | change (128/32)%num with 4%num | change (128/64)%num with 2%num]; lia.
Qed.

(** * Contexts *)

Lemma of_context_wf C C' : of_context C = Some C' -> S.wf_context C'.
Proof. by case/of_context_sound. Qed.

Definition label_ctx (ts : S.resulttype) : S.context :=
  {| S.context_TYPES := [::]; S.context_FUNCS := [::]; S.context_GLOBALS := [::];
     S.context_TABLES := [::]; S.context_MEMS := [::]; S.context_ELEMS := [::];
     S.context_DATAS := [::]; S.context_LOCALS := [::]; S.LABELS := [:: ts];
     S.context_RETURN := None |}.

Lemma of_context_label C C' ts :
  of_context C = Some C' ->
  of_context (upd_label C ([:: ts] ++ tc_labels C)) = Some (S._append (label_ctx (of_resulttype ts)) C').
Proof.
  case: C => ty fu ta me gl el da lo la re rf. rewrite /of_context /= => H. odestr H.
  by rewrite /upd_label /upd_local_label_return /=.
Qed.

(** * Alignment bounds *)

Lemma Qle_N_rev (x m d : N) : (0 < d)%num -> (x * d <= m)%num ->
  Qle_bool (inject_Z (Z.of_N x)) (inject_Z (Z.of_N m) / inject_Z (Z.of_N d)).
Proof.
  move=> Hd H. apply/Qle_bool_iff. case: d Hd H => [|p] Hd H; first lia.
  rewrite /Qle /=. nia.
Qed.

Lemma Qle_N2_rev (x m d k : N) : (0 < d)%num -> (x * d <= m * k)%num ->
  Qle_bool (inject_Z (Z.of_N x)) (inject_Z (Z.of_N m) / inject_Z (Z.of_N d) * inject_Z (Z.of_N k)).
Proof.
  move=> Hd H. apply/Qle_bool_iff. case: d Hd H => [|p] Hd H; first lia.
  rewrite /Qle /=. nia.
Qed.

Lemma Qlt_N_rev (x m d : N) : (0 < d)%num -> (x * d < m)%num ->
  is_true (S.Qlt_bool (inject_Z (Z.of_N x)) (inject_Z (Z.of_N m) / inject_Z (Z.of_N d))).
Proof.
  move=> Hd H. rewrite /S.Qlt_bool. apply/negP => /Qle_bool_iff.
  case: d Hd H => [|p] Hd H; first lia. rewrite /Qle /=. nia.
Qed.


Lemma of_context_fields C C' :
  of_context C = Some C' ->
  S.context_TYPES C' = map of_functype (tc_types C) /\
  S.context_FUNCS C' = map of_functype (tc_funcs C) /\
  S.context_GLOBALS C' = map of_globaltype (tc_globals C) /\
  olist of_tabletype (tc_tables C) = Some (S.context_TABLES C') /\
  olist of_memtype (tc_mems C) = Some (S.context_MEMS C') /\
  S.context_ELEMS C' = map of_reftype (tc_elems C) /\
  S.context_DATAS C' = map (fun _ => S.OK) (tc_datas C) /\
  S.context_LOCALS C' = map of_valtype (tc_locals C) /\
  S.LABELS C' = map of_resulttype (tc_labels C) /\
  S.context_RETURN C' = option_map of_resulttype (tc_return C).
Proof. rewrite /of_context => H. odestr H. by repeat split. Qed.

(* Names the fields of a back-translated context. *)
Ltac fields HC :=
  case: (of_context_fields HC) => HT [HF [HG [HTa [HM [HE [HD [HL [HLab HR]]]]]]]].

Lemma table_lookup C C' x tab :
  of_context C = Some C' -> lookup_N (tc_tables C) x = Some tab ->
  exists lim, is_true (x <? N.of_nat (size (S.context_TABLES C')))%num /\
    S.lookup_total (S.context_TABLES C') x = S.mk_tabletype lim (of_reftype (tt_elem_type tab)) /\
    S.wf_tabletype (S.mk_tabletype lim (of_reftype (tt_elem_type tab))).
Proof.
  case/of_context_fields => _ [_ [_ [Ht _]]] Hx.
  case: (lookup_olist Ht Hx) => tt [Ett [Hlt Hl]]. have Ett' := Ett.
  move: Ett'; rewrite /of_tabletype => Ett'. odestr Ett'.
  case/of_tabletype_sound: Ett => _ Hw. exists l. by rewrite -Ett' in Hw *.
Qed.

Lemma mem_lookup C C' mem :
  of_context C = Some C' -> lookup_N (tc_mems C) 0%num = Some mem ->
  exists mt, is_true (0 <? N.of_nat (size (S.context_MEMS C')))%num /\
    S.lookup_total (S.context_MEMS C') 0 = mt /\ S.wf_memtype mt.
Proof.
  case/of_context_fields => _ [_ [_ [_ [Hm _]]]] Hx.
  case: (lookup_olist Hm Hx) => mt [Emt [Hlt Hl]]. exists mt. split => //. split => //.
  by case/of_memtype_sound: Emt.
Qed.

Lemma blocktype_back C C' tb bt tn tm :
  of_context C = Some C' -> of_blocktype tb = Some bt -> expand_t C tb = Some (Tf tn tm) ->
  S.Blocktype_ok C' bt (of_functype (Tf tn tm)).
Proof.
  move=> HC Hbt He. have Hctx := of_context_wf HC.
  case: tb Hbt He => [n|[t|]] /= Hbt He.
  - move: Hbt; rewrite /option_map. case E: (of_u32 n) => [u|] // [<-].
    case/of_u32_Some: E => -> Hn. fields HC.
    case: (lookup_map_of of_functype He) => Hlt Hl.
    apply: S.Blocktype_ok__typeidx => //; rewrite /= ?HT //.
    + by rewrite Hl.
    + constructor. exact/wf_uN_iff.
  - case: Hbt He => <- [<- <-]. by apply: S.Blocktype_ok__valtype => //; constructor.
  - case: Hbt He => <- [<- <-]. by apply: S.Blocktype_ok__valtype => //; constructor.
Qed.

Lemma lookup_label C C' i ts :
  of_context C = Some C' -> lookup_N (tc_labels C) i = Some ts ->
  is_true (i <? N.of_nat (size (S.LABELS C')))%num /\
  S.lookup_total (S.LABELS C') i = of_resulttype ts.
Proof. case/of_context_fields => _ [_ [_ [_ [_ [_ [_ [_ [-> _]]]]]]]]. exact: lookup_map_of. Qed.

(** * Typing reflection *)

Section Typing.

Context `{hfc : host_function_class}.

Variable vec_instr : basic_instruction -> option S.instr.

Hypothesis vec_instr_sound :
  forall b i, vec_instr b = Some i -> tr_instr i = b /\ S.wf_instr i.
(* [i8x16.shuffle] is the SIMD opcode 13, whose lane indices WasmCert checks. *)
Hypothesis vec_code_shuffle : forall sh ls, vec_code (S.VSHUFFLE sh ls) = 13%num.

Lemma instrs_single C' b ins t1 t2 :
  S.wf_context C' -> of_instrs vec_instr [:: b] = Some ins ->
  (forall i, of_instr vec_instr b = Some i -> S.wf_instr i ->
     S.Instr_ok C' i (S.mk_functype (S.mk_list _ t1) (S.mk_list _ t2))) ->
  S.Instrs_ok C' ins (S.mk_functype (S.mk_list _ t1) (S.mk_list _ t2)).
Proof.
  move=> Hctx. rewrite /of_instrs /=. case E: (of_instr vec_instr b) => [i|] // [<-] H.
  have Hwi := proj2 (of_instr_sound vec_instr_sound E).
  by apply: S.Instrs_ok__instr => //; apply: H.
Qed.

(* Start a case on a single instruction: [i] is its back-translation. *)
Ltac single HC Hes :=
  let Hctx := fresh "Hctx" in
  have Hctx := of_context_wf HC;
  apply: (instrs_single Hctx Hes); clear Hes; intros ? Ei Hwi; rewrite /= in Ei; odestr Ei;
  cbn [map]; rewrite ?of_valtype_num ?of_valtype_ref;
  cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0];
  repeat match goal with
  | E : of_u32 _ = Some _ |- _ =>
      let Eu := fresh "Eu" in case/of_u32_Some: E => Eu _; match type of Eu with ?u = _ => subst u end
  | E : of_u8 _ = Some _ |- _ =>
      let Eu := fresh "Eu" in case/of_u8_Some: E => Eu _; match type of Eu with ?u = _ => subst u end
  end.

(* A SIMD instruction typed through its opcode. *)
Ltac vec_case :=
  repeat match goal with v : S.vectype |- _ => destruct v end;
  by econstructor; eauto.

(* An alignment bound, from WasmCert's [N] form. *)
Ltac align_lia Ha tp :=
  cbn [S.coerce S.proj_uN_0_coercion]; rewrite /tr_u32 in Ha; clear -Ha; case: tp Ha => /= Ha; lia.

(* Unfold a back-translated context. *)
Ltac ctx HC := move: HC; rewrite /of_context => HC; odestr HC.

Theorem be_typing_back C es tf :
  be_typing C es tf ->
  forall C' ins, of_context C = Some C' -> of_instrs vec_instr es = Some ins ->
  S.Instrs_ok C' ins (of_functype tf).
Proof.
  elim=> {C es tf}.
  - (* const_num *) move=> C v C' ins HC Hes. single HC Hes. exact: S.const.
  - (* const_vec *) move=> C [v] C' ins HC Hes. single HC Hes. exact: S.vconst.
  - (* ref_null *) move=> C t C' ins HC Hes. single HC Hes. exact: S.ref_null.
  - (* ref_is_null *) move=> C t C' ins HC Hes. single HC Hes. exact: S.ref_is_null.
  - (* ref_func *)
    move=> C t x Hx _ C' ins HC Hes. single HC Hes. ctx HC. case: (lookup_map_of of_functype Hx) => Hlt Hl.
    eapply S.ref_func; [exact: Hlt | exact: eqxx | done | done].
  - (* unop *)
    move=> C t op _ C' ins HC Hes. single HC Hes. exact: S.unop.
  - (* binop *)
    move=> C t op _ C' ins HC Hes. single HC Hes. exact: S.binop.
  - (* testop *)
    move=> C t op _ C' ins HC Hes. single HC Hes. exact: S.testop.
  - (* relop *)
    move=> C t op _ C' ins HC Hes. single HC Hes. exact: S.relop.
  - (* cvtop *)
    move=> C op t1 t2 sx _ C' ins HC Hes. single HC Hes. exact: S.cvtop.
  - (* vunop *)
    move=> C op C' ins HC Hes. single HC Hes. case/vec_instr_sound: Ei => Htr _.
    case: i Htr Hwi => //= *; vec_case.
  - (* vbinop *)
    move=> C [opc lanes] Hvalid C' ins HC Hes. single HC Hes. case/vec_instr_sound: Ei => Htr _.
    case: i Htr Hwi => //= *; try vec_case.
    (* i8x16.shuffle: WasmCert checks the lane indices *)
    match goal with H : BI_vbinop _ = BI_vbinop _ |- _ => case: H => Hopc Hl end.
    match goal with ls : seq S.laneidx |- _ => rename ls into ls0 end.
    rewrite vec_code_shuffle in Hopc. subst opc lanes. rewrite /vbinop_valid /= in Hvalid.
    match goal with H : S.wf_instr (S.VSHUFFLE _ _) |- _ => rename H into Hw end.
    have Hw' := Hw. inversion Hw'; subst.
    match goal with Hb : is_true ((_ == S.mk_ishape _) && _) |- _ => move: Hb => /andP [/eqP Esh _] end. subst.
    apply: S.vshuffle => //.
    + apply/List.Forall_forall => l Hl. move: Hvalid. case: ifP => // /List.forallb_forall H _.
      case: l Hl => n Hl.
      have Hn : List.In n (map tr_u32 ls0) by apply/List.in_map_iff; exists (S.mk_uN n).
      exact: (H n Hn).
  - (* vternop *)
    move=> C op C' ins HC Hes. single HC Hes. case/vec_instr_sound: Ei => Htr _.
    case: i Htr Hwi => //= *; vec_case.
  - (* vtestop *)
    move=> C op C' ins HC Hes. single HC Hes. case/vec_instr_sound: Ei => Htr _.
    case: i Htr Hwi => //= *; vec_case.
  - (* vshiftop *)
    move=> C op C' ins HC Hes. single HC Hes. case/vec_instr_sound: Ei => Htr _.
    case: i Htr Hwi => //= *; vec_case.
  - (* splat *)
    move=> C sh C' ins HC Hes. single HC Hes. rewrite shunpack_of. exact: S.vsplat.
  - (* extract_lane *)
    move=> C sh sx x Hx C' ins HC Hes. single HC Hes. rewrite shunpack_of.
    apply: S.vextract_lane => //; [exact: dim_of | exact: wf_dim_of].
  - (* replace_lane *)
    move=> C sh x Hx C' ins HC Hes. single HC Hes. rewrite shunpack_of.
    apply: S.vreplace_lane => //; [exact: dim_of | exact: wf_dim_of].
  - (* unreachable *) move=> C t1 t2 C' ins HC Hes. single HC Hes. exact: S.unreachable.
  - (* nop *) move=> C C' ins HC Hes. single HC Hes. exact: S.nop.
  - (* drop *) move=> C t C' ins HC Hes. single HC Hes. exact: S.drop.
  - (* select_Some *) move=> C t C' ins HC Hes. single HC Hes. exact: S.select_expl.
  - (* select_None *)
    move=> C t Ht C' ins HC Hes. single HC Hes.
    case: t Ht => [n|[]|r|] // _.
    + apply: (S.select_impl _ _ (S.valtype_numtype (of_numtype n)) (of_numtype n) S.V128) => //.
      * by rewrite of_valtype_num; constructor.
      * by rewrite eqxx.
    + apply: (S.select_impl _ _ S.valtype_V128 S.I32 S.V128) => //. by constructor.
    + apply: (S.select_impl _ _ S.valtype_I32 S.I32 S.V128) => //. by constructor.
  - (* block *)
    move=> C tb tn tm es He Hb IH C' ins HC Hes. single HC Hes.
    apply: S.block => //.
    + exact: blocktype_back HC E He.
    + apply: IH E0. exact: of_context_label.
  - (* loop *)
    move=> C tb tn tm es He Hb IH C' ins HC Hes. single HC Hes.
    apply: S.loop => //.
    + exact: blocktype_back HC E He.
    + apply: IH E0. exact: of_context_label.
  - (* if *)
    move=> C tb tn tm es1 es2 He Hb1 IH1 Hb2 IH2 C' ins HC Hes. single HC Hes. rewrite map_cat.
    apply: S.res_if => //.
    + exact: blocktype_back HC E He.
    + apply: IH1 E0. exact: of_context_label.
    + apply: IH2 E1. exact: of_context_label.
  - (* br *)
    move=> C i t1s ts t2s Hi C' ins HC Hes. single HC Hes. rewrite map_cat.
    case: (lookup_label HC Hi) => Hlt Hl.
    apply: S.br => //. by rewrite Hl.
  - (* br_if *)
    move=> C i ts Hi C' ins HC Hes. single HC Hes. rewrite map_cat.
    case: (lookup_label HC Hi) => Hlt Hl.
    apply: S.br_if => //. by rewrite Hl.
  - (* br_table *)
    move=> C i ls ts t1s t2s Hall C' ins HC Hes. single HC Hes. rewrite !map_cat.
    case/olist_u32_sound: E => Els _. subst ls.
    move/List.Forall_app: Hall => [Hall Hi]. inversion Hi as [|? ? [ts' [Hi' Hsub]] _]; subst.
    case: (lookup_label HC Hi') => Hlt Hl.
    apply: S.br_table => //.
    + apply/List.Forall_forall => j Hl'. move/List.Forall_forall: Hall => /(_ (tr_u32 j)).
      case/(_ (List.in_map _ _ _ Hl')) => ts'' [Hl'' _]. by case: (lookup_label HC Hl'').
    + apply/List.Forall_forall => j Hl'. move/List.Forall_forall: Hall => /(_ (tr_u32 j)).
      case/(_ (List.in_map _ _ _ Hl')) => ts'' [Hl'' Hs]. case: (lookup_label HC Hl'') => _ ->.
      exact: Resulttype_sub_of.
    + rewrite Hl. exact: Resulttype_sub_of.
  - (* return *)
    move=> C ts t1s t2s Hr C' ins HC Hes. single HC Hes. rewrite map_cat.
    fields HC.
    apply: S.res_return => //. by rewrite HR Hr.
  - (* call *)
    move=> C i [t1 t2] Hi C' ins HC Hes. single HC Hes.
    fields HC.
    case: (lookup_map_of of_functype Hi) => Hlt Hl.
    apply: S.call => //; rewrite ?HF //. by rewrite Hl.
  - (* call_indirect *)
    move=> C x y tab t1s t2s Hx Hel Hy C' ins HC Hes. single HC Hes. rewrite map_cat.
    case: (table_lookup HC Hx) => lim [Hlt [Hl Hw]]. rewrite Hel in Hl Hw.
    fields HC.
    case: (lookup_map_of of_functype Hy) => Hlt' Hl'.
    apply: (S.call_indirect _ _ _ _ _ lim) => //; rewrite ?HT //.
    + by rewrite Hl.
    + by rewrite Hl'.
  - (* return_call *) move=> C x t1s t2s t3s t4s _ _ C' ins HC Hes. single HC Hes. discriminate.
  - (* return_call_indirect *)
    move=> C x y tabt t1s t2s t3s t4s _ _ _ _ C' ins HC Hes. single HC Hes. discriminate.
  - (* local_get *)
    move=> C x t Hx C' ins HC Hes. single HC Hes. fields HC.
    case: (lookup_map_of of_valtype Hx) => Hlt Hl.
    apply: S.local_get => //; rewrite ?HL //. by rewrite Hl.
  - (* local_set *)
    move=> C x t Hx C' ins HC Hes. single HC Hes. fields HC.
    case: (lookup_map_of of_valtype Hx) => Hlt Hl.
    apply: S.local_set => //; rewrite ?HL //. by rewrite Hl.
  - (* local_tee *)
    move=> C x t Hx C' ins HC Hes. single HC Hes. fields HC.
    case: (lookup_map_of of_valtype Hx) => Hlt Hl.
    apply: S.local_tee => //; rewrite ?HL //. by rewrite Hl.
  - (* global_get *)
    move=> C x gt t Hx Ht C' ins HC Hes. subst t. single HC Hes. fields HC.
    case: (lookup_map_of of_globaltype Hx) => Hlt Hl.
    apply: (S.global_get _ _ _ (of_mut (tg_mut gt))) => //; rewrite ?HG //. by rewrite Hl.
  - (* global_set *)
    move=> C x gt t Hx Ht Hmut C' ins HC Hes. subst t. single HC Hes. fields HC.
    case: (lookup_map_of of_globaltype Hx) => Hlt Hl.
    apply: S.global_set => //; rewrite ?HG //. rewrite Hl /of_globaltype.
    by move: Hmut; rewrite /is_mut => /eqP ->.
  - (* table_get *)
    move=> C x tab t Hx Ht C' ins HC Hes. subst t. single HC Hes.
    case: (table_lookup HC Hx) => lim [Hlt [Hl Hw]].
    apply: (S.table_get _ _ _ lim) => //. by rewrite Hl.
  - (* table_set *)
    move=> C x tab t Hx Ht C' ins HC Hes. subst t. single HC Hes.
    case: (table_lookup HC Hx) => lim [Hlt [Hl Hw]].
    apply: (S.table_set _ _ _ lim) => //. by rewrite Hl.
  - (* table_size *)
    move=> C x tab Hx C' ins HC Hes. single HC Hes.
    case: (table_lookup HC Hx) => lim [Hlt [Hl Hw]].
    apply: (S.table_size _ _ lim (of_reftype (tt_elem_type tab))) => //. by rewrite Hl.
  - (* table_grow *)
    move=> C x tab t Hx Ht C' ins HC Hes. subst t. single HC Hes.
    case: (table_lookup HC Hx) => lim [Hlt [Hl Hw]].
    apply: (S.table_grow _ _ _ lim) => //. by rewrite Hl.
  - (* table_fill *)
    move=> C x tab t Hx Ht C' ins HC Hes. subst t. single HC Hes.
    case: (table_lookup HC Hx) => lim [Hlt [Hl Hw]].
    apply: (S.table_fill _ _ _ lim) => //. by rewrite Hl.
  - (* table_copy *)
    move=> C x y tab1 tab2 t Hx Ht1 Hy Ht2 C' ins HC Hes. subst t. single HC Hes.
    case: (table_lookup HC Hx) => lim1 [Hlt1 [Hl1 Hw1]].
    case: (table_lookup HC Hy) => lim2 [Hlt2 [Hl2 Hw2]]. rewrite Ht2 in Hl2 Hw2.
    apply: (S.table_copy _ _ _ lim1 (of_reftype (tt_elem_type tab1)) lim2) => //.
    + by rewrite Hl1.
    + by rewrite Hl2.
  - (* table_init *)
    move=> C x y tab t Hx Ht Hy C' ins HC Hes. subst t. single HC Hes. fields HC.
    case: (table_lookup HC Hx) => lim [Hlt [Hl Hw]].
    case: (lookup_map_of of_reftype Hy) => Hlt' Hl'.
    apply: (S.table_init _ _ _ lim (of_reftype (tt_elem_type tab))) => //; rewrite ?HE //.
    + by rewrite Hl.
    + by rewrite Hl'.
  - (* elem_drop *)
    move=> C x t Hx C' ins HC Hes. single HC Hes. fields HC.
    case: (lookup_map_of of_reftype Hx) => Hlt Hl.
    apply: (S.elem_drop _ _ (of_reftype t)) => //; rewrite ?HE //. by rewrite Hl.
  - (* load *)
    move=> C m tpsx t mem Hm Hb C' ins HC Hes. single HC Hes.
    match goal with H : of_memarg _ = Some _ |- _ => case/of_memarg_sound: H => Em _ end. subst m. rewrite /= in Hb.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt.
    case: tpsx E Hb Hwi => [[tp sx]|] /= E Hb Hwi; odestr E.
    { match goal with H : of_pack _ _ = Some _ |- _ => case/of_pack_sound: H => Et [Hlt' Hsz] end.
      rewrite Et in Hwi *. move: Hb => /andP [/andP [/N.leb_spec0 Ha _] _].
      case: i Et Hlt' Hwi Hsz => Et Hlt' Hwi Hsz;
        (apply: S.load_pack => //; apply: Qle_N_rev => //; align_lia Ha tp). }
    { move/N.leb_spec0: Hb => Ha.
      case: t Ha Hwi => /= Ha Hwi; (apply: S.load_val => //; apply: Qle_N_rev => //;
        cbn [S.coerce S.proj_uN_0_coercion S.the S.res_size S.valtype_numtype of_numtype];
        rewrite /tr_u32 in Ha; lia). }
  - (* load_vec *)
    move=> C lv m mem Hm Hb C' ins HC Hes. single HC Hes.
    match goal with H : of_memarg _ = Some _ |- _ => case/of_memarg_sound: H => Em _ end. subst m. rewrite /= in Hb.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt.
    case: lv E Hb Hwi => [[n k] sx|w|w|] /= E Hb Hwi; odestr E; move/N.leb_spec0: Hb => Ha.
    + match goal with H : _ = true |- _ => move: H => /andP [/andP [Hn _] _] end.
      apply: S.vload_pack => //.
      apply: Qle_N2_rev => //. cbn [S.coerce S.proj_uN_0_coercion]. rewrite /tr_u32 in Ha.
      case/sz_ok_cases: Hn Ha => [->|[->|[->|->]]] Ha; cbn -[N.pow N.mul] in Ha |- *; nia.
    + match goal with H : _ = true |- _ => move: H => /andP [Hw' _] end.
      apply: S.vload_zero => //.
      apply: Qle_N_rev => //. exact: div8_le.
    + match goal with H : _ = true |- _ => rename H into Hw' end.
      apply: S.vload_splat => //.
      apply: Qle_N_rev => //. exact: div8_le.
    + apply: S.vload_val => //.
      apply: Qle_N_rev => //. cbn [S.coerce S.proj_uN_0_coercion S.the S.res_size].
      rewrite /tr_u32 /v128_size in Ha. lia.
  - (* load_vec_lane *)
    move=> C w m x mem Hm Hb C' ins HC Hes. single HC Hes.
    match goal with H : of_memarg _ = Some _ |- _ => case/of_memarg_sound: H => Em _ end. subst m.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt.
    move: Hb; rewrite /load_store_vec_lane_bounds /= => /andP [/N.leb_spec0 Ha /N.ltb_spec0 Hx].
    match goal with H : sz_ok _ = true |- _ => rename H into Hsz end.
    have Hw0 : (0 < w)%num by case/sz_ok_cases: Hsz => [->|[->|[->|->]]].
    apply: S.vload_lane => //.
    + apply: Qle_N_rev => //. exact: div8_le.
    + apply: Qlt_N_rev => //. exact: div128_lt.
  - (* store *)
    move=> C m tp t mem Hm Hb C' ins HC Hes. single HC Hes.
    match goal with H : of_memarg _ = Some _ |- _ => case/of_memarg_sound: H => Em _ end. subst m. rewrite /= in Hb.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt.
    case: tp E Hb Hwi => [tp|] /= E Hb Hwi; odestr E.
    { match goal with H : of_pack _ _ = Some _ |- _ => case/of_pack_sound: H => Et [Hlt' Hsz] end.
      rewrite Et in Hwi *. move: Hb => /andP [/andP [/N.leb_spec0 Ha _] _].
      case: i Et Hlt' Hwi Hsz => Et Hlt' Hwi Hsz;
        (apply: S.store_pack => //; apply: Qle_N_rev => //; align_lia Ha tp). }
    { move/N.leb_spec0: Hb => Ha.
      case: t Ha Hwi => /= Ha Hwi; (apply: S.store_val => //; apply: Qle_N_rev => //;
        cbn [S.coerce S.proj_uN_0_coercion S.the S.res_size S.valtype_numtype of_numtype];
        rewrite /tr_u32 in Ha; lia). }
  - (* store_vec *)
    move=> C m mem Hm Hb C' ins HC Hes. single HC Hes.
    match goal with H : of_memarg _ = Some _ |- _ => case/of_memarg_sound: H => Em _ end. subst m.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt.
    move/N.leb_spec0: Hb => /= Ha.
    apply: S.vstore => //.
    apply: Qle_N_rev => //. cbn [S.coerce S.proj_uN_0_coercion S.the S.res_size].
    rewrite /tr_u32 /v128_size in Ha. lia.
  - (* store_vec_lane *)
    move=> C w m x mem Hm Hb C' ins HC Hes. single HC Hes.
    match goal with H : of_memarg _ = Some _ |- _ => case/of_memarg_sound: H => Em _ end. subst m.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt.
    move: Hb; rewrite /load_store_vec_lane_bounds /= => /andP [/N.leb_spec0 Ha /N.ltb_spec0 Hx].
    match goal with H : sz_ok _ = true |- _ => rename H into Hsz end.
    have Hw0 : (0 < w)%num by case/sz_ok_cases: Hsz => [->|[->|[->|->]]].
    apply: S.vstore_lane => //.
    + apply: Qle_N_rev => //. exact: div8_le.
    + apply: Qlt_N_rev => //. exact: div128_lt.
  - (* memory_size *)
    move=> C mem Hm C' ins HC Hes. single HC Hes.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt. by apply: S.memory_size.
  - (* memory_grow *)
    move=> C mem Hm C' ins HC Hes. single HC Hes.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt. by apply: S.memory_grow.
  - (* memory_fill *)
    move=> C mem Hm C' ins HC Hes. single HC Hes.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt. by apply: S.memory_fill.
  - (* memory_copy *)
    move=> C mem Hm C' ins HC Hes. single HC Hes.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt. by apply: S.memory_copy.
  - (* memory_init *)
    move=> C x mem dat Hm Hx C' ins HC Hes. single HC Hes. fields HC.
    case: (mem_lookup HC Hm) => mt [Hlt [Hl Hw]]; subst mt.
    case: (lookup_map_of (fun _ => S.OK) Hx) => Hlt' Hl'.
    apply: S.memory_init => //; rewrite ?HD //. by rewrite Hl'.
  - (* data_drop *)
    move=> C x dat Hx C' ins HC Hes. single HC Hes. fields HC.
    case: (lookup_map_of (fun _ => S.OK) Hx) => Hlt Hl.
    apply: S.data_drop => //; rewrite ?HD //. by rewrite Hl.
  - (* empty *)
    move=> C C' ins HC Hes. case: Hes => <-. apply: S.empty. exact: of_context_wf HC.
  - (* composition *)
    move=> C es e t1s t2s t3s _ IH1 _ IH2 C' ins HC Hes.
    case/olist_cat: Hes => r1 [r2 [-> [E1 E2]]].
    eapply S.res_seq; [exact: IH1 HC E1 | exact: IH2 HC E2 | exact: of_context_wf HC | |].
    + by case/(of_instrs_sound vec_instr_sound): E1.
    + by case/(of_instrs_sound vec_instr_sound): E2.
  - (* subtyping *)
    move=> C es t1s t2s t1s' t2s' _ IH Hsub C' ins HC Hes.
    have Hok := IH C' ins HC Hes. have Hctx := of_context_wf HC.
    case: (of_instrs_sound vec_instr_sound Hes) => _ Hw.
    case: Hsub => ts [ts' [ts1 [ts2 [-> [-> [Hts [H1 H2]]]]]]].
    rewrite /of_functype /of_resulttype !map_cat.
    eapply S.sub; [ | exact: Resulttype_sub_refl | | exact: Hctx | exact: Hw].
    + eapply S.Instrs_ok__frame; [ | exact: Hctx | exact: Hw].
      eapply S.sub; [exact: Hok | exact: (Resulttype_sub_of H1) | exact: (Resulttype_sub_of H2)
                    | exact: Hctx | exact: Hw].
    + apply: Resulttype_sub_cat. exact: (Resulttype_sub_of Hts).
Qed.

End Typing.

(** * Agreement of the two type systems *)

Section Agreement.

Context `{hfc : host_function_class}.

Variable vec_instr : basic_instruction -> option S.instr.
Hypothesis vec_instr_sound :
  forall b i, vec_instr b = Some i -> tr_instr i = b /\ S.wf_instr i.
Hypothesis vec_instr_complete :
  forall i, is_vec_op i -> S.wf_instr i -> vec_instr (tr_instr i) = Some i.
Hypothesis vec_code_shuffle : forall sh ls, vec_code (S.VSHUFFLE sh ls) = 13%num.

(* On well-formed SpecTec instruction sequences and contexts, SpecTec's typing
   and WasmCert's typing of the translation coincide. *)
Theorem Instrs_ok_iff C ins ft :
  S.wf_context C -> List.Forall S.wf_instr ins ->
  S.Instrs_ok C ins ft <-> be_typing (tr_context C) (tr_instrs ins) (tr_functype ft).
Proof.
  move=> HC Hw. split; first exact: T.Instrs_ok_tr.
  move=> Hb. have := be_typing_back vec_instr_sound vec_code_shuffle Hb.
  move/(_ C ins (of_context_complete HC) (of_instrs_complete vec_instr_complete Hw)).
  by rewrite of_tr_functype.
Qed.

(* WasmCert-typed code with a SpecTec counterpart is SpecTec-typed, in the
   context and at the type it translates to. *)
Corollary be_typing_of C es tf C' ins :
  be_typing C es tf -> of_context C = Some C' -> of_instrs vec_instr es = Some ins ->
  S.Instrs_ok C' ins (of_functype tf).
Proof. move=> Hb. exact: (be_typing_back vec_instr_sound vec_code_shuffle Hb). Qed.

End Agreement.

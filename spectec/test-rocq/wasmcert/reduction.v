(* Reduction: a forward simulation of SpecTec by WasmCert in the style of
   CompCert's "eventually" diagram ([forward_simulation_eventually]): every
   SpecTec step of a well-typed configuration is matched by WasmCert reduction
   steps of the translated configuration, possibly after further SpecTec steps
   that restore the relation, except for the steps collected in [Step_exc]
   ([Step_sim_eventually], at the end of the file). *)

From Stdlib Require Import NArith ZArith Lia List Relations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
(* Imported (before WasmCert, which shadows it) for its eqType instances. *)
From WasmSpectec Require Import wasm.
From Wasm Require Import datatypes operations opsem properties.
From WasmCertBridge Require Import translation.
From WasmCertBridge Require typing.

Module T := WasmCertBridge.typing.

Module S := WasmSpectec.wasm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope N_scope with num.

Section Reduction.

Context `{hfc : host_function_class} `{ho : @host hfc memory_tr}.

(** * Numerics

   Numeric results are compared, not assumed equal: a numeric step whose
   result differs from WasmCert's (NaN nondeterminism, or a genuine
   disagreement) is reported in [Exc_pure].  Showing those cases never arise
   is the remaining numerics hole. *)

Definition wc_testop (v : value_num) : value_num :=
  match v with
  | VAL_int32 x => VAL_int32 (wasm_bool (app_testop_i i32m TO_eqz x))
  | VAL_int64 x => VAL_int32 (wasm_bool (app_testop_i i64m TO_eqz x))
  | _ => v
  end.




(** * Translation of configurations *)

Definition tr_cfg (hs : host_state) (c : S.config) :
    host_state * store_record * frame * seq administrative_instruction :=
  match c with
  | S.mk_config (S.mk_state s f) es => (hs, tr_store s, tr_frame f, tr_admins es)
  end.

Definition sim (c c' : S.config) : Prop :=
  forall hs, reduce_trans (tr_cfg hs c) (tr_cfg hs c').

(** * Commutation lemmas *)

Lemma tr_admin_instr i : tr_admin (S.admininstr_instr i) = AI_basic (tr_instr i).
Proof. by case: i. Qed.

Lemma tr_admin_val v : tr_admin (S.admininstr_val v) = v_to_e (tr_val v).
Proof. by case: v. Qed.

Lemma tr_admin_ref r : tr_admin (S.admininstr_ref r) = v_to_e (VAL_ref (tr_ref r)).
Proof. by case: r. Qed.

Lemma tr_admins_cat es1 es2 : tr_admins (es1 ++ es2) = tr_admins es1 ++ tr_admins es2.
Proof. exact: map_cat. Qed.

Lemma tr_admins_vals vs :
  tr_admins (map S.admininstr_val vs) = v_to_e_list (map tr_val vs).
Proof. by elim: vs => //= v vs ->; rewrite tr_admin_val. Qed.

Lemma tr_admins_instrs ins :
  tr_admins (map S.admininstr_instr ins) = to_e_list (tr_instrs ins).
Proof. by elim: ins => //= i ins ->; rewrite tr_admin_instr. Qed.

Lemma size_tr_vals vs : size (map tr_val vs) = size vs.
Proof. exact: size_map. Qed.

(** * Lifting through contexts *)

Lemma reduce_trans_lfill k (lh : lholed k) hs s f es hs' s' f' es' :
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f, lfill lh es) (hs', s', f', lfill lh es').
Proof.
  move=> H.
  remember (hs, s, f, es) as x eqn:Hx. remember (hs', s', f', es') as y eqn:Hy.
  elim: H hs s f es hs' s' f' es' Hx Hy => {x y}.
  - move=> x y Hr ???????? Hx Hy; subst. apply: rt_step.
    by eapply r_label; [exact: Hr | reflexivity | reflexivity].
  - move=> x ???????? Hx Hy; subst. case: Hy => -> -> -> ->. exact: rt_refl.
  - move=> x [[[hs1 s1] f1] es1] z _ IH1 _ IH2 ???????? Hx Hz.
    apply: rt_trans; [exact: IH1 | exact: IH2].
Qed.

Lemma reduce_trans_frame n f0 hs s f es hs' s' f' es' :
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f0, [ :: AI_frame n f es]) (hs', s', f0, [ :: AI_frame n f' es']).
Proof.
  move=> H.
  remember (hs, s, f, es) as x eqn:Hx. remember (hs', s', f', es') as y eqn:Hy.
  elim: H hs s f es hs' s' f' es' Hx Hy => {x y}.
  - move=> x y Hr ???????? Hx Hy; subst. apply: rt_step. by apply: r_frame.
  - move=> x ???????? Hx Hy; subst. case: Hy => -> -> -> ->. exact: rt_refl.
  - move=> x [[[hs1 s1] f1] es1] z _ IH1 _ IH2 ???????? Hx Hz.
    apply: rt_trans; [exact: IH1 | exact: IH2].
Qed.

Lemma reduce_trans_step hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' -> reduce_trans (hs, s, f, es) (hs', s', f', es').
Proof. move=> H. exact: rt_step. Qed.

Lemma simple_sim s f es es' :
  reduce_simple (tr_admins es) (tr_admins es') ->
  sim (S.mk_config (S.mk_state s f) es) (S.mk_config (S.mk_state s f) es').
Proof. move=> H hs /=. apply: reduce_trans_step. exact: r_simple. Qed.

(** * 32-bit integers *)

Lemma max_unsigned32 : Wasm_int.Int32.max_unsigned = 4294967295%Z.
Proof. by vm_compute. Qed.

Lemma wf_uN32 n : S.wf_uN 32%num (S.mk_uN n) -> (n < 4294967296)%num.
Proof.
  move=> H; inversion H; subst.
  match goal with Hb : is_true (_ && _) |- _ => move: Hb => /andP [_ /N.leb_spec0 Hb] end.
  simpl in *. lia.
Qed.

Lemma wf_num_I32 c :
  S.wf_num_ S.I32 c -> exists n, c = S.mk_num__0 S.Inn_I32 (S.mk_uN n) /\ (n < 4294967296)%num.
Proof.
  move=> H; inversion H; subst; clear H.
  all: match goal with Hb : is_true (_ == _) |- _ => move/eqP: Hb => Hb end.
  - destruct v_Inn; try discriminate.
    match goal with Hw : S.wf_uN _ ?x |- _ => case: x Hw => n Hn end.
    exists n; split => //. exact: wf_uN32.
  - by destruct v_Fnn.
Qed.

Lemma tr_i32_unsigned n :
  (n < 4294967296)%num -> Wasm_int.Int32.unsigned (tr_i32 (S.mk_uN n)) = Z.of_N n.
Proof.
  move=> Hn. rewrite /tr_i32 /tr_u32 Wasm_int.Int32.unsigned_repr //.
  rewrite max_unsigned32 /=. lia.
Qed.

Lemma tr_i32_zero n :
  (n < 4294967296)%num -> tr_i32 (S.mk_uN n) = Wasm_int.Int32.zero <-> n = 0%num.
Proof.
  move=> Hn; split => [H | ->]; last by [].
  have := f_equal Wasm_int.Int32.unsigned H. rewrite tr_i32_unsigned //. move=> /= H'. lia.
Qed.

Lemma N_of_uint_tr n :
  (n < 4294967296)%num -> Wasm_int.N_of_uint i32m (tr_i32 (S.mk_uN n)) = n.
Proof.
  move=> Hn. transitivity (Z.to_N (Wasm_int.Int32.unsigned (tr_i32 (S.mk_uN n)))); first by [].
  by rewrite tr_i32_unsigned // N2Z.id.
Qed.

(** * Pure steps *)

Notation cfg s f es := (S.mk_config (S.mk_state s f) es).

Lemma wf_admin_const nt c : S.wf_admininstr (S.admininstr_CONST nt c) -> S.wf_num_ nt c.
Proof. by move=> H; inversion H. Qed.

Ltac wf_split :=
  repeat match goal with
  | H : List.Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  | H : List.Forall _ (_ ++ _) |- _ => apply List.Forall_app in H as [? ?]
  end.

Ltac get_i32 c :=
  match goal with
  | H : S.wf_admininstr (S.admininstr_CONST S.I32 c) |- _ =>
      let n := fresh "n" in let Hn := fresh "Hn" in
      have [n [? Hn]] := wf_num_I32 (wf_admin_const H); subst c
  end.

Lemma int_zero32 : Wasm_int.int_zero i32m = Wasm_int.Int32.zero.
Proof. by []. Qed.

Lemma vals_const vs : const_list (v_to_e_list vs).
Proof. exact: v_to_e_const. Qed.

Lemma length_size {A : Type} (l : seq A) : length l = size l.
Proof. by elim: l => //= ? ? ->. Qed.

Lemma length_vals vs : length (v_to_e_list (map tr_val vs)) = size vs.
Proof. by rewrite length_size /v_to_e_list !size_map. Qed.

Lemma sim_unreachable (s : S.store) (f : S.frame) :
  sim (cfg s f [ :: S.admininstr_UNREACHABLE]) (cfg s f [ :: S.admininstr_TRAP]).
Proof. apply: simple_sim. exact: rs_unreachable. Qed.

Lemma sim_nop (s : S.store) (f : S.frame) : sim (cfg s f [ :: S.admininstr_NOP]) (cfg s f [ ::]).
Proof. apply: simple_sim. exact: rs_nop. Qed.

Lemma sim_drop (s : S.store) (f : S.frame) (v : S.val) :
  sim (cfg s f [ :: S.admininstr_val v; S.admininstr_DROP]) (cfg s f [ ::]).
Proof. apply: simple_sim. rewrite /tr_admins /= tr_admin_val. exact: rs_drop. Qed.

Definition i32c (n : N) : S.admininstr := S.admininstr_CONST S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN n)).

Lemma sim_select (s : S.store) (f : S.frame) (v1 v2 : S.val) (n : N) t (b : bool) :
  (n < 4294967296)%num -> N.eqb n 0 = b ->
  sim (cfg s f [ :: S.admininstr_val v1; S.admininstr_val v2; i32c n; S.admininstr_SELECT t])
      (cfg s f [ :: S.admininstr_val (if b then v2 else v1)]).
Proof.
  move=> Hn Hb. apply: simple_sim. rewrite /tr_admins /= !tr_admin_val.
  case: b Hb => /N.eqb_spec Hb.
  - apply: rs_select_false. rewrite int_zero32. exact/(tr_i32_zero Hn).
  - apply: rs_select_true. rewrite int_zero32 => H0. exact/Hb/(tr_i32_zero Hn).
Qed.

Lemma sim_if (s : S.store) (f : S.frame) (n : N) bt is1 is2 (b : bool) :
  (n < 4294967296)%num -> N.eqb n 0 = b ->
  sim (cfg s f [ :: i32c n; S.admininstr_IFELSE bt is1 is2])
      (cfg s f [ :: S.admininstr_BLOCK bt (if b then is2 else is1)]).
Proof.
  move=> Hn Hb. apply: simple_sim. rewrite /tr_admins /=.
  case: b Hb => /N.eqb_spec Hb.
  - apply: rs_if_false. rewrite int_zero32. exact/(tr_i32_zero Hn).
  - apply: rs_if_true. rewrite int_zero32 => H0. exact/Hb/(tr_i32_zero Hn).
Qed.

Lemma sim_br_if (s : S.store) (f : S.frame) (n : N) l (b : bool) :
  (n < 4294967296)%num -> N.eqb n 0 = b ->
  sim (cfg s f [ :: i32c n; S.admininstr_BR_IF l])
      (cfg s f (if b then [ ::] else [ :: S.admininstr_BR l])).
Proof.
  move=> Hn Hb. apply: simple_sim. rewrite /tr_admins /=.
  case: b Hb => /N.eqb_spec Hb.
  - apply: rs_br_if_false. rewrite int_zero32. exact/(tr_i32_zero Hn).
  - apply: rs_br_if_true. rewrite int_zero32 => H0. exact/Hb/(tr_i32_zero Hn).
Qed.

Lemma sim_label_vals (s : S.store) (f : S.frame) n ins (vs : seq S.val) :
  sim (cfg s f [ :: S.LABEL_ n ins (map S.admininstr_val vs)]) (cfg s f (map S.admininstr_val vs)).
Proof.
  apply: simple_sim. rewrite /tr_admins /=. rewrite -/(tr_admins _) tr_admins_vals.
  apply: rs_label_const. exact: vals_const.
Qed.

Lemma sim_br_zero (s : S.store) (f : S.frame) n ins (vs' vs : seq S.val) es :
  n = N.of_nat (size vs) ->
  sim (cfg s f [ :: S.LABEL_ n ins (((map S.admininstr_val vs' ++ map S.admininstr_val vs)
                                     ++ [ :: S.admininstr_BR (S.mk_uN 0)]) ++ es)])
      (cfg s f (map S.admininstr_val vs ++ map S.admininstr_instr ins)).
Proof.
  move=> Hn. apply: simple_sim. rewrite /tr_admins /=. rewrite -!/(tr_admins _).
  rewrite !tr_admins_cat !tr_admins_vals tr_admins_instrs.
  eapply rs_br with (i := 0) (lh := LH_base (map tr_val vs') (tr_admins es)).
  - exact: vals_const.
  - by rewrite length_vals Hn Nat2N.id.
  - by rewrite /= -!catA.
Qed.

Lemma sim_frame_vals (s : S.store) (f : S.frame) n f' (vs : seq S.val) :
  n = N.of_nat (size vs) ->
  sim (cfg s f [ :: S.FRAME_ n f' (map S.admininstr_val vs)]) (cfg s f (map S.admininstr_val vs)).
Proof.
  move=> Hn. apply: simple_sim. rewrite /tr_admins /=. rewrite -/(tr_admins _) tr_admins_vals.
  apply: rs_local_const; first exact: vals_const.
  by rewrite length_vals Hn Nat2N.id.
Qed.

Lemma sim_return_frame (s : S.store) (f : S.frame) n f' (vs' vs : seq S.val) es :
  n = N.of_nat (size vs) ->
  sim (cfg s f [ :: S.FRAME_ n f' (((map S.admininstr_val vs' ++ map S.admininstr_val vs)
                                    ++ [ :: S.admininstr_RETURN]) ++ es)])
      (cfg s f (map S.admininstr_val vs)).
Proof.
  move=> Hn. apply: simple_sim. rewrite /tr_admins /=. rewrite -!/(tr_admins _).
  rewrite !tr_admins_cat !tr_admins_vals.
  eapply rs_return with (i := 0) (lh := LH_base (map tr_val vs') (tr_admins es)).
  - exact: vals_const.
  - by rewrite length_vals Hn Nat2N.id.
  - by rewrite /= -!catA.
Qed.

Lemma sim_trap_vals (s : S.store) (f : S.frame) (vs : seq S.val) (es : seq S.admininstr) :
  (vs != [ ::]) || (es != [ ::]) ->
  sim (cfg s f (map S.admininstr_val vs ++ [ :: S.admininstr_TRAP] ++ es)) (cfg s f [ :: S.admininstr_TRAP]).
Proof.
  move=> Hne. apply: simple_sim. rewrite !tr_admins_cat tr_admins_vals.
  eapply rs_trap with (lh := LH_base (map tr_val vs) (tr_admins es)); last by [].
  case: vs es Hne => [ |v vs] [ |e es] //= _ H; inversion H;
  match goal with H2 : _ ++ _ = [ ::] |- _ => by case: (v_to_e_list _) H2 end.
Qed.

Lemma sim_trap_label (s : S.store) (f : S.frame) n ins :
  sim (cfg s f [ :: S.LABEL_ n ins [ :: S.admininstr_TRAP]]) (cfg s f [ :: S.admininstr_TRAP]).
Proof. apply: simple_sim. exact: rs_label_trap. Qed.

Lemma sim_trap_frame (s : S.store) (f : S.frame) n f' :
  sim (cfg s f [ :: S.FRAME_ n f' [ :: S.admininstr_TRAP]]) (cfg s f [ :: S.admininstr_TRAP]).
Proof. apply: simple_sim. exact: rs_local_trap. Qed.

Lemma sim_local_tee (s : S.store) (f : S.frame) (v : S.val) x :
  sim (cfg s f [ :: S.admininstr_val v; S.admininstr_LOCAL_TEE x])
      (cfg s f [ :: S.admininstr_val v; S.admininstr_val v; S.admininstr_LOCAL_SET x]).
Proof. apply: simple_sim. rewrite /tr_admins /= !tr_admin_val. exact: rs_local_tee. Qed.

Lemma sim_ref_is_null (s : S.store) (f : S.frame) (r : S.ref) (b : bool) :
  ((exists rt, r = S.ref_REF_NULL rt) <-> b) ->
  sim (cfg s f [ :: S.admininstr_ref r; S.admininstr_REF_IS_NULL])
      (cfg s f [ :: i32c (if b then 1 else 0)%num]).
Proof.
  move=> Hb. apply: simple_sim. rewrite /tr_admins /= tr_admin_ref.
  case: b Hb => Hb.
  - have [rt ->] := proj2 Hb isT. exact: rs_ref_is_null_true.
  - apply: rs_ref_is_null_false => t. case: r Hb => //= rt Hb [_].
    by have := proj1 Hb (ex_intro _ rt erefl).
Qed.

Lemma sim_br_table (s : S.store) (f : S.frame) (n : N) ls l' :
  (n < 4294967296)%num ->
  sim (cfg s f [ :: i32c n; S.admininstr_BR_TABLE ls l'])
      (cfg s f [ :: S.admininstr_BR (if N.ltb n (N.of_nat (size ls)) then S.lookup_total ls n else l')]).
Proof.
  move=> Hn. apply: simple_sim. rewrite /tr_admins /=.
  case: ifP => Hlt.
  - apply: rs_br_table; rewrite N_of_uint_tr //.
    + move/N.ltb_spec0: Hlt. by rewrite length_size size_map.
    + by rewrite T.lookup_N_map.
  - apply: rs_br_table_length. rewrite N_of_uint_tr // length_size size_map.
    by apply N.ltb_ge in Hlt.
Qed.

Lemma sim_unop (s : S.store) (f : S.frame) nt op c1 c :
  S.wf_num_ nt c1 -> S.wf_unop_ nt op -> app_unop (tr_unop op) (tr_num c1) = tr_num c ->
  sim (cfg s f [ :: S.admininstr_CONST nt c1; S.admininstr_UNOP nt op])
      (cfg s f [ :: S.admininstr_CONST nt c]).
Proof.
  move=> Hc Hop Hf. apply: simple_sim. rewrite /tr_admins /=.
  rewrite -Hf. apply: rs_unop.
  by rewrite /unop_typecheck (T.wf_num_typeof Hc) eqxx (T.wf_unop_agree Hop).
Qed.

Lemma sim_binop (s : S.store) (f : S.frame) nt op c1 c2 c :
  S.wf_num_ nt c1 -> S.wf_num_ nt c2 -> S.wf_binop_ nt op ->
  app_binop (tr_binop op) (tr_num c1) (tr_num c2) = Some (tr_num c) ->
  sim (cfg s f [ :: S.admininstr_CONST nt c1; S.admininstr_CONST nt c2; S.admininstr_BINOP nt op])
      (cfg s f [ :: S.admininstr_CONST nt c]).
Proof.
  move=> H1 H2 Hop Hf. apply: simple_sim. rewrite /tr_admins /=.
  apply: rs_binop_success; last exact: Hf.
  by rewrite /binop_typecheck (T.wf_num_typeof H1) (T.wf_num_typeof H2) eqxx (T.wf_binop_agree Hop).
Qed.

Lemma sim_binop_trap (s : S.store) (f : S.frame) nt op c1 c2 :
  S.wf_num_ nt c1 -> S.wf_num_ nt c2 -> S.wf_binop_ nt op ->
  app_binop (tr_binop op) (tr_num c1) (tr_num c2) = None ->
  sim (cfg s f [ :: S.admininstr_CONST nt c1; S.admininstr_CONST nt c2; S.admininstr_BINOP nt op])
      (cfg s f [ :: S.admininstr_TRAP]).
Proof.
  move=> H1 H2 Hop Hf. apply: simple_sim. rewrite /tr_admins /=.
  apply: rs_binop_failure; last exact: Hf.
  by rewrite /binop_typecheck (T.wf_num_typeof H1) (T.wf_num_typeof H2) eqxx (T.wf_binop_agree Hop).
Qed.

Lemma sim_testop (s : S.store) (f : S.frame) nt op c1 c :
  S.wf_num_ nt c1 -> S.wf_testop_ nt op -> tr_num c = wc_testop (tr_num c1) ->
  sim (cfg s f [ :: S.admininstr_CONST nt c1; S.admininstr_TESTOP nt op])
      (cfg s f [ :: S.admininstr_CONST S.I32 c]).
Proof.
  move=> Hc Hop Hf. apply: simple_sim. rewrite /tr_admins /=.
  rewrite Hf.
  case: Hop Hc => nt' t x /eqP ->. rewrite /tr_testop. move=> Hc. inversion Hc; subst.
  all: match goal with Hb : is_true (_ == _) |- _ => move/eqP: Hb => Hb end.
  - destruct t, v_Inn; try discriminate; [exact: rs_testop_i32 | exact: rs_testop_i64].
  - by destruct t, v_Fnn.
Qed.

Lemma sim_relop (s : S.store) (f : S.frame) nt op c1 c2 c :
  S.wf_num_ nt c1 -> S.wf_num_ nt c2 -> S.wf_relop_ nt op ->
  tr_num c = VAL_int32 (wasm_bool (app_relop (tr_relop op) (tr_num c1) (tr_num c2))) ->
  sim (cfg s f [ :: S.admininstr_CONST nt c1; S.admininstr_CONST nt c2; S.admininstr_RELOP nt op])
      (cfg s f [ :: S.admininstr_CONST S.I32 c]).
Proof.
  move=> H1 H2 Hop Hf. apply: simple_sim. rewrite /tr_admins /=.
  rewrite Hf. apply: rs_relop.
  by rewrite /relop_typecheck (T.wf_num_typeof H1) (T.wf_num_typeof H2) eqxx (T.wf_relop_agree Hop).
Qed.

Lemma sim_cvtop (s : S.store) (f : S.frame) nt1 nt2 op c1 c :
  S.wf_num_ nt1 c1 -> S.wf_cvtop__ nt1 nt2 op ->
  eval_cvt (tr_numtype nt2) (tr_cvtop op).1 (tr_cvtop op).2 (tr_num c1) = Some (tr_num c) ->
  sim (cfg s f [ :: S.admininstr_CONST nt1 c1; S.admininstr_CVTOP nt2 nt1 op])
      (cfg s f [ :: S.admininstr_CONST nt2 c]).
Proof.
  move=> Hc Hop Hf. apply: simple_sim. rewrite /tr_admins /=.
  apply: rs_convert_success.
  - exact: T.wf_num_typeof Hc.
  - exact: T.wf_cvtop_valid Hop.
  - exact: Hf.
Qed.

Lemma sim_cvtop_trap (s : S.store) (f : S.frame) nt1 nt2 op c1 :
  S.wf_num_ nt1 c1 -> S.wf_cvtop__ nt1 nt2 op ->
  eval_cvt (tr_numtype nt2) (tr_cvtop op).1 (tr_cvtop op).2 (tr_num c1) = None ->
  sim (cfg s f [ :: S.admininstr_CONST nt1 c1; S.admininstr_CVTOP nt2 nt1 op])
      (cfg s f [ :: S.admininstr_TRAP]).
Proof.
  move=> Hc Hop Hf. apply: simple_sim. rewrite /tr_admins /=.
  apply: rs_convert_failure.
  - exact: T.wf_num_typeof Hc.
  - exact: T.wf_cvtop_valid Hop.
  - exact: Hf.
Qed.

(** * Pure steps that are not simulated *)

Definition is_vec_admin (a : S.admininstr) : bool :=
  match a with
  | S.admininstr_VVUNOP _ _ | S.admininstr_VVBINOP _ _ | S.admininstr_VVTERNOP _ _
  | S.admininstr_VVTESTOP _ _ | S.admininstr_VUNOP _ _ | S.admininstr_VBINOP _ _
  | S.admininstr_VTESTOP _ _ | S.admininstr_VRELOP _ _ | S.admininstr_VSHIFTOP _ _
  | S.admininstr_VBITMASK _ | S.admininstr_VSWIZZLE _ | S.admininstr_VSHUFFLE _ _
  | S.admininstr_VSPLAT _ | S.admininstr_VEXTRACT_LANE _ _ _ | S.admininstr_VREPLACE_LANE _ _
  | S.admininstr_VEXTUNOP _ _ _ | S.admininstr_VEXTBINOP _ _ _ | S.admininstr_VNARROW _ _ _
  | S.admininstr_VCVTOP _ _ _ | S.admininstr_VLOAD _ _ _ | S.admininstr_VLOAD_LANE _ _ _ _
  | S.admininstr_VSTORE _ _ | S.admininstr_VSTORE_LANE _ _ _ _ => true
  | _ => false
  end.

Definition vec_redex (es : seq S.admininstr) : bool :=
  match rev es with
  | a :: _ => is_vec_admin a
  | [ ::] => false
  end.

(* SpecTec leaves one label per step on a break or a return, while WasmCert
   jumps to the target in one [rs_br] / [rs_return]: the intermediate SpecTec
   states have no WasmCert counterpart, and the relation is only restored
   eventually, at the target (see [Step_sim_eventually]). *)
Inductive Label_exit : seq S.admininstr -> seq S.admininstr -> Prop :=
  | lexit_br n ins vs x es :
      Label_exit [ :: S.LABEL_ n ins ((map S.admininstr_val vs
                    ++ [ :: S.admininstr_BR (S.mk_uN (x + 1))]) ++ es)]
                 (map S.admininstr_val vs ++ [ :: S.admininstr_BR (S.mk_uN x)])
  | lexit_return n ins vs es :
      Label_exit [ :: S.LABEL_ n ins ((map S.admininstr_val vs ++ [ :: S.admininstr_RETURN]) ++ es)]
                 (map S.admininstr_val vs ++ [ :: S.admininstr_RETURN]).

(* Pure steps that are not simulated:
   - numeric steps whose SpecTec result differs from WasmCert's (this covers
     NaN nondeterminism as well as genuine disagreements);
   - vector instructions: their WasmCert semantics is opaque. *)
Inductive Exc_pure : seq S.admininstr -> seq S.admininstr -> Prop :=
  | exc_unop nt op c1 c cs :
      S.fun_unop_ nt op c1 = Some cs -> c \in cs ->
      app_unop (tr_unop op) (tr_num c1) <> tr_num c ->
      Exc_pure [ :: S.admininstr_CONST nt c1; S.admininstr_UNOP nt op] [ :: S.admininstr_CONST nt c]
  | exc_unop_trap nt op c1 :
      S.fun_unop_ nt op c1 = Some [ ::] ->
      Exc_pure [ :: S.admininstr_CONST nt c1; S.admininstr_UNOP nt op] [ :: S.admininstr_TRAP]
  | exc_binop nt op c1 c2 c cs :
      S.fun_binop_ nt op c1 c2 (Some cs) -> c \in cs ->
      app_binop (tr_binop op) (tr_num c1) (tr_num c2) <> Some (tr_num c) ->
      Exc_pure [ :: S.admininstr_CONST nt c1; S.admininstr_CONST nt c2; S.admininstr_BINOP nt op]
               [ :: S.admininstr_CONST nt c]
  | exc_binop_trap nt op c1 c2 :
      S.fun_binop_ nt op c1 c2 (Some [ ::]) ->
      app_binop (tr_binop op) (tr_num c1) (tr_num c2) <> None ->
      Exc_pure [ :: S.admininstr_CONST nt c1; S.admininstr_CONST nt c2; S.admininstr_BINOP nt op]
               [ :: S.admininstr_TRAP]
  | exc_testop nt op c1 c :
      S.fun_testop_ nt op c1 = Some c -> tr_num c <> wc_testop (tr_num c1) ->
      Exc_pure [ :: S.admininstr_CONST nt c1; S.admininstr_TESTOP nt op] [ :: S.admininstr_CONST S.I32 c]
  | exc_relop nt op c1 c2 c :
      S.fun_relop_ nt op c1 c2 (Some c) ->
      tr_num c <> VAL_int32 (wasm_bool (app_relop (tr_relop op) (tr_num c1) (tr_num c2))) ->
      Exc_pure [ :: S.admininstr_CONST nt c1; S.admininstr_CONST nt c2; S.admininstr_RELOP nt op]
               [ :: S.admininstr_CONST S.I32 c]
  | exc_cvtop nt1 nt2 op c1 c cs :
      S.fun_cvtop__ nt1 nt2 op c1 (Some cs) -> c \in cs ->
      eval_cvt (tr_numtype nt2) (tr_cvtop op).1 (tr_cvtop op).2 (tr_num c1) <> Some (tr_num c) ->
      Exc_pure [ :: S.admininstr_CONST nt1 c1; S.admininstr_CVTOP nt2 nt1 op]
               [ :: S.admininstr_CONST nt2 c]
  | exc_cvtop_trap nt1 nt2 op c1 :
      S.fun_cvtop__ nt1 nt2 op c1 (Some [ ::]) ->
      eval_cvt (tr_numtype nt2) (tr_cvtop op).1 (tr_cvtop op).2 (tr_num c1) <> None ->
      Exc_pure [ :: S.admininstr_CONST nt1 c1; S.admininstr_CVTOP nt2 nt1 op] [ :: S.admininstr_TRAP]
  | exc_vec es es' : S.Step_pure es es' -> vec_redex es -> Exc_pure es es'.

Lemma singleton_in {A : eqType} (c c' : A) : c \in [ :: c'] -> c = c'.
Proof. by rewrite mem_seq1 => /eqP. Qed.

Ltac wf_get :=
  wf_split;
  repeat match goal with
  | H : S.wf_admininstr (S.admininstr_CONST _ _) |- _ => apply wf_admin_const in H
  | H : S.wf_admininstr (S.admininstr_UNOP _ _) |- _ => inversion H; subst; clear H
  | H : S.wf_admininstr (S.admininstr_BINOP _ _) |- _ => inversion H; subst; clear H
  | H : S.wf_admininstr (S.admininstr_TESTOP _ _) |- _ => inversion H; subst; clear H
  | H : S.wf_admininstr (S.admininstr_RELOP _ _) |- _ => inversion H; subst; clear H
  | H : S.wf_admininstr (S.admininstr_CVTOP _ _ _) |- _ => inversion H; subst; clear H
  end.

Ltac i32_of c :=
  match goal with
  | H : S.wf_num_ S.I32 c |- _ =>
      let n := fresh "n" in let Hn := fresh "Hn" in
      have [n [? Hn]] := wf_num_I32 H; subst c
  end.

Lemma Step_pure_sim e1 e2 :
  S.Step_pure e1 e2 -> List.Forall S.wf_admininstr e1 ->
  (forall s f, sim (cfg s f e1) (cfg s f e2)) \/ Exc_pure e1 e2 \/ Label_exit e1 e2.
Proof.
  move=> H. move: (H). case: H.
  - (* unreachable *) move=> _ _. left => s f. exact: sim_unreachable.
  - (* nop *) move=> _ _. left => s f. exact: sim_nop.
  - (* drop *) move=> v _ _. left => s f. exact: sim_drop.
  - (* select_true *)
    move=> v1 v2 c t _ H2 _ Hwf. left => s f. wf_get. i32_of c.
    move: H2 => /= /eqP H2. have := sim_select s f v1 v2 t Hn (b := false). apply.
    exact/N.eqb_neq.
  - (* select_false *)
    move=> v1 v2 c t _ H2 _ Hwf. left => s f. wf_get. i32_of c.
    move: H2 => /= /eqP H2. have := sim_select s f v1 v2 t Hn (b := true). apply.
    exact/N.eqb_eq.
  - (* if_true *)
    move=> c bt is1 is2 _ H2 _ Hwf. left => s f. wf_get. i32_of c.
    move: H2 => /= /eqP H2. have := sim_if s f bt is1 is2 Hn (b := false). apply.
    exact/N.eqb_neq.
  - (* if_false *)
    move=> c bt is1 is2 _ H2 _ Hwf. left => s f. wf_get. i32_of c.
    move: H2 => /= /eqP H2. have := sim_if s f bt is1 is2 Hn (b := true). apply.
    exact/N.eqb_eq.
  - (* label_vals *) move=> n ins vs _ _. left => s f. exact: sim_label_vals.
  - (* br_zero *) move=> n ins vs' vs es /eqP Hn _ _. left => s f. exact: sim_br_zero.
  - (* br_succ *) move=> n ins vs [x] es _ _. right; right. exact: lexit_br.
  - (* br_if_true *)
    move=> c l _ H2 _ Hwf. left => s f. wf_get. i32_of c.
    move: H2 => /= /eqP H2. have := sim_br_if s f l Hn (b := false). apply.
    exact/N.eqb_neq.
  - (* br_if_false *)
    move=> c l _ H2 _ Hwf. left => s f. wf_get. i32_of c.
    move: H2 => /= /eqP H2. have := sim_br_if s f l Hn (b := true). apply.
    exact/N.eqb_eq.
  - (* br_table_lt *)
    move=> c ls l' H1 _ _ Hwf. left => s f. wf_get. i32_of c.
    have := sim_br_table s f ls l' Hn. by move: H1 => /= ->.
  - (* br_table_ge *)
    move=> c ls l' _ H2 _ Hwf. left => s f. wf_get. i32_of c.
    have := sim_br_table s f ls l' Hn.
    have -> // : N.ltb n (N.of_nat (size ls)) = false.
    apply/N.ltb_ge. move: H2 => /=. rewrite /S.N_geb. by move/N.leb_spec0.
  - (* frame_vals *) move=> n f' vs /eqP Hn _ _. left => s f. exact: sim_frame_vals.
  - (* return_frame *) move=> n f' vs' vs es /eqP Hn _ _. left => s f. exact: sim_return_frame.
  - (* return_label *) move=> n ins vs es _ _. right; right. exact: lexit_return.
  - (* trap_vals *) move=> vs es Hne _ _. left => s f. exact: sim_trap_vals.
  - (* trap_label *) move=> n ins _ _. left => s f. exact: sim_trap_label.
  - (* trap_frame *) move=> n f' _ _. left => s f. exact: sim_trap_frame.
  - (* unop_val *)
    move=> nt c1 op c _ H2 H3 _ Hwf. wf_get.
    case E: (S.fun_unop_ nt op c1) H2 H3 => [cs| ] //= _ Hin.
    case: (app_unop (tr_unop op) (tr_num c1) =P tr_num c) => Heq.
    + left => s f. exact: sim_unop Heq.
    + right; left. exact: exc_unop E Hin Heq.
  - (* unop_trap *)
    move=> nt c1 op H1 H2 _ Hwf. right; left. apply: exc_unop_trap.
    case: (S.fun_unop_ nt op c1) H1 H2 => [cs| ] //= _ /eqP -> //.
  - (* binop_val *)
    move=> nt c1 c2 op c v Hb _ H3 Hin _ Hwf. wf_get.
    case: v Hb H3 Hin => [cs| ] //= Hb _ Hin.
    case: (app_binop (tr_binop op) (tr_num c1) (tr_num c2) =P Some (tr_num c)) => Heq.
    + left => s f. exact: sim_binop Heq.
    + right; left. exact: exc_binop Hb Hin Heq.
  - (* binop_trap *)
    move=> nt c1 c2 op v Hb H2 H3 _ Hwf. wf_get.
    case: v Hb H2 H3 => [cs| ] //= Hb _ /eqP Hcs. subst cs.
    case: (app_binop (tr_binop op) (tr_num c1) (tr_num c2) =P None) => Heq.
    + left => s f. exact: sim_binop_trap Heq.
    + right; left. exact: exc_binop_trap Hb Heq.
  - (* testop *)
    move=> nt c1 op c H1 H2 _ _ Hwf. wf_get. move/eqP: H2 => H2.
    have Hf : S.fun_testop_ nt op c1 = Some c by case: (S.fun_testop_ nt op c1) H1 H2 => //= ? _ ->.
    case: (tr_num c =P wc_testop (tr_num c1)) => Heq.
    + left => s f. exact: sim_testop Heq.
    + right; left. exact: exc_testop Hf Heq.
  - (* relop *)
    move=> nt c1 c2 op c v Hr H2 H3 _ _ Hwf. wf_get. move/eqP: H3 => H3.
    case: v Hr H2 H3 => [c'| ] //= Hr _ Hc. subst c'.
    case: (tr_num c =P VAL_int32 (wasm_bool (app_relop (tr_relop op) (tr_num c1) (tr_num c2)))) => Heq.
    + left => s f. exact: sim_relop Heq.
    + right; left. exact: exc_relop Hr Heq.
  - (* cvtop_val *)
    move=> nt1 c1 nt2 op c v Hc _ H3 Hin _ Hwf. wf_get.
    case: v Hc H3 Hin => [cs| ] //= Hc _ Hin.
    case: (eval_cvt (tr_numtype nt2) (tr_cvtop op).1 (tr_cvtop op).2 (tr_num c1) =P Some (tr_num c)) => Heq.
    + left => s f. exact: sim_cvtop Heq.
    + right; left. exact: exc_cvtop Hc Hin Heq.
  - (* cvtop_trap *)
    move=> nt1 c1 nt2 op v Hc H2 H3 _ Hwf. wf_get.
    case: v Hc H2 H3 => [cs| ] //= Hc _ /eqP Hcs. subst cs.
    case: (eval_cvt (tr_numtype nt2) (tr_cvtop op).1 (tr_cvtop op).2 (tr_num c1) =P None) => Heq.
    + left => s f. exact: sim_cvtop_trap Heq.
    + right; left. exact: exc_cvtop_trap Hc Heq.
  - (* ref_is_null_true *)
    move=> r rt /eqP -> _ _. left => s f. apply: (@sim_ref_is_null s f _ true).
    split => // _. by exists rt.
  - (* ref_is_null_false *)
    move=> r Hn _ _. left => s f. apply: (@sim_ref_is_null s f r false).
    split => // [[rt Hr]]. exfalso. apply: Hn. subst r.
    by apply: (@S.ref_is_null_true_0 (S.ref_REF_NULL rt) rt).
  all: try (intros; right; left; apply: exc_vec; [eassumption | done]).
  (* local_tee *)
  move=> v x _ _. left => s f. exact: sim_local_tee.
Qed.

(** * Store and frame accessors *)

Lemma lookup_N_total {A : Type} `{S.Inhabited A} (l : seq A) (n : N) :
  (n < N.of_nat (size l))%num -> lookup_N l n = Some (S.lookup_total l n).
Proof.
  move=> Hn. have := @T.lookup_N_map A A _ id l n. rewrite map_id. apply. exact/N.ltb_spec0.
Qed.

Lemma lookup_N_tr {A B : Type} `{S.Inhabited A} (g : A -> B) (l : seq A) (n : N) :
  (n < N.of_nat (size l))%num -> lookup_N (map g l) n = Some (g (S.lookup_total l n)).
Proof. move=> Hn. apply: T.lookup_N_map. exact/N.ltb_spec0. Qed.

Lemma lookup_N_None {A : Type} (l : seq A) (n : N) :
  (N.of_nat (size l) <= n)%num -> lookup_N l n = None.
Proof.
  move=> Hn. rewrite /lookup_N. apply/List.nth_error_None.
  rewrite -/(size l) length_size. lia.
Qed.

Lemma update_func_tr {A B : Type} `{S.Inhabited A} (g : A -> B) (u : A -> A) (l : seq A) (n : N) (d : B) :
  (n < N.of_nat (size l))%num ->
  map g (S.list_update_func l n u) = set_nth d (map g l) (N.to_nat n) (g (u (S.lookup_total l n))).
Proof.
  rewrite /S.lookup_total. move: n. elim: l => [ |x l IH] n Hn; rewrite /= in Hn *; first by lia.
  case: n Hn => [ |p] Hn //=.
  rewrite IH; last by lia.
  have E : PosDef.Pos.to_nat p = Datatypes.S (N.to_nat (PosDef.Pos.pred_N p))
    by rewrite -Nnat.N2Nat.inj_succ N.succ_pos_pred.
  by rewrite E.
Qed.

Lemma update_func_oob {A : Type} (u : A -> A) (l : seq A) (n : N) :
  (N.of_nat (size l) <= n)%num -> S.list_update_func l n u = l.
Proof.
  move: n. elim: l => [ |x l IH] n Hn //=. rewrite /= in Hn.
  case: n Hn => [ |p] Hn /=; first by lia.
  rewrite IH //. lia.
Qed.

Section Accessors.

Variables (s : S.store) (f : S.frame).
Let z := S.mk_state s f.
Let mi := S.frame_MODULE f.

Definition local_ok (x : S.uN) : Prop := (S.proj_uN_0 x < N.of_nat (size (S.LOCALS f)))%num.

Definition addr_ok (idxs : seq N) (len : nat) (x : N) : Prop :=
  (x < N.of_nat (size idxs))%num /\ (S.lookup_total idxs x < N.of_nat len)%num.

Definition glob_ok (x : S.uN) : Prop :=
  addr_ok (S.GLOBALS mi) (size (S.store_GLOBALS s)) (S.proj_uN_0 x).
Definition tab_ok (x : S.uN) : Prop :=
  addr_ok (S.TABLES mi) (size (S.store_TABLES s)) (S.proj_uN_0 x).
Definition elem_ok (x : S.uN) : Prop :=
  addr_ok (S.ELEMS mi) (size (S.store_ELEMS s)) (S.proj_uN_0 x).
Definition data_ok (x : S.uN) : Prop :=
  addr_ok (S.DATAS mi) (size (S.store_DATAS s)) (S.proj_uN_0 x).
Definition mem_ok : Prop := addr_ok (S.MEMS mi) (size (S.store_MEMS s)) 0.
Definition type_ok (x : S.uN) : Prop := (S.proj_uN_0 x < N.of_nat (size (S.TYPES mi)))%num.

Lemma tr_frame_inst : f_inst (tr_frame f) = tr_moduleinst mi.
Proof. by []. Qed.

Lemma sglob_val_tr x :
  glob_ok x -> sglob_val (tr_store s) (tr_moduleinst mi) (tr_u32 x) = Some (tr_val (S.VALUE (S.fun_global z x))).
Proof.
  move=> [H1 H2]. rewrite /sglob_val /sglob /sglob_ind /=.
  by rewrite lookup_N_total // lookup_N_tr.
Qed.

Lemma stab_tr x :
  tab_ok x -> stab (tr_store s) (tr_moduleinst mi) (tr_u32 x) = Some (tr_tableinst (S.fun_table z x)).
Proof. move=> [H1 H2]. by rewrite /stab /= lookup_N_total // lookup_N_tr. Qed.

Lemma stab_elem_tr x i :
  tab_ok x ->
  stab_elem (tr_store s) (tr_moduleinst mi) (tr_u32 x) i = lookup_N (map tr_ref (S.REFS (S.fun_table z x))) i.
Proof. move=> [H1 H2]. by rewrite /stab_elem /= lookup_N_total // lookup_N_tr. Qed.

Lemma selem_tr x :
  elem_ok x -> selem (tr_store s) (tr_moduleinst mi) (tr_u32 x) = Some (tr_eleminst (S.fun_elem z x)).
Proof. move=> [H1 H2]. by rewrite /selem /= lookup_N_total // lookup_N_tr. Qed.

Lemma sdata_tr x :
  data_ok x -> sdata (tr_store s) (tr_moduleinst mi) (tr_u32 x) = Some (tr_datainst (S.fun_data z x)).
Proof. move=> [H1 H2]. by rewrite /sdata /= lookup_N_total // lookup_N_tr. Qed.

Lemma smem_tr :
  mem_ok -> smem (tr_store s) (tr_moduleinst mi) = Some (tr_meminst (S.fun_mem z (S.mk_uN 0))).
Proof. move=> [H1 H2]. by rewrite /smem /= lookup_N_total // lookup_N_tr. Qed.

End Accessors.

(** * Steps reading the store *)

Lemma read_sim (s : S.store) (f : S.frame) es es' :
  (forall hs, reduce hs (tr_store s) (tr_frame f) (tr_admins es) hs (tr_store s) (tr_frame f) (tr_admins es')) ->
  sim (cfg s f es) (cfg s f es').
Proof. move=> H hs. exact: reduce_trans_step. Qed.

Lemma Z_of_uint_tr n :
  (n < 4294967296)%num -> Wasm_int.Z_of_uint i32m (tr_i32 (S.mk_uN n)) = Z.of_N n.
Proof. exact: tr_i32_unsigned. Qed.

Lemma tr_i32_of_Z a z : Z.of_N a = z -> tr_i32 (S.mk_uN a) = Wasm_int.int_of_Z i32m z.
Proof. by move=> <-. Qed.

Definition ref_val (v : S.val) : option S.ref :=
  match v with
  | S.val_REF_NULL rt => Some (S.ref_REF_NULL rt)
  | S.val_REF_FUNC_ADDR a => Some (S.REF_FUNC_ADDR a)
  | S.val_REF_HOST_ADDR a => Some (S.REF_HOST_ADDR a)
  | _ => None
  end.

Lemma ref_val_tr v r : ref_val v = Some r -> tr_val v = VAL_ref (tr_ref r).
Proof. by case: v => // [rt|a|a] [<-]. Qed.

Lemma sim_call (s : S.store) (f : S.frame) x :
  (S.proj_uN_0 x < N.of_nat (size (S.FUNCS (S.frame_MODULE f))))%num ->
  sim (cfg s f [ :: S.admininstr_CALL x])
      (cfg s f [ :: S.CALL_ADDR (S.lookup_total (S.FUNCS (S.frame_MODULE f)) (S.proj_uN_0 x))]).
Proof. move=> Hx. apply: read_sim => hs. apply: r_call. by rewrite /= lookup_N_total. Qed.

Lemma sim_ref_func (s : S.store) (f : S.frame) x :
  (S.proj_uN_0 x < N.of_nat (size (S.FUNCS (S.frame_MODULE f))))%num ->
  sim (cfg s f [ :: S.admininstr_REF_FUNC x])
      (cfg s f [ :: S.admininstr_REF_FUNC_ADDR (S.lookup_total (S.FUNCS (S.frame_MODULE f)) (S.proj_uN_0 x))]).
Proof. move=> Hx. apply: read_sim => hs. apply: r_ref_func. by rewrite /= lookup_N_total. Qed.

Lemma sim_local_get (s : S.store) (f : S.frame) x :
  local_ok f x ->
  sim (cfg s f [ :: S.admininstr_LOCAL_GET x])
      (cfg s f [ :: S.admininstr_val (S.fun_local (S.mk_state s f) x)]).
Proof.
  move=> Hx. apply: read_sim => hs. rewrite /tr_admins /= tr_admin_val.
  apply: r_local_get. by rewrite /= lookup_N_tr.
Qed.

Lemma sim_global_get (s : S.store) (f : S.frame) x :
  glob_ok s f x ->
  sim (cfg s f [ :: S.admininstr_GLOBAL_GET x])
      (cfg s f [ :: S.admininstr_val (S.VALUE (S.fun_global (S.mk_state s f) x))]).
Proof.
  move=> Hx. apply: read_sim => hs. rewrite /tr_admins /= tr_admin_val.
  apply: r_global_get. exact: sglob_val_tr.
Qed.

Definition bt_ok (f : S.frame) (bt : S.blocktype) : Prop :=
  match bt with
  | S._IDX x => type_ok f x
  | S._RESULT _ => True
  end.

Lemma expand_tr (s : S.store) (f : S.frame) bt :
  bt_ok f bt ->
  expand (tr_moduleinst (S.frame_MODULE f)) (tr_blocktype bt)
  = Some (tr_functype (S.fun_blocktype (S.mk_state s f) bt)).
Proof.
  case: bt => [[t| ] | x] //= Hx.
  by rewrite lookup_N_tr.
Qed.

Lemma sim_block (s : S.store) (f : S.frame) (vs : seq S.val) bt ins t1 t2 :
  bt_ok f bt ->
  S.fun_blocktype (S.mk_state s f) bt = S.mk_functype (S.mk_list _ t1) (S.mk_list _ t2) ->
  size vs = size t1 ->
  sim (cfg s f (map S.admininstr_val vs ++ [ :: S.admininstr_BLOCK bt ins]))
      (cfg s f [ :: S.LABEL_ (N.of_nat (size t2)) [ ::] (map S.admininstr_val vs ++ map S.admininstr_instr ins)]).
Proof.
  move=> Hbt Hft Hsz. apply: read_sim => hs.
  rewrite tr_admins_cat tr_admins_vals /tr_admins /= -/(tr_admins _).
  rewrite tr_admins_cat tr_admins_vals tr_admins_instrs Nat2N.id.
  eapply r_block with (t1s := map tr_valtype t1) (t2s := map tr_valtype t2).
  - by rewrite (expand_tr s Hbt) Hft.
  - exact: vals_const.
  - by rewrite length_vals.
  - by rewrite length_size size_map.
  - by rewrite length_size size_map.
Qed.

Lemma sim_loop (s : S.store) (f : S.frame) (vs : seq S.val) bt ins t1 t2 :
  bt_ok f bt ->
  S.fun_blocktype (S.mk_state s f) bt = S.mk_functype (S.mk_list _ t1) (S.mk_list _ t2) ->
  size vs = size t1 ->
  sim (cfg s f (map S.admininstr_val vs ++ [ :: S.admininstr_LOOP bt ins]))
      (cfg s f [ :: S.LABEL_ (N.of_nat (size t1)) [ :: S.LOOP bt ins] (map S.admininstr_val vs ++ map S.admininstr_instr ins)]).
Proof.
  move=> Hbt Hft Hsz. apply: read_sim => hs.
  rewrite tr_admins_cat tr_admins_vals /tr_admins /= -/(tr_admins _).
  rewrite tr_admins_cat tr_admins_vals tr_admins_instrs Nat2N.id.
  eapply r_loop with (t1s := map tr_valtype t1) (t2s := map tr_valtype t2).
  - by rewrite (expand_tr s Hbt) Hft.
  - exact: vals_const.
  - by rewrite length_vals.
  - by rewrite length_size size_map.
  - by rewrite length_size size_map.
Qed.

(** ** Tables *)

Notation tabz s f x := (S.fun_table (S.mk_state s f) x).
Notation refsz s f x := (S.REFS (S.fun_table (S.mk_state s f) x)).

Lemma tab_size_tr ti : tab_size (tr_tableinst ti) = size (S.REFS ti).
Proof. by rewrite /tab_size /= length_size size_map. Qed.

Lemma sim_table_get (s : S.store) (f : S.frame) x n :
  tab_ok s f x -> (n < 4294967296)%num ->
  sim (cfg s f [ :: i32c n; S.admininstr_TABLE_GET x])
      (cfg s f (if N.ltb n (N.of_nat (size (refsz s f x)))
                then [ :: S.admininstr_ref (S.lookup_total (refsz s f x) n)]
                else [ :: S.admininstr_TRAP])).
Proof.
  move=> Ht Hn. apply: read_sim => hs. case: ifP => H; rewrite /tr_admins /=.
  - rewrite tr_admin_ref. apply: r_table_get_success.
    rewrite N_of_uint_tr // stab_elem_tr // lookup_N_tr //. exact/N.ltb_spec0.
  - apply: r_table_get_failure.
    rewrite N_of_uint_tr // stab_elem_tr // lookup_N_None // size_map. by apply N.ltb_ge in H.
Qed.

Lemma sim_table_size (s : S.store) (f : S.frame) x :
  tab_ok s f x ->
  sim (cfg s f [ :: S.admininstr_TABLE_SIZE x])
      (cfg s f [ :: i32c (N.of_nat (size (refsz s f x)))]).
Proof.
  move=> Ht. apply: read_sim => hs. rewrite /tr_admins /=.
  rewrite (@tr_i32_of_Z _ (Z.of_nat (tab_size (tr_tableinst (tabz s f x))))); last by rewrite tab_size_tr nat_N_Z.
  eapply r_table_size; [exact: stab_tr Ht | reflexivity].
Qed.

Lemma Z_of_uint_i32c n :
  (n < 4294967296)%num -> Wasm_int.Z_of_uint i32m (tr_i32 (S.mk_uN n)) = Z.of_N n.
Proof. exact: Z_of_uint_tr. Qed.

Lemma tr_i32_succ i : tr_i32 (S.mk_uN (i + 1)) = Wasm_int.int_of_Z i32m (Z.of_N i + 1).
Proof. apply: tr_i32_of_Z. lia. Qed.

Lemma tr_i32_pred n : (0 < n)%num ->
  tr_i32 (S.mk_uN (Z.to_N (Z.of_N n - Z.of_N 1))) = Wasm_int.int_of_Z i32m (Z.of_N n - 1).
Proof. move=> Hn. apply: tr_i32_of_Z. lia. Qed.

Lemma tr_i32_add_pred a n : (0 < n)%num ->
  tr_i32 (S.mk_uN (Z.to_N (Z.of_N (a + n) - Z.of_N 1))) = Wasm_int.int_of_Z i32m (Z.of_N a + Z.of_N n - 1).
Proof. move=> Hn. apply: tr_i32_of_Z. lia. Qed.

Ltac trsimpl := rewrite /tr_admins; cbn [seq.map tr_admin i32c tr_instr].

Lemma sim_table_fill (s : S.store) (f : S.frame) x i n v r :
  tab_ok s f x -> (i < 4294967296)%num -> (n < 4294967296)%num -> ref_val v = Some r ->
  sim (cfg s f [ :: i32c i; S.admininstr_val v; i32c n; S.admininstr_TABLE_FILL x])
      (cfg s f (if N.ltb (N.of_nat (size (refsz s f x))) (i + n) then [ :: S.admininstr_TRAP]
                else if N.eqb n 0 then [ ::]
                else [ :: i32c i; S.admininstr_val v; S.admininstr_TABLE_SET x; i32c (i + 1);
                         S.admininstr_val v; i32c (Z.to_N (Z.of_N n - Z.of_N 1)); S.admininstr_TABLE_FILL x])).
Proof.
  move=> Ht Hi Hn Hr. apply: read_sim => hs.
  have Hsz := tab_size_tr (tabz s f x).
  case: ifP => Hb; [ | case: ifP => Hz]; trsimpl; rewrite !tr_admin_val (ref_val_tr Hr).
  - eapply r_table_fill_bound; first exact: stab_tr Ht.
    rewrite !Z_of_uint_i32c // Hsz. move/N.ltb_spec0: Hb. lia.
  - apply N.ltb_ge in Hb. move/N.eqb_spec: Hz => Hz.
    eapply r_table_fill_return; first exact: stab_tr Ht.
    + rewrite !Z_of_uint_i32c // Hsz. lia.
    + by rewrite Hz Z_of_uint_i32c.
  - apply N.ltb_ge in Hb. move/N.eqb_spec: Hz => Hz.
    eapply r_table_fill_step; first exact: stab_tr Ht.
    + rewrite !Z_of_uint_i32c // Hsz. lia.
    + rewrite Z_of_uint_i32c //. lia.
    + rewrite Z_of_uint_i32c // tr_i32_pred //. lia.
    + by rewrite Z_of_uint_i32c // tr_i32_succ.
Qed.

Lemma sim_table_copy (s : S.store) (f : S.frame) x y j i n :
  tab_ok s f x -> tab_ok s f y ->
  (j < 4294967296)%num -> (i < 4294967296)%num -> (n < 4294967296)%num ->
  sim (cfg s f [ :: i32c j; i32c i; i32c n; S.admininstr_TABLE_COPY x y])
      (cfg s f (if N.ltb (N.of_nat (size (refsz s f y))) (i + n)
                   || N.ltb (N.of_nat (size (refsz s f x))) (j + n) then [ :: S.admininstr_TRAP]
                else if N.eqb n 0 then [ ::]
                else if N.leb j i then
                  [ :: i32c j; i32c i; S.admininstr_TABLE_GET y; S.admininstr_TABLE_SET x;
                      i32c (j + 1); i32c (i + 1); i32c (Z.to_N (Z.of_N n - Z.of_N 1));
                      S.admininstr_TABLE_COPY x y]
                else
                  [ :: i32c (Z.to_N (Z.of_N (j + n) - Z.of_N 1)); i32c (Z.to_N (Z.of_N (i + n) - Z.of_N 1));
                      S.admininstr_TABLE_GET y; S.admininstr_TABLE_SET x;
                      i32c j; i32c i; i32c (Z.to_N (Z.of_N n - Z.of_N 1));
                      S.admininstr_TABLE_COPY x y])).
Proof.
  move=> Hx Hy Hj Hi Hn. apply: read_sim => hs.
  have Hsx := tab_size_tr (tabz s f x). have Hsy := tab_size_tr (tabz s f y).
  case: ifP => Hb; [ | case: ifP => Hz; [ | case: ifP => Hle]]; trsimpl.
  - eapply r_table_copy_bound; [exact: stab_tr Hx | exact: stab_tr Hy | ].
    rewrite !Z_of_uint_i32c // Hsx Hsy.
    case/orP: Hb => /N.ltb_spec0 Hb; [left | right]; lia.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz.
    eapply r_table_copy_return; [exact: stab_tr Hx | exact: stab_tr Hy | | | ];
      rewrite !Z_of_uint_i32c // ?Hsx ?Hsy; lia.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz. move/N.leb_spec0: Hle => Hle.
    eapply r_table_copy_forward; [exact: stab_tr Hx | exact: stab_tr Hy | | | | | | | ];
      rewrite ?Z_of_uint_i32c // ?Hsx ?Hsy; try lia.
    + by rewrite tr_i32_pred //; lia.
    + by rewrite tr_i32_succ.
    + by rewrite tr_i32_succ.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz. move/N.leb_spec0: Hle => Hle.
    eapply r_table_copy_backward; [exact: stab_tr Hx | exact: stab_tr Hy | | | | | | | ];
      rewrite ?Z_of_uint_i32c // ?Hsx ?Hsy; try lia.
    + by rewrite tr_i32_pred //; lia.
    + by rewrite tr_i32_add_pred //; lia.
    + by rewrite tr_i32_add_pred //; lia.
Qed.

Lemma elem_size_tr ei : elem_size (tr_eleminst ei) = size (S.eleminst_REFS ei).
Proof. by rewrite /elem_size /= length_size size_map. Qed.

Lemma sim_table_init (s : S.store) (f : S.frame) x y j i n :
  tab_ok s f x -> elem_ok s f y ->
  (j < 4294967296)%num -> (i < 4294967296)%num -> (n < 4294967296)%num ->
  sim (cfg s f [ :: i32c j; i32c i; i32c n; S.admininstr_TABLE_INIT x y])
      (cfg s f (if N.ltb (N.of_nat (size (S.eleminst_REFS (S.fun_elem (S.mk_state s f) y)))) (i + n)
                   || N.ltb (N.of_nat (size (refsz s f x))) (j + n) then [ :: S.admininstr_TRAP]
                else if N.eqb n 0 then [ ::]
                else
                  [ :: i32c j; S.admininstr_ref (S.lookup_total (S.eleminst_REFS (S.fun_elem (S.mk_state s f) y)) i);
                      S.admininstr_TABLE_SET x; i32c (j + 1); i32c (i + 1);
                      i32c (Z.to_N (Z.of_N n - Z.of_N 1)); S.admininstr_TABLE_INIT x y])).
Proof.
  move=> Hx Hy Hj Hi Hn. apply: read_sim => hs.
  have Hsx := tab_size_tr (tabz s f x). have Hse := elem_size_tr (S.fun_elem (S.mk_state s f) y).
  case: ifP => Hb; [ | case: ifP => Hz]; trsimpl.
  - eapply r_table_init_bound; [exact: stab_tr Hx | exact: selem_tr Hy | ].
    rewrite !Z_of_uint_i32c // Hsx Hse.
    case/orP: Hb => /N.ltb_spec0 Hb; [left | right]; lia.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz.
    eapply r_table_init_return; [exact: stab_tr Hx | exact: selem_tr Hy | | | ];
      rewrite !Z_of_uint_i32c // ?Hsx ?Hse; lia.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz.
    rewrite tr_admin_ref.
    eapply r_table_init_step; [exact: stab_tr Hx | exact: selem_tr Hy | | | | | | | ];
      rewrite ?Z_of_uint_i32c // ?Hsx ?Hse; try lia.
    + rewrite N_of_uint_tr //; cbn [eleminst_elem tr_eleminst]; rewrite lookup_N_tr //. lia.
    + by rewrite tr_i32_pred //; lia.
    + by rewrite tr_i32_succ.
    + by rewrite tr_i32_succ.
Qed.

(** ** Memory instructions

   Like the table instructions, [memory.fill], [memory.copy] and [memory.init]
   unfold one byte at a time into [i32.store8] / [i32.load8_u] in both
   semantics, so only the bounds checks and the unfolding are compared here;
   the byte accesses are loads and stores. *)

Notation memz s f := (S.fun_mem (S.mk_state s f) (S.mk_uN 0)).
Notation bytesz s f := (S.BYTES (memz s f)).

Lemma mem_length_tr mi : mem_length (tr_meminst mi) = N.of_nat (size (S.BYTES mi)).
Proof. by rewrite /mem_length /= /memory_list.ml_length /= size_map. Qed.

Lemma tr_i32_iadd1 i :
  tr_i32 (S.iadd_ 32%num (S.mk_uN i) (S.mk_uN 1)) = Wasm_int.int_of_Z i32m (Z.of_N i + 1).
Proof.
  rewrite /tr_i32 /S.iadd_ /tr_u32 /=. apply: Wasm_int.Int32.eqm_samerepr.
  rewrite N2Z.inj_mod N2Z.inj_add. change (Z.of_N (N.pos (2 ^ 32))) with Wasm_int.Int32.modulus.
  apply: Wasm_int.Int32.eqm_sym. exact: compcert.lib.Zbits.eqmod_mod.
Qed.

Lemma sim_memory_size (s : S.store) (f : S.frame) n :
  mem_ok s f -> (n * 65536)%num = N.of_nat (size (bytesz s f)) ->
  sim (cfg s f [ :: S.admininstr_MEMORY_SIZE]) (cfg s f [ :: i32c n]).
Proof.
  move=> Hm Hn. apply: read_sim => hs. trsimpl. cbn [tr_num].
  rewrite (@tr_i32_of_Z _ (Z.of_N n)) //.
  eapply r_memory_size; first exact: smem_tr Hm.
  by rewrite /mem_size mem_length_tr -Hn N.div_mul.
Qed.

Lemma sim_memory_fill (s : S.store) (f : S.frame) i n c :
  mem_ok s f -> (i < 4294967296)%num -> (n < 4294967296)%num ->
  sim (cfg s f [ :: i32c i; i32c c; i32c n; S.admininstr_MEMORY_FILL])
      (cfg s f (if N.ltb (N.of_nat (size (bytesz s f))) (i + n) then [ :: S.admininstr_TRAP]
                else if N.eqb n 0 then [ ::]
                else [ :: i32c i; i32c c; S.admininstr_STORE S.I32 (Some (S.mk_sz 8)) S.memarg0;
                         S.admininstr_CONST S.I32 (S.mk_num__0 S.Inn_I32 (S.iadd_ 32%num (S.mk_uN i) (S.mk_uN 1)));
                         i32c c; i32c (Z.to_N (Z.of_N n - Z.of_N 1)); S.admininstr_MEMORY_FILL])).
Proof.
  move=> Hm Hi Hn. apply: read_sim => hs.
  have Hsz := mem_length_tr (memz s f).
  case: ifP => Hb; [ | case: ifP => Hz]; trsimpl; cbn [tr_num].
  - eapply r_memory_fill_bound; first exact: smem_tr Hm.
    rewrite !Z_of_uint_i32c // Hsz. move/N.ltb_spec0: Hb. lia.
  - apply N.ltb_ge in Hb. move/N.eqb_spec: Hz => Hz.
    eapply r_memory_fill_return; first exact: smem_tr Hm.
    + rewrite !Z_of_uint_i32c // Hsz. lia.
    + by rewrite Hz Z_of_uint_i32c.
  - apply N.ltb_ge in Hb. move/N.eqb_spec: Hz => Hz.
    eapply r_memory_fill_step; first exact: smem_tr Hm.
    + rewrite !Z_of_uint_i32c // Hsz. lia.
    + rewrite Z_of_uint_i32c //. lia.
    + rewrite Z_of_uint_i32c // tr_i32_pred //. lia.
    + by rewrite Z_of_uint_i32c // tr_i32_iadd1.
Qed.

Notation load8u := (S.admininstr_LOAD S.I32
  (Some (S.mk_loadop__0 S.Inn_I32 (S.mk_loadop_Inn (S.mk_sz 8) S.U))) S.memarg0).
Notation store8 := (S.admininstr_STORE S.I32 (Some (S.mk_sz 8)) S.memarg0).
Notation i32add1 i := (S.admininstr_CONST S.I32 (S.mk_num__0 S.Inn_I32 (S.iadd_ 32%num (S.mk_uN i) (S.mk_uN 1)))).

Lemma sim_memory_copy (s : S.store) (f : S.frame) j i n :
  mem_ok s f -> (j < 4294967296)%num -> (i < 4294967296)%num -> (n < 4294967296)%num ->
  sim (cfg s f [ :: i32c j; i32c i; i32c n; S.admininstr_MEMORY_COPY])
      (cfg s f (if N.ltb (N.of_nat (size (bytesz s f))) (i + n)
                   || N.ltb (N.of_nat (size (bytesz s f))) (j + n) then [ :: S.admininstr_TRAP]
                else if N.eqb n 0 then [ ::]
                else if N.leb j i then
                  [ :: i32c j; i32c i; load8u; store8; i32add1 j; i32add1 i;
                      i32c (Z.to_N (Z.of_N n - Z.of_N 1)); S.admininstr_MEMORY_COPY]
                else
                  [ :: i32c (Z.to_N (Z.of_N (j + n) - Z.of_N 1)); i32c (Z.to_N (Z.of_N (i + n) - Z.of_N 1));
                      load8u; store8; i32c j; i32c i; i32c (Z.to_N (Z.of_N n - Z.of_N 1));
                      S.admininstr_MEMORY_COPY])).
Proof.
  move=> Hm Hj Hi Hn. apply: read_sim => hs.
  have Hsz := mem_length_tr (memz s f).
  case: ifP => Hb; [ | case: ifP => Hz; [ | case: ifP => Hle]]; trsimpl; cbn [tr_num].
  - eapply r_memory_copy_bound; first exact: smem_tr Hm.
    rewrite !Z_of_uint_i32c // Hsz.
    case/orP: Hb => /N.ltb_spec0 Hb; [left | right]; lia.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz.
    eapply r_memory_copy_return; first exact: smem_tr Hm.
    1-3: rewrite ?Z_of_uint_i32c // ?Hsz; lia.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz. move/N.leb_spec0: Hle => Hle.
    eapply r_memory_copy_forward; first exact: smem_tr Hm.
    1-7: rewrite ?Z_of_uint_i32c // ?Hsz.
    1-4: lia.
    + by rewrite tr_i32_pred //; lia.
    + by rewrite tr_i32_iadd1.
    + by rewrite tr_i32_iadd1.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz. move/N.leb_spec0: Hle => Hle.
    eapply r_memory_copy_backward; first exact: smem_tr Hm.
    1-7: rewrite ?Z_of_uint_i32c // ?Hsz.
    1-4: lia.
    + by rewrite tr_i32_pred //; lia.
    + rewrite tr_i32_add_pred; [f_equal; lia | lia].
    + rewrite tr_i32_add_pred; [f_equal; lia | lia].
Qed.

Lemma Forall_lookup_total {A : Type} `{S.Inhabited A} (P : A -> Prop) (l : seq A) i :
  List.Forall P l -> (i < N.of_nat (size l))%num -> P (S.lookup_total l i).
Proof.
  rewrite /S.lookup_total => HF Hi. have : Peano.lt (N.to_nat i) (size l) by lia.
  move: (N.to_nat i) => k. elim: l k HF {Hi} => [ |a l IH] [ |k] HF Hk /=; inversion HF => //.
  - by simpl in Hk; lia.
  - by simpl in Hk; lia.
  - apply: IH => //. simpl in Hk. lia.
Qed.

Lemma deserialise_byte_tr b :
  S.wf_byte b -> wasm_deserialise [ :: tr_byte b] T_i32 = VAL_int32 (tr_i32 (S.mk_uN (S.proj_byte_0 b))).
Proof.
  case=> bn /andP [_ /N.leb_le Hb].
  rewrite /wasm_deserialise /common.Memdata.decode_int /common.Memdata.rev_if_be /=.
  have -> : (if Archi.big_endian then [ :: Integers.Byte.repr (Z.of_N bn)]
             else [ :: Integers.Byte.repr (Z.of_N bn)]) = [ :: Integers.Byte.repr (Z.of_N bn)]
    by case: Archi.big_endian.
  rewrite /= Integers.Byte.unsigned_repr; last by rewrite /Integers.Byte.max_unsigned /=; lia.
  by rewrite Z.add_0_r.
Qed.

Lemma sim_memory_init (s : S.store) (f : S.frame) x j i n :
  mem_ok s f -> data_ok s f x ->
  List.Forall S.wf_byte (S.datainst_BYTES (S.fun_data (S.mk_state s f) x)) ->
  (j < 4294967296)%num -> (i < 4294967296)%num -> (n < 4294967296)%num ->
  sim (cfg s f [ :: i32c j; i32c i; i32c n; S.admininstr_MEMORY_INIT x])
      (cfg s f (if N.ltb (N.of_nat (size (S.datainst_BYTES (S.fun_data (S.mk_state s f) x)))) (i + n)
                   || N.ltb (N.of_nat (size (bytesz s f))) (j + n) then [ :: S.admininstr_TRAP]
                else if N.eqb n 0 then [ ::]
                else
                  [ :: i32c j; i32c (S.proj_byte_0 (S.lookup_total (S.datainst_BYTES (S.fun_data (S.mk_state s f) x)) i));
                      store8; i32add1 j; i32add1 i;
                      i32c (Z.to_N (Z.of_N n - Z.of_N 1)); S.admininstr_MEMORY_INIT x])).
Proof.
  move=> Hm Hd Hbs Hj Hi Hn. apply: read_sim => hs.
  have Hsz := mem_length_tr (memz s f).
  have Hds : data_size (tr_datainst (S.fun_data (S.mk_state s f) x))
             = size (S.datainst_BYTES (S.fun_data (S.mk_state s f) x))
    by rewrite /data_size /= length_size size_map.
  case: ifP => Hb; [ | case: ifP => Hz]; trsimpl; cbn [tr_num].
  - eapply r_memory_init_bound; [exact: smem_tr Hm | exact: sdata_tr Hd | ].
    rewrite !Z_of_uint_i32c // Hsz Hds.
    case/orP: Hb => /N.ltb_spec0 Hb; [left | right]; lia.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz.
    eapply r_memory_init_return; [exact: smem_tr Hm | exact: sdata_tr Hd | | | ].
    1-3: rewrite ?Z_of_uint_i32c // ?Hsz ?Hds; lia.
  - move/norP: Hb => [/negbTE Hb1 /negbTE Hb2]. apply N.ltb_ge in Hb1. apply N.ltb_ge in Hb2.
    move/N.eqb_spec: Hz => Hz.
    have Hlt : (i < N.of_nat (size (S.datainst_BYTES (S.fun_data (S.mk_state s f) x))))%num by lia.
    rewrite -(deserialise_byte_tr (Forall_lookup_total Hbs Hlt)).
    eapply r_memory_init_step; [exact: smem_tr Hm | exact: sdata_tr Hd | | | | | | | ].
    1-7: rewrite ?Z_of_uint_i32c // ?Hsz ?Hds.
    1-3: lia.
    + rewrite N_of_uint_tr //. cbn [datainst_data tr_datainst]. by rewrite lookup_N_tr.
    + by rewrite tr_i32_pred //; lia.
    + by rewrite tr_i32_iadd1.
    + by rewrite tr_i32_iadd1.
Qed.


(** ** Calls *)

Lemma tr_valtype_inj : injective tr_valtype.
Proof. by do 2 case. Qed.

Lemma tr_functype_inj ft1 ft2 : tr_functype ft1 = tr_functype ft2 -> ft1 = ft2.
Proof.
  case: ft1 => [[l1] [l2]]; case: ft2 => [[l3] [l4]] /= [H1 H2].
  by rewrite (inj_map tr_valtype_inj H1) (inj_map tr_valtype_inj H2).
Qed.

Lemma sim_call_indirect (s : S.store) (f : S.frame) x y n a :
  tab_ok s f x -> type_ok f y -> (n < 4294967296)%num ->
  (n < N.of_nat (size (refsz s f x)))%num ->
  S.lookup_total (refsz s f x) n = S.REF_FUNC_ADDR a ->
  (a < N.of_nat (size (S.store_FUNCS s)))%num ->
  S.fun_type (S.mk_state s f) y = S.funcinst_TYPE (S.lookup_total (S.store_FUNCS s) a) ->
  sim (cfg s f [ :: i32c n; S.admininstr_CALL_INDIRECT x y]) (cfg s f [ :: S.CALL_ADDR a]).
Proof.
  move=> Hx Hy Hn Hlt Hr Ha Ht. apply: read_sim => hs. trsimpl.
  eapply r_call_indirect_success.
  - by rewrite N_of_uint_tr // stab_elem_tr // lookup_N_tr // Hr.
  - by rewrite /= lookup_N_tr.
  - by rewrite /= lookup_N_tr // -Ht.
Qed.

(* Table entries that call_indirect can meet in a well-typed store. *)
Definition funcref_ok (s : S.store) (r : S.ref) : Prop :=
  match r with
  | S.ref_REF_NULL _ => True
  | S.REF_FUNC_ADDR a => (a < N.of_nat (size (S.store_FUNCS s)))%num
  | S.REF_HOST_ADDR _ => False
  end.

Lemma sim_call_indirect_trap (s : S.store) (f : S.frame) x y n :
  tab_ok s f x -> type_ok f y -> (n < 4294967296)%num ->
  ((n < N.of_nat (size (refsz s f x)))%num -> funcref_ok s (S.lookup_total (refsz s f x) n)) ->
  ~ (exists a, (n < N.of_nat (size (refsz s f x)))%num /\
               S.lookup_total (refsz s f x) n = S.REF_FUNC_ADDR a /\
               (a < N.of_nat (size (S.store_FUNCS s)))%num /\
               S.fun_type (S.mk_state s f) y = S.funcinst_TYPE (S.lookup_total (S.store_FUNCS s) a)) ->
  sim (cfg s f [ :: i32c n; S.admininstr_CALL_INDIRECT x y]) (cfg s f [ :: S.admininstr_TRAP]).
Proof.
  move=> Hx Hy Hn Hok Hnot. apply: read_sim => hs. trsimpl.
  case: (N.lt_ge_cases n (N.of_nat (size (refsz s f x)))) => Hlt; last first.
  { apply: r_call_indirect_failure_bound.
    by rewrite N_of_uint_tr // stab_elem_tr // lookup_N_None // size_map. }
  have := Hok Hlt.
  case Er: (S.lookup_total (refsz s f x) n) => [rt|a|a] //= Ha.
  - eapply r_call_indirect_failure_null_ref.
    by rewrite N_of_uint_tr // stab_elem_tr // lookup_N_tr // Er.
  - eapply r_call_indirect_failure_mismatch.
    + by rewrite N_of_uint_tr // stab_elem_tr // lookup_N_tr // Er.
    + by rewrite /= lookup_N_tr.
    + rewrite /= lookup_N_tr // => [[Heq]]. apply: Hnot. exists a. do 3 (split => //).
      exact: tr_functype_inj.
Qed.

Definition no_v128 (ts : seq S.valtype) : Prop := ~ List.In S.valtype_V128 ts.

Lemma default_tr t :
  t <> S.valtype_V128 -> S.default_ t <> None ->
  default_val (tr_valtype t) = Some (tr_val (S.the (S.default_ t))).
Proof. by case: t. Qed.

Lemma default_vals_tr ts :
  no_v128 ts -> List.Forall (fun t => S.default_ t <> None) ts ->
  default_vals (map tr_valtype ts) = Some (map tr_val (map (fun t => S.the (S.default_ t)) ts)).
Proof.
  rewrite /default_vals -list_extra.those_those0.
  elim: ts => [ |t ts IH] //= Hv Hd. inversion Hd; subst.
  rewrite default_tr //; last by move=> E; apply: Hv; left.
  rewrite /= IH //. by move=> Hin; apply: Hv; right.
Qed.

Lemma sim_call_addr (s : S.store) (f : S.frame) (vs : seq S.val) a t1 t2 mm x t_lst ins :
  (a < N.of_nat (size (S.store_FUNCS s)))%num ->
  S.lookup_total (S.store_FUNCS s) a =
    {| S.funcinst_TYPE := S.mk_functype (S.mk_list _ t1) (S.mk_list _ t2);
       S.funcinst_MODULE := mm;
       S.CODE := S.func_FUNC x (map S.LOCAL t_lst) ins |} ->
  List.Forall (fun t => S.default_ t <> None) t_lst ->
  no_v128 t_lst ->
  size vs = size t1 ->
  sim (cfg s f (map S.admininstr_val vs ++ [ :: S.CALL_ADDR a]))
      (cfg s f [ :: S.FRAME_ (N.of_nat (size t2))
                     {| S.LOCALS := vs ++ map (fun t => S.the (S.default_ t)) t_lst; S.frame_MODULE := mm |}
                     [ :: S.LABEL_ (N.of_nat (size t2)) [ ::] (map S.admininstr_instr ins)]]).
Proof.
  move=> Ha Hf Hd Hv Hsz. apply: read_sim => hs.
  rewrite tr_admins_cat tr_admins_vals /tr_admins /= -/(tr_admins _) tr_admins_instrs Nat2N.id.
  have -> : tr_frame {| S.LOCALS := vs ++ map (fun t => S.the (S.default_ t)) t_lst; S.frame_MODULE := mm |}
          = Build_frame (map tr_val vs ++ map tr_val (map (fun t => S.the (S.default_ t)) t_lst))
                        (tr_moduleinst mm) by rewrite /tr_frame /= map_cat.
  eapply r_invoke_native with (ts1 := map tr_valtype t1) (ts2 := map tr_valtype t2)
                              (ts := map tr_valtype t_lst).
  - by rewrite /= lookup_N_tr.
  - by rewrite Hf.
  - rewrite /tr_func /tr_local /=. by rewrite -map_comp.
  - reflexivity.
  - reflexivity.
  - by rewrite !length_size !size_map.
  - by rewrite !length_size !size_map Hsz.
  - by rewrite !length_size !size_map.
  - exact: default_vals_tr.
Qed.

(** * Steps writing the state *)

Lemma sim_local_set (s : S.store) (f : S.frame) (v : S.val) x :
  local_ok f x ->
  sim (cfg s f [ :: S.admininstr_val v; S.admininstr_LOCAL_SET x])
      (S.mk_config (S.with_local (S.mk_state s f) x v) [ ::]).
Proof.
  move=> Hx hs. rewrite /= /tr_admins /= tr_admin_val. apply: reduce_trans_step.
  eapply r_local_set with (vd := tr_val v).
  - reflexivity.
  - rewrite /= length_size size_map. apply/ssrnat.ltP. move: Hx; rewrite /local_ok /tr_u32. lia.
  - unfold RecordSet.set; simpl. exact: (update_func_tr tr_val (fun=> v) (tr_val v) Hx).
Qed.

Lemma sim_global_set (s : S.store) (f : S.frame) (v : S.val) x :
  glob_ok s f x ->
  sim (cfg s f [ :: S.admininstr_val v; S.admininstr_GLOBAL_SET x])
      (S.mk_config (S.with_global (S.mk_state s f) x v) [ ::]).
Proof.
  move=> [H1 H2] hs. rewrite /= /tr_admins /= tr_admin_val. apply: reduce_trans_step.
  apply: r_global_set.
  rewrite /supdate_glob /sglob_ind /= lookup_N_total //= /supdate_glob_s lookup_N_tr //=.
  unfold RecordSet.set; rewrite /tr_store /tr_u32 /=.
  by erewrite update_func_tr; last exact: H2.
Qed.

Lemma sim_table_set (s : S.store) (f : S.frame) x n (r : S.ref) :
  tab_ok s f x -> (n < 4294967296)%num ->
  sim (cfg s f [ :: i32c n; S.admininstr_ref r; S.admininstr_TABLE_SET x])
      (if N.ltb n (N.of_nat (size (refsz s f x)))
       then S.mk_config (S.with_table (S.mk_state s f) x n r) [ ::]
       else cfg s f [ :: S.admininstr_TRAP]).
Proof.
  move=> [H1 H2] Hn hs. have Ht : tab_ok s f x by [].
  case: ifP => Hlt; rewrite /= /tr_admins /= tr_admin_ref; apply: reduce_trans_step.
  - apply: r_table_set_success.
    rewrite N_of_uint_tr // /stab_update /= lookup_N_total // lookup_N_tr //= /tab_size length_size size_map.
    have -> : (n <? N.of_nat (size (S.REFS ((S.store_TABLES s) [|(S.TABLES (S.frame_MODULE f)) [|tr_u32 x|]|]))))%num = true
      by exact: Hlt.
    unfold RecordSet.set; rewrite /tr_store /tr_u32 /=.
    erewrite (update_func_tr tr_tableinst); last exact: H2.
    rewrite /tr_tableinst /=. move/N.ltb_spec0: Hlt => Hlt.
    by erewrite (update_func_tr tr_ref); last exact: Hlt.
  - apply: r_table_set_failure.
    rewrite N_of_uint_tr // /stab_update /= lookup_N_total // lookup_N_tr //= /tab_size length_size size_map.
    have -> : (n <? N.of_nat (size (S.REFS ((S.store_TABLES s) [|(S.TABLES (S.frame_MODULE f)) [|tr_u32 x|]|]))))%num = false
      by exact: Hlt.
    by [].
Qed.

Lemma sim_elem_drop (s : S.store) (f : S.frame) x :
  elem_ok s f x ->
  sim (cfg s f [ :: S.admininstr_ELEM_DROP x]) (S.mk_config (S.with_elem (S.mk_state s f) x [ ::]) [ ::]).
Proof.
  move=> [H1 H2] hs. rewrite /= /tr_admins /=. apply: reduce_trans_step. apply: r_elem_drop.
  rewrite /selem_drop /= lookup_N_total // lookup_N_tr //=.
  unfold RecordSet.set; rewrite /tr_store /tr_u32 /=.
  by erewrite (update_func_tr tr_eleminst); last exact: H2.
Qed.

Lemma sim_data_drop (s : S.store) (f : S.frame) x :
  data_ok s f x ->
  sim (cfg s f [ :: S.admininstr_DATA_DROP x]) (S.mk_config (S.with_data (S.mk_state s f) x [ ::]) [ ::]).
Proof.
  move=> [H1 H2] hs. rewrite /= /tr_admins /=. apply: reduce_trans_step. apply: r_data_drop.
  rewrite /sdata_drop /= lookup_N_total // lookup_N_tr //=.
  unfold RecordSet.set; rewrite /tr_store /tr_u32 /=.
  by erewrite (update_func_tr tr_datainst); last exact: H2.
Qed.

Lemma map_repeat_N {A B : Type} (g : A -> B) (x : A) (n : N) :
  map g (S.list_repeat x n) = List.repeat (g x) (N.to_nat n).
Proof. rewrite /S.list_repeat. by elim: (N.to_nat n) => //= k ->. Qed.

Lemma wf_limits_u32 i j :
  S.wf_limits (S.mk_limits i j) ->
  (S.proj_uN_0 i < 4294967296)%num /\ (forall m, j = Some m -> (S.proj_uN_0 m < 4294967296)%num).
Proof.
  move=> H; inversion H; subst; clear H. case: i H2 => i Hi. split; first exact: wf_uN32.
  move=> m E. subst. inversion H3; subst; clear H3. case: m H1 => m Hm. exact: wf_uN32.
Qed.

Lemma growtable_tr T n r ti :
  S.fun_growtable T n r (Some ti) ->
  growtable (tr_tableinst T) n (tr_ref r) = Some (tr_tableinst ti).
Proof.
  move=> H; inversion H; subst; clear H.
  repeat match goal with Hb : is_true (_ == _) |- _ => move/eqP: Hb => Hb; subst end.
  match goal with Hw : S.wf_tableinst {| S.tableinst_TYPE := S.mk_tabletype (S.mk_limits (S.mk_uN _) _) _ |} |- _ =>
    inversion Hw; subst end.
  match goal with Hw : S.wf_tabletype _ |- _ => inversion Hw; subst end.
  match goal with Hl : S.wf_limits (S.mk_limits (S.mk_uN _) _) |- _ =>
    have [Hi' Hj] := wf_limits_u32 Hl end.
  rewrite /growtable /tab_size /= length_size size_map.
  have -> : (u32_bound <=? N.of_nat (size r'_lst) + n)%num = false
    by apply/N.leb_gt; rewrite /u32_bound; move: Hi' => /=; lia.
  have -> : limit_valid_range {| lim_min := (N.of_nat (size r'_lst) + n)%num;
                                 lim_max := Datatypes.option_map tr_u32 j_opt |} table_limit_bound = true.
  { rewrite /limit_valid_range /table_limit_bound /u32_bound /=.
    apply/andP; split; first by apply/N.leb_spec0; move: Hi' => /=; lia.
    match goal with Hf : List.Forall _ (S.option_to_list j_opt) |- _ => move: Hf end.
    destruct j_opt as [m| ]; move=> //= Hm. inversion Hm; subst.
    have := Hj m erefl. rewrite /tr_u32.
    match goal with H1 : is_true (_ <=? _)%num |- _ => move: H1 => /N.leb_spec0 H1 Hm' end.
    apply/andP; split; apply/N.leb_spec0; move: Hi' => /=; lia. }
  by rewrite /tr_tableinst /= map_cat map_repeat_N.
Qed.

(* Conversely, if WasmCert can grow a well-formed table, so can SpecTec. *)
Lemma sim_table_grow (s : S.store) (f : S.frame) x (r : S.ref) n ti :
  tab_ok s f x -> (n < 4294967296)%num -> S.fun_growtable (tabz s f x) n r (Some ti) ->
  sim (cfg s f [ :: S.admininstr_ref r; i32c n; S.admininstr_TABLE_GROW x])
      (S.mk_config (S.with_tableinst (S.mk_state s f) x ti) [ :: i32c (N.of_nat (size (refsz s f x)))]).
Proof.
  move=> [H1 H2] Hn Hg hs.
  have E : tr_i32 (S.mk_uN (N.of_nat (size (refsz s f x))))
           = Wasm_int.int_of_Z i32m (Z.of_nat (tab_size (tr_tableinst (tabz s f x)))).
  { apply: tr_i32_of_Z. by rewrite tab_size_tr nat_N_Z. }
  rewrite [tr_cfg _ _]/= [tr_cfg _ (S.mk_config _ _)]/= /tr_admins; cbn [seq.map tr_admin i32c tr_instr].
  rewrite tr_admin_ref E. apply: reduce_trans_step.
  apply: r_table_grow_success.
  rewrite N_of_uint_tr // /stab_grow /= lookup_N_total // lookup_N_tr //.
  rewrite (growtable_tr Hg) /=. unfold RecordSet.set; rewrite /tr_store /tr_u32 /=.
  by erewrite (update_func_tr tr_tableinst); last exact: H2.
Qed.

Lemma mkseq_const {T : Type} (x : T) m : mkseq (fun _ => x) m = List.repeat x m.
Proof. rewrite /mkseq. elim: m 0 => //= m IH k. by rewrite IH. Qed.

(* Growing a memory whose size is a whole number of pages. *)
Lemma growmem_tr mi n mi' k :
  N.of_nat (size (S.BYTES mi)) = (k * 65536)%num ->
  S.fun_growmemory mi n (Some mi') ->
  mem_grow (tr_meminst mi) n = Some (tr_meminst mi').
Proof.
  move=> Hk H; inversion H; subst; clear H.
  repeat match goal with Hb : is_true (_ == _) |- _ => move/eqP: Hb => Hb; subst end.
  rewrite /= in Hk. move/QArith_base.Qeq_bool_eq: H2 => H2.
  (* the new page count is the old one plus [n] *)
  have E1 : QArith_base.Qeq
      (QArith_base.Qplus (QArith_base.Qdiv (QArith_base.inject_Z (Z.of_N (N.of_nat (size b_lst))))
                                           (QArith_base.inject_Z (Z.of_N (64 * S.Ki)%num)))
                         (QArith_base.inject_Z (Z.of_N n)))
      (QArith_base.inject_Z (Z.of_N k + Z.of_N n)).
  { rewrite Hk /QArith_base.Qeq /QArith_base.Qdiv /QArith_base.Qmult /QArith_base.Qinv
            /QArith_base.Qplus /QArith_base.inject_Z /=. lia. }
  have Ei' := QArith_base.Qeq_trans _ _ _ H2 E1.
  have Ef : Qround.Qfloor i' = (Z.of_N k + Z.of_N n)%Z
    by rewrite (Qround.Qfloor_comp _ _ Ei') Qround.Qfloor_Z.
  move/QArith_base.Qle_bool_iff: H4 => H4.
  have H16 : (k + n <= 65536)%num.
  { move: Ei' H4. rewrite /QArith_base.Qeq /QArith_base.Qle /QArith_base.inject_Z /=. nia. }
  have Hsz : mem_size (tr_meminst {| S.meminst_TYPE := S.PAGE (S.mk_limits i j_opt); S.BYTES := b_lst |}) = k
    by rewrite /mem_size mem_length_tr /= Hk N.div_mul.
  rewrite /mem_grow Hsz.
  have -> : (k + n <=? mem_limit_bound)%num = true by apply/N.leb_le; rewrite /mem_limit_bound; lia.
  cbn. rewrite /memory_list.ml_grow /tr_mem_data. cbn [memory_list.ml_data memory_list.ml_init].
  (* the byte comparison is on unary naturals: never compute it *)
  case: Nat.leb_spec0 => Hbl; last first.
  { exfalso. apply: Hbl. rewrite !nat_bin length_size size_map Hk /byte_limit /page_size /page_limit. lia. }
  clear Hbl.
  have Hmin : Z.to_N (Qround.Qfloor i') = (k + n)%num by rewrite Ef -N2Z.inj_add N2Z.id.
  have Hdata : map tr_byte (b_lst ++ S.list_repeat (S.mk_byte 0) (n * 65536))
               = map tr_byte b_lst ++ mkseq (fun _ => Integers.Byte.zero) (N.to_nat (n * page_size))
    by rewrite map_cat map_repeat_N mkseq_const.
  clear H6 H9 Hsz. case: j_opt H3 => [jm | ] H3 /=.
  - inversion H3 as [ | ? ? Hj _]; subst. move/QArith_base.Qle_bool_iff: Hj => Hj.
    have -> : (k + n <=? tr_u32 jm)%num = true.
    { apply/N.leb_le. move: Ei' Hj.
      rewrite /tr_u32 /QArith_base.Qeq /QArith_base.Qle /QArith_base.inject_Z /=. nia. }
    rewrite /tr_meminst /tr_memtype /tr_limits /tr_mem_data. cbn [S.meminst_TYPE S.BYTES].
    by rewrite Hdata /tr_u32 /= Hmin.
  - rewrite /tr_meminst /tr_memtype /tr_limits /tr_mem_data. cbn [S.meminst_TYPE S.BYTES].
    by rewrite Hdata /tr_u32 /= Hmin.
Qed.

(* SpecTec computes the page count in Q. *)
Lemma page_count b k :
  b = (k * 65536)%num ->
  Z.to_N (Qround.Qfloor (QArith_base.Qdiv (QArith_base.inject_Z (Z.of_N b))
                                         (QArith_base.inject_Z (Z.of_N (64 * S.Ki)%num)))) = k.
Proof.
  move=> ->. rewrite -Qround.Zdiv_Qdiv. change (Z.of_N (64 * S.Ki)%num) with 65536%Z.
  by rewrite N2Z.inj_mul Z.div_mul // N2Z.id.
Qed.

(* Conversely, if WasmCert can grow a well-formed memory whose size is a whole
   number of pages, so can SpecTec. *)
Lemma sim_memory_grow (s : S.store) (f : S.frame) n k mi' :
  mem_ok s f -> (n < 4294967296)%num -> N.of_nat (size (bytesz s f)) = (k * 65536)%num ->
  S.fun_growmemory (memz s f) n (Some mi') ->
  sim (cfg s f [ :: i32c n; S.admininstr_MEMORY_GROW])
      (S.mk_config (S.with_meminst (S.mk_state s f) (S.mk_uN 0) mi') [ :: i32c k]).
Proof.
  move=> [H1 H2] Hn Hk Hg hs.
  have E : tr_i32 (S.mk_uN k) = Wasm_int.int_of_Z i32m (Z.of_N (mem_size (tr_meminst (memz s f)))).
  { apply: tr_i32_of_Z. by rewrite /mem_size mem_length_tr Hk N.div_mul. }
  rewrite [tr_cfg _ _]/= [tr_cfg _ (S.mk_config _ _)]/= /tr_admins;
    cbn [seq.map tr_admin i32c tr_instr tr_num].
  rewrite E. apply: reduce_trans_step. apply: r_memory_grow_success.
  rewrite N_of_uint_tr // /smem_grow /= lookup_N_total // lookup_N_tr //.
  rewrite (growmem_tr Hk Hg) /=. rewrite /upd_s_mem /tr_store /tr_u32 /=.
  by erewrite (update_func_tr tr_meminst); last exact: H2.
Qed.

Lemma sim_memory_grow_fail (s : S.store) (f : S.frame) n m :
  mem_ok s f -> (n < 4294967296)%num -> S.fun_inv_signed_ 32%num (-1)%Z m ->
  mem_grow (tr_meminst (memz s f)) n = None ->
  sim (cfg s f [ :: i32c n; S.admininstr_MEMORY_GROW]) (cfg s f [ :: i32c m]).
Proof.
  move=> [H1 H2] Hn Hm Hg hs. rewrite /= /tr_admins /=. apply: reduce_trans_step.
  have -> : tr_i32 (S.mk_uN m) = int32_minus_one.
  { inversion Hm; subst;
    match goal with Hb : is_true (_ && _) |- _ => move: Hb => /andP [/Z.leb_spec0 Ha /Z.ltb_spec0 Hb] end;
    simpl in *; try lia.
    by apply: Wasm_int.Int32.mkint_eq. }
  apply: r_memory_grow_failure.
  by rewrite N_of_uint_tr // /smem_grow /= lookup_N_total // lookup_N_tr // Hg.
Qed.

Lemma sim_table_grow_fail (s : S.store) (f : S.frame) x (r : S.ref) n m :
  tab_ok s f x -> (n < 4294967296)%num -> S.fun_inv_signed_ 32%num (-1)%Z m ->
  growtable (tr_tableinst (tabz s f x)) n (tr_ref r) = None ->
  sim (cfg s f [ :: S.admininstr_ref r; i32c n; S.admininstr_TABLE_GROW x]) (cfg s f [ :: i32c m]).
Proof.
  move=> [H1 H2] Hn Hm Hg hs. rewrite /= /tr_admins /= tr_admin_ref. apply: reduce_trans_step.
  have -> : tr_i32 (S.mk_uN m) = int32_minus_one.
  { inversion Hm; subst;
    match goal with Hb : is_true (_ && _) |- _ => move: Hb => /andP [/Z.leb_spec0 Ha /Z.ltb_spec0 Hb] end;
    simpl in *; try lia.
    by apply: Wasm_int.Int32.mkint_eq. }
  apply: r_table_grow_failure.
  by rewrite N_of_uint_tr // /stab_grow /= lookup_N_total // lookup_N_tr // Hg.
Qed.

(** * Side conditions of store-accessing redexes *)

(* Indices must be in range and table entries met by call_indirect must be
   function references to existing functions.  SpecTec's accessors silently
   return default values out of range, while WasmCert gets stuck; validation
   and store typing rule both situations out.  Memory and vector redexes are
   not covered by the simulation yet and are reported as exceptions. *)

Definition addr_okb (idxs : seq N) (len : nat) (x : N) : bool :=
  N.ltb x (N.of_nat (size idxs)) && N.ltb (S.lookup_total idxs x) (N.of_nat len).

Lemma addr_okP idxs len x : addr_okb idxs len x -> addr_ok idxs len x.
Proof. by case/andP => /N.ltb_spec0 ? /N.ltb_spec0 ?. Qed.

Definition funcref_okb (s : S.store) (r : S.ref) : bool :=
  match r with
  | S.ref_REF_NULL _ => true
  | S.REF_FUNC_ADDR a => N.ltb a (N.of_nat (size (S.store_FUNCS s)))
  | S.REF_HOST_ADDR _ => false
  end.

Lemma funcref_okP s r : funcref_okb s r -> funcref_ok s r.
Proof. by case: r => //= a /N.ltb_spec0. Qed.

Definition is_ref_admin (a : S.admininstr) : bool :=
  match a with
  | S.admininstr_REF_NULL _ | S.admininstr_REF_FUNC_ADDR _ | S.admininstr_REF_HOST_ADDR _ => true
  | _ => false
  end.

Definition callee_okb (s : S.store) (a : N) : bool :=
  match S.CODE (S.lookup_total (S.store_FUNCS s) a) with
  | S.func_FUNC _ ls _ => all (fun l => match l with S.LOCAL t => t != S.valtype_V128 end) ls
  end.

(* Loads and stores: their byte encodings are axioms in SpecTec. *)
Definition is_mem_admin (a : S.admininstr) : bool :=
  match a with
  | S.admininstr_LOAD _ _ _ | S.admininstr_STORE _ _ _ => true
  | _ => false
  end.

Definition is_i32_admin (a : S.admininstr) : bool :=
  match a with
  | S.admininstr_CONST S.I32 (S.mk_num__0 S.Inn_I32 _) => true
  | _ => false
  end.

Lemma i32_admin_val v :
  is_i32_admin (S.admininstr_val v) -> exists c, v = S.val_CONST S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN c)).
Proof.
  case: v => //= nt c. case: nt => //. case: c => // inn u. case: inn => //.
  case: u => cv _. by exists cv.
Qed.

Definition ok_redex (z : S.state) (es : seq S.admininstr) : bool :=
  match z with
  | S.mk_state s f =>
    let mi := S.frame_MODULE f in
    let tabb x := addr_okb (S.TABLES mi) (size (S.store_TABLES s)) (S.proj_uN_0 x) in
    let globb x := addr_okb (S.GLOBALS mi) (size (S.store_GLOBALS s)) (S.proj_uN_0 x) in
    let elemb x := addr_okb (S.ELEMS mi) (size (S.store_ELEMS s)) (S.proj_uN_0 x) in
    let datab x := addr_okb (S.DATAS mi) (size (S.store_DATAS s)) (S.proj_uN_0 x) in
    let typeb x := N.ltb (S.proj_uN_0 x) (N.of_nat (size (S.TYPES mi))) in
    let localb x := N.ltb (S.proj_uN_0 x) (N.of_nat (size (S.LOCALS f))) in
    let memb := addr_okb (S.MEMS mi) (size (S.store_MEMS s)) 0 in
    let pagesb := N.eqb (N.modulo (N.of_nat (size (S.BYTES (S.fun_mem z (S.mk_uN 0))))) 65536) 0 in
    match rev es with
    | S.admininstr_BLOCK (S._IDX x) _ :: _ => typeb x
    | S.admininstr_LOOP (S._IDX x) _ :: _ => typeb x
    | S.admininstr_CALL_INDIRECT x y :: S.admininstr_CONST _ (S.mk_num__0 _ (S.mk_uN n)) :: _ =>
        tabb x && typeb y &&
        (if N.ltb n (N.of_nat (size (S.REFS (S.fun_table z x))))
         then funcref_okb s (S.lookup_total (S.REFS (S.fun_table z x)) n) else true)
    | S.CALL_ADDR a :: _ => callee_okb s a
    | S.admininstr_LOCAL_GET x :: _ => localb x
    | S.admininstr_LOCAL_SET x :: _ => localb x
    | S.admininstr_GLOBAL_GET x :: _ => globb x
    | S.admininstr_GLOBAL_SET x :: _ => globb x
    | S.admininstr_TABLE_GET x :: _ => tabb x
    | S.admininstr_TABLE_SET x :: _ => tabb x
    | S.admininstr_TABLE_SIZE x :: _ => tabb x
    | S.admininstr_TABLE_GROW x :: _ => tabb x
    | S.admininstr_TABLE_FILL x :: _ :: v :: _ => tabb x && is_ref_admin v
    | S.admininstr_TABLE_COPY x y :: _ => tabb x && tabb y
    | S.admininstr_TABLE_INIT x y :: _ => tabb x && elemb y
    | S.admininstr_ELEM_DROP x :: _ => elemb x
    | S.admininstr_DATA_DROP x :: _ => datab x
    | S.admininstr_MEMORY_SIZE :: _ => memb
    | S.admininstr_MEMORY_GROW :: _ => memb && pagesb
    | S.admininstr_MEMORY_FILL :: _ :: v :: _ => memb && is_i32_admin v
    | S.admininstr_MEMORY_COPY :: _ => memb
    | S.admininstr_MEMORY_INIT x :: _ => memb && datab x
    | a :: _ => ~~ is_mem_admin a && ~~ is_vec_admin a
    | [ ::] => true
    end
  end.

(** * Reading steps *)

Lemma wf_cfg_instrs s f es : S.wf_config (cfg s f es) -> List.Forall S.wf_admininstr es.
Proof. by move=> H; inversion H. Qed.

Lemma wf_i32_const es c n :
  List.Forall S.wf_admininstr es -> List.In (S.admininstr_CONST S.I32 c) es ->
  c = S.mk_num__0 S.Inn_I32 (S.mk_uN n) -> (n < 4294967296)%num.
Proof.
  move=> /List.Forall_forall H Hin Ec. subst.
  have := wf_num_I32 (wf_admin_const (H _ Hin)). by case=> m [[->]].
Qed.

Lemma ref_admin_val v : is_ref_admin (S.admininstr_val v) -> exists r, ref_val v = Some r.
Proof. by case: v => //= [rt|a|a] _; eexists. Qed.

Lemma Forall_neq {A : Type} {B : eqType} (P : A -> B) (l : seq A) (c : B) :
  List.Forall (fun t => P t != c) l -> List.Forall (fun t => P t <> c) l.
Proof. move=> H. apply: List.Forall_impl H => t /eqP. done. Qed.

Lemma all_local_no_v128 ts :
  all (fun l => match l with S.LOCAL t => t != S.valtype_V128 end) (map S.LOCAL ts) -> no_v128 ts.
Proof.
  rewrite /no_v128. elim: ts => [ |t ts IH] /=; first by move=> _ [].
  move=> /andP [Ht Hts] [E | Hin].
  - subst t. by rewrite eqxx in Ht.
  - exact: IH Hts Hin.
Qed.

Lemma callee_no_v128 s a x ts ins tf mm :
  callee_okb s a ->
  S.lookup_total (S.store_FUNCS s) a =
    {| S.funcinst_TYPE := tf; S.funcinst_MODULE := mm; S.CODE := S.func_FUNC x (map S.LOCAL ts) ins |} ->
  no_v128 ts.
Proof. rewrite /callee_okb => Hok E. rewrite E /= in Hok. exact: all_local_no_v128. Qed.

Ltac excl :=
  intros;
  match goal with Hc : S.mk_config _ _ = S.mk_config _ _ |- _ => case: Hc => ? ?; subst end;
  match goal with z : S.state |- _ => destruct z end;
  match goal with Hok : is_true (ok_redex _ _) |- _ => rewrite /ok_redex ?rev_cat /= in Hok; by [] end.

Lemma wf_i32_lit n : S.wf_num_ S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN n)) -> (n < 4294967296)%num.
Proof. move=> /wf_num_I32 [m [[->] Hm]] //. Qed.

Ltac wf_all :=
  match goal with Hwf : S.wf_config _ |- _ => apply wf_cfg_instrs in Hwf end; wf_get.

Ltac i32s :=
  repeat match goal with
  | H : S.wf_num_ S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN ?n)) |- _ => apply wf_i32_lit in H
  | H : S.wf_num_ S.I32 ?c |- _ => is_var c; i32_of c
  end.

Ltac grab_i32 c nm Hnm :=
  match goal with H : S.wf_num_ S.I32 c |- _ => have [nm [? Hnm]] := wf_num_I32 H; subst c end.
Ltac grab_lit n Hnm :=
  match goal with H : S.wf_num_ S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN n)) |- _ =>
    have Hnm := wf_i32_lit H end.

Ltac norm :=
  cbn [S.coerce S.proj_uN_0_coercion S.proj_num__0 S.the S.proj_uN_0] in *;
  unfold S.N_gtb, S.N_geb in *.

Lemma leb_ltb_false a b : (a <=? b)%num = true -> (b <? a)%num = false.
Proof. move=> /N.leb_spec0 H. apply/N.ltb_ge. lia. Qed.

Lemma neq_eqb_false (a : N) : a != 0%num -> N.eqb a 0 = false.
Proof. by move=> /eqP H; apply/N.eqb_neq. Qed.

Lemma wf_cfg_data_bytes s f es :
  S.wf_config (cfg s f es) ->
  forall x, data_ok s f x -> List.Forall S.wf_byte (S.datainst_BYTES (S.fun_data (S.mk_state s f) x)).
Proof.
  move=> Hwf x [_ Ha]. inversion Hwf as [z0 es0 Hz _]; subst.
  inversion Hz as [s0 f0 Hs _]; subst. clear Hwf Hz. case: s Hs Ha => fs gs ts ms es1 ds Hs Ha.
  inversion Hs as [? ? ? ? ? ? _ _ _ _ Hds]; subst. rewrite /S.fun_data /=.
  have : S.wf_datainst (S.lookup_total ds (S.lookup_total (S.DATAS (S.frame_MODULE f)) (S.proj_uN_0 x)))
    by apply: Forall_lookup_total Hds Ha.
  by case.
Qed.

Lemma Step_read_sim z es es' :
  S.Step_read (S.mk_config z es) es' -> S.wf_config (S.mk_config z es) -> ok_redex z es ->
  sim (S.mk_config z es) (S.mk_config z es').
Proof.
  move=> H. remember (S.mk_config z es) as c eqn:Hc. case: H Hc.
  all: try (excl; fail).
  - (* block *)
    move=> z0 k vs bt ins n t1 t2 /eqP Hft /eqP Hk1 /eqP Hk2 /eqP Hn [<- <-] Hwf Hok.
    case: z0 Hft Hwf Hok => s f Hft Hwf Hok. subst n.
    move: Hok; rewrite /ok_redex rev_cat /= => Hok.
    have Hbt : bt_ok f bt.
    { clear -Hok. destruct bt as [t|x]; first done. by move: Hok => /= /N.ltb_spec0. }
    apply: (@sim_block s f vs bt ins t1 t2) => //. apply: Nat2N.inj. by rewrite -Hk1 -Hk2.
  - (* loop *)
    move=> z0 k vs bt ins t1 n t2 /eqP Hft /eqP Hk1 /eqP Hk2 /eqP Hn [<- <-] Hwf Hok.
    case: z0 Hft Hwf Hok => s f Hft Hwf Hok. subst n. rewrite Hk2.
    move: Hok; rewrite /ok_redex rev_cat /= => Hok.
    have Hbt : bt_ok f bt.
    { clear -Hok. destruct bt as [t|x]; first done. by move: Hok => /= /N.ltb_spec0. }
    apply: (@sim_loop s f vs bt ins t1 t2) => //. apply: Nat2N.inj. by rewrite -Hk1 -Hk2.
  - (* call *)
    move=> z0 x /N.ltb_spec0 Hx [<- <-] Hwf Hok. case: z0 Hx Hwf Hok => s f Hx _ _.
    exact: sim_call.
  - (* call_indirect_call *)
    move=> z0 i x y a H1 _ /eqP H3 /N.ltb_spec0 H4 /eqP H5 [<- <-] Hwf Hok.
    case: z0 H1 H3 H4 H5 Hwf Hok => s f H1 H3 H4 H5 Hwf Hok. wf_all. i32s. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/andP [/addr_okP Hx /N.ltb_spec0 Hy] _].
    apply: sim_call_indirect => //. exact/N.ltb_spec0.
  - (* call_indirect_trap *)
    move=> z0 i x y Hnot [<- <-] Hwf Hok.
    case: z0 Hnot Hwf Hok => s f Hnot Hwf Hok. wf_all. i32s.
    move: Hok; rewrite /ok_redex /= => /andP [/andP [/addr_okP Hx /N.ltb_spec0 Hy] Hr].
    apply: sim_call_indirect_trap => //.
    + move=> /N.ltb_spec0 Hlt. move: Hr. rewrite Hlt. exact: funcref_okP.
    + move=> [a [Hlt [Ha [Hf Ht]]]]. apply: Hnot.
      apply: (@S.call_indirect_call_0 _ _ _ _ a).
      * exact/N.ltb_spec0.
      * by [].
      * by apply/eqP.
      * exact/N.ltb_spec0.
      * by apply/eqP.
  - (* call_addr *)
    move=> z0 k vs a n f' ins t1 t2 mm fn x ts /N.ltb_spec0 Ha /eqP Hfi /eqP Hfn Hd /eqP Hf' _ _ _
           /eqP Hk1 /eqP Hk2 /eqP Hn [<- <-] Hwf Hok.
    case: z0 Ha Hfi Hwf Hok => s f Ha Hfi Hwf Hok. subst fn f' n.
    move: Hok; rewrite /ok_redex rev_cat /= => Hok.
    apply: (@sim_call_addr s f vs a t1 t2 mm x ts ins) => //.
    + exact: Forall_neq Hd.
    + exact: callee_no_v128 Hok Hfi.
    + apply: Nat2N.inj. by rewrite -Hk1 -Hk2.
  - (* ref_func *)
    move=> z0 x /N.ltb_spec0 Hx [<- <-] Hwf Hok. case: z0 Hx Hwf Hok => s f Hx _ _.
    exact: sim_ref_func.
  - (* local_get *)
    move=> z0 x [<- <-] Hwf Hok. case: z0 Hwf Hok => s f _ Hok.
    move: Hok; rewrite /ok_redex /= => /N.ltb_spec0 Hx. exact: sim_local_get.
  - (* global_get *)
    move=> z0 x [<- <-] Hwf Hok. case: z0 Hwf Hok => s f _ Hok.
    move: Hok; rewrite /ok_redex /= => /addr_okP Hx. exact: sim_global_get.
  - (* table_get_trap *)
    move=> z0 i x _ H2 [<- <-] Hwf Hok. case: z0 H2 Hwf Hok => s f H2 Hwf Hok.
    wf_all. grab_i32 i ni Hni. norm. move: Hok; rewrite /ok_redex /= => /addr_okP Hx.
    have := @sim_table_get s f x ni Hx Hni. by rewrite (leb_ltb_false H2).
  - (* table_get_val *)
    move=> z0 i x H1 _ [<- <-] Hwf Hok. case: z0 H1 Hwf Hok => s f H1 Hwf Hok.
    wf_all. grab_i32 i ni Hni. norm. move: Hok; rewrite /ok_redex /= => /addr_okP Hx.
    have := @sim_table_get s f x ni Hx Hni. by rewrite H1.
  - (* table_size *)
    move=> z0 x n /eqP Hn [<- <-] Hwf Hok. case: z0 Hn Hwf Hok => s f Hn _ Hok. subst n.
    move: Hok; rewrite /ok_redex /= => /addr_okP Hx. exact: sim_table_size.
  - (* table_fill_trap *)
    move=> z0 i v n x _ H2 [<- <-] Hwf Hok. case: z0 H2 Hwf Hok => s f H2 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /ref_admin_val [r Hr]].
    have := @sim_table_fill s f x ni n v r Hx Hni Hn Hr. by rewrite H2.
  - (* table_fill_zero *)
    move=> z0 i v n x _ H2 H3 [<- <-] Hwf Hok. case: z0 H2 H3 Hwf Hok => s f H2 H3 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_lit n Hn. norm. move/eqP: H3 => H3.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /ref_admin_val [r Hr]].
    have := @sim_table_fill s f x ni n v r Hx Hni Hn Hr. by rewrite (leb_ltb_false H2) H3.
  - (* table_fill_succ *)
    move=> z0 i v n x _ H2 H3 [<- <-] Hwf Hok. case: z0 H2 H3 Hwf Hok => s f H2 H3 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /ref_admin_val [r Hr]].
    have := @sim_table_fill s f x ni n v r Hx Hni Hn Hr.
    by rewrite (leb_ltb_false H3) (neq_eqb_false H2).
  - (* table_copy_trap *)
    move=> z0 j i n x y _ _ H3 [<- <-] Hwf Hok. case: z0 H3 Hwf Hok => s f H3 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /addr_okP Hy].
    have := @sim_table_copy s f x y nj ni n Hx Hy Hnj Hni Hn. by rewrite H3.
  - (* table_copy_zero *)
    move=> z0 j i n x y _ _ /andP [H3 H3'] H4 [<- <-] Hwf Hok.
    case: z0 H3 H3' H4 Hwf Hok => s f H3 H3' H4 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm. move/eqP: H4 => H4.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /addr_okP Hy].
    have := @sim_table_copy s f x y nj ni n Hx Hy Hnj Hni Hn.
    by rewrite (leb_ltb_false H3) (leb_ltb_false H3') H4.
  - (* table_copy_le *)
    move=> z0 j i n x y _ _ H3 /andP [H4 H4'] H5 [<- <-] Hwf Hok.
    case: z0 H3 H4 H4' H5 Hwf Hok => s f H3 H4 H4' H5 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /addr_okP Hy].
    have := @sim_table_copy s f x y nj ni n Hx Hy Hnj Hni Hn.
    by rewrite (leb_ltb_false H4) (leb_ltb_false H4') (neq_eqb_false H3) H5.
  - (* table_copy_gt *)
    move=> z0 j i n x y _ _ H3 H4 /andP [H5 H5'] [<- <-] Hwf Hok.
    case: z0 H3 H4 H5 H5' Hwf Hok => s f H3 H4 H5 H5' Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /addr_okP Hy].
    have := @sim_table_copy s f x y nj ni n Hx Hy Hnj Hni Hn.
    have H3' : (nj <=? ni)%num = false by apply/N.leb_gt; move/N.ltb_spec0: H3.
    by rewrite (leb_ltb_false H5) (leb_ltb_false H5') (neq_eqb_false H4) H3'.
  - (* table_init_trap *)
    move=> z0 j i n x y _ _ H3 [<- <-] Hwf Hok. case: z0 H3 Hwf Hok => s f H3 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /addr_okP Hy].
    have := @sim_table_init s f x y nj ni n Hx Hy Hnj Hni Hn. by rewrite H3.
  - (* table_init_zero *)
    move=> z0 j i n x y _ _ /andP [H3 H3'] H4 [<- <-] Hwf Hok.
    case: z0 H3 H3' H4 Hwf Hok => s f H3 H3' H4 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm. move/eqP: H4 => H4.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /addr_okP Hy].
    have := @sim_table_init s f x y nj ni n Hx Hy Hnj Hni Hn.
    by rewrite (leb_ltb_false H3) (leb_ltb_false H3') H4.
  - (* table_init_succ *)
    move=> z0 j i n x y _ _ _ H4 /andP [H5 H5'] [<- <-] Hwf Hok.
    case: z0 H4 H5 H5' Hwf Hok => s f H4 H5 H5' Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hx /addr_okP Hy].
    have := @sim_table_init s f x y nj ni n Hx Hy Hnj Hni Hn.
    by rewrite (leb_ltb_false H5) (leb_ltb_false H5') (neq_eqb_false H4).
  - (* memory_size *)
    move=> z0 n /eqP Hn _ [<- <-] Hwf Hok. case: z0 Hn Hwf Hok => s f Hn _ Hok.
    move: Hok; rewrite /ok_redex /= => /addr_okP Hm.
    apply: sim_memory_size Hm _. rewrite -Hn /S.Ki. lia.
  - (* memory_fill_trap *)
    move=> z0 i v n _ H2 _ [<- <-] Hwf Hok. case: z0 H2 Hwf Hok => s f H2 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hm /i32_admin_val [cv Ec]]. subst v.
    have := @sim_memory_fill s f ni n cv Hm Hni Hn. by rewrite H2.
  - (* memory_fill_zero *)
    move=> z0 i v n _ H2 H3 [<- <-] Hwf Hok. case: z0 H2 H3 Hwf Hok => s f H2 H3 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_lit n Hn. norm. move/eqP: H3 => H3.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hm /i32_admin_val [cv Ec]]. subst v.
    have := @sim_memory_fill s f ni n cv Hm Hni Hn. by rewrite (leb_ltb_false H2) H3.
  - (* memory_fill_succ *)
    move=> z0 i v n _ H2 H3 [<- <-] Hwf Hok. case: z0 H2 H3 Hwf Hok => s f H2 H3 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hm /i32_admin_val [cv Ec]]. subst v.
    have := @sim_memory_fill s f ni n cv Hm Hni Hn.
    by rewrite (leb_ltb_false H3) (neq_eqb_false H2).
  - (* memory_copy_trap *)
    move=> z0 j i n _ _ H3 _ [<- <-] Hwf Hok. case: z0 H3 Hwf Hok => s f H3 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /addr_okP Hm.
    have := @sim_memory_copy s f nj ni n Hm Hnj Hni Hn. by rewrite H3.
  - (* memory_copy_zero *)
    move=> z0 j i n _ _ /andP [H3 H3'] H4 [<- <-] Hwf Hok.
    case: z0 H3 H3' H4 Hwf Hok => s f H3 H3' H4 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm. move/eqP: H4 => H4.
    move: Hok; rewrite /ok_redex /= => /addr_okP Hm.
    have := @sim_memory_copy s f nj ni n Hm Hnj Hni Hn.
    by rewrite (leb_ltb_false H3) (leb_ltb_false H3') H4.
  - (* memory_copy_le *)
    move=> z0 j i n _ _ H3 /andP [H4 H4'] H5 [<- <-] Hwf Hok.
    case: z0 H3 H4 H4' H5 Hwf Hok => s f H3 H4 H4' H5 Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /addr_okP Hm.
    have := @sim_memory_copy s f nj ni n Hm Hnj Hni Hn.
    by rewrite (leb_ltb_false H4) (leb_ltb_false H4') (neq_eqb_false H3) H5.
  - (* memory_copy_gt *)
    move=> z0 j i n _ _ H3 H4 /andP [H5 H5'] [<- <-] Hwf Hok.
    case: z0 H3 H4 H5 H5' Hwf Hok => s f H3 H4 H5 H5' Hwf Hok.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /addr_okP Hm.
    have := @sim_memory_copy s f nj ni n Hm Hnj Hni Hn.
    have H3' : (nj <=? ni)%num = false by apply/N.leb_gt; move/N.ltb_spec0: H3.
    by rewrite (leb_ltb_false H5) (leb_ltb_false H5') (neq_eqb_false H4) H3'.
  - (* memory_init_trap *)
    move=> z0 j i n x _ _ H3 _ [<- <-] Hwf Hok. case: z0 H3 Hwf Hok => s f H3 Hwf Hok.
    have Hb := wf_cfg_data_bytes Hwf.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hm /addr_okP Hx].
    have := @sim_memory_init s f x nj ni n Hm Hx (Hb x Hx) Hnj Hni Hn. by rewrite H3.
  - (* memory_init_zero *)
    move=> z0 j i n x _ _ /andP [H3 H3'] H4 [<- <-] Hwf Hok.
    case: z0 H3 H3' H4 Hwf Hok => s f H3 H3' H4 Hwf Hok.
    have Hb := wf_cfg_data_bytes Hwf.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm. move/eqP: H4 => H4.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hm /addr_okP Hx].
    have := @sim_memory_init s f x nj ni n Hm Hx (Hb x Hx) Hnj Hni Hn.
    by rewrite (leb_ltb_false H3) (leb_ltb_false H3') H4.
  - (* memory_init_succ *)
    move=> z0 j i n x _ _ _ H4 /andP [H5 H5'] [<- <-] Hwf Hok.
    case: z0 H4 H5 H5' Hwf Hok => s f H4 H5 H5' Hwf Hok.
    have Hb := wf_cfg_data_bytes Hwf.
    wf_all. grab_i32 i ni Hni. grab_i32 j nj Hnj. grab_lit n Hn. norm.
    cbn [S.proj_byte_0_coercion S.coerce] in *.
    move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hm /addr_okP Hx].
    have := @sim_memory_init s f x nj ni n Hm Hx (Hb x Hx) Hnj Hni Hn.
    by rewrite (leb_ltb_false H5) (leb_ltb_false H5') (neq_eqb_false H4).
Qed.

(** * Plain redexes and contexts *)

Definition is_val_admin (a : S.admininstr) : bool :=
  match a with
  | S.admininstr_CONST _ _ | S.admininstr_VCONST _ _ | S.admininstr_REF_NULL _
  | S.admininstr_REF_FUNC_ADDR _ | S.admininstr_REF_HOST_ADDR _ => true
  | _ => false
  end.

(* A plain redex: operand values followed by one non-value instruction. *)
Definition redex_shape (es : seq S.admininstr) : bool :=
  match rev es with
  | a :: vs => all is_val_admin vs && ~~ is_val_admin a
  | [ ::] => false
  end.

Lemma val_admin_is_val v : is_val_admin (S.admininstr_val v).
Proof. by case: v. Qed.

Lemma ref_admin_is_val r : is_val_admin (S.admininstr_ref r).
Proof. by case: r. Qed.

Lemma sim_label z z' n ins es es' :
  sim (S.mk_config z es) (S.mk_config z' es') ->
  sim (S.mk_config z [ :: S.LABEL_ n ins es]) (S.mk_config z' [ :: S.LABEL_ n ins es']).
Proof.
  case: z => s f; case: z' => s' f' H hs. have := reduce_trans_lfill
    (LH_rec [ ::] (N.to_nat n) (to_e_list (tr_instrs ins)) (LH_base [ ::] [ ::]) [ ::]) (H hs).
  by rewrite /= !cats0.
Qed.

Lemma sim_frame s f n f' es s' f'' es' :
  sim (cfg s f' es) (cfg s' f'' es') ->
  sim (cfg s f [ :: S.FRAME_ n f' es]) (cfg s' f [ :: S.FRAME_ n f'' es']).
Proof. move=> H hs. exact: reduce_trans_frame (H hs). Qed.

Lemma sim_instrs z z' vs es es1 es' :
  sim (S.mk_config z es) (S.mk_config z' es') ->
  sim (S.mk_config z (map S.admininstr_val vs ++ es ++ es1))
      (S.mk_config z' (map S.admininstr_val vs ++ es' ++ es1)).
Proof.
  case: z => s f; case: z' => s' f' H hs.
  have := reduce_trans_lfill (LH_base (map tr_val vs) (tr_admins es1)) (H hs).
  by rewrite /= !tr_admins_cat tr_admins_vals.
Qed.

End Reduction.

(** * Steps that are not simulated *)

Notation cfg s f es := (S.mk_config (S.mk_state s f) es).

(* The callee declares a v128 local: WasmCert initialises it with an empty
   byte list ([v128_default = nil]) instead of 16 zero bytes. *)
Definition has_v128_local (s : S.store) (a : S.funcaddr) : bool := ~~ callee_okb s a.

Inductive Step_exc : S.config -> S.config -> Prop :=
  (* numeric disagreements and pure vector steps *)
  | exc_pure z es es' :
      Exc_pure es es' -> Step_exc (S.mk_config z es) (S.mk_config z es')
  (* loads and stores: SpecTec's byte encodings [nbytes_]/[ibytes_] are axioms *)
  | exc_load z vs nt lo ao c' :
      S.Step (S.mk_config z (map S.admininstr_val vs ++ [ :: S.admininstr_LOAD nt lo ao])) c' ->
      Step_exc (S.mk_config z (map S.admininstr_val vs ++ [ :: S.admininstr_LOAD nt lo ao])) c'
  | exc_store z vs nt so ao c' :
      S.Step (S.mk_config z (map S.admininstr_val vs ++ [ :: S.admininstr_STORE nt so ao])) c' ->
      Step_exc (S.mk_config z (map S.admininstr_val vs ++ [ :: S.admininstr_STORE nt so ao])) c'
  (* vector instructions, including vector loads and stores: WasmCert's SIMD
     semantics is opaque *)
  | exc_vector z vs a c' :
      is_vec_admin a ->
      S.Step (S.mk_config z (map S.admininstr_val vs ++ [ :: a])) c' ->
      Step_exc (S.mk_config z (map S.admininstr_val vs ++ [ :: a])) c'
  (* calls to a function with a v128 local *)
  | exc_call_v128 s f vs a c' :
      has_v128_local s a ->
      S.Step (cfg s f (map S.admininstr_val vs ++ [ :: S.CALL_ADDR a])) c' ->
      Step_exc (cfg s f (map S.admininstr_val vs ++ [ :: S.CALL_ADDR a])) c'
  (* SpecTec may fail table.grow and memory.grow when WasmCert would grow *)
  | exc_table_grow_fail s f r n x m :
      S.fun_inv_signed_ 32%num (-1)%Z m ->
      growtable (tr_tableinst (S.fun_table (S.mk_state s f) x)) n (tr_ref r) <> None ->
      Step_exc (cfg s f [ :: S.admininstr_ref r; i32c n; S.admininstr_TABLE_GROW x])
               (cfg s f [ :: i32c m])
  | exc_memory_grow_fail s f n m :
      S.fun_inv_signed_ 32%num (-1)%Z m ->
      mem_grow (tr_meminst (S.fun_mem (S.mk_state s f) (S.mk_uN 0))) n <> None ->
      Step_exc (cfg s f [ :: i32c n; S.admininstr_MEMORY_GROW]) (cfg s f [ :: i32c m])
  (* the above, in SpecTec's evaluation contexts *)
  | exc_label z n ins es z' es' :
      Step_exc (S.mk_config z es) (S.mk_config z' es') ->
      Step_exc (S.mk_config z [ :: S.LABEL_ n ins es]) (S.mk_config z' [ :: S.LABEL_ n ins es'])
  | exc_frame s f n f' es s' f'' es' :
      Step_exc (cfg s f' es) (cfg s' f'' es') ->
      Step_exc (cfg s f [ :: S.FRAME_ n f' es]) (cfg s' f [ :: S.FRAME_ n f'' es'])
  | exc_instrs z vs es es1 z' es' :
      Step_exc (S.mk_config z es) (S.mk_config z' es') ->
      Step_exc (S.mk_config z (map S.admininstr_val vs ++ es ++ es1))
               (S.mk_config z' (map S.admininstr_val vs ++ es' ++ es1)).

(** * Side conditions guaranteed by typing

   The index, table-entry and memory side conditions of [ok_redex] follow from
   SpecTec's typing.  This part works with SpecTec's names unqualified. *)

From WasmSpectec Require Import helper_lemmas helper_tactics subtyping typing_lemmas extension_lemmas.
Import datatypes operations opsem properties.

Module TypedFacts.
Import WasmSpectec.wasm.

(** * Typing invariant

   The invariant [t_preservation_type] works with: the instructions are typed
   in a context [C'] that agrees with the frame's module context [C] on
   everything but locals, labels and return, and the locals match [C']. *)

Definition Inv (s : store) (f : frame) (es : seq admininstr) : Prop :=
  exists C C' t1 t2,
    Store_ok s /\ Moduleinst_ok s (frame_MODULE f) C /\
    Vals_ok s (LOCALS f) (context_LOCALS C') /\ inst_match C C' /\
    Instrs_ok2 s C' es (t1 :-> t2).

Lemma moduleinst_locals s mi C : Moduleinst_ok s mi C -> context_LOCALS C = [ ::].
Proof. by case. Qed.

Lemma ctx_locals_app (C1 C2 : context) :
  context_LOCALS (C1 @@ C2) = context_LOCALS C1 ++ context_LOCALS C2.
Proof. by []. Qed.

(* Prepending locals, labels or a return type keeps the module part. *)
Lemma inst_match_prepend C (C1 C2 : context) :
  context_TYPES C1 = [ ::] -> context_FUNCS C1 = [ ::] -> context_GLOBALS C1 = [ ::] ->
  context_TABLES C1 = [ ::] -> context_MEMS C1 = [ ::] -> context_ELEMS C1 = [ ::] ->
  context_DATAS C1 = [ ::] -> inst_match C C2 -> inst_match C (C1 @@ C2).
Proof.
  case: C1 => /= ? ? ? ? ? ? ? ? ? ? -> -> -> -> -> -> ->.
  by case=> [? [? [? [? [? [? ?]]]]]]; rewrite /inst_match /=; repeat split.
Qed.

Lemma inst_match_refl C : inst_match C C.
Proof. by rewrite /inst_match; repeat split. Qed.

Lemma frame_inv s f C' :
  Frame_ok s f C' ->
  exists C, Moduleinst_ok s (frame_MODULE f) C /\
            Vals_ok s (LOCALS f) (context_LOCALS C') /\ inst_match C C'.
Proof.
  case=> {s f C'} s vs mi ts C Hmi _ Hvals _ _ _ _.
  exists C. split => //. split.
  - by rewrite ctx_locals_app (moduleinst_locals Hmi) cats0.
  - exact: inst_match_prepend (inst_match_refl C).
Qed.

(** * Side conditions guaranteed by typing *)

Lemma Forall2_lookup {A B : Type} {_ : Inhabited A} {_ : Inhabited B} (R : A -> B -> Prop) l l' i :
  List.Forall2 R l l' -> (i <? |l'|)%N -> R (lookup_total l i) (lookup_total l' i).
Proof. by move=> H /N.ltb_lt Hi; apply: (Forall2_size2 _ _ _ H). Qed.

Lemma Forall_lookup {A : Type} {_ : Inhabited A} (P : A -> Prop) l i :
  List.Forall P l -> (i <? |l|)%N -> P (lookup_total l i).
Proof.
  move=> HF Hi. have H2 : List.Forall2 (fun a (_ : A) => P a) l l.
  { by elim: HF => *; constructor. }
  exact: (Forall2_lookup H2 Hi).
Qed.

(* An index valid in the context is valid in the module instance and its
   address is valid in the store. *)
Lemma addr_okb_Forall2 {B : Type} {_ : Inhabited B} (R : N -> B -> Prop) idxs (cts : seq B) len x :
  List.Forall2 R idxs cts -> (forall a t, R a t -> (a < N.of_nat len)%num) ->
  (x <? |cts|)%N -> addr_okb idxs len x.
Proof.
  move=> H HR Hx. rewrite /addr_okb (Forall2_seq_size _ _ _ H) Hx /=.
  apply/N.ltb_lt. exact: HR (Forall2_lookup H Hx).
Qed.

Lemma addr_okb_Forall {B : Type} (P : N -> Prop) idxs (cts : seq B) len x :
  |idxs| = |cts| -> List.Forall P idxs -> (forall a, P a -> (a < N.of_nat len)%num) ->
  (x <? |cts|)%N -> addr_okb idxs len x.
Proof.
  move=> Hsz H HP Hx. rewrite /addr_okb Hsz Hx /=.
  apply/N.ltb_lt. apply: HP. apply: Forall_lookup H _. by rewrite Hsz.
Qed.

Lemma externaddr_func_bound s a xt :
  Externaddr_ok s (externaddr_FUNC a) xt -> (a <? |store_FUNCS s|)%N.
Proof.
  move=> H. remember (externaddr_FUNC a) as e eqn:Ee.
  induction H; try discriminate; auto. by injection Ee as <-.
Qed.

Section Typed.

Variables (s : store) (f : frame) (C C' : context).
Hypotheses (Hs : Store_ok s) (Hmi : Moduleinst_ok s (frame_MODULE f) C)
  (Hvals : Vals_ok s (LOCALS f) (context_LOCALS C')) (Hm : inst_match C C').
Let mi := frame_MODULE f.

Lemma local_typed x : (x <? |context_LOCALS C'|)%N -> N.ltb x (N.of_nat (size (LOCALS f))).
Proof. by rewrite -(Forall2_seq_size _ _ _ Hvals). Qed.

Lemma type_typed x : (x <? |context_TYPES C'|)%N -> N.ltb x (N.of_nat (size (TYPES mi))).
Proof. by rewrite (minst_invert_functypes _ _ _ _ Hmi Hm). Qed.

Lemma glob_typed x :
  (x <? |context_GLOBALS C'|)%N -> addr_okb (GLOBALS mi) (size (store_GLOBALS s)) x.
Proof.
  apply: (addr_okb_Forall2 (minst_invert_globals _ _ _ _ Hmi Hm)).
  by move=> a t [? [? [? _]]].
Qed.

Lemma tab_typed x :
  (x <? |context_TABLES C'|)%N -> addr_okb (TABLES mi) (size (store_TABLES s)) x.
Proof.
  apply: (addr_okb_Forall2 (minst_invert_tables _ _ _ _ Hmi Hm)).
  by move=> a t [? [? [? _]]].
Qed.

Lemma elem_typed x :
  (x <? |context_ELEMS C'|)%N -> addr_okb (ELEMS mi) (size (store_ELEMS s)) x.
Proof.
  apply: (addr_okb_Forall2 (minst_invert_elems _ _ _ _ Hmi Hm)).
  by move=> a t [? [? _]].
Qed.

Lemma data_typed x :
  (x <? |context_DATAS C'|)%N -> addr_okb (DATAS mi) (size (store_DATAS s)) x.
Proof.
  case: (minst_invert_datas _ _ _ _ Hmi Hm) => Hsz H.
  apply: (addr_okb_Forall _ H) => //. by move=> a [? [? _]].
Qed.

Lemma funcref_typed r : Ref_ok s r FUNCREF -> funcref_okb s r.
Proof.
  move Ert: FUNCREF => rt H. case: H Ert => //= s' a ext Ha _ _ _.
  exact: externaddr_func_bound Ha.
Qed.

(* A table of type funcref only holds null or valid function references. *)
Lemma table_refs_typed x lim :
  (x <? |context_TABLES C'|)%N ->
  lookup_total (context_TABLES C') x = mk_tabletype lim FUNCREF ->
  forall n, (n <? |REFS (fun_table (mk_state s f) (mk_uN x))|)%N ->
  funcref_okb s (lookup_total (REFS (fun_table (mk_state s f) (mk_uN x))) n).
Proof.
  move=> Hx Ht n Hn. apply: funcref_typed.
  case: (Forall2_lookup (minst_invert_tables _ _ _ _ Hmi Hm) Hx) => refs [tbt' [Ha [Etab Hsub]]].
  have Ha' : (lookup_total (TABLES mi) x <? |store_TABLES s|)%N by apply/N.ltb_lt.
  case: (s_invert_tables _ Hs) => tbts Htabs.
  have Ha'' : (lookup_total (TABLES mi) x <? |tbts|)%N by rewrite -(Forall2_seq_size _ _ _ Htabs).
  case: (Forall2_lookup Htabs Ha'') => refs' [m [rt [Etb [Etbt [_ Hrefs]]]]].
  rewrite Etab in Etb. case: Etb => Etyp Erefs. rewrite Ht Etyp Etbt in Hsub.
  inversion Hsub as [ | | tt1 tt2 Hts | ]; subst. inversion Hts; subst.
  move: Hn. rewrite /fun_table /= Etab /= => Hn. exact: Forall_lookup Hrefs Hn.
Qed.

Lemma mem_typed :
  (0 <? |context_MEMS C'|)%N -> addr_okb (MEMS mi) (size (store_MEMS s)) 0.
Proof.
  apply: (addr_okb_Forall2 (minst_invert_mems _ _ _ _ Hmi Hm)).
  by move=> a t [? [? [? _]]].
Qed.

(* Memories in a well-typed store are whole numbers of pages. *)
Lemma pages_typed :
  (0 <? |context_MEMS C'|)%N ->
  N.eqb (N.modulo (N.of_nat (size (BYTES (lookup_total (store_MEMS s) (lookup_total (MEMS mi) 0))))) 65536) 0.
Proof.
  move=> H0. move/andP: (mem_typed H0) => [_ Ha]. have Hs' := Hs.
  inversion Hs' as [s0 gl gt ml mt tl tt fl ft dl dt el et Hgs Hg Hms Hmems Hts Ht Hfs Hf
                    Hds Hd Hes He Es Hwf Hmt].
  move/eqP: Es => Es. rewrite Es /= in Ha *.
  have Ha' : (lookup_total (MEMS mi) 0 <? |mt|)%N by rewrite -(eqP Hms).
  have Hmo : Meminst_ok s (lookup_total ml (lookup_total (MEMS mi) 0))
                          (lookup_total mt (lookup_total (MEMS mi) 0))
    by apply: Forall2_lookup Hmems Ha'.
  move: Hmo. case E: (lookup_total ml (lookup_total (MEMS mi) 0)) => [ty b] Hmo.
  inversion Hmo as [s1 n0 m0 b0 Hmt0 Hb]; subst. move/eqP: Hb => /= ->.
  apply/eqP. rewrite /S.Ki. change (64 * 1024)%num with 65536%num. by rewrite N.Div0.mod_mul.
Qed.

End Typed.

(* The filled value of a typed table.fill is a reference. *)
Lemma memory_fill_operand s C' v c t1 t2 :
  Instrs_ok2 s C' [ :: admininstr_val v; admininstr_val c; admininstr_MEMORY_FILL] (t1 :-> t2) ->
  is_i32_admin (admininstr_val v).
Proof.
  move=> HType. repeat rewrite -(cat1s _ (_ :: _)) in HType.
  typing_inversion HType. rename Hai into Haifinal. rename Hsub into Hsubfinal.
  typing_inversion H1. rename Hsub into Hsubv.
  typing_inversion H0. rename Hsub into Hsubc.
  simpl in Haifinal; extract_premise.
  rewrite -(cats0 [ :: t]) in Hsubv.
  have Hvc := instrtype_sub_compose2 _ _ _ _ _ _ _ Hsubv Hsubc. rewrite /= in Hvc.
  have [_ Hts] := instrtype_sub_compose_le [ ::] [ :: t; t0]
    [ :: valtype_I32; valtype_I32] [ :: valtype_I32] [ ::] _ _ _ Hvc Hsubfinal erefl.
  case/resulttype_sub_cons: Hts => Ht _.
  have Et := valtype_sub_non_bot _ _ Ht (Val_ok_non_bot _ _ _ HValok). subst t. clear -HValok.
  case: v HValok => [nt w | vt w | rt | a | a] /= H; inversion H; subst.
  all: try by match goal with E : val_ref ?r = _ |- _ => destruct r end.
  - case: nt H H3 H5 => // _ _ H5. inversion H5; subst.
    match goal with Hw : S.wf_num_ S.I32 w |- _ => by have [m [-> _]] := wf_num_I32 Hw end.
  - by case: vt H H3 H5.
  - by case: rt0 H1 H3.
  - by case: rt H1 H3.
  - by case: rt H1 H3.
Qed.

Lemma table_fill_operand s C' v c x t1 t2 :
  Instrs_ok2 s C' [ :: admininstr_val v; admininstr_val c; admininstr_TABLE_FILL x] (t1 :-> t2) ->
  is_ref_admin (admininstr_val v).
Proof.
  move=> HType. repeat rewrite -(cat1s _ (_ :: _)) in HType.
  typing_inversion HType. rename Hai into Haifinal. rename Hsub into Hsubfinal.
  typing_inversion H1. rename Hsub into Hsubv.
  typing_inversion H0. rename Hsub into Hsubc.
  simpl in Haifinal; extract_premise.
  rewrite -(cats0 [ :: t]) in Hsubv.
  have Hvc := instrtype_sub_compose2 _ _ _ _ _ _ _ Hsubv Hsubc. rewrite /= in Hvc.
  have [_ Hts] := instrtype_sub_compose_le [ ::] [ :: t; t0]
    [ :: valtype_reftype extr; valtype_I32] [ :: valtype_I32] [ ::] _ _ _ Hvc Hsubfinal erefl.
  case/resulttype_sub_cons: Hts => Ht _.
  have Et := valtype_sub_non_bot _ _ Ht (Val_ok_non_bot _ _ _ HValok). subst t.
  case: v HValok => //=; move=> ty w H; inversion H; subst.
  all: first [ destruct r; simpl in *; discriminate | destruct extr, ty; simpl in *; discriminate ].
Qed.

(** * The typed side conditions *)

(* What remains of [ok_redex] once typing is known: the redex is not a memory
   or vector instruction, and a called function has no v128 locals. *)
Definition covered (z : state) (es : seq admininstr) : bool :=
  match z with
  | mk_state s _ =>
    match rev es with
    | CALL_ADDR a :: _ => callee_okb s a
    | a :: _ => ~~ is_mem_admin a && ~~ is_vec_admin a
    | [ ::] => true
    end
  end.

Lemma val_admin_val a : is_val_admin a -> exists v, a = admininstr_val v.
Proof.
  case: a => //=.
  - by move=> nt c _; exists (val_CONST nt c).
  - by move=> vt c _; exists (val_VCONST vt c).
  - by move=> rt _; exists (val_REF_NULL rt).
  - by move=> a _; exists (val_REF_FUNC_ADDR a).
  - by move=> a _; exists (val_REF_HOST_ADDR a).
Qed.

Ltac flatten :=
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  end.

Lemma ok_redex_typed s f es :
  Inv s f es -> redex_shape es -> covered (mk_state s f) es -> ok_redex (mk_state s f) es.
Proof.
  case=> C [C' [t1 [t2 [Hs [Hmi [Hvals [Hm Hty]]]]]]].
  rewrite /redex_shape /covered /ok_redex.
  case E: (rev es) => [ |a rest] //.
  have Ees : es = rev rest ++ [ :: a] by rewrite -[es]revK E rev_cons cats1.
  clear E.
  rewrite Ees in Hty.
  case/ais_composition_typing: (Hty) => t3 [_ /ais_single_typing_inversion [t1' [t2' [Hpt _]]]].
  case/andP => Hvs _.
  case: a Hpt Ees Hty => //=; intros; flatten.
  all: try (rewrite (local_typed Hvals); done).
  all: try (rewrite (glob_typed Hmi Hm); done).
  all: try (rewrite (elem_typed Hmi Hm); done).
  all: try (rewrite (data_typed Hmi Hm); done).
  all: try (rewrite (tab_typed Hmi Hm) ?(elem_typed Hmi Hm) ?(tab_typed Hmi Hm); done).
  all: try (match goal with H : Blocktype_ok _ _ _ |- _ =>
              inversion H; subst; simpl; first [ done | rewrite (type_typed Hmi Hm); done ] end).
  all: try (rewrite (mem_typed Hmi Hm) ?(pages_typed Hs Hmi Hvals Hm) ?(data_typed Hmi Hm); done).
  - (* call_indirect: every entry of a funcref table is a valid reference *)
    case: rest Hvs {Ees Hty} => [ |b rest] //= _.
    case: b => //= nt [inn [n] | ? ?] //=.
    rewrite (tab_typed Hmi Hm) // (type_typed Hmi Hm) //=.
    case: ifP => // Hn. exact: (table_refs_typed Hs Hmi Hm H1 H2 Hn).
  - (* table.fill: the fill value is a reference *)
    case: rest Hvs Ees Hty => [ |c [ |v rest]] //= /and3P [Hc Hv _] _ Hty.
    rewrite (tab_typed Hmi Hm) //=.
    case/val_admin_val: Hv => vv Ev. case/val_admin_val: Hc => cv Ec. subst.
    move: Hty. rewrite !rev_cons -!cats1 -!catA /=.
    by case/ais_composition_typing => t4 [_ /table_fill_operand].
  - (* memory.fill: the fill value is an i32 *)
    case: rest Hvs Ees Hty => [ |c [ |v rest]] //= /and3P [Hc Hv _] _ Hty.
    rewrite (mem_typed Hmi Hm) //=.
    case/val_admin_val: Hv => vv Ev. case/val_admin_val: Hc => cv Ec. subst.
    move: Hty. rewrite !rev_cons -!cats1 -!catA /=.
    by case/ais_composition_typing => t4 [_ /memory_fill_operand].
Qed.

Lemma redex_shape_vals vs a :
  redex_shape (map admininstr_val vs ++ [ :: a]) = ~~ is_val_admin a.
Proof.
  rewrite /redex_shape rev_cat /= all_rev.
  have -> : all is_val_admin (map admininstr_val vs) by apply/allP => _ /mapP [v _ ->]; case: v.
  by [].
Qed.

Lemma Step_read_shape z es es' : Step_read (mk_config z es) es' -> redex_shape es.
Proof.
  move=> H. inversion H; subst.
  all: try (rewrite /redex_shape /= ?val_admin_is_val ?ref_admin_is_val //; done).
  all: by rewrite redex_shape_vals.
Qed.

Lemma covered_false s f es :
  Inv s f es -> redex_shape es -> ok_redex (mk_state s f) es = false ->
  covered (mk_state s f) es = false.
Proof.
  move=> Hinv Hsh Hok. apply/negbTE/negP => Hcov.
  by rewrite (ok_redex_typed Hinv Hsh Hcov) in Hok.
Qed.

Lemma all_vals l : all is_val_admin l -> exists vs, l = map admininstr_val vs.
Proof.
  elim: l => [ |b l IH] /=; first by exists [ ::].
  case/andP => /val_admin_val [v ->] /IH [vs ->]. by exists (v :: vs).
Qed.

Lemma redex_vals es : redex_shape es -> exists vs a, es = map admininstr_val vs ++ [ :: a].
Proof.
  rewrite /redex_shape. case E: (rev es) => [ |a rest] // /andP [/all_vals [vs Ers] _].
  exists (rev vs), a. by rewrite -[es]revK E Ers rev_cons -cats1 map_rev.
Qed.

(* A step on a redex that is not covered is one of the named exceptions. *)
Lemma uncovered_exc z es c' :
  Step (mk_config z es) c' -> redex_shape es -> covered z es = false ->
  Step_exc (mk_config z es) c'.
Proof.
  move=> Hst /redex_vals [vs [a Ees]]. subst es. case: z Hst => s f Hst.
  rewrite /covered rev_cat /=. case: a Hst => //= *.
  all: first [ by apply: exc_load | by apply: exc_store | by apply: exc_vector
             | apply: exc_call_v128 => //;
               match goal with H : callee_okb _ _ = false |- _ => by rewrite /has_v128_local H end ].
Qed.

End TypedFacts.
Import TypedFacts.

(** * Eventual simulation *)

From mathcomp Require Import ssrnat.
Import datatypes operations opsem properties.

(** * Typing facts for breaks and returns *)

(* The typing invariant [Inv] with its contexts made explicit. *)
Definition InvX (s : S.store) (f : S.frame) (es : seq S.admininstr) (C C' : S.context) : Prop :=
  exists t1 t2,
    S.Store_ok s /\ S.Moduleinst_ok s (S.frame_MODULE f) C /\
    Vals_ok s (S.LOCALS f) (S.context_LOCALS C') /\ inst_match C C' /\
    S.Instrs_ok2 s C' es (t1 :-> t2).

Lemma InvX_Inv s f es C C' : InvX s f es C C' -> Inv s f es.
Proof. case=> t1 [t2 H]. by exists C, C', t1, t2. Qed.

(* The operands of a typed redex in a block body come from that body. *)
Lemma redex_operands s C vs a es t' :
  S.Instrs_ok2 s C (map S.admininstr_val vs ++ [ :: a] ++ es) ([ ::] :-> t') ->
  exists ta tb, ai_principal_typing s C a (ta :-> tb) /\ size ta <= size vs.
Proof.
  case/ais_composition_typing => t3 [Hvs /ais_composition_typing [t4 [Ha _]]].
  case/ais_vals_typing_inversion: Hvs => ts [Hsub Hvals].
  case/ais_single_typing_inversion: Ha => ta [tb [Hpt Hsub']].
  exists ta, tb. split => //. move: Hsub Hsub'. rewrite /instrtype_sub.
  have sz : forall x y, Resulttype_subtype x y -> size x = size y.
  { by move=> x y /resulttype_sub_size_eq /Nat2N.inj. }
  move=> [ts_sub [ts0 [ts11 [ts12 [E0 [-> [H1 [_ H3]]]]]]]] [a1 [a2 [a3 [a4 [E3 [_ [_ [H4 _]]]]]]]].
  case: ts_sub E0 H1 => // _ /resulttype_empty_sub E. subst ts0. rewrite /= in E3.
  rewrite -(sz _ _ H4) -(Nat2N.inj _ _ (Forall2_seq_size _ _ _ Hvals)) (sz _ _ H3) E3 size_cat.
  exact: leq_addl.
Qed.

(* A break leaving a label targets an enclosing label of the context, and the
   body holds enough values for it. *)
Lemma br_label_typed s C' n ins vs x es t1 t2 :
  S.Instrs_ok2 s C' [ :: S.LABEL_ n ins ((map S.admininstr_val vs
                         ++ [ :: S.admininstr_BR (S.mk_uN (x + 1))]) ++ es)] (t1 :-> t2) ->
  (x < N.of_nat (size (S.LABELS C')))%num /\
  size (S.proj_list_0 _ (lookup_total (S.LABELS C') x)) <= size vs.
Proof.
  move/ais_single_typing_inversion => [? [? [/= [t [t' [_ [_ [Hb _]]]]] _]]].
  rewrite -catA in Hb.
  case/redex_operands: Hb => ta [tb [/= [t0 [t'' [tl [Eft [Hlt Elab]]]]] Hle]].
  case: Eft => Eta _. subst ta. rewrite (lookup_label_1 C' t x) in Elab. split.
  - move/N.ltb_lt: Hlt. change (N.pos (Pos.of_succ_nat ?m)) with (N.of_nat m.+1).
    rewrite Nat2N.inj_succ. lia.
  - rewrite Elab. apply: leq_trans Hle. rewrite size_cat. exact: leq_addl.
Qed.

(* A return leaving a label is typed by the return type of the context. *)
Lemma return_label_typed s C' n ins vs es t1 t2 :
  S.Instrs_ok2 s C' [ :: S.LABEL_ n ins ((map S.admininstr_val vs
                         ++ [ :: S.admininstr_RETURN]) ++ es)] (t1 :-> t2) ->
  exists t, S.context_RETURN C' = Some (S.mk_list _ t) /\ size t <= size vs.
Proof.
  move/ais_single_typing_inversion => [? [? [/= [t [t' [_ [_ [Hb _]]]]] _]]].
  rewrite -catA in Hb.
  case/redex_operands: Hb => ta [tb [/= [t0 [t'' [tl [Eft [Eret _]]]]] Hle]].
  case: Eft => Eta _. subst ta. exists tl. split => //.
  apply: leq_trans Hle. rewrite size_cat. exact: leq_addl.
Qed.

Lemma moduleinst_ctx s mi C :
  S.Moduleinst_ok s mi C -> S.LABELS C = [ ::] /\ S.context_RETURN C = None.
Proof. by case. Qed.

Lemma frame_ctx s f C :
  S.Frame_ok s f C -> S.LABELS C = [ ::] /\ S.context_RETURN C = None.
Proof. case=> {s f C} s vs mi ts C /moduleinst_ctx [HL HR] *. by rewrite /= HL HR. Qed.

Lemma InvX_label s f n ins es C C' :
  InvX s f [ :: S.LABEL_ n ins es] C C' ->
  exists t, InvX s f es C (prepend_label C' t) /\ n = N.of_nat (size t).
Proof.
  case=> t1 [t2 [Hs [Hmi [Hvals [Hm Hty]]]]].
  move/ais_single_typing_inversion: Hty => [t1' [t2' [/= [t [t' [_ [_ [Hes En]]]]] _]]].
  exists t. split => //. exists [ ::], t'. by do 2 (split => //).
Qed.

Lemma InvX_frame s f n f' es C C' :
  InvX s f [ :: S.FRAME_ n f' es] C C' ->
  exists C0 C'' t, InvX s f' es C0 C'' /\ S.LABELS C'' = [ ::] /\
    S.context_RETURN C'' = Some (S.mk_list _ t) /\ n = N.of_nat (size t).
Proof.
  case=> t1 [t2 [Hs [Hmi [Hvals [Hm Hty]]]]].
  move/ais_single_typing_inversion: Hty => [t1' [t2' [/= [t [C'' [_ [Hf [Hexpr En]]]]] _]]].
  case: (frame_inv Hf) => C0 [Hmi' [Hvals' Hm']].
  case: (frame_ctx Hf) => HL HR.
  inversion Hexpr as [s2 C2 es2 ts2 Hes _ _ _]; subst.
  exists C0, (prepend_return C'' t), t. split; last by rewrite /= HL HR.
  exists [ ::], t. by do 2 (split => //).
Qed.

Lemma InvX_instrs s f vs es es1 C C' :
  InvX s f (map S.admininstr_val vs ++ es ++ es1) C C' -> InvX s f es C C'.
Proof.
  case=> t1 [t2 [Hs [Hmi [Hvals [Hm Hty]]]]].
  move/ais_composition_typing: Hty => [t3 [_ /ais_composition_typing [t4 [Hes _]]]].
  by exists t3, t4.
Qed.

Lemma config_InvX s f es ts :
  S.Config_ok (S.mk_config (S.mk_state s f) es) ts ->
  exists C C', InvX s f es C C' /\ S.LABELS C' = [ ::] /\ S.context_RETURN C' = None.
Proof.
  move=> H. inversion H as [s0 f0 es0 ts0 C Hst Hexpr _ _ _]; subst.
  inversion Hst as [s1 f1 C1 Hs Hf _ _]; subst.
  inversion Hexpr as [s2 C2 es2 ts2 Hes _ _ _]; subst.
  case: (frame_inv Hf) => C0 [Hmi [Hvals Hm]].
  exists C0, C. split; last exact: frame_ctx Hf.
  by exists [ ::], ts0.
Qed.

(** * WasmCert label contexts *)

(* Values pushed right before the hole. *)
Fixpoint lh_push {k} (lh : lholed k) (extra : seq value) : lholed k :=
  match lh in lholed k return lholed k with
  | LH_base vs es => LH_base (vs ++ extra) es
  | LH_rec _ vs n es' lh' es'' => LH_rec vs n es' (lh_push lh' extra) es''
  end.

Lemma lfill_push k (lh : lholed k) extra es :
  lfill (lh_push lh extra) es = lfill lh (v_to_e_list extra ++ es).
Proof.
  elim: lh => [vs es' | k' vs n es' lh IH es''] /=.
  - by rewrite /v_to_e_list map_cat -!catA.
  - by rewrite IH.
Qed.

(* Values and instructions put around the outermost level. *)
Definition lh_wrap {k} (pre : seq value) (lh : lholed k) (post : seq administrative_instruction) :
    lholed k :=
  match lh in lholed k return lholed k with
  | LH_base vs es => LH_base (pre ++ vs) (es ++ post)
  | LH_rec _ vs n es' lh' es'' => LH_rec (pre ++ vs) n es' lh' (es'' ++ post)
  end.

Lemma lfill_wrap k (lh : lholed k) pre post es :
  lfill (lh_wrap pre lh post) es = v_to_e_list pre ++ lfill lh es ++ post.
Proof. case: lh => [vs es' | k' vs n es' lh es''] /=; by rewrite /v_to_e_list map_cat -!catA. Qed.

(** * Same-state SpecTec steps with well-formed intermediate configurations *)

Definition wf_es (es : seq S.admininstr) : Prop := List.Forall S.wf_admininstr es.

Inductive CSteps (z : S.state) : seq S.admininstr -> seq S.admininstr -> Prop :=
  | cs_refl es : CSteps z es es
  | cs_step es1 es2 es3 :
      S.Step (S.mk_config z es1) (S.mk_config z es2) -> wf_es es1 -> wf_es es2 ->
      CSteps z es2 es3 -> CSteps z es1 es3.

Lemma CSteps_trans z es1 es2 es3 : CSteps z es1 es2 -> CSteps z es2 es3 -> CSteps z es1 es3.
Proof.
  move=> H. elim: H es3 => [es | e1 e2 e3 Hst H1 H2 _ IH] es4 H4 //.
  exact: cs_step Hst H1 H2 (IH _ H4).
Qed.

Lemma CSteps_one z es es' :
  S.Step (S.mk_config z es) (S.mk_config z es') -> wf_es es -> wf_es es' -> CSteps z es es'.
Proof. move=> Hst H1 H2. exact: cs_step Hst H1 H2 (cs_refl _ _). Qed.

Lemma CSteps_Steps z es es' :
  CSteps z es es' -> S.wf_state z -> wf_es es -> wf_es es' ->
  S.Steps (S.mk_config z es) (S.mk_config z es').
Proof.
  elim=> [es0 | es1 es2 es3 Hst H1 H2 _ IH] Hz Hw Hw'.
  - by apply: S.Steps__refl; constructor.
  - apply: S.trans Hst (IH Hz H2 Hw') _ _ _; by constructor.
Qed.

Lemma CSteps_label z n ins es es' :
  CSteps z es es' -> S.wf_state z -> List.Forall S.wf_instr ins ->
  CSteps z [ :: S.LABEL_ n ins es] [ :: S.LABEL_ n ins es'].
Proof.
  move=> H Hz Hins. elim: H => [es0 | es1 es2 es3 Hst H1 H2 _ IH].
  - exact: cs_refl.
  - apply: cs_step IH; try by repeat constructor.
    apply: S.ctxt_label Hst _ _; by constructor.
Qed.

Lemma CSteps_frame s f n f' es es' :
  CSteps (S.mk_state s f') es es' -> S.wf_store s -> S.wf_frame f' ->
  CSteps (S.mk_state s f) [ :: S.FRAME_ n f' es] [ :: S.FRAME_ n f' es'].
Proof.
  move=> H Hs Hf. elim: H => [es0 | es1 es2 es3 Hst H1 H2 _ IH].
  - exact: cs_refl.
  - apply: cs_step IH; try by repeat constructor.
    apply: S.ctxt_frame Hst _ _; by repeat constructor.
Qed.

Lemma CSteps_instrs z vs es es1 es' :
  CSteps z es es' -> S.wf_state z -> wf_es (map S.admininstr_val vs) -> wf_es es1 ->
  CSteps z (map S.admininstr_val vs ++ es ++ es1) (map S.admininstr_val vs ++ es' ++ es1).
Proof.
  move=> H Hz Hvs Hes1.
  case E: ((vs != [ ::]) || (es1 != [ ::])); last first.
  { move/norP: E => [/negPn/eqP -> /negPn/eqP ->] /=. by rewrite !cats0. }
  elim: H => [es0 | ea eb ec Hst H1 H2 _ IH].
  - exact: cs_refl.
  - apply: cs_step IH; try by rewrite /wf_es !List.Forall_app.
    apply: S.ctxt_instrs Hst E _ _; by constructor.
Qed.

(** * Well-formedness of the intermediate configurations *)

Lemma wf_es_cat es1 es2 : wf_es (es1 ++ es2) <-> wf_es es1 /\ wf_es es2.
Proof. exact: List.Forall_app. Qed.

Lemma wf_br_pred l :
  S.wf_admininstr (S.admininstr_BR (S.mk_uN (N.of_nat l.+1))) ->
  S.wf_admininstr (S.admininstr_BR (S.mk_uN (N.of_nat l))).
Proof.
  move=> H. inversion H; subst. constructor.
  match goal with Hx : S.wf_uN _ _ |- _ => inversion Hx; subst end. constructor.
  match goal with Hi : is_true (_ && _) |- _ => move: Hi end.
  move=> /andP [_ /N.leb_le Hi]. apply/andP; split; first by apply/N.leb_le; lia.
  apply/N.leb_le. apply: N.le_trans Hi.
  change (N.pos (Pos.of_succ_nat l)) with (N.of_nat l.+1). rewrite Nat2N.inj_succ. lia.
Qed.

Lemma wf_cfg_inv z es : S.wf_config (S.mk_config z es) -> S.wf_state z /\ wf_es es.
Proof. by move=> H; inversion H. Qed.

Lemma wf_state_inv s f : S.wf_state (S.mk_state s f) -> S.wf_store s /\ S.wf_frame f.
Proof. by move=> H; inversion H. Qed.

Lemma wf_label_inv n ins es :
  S.wf_admininstr (S.LABEL_ n ins es) -> List.Forall S.wf_instr ins /\ wf_es es.
Proof. by move=> H; inversion H. Qed.

Lemma wf_frame_inv n f es : S.wf_admininstr (S.FRAME_ n f es) -> S.wf_frame f /\ wf_es es.
Proof. by move=> H; inversion H. Qed.

Lemma wf_one a : wf_es [ :: a] <-> S.wf_admininstr a.
Proof. split; [by move=> H; inversion H | by repeat constructor]. Qed.

Lemma wf_instrs ins : List.Forall S.wf_instr ins -> wf_es (map S.admininstr_instr ins).
Proof. elim=> //= i ins' Hi _ IH. constructor => //. exact/wf_admininstr_instr. Qed.

(** * Pending breaks and returns *)

(* SpecTec has moved [BR l] out of [k] labels; WasmCert, which has not moved,
   still has those labels, as [lh], around the break [BR (l + k)].  [vs_in] are
   the values beside the break in the innermost label: typing guarantees that
   the target label exists in [C'] and that they suffice for it. *)
Definition br_pending (C' : S.context) (es es' : seq S.admininstr) : Prop :=
  exists k (lh : lholed k) l vs_out vs_in rest,
    tr_admins es = lfill lh (v_to_e_list (map tr_val vs_in)
                             ++ [ :: AI_basic (BI_br (N.of_nat (l + k)))]) /\
    es' = map S.admininstr_val (vs_out ++ vs_in)
          ++ [ :: S.admininstr_BR (S.mk_uN (N.of_nat l))] ++ rest /\
    (N.of_nat l < N.of_nat (size (S.LABELS C')))%num /\
    size (S.proj_list_0 _ (lookup_total (S.LABELS C') (N.of_nat l))) <= size vs_in.

(* The same for a return, whose target is the enclosing frame. *)
Definition ret_pending (C' : S.context) (es es' : seq S.admininstr) : Prop :=
  exists k (lh : lholed k) vs_out vs_in rest t,
    tr_admins es = lfill lh (v_to_e_list (map tr_val vs_in) ++ [ :: AI_basic BI_return]) /\
    es' = map S.admininstr_val (vs_out ++ vs_in) ++ [ :: S.admininstr_RETURN] ++ rest /\
    S.context_RETURN C' = Some (S.mk_list _ t) /\ size t <= size vs_in.

(* The last [m] values, and the ones before them. *)
Lemma split_last (vs : seq S.val) m :
  m <= size vs -> vs = seq.take (size vs - m) vs ++ seq.drop (size vs - m) vs /\
                  size (seq.drop (size vs - m) vs) = m.
Proof. move=> Hm. by rewrite cat_take_drop size_drop subKn. Qed.

Section Eventually.

Context `{hfc : host_function_class} `{ho : @host hfc memory_tr}.

Lemma label_pending_br s f C' n ins (t : S.resulttype) es es'' :
  br_pending (prepend_label C' t) es es'' -> n = N.of_nat (size t) ->
  wf_es es'' -> S.wf_state (S.mk_state s f) -> List.Forall S.wf_instr ins ->
  exists es3, CSteps (S.mk_state s f) [ :: S.LABEL_ n ins es''] es3 /\ wf_es es3 /\
    (sim (cfg s f [ :: S.LABEL_ n ins es]) (cfg s f es3) \/
     br_pending C' [ :: S.LABEL_ n ins es] es3).
Proof.
  case: t => t.
  move=> [k [lh [l [vs_out [vs_in [rest [Etr [-> [Hl Hsz]]]]]]]]] En Hw Hz Hins.
  case: l Hl Hsz Etr Hw => [ | l] Hl Hsz Etr Hw.
  - (* the break targets this label: [br_zero] in SpecTec, [rs_br] in WasmCert *)
    rewrite (lookup_label_0 C' t) /= in Hsz.
    have [extra [vs_m [Evs Hm]]] : exists extra vs_m, vs_in = extra ++ vs_m /\ size vs_m = size t.
    { case: (split_last Hsz) => E1 E2.
      by exists (seq.take (size vs_in - size t) vs_in), (seq.drop (size vs_in - size t) vs_in). }
    subst vs_in.
    have Eb : map S.admininstr_val (vs_out ++ extra ++ vs_m)
                ++ [ :: S.admininstr_BR (S.mk_uN (N.of_nat 0))] ++ rest
            = ((map S.admininstr_val (vs_out ++ extra) ++ map S.admininstr_val vs_m)
                ++ [ :: S.admininstr_BR (S.mk_uN 0)]) ++ rest by rewrite !map_cat -!catA.
    move: Hw. rewrite Eb => Hw. case/wf_es_cat: (Hw) => /wf_es_cat [/wf_es_cat [_ Hwm] _] _.
    exists (map S.admininstr_val vs_m ++ map S.admininstr_instr ins). split; [ | split].
    + apply: CSteps_one.
      * apply: S.pure. apply: S.br_zero. apply/eqP. by rewrite En Hm.
      * by repeat constructor.
      * apply/wf_es_cat. split => //. exact: wf_instrs.
    + apply/wf_es_cat. split => //. exact: wf_instrs.
    + left. apply: simple_sim. rewrite tr_admins_cat tr_admins_vals tr_admins_instrs.
      change (tr_admins [ :: S.LABEL_ n ins es])
        with [ :: AI_label (N.to_nat n) (to_e_list (tr_instrs ins)) (tr_admins es)].
      rewrite Etr map_cat /v_to_e_list map_cat -catA -/v_to_e_list -lfill_push.
      eapply rs_br with (i := k) (lh := lh_push lh (map tr_val extra)).
      * exact: vals_const.
      * by rewrite length_vals Hm En Nat2N.id.
      * by [].
  - (* the break leaves this label too: [br_succ] *)
    have El : N.of_nat l.+1 = (N.of_nat l + 1)%num by rewrite Nat2N.inj_succ N.add_1_r.
    have Eb : map S.admininstr_val (vs_out ++ vs_in)
                ++ [ :: S.admininstr_BR (S.mk_uN (N.of_nat l.+1))] ++ rest
            = (map S.admininstr_val (vs_out ++ vs_in)
                ++ [ :: S.admininstr_BR (S.mk_uN (N.of_nat l + 1))]) ++ rest by rewrite El -catA.
    case/wf_es_cat: (Hw) => Hwv /wf_es_cat [/List.Forall_cons_iff [Hbr _] _].
    have Hw3 : wf_es (map S.admininstr_val (vs_out ++ vs_in)
                      ++ [ :: S.admininstr_BR (S.mk_uN (N.of_nat l))]).
    { apply/wf_es_cat. split => //. constructor => //. exact: wf_br_pred. }
    exists (map S.admininstr_val (vs_out ++ vs_in) ++ [ :: S.admininstr_BR (S.mk_uN (N.of_nat l))]).
    split; [ | split => //].
    + apply: CSteps_one => //.
      * rewrite Eb. apply: S.pure.
        exact: (S.br_succ n ins (vs_out ++ vs_in) (S.mk_uN (N.of_nat l)) rest).
      * by repeat constructor.
    + right. exists k.+1, (LH_rec [ ::] (N.to_nat n) (to_e_list (tr_instrs ins)) lh [ ::]).
      exists l, vs_out, vs_in, [ ::]. split; [ | split; [by rewrite cats0 | ]].
      * change (tr_admins [ :: S.LABEL_ n ins es])
          with [ :: AI_label (N.to_nat n) (to_e_list (tr_instrs ins)) (tr_admins es)].
        by rewrite /= Etr addSnnS.
      * rewrite El (lookup_label_1 C' t) in Hsz. split => //.
        move: Hl. rewrite /prepend_label /=.
        have E : forall m, N.pos (Pos.of_succ_nat m) = N.of_nat m.+1 by [].
        rewrite !E !Nat2N.inj_succ. lia.
Qed.

Lemma label_pending_ret s f C' n ins (t : S.resulttype) es es'' :
  ret_pending (prepend_label C' t) es es'' ->
  wf_es es'' -> S.wf_state (S.mk_state s f) -> List.Forall S.wf_instr ins ->
  exists es3, CSteps (S.mk_state s f) [ :: S.LABEL_ n ins es''] es3 /\ wf_es es3 /\
    ret_pending C' [ :: S.LABEL_ n ins es] es3.
Proof.
  move=> [k [lh [vs_out [vs_in [rest [t' [Etr [-> [Hret Hsz]]]]]]]]] Hw Hz Hins.
  case/wf_es_cat: (Hw) => Hwv /wf_es_cat [Hr _].
  have Hw3 : wf_es (map S.admininstr_val (vs_out ++ vs_in) ++ [ :: S.admininstr_RETURN])
    by apply/wf_es_cat.
  exists (map S.admininstr_val (vs_out ++ vs_in) ++ [ :: S.admininstr_RETURN]).
  split; [ | split => //].
  - apply: CSteps_one => //.
    + rewrite catA. apply: S.pure. exact: S.return_label.
    + by repeat constructor.
  - exists k.+1, (LH_rec [ ::] (N.to_nat n) (to_e_list (tr_instrs ins)) lh [ ::]).
    exists vs_out, vs_in, [ ::], t'. split; [ | split; [by rewrite cats0 | split => //]].
    change (tr_admins [ :: S.LABEL_ n ins es])
      with [ :: AI_label (N.to_nat n) (to_e_list (tr_instrs ins)) (tr_admins es)].
    by rewrite /= Etr.
Qed.

Lemma frame_pending_ret s f n f' C'' (t : seq valtype) es es'' :
  ret_pending C'' es es'' -> S.context_RETURN C'' = Some (S.mk_list _ t) ->
  n = N.of_nat (size t) -> wf_es es'' -> S.wf_store s -> S.wf_frame f -> S.wf_frame f' ->
  exists es3, CSteps (S.mk_state s f) [ :: S.FRAME_ n f' es''] es3 /\ wf_es es3 /\
    sim (cfg s f [ :: S.FRAME_ n f' es]) (cfg s f es3).
Proof.
  move=> [k [lh [vs_out [vs_in [rest [t' [Etr [-> [Hret Hsz]]]]]]]]] Ht En Hw Hs Hf Hf'.
  rewrite Ht in Hret. case: Hret => Et. subst t'.
  have [extra [vs_m [Evs Hm]]] : exists extra vs_m, vs_in = extra ++ vs_m /\ size vs_m = size t.
  { case: (split_last Hsz) => E1 E2.
    by exists (seq.take (size vs_in - size t) vs_in), (seq.drop (size vs_in - size t) vs_in). }
  subst vs_in.
  have Eb : map S.admininstr_val (vs_out ++ extra ++ vs_m) ++ [ :: S.admininstr_RETURN] ++ rest
          = ((map S.admininstr_val (vs_out ++ extra) ++ map S.admininstr_val vs_m)
              ++ [ :: S.admininstr_RETURN]) ++ rest by rewrite !map_cat -!catA.
  move: Hw. rewrite Eb => Hw. case/wf_es_cat: (Hw) => /wf_es_cat [/wf_es_cat [_ Hwm] _] _.
  exists (map S.admininstr_val vs_m). split; [ | split => //].
  - apply: CSteps_one => //.
    + apply: S.pure. apply: S.return_frame. apply/eqP. by rewrite En Hm.
    + by repeat constructor.
  - apply: simple_sim. rewrite tr_admins_vals.
    change (tr_admins [ :: S.FRAME_ n f' es])
      with [ :: AI_frame (N.to_nat n) (tr_frame f') (tr_admins es)].
    rewrite Etr map_cat /v_to_e_list map_cat -catA -/v_to_e_list -lfill_push.
    eapply rs_return with (lh := lh_push lh (map tr_val extra)).
    + exact: vals_const.
    + by rewrite length_vals Hm En Nat2N.id.
    + by [].
Qed.

(** * The relation is restored eventually *)

(* After the step [c -> c'], SpecTec eventually reaches (in [CSteps]) a
   configuration that is either simulated by WasmCert, or still has a break or
   return on its way out (which the enclosing labels and frames will
   resolve). *)
Definition eventually_sim (C' : S.context) (c c' : S.config) : Prop :=
  match c, c' with
  | S.mk_config z es, S.mk_config z' es' =>
      z' = z /\ wf_es es' /\
      exists es'', CSteps z es' es'' /\ wf_es es'' /\
        (sim c (S.mk_config z es'') \/ br_pending C' es es'' \/ ret_pending C' es es'')
  end.

Definition InvXc (c : S.config) (C C' : S.context) : Prop :=
  match c with S.mk_config (S.mk_state s f) es => InvX s f es C C' end.

(* Tactics of the [Reduction] section, which do not survive its end. *)
Ltac wf_split :=
  repeat match goal with
  | H : List.Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  | H : List.Forall _ (_ ++ _) |- _ => apply List.Forall_app in H as [? ?]
  end.
Ltac wf_get :=
  wf_split;
  repeat match goal with
  | H : S.wf_admininstr (S.admininstr_CONST _ _) |- _ => apply wf_admin_const in H
  | H : S.wf_admininstr (S.admininstr_UNOP _ _) |- _ => inversion H; subst; clear H
  | H : S.wf_admininstr (S.admininstr_BINOP _ _) |- _ => inversion H; subst; clear H
  | H : S.wf_admininstr (S.admininstr_TESTOP _ _) |- _ => inversion H; subst; clear H
  | H : S.wf_admininstr (S.admininstr_RELOP _ _) |- _ => inversion H; subst; clear H
  | H : S.wf_admininstr (S.admininstr_CVTOP _ _ _) |- _ => inversion H; subst; clear H
  end.
Ltac grab_i32 c nm Hnm :=
  match goal with H : S.wf_num_ S.I32 c |- _ => have [nm [? Hnm]] := wf_num_I32 H; subst c end.
Ltac grab_lit n Hnm :=
  match goal with H : S.wf_num_ S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN n)) |- _ =>
    have Hnm := wf_i32_lit H end.
Ltac norm :=
  cbn [S.coerce S.proj_uN_0_coercion S.proj_num__0 S.the S.proj_uN_0] in *;
  unfold S.N_gtb, S.N_geb in *.

(* An uncovered step on a plain redex: one of the named exceptions. *)
Ltac leaf_exc Hst Hinv :=
  right; right; apply: (uncovered_exc Hst);
  [ by rewrite /redex_shape /= ?val_admin_is_val ?ref_admin_is_val
  | apply: (covered_false (InvX_Inv Hinv));
    [ by rewrite /redex_shape /= ?val_admin_is_val ?ref_admin_is_val | assumption ] ].

Ltac excl_leaf :=
  intros;
  match goal with z : S.state |- _ => destruct z end;
  match goal with Hst : S.Step _ _ |- _ =>
    right; right; apply: (uncovered_exc Hst);
    [ by rewrite /redex_shape /= | by rewrite /covered /= ] end.

Lemma step_eventually c c' :
  S.Step c c' -> S.wf_config c -> forall C C', InvXc c C C' ->
  sim c c' \/ eventually_sim C' c c' \/ Step_exc c c'.
Proof.
  move=> H. move: (H). elim: H => {c c'}.
  - (* pure *)
    move=> [s f] es es' Hp _ Hwf C C' Hinv.
    case: (Step_pure_sim Hp (wf_cfg_instrs Hwf)) => [H | [H | H]].
    + left. exact: H.
    + right; right. exact: exc_pure.
    + (* a label exit starts a pending break or return *)
      right; left. case: H Hwf Hinv => [n ins vs x rest | n ins vs rest] Hwf Hinv.
        case: Hinv => t1 [t2 [_ [_ [_ [_ Hty]]]]].
        case: (br_label_typed Hty) => Hx Hsz.
        case/wf_cfg_inv: Hwf => Hz /wf_one /wf_label_inv [Hins Hb].
        move: Hb => /wf_es_cat [/wf_es_cat [Hwv Hbr] Hwr]. move/wf_one: Hbr => Hbr.
        have Ex : x = N.of_nat (N.to_nat x) by rewrite N2Nat.id.
        have Ex1 : (x + 1)%num = N.of_nat (N.to_nat x).+1 by rewrite Nat2N.inj_succ -Ex N.add_1_r.
        rewrite Ex1 in Hbr.
        have Hw' : wf_es (map S.admininstr_val vs ++ [ :: S.admininstr_BR (S.mk_uN x)]).
        { apply/wf_es_cat. split => //. apply/wf_one. rewrite Ex. exact: wf_br_pred. }
        split => //. split => //.
        exists (map S.admininstr_val vs ++ [ :: S.admininstr_BR (S.mk_uN x)]).
        split; first exact: cs_refl. split => //. right; left.
        exists 1, (LH_rec [ ::] (N.to_nat n) (to_e_list (tr_instrs ins))
                     (LH_base [ ::] (tr_admins rest)) [ ::]).
        exists (N.to_nat x), [ ::], vs, [ ::]. rewrite N2Nat.id cats0. split => //.
        change (tr_admins [ :: S.LABEL_ n ins ((map S.admininstr_val vs
                  ++ [ :: S.admininstr_BR (S.mk_uN (x + 1))]) ++ rest)])
          with [ :: AI_label (N.to_nat n) (to_e_list (tr_instrs ins))
                  (tr_admins ((map S.admininstr_val vs
                    ++ [ :: S.admininstr_BR (S.mk_uN (x + 1))]) ++ rest))].
        rewrite !tr_admins_cat tr_admins_vals Nat2N.inj_add N2Nat.id /= -catA.
        done.
        case: Hinv => t1 [t2 [_ [_ [_ [_ Hty]]]]].
        case: (return_label_typed Hty) => t [Hret Hsz].
        case/wf_cfg_inv: Hwf => Hz /wf_one /wf_label_inv [Hins Hb].
        move: Hb => /wf_es_cat [/wf_es_cat [Hwv Hr] Hwr].
        have Hw' : wf_es (map S.admininstr_val vs ++ [ :: S.admininstr_RETURN]) by apply/wf_es_cat.
        split => //. split => //.
        exists (map S.admininstr_val vs ++ [ :: S.admininstr_RETURN]).
        split; first exact: cs_refl. split => //. right; right.
        exists 1, (LH_rec [ ::] (N.to_nat n) (to_e_list (tr_instrs ins))
                     (LH_base [ ::] (tr_admins rest)) [ ::]).
        exists [ ::], vs, [ ::], t. rewrite cats0. split => //.
        change (tr_admins [ :: S.LABEL_ n ins ((map S.admininstr_val vs
                  ++ [ :: S.admininstr_RETURN]) ++ rest)])
          with [ :: AI_label (N.to_nat n) (to_e_list (tr_instrs ins))
                  (tr_admins ((map S.admininstr_val vs ++ [ :: S.admininstr_RETURN]) ++ rest))].
        rewrite !tr_admins_cat tr_admins_vals /= -catA.
        done.
  - (* read *)
    move=> [s f] es es' Hr _ Hwf C C' Hinv. case Hok: (ok_redex (S.mk_state s f) es).
    + left. exact: Step_read_sim.
    + right; right. have Hsh := Step_read_shape Hr.
      apply: (uncovered_exc (S.read _ _ _ Hr) Hsh). exact: covered_false (InvX_Inv Hinv) Hsh Hok.
  - (* ctxt_label *)
    move=> [s f] n ins es z' es' Hin IH Hw _ _ Hwf C C' Hinv.
    case: (InvX_label Hinv) => t [Hinv' En].
    case/wf_cfg_inv: (Hwf) => Hz /wf_one /wf_label_inv [Hins Hwes].
    case: (IH Hin Hw C (prepend_label C' t) Hinv') => [H | [H | H]].
    { left. exact: sim_label. }
    2: { right; right. exact: exc_label. }
    right; left. clear IH. case: z' Hin H => s' f' _. move=> [[-> ->] [Hw' [es'' [Hcs [Hw'' Hres]]]]].
    have HwL : forall b, wf_es b -> wf_es [ :: S.LABEL_ n ins b] by move=> b Hb; repeat constructor.
    split => //. split; first exact: HwL. 
    have Hcs' := CSteps_label n Hcs Hz Hins.
    case: Hres => [Hsim | [Hbr | Hret]].
    + exists [ :: S.LABEL_ n ins es'']. split; first exact: Hcs'. split; first exact: HwL.
      left. exact: sim_label.
    + case: (label_pending_br Hbr En Hw'' Hz Hins) => es3 [Hcs3 [Hw3 Hres3]].
      exists es3. split; first exact: CSteps_trans Hcs' Hcs3. split => //.
      by case: Hres3; [left | right; left].
    + case: (label_pending_ret n Hret Hw'' Hz Hins) => es3 [Hcs3 [Hw3 Hres3]].
      exists es3. split; first exact: CSteps_trans Hcs' Hcs3. by split => //; right; right.
  - (* ctxt_frame *)
    move=> s f n f' es s' f'' es' Hin IH Hw _ _ Hwf C C' Hinv.
    case: (InvX_frame Hinv) => C0 [C'' [t [Hinv' [HL [HR En]]]]].
    case/wf_cfg_inv: (Hwf) => /wf_state_inv [Hs Hf] /wf_one /wf_frame_inv [Hf' Hwes].
    case: (IH Hin Hw C0 C'' Hinv') => [H | [H | H]].
    { left. exact: sim_frame. }
    2: { right; right. exact: exc_frame. }
    right; left. clear IH Hin. move: H => [[-> ->] [Hw' [es'' [Hcs [Hw'' Hres]]]]].
    have HwF : forall b, wf_es b -> wf_es [ :: S.FRAME_ n f' b] by move=> b Hb; repeat constructor.
    split => //. split; first exact: HwF.
    have Hcs' := CSteps_frame f n Hcs Hs Hf'.
    case: Hres => [Hsim | [Hbr | Hret]].
    + exists [ :: S.FRAME_ n f' es'']. split; first exact: Hcs'. split; first exact: HwF.
      left. exact: sim_frame.
    + (* a break cannot leave a frame *)
      case: Hbr => [k [lh [l [vs_out [vs_in [rest [_ [_ [Hl _]]]]]]]]].
      by rewrite HL /= in Hl; lia.
    + case: (frame_pending_ret Hret HR En Hw'' Hs Hf Hf') => es3 [Hcs3 [Hw3 Hsim]].
      exists es3. split; first exact: CSteps_trans Hcs' Hcs3. by split => //; left.
  - (* ctxt_instrs *)
    move=> [s f] vs es es1 z' es' Hin IH _ Hw _ _ Hwf C C' Hinv.
    have Hinv' := InvX_instrs Hinv.
    case/wf_cfg_inv: (Hwf) => Hz /wf_es_cat [Hwvs /wf_es_cat [Hwes Hwes1]].
    case: (IH Hin Hw C C' Hinv') => [H | [H | H]].
    { left. exact: sim_instrs. }
    2: { right; right. exact: exc_instrs. }
    right; left. clear IH. case: z' Hin H => s' f' _. move=> [[-> ->] [Hw' [es'' [Hcs [Hw'' Hres]]]]].
    have HwI : forall b, wf_es b -> wf_es (map S.admininstr_val vs ++ b ++ es1).
    { move=> b Hb. apply/wf_es_cat. split => //. exact/wf_es_cat. }
    split => //. split; first exact: HwI.
    have Hcs' := CSteps_instrs Hcs Hz Hwvs Hwes1.
    exists (map S.admininstr_val vs ++ es'' ++ es1). split => //. split; first exact: HwI.
    case: Hres => [Hsim | [Hbr | Hret]].
    + left. exact: sim_instrs.
    + right; left.
      case: Hbr => [k [lh [l [vs_out [vs_in [rest [Etr [-> [Hl Hsz]]]]]]]]].
      exists k, (lh_wrap (map tr_val vs) lh (tr_admins es1)), l, (vs ++ vs_out), vs_in, (rest ++ es1).
      split; last by rewrite !map_cat -!catA.
      rewrite lfill_wrap -Etr !tr_admins_cat tr_admins_vals.
      done.
    + right; right.
      case: Hret => [k [lh [vs_out [vs_in [rest [t [Etr [-> Ht]]]]]]]].
      exists k, (lh_wrap (map tr_val vs) lh (tr_admins es1)), (vs ++ vs_out), vs_in, (rest ++ es1), t.
      split; last by rewrite !map_cat -!catA.
      rewrite lfill_wrap -Etr !tr_admins_cat tr_admins_vals.
      done.
  - (* local_set *)
    move=> [s f] v x Hst Hwf C C' Hinv.
    case Hok: (ok_redex (S.mk_state s f) [ :: S.admininstr_val v; S.admininstr_LOCAL_SET x]).
    + left. move: Hok; rewrite /ok_redex /= => /N.ltb_spec0 Hx. exact: sim_local_set.
    + leaf_exc Hst Hinv.
  - (* global_set *)
    move=> [s f] v x Hst Hwf C C' Hinv.
    case Hok: (ok_redex (S.mk_state s f) [ :: S.admininstr_val v; S.admininstr_GLOBAL_SET x]).
    + left. move: Hok; rewrite /ok_redex /= => /addr_okP Hx. exact: sim_global_set.
    + leaf_exc Hst Hinv.
  - (* table_set_trap *)
    move=> [s f] i r x H1 H2 Hst Hwf C C' Hinv.
    case Hok: (ok_redex (S.mk_state s f) [ :: S.admininstr_CONST S.I32 i; S.admininstr_ref r; S.admininstr_TABLE_SET x]).
    + left. move: Hok; rewrite /ok_redex /= => /addr_okP Hx.
      have Hw := wf_cfg_instrs Hwf. wf_get. grab_i32 i ni Hni. norm.
      have := @sim_table_set _ _ s f x ni r Hx Hni. by rewrite (leb_ltb_false H2).
    + leaf_exc Hst Hinv.
  - (* table_set_val *)
    move=> [s f] i r x H1 H2 Hst Hwf C C' Hinv.
    case Hok: (ok_redex (S.mk_state s f) [ :: S.admininstr_CONST S.I32 i; S.admininstr_ref r; S.admininstr_TABLE_SET x]).
    + left. move: Hok; rewrite /ok_redex /= => /addr_okP Hx.
      have Hw := wf_cfg_instrs Hwf. wf_get. grab_i32 i ni Hni. norm.
      have := @sim_table_set _ _ s f x ni r Hx Hni. by rewrite H2.
    + leaf_exc Hst Hinv.
  - (* table_grow_succeed *)
    move=> [s f] r n x ti v Hg Hv /eqP Hti Hst Hwf C C' Hinv.
    case: v Hg Hv Hti Hst => [ti'| ] //= Hg _ Hti Hst. subst ti'.
    case Hok: (ok_redex (S.mk_state s f) [ :: S.admininstr_ref r; i32c n; S.admininstr_TABLE_GROW x]).
    + left. move: Hok; rewrite /ok_redex /= => /addr_okP Hx.
      have Hw := wf_cfg_instrs Hwf. wf_get. grab_lit n Hn. exact: sim_table_grow.
    + leaf_exc Hst Hinv.
  - (* table_grow_fail *)
    move=> [s f] r n x m Hm Hst Hwf C C' Hinv.
    case Hok: (ok_redex (S.mk_state s f) [ :: S.admininstr_ref r; i32c n; S.admininstr_TABLE_GROW x]).
    + move: Hok; rewrite /ok_redex /= => /addr_okP Hx.
      have Hw := wf_cfg_instrs Hwf. wf_get. grab_lit n Hn.
      case Hg: (growtable (tr_tableinst (S.fun_table (S.mk_state s f) x)) n (tr_ref r)) => [t| ].
      * right; right. apply: exc_table_grow_fail => //. by rewrite Hg.
      * left. exact: sim_table_grow_fail.
    + leaf_exc Hst Hinv.
  - (* elem_drop *)
    move=> [s f] x Hst Hwf C C' Hinv.
    case Hok: (ok_redex (S.mk_state s f) [ :: S.admininstr_ELEM_DROP x]).
    + left. move: Hok; rewrite /ok_redex /= => /addr_okP Hx. exact: sim_elem_drop.
    + leaf_exc Hst Hinv.
  all: try (excl_leaf; fail).
  - (* memory_grow_succeed *)
    move=> [s f] n mi v Hg Hv /eqP Hmi _ Hst Hwf C C' Hinv.
    case: v Hg Hv Hmi Hst => [mi'| ] //= Hg _ Hmi Hst. subst mi'.
    case Hok: (ok_redex (S.mk_state s f) [ :: i32c n; S.admininstr_MEMORY_GROW]).
    + left. move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hm /N.eqb_spec Hp].
      have Hw := wf_cfg_instrs Hwf. wf_get. grab_lit n Hn.
      set b := N.of_nat (size (S.BYTES (S.fun_mem (S.mk_state s f) (S.mk_uN 0)))).
      have Hk : b = (b / 65536 * 65536)%num.
      { rewrite {1}(N.div_mod b 65536) // Hp. lia. }
      rewrite (page_count Hk). exact: sim_memory_grow Hm Hn Hk Hg.
    + leaf_exc Hst Hinv.
  - (* memory_grow_fail *)
    move=> [s f] n m Hm Hst Hwf C C' Hinv.
    case Hok: (ok_redex (S.mk_state s f) [ :: i32c n; S.admininstr_MEMORY_GROW]).
    + move: Hok; rewrite /ok_redex /= => /andP [/addr_okP Hmo _].
      have Hw := wf_cfg_instrs Hwf. wf_get. grab_lit n Hn.
      case Hg: (mem_grow (tr_meminst (S.fun_mem (S.mk_state s f) (S.mk_uN 0))) n) => [mm| ].
      * right; right. apply: exc_memory_grow_fail => //. by rewrite Hg.
      * left. exact: sim_memory_grow_fail.
    + leaf_exc Hst Hinv.
  (* data_drop *)
  move=> [s f] x Hst Hwf C C' Hinv.
  case Hok: (ok_redex (S.mk_state s f) [ :: S.admininstr_DATA_DROP x]).
  + left. move: Hok; rewrite /ok_redex /= => /addr_okP Hx. exact: sim_data_drop.
  + leaf_exc Hst Hinv.
Qed.

(** Every step of a well-typed configuration is simulated by WasmCert, either
    directly or eventually, except for the steps in [Step_exc].

    This is the "eventually" forward simulation diagram of CompCert
    ([Smallstep.forward_simulation_eventually]: "a forward simulation diagram
    where the first semantics can take some extra steps before reaching a
    state that restores the simulation relation"), with SpecTec as the first
    semantics; it is a form of stuttering simulation (Browne, Clarke and
    Grumberg, 1988), the extra SpecTec steps being matched by no WasmCert step.
    It differs from CompCert's in two ways: the restoring SpecTec run is
    existential ([S.Steps]) rather than over all silent runs of a given length,
    and no measure bounds the stuttering, so the theorem alone does not
    preserve divergence. *)
Theorem Step_sim_eventually c c' ts :
  S.Step c c' -> S.Config_ok c ts ->
  sim c c' \/ (exists c'', S.Steps c' c'' /\ sim c c'') \/ Step_exc c c'.
Proof.
  move=> Hst Hok. have Hwf : S.wf_config c by case: Hok.
  case: c Hst Hok Hwf => [[s f] es] Hst Hok Hwf.
  case: (config_InvX Hok) => C [C' [Hinv [HL HR]]].
  case: (step_eventually Hst Hwf Hinv) => [H | [H | H]]; [by left | | by right; right].
  case: c' Hst H => z' es' Hst [Ez [Hw' [es'' [Hcs [Hw'' Hres]]]]]. subst z'.
  case/wf_cfg_inv: Hwf => Hz _.
  case: Hres => [Hsim | [Hbr | Hret]].
  - right; left. exists (cfg s f es''). split => //. exact: CSteps_Steps.
  - (* no label encloses the configuration *)
    case: Hbr => [k [lh [l [? [? [? [_ [_ [Hl _]]]]]]]]]. by rewrite HL /= in Hl; lia.
  - (* nor a frame *)
    case: Hret => [k [lh [? [? [? [t [_ [_ [Hr _]]]]]]]]]. by rewrite HR in Hr.
Qed.

End Eventually.

(* Agreement axioms for the builtins of the SpecTec Wasm 2.0 numerics.

   wasm.v declares the numeric primitives of 3-numerics.spectec that the
   Rocq backend cannot define (iclz_, fadd_, trunc__, nbytes_, ...) as
   [Axiom]s: uninterpreted function symbols with no property at all.  To
   relate SpecTec's numeric steps to WasmCert's, we fix their meaning here,
   with one axiom per builtin:
   - most builtins are stated to agree with the WasmCert operation that
     implements them, through the translation ([tr_num]);
   - [wrap__], [extend__] and [truncz] are given their definition in the
     specification, since they are used at many widths.

   Each axiom constrains a single uninterpreted symbol of wasm.v, and only at
   well-formed arguments of the widths it mentions; the axioms are satisfied
   by taking each symbol to be the WasmCert operation composed with the
   back-translation (backtranslation.v), so they are consistent.  They do
   fix SpecTec's NaN nondeterminism to WasmCert's choice of NaN. *)

From Stdlib Require Import NArith ZArith QArith Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
(* Imported (before WasmCert, which shadows it) for its eqType instances. *)
From WasmSpectec Require Import wasm.
From Wasm Require Import numerics datatypes operations.
From WasmCertBridge Require Import translation.

From WasmSpectec Require wasm_funs.
Module S := WasmSpectec.wasm.
Module F := WasmSpectec.wasm_funs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope N_scope with num.

(** * Notations for the statements *)

(* An integer or float of SpecTec's number type [t], translated. *)
Definition ival (t : S.Inn) (i : S.uN) : value_num := tr_num (S.mk_num__0 t i).
Definition fval (t : S.Fnn) (x : S.fN) : value_num := tr_num (S.mk_num__1 t x).

(* Well-formed numbers of type [t]. *)
Definition iok (t : S.Inn) (i : S.uN) : Prop := S.wf_num_ (S.numtype_Inn t) (S.mk_num__0 t i).
Definition fok (t : S.Fnn) (x : S.fN) : Prop := S.wf_num_ (S.numtype_Fnn t) (S.mk_num__1 t x).

(* The bit width SpecTec passes to the builtins at type [t]. *)
Definition isz (t : S.Inn) : N := F.sizenn (S.numtype_Inn t).
Definition fsz (t : S.Fnn) : N := F.sizenn (S.numtype_Fnn t).

(* A partial WasmCert result, as the list of results SpecTec uses. *)
Definition olist {A : Type} (o : option A) : seq A :=
  match o with Some x => [:: x] | None => [::] end.

(** * Builtins given their specification definition *)

Axiom wrap__def : forall M N i,
  S.wrap__ M N i = S.mk_uN (N.modulo (S.proj_uN_0 i) (2 ^ N)).

Axiom extend__def : forall M N sx i,
  S.extend__ M N sx i =
  S.mk_uN (match sx with
           | S.U => S.proj_uN_0 i
           | S.res_S =>
               if (S.proj_uN_0 i <? 2 ^ (M - 1))%num then S.proj_uN_0 i
               else (S.proj_uN_0 i + 2 ^ N - 2 ^ M)%num
           end).

(* Truncation of a rational towards zero. *)
Axiom truncz_def : forall q, S.truncz q = Z.quot (Qnum q) (Zpos (Qden q)).

(** * Integer builtins *)

Axiom iclz_tr : forall t i, iok t i ->
  ival t (S.iclz_ (isz t) i) = app_unop (Unop_i UOI_clz) (ival t i).
Axiom ictz_tr : forall t i, iok t i ->
  ival t (S.ictz_ (isz t) i) = app_unop (Unop_i UOI_ctz) (ival t i).
Axiom ipopcnt_tr : forall t i, iok t i ->
  ival t (S.ipopcnt_ (isz t) i) = app_unop (Unop_i UOI_popcnt) (ival t i).

Axiom iand_tr : forall t i j, iok t i -> iok t j ->
  Some (ival t (S.iand_ (isz t) i j)) = app_binop (Binop_i BOI_and) (ival t i) (ival t j).
Axiom ior_tr : forall t i j, iok t i -> iok t j ->
  Some (ival t (S.ior_ (isz t) i j)) = app_binop (Binop_i BOI_or) (ival t i) (ival t j).
Axiom ixor_tr : forall t i j, iok t i -> iok t j ->
  Some (ival t (S.ixor_ (isz t) i j)) = app_binop (Binop_i BOI_xor) (ival t i) (ival t j).
Axiom ishl_tr : forall t i j, iok t i -> iok t j ->
  Some (ival t (S.ishl_ (isz t) i j)) = app_binop (Binop_i BOI_shl) (ival t i) (ival t j).
Axiom ishr_tr : forall t sx i j, iok t i -> iok t j ->
  Some (ival t (S.ishr_ (isz t) sx i j)) = app_binop (Binop_i (BOI_shr (tr_sx sx))) (ival t i) (ival t j).
Axiom irotl_tr : forall t i j, iok t i -> iok t j ->
  Some (ival t (S.irotl_ (isz t) i j)) = app_binop (Binop_i BOI_rotl) (ival t i) (ival t j).
Axiom irotr_tr : forall t i j, iok t i -> iok t j ->
  Some (ival t (S.irotr_ (isz t) i j)) = app_binop (Binop_i BOI_rotr) (ival t i) (ival t j).

(** * Float builtins

   SpecTec's float operations return the list of their possible results; the
   axioms say that it is exactly WasmCert's result. *)

Axiom fabs_tr : forall t x, fok t x ->
  map (fval t) (S.fabs_ (fsz t) x) = [:: app_unop (Unop_f UOF_abs) (fval t x)].
Axiom fneg_tr : forall t x, fok t x ->
  map (fval t) (S.fneg_ (fsz t) x) = [:: app_unop (Unop_f UOF_neg) (fval t x)].
Axiom fsqrt_tr : forall t x, fok t x ->
  map (fval t) (S.fsqrt_ (fsz t) x) = [:: app_unop (Unop_f UOF_sqrt) (fval t x)].
Axiom fceil_tr : forall t x, fok t x ->
  map (fval t) (S.fceil_ (fsz t) x) = [:: app_unop (Unop_f UOF_ceil) (fval t x)].
Axiom ffloor_tr : forall t x, fok t x ->
  map (fval t) (S.ffloor_ (fsz t) x) = [:: app_unop (Unop_f UOF_floor) (fval t x)].
Axiom ftrunc_tr : forall t x, fok t x ->
  map (fval t) (S.ftrunc_ (fsz t) x) = [:: app_unop (Unop_f UOF_trunc) (fval t x)].
Axiom fnearest_tr : forall t x, fok t x ->
  map (fval t) (S.fnearest_ (fsz t) x) = [:: app_unop (Unop_f UOF_nearest) (fval t x)].

Axiom fadd_tr : forall t x y, fok t x -> fok t y ->
  map (fval t) (S.fadd_ (fsz t) x y) = olist (app_binop (Binop_f BOF_add) (fval t x) (fval t y)).
Axiom fsub_tr : forall t x y, fok t x -> fok t y ->
  map (fval t) (S.fsub_ (fsz t) x y) = olist (app_binop (Binop_f BOF_sub) (fval t x) (fval t y)).
Axiom fmul_tr : forall t x y, fok t x -> fok t y ->
  map (fval t) (S.fmul_ (fsz t) x y) = olist (app_binop (Binop_f BOF_mul) (fval t x) (fval t y)).
Axiom fdiv_tr : forall t x y, fok t x -> fok t y ->
  map (fval t) (S.fdiv_ (fsz t) x y) = olist (app_binop (Binop_f BOF_div) (fval t x) (fval t y)).
Axiom fmin_tr : forall t x y, fok t x -> fok t y ->
  map (fval t) (S.fmin_ (fsz t) x y) = olist (app_binop (Binop_f BOF_min) (fval t x) (fval t y)).
Axiom fmax_tr : forall t x y, fok t x -> fok t y ->
  map (fval t) (S.fmax_ (fsz t) x y) = olist (app_binop (Binop_f BOF_max) (fval t x) (fval t y)).
Axiom fcopysign_tr : forall t x y, fok t x -> fok t y ->
  map (fval t) (S.fcopysign_ (fsz t) x y) = olist (app_binop (Binop_f BOF_copysign) (fval t x) (fval t y)).

Axiom feq_tr : forall t x y, fok t x -> fok t y ->
  ival S.Inn_I32 (S.feq_ (fsz t) x y) = VAL_int32 (wasm_bool (app_relop (Relop_f ROF_eq) (fval t x) (fval t y))).
Axiom fne_tr : forall t x y, fok t x -> fok t y ->
  ival S.Inn_I32 (S.fne_ (fsz t) x y) = VAL_int32 (wasm_bool (app_relop (Relop_f ROF_ne) (fval t x) (fval t y))).
Axiom flt_tr : forall t x y, fok t x -> fok t y ->
  ival S.Inn_I32 (S.flt_ (fsz t) x y) = VAL_int32 (wasm_bool (app_relop (Relop_f ROF_lt) (fval t x) (fval t y))).
Axiom fgt_tr : forall t x y, fok t x -> fok t y ->
  ival S.Inn_I32 (S.fgt_ (fsz t) x y) = VAL_int32 (wasm_bool (app_relop (Relop_f ROF_gt) (fval t x) (fval t y))).
Axiom fle_tr : forall t x y, fok t x -> fok t y ->
  ival S.Inn_I32 (S.fle_ (fsz t) x y) = VAL_int32 (wasm_bool (app_relop (Relop_f ROF_le) (fval t x) (fval t y))).
Axiom fge_tr : forall t x y, fok t x -> fok t y ->
  ival S.Inn_I32 (S.fge_ (fsz t) x y) = VAL_int32 (wasm_bool (app_relop (Relop_f ROF_ge) (fval t x) (fval t y))).

(** * Conversions *)

Axiom convert__tr : forall t1 t2 sx i, iok t1 i ->
  Some (fval t2 (S.convert__ (F.sizenn1 (S.numtype_Inn t1)) (F.sizenn2 (S.numtype_Fnn t2)) sx i)) =
  eval_cvt (tr_numtype (S.numtype_Fnn t2)) CVO_convert (Some (tr_sx sx)) (ival t1 i).
Axiom trunc__tr : forall t1 t2 sx x, fok t1 x ->
  option_map (ival t2) (S.trunc__ (F.sizenn1 (S.numtype_Fnn t1)) (F.sizenn2 (S.numtype_Inn t2)) sx x) =
  eval_cvt (tr_numtype (S.numtype_Inn t2)) CVO_trunc (Some (tr_sx sx)) (fval t1 x).
Axiom trunc_sat__tr : forall t1 t2 sx x, fok t1 x ->
  option_map (ival t2) (S.trunc_sat__ (F.sizenn1 (S.numtype_Fnn t1)) (F.sizenn2 (S.numtype_Inn t2)) sx x) =
  eval_cvt (tr_numtype (S.numtype_Inn t2)) CVO_trunc_sat (Some (tr_sx sx)) (fval t1 x).
Axiom promote__tr : forall t1 t2 x, fok t1 x ->
  map (fval t2) (S.promote__ (F.sizenn1 (S.numtype_Fnn t1)) (F.sizenn2 (S.numtype_Fnn t2)) x) =
  olist (eval_cvt (tr_numtype (S.numtype_Fnn t2)) CVO_promote None (fval t1 x)).
Axiom demote__tr : forall t1 t2 x, fok t1 x ->
  map (fval t2) (S.demote__ (F.sizenn1 (S.numtype_Fnn t1)) (F.sizenn2 (S.numtype_Fnn t2)) x) =
  olist (eval_cvt (tr_numtype (S.numtype_Fnn t2)) CVO_demote None (fval t1 x)).
Axiom reinterpret__tr : forall nt1 nt2 c, S.wf_num_ nt1 c ->
  tr_num (S.reinterpret__ nt1 nt2 c) = wasm_deserialise (serialise_num (tr_num c)) (tr_numtype nt2).

(** * The integer operations wasm.v defines agree with WasmCert's *)

Lemma eqm32_mod x : Wasm_int.Int32.eqm (x mod 4294967296) x.
Proof.
  exists (- (x / 4294967296))%Z. have := Z.div_mod x 4294967296.
  change Wasm_int.Int32.modulus with 4294967296%Z. lia.
Qed.

Lemma eqm64_mod x : Wasm_int.Int64.eqm (x mod 18446744073709551616) x.
Proof.
  exists (- (x / 18446744073709551616))%Z. have := Z.div_mod x 18446744073709551616.
  change Wasm_int.Int64.modulus with 18446744073709551616%Z. lia.
Qed.

Lemma iadd_tr t i j : iok t i -> iok t j ->
  Some (ival t (S.iadd_ (isz t) i j)) = app_binop (Binop_i BOI_add) (ival t i) (ival t j).
Proof.
  move=> _ _. case: t; case: i => a; case: j => b; cbn; f_equal; f_equal.
  - rewrite /tr_i32 /tr_u32 /= /Wasm_int.Int32.iadd Wasm_int.Int32.add_unsigned.
    apply: Wasm_int.Int32.eqm_samerepr. rewrite N2Z.inj_mod N2Z.inj_add.
    apply: Wasm_int.Int32.eqm_trans; first exact: eqm32_mod.
    apply: Wasm_int.Int32.eqm_add; exact: Wasm_int.Int32.eqm_unsigned_repr.
  - rewrite /tr_i64 /tr_u32 /= /Wasm_int.Int64.iadd Wasm_int.Int64.add_unsigned.
    apply: Wasm_int.Int64.eqm_samerepr. rewrite N2Z.inj_mod N2Z.inj_add.
    apply: Wasm_int.Int64.eqm_trans; first exact: eqm64_mod.
    apply: Wasm_int.Int64.eqm_add; exact: Wasm_int.Int64.eqm_unsigned_repr.
Qed.

Lemma truncz_div a b : b <> 0%Z -> S.truncz (inject_Z a / inject_Z b)%Q = Z.quot a b.
Proof.
  move=> Hb. rewrite truncz_def. case: b Hb => [//|p|p] _ /=.
  - by rewrite Z.mul_1_r.
  - have -> : Z.neg p = (- Z.pos p)%Z by []. rewrite Z.quot_opp_r //.
    have -> : (a * -1 = - a)%Z by lia. by rewrite Z.quot_opp_l.
Qed.

(* WasmCert computes the signed remainder from the floored one. *)
Lemma rem_wasm a b : b <> 0%Z ->
  (if (a mod b == 0)%Z then (a mod b)%Z else
   match (a mod b >=? 0)%Z, (a >=? 0)%Z with
   | true, true | false, false => (a mod b)%Z
   | true, false | false, true => (a mod b - b)%Z
   end) = Z.rem a b.
Proof.
  move=> Hb. have Hd := Z.div_mod a b Hb. have Hq := Z.quot_rem' a b.
  have Hr := Z.rem_bound_abs a b Hb.
  have Hs : (0 <= a -> 0 <= Z.rem a b)%Z by move=> ?; apply: Z.rem_nonneg.
  have Hs' : (a <= 0 -> Z.rem a b <= 0)%Z by move=> ?; apply: Z.rem_nonpos.
  have Hm : (0 < b -> 0 <= a mod b < b)%Z /\ (b < 0 -> b < a mod b <= 0)%Z.
  { split => H; [exact: Z.mod_pos_bound | exact: Z.mod_neg_bound]. }
  set q := (a / b)%Z in Hd. set q' := (a ÷ b)%Z in Hq.
  have E : (b * (q - q') = Z.rem a b - a mod b)%Z by rewrite Z.mul_sub_distr_l; lia.
  clearbody q q'. move: E. set k := (q - q')%Z => E. clearbody k.
  have Hk : (k = -1 \/ k = 0 \/ k = 1)%Z.
  { case: (Z.lt_trichotomy b 0) => [Hn|[//|Hn]]; clear -E Hr Hm Hb Hn; nia. }
  case: eqP => E0; [ |case: Z.geb_spec => H1; case: Z.geb_spec => H2];
    case: (Z.lt_trichotomy b 0) => [Hn|[//|Hp]]; nia.
Qed.

Lemma isub_tr t i j : iok t i -> iok t j ->
  Some (ival t (S.isub_ (isz t) i j)) = app_binop (Binop_i BOI_sub) (ival t i) (ival t j).
Proof.
  move=> _ _. case: t; case: i => a; case: j => b; cbn; f_equal; f_equal.
  - rewrite /tr_i32 /tr_u32 /S.isub_ /Wasm_int.Int32.isub /Wasm_int.Int32.sub.
    cbn [S.proj_uN_0 S.coerce S.proj_uN_0_coercion].
    apply: Wasm_int.Int32.eqm_samerepr. change (Z.of_N (2 ^ 32)) with 4294967296%Z.
    rewrite Z2N.id; last by apply: (proj1 (Z.mod_pos_bound _ _ _)).
    apply: Wasm_int.Int32.eqm_trans; first exact: eqm32_mod.
    rewrite N2Z.inj_add.
    apply: Wasm_int.Int32.eqm_trans; last apply: Wasm_int.Int32.eqm_sub;
      [ |exact: Wasm_int.Int32.eqm_unsigned_repr|exact: Wasm_int.Int32.eqm_unsigned_repr].
    exists 1%Z. change Wasm_int.Int32.modulus with 4294967296%Z. lia.
  - rewrite /tr_i64 /tr_u32 /S.isub_ /Wasm_int.Int64.isub /Wasm_int.Int64.sub.
    cbn [S.proj_uN_0 S.coerce S.proj_uN_0_coercion].
    apply: Wasm_int.Int64.eqm_samerepr. change (Z.of_N (2 ^ 64)) with 18446744073709551616%Z.
    rewrite Z2N.id; last by apply: (proj1 (Z.mod_pos_bound _ _ _)).
    apply: Wasm_int.Int64.eqm_trans; first exact: eqm64_mod.
    rewrite N2Z.inj_add.
    apply: Wasm_int.Int64.eqm_trans; last apply: Wasm_int.Int64.eqm_sub;
      [ |exact: Wasm_int.Int64.eqm_unsigned_repr|exact: Wasm_int.Int64.eqm_unsigned_repr].
    exists 1%Z. change Wasm_int.Int64.modulus with 18446744073709551616%Z. lia.
Qed.

Lemma imul_tr t i j : iok t i -> iok t j ->
  Some (ival t (S.imul_ (isz t) i j)) = app_binop (Binop_i BOI_mul) (ival t i) (ival t j).
Proof.
  move=> _ _. case: t; case: i => a; case: j => b; cbn; f_equal; f_equal.
  - rewrite /tr_i32 /tr_u32 /S.imul_ /Wasm_int.Int32.imul /Wasm_int.Int32.mul.
    cbn [S.proj_uN_0 S.coerce S.proj_uN_0_coercion].
    apply: Wasm_int.Int32.eqm_samerepr. rewrite N2Z.inj_mod N2Z.inj_mul.
    change (Z.of_N (2 ^ 32)) with 4294967296%Z.
    apply: Wasm_int.Int32.eqm_trans; first exact: eqm32_mod.
    apply: Wasm_int.Int32.eqm_mult; exact: Wasm_int.Int32.eqm_unsigned_repr.
  - rewrite /tr_i64 /tr_u32 /S.imul_ /Wasm_int.Int64.imul /Wasm_int.Int64.mul.
    cbn [S.proj_uN_0 S.coerce S.proj_uN_0_coercion].
    apply: Wasm_int.Int64.eqm_samerepr. rewrite N2Z.inj_mod N2Z.inj_mul.
    change (Z.of_N (2 ^ 64)) with 18446744073709551616%Z.
    apply: Wasm_int.Int64.eqm_trans; first exact: eqm64_mod.
    apply: Wasm_int.Int64.eqm_mult; exact: Wasm_int.Int64.eqm_unsigned_repr.
Qed.

Lemma signed32 a z : (a < 4294967296)%num -> S.fun_signed_ 32%num a z ->
  z = Wasm_int.Int32.signed (Wasm_int.Int32.repr (Z.of_N a)).
Proof.
  move=> Ha H. rewrite /Wasm_int.Int32.signed Wasm_int.Int32.unsigned_repr;
    last by change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia.
  change Wasm_int.Int32.half_modulus with 2147483648%Z.
  change Wasm_int.Int32.modulus with 4294967296%Z.
  inversion H; subst; move: H0;
    change (2 ^ Z.to_N (Z.of_N 32 - Z.of_N 1))%num with 2147483648%num.
  - move/N.ltb_spec0 => ?. case: Coqlib.zlt => ? //; lia.
  - change (Z.of_N (2 ^ 32)) with 4294967296%Z.
    move/andP => [/N.leb_spec0 ? _]. case: Coqlib.zlt => ? //; lia.
Qed.

Lemma inv_signed32 z n : S.fun_inv_signed_ 32%num z n ->
  (-2147483648 <= z < 2147483648)%Z /\ Wasm_int.Int32.repr (Z.of_N n) = Wasm_int.Int32.repr z.
Proof.
  move=> H. inversion H; subst; move: H0;
    change (Z.of_N (2 ^ Z.to_N (Z.of_N 32 - Z.of_N 1))) with 2147483648%Z;
    change (Z.of_N (2 ^ 32)) with 4294967296%Z.
  - move/andP => [/Z.leb_spec0 ? /Z.ltb_spec0 ?]. rewrite Z2N.id //. split => //. lia.
  - move/andP => [/Z.leb_spec0 ? /Z.ltb_spec0 ?]. rewrite Z2N.id; last lia. split; first lia.
    apply: Wasm_int.Int32.eqm_samerepr. exists 1%Z.
    change Wasm_int.Int32.modulus with 4294967296%Z. lia.
Qed.

Lemma signed64 a z : (a < 18446744073709551616)%num -> S.fun_signed_ 64%num a z ->
  z = Wasm_int.Int64.signed (Wasm_int.Int64.repr (Z.of_N a)).
Proof.
  move=> Ha H. rewrite /Wasm_int.Int64.signed Wasm_int.Int64.unsigned_repr;
    last by change Wasm_int.Int64.max_unsigned with 18446744073709551615%Z; lia.
  change Wasm_int.Int64.half_modulus with 9223372036854775808%Z.
  change Wasm_int.Int64.modulus with 18446744073709551616%Z.
  inversion H; subst; move: H0;
    change (2 ^ Z.to_N (Z.of_N 64 - Z.of_N 1))%num with 9223372036854775808%num.
  - move/N.ltb_spec0 => ?. case: Coqlib.zlt => ? //; lia.
  - change (Z.of_N (2 ^ 64)) with 18446744073709551616%Z.
    move/andP => [/N.leb_spec0 ? _]. case: Coqlib.zlt => ? //; lia.
Qed.

Lemma inv_signed64 z n : S.fun_inv_signed_ 64%num z n ->
  (-9223372036854775808 <= z < 9223372036854775808)%Z /\ Wasm_int.Int64.repr (Z.of_N n) = Wasm_int.Int64.repr z.
Proof.
  move=> H. inversion H; subst; move: H0;
    change (Z.of_N (2 ^ Z.to_N (Z.of_N 64 - Z.of_N 1))) with 9223372036854775808%Z;
    change (Z.of_N (2 ^ 64)) with 18446744073709551616%Z.
  - move/andP => [/Z.leb_spec0 ? /Z.ltb_spec0 ?]. rewrite Z2N.id //. split => //. lia.
  - move/andP => [/Z.leb_spec0 ? /Z.ltb_spec0 ?]. rewrite Z2N.id; last lia. split; first lia.
    apply: Wasm_int.Int64.eqm_samerepr. exists 1%Z.
    change Wasm_int.Int64.modulus with 18446744073709551616%Z. lia.
Qed.

Lemma Qdiv_Z_eq x y k : y <> 0%Z -> Qeq_bool (inject_Z x / inject_Z y) (inject_Z k) -> x = (k * y)%Z.
Proof.
  move=> Hy /Qeq_bool_iff. rewrite /Qeq /=. case: y Hy => [//|p|p] _ /=; lia.
Qed.

Lemma iok32 a : iok S.Inn_I32 (S.mk_uN a) -> (a < 4294967296)%num.
Proof.
  move=> H. inversion H; subst. match goal with H : S.wf_uN _ _ |- _ => inversion H; subst end.
  match goal with H : is_true (_ && _) |- _ => move: H => /andP [_ /N.leb_spec0] end.
  cbn. lia.
Qed.

Lemma iok64 a : iok S.Inn_I64 (S.mk_uN a) -> (a < 18446744073709551616)%num.
Proof.
  move=> H. inversion H; subst. match goal with H : S.wf_uN _ _ |- _ => inversion H; subst end.
  match goal with H : is_true (_ && _) |- _ => move: H => /andP [_ /N.leb_spec0] end.
  cbn. lia.
Qed.

Lemma signed32_nz b : (b < 4294967296)%num -> b <> 0%num ->
  Wasm_int.Int32.signed (Wasm_int.Int32.repr (Z.of_N b)) <> 0%Z.
Proof.
  move=> Hb Hb0. rewrite /Wasm_int.Int32.signed Wasm_int.Int32.unsigned_repr;
    last by change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia.
  case: Coqlib.zlt => _; change Wasm_int.Int32.modulus with 4294967296%Z; lia.
Qed.

Lemma idiv_tr32 sx a b r : iok S.Inn_I32 (S.mk_uN a) -> iok S.Inn_I32 (S.mk_uN b) -> b <> 0%num ->
  S.fun_idiv_ 32%num sx (S.mk_uN a) (S.mk_uN b) r ->
  option_map (ival S.Inn_I32) r =
  app_binop (Binop_i (BOI_div (tr_sx sx))) (ival S.Inn_I32 (S.mk_uN a)) (ival S.Inn_I32 (S.mk_uN b)).
Proof.
  move=> /iok32 Ha /iok32 Hb Hb0 H. have Hy := signed32_nz Hb Hb0.
  inversion H; subst => //.
  all: cbn [ival tr_num tr_sx app_binop app_binop_i Wasm_int.int_div_u Wasm_int.int_div_s
            i32m Wasm_int.Int32.Tmixin option_map].
  all: rewrite /tr_i32 /tr_u32; cbn [S.proj_uN_0].
  - cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0]. rewrite truncz_div; last lia.
    rewrite Z.quot_div_nonneg; try lia. rewrite -N2Z.inj_div N2Z.id.
    rewrite /Wasm_int.Int32.idiv_u /Wasm_int.Int32.eq /Wasm_int.Int32.divu.
    rewrite !Wasm_int.Int32.unsigned_repr; try (change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia).
    case: Coqlib.zeq => [?|_] /=; first lia. by rewrite N2Z.inj_div.
  - move: H0 H1 H2. cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0].
    move=> /(signed32 Hb) -> /(signed32 Ha) ->.
    change (Z.of_N (2 ^ Z.to_N (Z.of_N 32 - Z.of_N 1))) with 2147483648%Z.
    move/(Qdiv_Z_eq Hy) => Hq. rewrite /Wasm_int.Int32.idiv_s. case: eqP => // _.
    by rewrite Hq Z.quot_mul.
  - move: H0 H1 H2. cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0].
    move=> /(signed32 Hb) -> /(signed32 Ha) ->. rewrite truncz_div //.
    move/inv_signed32 => [Hr ->]. rewrite /Wasm_int.Int32.idiv_s. case: eqP => // _.
    change Wasm_int.Int32.half_modulus with 2147483648%Z. case: eqP => // ?. lia.
Qed.

Lemma irem_tr32 sx a b r : iok S.Inn_I32 (S.mk_uN a) -> iok S.Inn_I32 (S.mk_uN b) -> b <> 0%num ->
  S.fun_irem_ 32%num sx (S.mk_uN a) (S.mk_uN b) r ->
  option_map (ival S.Inn_I32) r =
  app_binop (Binop_i (BOI_rem (tr_sx sx))) (ival S.Inn_I32 (S.mk_uN a)) (ival S.Inn_I32 (S.mk_uN b)).
Proof.
  move=> /iok32 Ha /iok32 Hb Hb0 H. have Hy := signed32_nz Hb Hb0.
  inversion H; subst => //.
  all: cbn [ival tr_num tr_sx app_binop app_binop_i Wasm_int.int_rem_u Wasm_int.int_rem_s
            i32m Wasm_int.Int32.Tmixin option_map].
  all: rewrite /tr_i32 /tr_u32; cbn [S.proj_uN_0 S.coerce S.proj_uN_0_coercion].
  - rewrite truncz_div; last lia. rewrite Z.quot_div_nonneg; try lia. rewrite -N2Z.inj_div N2Z.id.
    rewrite (_ : (Z.of_N a - Z.of_N (b * (a / b)))%Z = Z.of_N (a mod b)); last first.
    { rewrite N.Div0.mod_eq N2Z.inj_sub //. exact: N.Div0.mul_div_le. }
    rewrite N2Z.id N2Z.inj_mod.
    rewrite /Wasm_int.Int32.irem_u /Wasm_int.Int32.eq /Wasm_int.Int32.modu.
    rewrite !Wasm_int.Int32.unsigned_repr; try (change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia).
    by case: Coqlib.zeq => [?|_] /=; first lia.
  - move: H3 => /andP [/eqP ? /eqP ?]. subst. move: H0 H1 H2.
    cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0].
    move=> /(signed32 Hb) -> /(signed32 Ha) ->. rewrite truncz_div // -Z.rem_eq //.
    move/inv_signed32 => [Hr ->]. rewrite /Wasm_int.Int32.irem_s.
    case: eqP => // _. by rewrite rem_wasm.
Qed.

Lemma signed64_nz b : (b < 18446744073709551616)%num -> b <> 0%num ->
  Wasm_int.Int64.signed (Wasm_int.Int64.repr (Z.of_N b)) <> 0%Z.
Proof.
  move=> Hb Hb0. rewrite /Wasm_int.Int64.signed Wasm_int.Int64.unsigned_repr;
    last by change Wasm_int.Int64.max_unsigned with 18446744073709551615%Z; lia.
  case: Coqlib.zlt => _; change Wasm_int.Int64.modulus with 18446744073709551616%Z; lia.
Qed.

Lemma idiv_tr64 sx a b r : iok S.Inn_I64 (S.mk_uN a) -> iok S.Inn_I64 (S.mk_uN b) -> b <> 0%num ->
  S.fun_idiv_ 64%num sx (S.mk_uN a) (S.mk_uN b) r ->
  option_map (ival S.Inn_I64) r =
  app_binop (Binop_i (BOI_div (tr_sx sx))) (ival S.Inn_I64 (S.mk_uN a)) (ival S.Inn_I64 (S.mk_uN b)).
Proof.
  move=> /iok64 Ha /iok64 Hb Hb0 H. have Hy := signed64_nz Hb Hb0.
  inversion H; subst => //.
  all: cbn [ival tr_num tr_sx app_binop app_binop_i Wasm_int.int_div_u Wasm_int.int_div_s
            i64m Wasm_int.Int64.Tmixin option_map].
  all: rewrite /tr_i64 /tr_u32; cbn [S.proj_uN_0].
  - cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0]. rewrite truncz_div; last lia.
    rewrite Z.quot_div_nonneg; try lia. rewrite -N2Z.inj_div N2Z.id.
    rewrite /Wasm_int.Int64.idiv_u /Wasm_int.Int64.eq /Wasm_int.Int64.divu.
    rewrite !Wasm_int.Int64.unsigned_repr; try (change Wasm_int.Int64.max_unsigned with 18446744073709551615%Z; lia).
    case: Coqlib.zeq => [?|_] /=; first lia. by rewrite N2Z.inj_div.
  - move: H0 H1 H2. cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0].
    move=> /(signed64 Hb) -> /(signed64 Ha) ->.
    change (Z.of_N (2 ^ Z.to_N (Z.of_N 64 - Z.of_N 1))) with 9223372036854775808%Z.
    move/(Qdiv_Z_eq Hy) => Hq. rewrite /Wasm_int.Int64.idiv_s. case: eqP => // _.
    by rewrite Hq Z.quot_mul.
  - move: H0 H1 H2. cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0].
    move=> /(signed64 Hb) -> /(signed64 Ha) ->. rewrite truncz_div //.
    move/inv_signed64 => [Hr ->]. rewrite /Wasm_int.Int64.idiv_s. case: eqP => // _.
    change Wasm_int.Int64.half_modulus with 9223372036854775808%Z. case: eqP => // ?. lia.
Qed.

Lemma irem_tr64 sx a b r : iok S.Inn_I64 (S.mk_uN a) -> iok S.Inn_I64 (S.mk_uN b) -> b <> 0%num ->
  S.fun_irem_ 64%num sx (S.mk_uN a) (S.mk_uN b) r ->
  option_map (ival S.Inn_I64) r =
  app_binop (Binop_i (BOI_rem (tr_sx sx))) (ival S.Inn_I64 (S.mk_uN a)) (ival S.Inn_I64 (S.mk_uN b)).
Proof.
  move=> /iok64 Ha /iok64 Hb Hb0 H. have Hy := signed64_nz Hb Hb0.
  inversion H; subst => //.
  all: cbn [ival tr_num tr_sx app_binop app_binop_i Wasm_int.int_rem_u Wasm_int.int_rem_s
            i64m Wasm_int.Int64.Tmixin option_map].
  all: rewrite /tr_i64 /tr_u32; cbn [S.proj_uN_0 S.coerce S.proj_uN_0_coercion].
  - rewrite truncz_div; last lia. rewrite Z.quot_div_nonneg; try lia. rewrite -N2Z.inj_div N2Z.id.
    rewrite (_ : (Z.of_N a - Z.of_N (b * (a / b)))%Z = Z.of_N (a mod b)); last first.
    { rewrite N.Div0.mod_eq N2Z.inj_sub //. exact: N.Div0.mul_div_le. }
    rewrite N2Z.id N2Z.inj_mod.
    rewrite /Wasm_int.Int64.irem_u /Wasm_int.Int64.eq /Wasm_int.Int64.modu.
    rewrite !Wasm_int.Int64.unsigned_repr; try (change Wasm_int.Int64.max_unsigned with 18446744073709551615%Z; lia).
    by case: Coqlib.zeq => [?|_] /=; first lia.
  - move: H3 => /andP [/eqP ? /eqP ?]. subst. move: H0 H1 H2.
    cbn [S.coerce S.proj_uN_0_coercion S.proj_uN_0].
    move=> /(signed64 Hb) -> /(signed64 Ha) ->. rewrite truncz_div // -Z.rem_eq //.
    move/inv_signed64 => [Hr ->]. rewrite /Wasm_int.Int64.irem_s.
    case: eqP => // _. by rewrite rem_wasm.
Qed.

Lemma res_bool_tr b : tr_i32 (S.mk_uN (S.res_bool b)) = wasm_bool b.
Proof. by case: b. Qed.

Lemma res_bool_repr b : Wasm_int.Int32.repr (Z.of_N (S.res_bool b)) = wasm_bool b.
Proof. by case: b. Qed.

Lemma eqz_tr32 a : (a < 4294967296)%num ->
  Wasm_int.Int32.eq Wasm_int.Int32.zero (Wasm_int.Int32.repr (Z.of_N a)) = N.eqb a 0.
Proof.
  move=> Ha. rewrite /Wasm_int.Int32.eq Wasm_int.Int32.unsigned_repr;
    last by change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia.
  case: Coqlib.zeq => /= E; case: N.eqb_spec => ? //; lia.
Qed.

Lemma eq_tr32 a b : (a < 4294967296)%num -> (b < 4294967296)%num ->
  Wasm_int.Int32.eq (Wasm_int.Int32.repr (Z.of_N a)) (Wasm_int.Int32.repr (Z.of_N b)) = (S.mk_uN a == S.mk_uN b).
Proof.
  move=> Ha Hb. rewrite /Wasm_int.Int32.eq !Wasm_int.Int32.unsigned_repr;
    try by change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia.
  case: Coqlib.zeq => /= E; case: eqP => // E'.
  - exfalso. apply: E'. f_equal. lia.
  - case: E'. lia.
Qed.

Lemma ltu_tr32 a b : (a < 4294967296)%num -> (b < 4294967296)%num ->
  Wasm_int.Int32.ltu (Wasm_int.Int32.repr (Z.of_N a)) (Wasm_int.Int32.repr (Z.of_N b)) = (a <? b)%num.
Proof.
  move=> Ha Hb. rewrite /Wasm_int.Int32.ltu !Wasm_int.Int32.unsigned_repr;
    try by change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia.
  case: Coqlib.zlt => /= E; case: N.ltb_spec0 => //; lia.
Qed.

Lemma lt_tr32 a b x y : (a < 4294967296)%num -> (b < 4294967296)%num ->
  S.fun_signed_ 32%num a x -> S.fun_signed_ 32%num b y ->
  Wasm_int.Int32.lt (Wasm_int.Int32.repr (Z.of_N a)) (Wasm_int.Int32.repr (Z.of_N b)) = (x <? y)%Z.
Proof.
  move=> Ha Hb /(signed32 Ha) -> /(signed32 Hb) ->. rewrite /Wasm_int.Int32.lt.
  case: Coqlib.zlt => /= E; case: Z.ltb_spec0 => //; lia.
Qed.

Lemma ilt_tr32 sx a b r : (a < 4294967296)%num -> (b < 4294967296)%num ->
  S.fun_ilt_ 32%num sx (S.mk_uN a) (S.mk_uN b) r ->
  tr_i32 r = wasm_bool (app_relop_i i32m (ROI_lt (tr_sx sx)) (Wasm_int.Int32.repr (Z.of_N a)) (Wasm_int.Int32.repr (Z.of_N b))).
Proof.
  move=> Ha Hb H. inversion H; subst; rewrite res_bool_tr; cbn [tr_sx app_relop_i i32m Wasm_int.int_lt_u Wasm_int.int_lt_s Wasm_int.Int32.Tmixin].
  - by rewrite ltu_tr32.
  - by rewrite (lt_tr32 Ha Hb H1 H0).
Qed.

Lemma igt_tr32 sx a b r : (a < 4294967296)%num -> (b < 4294967296)%num ->
  S.fun_igt_ 32%num sx (S.mk_uN a) (S.mk_uN b) r ->
  tr_i32 r = wasm_bool (app_relop_i i32m (ROI_gt (tr_sx sx)) (Wasm_int.Int32.repr (Z.of_N a)) (Wasm_int.Int32.repr (Z.of_N b))).
Proof.
  move=> Ha Hb H. inversion H; subst; rewrite res_bool_tr; cbn [tr_sx app_relop_i i32m Wasm_int.int_gt_u Wasm_int.int_gt_s Wasm_int.Int32.Tmixin].
  - by rewrite ltu_tr32.
  - rewrite (lt_tr32 Hb Ha H0 H1). by rewrite Z.gtb_ltb.
Qed.

Lemma ile_tr32 sx a b r : (a < 4294967296)%num -> (b < 4294967296)%num ->
  S.fun_ile_ 32%num sx (S.mk_uN a) (S.mk_uN b) r ->
  tr_i32 r = wasm_bool (app_relop_i i32m (ROI_le (tr_sx sx)) (Wasm_int.Int32.repr (Z.of_N a)) (Wasm_int.Int32.repr (Z.of_N b))).
Proof.
  move=> Ha Hb H. inversion H; subst; rewrite res_bool_tr; cbn [tr_sx app_relop_i i32m Wasm_int.int_le_u Wasm_int.int_le_s Wasm_int.Int32.Tmixin].
  - rewrite ltu_tr32 //. by rewrite N.leb_antisym.
  - rewrite (lt_tr32 Hb Ha H0 H1). by rewrite Z.leb_antisym.
Qed.

Lemma ige_tr32 sx a b r : (a < 4294967296)%num -> (b < 4294967296)%num ->
  S.fun_ige_ 32%num sx (S.mk_uN a) (S.mk_uN b) r ->
  tr_i32 r = wasm_bool (app_relop_i i32m (ROI_ge (tr_sx sx)) (Wasm_int.Int32.repr (Z.of_N a)) (Wasm_int.Int32.repr (Z.of_N b))).
Proof.
  move=> Ha Hb H. inversion H; subst; rewrite res_bool_tr; cbn [tr_sx app_relop_i i32m Wasm_int.int_ge_u Wasm_int.int_ge_s Wasm_int.Int32.Tmixin].
  - rewrite ltu_tr32 //. by rewrite /S.N_geb N.leb_antisym.
  - rewrite (lt_tr32 Ha Hb H1 H0). by rewrite Z.geb_leb Z.leb_antisym.
Qed.

Lemma eqz_tr64 a : (a < 18446744073709551616)%num ->
  Wasm_int.Int64.eq Wasm_int.Int64.zero (Wasm_int.Int64.repr (Z.of_N a)) = N.eqb a 0.
Proof.
  move=> Ha. rewrite /Wasm_int.Int64.eq Wasm_int.Int64.unsigned_repr;
    last by change Wasm_int.Int64.max_unsigned with 18446744073709551615%Z; lia.
  case: Coqlib.zeq => /= E; case: N.eqb_spec => ? //; lia.
Qed.

Lemma eq_tr64 a b : (a < 18446744073709551616)%num -> (b < 18446744073709551616)%num ->
  Wasm_int.Int64.eq (Wasm_int.Int64.repr (Z.of_N a)) (Wasm_int.Int64.repr (Z.of_N b)) = (S.mk_uN a == S.mk_uN b).
Proof.
  move=> Ha Hb. rewrite /Wasm_int.Int64.eq !Wasm_int.Int64.unsigned_repr;
    try by change Wasm_int.Int64.max_unsigned with 18446744073709551615%Z; lia.
  case: Coqlib.zeq => /= E; case: eqP => // E'.
  - exfalso. apply: E'. f_equal. lia.
  - case: E'. lia.
Qed.

Lemma ltu_tr64 a b : (a < 18446744073709551616)%num -> (b < 18446744073709551616)%num ->
  Wasm_int.Int64.ltu (Wasm_int.Int64.repr (Z.of_N a)) (Wasm_int.Int64.repr (Z.of_N b)) = (a <? b)%num.
Proof.
  move=> Ha Hb. rewrite /Wasm_int.Int64.ltu !Wasm_int.Int64.unsigned_repr;
    try by change Wasm_int.Int64.max_unsigned with 18446744073709551615%Z; lia.
  case: Coqlib.zlt => /= E; case: N.ltb_spec0 => //; lia.
Qed.

Lemma lt_tr64 a b x y : (a < 18446744073709551616)%num -> (b < 18446744073709551616)%num ->
  S.fun_signed_ 64%num a x -> S.fun_signed_ 64%num b y ->
  Wasm_int.Int64.lt (Wasm_int.Int64.repr (Z.of_N a)) (Wasm_int.Int64.repr (Z.of_N b)) = (x <? y)%Z.
Proof.
  move=> Ha Hb /(signed64 Ha) -> /(signed64 Hb) ->. rewrite /Wasm_int.Int64.lt.
  case: Coqlib.zlt => /= E; case: Z.ltb_spec0 => //; lia.
Qed.

Lemma ilt_tr64 sx a b r : (a < 18446744073709551616)%num -> (b < 18446744073709551616)%num ->
  S.fun_ilt_ 64%num sx (S.mk_uN a) (S.mk_uN b) r ->
  tr_i32 r = wasm_bool (app_relop_i i64m (ROI_lt (tr_sx sx)) (Wasm_int.Int64.repr (Z.of_N a)) (Wasm_int.Int64.repr (Z.of_N b))).
Proof.
  move=> Ha Hb H. inversion H; subst; rewrite res_bool_tr; cbn [tr_sx app_relop_i i64m Wasm_int.int_lt_u Wasm_int.int_lt_s Wasm_int.Int64.Tmixin].
  - by rewrite ltu_tr64.
  - by rewrite (lt_tr64 Ha Hb H1 H0).
Qed.

Lemma igt_tr64 sx a b r : (a < 18446744073709551616)%num -> (b < 18446744073709551616)%num ->
  S.fun_igt_ 64%num sx (S.mk_uN a) (S.mk_uN b) r ->
  tr_i32 r = wasm_bool (app_relop_i i64m (ROI_gt (tr_sx sx)) (Wasm_int.Int64.repr (Z.of_N a)) (Wasm_int.Int64.repr (Z.of_N b))).
Proof.
  move=> Ha Hb H. inversion H; subst; rewrite res_bool_tr; cbn [tr_sx app_relop_i i64m Wasm_int.int_gt_u Wasm_int.int_gt_s Wasm_int.Int64.Tmixin].
  - by rewrite ltu_tr64.
  - rewrite (lt_tr64 Hb Ha H0 H1). by rewrite Z.gtb_ltb.
Qed.

Lemma ile_tr64 sx a b r : (a < 18446744073709551616)%num -> (b < 18446744073709551616)%num ->
  S.fun_ile_ 64%num sx (S.mk_uN a) (S.mk_uN b) r ->
  tr_i32 r = wasm_bool (app_relop_i i64m (ROI_le (tr_sx sx)) (Wasm_int.Int64.repr (Z.of_N a)) (Wasm_int.Int64.repr (Z.of_N b))).
Proof.
  move=> Ha Hb H. inversion H; subst; rewrite res_bool_tr; cbn [tr_sx app_relop_i i64m Wasm_int.int_le_u Wasm_int.int_le_s Wasm_int.Int64.Tmixin].
  - rewrite ltu_tr64 //. by rewrite N.leb_antisym.
  - rewrite (lt_tr64 Hb Ha H0 H1). by rewrite Z.leb_antisym.
Qed.

Lemma ige_tr64 sx a b r : (a < 18446744073709551616)%num -> (b < 18446744073709551616)%num ->
  S.fun_ige_ 64%num sx (S.mk_uN a) (S.mk_uN b) r ->
  tr_i32 r = wasm_bool (app_relop_i i64m (ROI_ge (tr_sx sx)) (Wasm_int.Int64.repr (Z.of_N a)) (Wasm_int.Int64.repr (Z.of_N b))).
Proof.
  move=> Ha Hb H. inversion H; subst; rewrite res_bool_tr; cbn [tr_sx app_relop_i i64m Wasm_int.int_ge_u Wasm_int.int_ge_s Wasm_int.Int64.Tmixin].
  - rewrite ltu_tr64 //. by rewrite /S.N_geb N.leb_antisym.
  - rewrite (lt_tr64 Ha Hb H1 H0). by rewrite Z.geb_leb Z.leb_antisym.
Qed.

Lemma extend_unop_tr32 M a : (a < 4294967296)%num -> (M mod 8 = 0)%num ->
  VAL_int32 (tr_i32 (S.extend__ M 32%num S.res_S (S.wrap__ 32%num M (S.mk_uN a)))) =
  app_unop (Unop_extend M) (VAL_int32 (Wasm_int.Int32.repr (Z.of_N a))).
Proof.
  move=> Ha HM. rewrite wrap__def extend__def /tr_i32 /tr_u32.
  cbn [S.proj_uN_0 app_unop app_unop_extend sign_extend_n Wasm_int.N_of_uint i32m
       Wasm_int.Int32.Tmixin Wasm_int.int_of_Z].
  rewrite Wasm_int.Int32.unsigned_repr; last by change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia.
  rewrite N2Z.id.
  have E8 : (8 * (M / 8) = M)%num by have := N.div_mod M 8; rewrite HM; lia.
  rewrite E8 /sign_extend_n.
  have E8' : ((M / 8) * 8 - 1 = M - 1)%num by rewrite N.mul_comm E8.
  rewrite E8' (_ : (2 * 2 ^ (M - 1))%num = if (M =? 0)%num then 2%num else (2 ^ M)%num); last first.
  { case: N.eqb_spec => [->//|?]. rewrite -N.pow_succ_r'. f_equal. lia. }
  set w := (a mod 2 ^ M)%num.
  have Hw : (w < 2 ^ M)%num by apply: N.mod_lt; apply: N.pow_nonzero.
  f_equal. case: N.ltb_spec => H1; first done.
  case: N.eqb_spec => HM0.
  { exfalso. move: H1 Hw. rewrite HM0 /=. lia. }
  have HM32 : (M <= 32)%num.
  { case: (N.le_gt_cases M 32) => // HM'. exfalso.
    have : (2 ^ 32 <= 2 ^ (M - 1))%num by apply: N.pow_le_mono_r; lia.
    have : (w <= a)%num by apply: N.Div0.mod_le. lia. }
  have HpM : (2 ^ M <= 2 ^ 32)%num by apply: N.pow_le_mono_r.
  apply: Wasm_int.Int32.eqm_samerepr. exists 1%Z.
  rewrite N2Z.inj_sub; last lia. rewrite N2Z.inj_add.
  change Wasm_int.Int32.modulus with 4294967296%Z. change (Z.of_N (2 ^ 32)) with 4294967296%Z. lia.
Qed.

Lemma extend_unop_tr64 M a : (a < 18446744073709551616)%num -> (M mod 8 = 0)%num ->
  VAL_int64 (tr_i64 (S.extend__ M 64%num S.res_S (S.wrap__ 64%num M (S.mk_uN a)))) =
  app_unop (Unop_extend M) (VAL_int64 (Wasm_int.Int64.repr (Z.of_N a))).
Proof.
  move=> Ha HM. rewrite wrap__def extend__def /tr_i64 /tr_u32.
  cbn [S.proj_uN_0 app_unop app_unop_extend sign_extend_n Wasm_int.N_of_uint i64m
       Wasm_int.Int64.Tmixin Wasm_int.int_of_Z].
  rewrite Wasm_int.Int64.unsigned_repr; last by change Wasm_int.Int64.max_unsigned with 18446744073709551615%Z; lia.
  rewrite N2Z.id.
  have E8 : (8 * (M / 8) = M)%num by have := N.div_mod M 8; rewrite HM; lia.
  rewrite E8 /sign_extend_n.
  have E8' : ((M / 8) * 8 - 1 = M - 1)%num by rewrite N.mul_comm E8.
  rewrite E8' (_ : (2 * 2 ^ (M - 1))%num = if (M =? 0)%num then 2%num else (2 ^ M)%num); last first.
  { case: N.eqb_spec => [->//|?]. rewrite -N.pow_succ_r'. f_equal. lia. }
  set w := (a mod 2 ^ M)%num.
  have Hw : (w < 2 ^ M)%num by apply: N.mod_lt; apply: N.pow_nonzero.
  f_equal. case: N.ltb_spec => H1; first done.
  case: N.eqb_spec => HM0.
  { exfalso. move: H1 Hw. rewrite HM0 /=. lia. }
  have HM64 : (M <= 64)%num.
  { case: (N.le_gt_cases M 64) => // HM'. exfalso.
    have : (2 ^ 64 <= 2 ^ (M - 1))%num by apply: N.pow_le_mono_r; lia.
    have : (w <= a)%num by apply: N.Div0.mod_le. lia. }
  have HpM : (2 ^ M <= 2 ^ 64)%num by apply: N.pow_le_mono_r.
  apply: Wasm_int.Int64.eqm_samerepr. exists 1%Z.
  rewrite N2Z.inj_sub; last lia. rewrite N2Z.inj_add.
  change Wasm_int.Int64.modulus with 18446744073709551616%Z. change (Z.of_N (2 ^ 64)) with 18446744073709551616%Z. lia.
Qed.

(** * Numeric operators *)

(* SpecTec's [EXTEND n] sign-extends from bit [n]; WasmCert's [Unop_extend n]
   from byte [n / 8].  They agree when [n] is a multiple of 8 (Wasm only has
   8, 16 and 32, but SpecTec's syntax and typing allow any [n]). *)
Definition ext_ok (op : S.unop_) : bool :=
  match op with S.mk_unop__0 _ (S.EXTEND n) => N.eqb (n mod 8) 0 | _ => true end.

Lemma unop_tr nt op c1 cs : S.wf_num_ nt c1 -> S.fun_unop_ nt op c1 (Some cs) -> ext_ok op ->
  map tr_num cs = [:: app_unop (tr_unop op) (tr_num c1)].
Proof.
  move=> Hc E Hext. inversion E; subst;
    repeat match goal with H : S.fun_sizenn _ _ |- _ => move/F.fun_sizenn_eq: H => H; subst end.
  all: try (match goal with v : S.uN |- _ => destruct v as [a] end).
  all: cbn [map]; try rewrite -map_comp.
  all: lazymatch goal with
       | |- context[S.mk_num__0 ?t (S.iclz_ _ _)] => f_equal; exact: (@iclz_tr t _ Hc)
       | |- context[S.mk_num__0 ?t (S.ictz_ _ _)] => f_equal; exact: (@ictz_tr t _ Hc)
       | |- context[S.mk_num__0 ?t (S.ipopcnt_ _ _)] => f_equal; exact: (@ipopcnt_tr t _ Hc)
       | |- context[S.mk_num__0 S.Inn_I32 (S.extend__ _ _ _ _)] =>
           f_equal; exact: (extend_unop_tr32 (iok32 Hc) (proj1 (N.eqb_eq _ _) Hext))
       | |- context[S.mk_num__0 S.Inn_I64 (S.extend__ _ _ _ _)] =>
           f_equal; exact: (extend_unop_tr64 (iok64 Hc) (proj1 (N.eqb_eq _ _) Hext))
       | |- context[S.mk_num__1 ?t] =>
           first [exact: (@fabs_tr t _ Hc) | exact: (@fneg_tr t _ Hc) | exact: (@fsqrt_tr t _ Hc)
                 | exact: (@fceil_tr t _ Hc) | exact: (@ffloor_tr t _ Hc) | exact: (@ftrunc_tr t _ Hc)
                 | exact: (@fnearest_tr t _ Hc)]
       end.
Qed.

(* Division and remainder by zero.  SpecTec's [$idiv_] and [$irem_] have a
   clause for a zero divisor (no result) and a general clause; in Rocq the
   general clauses (signed and unsigned) also apply to 0, since [x / 0 = 0]
   in [Q], and give a result where WasmCert traps. *)
Definition divzero (op : S.binop_) (c2 : S.num_) : bool :=
  match op, c2 with
  | S.mk_binop__0 _ (S.DIV _), S.mk_num__0 _ (S.mk_uN N0)
  | S.mk_binop__0 _ (S.REM _), S.mk_num__0 _ (S.mk_uN N0) => true
  | _, _ => false
  end.

Lemma map_list_ {A : Type} {B : eqType} {C : Type} (f : B -> C) (g : A -> B) (o : option A) :
  map f (S.list_ B (S.option_map g o)) = olist (option_map (f \o g) o).
Proof. by case: o. Qed.

Lemma binop_tr nt op c1 c2 cs :
  S.wf_num_ nt c1 -> S.wf_num_ nt c2 -> S.fun_binop_ nt op c1 c2 (Some cs) -> ~~ divzero op c2 ->
  map tr_num cs = olist (app_binop (tr_binop op) (tr_num c1) (tr_num c2)).
Proof.
  move=> Hc1 Hc2 Hf Hdz. inversion Hf; subst; clear Hf;
    repeat match goal with H : S.fun_sizenn _ _ |- _ => move/F.fun_sizenn_eq: H => H; subst end.
  all: try rewrite -map_comp.
  all: lazymatch goal with
       | |- context[S.mk_num__0 ?t (S.iadd_ _ _ _)] => exact: (f_equal olist (@iadd_tr t _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.isub_ _ _ _)] => exact: (f_equal olist (@isub_tr t _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.imul_ _ _ _)] => exact: (f_equal olist (@imul_tr t _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.iand_ _ _ _)] => exact: (f_equal olist (@iand_tr t _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.ior_ _ _ _)] => exact: (f_equal olist (@ior_tr t _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.ixor_ _ _ _)] => exact: (f_equal olist (@ixor_tr t _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.ishl_ _ _ _)] => exact: (f_equal olist (@ishl_tr t _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.ishr_ _ ?sx _ _)] => exact: (f_equal olist (@ishr_tr t sx _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.irotl_ _ _ _)] => exact: (f_equal olist (@irotl_tr t _ _ Hc1 Hc2))
       | |- context[S.mk_num__0 ?t (S.irotr_ _ _ _)] => exact: (f_equal olist (@irotr_tr t _ _ Hc1 Hc2))
       | H : S.fun_idiv_ _ _ ?i1 ?i2 _ |- _ =>
           rewrite map_list_; move: Hc1 Hc2 Hdz H; case: i1 => a; case: i2 => b Hc1 Hc2 Hdz H;
           (have Hb : b <> 0%num by move=> E; rewrite E in Hdz);
           first [exact: (f_equal olist (idiv_tr32 Hc1 Hc2 Hb H))
                 | exact: (f_equal olist (idiv_tr64 Hc1 Hc2 Hb H))]
       | H : S.fun_irem_ _ _ ?i1 ?i2 _ |- _ =>
           rewrite map_list_; move: Hc1 Hc2 Hdz H; case: i1 => a; case: i2 => b Hc1 Hc2 Hdz H;
           (have Hb : b <> 0%num by move=> E; rewrite E in Hdz);
           first [exact: (f_equal olist (irem_tr32 Hc1 Hc2 Hb H))
                 | exact: (f_equal olist (irem_tr64 Hc1 Hc2 Hb H))]
       | |- context[S.mk_num__1 ?t] =>
           first [exact: (@fadd_tr t _ _ Hc1 Hc2) | exact: (@fsub_tr t _ _ Hc1 Hc2)
                 | exact: (@fmul_tr t _ _ Hc1 Hc2) | exact: (@fdiv_tr t _ _ Hc1 Hc2)
                 | exact: (@fmin_tr t _ _ Hc1 Hc2) | exact: (@fmax_tr t _ _ Hc1 Hc2)
                 | exact: (@fcopysign_tr t _ _ Hc1 Hc2)]
       end.
Qed.

(* WasmCert's result of [eqz]. *)
Definition wc_testop (v : value_num) : value_num :=
  match v with
  | VAL_int32 x => VAL_int32 (wasm_bool (app_testop_i i32m TO_eqz x))
  | VAL_int64 x => VAL_int32 (wasm_bool (app_testop_i i64m TO_eqz x))
  | _ => v
  end.

Lemma testop_tr nt op c1 c : S.wf_num_ nt c1 -> S.fun_testop_ nt op c1 (Some c) ->
  tr_num c = wc_testop (tr_num c1).
Proof.
  move=> Hc E. inversion E; subst;
    repeat match goal with H : S.fun_sizenn _ _ |- _ => move/F.fun_sizenn_eq: H => H; subst end.
  all: match goal with v : S.uN |- _ => destruct v as [a] end.
  - cbn [tr_num S.ieqz_ wc_testop app_testop_i Wasm_int.int_eqz i32m Wasm_int.Int32.Tmixin].
    rewrite res_bool_tr /tr_i32 /tr_u32. cbn [S.proj_uN_0 S.coerce S.proj_uN_0_coercion].
    rewrite eqz_tr32; last exact: (iok32 Hc).
    by case: N.eqb_spec => [->|?]; case: eqP.
  - cbn [tr_num S.ieqz_ wc_testop app_testop_i Wasm_int.int_eqz i64m Wasm_int.Int64.Tmixin].
    rewrite res_bool_tr /tr_i64 /tr_u32. cbn [S.proj_uN_0 S.coerce S.proj_uN_0_coercion].
    rewrite eqz_tr64; last exact: (iok64 Hc).
    by case: N.eqb_spec => [->|?]; case: eqP.
Qed.

Lemma relop_tr nt op c1 c2 c :
  S.wf_num_ nt c1 -> S.wf_num_ nt c2 -> S.fun_relop_ nt op c1 c2 (Some c) ->
  tr_num c = VAL_int32 (wasm_bool (app_relop (tr_relop op) (tr_num c1) (tr_num c2))).
Proof.
  move=> Hc1 Hc2 Hf. inversion Hf; subst; clear Hf; F.inv_size_rels.
  all: lazymatch goal with
       | |- context[S.mk_num__1 ?t] =>
           first [exact: (@feq_tr t _ _ Hc1 Hc2) | exact: (@fne_tr t _ _ Hc1 Hc2)
                 | exact: (@flt_tr t _ _ Hc1 Hc2) | exact: (@fgt_tr t _ _ Hc1 Hc2)
                 | exact: (@fle_tr t _ _ Hc1 Hc2) | exact: (@fge_tr t _ _ Hc1 Hc2)]
       | |- _ => idtac
       end.
  all: destruct iN_1 as [a], iN_2 as [b].
  all: first [have Ha := iok32 Hc1; have Hb := iok32 Hc2 | have Ha := iok64 Hc1; have Hb := iok64 Hc2].
  all: cbn [tr_num tr_relop app_relop S.ieq_ S.ine_]; rewrite /tr_i32 /tr_i64 /tr_u32; cbn [S.proj_uN_0].
  all: lazymatch goal with
       | H : S.fun_ilt_ _ _ _ _ _ |- _ => first [exact: (f_equal VAL_int32 (ilt_tr32 Ha Hb H)) | exact: (f_equal VAL_int32 (ilt_tr64 Ha Hb H))]
       | H : S.fun_igt_ _ _ _ _ _ |- _ => first [exact: (f_equal VAL_int32 (igt_tr32 Ha Hb H)) | exact: (f_equal VAL_int32 (igt_tr64 Ha Hb H))]
       | H : S.fun_ile_ _ _ _ _ _ |- _ => first [exact: (f_equal VAL_int32 (ile_tr32 Ha Hb H)) | exact: (f_equal VAL_int32 (ile_tr64 Ha Hb H))]
       | H : S.fun_ige_ _ _ _ _ _ |- _ => first [exact: (f_equal VAL_int32 (ige_tr32 Ha Hb H)) | exact: (f_equal VAL_int32 (ige_tr64 Ha Hb H))]
       | |- _ => (try rewrite /S.ieq_); (try rewrite /S.ine_); cbn [S.proj_uN_0]; rewrite res_bool_repr; cbn [app_relop_i];
                 (try rewrite /Wasm_int.int_ne); cbn [Wasm_int.int_eq i32m i64m Wasm_int.Int32.Tmixin Wasm_int.Int64.Tmixin];
                 first [rewrite eq_tr32 // | rewrite eq_tr64 //]
       end.
Qed.

Lemma extend_cvt_tr sx a : (a < 4294967296)%num ->
  Some (VAL_int64 (tr_i64 (S.extend__ 32%num 64%num sx (S.mk_uN a)))) =
  eval_cvt T_i64 CVO_extend (Some (tr_sx sx)) (VAL_int32 (Wasm_int.Int32.repr (Z.of_N a))).
Proof.
  move=> Ha. rewrite extend__def /tr_i64 /tr_u32. cbn [S.proj_uN_0].
  case: sx; cbn [tr_sx eval_cvt cvt_extend]; rewrite /wasm_extend_u /wasm_extend_s;
    cbn [Wasm_int.int_of_Z Wasm_int.Z_of_uint Wasm_int.Z_of_sint i32m i64m
         Wasm_int.Int32.Tmixin Wasm_int.Int64.Tmixin].
  - by rewrite Wasm_int.Int32.unsigned_repr //; change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia.
  - rewrite /Wasm_int.Int32.signed Wasm_int.Int32.unsigned_repr;
      last by change Wasm_int.Int32.max_unsigned with 4294967295%Z; lia.
    change Wasm_int.Int32.half_modulus with 2147483648%Z.
    change Wasm_int.Int32.modulus with 4294967296%Z.
    change (2 ^ (32 - 1))%num with 2147483648%num.
    case: N.ltb_spec => H; case: Coqlib.zlt => H' //; try lia.
    do 2 f_equal. apply: Wasm_int.Int64.eqm_samerepr. exists 1%Z.
    change Wasm_int.Int64.modulus with 18446744073709551616%Z.
    rewrite N2Z.inj_sub; last (change (2 ^ 32)%num with 4294967296%num; lia).
    rewrite N2Z.inj_add. change (Z.of_N (2 ^ 64)) with 18446744073709551616%Z.
    change (Z.of_N (2 ^ 32)) with 4294967296%Z. lia.
Qed.

Lemma eqm32_mod64 x : Wasm_int.Int32.eqm (x mod 18446744073709551616) x.
Proof.
  exists (- (x / 18446744073709551616) * 4294967296)%Z. have := Z.div_mod x 18446744073709551616.
  change Wasm_int.Int32.modulus with 4294967296%Z. lia.
Qed.

Lemma wrap_cvt_tr a :
  Some (VAL_int32 (tr_i32 (S.wrap__ 64%num 32%num (S.mk_uN a)))) =
  eval_cvt T_i32 CVO_wrap None (VAL_int64 (Wasm_int.Int64.repr (Z.of_N a))).
Proof.
  rewrite wrap__def /tr_i32 /tr_u32. cbn [S.proj_uN_0 eval_cvt cvt_wrap].
  rewrite /wasm_wrap. cbn [Wasm_int.int_of_Z Wasm_int.Z_of_uint i32m i64m
                           Wasm_int.Int32.Tmixin Wasm_int.Int64.Tmixin].
  do 2 f_equal. apply: Wasm_int.Int32.eqm_samerepr.
  rewrite N2Z.inj_mod Wasm_int.Int64.unsigned_repr_eq.
  change (Z.of_N (2 ^ 32)) with 4294967296%Z.
  change Wasm_int.Int64.modulus with 18446744073709551616%Z.
  apply: Wasm_int.Int32.eqm_trans; first exact: eqm32_mod.
  apply: Wasm_int.Int32.eqm_sym. exact: eqm32_mod64.
Qed.

Lemma cvtop_tr nt1 nt2 op c1 cs :
  S.wf_num_ nt1 c1 -> S.wf_cvtop__ nt1 nt2 op -> S.fun_cvtop__ nt1 nt2 op c1 (Some cs) ->
  map tr_num cs = olist (eval_cvt (tr_numtype nt2) (tr_cvtop op).1 (tr_cvtop op).2 (tr_num c1)).
Proof.
  move=> Hc Hop Hf. inversion Hf; subst; clear Hf; F.inv_size_rels.
  (* the integer extensions and wrappings that are not well-formed *)
  all: try (inversion Hop; subst;
            match goal with H : S.wf_cvtop__Inn_1_Inn_2 _ _ _ |- _ => inversion H; subst end; F.inv_size_rels;
            match goal with H : is_true _ |- _ => exfalso; move: H; cbn; discriminate end).
  all: try rewrite map_list_.
  all: try rewrite -map_comp.
  all: lazymatch goal with
       | |- context[S.extend__] =>
           case: iN_1 Hc => a Hc; exact: (f_equal olist (extend_cvt_tr _ (iok32 Hc)))
       | |- context[S.wrap__] => case: iN_1 Hc => a Hc; exact: (f_equal olist (wrap_cvt_tr a))
       | Hc : S.wf_num_ _ (S.mk_num__1 ?t1 _) |- context[S.trunc__] =>
           first [exact: (f_equal olist (@trunc__tr t1 S.Inn_I32 _ _ Hc))
                 | exact: (f_equal olist (@trunc__tr t1 S.Inn_I64 _ _ Hc))]
       | Hc : S.wf_num_ _ (S.mk_num__1 ?t1 _) |- context[S.trunc_sat__] =>
           first [exact: (f_equal olist (@trunc_sat__tr t1 S.Inn_I32 _ _ Hc))
                 | exact: (f_equal olist (@trunc_sat__tr t1 S.Inn_I64 _ _ Hc))]
       | Hc : S.wf_num_ _ (S.mk_num__0 ?t1 _) |- context[S.convert__] =>
           first [exact: (f_equal olist (@convert__tr t1 S.Fnn_F32 _ _ Hc))
                 | exact: (f_equal olist (@convert__tr t1 S.Fnn_F64 _ _ Hc))]
       | Hc : S.wf_num_ _ (S.mk_num__1 ?t1 _) |- context[S.promote__] =>
           first [exact: (@promote__tr t1 S.Fnn_F32 _ Hc) | exact: (@promote__tr t1 S.Fnn_F64 _ Hc)]
       | Hc : S.wf_num_ _ (S.mk_num__1 ?t1 _) |- context[S.demote__] =>
           first [exact: (@demote__tr t1 S.Fnn_F32 _ Hc) | exact: (@demote__tr t1 S.Fnn_F64 _ Hc)]
       | |- context[S.reinterpret__] => by rewrite /= reinterpret__tr
       end.
Qed.

(* WasmCert traps on a zero divisor. *)
Lemma divzero_none op c1 c2 : divzero op c2 ->
  app_binop (tr_binop op) (tr_num c1) (tr_num c2) = None.
Proof.
  case: op => [t o|t o] //=; case: o => //= sx; case: c2 => [t2 [[ | p]]|t2 x] //= _;
    case: c1 => [t1 y|t1 y]; case: t; case: t2; try case: t1; case: sx => //.
Qed.

Lemma in_map_single {A : eqType} {B : Type} (f : A -> B) cs c x :
  map f cs = [:: x] -> c \in cs -> f c = x.
Proof. case: cs => [//|c' [ |//]] /= [<-]. by rewrite mem_seq1 => /eqP ->. Qed.

Lemma in_map_olist {A : eqType} {B : Type} (f : A -> B) cs c o :
  map f cs = olist o -> c \in cs -> o = Some (f c).
Proof.
  case: o => [x| ]; last by case: cs.
  move=> Hm Hc. by rewrite (in_map_single Hm Hc).
Qed.

(** * Byte encodings *)

From compcert Require Memdata.

Axiom nbytes_tr : forall nt c, S.wf_num_ nt c ->
  map tr_byte (S.nbytes_ nt c) = serialise_num (tr_num c).

Axiom ibytes_tr : forall M i, S.wf_uN M i ->
  map tr_byte (S.ibytes_ M i) = Memdata.encode_int (N.to_nat (M / 8)) (Z.of_N (S.proj_uN_0 i)).

(** * Vector instructions

   WasmCert executes most SIMD instructions through opaque functions
   ([app_vunop_str], ...) and the rest through concrete ones ([app_splat_vec],
   [load_vec], ...), while SpecTec's vector semantics rests on the builtins
   [lanes_], [inv_lanes_] and [vbytes_].  There is one axiom per WasmCert SIMD
   function: a SpecTec step of a well-typed instruction that WasmCert
   implements with that function is a WasmCert step of the translation.  The
   vector stores where the two semantics genuinely disagree
   ([Vstore_disagree]) are excluded. *)

From Wasm Require Import opsem.

Inductive simd_fun : Type :=
  | SF_unop | SF_binop | SF_ternop | SF_testop | SF_shiftop
  | SF_splat | SF_extract | SF_replace
  | SF_load | SF_load_lane | SF_store | SF_store_lane.

(* The WasmCert SIMD function that implements a SpecTec vector instruction. *)
Definition simd_of (a : S.admininstr) : option simd_fun :=
  match a with
  | S.admininstr_VVUNOP _ _ | S.admininstr_VUNOP _ _ | S.admininstr_VEXTUNOP _ _ _
  | S.admininstr_VCVTOP _ _ _ => Some SF_unop
  | S.admininstr_VVBINOP _ _ | S.admininstr_VBINOP _ _ | S.admininstr_VRELOP _ _
  | S.admininstr_VSWIZZLE _ | S.admininstr_VSHUFFLE _ _ | S.admininstr_VEXTBINOP _ _ _
  | S.admininstr_VNARROW _ _ _ => Some SF_binop
  | S.admininstr_VVTERNOP _ _ => Some SF_ternop
  | S.admininstr_VVTESTOP _ _ | S.admininstr_VTESTOP _ _ | S.admininstr_VBITMASK _ => Some SF_testop
  | S.admininstr_VSHIFTOP _ _ => Some SF_shiftop
  | S.admininstr_VSPLAT _ => Some SF_splat
  | S.admininstr_VEXTRACT_LANE _ _ _ => Some SF_extract
  | S.admininstr_VREPLACE_LANE _ _ => Some SF_replace
  | S.admininstr_VLOAD _ _ _ => Some SF_load
  | S.admininstr_VLOAD_LANE _ _ _ _ => Some SF_load_lane
  | S.admininstr_VSTORE _ _ => Some SF_store
  | S.admininstr_VSTORE_LANE _ _ _ _ => Some SF_store_lane
  | _ => None
  end.

(* A redex of operands [vs] and a well-typed, well-formed vector instruction
   [i] that WasmCert implements with [k]. *)
Definition simd_redex (k : simd_fun) (vs : seq S.val) (i : S.instr) (es : seq S.admininstr) : Prop :=
  es = map S.admininstr_val vs ++ [:: S.admininstr_instr i] /\
  simd_of (S.admininstr_instr i) = Some k /\
  (exists C ft, S.Instr_ok C i ft) /\ List.Forall S.wf_admininstr es.

(* The memory of the current module exists. *)
Definition mem_exists (s : S.store) (f : S.frame) : Prop :=
  (0 < N.of_nat (size (S.MEMS (S.frame_MODULE f))))%num /\
  (S.lookup_total (S.MEMS (S.frame_MODULE f)) 0 < N.of_nat (size (S.store_MEMS s)))%num.

Definition vbytesz (s : S.store) (f : S.frame) : N :=
  N.of_nat (size (S.BYTES (F.fun_mem_f (S.mk_state s f) (S.mk_uN 0)))).

Definition vaddr (i : N) (ao : S.memarg) : N := (i + S.proj_uN_0 (S.OFFSET ao))%num.

(* The vector stores where SpecTec and WasmCert disagree: a store that
   succeeds out of bounds (no bounds premise in vstore_val / vstore_lane_val),
   and vstore_lane-oob, which adds the lane width in bits instead of bytes. *)
Inductive Vstore_disagree : S.config -> S.config -> Prop :=
  | vd_store_oob s f i c ao z' :
      (vbytesz s f < vaddr i ao + 16)%num ->
      Vstore_disagree (S.mk_config (S.mk_state s f)
                         [:: S.admininstr_CONST S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN i));
                             S.admininstr_VCONST S.V128 c; S.admininstr_VSTORE S.V128 ao])
                      (S.mk_config z' [::])
  | vd_store_lane_oob s f i c n ao j z' :
      (vbytesz s f < vaddr i ao + n / 8)%num ->
      Vstore_disagree (S.mk_config (S.mk_state s f)
                         [:: S.admininstr_CONST S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN i));
                             S.admininstr_VCONST S.V128 c; S.admininstr_VSTORE_LANE S.V128 (S.mk_sz n) ao j])
                      (S.mk_config z' [::])
  | vd_store_lane_trap s f i c n ao j :
      (vaddr i ao + n / 8 <= vbytesz s f)%num ->
      Vstore_disagree (S.mk_config (S.mk_state s f)
                         [:: S.admininstr_CONST S.I32 (S.mk_num__0 S.Inn_I32 (S.mk_uN i));
                             S.admininstr_VCONST S.V128 c; S.admininstr_VSTORE_LANE S.V128 (S.mk_sz n) ao j])
                      (S.mk_config (S.mk_state s f) [:: S.admininstr_TRAP]).

Axiom simd_unop_tr : forall vs i es es', simd_redex SF_unop vs i es ->
  S.Step_pure es es' -> reduce_simple (tr_admins es) (tr_admins es').
Axiom simd_binop_tr : forall vs i es es', simd_redex SF_binop vs i es ->
  S.Step_pure es es' -> reduce_simple (tr_admins es) (tr_admins es').
Axiom simd_ternop_tr : forall vs i es es', simd_redex SF_ternop vs i es ->
  S.Step_pure es es' -> reduce_simple (tr_admins es) (tr_admins es').
Axiom simd_testop_tr : forall vs i es es', simd_redex SF_testop vs i es ->
  S.Step_pure es es' -> reduce_simple (tr_admins es) (tr_admins es').
Axiom simd_shiftop_tr : forall vs i es es', simd_redex SF_shiftop vs i es ->
  S.Step_pure es es' -> reduce_simple (tr_admins es) (tr_admins es').
Axiom simd_splat_tr : forall vs i es es', simd_redex SF_splat vs i es ->
  S.Step_pure es es' -> reduce_simple (tr_admins es) (tr_admins es').
Axiom simd_extract_tr : forall vs i es es', simd_redex SF_extract vs i es ->
  S.Step_pure es es' -> reduce_simple (tr_admins es) (tr_admins es').
Axiom simd_replace_tr : forall vs i es es', simd_redex SF_replace vs i es ->
  S.Step_pure es es' -> reduce_simple (tr_admins es) (tr_admins es').

Axiom simd_load_tr : forall hfc ho hs s f vs i es es', simd_redex SF_load vs i es -> mem_exists s f ->
  S.Step_read (S.mk_config (S.mk_state s f) es) es' ->
  @reduce hfc memory_tr ho hs (tr_store s) (tr_frame f) (tr_admins es) hs (tr_store s) (tr_frame f) (tr_admins es').
Axiom simd_load_lane_tr : forall hfc ho hs s f vs i es es', simd_redex SF_load_lane vs i es -> mem_exists s f ->
  S.Step_read (S.mk_config (S.mk_state s f) es) es' ->
  @reduce hfc memory_tr ho hs (tr_store s) (tr_frame f) (tr_admins es) hs (tr_store s) (tr_frame f) (tr_admins es').
Axiom simd_store_tr : forall hfc ho hs s f vs i es s' f' es', simd_redex SF_store vs i es -> mem_exists s f ->
  S.Step (S.mk_config (S.mk_state s f) es) (S.mk_config (S.mk_state s' f') es') ->
  ~ Vstore_disagree (S.mk_config (S.mk_state s f) es) (S.mk_config (S.mk_state s' f') es') ->
  @reduce hfc memory_tr ho hs (tr_store s) (tr_frame f) (tr_admins es) hs (tr_store s') (tr_frame f') (tr_admins es').
Axiom simd_store_lane_tr : forall hfc ho hs s f vs i es s' f' es', simd_redex SF_store_lane vs i es -> mem_exists s f ->
  S.Step (S.mk_config (S.mk_state s f) es) (S.mk_config (S.mk_state s' f') es') ->
  ~ Vstore_disagree (S.mk_config (S.mk_state s f) es) (S.mk_config (S.mk_state s' f') es') ->
  @reduce hfc memory_tr ho hs (tr_store s) (tr_frame f) (tr_admins es) hs (tr_store s') (tr_frame f') (tr_admins es').

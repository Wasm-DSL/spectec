(* Conversion between SpecTec's fN(N) and Flocq's IEEE 754 binary_float.

   SpecTec (1-syntax.spectec):
     NORM m e    = (1 + m * 2^-M) * 2^e     with m < 2^M, 2 - 2^(E-1) <= e <= 2^(E-1) - 1
     SUBNORM m   = (0 + m * 2^-M) * 2^emin  with m < 2^M, emin = 2 - 2^(E-1)
     INF, NAN m  (1 <= m < 2^M)
   Flocq (IEEE754.Binary):
     B754_finite s mx ex = (-1)^s * mx * 2^ex  (integer significand mx, prec digits)
     with prec = M + 1 and emax = 2^(E-1).
   So NORM m e  <->  mx = 2^M + m, ex = e - M,
      SUBNORM m <->  mx = m,       ex = emin - M = 3 - emax - prec  (Flocq's emin),
   and SUBNORM 0 is Flocq's B754_zero. *)

From Stdlib Require Import ZArith NArith Lia Bool Eqdep_dec.
From Flocq Require Import Core.Zaux Core.Digits IEEE754.Binary IEEE754.Bits.
From WasmSpectec Require Import wasm.

Open Scope Z_scope.

Arguments B754_zero {prec emax}.
Arguments B754_infinity {prec emax}.
Arguments B754_nan {prec emax}.
Arguments B754_finite {prec emax}.

(** * Format parameters *)

Definition fprec (N : res_N) : Z := Z.of_N (fun_M N) + 1.
Definition femax (N : res_N) : Z := 2 ^ (Z.of_N (E N) - 1).

Definition flocq_float (N : res_N) : Type := binary_float (fprec N) (femax N).

(** * fN -> Flocq *)

Definition mk_finite (N : res_N) (s : bool) (mx : positive) (ex : Z) : option (flocq_float N) :=
  match bool_dec (SpecFloat.bounded (fprec N) (femax N) mx ex) true with
  | left H => Some (B754_finite s mx ex H)
  | right _ => None
  end.

Definition mk_nan (N : res_N) (s : bool) (pl : positive) : option (flocq_float N) :=
  match bool_dec (nan_pl (fprec N) pl) true with
  | left H => Some (B754_nan s pl H)
  | right _ => None
  end.

Definition fNmag_to_flocq (N : res_N) (s : bool) (x : fNmag) : option (flocq_float N) :=
  match x with
  | NORM m e =>
      mk_finite N s (Z.to_pos (2 ^ Z.of_N (fun_M N) + Z.of_N m)) (e - Z.of_N (fun_M N))
  | SUBNORM m =>
      (* Flocq would also accept m = 2^M here (as the smallest normal), so check
         the bound explicitly to stay faithful to wf_fNmag. *)
      if (m <? 2 ^ fun_M N)%N then
        match m with
        | N0 => Some (B754_zero s)
        | Npos p => mk_finite N s p (SpecFloat.emin (fprec N) (femax N))
        end
      else None
  | INF => Some (B754_infinity s)
  | NAN m =>
      match m with
      | N0 => None
      | Npos p => mk_nan N s p
      end
  end.

(** Returns [None] exactly on ill-formed inputs (see [fN_to_flocq_wf] below). *)
Definition fN_to_flocq (N : res_N) (f : fN) : option (flocq_float N) :=
  match f with
  | POS x => fNmag_to_flocq N false x
  | NEG x => fNmag_to_flocq N true x
  end.

(** * Flocq -> fN *)

Definition sign_fN (s : bool) (x : fNmag) : fN := if s then NEG x else POS x.

Definition flocq_to_fN (N : res_N) (b : flocq_float N) : fN :=
  match b with
  | B754_zero s => sign_fN s (SUBNORM 0)
  | B754_infinity s => sign_fN s INF
  | B754_nan s pl _ => sign_fN s (NAN (Npos pl))
  | B754_finite s mx ex _ =>
      if Zpos mx <? 2 ^ Z.of_N (fun_M N)
      then sign_fN s (SUBNORM (Npos mx))
      else sign_fN s (NORM (Z.to_N (Zpos mx - 2 ^ Z.of_N (fun_M N))) (ex + Z.of_N (fun_M N)))
  end.

(** * Concrete formats *)

Definition fN_to_binary32 : fN -> option binary32 := fN_to_flocq 32.
Definition fN_to_binary64 : fN -> option binary64 := fN_to_flocq 64.
Definition binary32_to_fN : binary32 -> fN := flocq_to_fN 32.
Definition binary64_to_fN : binary64 -> fN := flocq_to_fN 64.

(** Total version, for use on well-formed values (where it never hits the default). *)
Definition fN_to_flocq_total (N : res_N) (f : fN) : flocq_float N :=
  match fN_to_flocq N f with
  | Some b => b
  | None => B754_zero false
  end.

(** * Round-trip lemmas *)

Lemma mk_finite_Some N s mx ex b :
  mk_finite N s mx ex = Some b ->
  exists H, b = B754_finite s mx ex H.
Proof.
  unfold mk_finite. destruct bool_dec as [H|H]; intro Heq; [ |discriminate].
  injection Heq as <-. now exists H.
Qed.

Lemma mk_finite_eq N s mx ex H :
  mk_finite N s mx ex = Some (B754_finite s mx ex H).
Proof.
  unfold mk_finite. destruct bool_dec as [H'|H']; [ |congruence].
  f_equal. f_equal. apply UIP_dec, bool_dec.
Qed.

Lemma mk_nan_Some N s pl b :
  mk_nan N s pl = Some b ->
  exists H, b = B754_nan s pl H.
Proof.
  unfold mk_nan. destruct bool_dec as [H|H]; intro Heq; [ |discriminate].
  injection Heq as <-. now exists H.
Qed.

Lemma mk_nan_eq N s pl H :
  mk_nan N s pl = Some (B754_nan s pl H).
Proof.
  unfold mk_nan. destruct bool_dec as [H'|H']; [ |congruence].
  f_equal. f_equal. apply UIP_dec, bool_dec.
Qed.

Lemma pow2_pos (k : N) : 0 < 2 ^ Z.of_N k.
Proof. apply Z.pow_pos_nonneg; lia. Qed.

Lemma Nltb_pow2 (m k : N) : (m <? 2 ^ k)%N = (Z.of_N m <? 2 ^ Z.of_N k).
Proof.
  apply eq_iff_eq_true. rewrite N.ltb_lt, Z.ltb_lt, N2Z.inj_lt, N2Z.inj_pow. reflexivity.
Qed.

Theorem fN_to_flocq_inv (N : res_N) (f : fN) (b : flocq_float N) :
  fN_to_flocq N f = Some b -> flocq_to_fN N b = f.
Proof.
  pose proof (pow2_pos (fun_M N)) as HP.
  assert (Hmag : forall s x, fNmag_to_flocq N s x = Some b -> flocq_to_fN N b = sign_fN s x).
  { intros s [m e | m | | m]; cbn [fNmag_to_flocq].
    - intro Hb. apply mk_finite_Some in Hb as [H ->]. cbn [flocq_to_fN].
      rewrite Z2Pos.id by lia.
      replace (2 ^ Z.of_N (fun_M N) + Z.of_N m <? 2 ^ Z.of_N (fun_M N)) with false
        by (symmetry; apply Z.ltb_ge; lia).
      do 2 f_equal; [ |lia].
      replace (2 ^ Z.of_N (fun_M N) + Z.of_N m - 2 ^ Z.of_N (fun_M N)) with (Z.of_N m) by lia.
      apply N2Z.id.
    - rewrite Nltb_pow2. destruct (Z.of_N m <? 2 ^ Z.of_N (fun_M N)) eqn:Hlt; [ |discriminate].
      destruct m as [ |p].
      + intro Hb. injection Hb as <-. reflexivity.
      + intro Hb. apply mk_finite_Some in Hb as [H ->]. cbn [flocq_to_fN]. cbn [Z.of_N] in Hlt.
        now rewrite Hlt.
    - intro Hb. injection Hb as <-. reflexivity.
    - destruct m as [ |p]; [discriminate| ].
      intro Hb. apply mk_nan_Some in Hb as [H ->]. reflexivity. }
  destruct f as [x|x]; apply Hmag.
Qed.

(** Digits of a positive below 2^M. *)
Lemma digits_lt_pow2 (p : positive) (k : Z) :
  0 <= k -> (Zpos p < 2 ^ k <-> Zpos (SpecFloat.digits2_pos p) <= k).
Proof.
  intro Hk. rewrite Zpos_digits2_pos. split.
  - intro H. apply (Zdigits_le_Zpower radix2). simpl. lia.
  - intro H. apply (Zpower_gt_Zdigits radix2) in H. simpl in H. lia.
Qed.

Theorem flocq_to_fN_inv (N : res_N) (b : flocq_float N) :
  fN_to_flocq N (flocq_to_fN N b) = Some b.
Proof.
  pose proof (pow2_pos (fun_M N)) as HP.
  assert (Hsign : forall s x, fN_to_flocq N (sign_fN s x) = fNmag_to_flocq N s x)
    by (now intros [] x).
  destruct b as [s | s | s pl H | s mx ex H]; cbn [flocq_to_fN];
    try (rewrite Hsign; cbn [fNmag_to_flocq]).
  - rewrite Nltb_pow2. cbn [Z.of_N]. now replace (0 <? _) with true by (symmetry; apply Z.ltb_lt; lia).
  - reflexivity.
  - apply mk_nan_eq.
  - destruct (Zpos mx <? 2 ^ Z.of_N (fun_M N)) eqn:Hlt; rewrite Hsign; cbn [fNmag_to_flocq].
    + rewrite Nltb_pow2. cbn [Z.of_N]. rewrite Hlt.
      (* A subnormal-sized significand forces the minimal exponent. *)
      assert (Hex : ex = SpecFloat.emin (fprec N) (femax N)).
      { apply Z.ltb_lt, digits_lt_pow2 in Hlt; [ |lia].
        pose proof H as H'. unfold SpecFloat.bounded, SpecFloat.canonical_mantissa in H'.
        apply andb_prop in H' as [Hc _]. apply Z.eqb_eq in Hc.
        unfold SpecFloat.fexp, SpecFloat.emin, fprec in *. lia. }
      subst ex. apply mk_finite_eq.
    + apply Z.ltb_ge in Hlt.
      replace (Z.to_pos (2 ^ Z.of_N (fun_M N) + Z.of_N (Z.to_N (Zpos mx - 2 ^ Z.of_N (fun_M N)))))
        with mx by (rewrite Z2N.id by lia; now replace (_ + _) with (Zpos mx) by lia).
      replace (ex + Z.of_N (fun_M N) - Z.of_N (fun_M N)) with ex by lia.
      apply mk_finite_eq.
Qed.

(** * Well-formedness corresponds exactly to Flocq's validity *)

Lemma pow2_E (N : res_N) :
  1 <= Z.of_N (E N) ->
  Z.of_N (2 ^ Z.to_N (Z.of_N (E N) - Z.of_N 1))%N = femax N.
Proof.
  intro HE. unfold femax. rewrite N2Z.inj_pow, Z2N.id; simpl; lia.
Qed.

Lemma wf_fNmag_Z (N : res_N) (x : fNmag) :
  1 <= Z.of_N (E N) ->
  wf_fNmag N x <->
  match x with
  | NORM m e => Z.of_N m < 2 ^ Z.of_N (fun_M N) /\ 2 - femax N <= e <= femax N - 1
  | SUBNORM m => Z.of_N m < 2 ^ Z.of_N (fun_M N)
  | INF => True
  | NAN m => 1 <= Z.of_N m < 2 ^ Z.of_N (fun_M N)
  end.
Proof.
  intro HE. split.
  - intro Hwf. inversion Hwf as [N' m e Hc | N' e m Hc | N' | N' m Hc]; subst; clear Hwf; unfold is_true in *;
      repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
      repeat match goal with
        | H : N.ltb _ _ = true |- _ => apply N.ltb_lt, N2Z.inj_lt in H; rewrite N2Z.inj_pow in H
        | H : N.leb _ _ = true |- _ => apply N.leb_le, N2Z.inj_le in H
        | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
        end;
      rewrite ?pow2_E in * by exact HE; cbn [Z.of_N] in *; lia.
  - destruct x as [m e | m | | m]; intro Hx.
    + constructor. rewrite Nltb_pow2, !pow2_E by exact HE.
      apply andb_true_intro; split; [now apply Z.ltb_lt| ].
      apply andb_true_intro; split; apply Z.leb_le; cbn [Z.of_N]; lia.
    + apply (fNmag_case_1 N (2 - femax N)). rewrite Nltb_pow2, pow2_E by exact HE.
      apply andb_true_intro; split; [now apply Z.ltb_lt| ]. apply (ssrbool.introT eqtype.eqP); reflexivity.
    + constructor.
    + constructor. rewrite Nltb_pow2.
      apply andb_true_intro; split; [apply N.leb_le, N2Z.inj_le; cbn [Z.of_N]; lia|now apply Z.ltb_lt].
Qed.

Lemma femax_ge_2 (N : res_N) : 2 <= Z.of_N (E N) -> 2 <= femax N.
Proof.
  intro HE. unfold femax.
  replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia.
Qed.

Theorem fNmag_to_flocq_wf (N : res_N) (s : bool) (x : fNmag) :
  2 <= Z.of_N (E N) ->
  wf_fNmag N x <-> fNmag_to_flocq N s x <> None.
Proof.
  intro HE. pose proof (femax_ge_2 N HE) as Hemax.
  pose proof (pow2_pos (fun_M N)) as HP.
  rewrite wf_fNmag_Z; [ |lia].
  destruct x as [m e | m | | m]; cbn [fNmag_to_flocq].
  - (* NORM: the significand 2^M + m has exactly prec digits iff m < 2^M *)
    set (mx := Z.to_pos (2 ^ Z.of_N (fun_M N) + Z.of_N m)).
    assert (Hmx : Zpos mx = 2 ^ Z.of_N (fun_M N) + Z.of_N m) by (apply Z2Pos.id; lia).
    assert (Hge : Z.of_N (fun_M N) + 1 <= Zpos (SpecFloat.digits2_pos mx)).
    { rewrite Zpos_digits2_pos.
      assert (Z.of_N (fun_M N) < Zdigits radix2 (Zpos mx))
        by (apply (Zdigits_gt_Zpower radix2); simpl; lia).
      lia. }
    assert (Hdig : Zpos (SpecFloat.digits2_pos mx) = Z.of_N (fun_M N) + 1 <->
                   Z.of_N m < 2 ^ Z.of_N (fun_M N)).
    { rewrite Zpos_digits2_pos. split.
      - intro Hd. pose proof (Zdigits_correct radix2 (Zpos mx)) as [_ Hc].
        rewrite Hd, Z.pow_add_r in Hc; simpl in *; lia.
      - intro Hm. apply (Zdigits_unique radix2). simpl.
        rewrite Z.add_simpl_r, Z.pow_add_r; lia. }
    unfold mk_finite. destruct bool_dec as [H|H]; split; try congruence.
    + intros _. unfold SpecFloat.bounded, SpecFloat.canonical_mantissa in H.
      apply andb_prop in H as [Hc Hle]. apply Z.eqb_eq in Hc. apply Z.leb_le in Hle.
      unfold SpecFloat.fexp, SpecFloat.emin, fprec in *. fold mx in Hc. split; [apply Hdig| ]; lia.
    + intros [Hm He] _. apply H.
      unfold SpecFloat.bounded, SpecFloat.canonical_mantissa. fold mx.
      apply Hdig in Hm. rewrite Hm.
      apply andb_true_intro; split; [apply Z.eqb_eq|apply Z.leb_le];
        unfold SpecFloat.fexp, SpecFloat.emin, fprec; lia.
  - (* SUBNORM *)
    rewrite Nltb_pow2.
    destruct (Z.of_N m <? 2 ^ Z.of_N (fun_M N)) eqn:Hlt; split; try congruence.
    + intros _. destruct m as [ |p]; [congruence| ].
      unfold mk_finite. destruct bool_dec as [H|H]; [congruence| ].
      exfalso. apply H. simpl in Hlt. apply Z.ltb_lt, digits_lt_pow2 in Hlt; [ |lia].
      unfold SpecFloat.bounded, SpecFloat.canonical_mantissa.
      apply andb_true_intro; split; [apply Z.eqb_eq|apply Z.leb_le];
        unfold SpecFloat.fexp, SpecFloat.emin, fprec; lia.
    + intros _. now apply Z.ltb_lt.
    + intro Hm. apply Z.ltb_lt in Hm. congruence.
  - split; intros _; [discriminate|exact I].
  - destruct m as [ |p]; cbn [Z.of_N]; [split; [intros [? ?]; lia|congruence]| ].
    unfold mk_nan, nan_pl, fprec. destruct bool_dec as [H|H]; split; try congruence.
    + intros _. apply Z.ltb_lt in H.
      assert (Zpos p < 2 ^ Z.of_N (fun_M N)) by (apply digits_lt_pow2; lia). lia.
    + intros Hp _. apply H, Z.ltb_lt.
      assert (Zpos (SpecFloat.digits2_pos p) <= Z.of_N (fun_M N))
        by (apply digits_lt_pow2; lia). lia.
Qed.

Theorem fN_to_flocq_wf (N : res_N) (f : fN) :
  2 <= Z.of_N (E N) ->
  wf_fN N f <-> fN_to_flocq N f <> None.
Proof.
  intro HE. destruct f as [x|x]; simpl; rewrite <- fNmag_to_flocq_wf by exact HE;
    split; [now inversion 1 | now constructor | now inversion 1 | now constructor].
Qed.

Corollary flocq_to_fN_wf (N : res_N) (b : flocq_float N) :
  2 <= Z.of_N (E N) -> wf_fN N (flocq_to_fN N b).
Proof.
  intro HE. apply fN_to_flocq_wf; [exact HE| ]. rewrite flocq_to_fN_inv. discriminate.
Qed.

Corollary fN_to_flocq_total_inv (N : res_N) (f : fN) :
  2 <= Z.of_N (E N) -> wf_fN N f -> flocq_to_fN N (fN_to_flocq_total N f) = f.
Proof.
  intros HE Hwf. apply fN_to_flocq_wf in Hwf; [ |exact HE].
  unfold fN_to_flocq_total. destruct (fN_to_flocq N f) eqn:Hf; [ |congruence].
  now apply fN_to_flocq_inv.
Qed.

(** Specialisations: f32 <-> binary32 and f64 <-> binary64 are bijections on wf values. *)

Corollary fN_to_binary32_wf (f : fN) : wf_fN 32 f <-> fN_to_binary32 f <> None.
Proof. apply fN_to_flocq_wf. vm_compute. discriminate. Qed.

Corollary fN_to_binary64_wf (f : fN) : wf_fN 64 f <-> fN_to_binary64 f <> None.
Proof. apply fN_to_flocq_wf. vm_compute. discriminate. Qed.

Corollary binary32_to_fN_inv (b : binary32) : fN_to_binary32 (binary32_to_fN b) = Some b.
Proof. exact (flocq_to_fN_inv 32 b). Qed.

Corollary binary64_to_fN_inv (b : binary64) : fN_to_binary64 (binary64_to_fN b) = Some b.
Proof. exact (flocq_to_fN_inv 64 b). Qed.

(** * Sanity checks against the IEEE 754 bit encodings *)

(* +1.0 = 0x3F800000 *)
Example one_f32 :
  option_map bits_of_b32 (fN_to_binary32 (POS (NORM 0 0))) = Some 1065353216.
Proof. vm_compute. reflexivity. Qed.

(* -0.0 = 0x80000000 *)
Example negzero_f32 :
  option_map bits_of_b32 (fN_to_binary32 (NEG (SUBNORM 0))) = Some 2147483648.
Proof. vm_compute. reflexivity. Qed.

(* smallest positive subnormal = 0x00000001 *)
Example min_subnorm_f32 :
  option_map bits_of_b32 (fN_to_binary32 (POS (SUBNORM 1))) = Some 1.
Proof. vm_compute. reflexivity. Qed.

(* canonical NaN 0x7FC00000 has payload canon_ 32 = 2^22 *)
Example canon_nan_f32 :
  binary32_to_fN (b32_of_bits 2143289344) = POS (NAN (canon_ 32)).
Proof. vm_compute. reflexivity. Qed.

(* +inf in f64 = 0x7FF0000000000000 *)
Example inf_f64 :
  option_map bits_of_b64 (fN_to_binary64 (POS INF)) = Some 9218868437227405312.
Proof. vm_compute. reflexivity. Qed.

(* largest finite f64 = 0x7FEFFFFFFFFFFFFF *)
Example max_f64 :
  option_map bits_of_b64 (fN_to_binary64 (POS (NORM (2 ^ 52 - 1) 1023))) = Some 9218868437227405311.
Proof. vm_compute. reflexivity. Qed.

(* Ill-formed values are rejected. *)
Example bad_subnorm_f32 : fN_to_binary32 (POS (SUBNORM (2 ^ 23))) = None.
Proof. vm_compute. reflexivity. Qed.
Example bad_exp_f32 : fN_to_binary32 (POS (NORM 0 128)) = None.
Proof. vm_compute. reflexivity. Qed.

(* Note: $fone(N) = POS (NORM 1 0) is 1 + 2^-M, not 1.0 (0x3F800001, not 0x3F800000). *)
Example fone_f32 :
  option_map bits_of_b32 (fN_to_binary32 (POS (NORM 1 0))) = Some 1065353217.
Proof. vm_compute. reflexivity. Qed.

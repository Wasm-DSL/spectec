# prove-H07 (bundle20 progress port, proof batch H07)

Targets (TypeProgress.lean:631-697): `Zquot_ge_inv`, `wf_uN_lt'`, `signed_nonzero`, `lt_wf_uN`, `inv_signed_wf`, `idiv_total`, `irem_total`, `ilt_total`, `igt_total`, `ile_total`, `ige_total`, `idiv_wf`, `wf_uN_mk_proj`, `wf_fN_num_`. ALL 14 PROVED.
No repo file was edited. Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H07/`. Only my own log file was written inside the target dir (plus the safety-check output files the check script itself creates in `claude-logging/safety-checks/`).

## Safety check at START
```
safety check [prove-H07] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T123254.174736664Z-prove-H07-1456110.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- `Work.lean` (scratch): header of each target copied verbatim from TypeProgress.lean, theorem renamed `<name>_proof`, plus the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` for each of the 14. Negative control (`Neg.lean`: a statement with `fun_idiv_` in place of `fun_irem_`) correctly FAILS the guard, so the guard is live. `Work.lean` compiles: no errors (only a naming-style linter warning for the scratch name `wf_fN_num__proof`).
- `Head.lean` (scratch): merge simulation = the first 697 lines of the real TypeProgress.lean (everything up to and including the statement of `wf_fN_num_`, i.e. every declaration before and including my batch) with the 14 proof blocks substituted for `:= sorry`, closed by `end TLC`, compiled with `lake env lean` against the same imports. It has NO errors; the only `sorry` warnings are the other (not-mine) lemmas that are still `sorry`. This also checks the ordering rule: the proofs use only declarations earlier in the file or imported ones.
- One Lean process at a time, `lake env lean` only (never `lake build`); each run took about 2-3 s.
- `#print axioms` (in Head.lean) shows the dependencies:
```
'TLC.Zquot_ge_inv' depends on axioms: [propext, Quot.sound]
'TLC.wf_uN_lt'' depends on axioms: [propext, Quot.sound]
'TLC.signed_nonzero' depends on axioms: [propext, Quot.sound]
'TLC.lt_wf_uN' depends on axioms: [propext, Quot.sound]
'TLC.inv_signed_wf' depends on axioms: [propext, Quot.sound]
'TLC.idiv_total' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, TLC.truncz_quot]
'TLC.irem_total' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, TLC.truncz_quot]
'TLC.ilt_total' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.igt_total' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.ile_total' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.ige_total' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.idiv_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.wf_uN_mk_proj' does not depend on any axioms
'TLC.wf_fN_num_' depends on axioms: [propext]
```
  `sorryAx` appears exactly where a proof uses an earlier still-`sorry` lemma (listed per target below); `TLC.truncz_quot` is the project axiom of HelperLemmas (mirrors Rocq `axioms.v`; Rocq's own proofs of `idiv_total`/`irem_total` also rewrite with `truncz_quot`). No `sorry`, `admit`, `native_decide`, or new axiom was written.

## Results

### `Zquot_ge_inv` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): none.
Notes: Rocq structure kept (cases b = 1 / b = -1 / |b| >= 2). Third case: `Int.natAbs_tdiv` gives |a tdiv b| = |a| / |b| on Nat, `Nat.div_le_div_left` bounds it by |a| / 2, then omega (replaces Rocq's Z.quot_le_compat_l / Z.quot_le_mono / Z.quot_lt).
```lean
  intro Hb Hp Ha Hge
  have Ha' := abs_le.mp Ha
  have Hcase : b = 1 ∨ b = -1 ∨ 2 ≤ |b| := by
    rcases lt_trichotomy b 0 with h | h | h
    · rw [abs_of_neg h]; omega
    · exact absurd h Hb
    · rw [abs_of_pos h]; omega
  rcases Hcase with Hb1 | Hbm1 | Hb2
  · subst Hb1
    rw [Int.tdiv_one] at Hge
    left
    exact ⟨rfl, by omega⟩
  · subst Hbm1
    right
    refine ⟨rfl, ?_⟩
    have Hop : Int.tdiv a (-1) = - Int.tdiv a 1 := Int.tdiv_neg a 1
    rw [Hop, Int.tdiv_one] at Hge
    omega
  · exfalso
    have H1 : (Int.tdiv a b).natAbs = Int.natAbs a / Int.natAbs b := Int.natAbs_tdiv a b
    rw [Int.abs_eq_natAbs] at Ha Hb2
    have H2 : Int.natAbs a / Int.natAbs b ≤ Int.natAbs a / 2 :=
      Nat.div_le_div_left (by omega) (by omega)
    omega
```

### `wf_uN_lt'` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): none.
Notes: Uses `iswf_uN_proj_lt` (wasm2.0.lean) instead of the still-sorry `wf_uN_lt`, so no sorry dependency.
```lean
  intro H
  exact iswf_uN_proj_lt H
```

### `signed_nonzero` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): none.
Notes: Rocq's inversion becomes `cases H` (the two constructors have ONE binder slot each: the premise; v_N and i are inductive parameters). Uses `iswf_two_pow_cast` (wasm2.0.lean) to align `(2:Int)^v_N` with the Nat power, then omega.
```lean
  intro H Hi
  cases H with
  | fun_signed__case_0 h => omega
  | fun_signed__case_1 h =>
    have h2 := h.2
    simp only [iswf_two_pow_cast] at *
    omega
```

### `lt_wf_uN` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): none.
Notes: Uses `iswf_uN_of_lt` (wasm2.0.lean).
```lean
  intro H
  exact iswf_uN_of_lt H
```

### `inv_signed_wf` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): none.
Notes: Uses `iswf_inv_signed` (wasm2.0.lean).
```lean
  intro H
  exact iswf_inv_signed H
```

### `idiv_total` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): `signed_total`, `invsigned_total`, `Zquot_abs_le`.
Earlier lemmas of this same batch used (proved here, before it in the file): `wf_uN_lt'`, `signed_nonzero`, `lt_wf_uN`, `inv_signed_wf`, `Zquot_ge_inv`.
Notes: Follows Rocq: split sx; i2 = 0 gives case_0/case_2; unsigned case_1 via truncz_quot + Int.tdiv_nonneg/Int.tdiv_le_self; signed: signed_total on both operands, signed_nonzero, by_cases tdiv z1 z2 < P; < P branch uses Zquot_abs_le + invsigned_total + inv_signed_wf (fun_idiv__case_4); >= P branch uses Zquot_ge_inv and fun_idiv__case_3 (the Rat equation closed by push_cast; simp). Both operands are destructured (`obtain ⟨n1⟩ := i1`) so `proj_uN_0 (mk_uN n)` reduces (with i1 a variable, `simp only [proj_uN_0]` produces `i1.1`, which breaks `rw [truncz_quot ..]`). Uses project axiom `truncz_quot` (HelperLemmas, mirrors axioms.v), as Rocq does.
```lean
  intro Hw1 Hw2
  have Hl1 := wf_uN_lt' _ _ Hw1
  have Hl2 := wf_uN_lt' _ _ Hw2
  obtain ⟨n1⟩ := i1
  obtain ⟨n2⟩ := i2
  simp only [proj_uN_0] at Hl1 Hl2
  cases v_sx with
  | U =>
    cases n2 with
    | zero => exact ⟨_, fun_idiv_.fun_idiv__case_0 _ _⟩
    | succ p2 =>
      refine ⟨_, fun_idiv_.fun_idiv__case_1 _ _ _ ?_⟩
      apply lt_wf_uN
      have Hq := truncz_quot (n1 : Int) ((p2 + 1 : Nat) : Int) (by omega)
      simp only [Int.cast_natCast] at Hq
      simp only [proj_uN_0]
      rw [Hq]
      have Hq0 : 0 ≤ Int.tdiv (n1 : Int) ((p2 + 1 : Nat) : Int) :=
        Int.tdiv_nonneg (by omega) (by omega)
      have Hq1 : Int.tdiv (n1 : Int) ((p2 + 1 : Nat) : Int) ≤ (n1 : Int) :=
        Int.tdiv_le_self _ (by omega)
      omega
  | S =>
    cases n2 with
    | zero => exact ⟨_, fun_idiv_.fun_idiv__case_2 _ _⟩
    | succ p2 =>
      obtain ⟨z1, Hs1, Hlo1, Hhi1⟩ := signed_total v_N n1 Hl1
      obtain ⟨z2, Hs2, Hlo2, Hhi2⟩ := signed_total v_N (p2 + 1) Hl2
      have Hz2 : z2 ≠ 0 := signed_nonzero _ _ _ Hs2 (by omega)
      have HPp : 0 < 2 ^ (v_N - 1) := Nat.two_pow_pos _
      have HP1 : (1 : Int) ≤ ((2 ^ (v_N - 1) : Nat) : Int) := by omega
      have Ha1 : |z1| ≤ ((2 ^ (v_N - 1) : Nat) : Int) := by
        rw [abs_le]; omega
      by_cases Hq : Int.tdiv z1 z2 < ((2 ^ (v_N - 1) : Nat) : Int)
      · have Hab := Zquot_abs_le z1 z2 ((2 ^ (v_N - 1) : Nat) : Int) Hz2 (by omega) Ha1
        have Hab' := abs_le.mp Hab
        obtain ⟨r, Hr⟩ := invsigned_total v_N (Int.tdiv z1 z2) (by omega) Hq
        refine ⟨some (uN.mk_uN r), fun_idiv_.fun_idiv__case_4 _ _ _ z2 z1 r Hs2 Hs1 ?_
          (inv_signed_wf _ _ _ Hr)⟩
        rw [truncz_quot z1 z2 Hz2]
        exact Hr
      · have Hge : ((2 ^ (v_N - 1) : Nat) : Int) ≤ Int.tdiv z1 z2 := by omega
        have Hinv := Zquot_ge_inv z1 z2 _ Hz2 HP1 Ha1 Hge
        refine ⟨none, fun_idiv_.fun_idiv__case_3 _ _ _ z2 z1 Hs2 Hs1 ?_⟩
        have Hn : Int.toNat ((v_N : Int) - 1) = v_N - 1 := by omega
        rw [Hn]
        rcases Hinv with ⟨Hb, Ha⟩ | ⟨Hb, Ha⟩
        · rw [Hb, Ha]
          push_cast
          simp
        · rw [Hb, Ha]
          push_cast
          simp
```

### `irem_total` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): `signed_total`, `invsigned_total`.
Earlier lemmas of this same batch used (proved here, before it in the file): `wf_uN_lt'`, `signed_nonzero`.
Notes: Follows Rocq. Rocq's Z.rem_bound_abs is replaced by `Int.natAbs_tmod` + `Nat.mod_lt` (|tmod z1 z2| < |z2| <= P), and Rocq's Hrem by `Int.tmod_def`; invsigned_total then applies after `rw [truncz_quot, Hrem]`. Uses project axiom `truncz_quot`.
```lean
  intro Hw1 Hw2
  have Hl1 := wf_uN_lt' _ _ Hw1
  have Hl2 := wf_uN_lt' _ _ Hw2
  cases v_sx with
  | U => exact ⟨_, fun_irem_.fun_irem__case_1 _ _ _⟩
  | S =>
    cases i2 with
    | mk_uN n2 =>
      cases n2 with
      | zero => exact ⟨_, fun_irem_.fun_irem__case_2 _ _⟩
      | succ p2 =>
        obtain ⟨z1, Hs1, Hlo1, Hhi1⟩ := signed_total v_N (proj_uN_0 i1) Hl1
        obtain ⟨z2, Hs2, Hlo2, Hhi2⟩ := signed_total v_N (proj_uN_0 (uN.mk_uN (p2 + 1))) Hl2
        have Hz2 : z2 ≠ 0 := signed_nonzero _ _ _ Hs2 (by simp [proj_uN_0])
        have HPp : 0 < 2 ^ (v_N - 1) := Nat.two_pow_pos _
        have Hrem : z1 - z2 * Int.tdiv z1 z2 = Int.tmod z1 z2 := (Int.tmod_def z1 z2).symm
        have Hbnd : (Int.tmod z1 z2).natAbs < z2.natAbs := by
          rw [Int.natAbs_tmod]
          exact Nat.mod_lt _ (Int.natAbs_pos.mpr Hz2)
        obtain ⟨r, Hr⟩ : ∃ ret, fun_inv_signed_ v_N
            (z1 - z2 * truncz ((z1 : Rat) / (z2 : Rat))) ret := by
          rw [truncz_quot _ _ Hz2, Hrem]
          apply invsigned_total
          · omega
          · omega
        exact ⟨some (uN.mk_uN r), fun_irem_.fun_irem__case_3 _ _ _ z1 z2 z2 z1 r Hs2 Hs1 Hr
          ⟨rfl, rfl⟩⟩
```

### `ilt_total` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): `signed_total`.
Earlier lemmas of this same batch used (proved here, before it in the file): `wf_uN_lt'`.
Notes: Same shape as Rocq: U gives case_0, S gives signed_total on both operands then case_1.
```lean
  intro Hw1 Hw2
  cases v_sx with
  | U => exact ⟨_, fun_ilt_.fun_ilt__case_0 _ _ _⟩
  | S =>
    obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ Hw1)
    obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ Hw2)
    exact ⟨_, fun_ilt_.fun_ilt__case_1 _ _ _ _ _ Hs2 Hs1⟩
```

### `igt_total` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): `signed_total`.
Earlier lemmas of this same batch used (proved here, before it in the file): `wf_uN_lt'`.
Notes: Same as ilt_total.
```lean
  intro Hw1 Hw2
  cases v_sx with
  | U => exact ⟨_, fun_igt_.fun_igt__case_0 _ _ _⟩
  | S =>
    obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ Hw1)
    obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ Hw2)
    exact ⟨_, fun_igt_.fun_igt__case_1 _ _ _ _ _ Hs2 Hs1⟩
```

### `ile_total` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): `signed_total`.
Earlier lemmas of this same batch used (proved here, before it in the file): `wf_uN_lt'`.
Notes: Same as ilt_total.
```lean
  intro Hw1 Hw2
  cases v_sx with
  | U => exact ⟨_, fun_ile_.fun_ile__case_0 _ _ _⟩
  | S =>
    obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ Hw1)
    obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ Hw2)
    exact ⟨_, fun_ile_.fun_ile__case_1 _ _ _ _ _ Hs2 Hs1⟩
```

### `ige_total` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): `signed_total`.
Earlier lemmas of this same batch used (proved here, before it in the file): `wf_uN_lt'`.
Notes: Same as ilt_total.
```lean
  intro Hw1 Hw2
  cases v_sx with
  | U => exact ⟨_, fun_ige_.fun_ige__case_0 _ _ _⟩
  | S =>
    obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ Hw1)
    obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ Hw2)
    exact ⟨_, fun_ige_.fun_ige__case_1 _ _ _ _ _ Hs2 Hs1⟩
```

### `idiv_wf` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): none.
Notes: `cases H` on the five fun_idiv_ clauses; the some-clauses carry the wf premise (case_1 premise slot `h`; case_4 has 8 binder slots before its wf premise `h`).
```lean
  intro H
  cases H with
  | fun_idiv__case_0 => exact iswf_Forall_nil _
  | fun_idiv__case_1 _ _ h => exact iswf_Forall_cons h (iswf_Forall_nil _)
  | fun_idiv__case_2 => exact iswf_Forall_nil _
  | fun_idiv__case_3 => exact iswf_Forall_nil _
  | fun_idiv__case_4 _ _ _ _ _ _ _ _ h => exact iswf_Forall_cons h (iswf_Forall_nil _)
```

### `wf_uN_mk_proj` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): none.
Notes: `cases x` then `exact H` (proj_uN_0 (mk_uN i) is defeq i).
```lean
  intro H
  cases x with
  | mk_uN i => exact H
```

### `wf_fN_num_` : proved
Still-`sorry` earlier lemmas relied on (outside this batch): none.
Notes: Pointwise `wf_num_.num__case_1` (Rocq's Forall_impl + num__case_1).
```lean
  intro Hl x hx
  exact wf_num_.num__case_1 _ _ _ (Hl x hx) rfl
```

## Final Lean check output (Head.lean merge simulation; exit code 0, zero errors)
```
'TLC.Zquot_ge_inv' depends on axioms: [propext, Quot.sound]
'TLC.wf_uN_lt'' depends on axioms: [propext, Quot.sound]
'TLC.signed_nonzero' depends on axioms: [propext, Quot.sound]
'TLC.lt_wf_uN' depends on axioms: [propext, Quot.sound]
'TLC.inv_signed_wf' depends on axioms: [propext, Quot.sound]
'TLC.idiv_total' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, TLC.truncz_quot]
'TLC.irem_total' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, TLC.truncz_quot]
'TLC.ilt_total' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.igt_total' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.ile_total' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.ige_total' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.idiv_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.wf_uN_mk_proj' does not depend on any axioms
'TLC.wf_fN_num_' depends on axioms: [propext]
exit=0
```
(`Work.lean`: exit 0, only the naming-style warning for the scratch name `wf_fN_num__proof`; all 14 `type_of%` guards pass.)

## Safety check at END (run after the log was written)
```
safety check [prove-H07] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T123937.111720403Z-prove-H07-1461898.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```
(An earlier END run, just before writing this log, printed the same `VERIFIED: zero new changes outside spectec/src/test-lean-claude`.)

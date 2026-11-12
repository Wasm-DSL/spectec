# prove-H10 (bundle20 progress port, proof batch H10)

Targets (14, all PROVED): imax_total_wf, iadd_sat_total_wf, isub_sat_total_wf, lanes_Jnn_form, lanes_Fnn_form, jlane_some, flane_some, lanes_size_eq, zip_lane_wf, zip_flane_wf, zip_lane_rel, vbinop_some, mk_uN_eta, res_bool_bit.

Scratch dir: /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H10/ (Final.lean = all 14 proofs as `<name>_proof` + rfl guards; TypeProgress_merged.lean = copy of TypeProgress.lean with the 14 proofs dropped in, compiled standalone to enforce the ordering rule).

## Safety check, START

```
safety check [prove-H10] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T124113.924909634Z-prove-H10-1462710.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method

1. Each target's header copied verbatim into Final.lean (renamed `<name>_proof`), guarded by `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all guards pass).
2. `lake env lean Final.lean`: exit 0, no errors (output below).
3. Ordering check: `merge.py` replaced the 14 `sorry` bodies in a COPY of TypeProgress.lean (scratch dir, repo file untouched) by the compiled tactic blocks; `lake env lean TypeProgress_merged.lean`: 0 errors, 266 `declaration uses sorry` warnings = 280 original sorries minus the 14 targets (no warning at any of the 14 target lines). So no proof uses a later TypeProgress lemma.
4. Only one Lean process was run at a time; no `lake build`; nothing written under `.lake/` or any repo file other than this log.

## Results

### imax_total_wf  (TypeProgress.lean:919; Rocq type_progress.v:2119-2133)  -- PROVED

Still-sorry earlier lemmas relied on: signed_total, wf_uN_lt' (TypeProgress, still sorry; owners H06/H07)

Notes: Direct port: case on sx; U by order on proj_uN_0, S via signed_total.

Proof body (after `:= by`):

```lean
  intro H1 H2
  have hex : ∃ r, fun_imax_ v_N v_sx i1 i2 r := by
    cases v_sx with
    | U =>
      by_cases E : proj_uN_0 i1 < proj_uN_0 i2
      · exact ⟨i2, fun_imax_.fun_imax__case_1 v_N i1 i2 E⟩
      · exact ⟨i1, fun_imax_.fun_imax__case_0 v_N i1 i2 (by omega)⟩
    | S =>
      obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ H1)
      obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ H2)
      exact ⟨_, fun_imax_.fun_imax__case_2 v_N i1 i2 z2 z1 Hs2 Hs1⟩
  obtain ⟨r, Hr⟩ := hex
  exact ⟨r, Hr, imax__is_wf _ _ _ _ _ _ Hr H1 H2 rfl⟩
```

### iadd_sat_total_wf  (TypeProgress.lean:924; Rocq type_progress.v:2135-2147)  -- PROVED

Still-sorry earlier lemmas relied on: signed_total, wf_uN_lt', sat_s_range, invsigned_total (TypeProgress, still sorry; H06/H07/H09)

Notes: Direct port.

Proof body (after `:= by`):

```lean
  intro H1 H2
  have hex : ∃ r, fun_iadd_sat_ v_N v_sx i1 i2 r := by
    cases v_sx with
    | U => exact ⟨_, fun_iadd_sat_.fun_iadd_sat__case_0 v_N i1 i2⟩
    | S =>
      obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ H1)
      obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ H2)
      obtain ⟨Hlo, Hhi⟩ := sat_s_range v_N (z1 + z2)
      obtain ⟨m, Hm⟩ := invsigned_total v_N (sat_s_ v_N (z1 + z2)) Hlo Hhi
      exact ⟨_, fun_iadd_sat_.fun_iadd_sat__case_1 v_N i1 i2 z2 z1 m Hs2 Hs1 Hm⟩
  obtain ⟨r, Hr⟩ := hex
  exact ⟨r, Hr, iadd_sat__is_wf _ _ _ _ _ _ Hr H1 H2 rfl⟩
```

### isub_sat_total_wf  (TypeProgress.lean:929; Rocq type_progress.v:2149-2161)  -- PROVED

Still-sorry earlier lemmas relied on: signed_total, wf_uN_lt', sat_s_range, invsigned_total (TypeProgress, still sorry; H06/H07/H09)

Notes: Direct port.

Proof body (after `:= by`):

```lean
  intro H1 H2
  have hex : ∃ r, fun_isub_sat_ v_N v_sx i1 i2 r := by
    cases v_sx with
    | U => exact ⟨_, fun_isub_sat_.fun_isub_sat__case_0 v_N i1 i2⟩
    | S =>
      obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (wf_uN_lt' _ _ H1)
      obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (wf_uN_lt' _ _ H2)
      obtain ⟨Hlo, Hhi⟩ := sat_s_range v_N (z1 - z2)
      obtain ⟨m, Hm⟩ := invsigned_total v_N (sat_s_ v_N (z1 - z2)) Hlo Hhi
      exact ⟨_, fun_isub_sat_.fun_isub_sat__case_1 v_N i1 i2 z2 z1 m Hs2 Hs1 Hm⟩
  obtain ⟨r, Hr⟩ := hex
  exact ⟨r, Hr, isub_sat__is_wf _ _ _ _ _ _ Hr H1 H2 rfl⟩
```

### lanes_Jnn_form  (TypeProgress.lean:942; Rocq type_progress.v:2170-2177)  -- PROVED

Still-sorry earlier lemmas relied on: wf_lane_Jnn_inv, wf_lane_Jnn_some (TypeProgress, still sorry; H09); wasm2.0 lanes__is_wf (sorry in generated file)

Notes: Direct port; Forall is a plain def so no Forall_impl needed.

Proof body (after `:= by`):

```lean
  intro Hsh Hc
  have Hl := lanes__is_wf _ _ _ Hsh Hc rfl
  intro l hl
  have Hw := Hl l hl
  exact wf_lane_Jnn_inv J l Hw (wf_lane_Jnn_some J l Hw)
```

### lanes_Fnn_form  (TypeProgress.lean:948; Rocq type_progress.v:2179-2185)  -- PROVED

Still-sorry earlier lemmas relied on: wf_lane_Fnn_inv (TypeProgress, still sorry; H09); wasm2.0 lanes__is_wf (sorry in generated file)

Notes: Direct port.

Proof body (after `:= by`):

```lean
  intro Hsh Hc
  have Hl := lanes__is_wf _ _ _ Hsh Hc rfl
  intro l hl
  exact wf_lane_Fnn_inv F l (Hl l hl)
```

### jlane_some  (TypeProgress.lean:953; Rocq type_progress.v:2187-2189)  -- PROVED

Still-sorry earlier lemmas relied on: none

Proof body (after `:= by`):

```lean
  intro H l hl
  obtain ⟨x, rfl, _⟩ := H l hl
  simp [proj_lane__0]
```

### flane_some  (TypeProgress.lean:957; Rocq type_progress.v:2190-2192)  -- PROVED

Still-sorry earlier lemmas relied on: none

Proof body (after `:= by`):

```lean
  intro H l hl
  obtain ⟨x, rfl, _⟩ := H l hl
  simp [proj_lane__1]
```

### lanes_size_eq  (TypeProgress.lean:963; Rocq type_progress.v:2193-2197)  -- PROVED

Still-sorry earlier lemmas relied on: none

Notes: Uses HelperLemmas axiom lanes_len (mirrors Rocq axioms.v lanes_len).

Proof body (after `:= by`):

```lean
  rw [lanes_len, lanes_len]
```

### zip_lane_wf  (TypeProgress.lean:972; Rocq type_progress.v:2200-2212)  -- PROVED

Still-sorry earlier lemmas relied on: none

Notes: Pointwise over the zip (List.of_mem_zip), not Rocq elim, since Lean Forall2 is zip-based; length premise unused.

Proof body (after `:= by`):

```lean
  intro hlt Hf H1 H2 _
  subst hlt
  rintro ⟨l1, l2⟩ ht
  obtain ⟨h1, h2⟩ := List.of_mem_zip ht
  obtain ⟨x1, rfl, Hx1⟩ := H1 _ h1
  obtain ⟨x2, rfl, Hx2⟩ := H2 _ h2
  exact wf_lane_.lane__case_0 _ _ _ (Hf _ _ Hx1 Hx2) rfl
```

### zip_flane_wf  (TypeProgress.lean:986; Rocq type_progress.v:2214-2227)  -- PROVED

Still-sorry earlier lemmas relied on: none

Notes: Same as zip_lane_wf.

Proof body (after `:= by`):

```lean
  intro Hf H1 H2 _
  rintro ⟨l1, l2⟩ ht
  obtain ⟨h1, h2⟩ := List.of_mem_zip ht
  obtain ⟨x1, rfl, Hx1⟩ := H1 _ h1
  obtain ⟨x2, rfl, Hx2⟩ := H2 _ h2
  intro r hr
  exact wf_lane_.lane__case_1 _ _ _ (Hf _ _ Hx1 Hx2 r hr) rfl
```

### zip_lane_rel  (TypeProgress.lean:999; Rocq type_progress.v:2230-2244)  -- PROVED

Still-sorry earlier lemmas relied on: none

Notes: Induction on L1 generalizing L2 (as Rocq), constructing vs.

Proof body (after `:= by`):

```lean
  intro HR H1 H2 Hlen
  induction L1 generalizing L2 with
  | nil =>
    refine ⟨[], ?_, ?_, rfl⟩
    · rintro ⟨⟨v, l1⟩, l2⟩ ht
      simp at ht
    · intro v hv
      simp at hv
  | cons l1 L1' IH =>
    cases L2 with
    | nil => simp at Hlen
    | cons l2 L2' =>
      obtain ⟨x1, rfl, Hx1⟩ := H1 _ (List.mem_cons_self ..)
      obtain ⟨x2, rfl, Hx2⟩ := H2 _ (List.mem_cons_self ..)
      obtain ⟨vs, H3, Hw, Hs⟩ := IH L2' (fun l hl => H1 l (List.mem_cons_of_mem _ hl))
        (fun l hl => H2 l (List.mem_cons_of_mem _ hl)) (by simpa using Hlen)
      obtain ⟨r, Hr, Hwr⟩ := HR x1 x2 Hx1 Hx2
      refine ⟨r :: vs, ?_, ?_, ?_⟩
      · rintro ⟨⟨v, l1'⟩, l2'⟩ ht
        simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at ht
        rcases ht with ⟨⟨rfl, rfl⟩, rfl⟩ | ht
        · simpa [proj_lane__0] using Hr
        · exact H3 _ (by simpa using ht)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Hwr
        · exact Hw v hv
      · simp [Hs]
```

### vbinop_some  (TypeProgress.lean:1012; Rocq type_progress.v:2282-2325)  -- PROVED

Still-sorry earlier lemmas relied on: same-batch: lanes_Jnn_form, lanes_Fnn_form, jlane_some, lanes_size_eq, zip_lane_wf, zip_flane_wf, zip_lane_rel, imax_total_wf, iadd_sat_total_wf, isub_sat_total_wf; earlier still-sorry: imin_total_wf (H09); wasm2.0 sorry'd *_is_wf: iavgr__is_wf, iq15mulr_sat__is_wf, fadd__is_wf, fsub__is_wf, fmul__is_wf, fdiv__is_wf, fmin__is_wf, fmax__is_wf, fpmin__is_wf, fpmax__is_wf

Notes: Port of the Rocq proof: inversion of wf_vbinop_, destruct op; the Ltac vlane_close/econstructor is replaced by explicit applications of fun_vbinop__case_0..51; 12 of the 36 integer (J, op) pairs are excluded by the lane-size side condition of `wf_vbinop_Jnn_N` and closed by `absurd ... (by decide)`; the other 24 integer pairs and the 16 float pairs each use one of the constructors `fun_vbinop__case_0..51` (40 used, 12 unused).

Proof body (after `:= by`):

```lean
  intro Hsh Hop H1 H2
  -- Rocq `inversion Hop`: integer shapes first, then float shapes.
  cases Hop
  · rename_i J M o Ho Hs
    subst Hs
    have HL1 := lanes_Jnn_form J M c1 Hsh H1
    have HL2 := lanes_Jnn_form J M c2 Hsh H2
    have HS1 := jlane_some _ _ HL1
    have HS2 := jlane_some _ _ HL2
    have Hsz := lanes_size_eq (lanetype_Jnn J) M c1 c2
    -- Rocq `destruct o`. After `cases J` the goals are I32, I64, I8, I16, which is the order of
    -- the generated `fun_vbinop__case_*` constructors; the (J, op) pairs excluded by the lane-size
    -- side condition of `wf_vbinop_Jnn_N` (`Hle`/`Hge`/`Heq`) are closed by `absurd`.
    cases o with
    | ADD =>
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => iadd_ (lsizenn (lanetype_Jnn J)) a b) _ _ rfl
        (fun a b Ha Hb => iadd__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_0 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_1 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_2 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_3 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | SUB =>
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => isub_ (lsizenn (lanetype_Jnn J)) a b) _ _ rfl
        (fun a b Ha Hb => isub__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_4 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_5 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_6 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_7 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | ADD_SAT sx =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 16 := by cases Ho; assumption
      -- `zip_lane_rel` gives the lane results `vs` (used for both `var_1_lst` and `var_0_lst`)
      obtain ⟨vs, H3, Hw, Hsv⟩ := zip_lane_rel J
        (fun a b r => fun_iadd_sat_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN (lsize (lanetype_Jnn J)) r) _ _
        (fun a b Ha Hb => iadd_sat_total_wf _ sx a b Ha Hb) HL1 HL2 Hsz
      have Hw' : Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs :=
        fun v hv => wf_lane_.lane__case_0 _ _ _ (Hw v hv) rfl
      cases J
      · exact absurd Hle (by decide)
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_18 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_19 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
    | SUB_SAT sx =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 16 := by cases Ho; assumption
      obtain ⟨vs, H3, Hw, Hsv⟩ := zip_lane_rel J
        (fun a b r => fun_isub_sat_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN (lsize (lanetype_Jnn J)) r) _ _
        (fun a b Ha Hb => isub_sat_total_wf _ sx a b Ha Hb) HL1 HL2 Hsz
      have Hw' : Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs :=
        fun v hv => wf_lane_.lane__case_0 _ _ _ (Hw v hv) rfl
      cases J
      · exact absurd Hle (by decide)
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_22 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_23 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
    | MUL =>
      have Hge : lsizenn (lanetype_Jnn J) ≥ 16 := by cases Ho; assumption
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => imul_ (lsizenn (lanetype_Jnn J)) a b) _ _ rfl
        (fun a b Ha Hb => imul__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_24 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_25 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact absurd Hge (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_27 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | AVGRU =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 16 := by cases Ho; assumption
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => iavgr_ (lsizenn (lanetype_Jnn J)) sx.U a b) _ _ rfl
        (fun a b Ha Hb => iavgr__is_wf _ _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact absurd Hle (by decide)
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_30 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_31 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | Q15MULR_SATS =>
      have Heq : lsizenn (lanetype_Jnn J) = 16 := by cases Ho; assumption
      have hz := zip_lane_wf J (lanetype_Jnn J) (fun a b => iq15mulr_sat_ (lsizenn (lanetype_Jnn J)) sx.S a b) _ _ rfl
        (fun a b Ha Hb => iq15mulr_sat__is_wf _ _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases J
      · exact absurd Heq (by decide)
      · exact absurd Heq (by decide)
      · exact absurd Heq (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_35 M c1 c2 M _ _ _ rfl rfl HS1 HS2 rfl Hsh Hsz HS1 HS2 hz rfl⟩
    | MIN sx =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 32 := by cases Ho; assumption
      obtain ⟨vs, H3, Hw, Hsv⟩ := zip_lane_rel J
        (fun a b r => fun_imin_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN (lsize (lanetype_Jnn J)) r) _ _
        (fun a b Ha Hb => imin_total_wf _ sx a b Ha Hb) HL1 HL2 Hsz
      have Hw' : Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs :=
        fun v hv => wf_lane_.lane__case_0 _ _ _ (Hw v hv) rfl
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_8 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_10 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_11 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
    | MAX sx =>
      have Hle : lsizenn (lanetype_Jnn J) ≤ 32 := by cases Ho; assumption
      obtain ⟨vs, H3, Hw, Hsv⟩ := zip_lane_rel J
        (fun a b r => fun_imax_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN (lsize (lanetype_Jnn J)) r) _ _
        (fun a b Ha Hb => imax_total_wf _ sx a b Ha Hb) HL1 HL2 Hsz
      have Hw' : Forall (fun v => wf_lane_ (lanetype_Jnn J) (lane_.mk_lane__0 J v)) vs :=
        fun v hv => wf_lane_.lane__case_0 _ _ _ (Hw v hv) rfl
      cases J
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_12 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact absurd Hle (by decide)
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_14 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_15 M sx c1 c2 M _ _ _ vs vs Hsv (Hsv.trans Hsz) HS1 HS2 H3
          Hsv (Hsv.trans Hsz) HS1 HS2 H3 rfl rfl rfl Hsh Hw' rfl⟩
  · -- float shapes: the result list is `v128_lst`, built from `setproduct_` of the lane results
    rename_i F M o Hs
    subst Hs
    have HL1 := lanes_Fnn_form F M c1 Hsh H1
    have HL2 := lanes_Fnn_form F M c2 Hsh H2
    have Hsz := lanes_size_eq (lanetype_Fnn F) M c1 c2
    cases o with
    | ADD =>
      have hz := zip_flane_wf F fadd_ _ _ (fun a b Ha Hb => fadd__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_36 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_37 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | SUB =>
      have hz := zip_flane_wf F fsub_ _ _ (fun a b Ha Hb => fsub__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_38 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_39 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | MUL =>
      have hz := zip_flane_wf F fmul_ _ _ (fun a b Ha Hb => fmul__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_40 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_41 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | DIV =>
      have hz := zip_flane_wf F fdiv_ _ _ (fun a b Ha Hb => fdiv__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_42 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_43 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | MIN =>
      have hz := zip_flane_wf F fmin_ _ _ (fun a b Ha Hb => fmin__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_44 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_45 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | MAX =>
      have hz := zip_flane_wf F fmax_ _ _ (fun a b Ha Hb => fmax__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_46 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_47 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | PMIN =>
      have hz := zip_flane_wf F fpmin_ _ _ (fun a b Ha Hb => fpmin__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_48 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_49 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
    | PMAX =>
      have hz := zip_flane_wf F fpmax_ _ _ (fun a b Ha Hb => fpmax__is_wf _ _ _ _ Ha Hb rfl) HL1 HL2 Hsz
      cases F
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_50 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
      · exact ⟨_, fun_vbinop_.fun_vbinop__case_51 M c1 c2 M _ _ _ _ rfl rfl rfl rfl Hsh Hsz hz rfl⟩
```

### mk_uN_eta  (TypeProgress.lean:1019; Rocq type_progress.v:2327-2331)  -- PROVED

Still-sorry earlier lemmas relied on: none

Proof body (after `:= by`):

```lean
  cases u
  rfl
```

### res_bool_bit  (TypeProgress.lean:1025; Rocq type_progress.v:2332-2334)  -- PROVED

Still-sorry earlier lemmas relied on: none

Proof body (after `:= by`):

```lean
  apply iswf_uN_of_lt
  cases b <;> simp [nat_of_bool]
```

## Axioms / sorry dependencies

`#print axioms` of the 14 `_proof` theorems (final run, `lake env lean Final.lean`):

```
'TLC.imax_total_wf_proof' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.iadd_sat_total_wf_proof' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.isub_sat_total_wf_proof' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.lanes_Jnn_form_proof' depends on axioms: [propext, sorryAx]
'TLC.lanes_Fnn_form_proof' depends on axioms: [propext, sorryAx]
'TLC.jlane_some_proof' depends on axioms: [propext]
'TLC.flane_some_proof' depends on axioms: [propext]
'TLC.lanes_size_eq_proof' depends on axioms: [lanes_len]
'TLC.zip_lane_wf_proof' depends on axioms: [propext]
'TLC.zip_flane_wf_proof' depends on axioms: [propext]
'TLC.zip_lane_rel_proof' depends on axioms: [propext]
'TLC.vbinop_some_proof' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.mk_uN_eta_proof' does not depend on any axioms
'TLC.res_bool_bit_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sorryAx` appears only through the still-`sorry` lemmas listed above (TypeProgress ones owned by H06/H07/H09, and the generated wasm2.0 well-formedness theorems `lanes__is_wf`, `iavgr__is_wf`, `iq15mulr_sat__is_wf`, `fadd__is_wf`, `fsub__is_wf`, `fmul__is_wf`, `fdiv__is_wf`, `fmin__is_wf`, `fmax__is_wf`, `fpmin__is_wf`, `fpmax__is_wf`, which are `sorry` in the generated wasm2.0.lean; the Rocq proof uses the corresponding generated lemmas too, via `lanes__is_wf` and the Ltac `vlane_close`). The only project axiom used is HelperLemmas `lanes_len` (by `lanes_size_eq`; mirrors Rocq axioms.v). No new axioms, no `native_decide`, no `sorry` in the proofs. `decide` is used only to refute the numeric side conditions (`lsizenn (lanetype_Jnn Jnn.I32) ≤ 16` etc.).

## Final Lean check (last lines)

```
$ lake env lean Final.lean   -> exit 0 (output above, no errors)
$ lake env lean TypeProgress_merged.lean -> exit 0; 0 'error' lines; 266 'declaration uses `sorry`' warnings (none at the 14 target lines)
```

## Safety check, END

```
safety check [prove-H10] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T124951.696210375Z-prove-H10-1467707.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

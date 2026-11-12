# prove-H13 (bundle20 progress port, proof batch H13)

Targets (TypeProgress.lean:1242-1354, in order): `evens_odds_size`, `Forall_evens`, `Forall_odds`, `Forall2_of_Forall`, `list_slice_size_eq`, `zip_lane_wf2`, `zip_wf`, `size_zipWith_eq`, `shape_lanes_even`, `add_sub_parens`, `call_indirect_progress`, `vcvtop_lane_total`, `vcvtop_lanes_total`, `setproduct2_Forall`.

RESULT: all 14 PROVED. No repo file was edited. Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H13/`. Only my own log file was written inside the target dir (plus the safety-check output files the check script itself creates).

## Safety check at START
```
safety check [prove-H13] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T125420.993671975Z-prove-H13-1471497.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- `Work.lean` (scratch, final combined file): header of each target copied verbatim from TypeProgress.lean, renamed `<name>_proof`, plus the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all 14 guards pass), plus `#print axioms` for each. Written first as `Work1.lean` (12 simple targets) and `Work2.lean` (the two vcvtop lemmas), then merged.
- `Merge.lean` (merge simulation): the real `TypeProgress.lean` from line 1 through `setproduct2_Forall` (cut before `setproduct1_Forall`) with the 14 `sorry` bodies replaced by the tactic blocks below, compiled with `lake env lean` against the same imports: exit 0, ZERO errors; the 158 `declaration uses sorry` warnings are for other, unproved lemmas (none of my 14 is flagged). So the blocks drop into the real file unchanged and the ordering rule holds (every dependency is earlier in the file or imported).
- Direct TLC-lemma dependencies of each proof were also listed with `Expr.getUsedConstants` (only `evens_odds_ind` for the three evens/odds lemmas; `Forall_exists_Forall2`, `Forall_map_P`, `vcvtop_lane_total` for `vcvtop_lanes_total`; `lanes_len`, `trunc_sat_total`, `demote_nonempty`, `promote_nonempty` are HelperLemmas axioms).
- One Lean process at a time (each run ~2.5 s because the oleans are mmapped).
- Traps met (all fixed): (1) `cases h with | lane__case_0 ..` / `vcvtop___case_k ..` binder slots: indices that are uniformly variables in every constructor (`wf_lane_`'s lanetype, `wf_vcvtop__`'s two shapes) are promoted to inductive parameters and take NO slot, so the slots are `lane__case_0 J c hwf Heq` and `vcvtop___case_0 J1 M1 J2 M2 o Ho E1 E2`; for the single-constructor `wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2` etc. the slots are only the not-yet-unified fields plus the hypothesis (`_case_0 _ _ hs` for EXTEND/CONVERT/TRUNC_SAT, `_ hs` for DEMOTE, `hs` for PROMOTELOW). (2) The constructors of `fun_lcvtop__` need their namespace: `fun_lcvtop__.fun_lcvtop___case_14`. (3) In `first | exact absurd h (by simp ..) | ..` a `by` block that leaves `⊢ False` is a LOGGED error, not an exception, so `first` does not backtrack; use `by decide` (throws) or `(simp .. at H; done)`. (4) `decide` refuses goals with free variables, hence `Hts` is discharged with `simp [vcvtop_trunc_sat_i16] at Hts`. (5) `List.mem_zipWith` does not exist in this core; use `← List.map_uncurry_zip_eq_zipWith` + `List.mem_map`.

## Per-target results

### 1. `evens_odds_size` (TypeProgress.lean:1242; Rocq type_progress.v:2652-2656) — PROVED

Earlier still-`sorry` lemmas used: `evens_odds_ind`.

Notes: Same shape as Rocq (`evens_odds_ind`, then `negbK`/IH). `Odd` is unfolded with `Nat.odd_iff` and `omega` (list lengths are genuine `Nat`). `evens_odds_ind` was PROVED by batch H12 (still `sorry` in the current file).

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  refine evens_odds_ind T (fun l => ¬ Odd l.length → (evens l).length = (odds l).length) ?_ ?_ ?_ l
  · intro _
    simp [evens, odds]
  · intro a h
    exact absurd ⟨0, by simp⟩ h
  · intro a b l IH Hl
    have Hl' : ¬ Odd l.length := by
      intro ho
      apply Hl
      rw [Nat.odd_iff] at ho ⊢
      simp only [List.length_cons]
      omega
    simp only [evens, odds, List.length_cons]
    rw [IH Hl']
```

### 2. `Forall_evens` (TypeProgress.lean:1247; Rocq type_progress.v:2658-2662) — PROVED

Earlier still-`sorry` lemmas used: `evens_odds_ind`.

Notes: `refine evens_odds_ind T (fun l => ..) ?_ ?_ ?_ l`; Rocq's `inversion H` twice becomes membership reasoning (`Forall P l := ∀ x ∈ l, P x`).

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  refine evens_odds_ind T (fun l => Forall P l → Forall P (evens l)) ?_ ?_ ?_ l
  · intro _ x hx
    simp [evens] at hx
  · intro a _ x hx
    simp [evens] at hx
  · intro a b l IH H x hx
    simp only [evens, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact H _ (by simp)
    · exact IH (fun y hy => H y (by simp [hy])) x hx
```

### 3. `Forall_odds` (TypeProgress.lean:1252; Rocq type_progress.v:2664-2668) — PROVED

Earlier still-`sorry` lemmas used: `evens_odds_ind`.

Notes: Identical to `Forall_evens` with `odds`.

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  refine evens_odds_ind T (fun l => Forall P l → Forall P (odds l)) ?_ ?_ ?_ l
  · intro _ x hx
    simp [odds] at hx
  · intro a _ x hx
    simp [odds] at hx
  · intro a b l IH H x hx
    simp only [odds, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact H _ (by simp)
    · exact IH (fun y hy => H y (by simp [hy])) x hx
```

### 4. `Forall2_of_Forall` (TypeProgress.lean:1259; Rocq type_progress.v:2670-2677) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: Zip-based `Forall₂` is membership in `l1.zip l2`; `List.of_mem_zip` gives both memberships, so the length premise is not even needed (it is kept in the statement, bound as `_`).

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro HQ H1 H2 _ t ht
  obtain ⟨a, b⟩ := t
  have h := List.of_mem_zip ht
  exact HQ a b (H1 a h.1) (H2 b h.2)
```

### 5. `list_slice_size_eq` (TypeProgress.lean:1266; Rocq type_progress.v:2679-2685) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: `List.length_take` / `List.length_drop` and the length premise.

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro h
  simp [List.length_take, List.length_drop, h]
```

### 6. `zip_lane_wf2` (TypeProgress.lean:1274; Rocq type_progress.v:2687-2699) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: Pointwise over the zip (`List.of_mem_zip`); each lane unfolds `jlane` to `mk_lane__0 Ji x` (`obtain ⟨x1, rfl, Hx1⟩`), `proj_lane__0 (mk_lane__0 _ x) = some x` reduces by defeq, then `wf_lane_.lane__case_0` (Rocq's `lane__case_0`).

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro hlt Hf H1 H2 _ t ht
  obtain ⟨a, b⟩ := t
  have h := List.of_mem_zip ht
  obtain ⟨x1, rfl, Hx1⟩ := H1 a h.1
  obtain ⟨x2, rfl, Hx2⟩ := H2 b h.2
  exact wf_lane_.lane__case_0 lt Jo _ (Hf x1 x2 Hx1 Hx2) hlt
```

### 7. `zip_wf` (TypeProgress.lean:1286; Rocq type_progress.v:2701-2708) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: No `List.mem_zipWith` exists in this core; `← List.map_uncurry_zip_eq_zipWith` + `List.mem_map` reduces `x ∈ zipWith f L1 L2` to a zip membership.

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro Hf H1 H2 x hx
  rw [← List.map_uncurry_zip_eq_zipWith] at hx
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hx
  have h := List.of_mem_zip hab
  exact Hf a b (H1 a h.1) (H2 b h.2)
```

### 8. `size_zipWith_eq` (TypeProgress.lean:1292; Rocq type_progress.v:2710-2714) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: `List.length_zipWith` (= min of the lengths) and the length premise.

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro h
  simp [List.length_zipWith, h]
```

### 9. `shape_lanes_even` (TypeProgress.lean:1298; Rocq type_progress.v:2715-2725) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: Uses the project axiom `lanes_len` (HelperLemmas; mirrors Rocq `axioms.v` `lanes_len`) to turn the lane count into `M`; then `cases J`, unfold `lsize`/`psize`/`size`, `omega` pins `M ∈ {16,8,4,2}` and `decide` gives `¬ Odd M`. (`lsize (I32)` unfolds through `Option.get! (size ..)`.)

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro H
  rw [lanes_len]
  cases J <;> simp only [lsize, lanetype_Jnn, psize, size, valtype_numtype, Option.get!] at H <;>
    (have : M = 16 ∨ M = 8 ∨ M = 4 ∨ M = 2 := by omega
     rcases this with rfl | rfl | rfl | rfl <;> decide)
```

### 10. `add_sub_parens` (TypeProgress.lean:1306; Rocq type_progress.v:2727-2732) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: `omega` (it understands `Int.toNat` and the `Nat→Int` cast), as Rocq's `lia`.

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro h
  omega
```

### 11. `call_indirect_progress` (TypeProgress.lean:1312; Rocq type_progress.v:2734-2794) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: Much shorter than Rocq's 5-way case analysis: Lean's generated `Step_read.call_indirect_trap` has the negated side condition `¬ Step_read_before_call_indirect_trap ..`, so `by_cases` on that predicate decides everything: if it holds, `cases` extracts the 5 premises of `call_indirect_call_0` and `Step_read.call_indirect_call` applies verbatim (result `CALL_ADDR a`); otherwise `call_indirect_trap` gives `TRAP`. The `[x] ++ [y]` in the statement is `[x, y]` by defeq, so `Step.read _ _ _ ..` unifies.

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro HNone
  by_cases h : Step_read_before_call_indirect_trap (config.mk_config (state.mk_state s f) [admininstr.CONST numtype.I32 v_i, admininstr.CALL_INDIRECT x y])
  · cases h with
    | call_indirect_call_0 _ _ _ _ a h1 h2 h3 h4 h5 =>
      exact ⟨[admininstr.CALL_ADDR a], Step.read _ _ _ (Step_read.call_indirect_call _ _ _ _ _ h1 h2 h3 h4 h5)⟩
  · exact ⟨[admininstr.TRAP], Step.read _ _ _ (Step_read.call_indirect_trap _ _ _ _ h)⟩
```

### 12. `vcvtop_lane_total` (TypeProgress.lean:1328; Rocq type_progress.v:2817-2846) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: Rocq-style enumeration. (1) local helper facts (`inj`, `injF`, `hJF`: `lanetype_Jnn`/`lanetype_Fnn` are injective and disjoint; `lJ`/`lF`: a `wf_lane_ (lanetype_Jnn J1)` lane is `mk_lane__0 J1 c`, resp. `lanetype_Fnn`/`mk_lane__1`; `key`/`keyL`: non-emptiness of `list_ lane_ (OMap f o)` for `o ≠ none` and of `Map f l` for `l ≠ []`). (2) `cases Hop` into the four `vcvtop___case_k`; `subst`; `obtain ⟨c, rfl⟩ := lJ/lF ..` to expose the lane; `cases o` / `cases Ho` to get the size side condition `hs`; `cases` on the lane-type variables and `first | absurd (by decide) | witness`: impossible combinations die by `decide` on `hs` (closed Nat equalities), the F32→I16 TRUNC_SAT combination dies on `Hts` (`simp [vcvtop_trunc_sat_i16] at Hts; done`, `done` is required because `first` would otherwise accept a `simp` that merely clears `Hts`), the 10 valid combinations are witnessed by `fun_lcvtop__.fun_lcvtop___case_{14,3,4}` (EXTEND I8→I16, I16→I32, I32→I64), `{16,19,20}` (CONVERT I32→F32, I16→F32, I32→F64), `{24,25}` (TRUNC_SAT F32→I32, F64→I32), `29` (DEMOTE F64→F32), `34` (PROMOTELOW F32→F64). Non-emptiness: `List.cons_ne_nil` for EXTEND/CONVERT, `key _ _ (trunc_sat_total ..)` for TRUNC_SAT, `keyL _ _ (demote_nonempty ..)` / `(promote_nonempty ..)` for DEMOTE/PROMOTELOW (project axioms from HelperLemmas = Rocq `axioms.v`). No `sorry` anywhere (`#print axioms`: propext + those 3 axioms).

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro Hop Hts Hl
  have inj : ∀ a b : Jnn, lanetype_Jnn a = lanetype_Jnn b → a = b := by
    intro a b h
    cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)
  have injF : ∀ a b : Fnn, lanetype_Fnn a = lanetype_Fnn b → a = b := by
    intro a b h
    cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)
  have hJF : ∀ (a : Jnn) (b : Fnn), lanetype_Jnn a ≠ lanetype_Fnn b := by
    intro a b h
    cases a <;> cases b <;> (revert h; decide)
  have lJ : ∀ (J1 : Jnn) (c0 : lane_), wf_lane_ (lanetype_Jnn J1) c0 →
      ∃ c, c0 = lane_.mk_lane__0 J1 c := by
    intro J1 c0 h
    cases h with
    | lane__case_0 J c _ Heq => exact ⟨c, by rw [inj _ _ Heq]⟩
    | lane__case_1 F c _ Heq => exact absurd Heq (hJF _ _)
  have lF : ∀ (F1 : Fnn) (c0 : lane_), wf_lane_ (lanetype_Fnn F1) c0 →
      ∃ c, c0 = lane_.mk_lane__1 F1 c := by
    intro F1 c0 h
    cases h with
    | lane__case_0 J c _ Heq => exact absurd Heq.symm (hJF _ _)
    | lane__case_1 F c _ Heq => exact ⟨c, by rw [injF _ _ Heq]⟩
  have key : ∀ (f : iN → lane_) (o : Option iN), o ≠ none → list_ lane_ (OMap f o) ≠ [] := by
    intro f o ho
    cases o with
    | none => exact absurd rfl ho
    | some y => simp [list_, OMap]
  have keyL : ∀ (f : fN → lane_) (l : List fN), l ≠ [] → Map f l ≠ [] := by
    intro f l hl h
    exact hl (List.map_eq_nil_iff.mp h)
  cases Hop with
  | vcvtop___case_0 J1 M1 J2 M2 o Ho E1 E2 =>
    subst E1 E2
    obtain ⟨c, rfl⟩ := lJ J1 ci Hl
    cases o with
    | EXTEND h sx =>
      cases Ho with
      | vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 _ _ hs =>
        cases J1 <;> cases J2 <;>
        first
        | exact absurd hs (by decide)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_14 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_3 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_4 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
  | vcvtop___case_1 J1 M1 F2 M2 o Ho E1 E2 =>
    subst E1 E2
    obtain ⟨c, rfl⟩ := lJ J1 ci Hl
    cases o with
    | CONVERT ho sx =>
      cases Ho with
      | vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 _ _ hs =>
        rcases hs with ⟨⟨h1, h2⟩, _⟩ | ⟨h1, _⟩ <;> cases J1 <;> cases F2 <;>
        first
        | exact absurd h1 (by decide)
        | exact absurd h2 (by decide)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_16 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_19 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_20 _ _ _ _ _ _ _ _ rfl rfl rfl, List.cons_ne_nil _ _⟩
  | vcvtop___case_2 F1 M1 J2 M2 o Ho E1 E2 =>
    subst E1 E2
    obtain ⟨c, rfl⟩ := lF F1 ci Hl
    cases o with
    | TRUNC_SAT sx zo =>
      cases Ho with
      | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 _ _ hs =>
        rcases hs with ⟨⟨h1, h2⟩, _⟩ | ⟨h1, _⟩ <;> cases F1 <;> cases J2 <;>
        first
        | exact absurd h1 (by decide)
        | exact absurd h2 (by decide)
        | (simp [vcvtop_trunc_sat_i16] at Hts; done)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_24 _ _ _ _ _ _ _ _ rfl rfl rfl, key _ _ (trunc_sat_total _ _ _ _)⟩
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_25 _ _ _ _ _ _ _ _ rfl rfl rfl, key _ _ (trunc_sat_total _ _ _ _)⟩
  | vcvtop___case_3 F1 M1 F2 M2 o Ho E1 E2 =>
    subst E1 E2
    obtain ⟨c, rfl⟩ := lF F1 ci Hl
    cases o with
    | DEMOTE z =>
      cases Ho with
      | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 _ hs =>
        cases F1 <;> cases F2 <;>
        first
        | exact absurd hs (by decide)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_29 _ _ _ _ _ _ rfl rfl rfl, keyL _ _ (demote_nonempty _ _ _)⟩
    | PROMOTELOW =>
      cases Ho with
      | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 hs =>
        cases F1 <;> cases F2 <;>
        first
        | exact absurd hs (by decide)
        | exact ⟨_, fun_lcvtop__.fun_lcvtop___case_34 _ _ _ _ _ _ rfl rfl rfl, keyL _ _ (promote_nonempty _ _ _)⟩
```

### 13. `vcvtop_lanes_total` (TypeProgress.lean:1339; Rocq type_progress.v:2849-2869) — PROVED

Earlier still-`sorry` lemmas used: `Forall_exists_Forall2`, `Forall_map_P`, `vcvtop_lane_total (earlier in this same batch: proved above)`.

Notes: Follows Rocq exactly: `Forall_exists_Forall2` with `P v := v ≠ none ∧ get! v ≠ [] ∧ Forall wf (get! v)` where each lane is handled by `vcvtop_lane_total` (witness `some r`) and `lcvtop___is_wf` (generated well-formedness theorem). The extra conjunct `vs.length = L.length` (the stated deviation) comes from the length conjunct of Lean's `Forall_exists_Forall2`. The two `Forall (..) (List.map get! vs)` conjuncts use `Forall_map_P`.

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro Hs1 Hs2 Hop Hts HL
  have H : ∃ vs : List (Option (List lane_)),
      (Forall₂ (fun v ci => fun_lcvtop__ sh_1 sh_2 op ci v) vs L ∧ vs.length = L.length) ∧
      Forall (fun v => v ≠ none ∧ Option.get! v ≠ [] ∧
        Forall (wf_lane_ (fun_lanetype sh_2)) (Option.get! v)) vs := by
    apply Forall_exists_Forall2 (Option (List lane_)) lane_ (fun v ci => fun_lcvtop__ sh_1 sh_2 op ci v)
    intro ci Hci
    obtain ⟨r, Hr, Hne⟩ := vcvtop_lane_total _ _ _ _ Hop Hts (HL ci Hci)
    refine ⟨some r, Hr, by simp, by simpa using Hne, ?_⟩
    exact lcvtop___is_wf _ _ _ _ _ _ Hr Hs1 Hs2 Hop (HL ci Hci) (by simp) rfl
  obtain ⟨vs, ⟨H2, Hlen⟩, HP⟩ := H
  refine ⟨vs, H2, Hlen, ?_, ?_, ?_⟩
  · intro v hv
    exact (HP v hv).1
  · exact Forall_map_P _ _ _ _ _ _ (fun v hv => hv.2.1) HP
  · exact Forall_map_P _ _ _ _ _ _ (fun v hv => hv.2.2) HP
```

### 14. `setproduct2_Forall` (TypeProgress.lean:1354; Rocq type_progress.v:2871-2874) — PROVED

Earlier still-`sorry` lemmas used: none.

Notes: Induction on `S`; `setproduct2_` unfolds to `[[w] ++ s] ++ setproduct2_ w S'`.

Proof (the tactic block after `:= by`, exactly as compiled):
```lean
  intro Hw HS
  induction S with
  | nil =>
    intro l hl
    simp [setproduct2_] at hl
  | cons s S' IH =>
    intro l hl
    simp only [setproduct2_, List.mem_append, List.mem_singleton] at hl
    rcases hl with rfl | hl
    · intro x hx
      simp only [List.singleton_append, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Hw
      · exact HS s (by simp) x hx
    · exact IH (fun t ht => HS t (List.mem_cons_of_mem _ ht)) l hl
```

## Axioms (`#print axioms` of the `_proof` versions, in Work.lean against the CURRENT file where the earlier lemmas are still `sorry`)
```
'TLC.evens_odds_size_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.Forall_evens_proof' depends on axioms: [propext, sorryAx]
'TLC.Forall_odds_proof' depends on axioms: [propext, sorryAx]
'TLC.Forall2_of_Forall_proof' depends on axioms: [propext]
'TLC.list_slice_size_eq_proof' depends on axioms: [propext]
'TLC.zip_lane_wf2_proof' depends on axioms: [propext]
'TLC.zip_wf_proof' depends on axioms: [propext, Quot.sound]
'TLC.size_zipWith_eq_proof' depends on axioms: [propext]
'TLC.shape_lanes_even_proof' depends on axioms: [propext, Classical.choice, Quot.sound, lanes_len]
'TLC.add_sub_parens_proof' depends on axioms: [propext, Quot.sound]
'TLC.call_indirect_progress_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.vcvtop_lane_total_proof' depends on axioms: [propext, demote_nonempty, promote_nonempty, trunc_sat_total]
'TLC.vcvtop_lanes_total_proof' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.setproduct2_Forall_proof' depends on axioms: [propext]
```
`sorryAx` appears only for `evens_odds_size`/`Forall_evens`/`Forall_odds` (via the still-`sorry` `evens_odds_ind`, which batch H12 proves) and `vcvtop_lanes_total` (via the still-`sorry` `Forall_exists_Forall2`, `Forall_map_P`, and, in this scratch setting only, the not-yet-merged `vcvtop_lane_total`). Project axioms used: `lanes_len` (shape_lanes_even), `trunc_sat_total`, `demote_nonempty`, `promote_nonempty` (vcvtop_lane_total); standard `propext`/`Classical.choice`/`Quot.sound`. No new axioms, no `sorry`/`admit`/`native_decide`.

## Final Lean check output (last `lake env lean Work.lean` run, exit 0, no errors/warnings)
```
'TLC.evens_odds_size_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.Forall_evens_proof' depends on axioms: [propext, sorryAx]
'TLC.Forall_odds_proof' depends on axioms: [propext, sorryAx]
'TLC.Forall2_of_Forall_proof' depends on axioms: [propext]
'TLC.list_slice_size_eq_proof' depends on axioms: [propext]
'TLC.zip_lane_wf2_proof' depends on axioms: [propext]
'TLC.zip_wf_proof' depends on axioms: [propext, Quot.sound]
'TLC.size_zipWith_eq_proof' depends on axioms: [propext]
'TLC.shape_lanes_even_proof' depends on axioms: [propext, Classical.choice, Quot.sound, lanes_len]
'TLC.add_sub_parens_proof' depends on axioms: [propext, Quot.sound]
'TLC.call_indirect_progress_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.vcvtop_lane_total_proof' depends on axioms: [propext, demote_nonempty, promote_nonempty, trunc_sat_total]
'TLC.vcvtop_lanes_total_proof' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.setproduct2_Forall_proof' depends on axioms: [propext]
```

## Safety check at END
```
safety check [prove-H13] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T130424.031516204Z-prove-H13-1478359.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

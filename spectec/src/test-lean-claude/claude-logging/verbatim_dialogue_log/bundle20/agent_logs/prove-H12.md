# prove-H12 (bundle20 progress port, proof batch H12)

Targets (TypeProgress.lean:1128-1236, in order): `lanes_nth_wf`, `vstore_lane_progress`, `Forall2_map_l`, `invert_typeof_I32_wf`, `size_list_repeat`, `Forall_list_repeat`, `bit_of_wf1`, `wf_dim_le16`, `wf_ishape_inv`, `holds_upto_intro`, `jlane_proj_wf`, `jlane_map_proj`, `evens_odds_ind`, `evens_odds_concat`.

RESULT: all 14 PROVED. No repo file was edited. Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H12/`. Only my own log file was written inside the target dir (plus the safety-check output files the check script itself creates).

## Safety check at START
```
safety check [prove-H12] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T125221.044587151Z-prove-H12-1470871.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- `Work.lean` (scratch): header of each target copied verbatim from TypeProgress.lean, renamed `<name>_proof`, plus guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all 14 guards pass).
- `WorkAx.lean` / `WorkAx2.lean`: same + `#print axioms`; in `WorkAx2` the three intra-batch uses (`lanes_nth_wf`, `wf_dim_le16`, `evens_odds_ind`) are redirected to the new `_proof` versions, which shows that the batch is closed up to external still-`sorry` lemmas.
- `Head.lean` / `HeadAx.lean` (merge simulation): the first ~1240 lines of the real `TypeProgress.lean` (through `evens_odds_concat`, cut before `evens_odds_size`) with the 14 `sorry` bodies replaced by the tactic blocks below, compiled with `lake env lean` against the same imports. It compiles with NO error (only `declaration uses sorry` warnings for the unrelated earlier/other lemmas), so the blocks drop into the real file unchanged, and the ordering rule holds (every dependency is earlier in the file or imported).
- One Lean process at a time (each run ~2.5 s because the oleans are mmapped).
- Tool trap met: `omega` does NOT work on goals/hypotheses typed `N` (an `abbrev N : Type := Nat`; omega matches the type syntactically and reports "No usable constraints found"). Worked around with `simp [h]` / `Nat.le_one_iff_eq_zero_or_eq_one` where the subject is `N`-typed; `omega` is used only on genuine `Nat` (list lengths, `Odd` witnesses).
- `cases ... with | ctor ...` slot trap met again: for `wf_num_` / `wf_uN` the index argument (`v_numtype`, `v_N`) takes NO name slot (`num__case_0 I x Hr Hx Hnt`, `num__case_1 F x Hx Hnt`, `uN_case_0 i Hb`).

## Proofs (tactic block after `:= by`, exactly as compiled)

### 1. `lanes_nth_wf` — proved (Rocq 2513-2523, same lemmas)
```lean
  intro Hsh Hc Hk
  have Hall := lanes__is_wf (shape.X lt (dim.mk_dim v_N)) c _ Hsh Hc rfl
  have H := Forall_size _ _ Hall k
  rw [lanes_len] at H
  exact H Hk
```
Uses: `lanes__is_wf` (wasm2.0.lean:4651, generated `theorem ... := sorry`), `Forall_size` (HelperLemmas), axiom `lanes_len` (HelperLemmas, mirrors Rocq `axioms.v`). `fun_lanetype (shape.X lt _) = lt` is by defeq.

### 2. `vstore_lane_progress` — proved (Rocq 2527-2549, same structure)
```lean
  intro Hc Hsh Hk HM
  have Hl := lanes_nth_wf _ _ _ _ Hsh Hc Hk
  obtain ⟨x, Hx, Hwx⟩ := wf_lane_Jnn_inv J _ Hl (wf_lane_Jnn_some J _ Hl)
  refine ⟨_, _, _, Step.vstore_lane_val (state.mk_state s f) _ c1 (jsize J) memarg laneidx _ J M ?_ rfl HM ?_ ?_ rfl ?_⟩
  · simp [proj_num__0]
  · rw [Hx]; simp [proj_lane__0]
  · rw [lanes_len]; exact Hk
  · rw [Hx]; exact Hwx
```
Earlier still-`sorry` lemmas used: `lanes_nth_wf` (this batch), `wf_lane_Jnn_inv`, `wf_lane_Jnn_some` (TypeProgress 814/820). Axiom: `lanes_len`.

### 3. `Forall2_map_l` — proved (Rocq 2551-2555; Lean induction because `Forall₂` is zip-based)
```lean
  intro H
  induction l with
  | nil => intro t ht; simp at ht
  | cons a l ih =>
    intro t ht
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact H a (List.mem_cons_self ..)
    · exact ih (fun x hx => H x (List.mem_cons_of_mem _ hx)) t ht
```
No project lemmas used.

### 4. `invert_typeof_I32_wf` — proved (Rocq 2556-2566, same case analysis)
```lean
  intro Ht Hwf
  obtain ⟨n, Heqv, Hwfn⟩ := invert_typeof_numtype_wf v numtype.I32 Ht Hwf
  cases Hwfn with
  | num__case_0 I x Hr Hx Hnt =>
    cases I with
    | I32 =>
      cases x with
      | mk_uN k => exact ⟨k, Heqv, Hx⟩
    | I64 => cases Hnt
  | num__case_1 F x Hx Hnt => cases F <;> cases Hnt
```
Earlier still-`sorry` lemma used: `invert_typeof_numtype_wf` (TypeProgress:232). (`Hx : wf_uN (size (valtype_Inn Inn.I32)).get! (uN.mk_uN k)` is accepted for `wf_uN 32 _` by defeq.)

### 5. `size_list_repeat` — proved
```lean
  simp
```
(core `List.length_replicate`.)

### 6. `Forall_list_repeat` — proved
```lean
  intro hx t ht
  rw [List.eq_of_mem_replicate ht]
  exact hx
```

### 7. `bit_of_wf1` — proved (Rocq 2579-2585)
```lean
  intro H
  cases H with
  | uN_case_0 _ Hb =>
    have Hle : i ≤ 1 := by simpa using Hb.2
    exact wf_bit.bit_case_0 i (Nat.le_one_iff_eq_zero_or_eq_one.mp Hle)
```

### 8. `wf_dim_le16` — proved (Rocq 2587-2591)
```lean
  intro H
  cases H with
  | dim_case_0 i Hi => rcases Hi with (((h | h) | h) | h) | h <;> simp [h]
```

### 9. `wf_ishape_inv` — proved (Rocq 2594-2602, same structure)
```lean
  intro H
  cases H with
  | ishape_case_0 J sh' Hs Hlt =>
    cases sh' with
    | X lt d =>
      cases d with
      | mk_dim M =>
        simp only [fun_lanetype] at Hlt
        subst Hlt
        refine ⟨J, M, rfl, Hs, ?_⟩
        cases Hs with
        | shape_case_0 _ _ Hd _ => exact wf_dim_le16 M Hd
```
Earlier still-`sorry` lemma used: `wf_dim_le16` (this batch).

### 10. `holds_upto_intro` — proved (Rocq 2604-2612; here `holds_upto P n = Forall P (List.range n)`)
```lean
  intro H k hk
  exact H k (List.mem_range.mp hk)
```

### 11. `jlane_proj_wf` — proved (Rocq 2614-2618)
```lean
  intro H x hx
  simp only [List.mem_map] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  obtain ⟨y, rfl, hy⟩ := H l hl
  exact hy
```
(`proj_lane__0 (mk_lane__0 J y)` and `Option.get!` reduce by defeq, so `exact hy` is enough.)

### 12. `jlane_map_proj` — proved (Rocq 2619-2624)
```lean
  intro H
  induction L with
  | nil => rfl
  | cons l L ih =>
    obtain ⟨x, rfl, _⟩ := H l (List.mem_cons_self ..)
    have := ih (fun t ht => H t (List.mem_cons_of_mem _ ht))
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨rfl, this⟩
```

### 13. `evens_odds_ind` — proved (Rocq 2636-2643, same length-bounded induction)
```lean
  intro H0 H1 H2
  have H : ∀ (n : Nat) (l : List T), l.length ≤ n → P l := by
    intro n
    induction n with
    | zero =>
      intro l hl
      cases l with
      | nil => exact H0
      | cons a l => simp at hl
    | succ n ih =>
      intro l hl
      match l with
      | [] => exact H0
      | [a] => exact H1 a
      | a :: b :: l =>
        apply H2
        apply ih
        simp at hl
        omega
  intro l
  exact H l.length l (Nat.le_refl _)
```

### 14. `evens_odds_concat` — proved (Rocq 2645-2650, via `evens_odds_ind`)
```lean
  revert l
  apply evens_odds_ind T (fun l => ¬ Odd l.length → concat_ T (List.zipWith (fun a b => [a, b]) (evens l) (odds l)) = l)
  · intro _
    simp [evens, odds, concat_]
  · intro a h
    exfalso
    exact h (by simp)
  · intro a b l IH Hl
    have hl' : ¬ Odd l.length := by
      intro hodd
      apply Hl
      simp only [List.length_cons]
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m + 1, by omega⟩
    have IH' := IH hl'
    simp [evens, odds, concat_, IH']
```
Earlier still-`sorry` lemma used: `evens_odds_ind` (this batch). `evens`/`odds` are the defs at TypeProgress:1223/1230.

## Final Lean check output (merge simulation `HeadAx.lean`, `#print axioms` lines)
```
'TLC.lanes_nth_wf' depends on axioms: [propext, sorryAx, lanes_len]
'TLC.vstore_lane_progress' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, lanes_len]
'TLC.Forall2_map_l' depends on axioms: [propext]
'TLC.invert_typeof_I32_wf' depends on axioms: [propext, sorryAx]
'TLC.size_list_repeat' depends on axioms: [propext]
'TLC.Forall_list_repeat' depends on axioms: [propext]
'TLC.bit_of_wf1' depends on axioms: [propext, Quot.sound]
'TLC.wf_dim_le16' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.wf_ishape_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.holds_upto_intro' depends on axioms: [propext, Quot.sound]
'TLC.jlane_proj_wf' depends on axioms: [propext, Quot.sound]
'TLC.jlane_map_proj' depends on axioms: [propext]
'TLC.evens_odds_ind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.evens_odds_concat' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(`sorryAx` appears only through the external still-`sorry` lemmas `lanes__is_wf` (wasm2.0.lean, generated), `wf_lane_Jnn_inv`, `wf_lane_Jnn_some`, `invert_typeof_numtype_wf`; the proof texts above contain no `sorry`/`admit`/`native_decide`/new axiom. Only project axiom used: `lanes_len`.)
`Work.lean` (guards for all 14 statements): no output, i.e. no error and no warning.

## Safety check at END
```
safety check [prove-H12] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T125753.789859210Z-prove-H12-1473415.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

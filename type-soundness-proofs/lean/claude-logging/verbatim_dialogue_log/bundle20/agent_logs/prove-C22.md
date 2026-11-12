# prove-C22 log (bundle20 progress port, proof batch C22)

Agent label: prove-C22. Brief: scratchpad/briefs/progress_prove_brief.md; task: scratchpad/briefs/task_prove-C22.md.
Only files written: this log, and scratch files under scratchpad/agents/prove-C22/. No repo file was edited, TypeProgress.lean included.

## Safety check (START)

```
safety check [prove-C22] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T135835.626414912Z-prove-C22-1516398.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Results

### `t_progress_be_instr`: proved

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro C v_instr t_1_lst t_2_lst a a_1 a_2 ih
  exact ih
```

- Still-`sorry` lemmas it relies on: none
- Notes: Rocq has no separate bullet (Instrs_ok_ind' handles it). The motives `t_progress_be_P C v_instr tf a` and `t_progress_be_P0 C [v_instr] tf (Instrs_ok.instr ..)` coincide definitionally, so the IH closes the goal.

### `t_progress_be_seq`: proved

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro C instr_1_lst instr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 ih1 ih2
  unfold t_progress_be_P0 at ih1 ih2 ⊢
  intro s f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  rw [← e1] at hts
  rw [List.map_append] at hnotbr hnotret hwf ⊢
  by_cases hconst : const_list (List.map admininstr_instr instr_1_lst) = true
  · -- Rocq: the first sequence is all values; continue with the second one
    obtain ⟨vs1, hvs1⟩ := const_es_exists _ hconst
    have hadmin1 : Instrs_ok2 s C (List.map admininstr_instr instr_1_lst) (mkFunctype t_1_lst t_2_lst) :=
      construct_instrs_from_ais s C instr_1_lst t_1_lst t_2_lst (by cases hstore; assumption) a
    rw [hvs1] at hadmin1
    obtain ⟨vts, hsub, hvok⟩ := ais_vals_typing_inversion s C vs1 t_1_lst t_2_lst hadmin1
    obtain ⟨ts_sub, ts0, ts11_sub, ts12_sup, h1, h2, hs0, hs1, hs2⟩ := hsub
    have e11 : ts11_sub = [] := resulttype_sub_empty _ hs1
    rw [e11, List.append_nil] at h1
    have hnb0 : Forall (fun t => t ≠ valtype.BOT) ts_sub := by
      rw [← h1]; exact typeof_vals_non_bot vcs t_1_lst hts
    have e0 : ts_sub = ts0 := resulttype_sub_non_bot _ _ hnb0 hs0
    have e2 : vts = ts12_sup := resulttype_sub_non_bot _ _ (Vals_ok_non_bot _ _ _ hvok) hs2
    obtain ⟨hvlen, hvf⟩ := hvok
    have hmapvs1 : List.map typeof vs1 = vts := Forall2_Val_ok_is_same_as_map s vts vs1 hvf hvlen
    have heqts2 : List.map typeof (vcs ++ vs1) = t_2_lst := by
      rw [List.map_append, hmapvs1, hts, h2, ← e0, ← h1, e2]
    have hnotbr2 := not_lf_br_left _ _ hconst hnotbr
    have hnotret2 := not_lf_return_left _ _ hconst hnotret
    rw [hvs1, ← List.append_assoc, ← List.map_append] at hwf
    have hwfvs1 : Forall (fun v => wf_val v) vs1 := by
      have h := wf_forall_admin _ a_3
      rw [hvs1] at h
      exact (wf_forall_admin_val vs1).mpr h
    have hwfv' : Forall (fun e => wf_val e) (vcs ++ vs1) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hwfv x hx
      · exact hwfvs1 x hx
    rcases ih2 s f C' (vcs ++ vs1) t_2_lst t_3_lst lab ret hwf hwfv' rfl hctx hmod heqts2 hstore hnotbr2
        hnotret2 with hconst2 | ⟨s', f', es', hstep⟩
    · left
      exact const_list_concat _ _ hconst hconst2
    · right
      refine ⟨s', f', es', ?_⟩
      rw [hvs1, ← List.append_assoc, ← List.map_append]
      exact hstep
  · -- Rocq: the first sequence is not all values; it steps, in the context of the second one
    have hnotbr1 := not_lf_br_right _ _ hnotbr
    have hnotret1 := not_lf_return_right _ _ hnotret
    rw [← List.append_assoc] at hwf
    obtain ⟨hwf1, hwf2⟩ := (wf_config_app _ _ _).mp hwf
    rcases ih1 s f C' vcs t_1_lst t_2_lst lab ret hwf1 hwfv rfl hctx hmod hts hstore hnotbr1 hnotret1 with
      hc | ⟨s', f', es1', hstep⟩
    · exact absurd hc hconst
    · right
      refine ⟨s', f', es1' ++ List.map admininstr_instr instr_2_lst, ?_⟩
      rw [← List.append_assoc]
      rcases instr_2_lst with _ | ⟨i2, instr_2_lst⟩
      · simp only [List.map_nil, List.append_nil]
        exact hstep
      · have hwf' := Step_is_wf (state.mk_state s f) _ _ hwf1 hstore hstep
        have h := Step.ctxt_instrs (state.mk_state s f) []
          (List.map admininstr_val vcs ++ List.map admininstr_instr instr_1_lst)
          (List.map admininstr_instr (i2 :: instr_2_lst)) (state.mk_state s' f') es1' hstep
          (Or.inr (by simp)) hwf1 hwf'
        exact h
```

- Still-`sorry` lemmas it relies on: const_es_exists, const_list_concat, wf_config_app, not_lf_br_right, not_lf_br_left, not_lf_return_right, not_lf_return_left, Forall2_Val_ok_is_same_as_map, wf_forall_admin_val, wf_forall_admin, typeof_vals_non_bot (earlier TypeProgress lemmas, all still `sorry`); generated `Step_is_wf` (wasm2.0.lean, proved there, but transitively depends on the `sorry` `Step_read_is_wf`, which is Admitted in Rocq too)
- Notes: Ports Rocq type_progress.v:5399-5466 step by step. Case on `const_list (map admininstr_instr bes1)`. (1) Const: `const_es_exists` gives `vs1`; `construct_instrs_from_ais` + `ais_vals_typing_inversion` + `resulttype_sub_empty` / `resulttype_sub_non_bot` (with `typeof_vals_non_bot`, `Vals_ok_non_bot`) + `Forall2_Val_ok_is_same_as_map` give `map typeof (vcs ++ vs1) = t_2_lst`; then IH2 on `vcs ++ vs1`, finishing with `const_list_concat` or the rewritten step. (2) Non-const: IH1 (via `wf_config_app`, `not_lf_*_right`); if `bes2 = []`, the step is used directly, otherwise `Step.ctxt_instrs` with `val_lst := []` and `admininstr_1_lst := map admininstr_instr bes2`; the post-step wf premise comes from `Step_is_wf`, as in Rocq. Rocq's `invert_storeok` (needed for `wf_store s`) becomes `(by cases hstore; assumption)`, which uses no TypePreservation lemma.

### `t_progress_be_sub`: proved

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro C instr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 ih
  unfold t_progress_be_P0 at ih ⊢
  intro s f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t'_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  have hnb : Forall (fun t => t ≠ valtype.BOT) t'_1_lst := by
    rw [e1]; exact typeof_vals_non_bot vcs ts1 hts
  have e2 : t'_1_lst = t_1_lst := resulttype_sub_non_bot _ _ hnb a_1
  exact ih s f C' vcs t_1_lst t_2_lst lab ret hwf hwfv rfl hctx hmod (by rw [hts, ← e1, e2]) hstore hnotbr
    hnotret
```

- Still-`sorry` lemmas it relies on: typeof_vals_non_bot
- Notes: Ports Rocq type_progress.v:5466-5475: `t'_1 = ts1 = map typeof vcs` is non-BOT, so `resulttype_sub_non_bot` gives `t'_1 = t_1`; then apply the IH at `t_1 -> t_2`.

### `t_progress_be_frame`: proved

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro C instr_lst t_lst t_1_lst t_2_lst a a_1 a_2 ih
  unfold t_progress_be_P0 at ih ⊢
  intro s f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t_lst ++ t_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  rw [← e1] at hts
  -- Rocq splits `vcs` at `size ts` (take/drop); here split it along the type list directly
  obtain ⟨vcs1, vcs2, rfl, _hts1, hts2⟩ := List.map_eq_append_iff.mp hts
  rw [List.map_append, List.append_assoc] at hwf
  obtain ⟨_hwf1, hwf2⟩ := (wf_config_app _ _ _).mp hwf
  have hwfv2 : Forall (fun e => wf_val e) vcs2 := fun x hx => hwfv x (List.mem_append_right _ hx)
  rcases ih s f C' vcs2 t_1_lst t_2_lst lab ret hwf2 hwfv2 rfl hctx hmod hts2 hstore hnotbr hnotret with
    hconst | ⟨s', f', es', hstep⟩
  · exact Or.inl hconst
  · right
    refine ⟨s', f', List.map admininstr_val vcs1 ++ es', ?_⟩
    rw [List.map_append, List.append_assoc]
    rcases vcs1 with _ | ⟨v, vcs1⟩
    · simp only [List.map_nil, List.nil_append]
      exact hstep
    · have hwf' := Step_is_wf (state.mk_state s f) _ _ hwf2 hstore hstep
      have h := Step.ctxt_instrs (state.mk_state s f) (v :: vcs1)
        (List.map admininstr_val vcs2 ++ List.map admininstr_instr instr_lst) [] (state.mk_state s' f') es' hstep
        (Or.inl (List.cons_ne_nil _ _)) hwf2 hwf'
      simp only [List.append_nil] at h
      exact h
```

- Still-`sorry` lemmas it relies on: wf_config_app (TypeProgress, still `sorry`); generated `Step_is_wf` (transitively `sorry` via `Step_read_is_wf`)
- Notes: Ports Rocq type_progress.v:5475-5512. Deviation: Rocq splits `vcs` at `size ts` with take/drop; here `List.map_eq_append_iff` on `map typeof vcs = t_lst ++ t_1_lst` gives `vcs = vcs1 ++ vcs2` with `map typeof vcs2 = t_1_lst`, which is equivalent and avoids take/drop arithmetic. Then the IH on `vcs2` (wf via `wf_config_app`); if `vcs1 = []` the step is direct, otherwise `Step.ctxt_instrs` with `val_lst := vcs1` and `admininstr_1_lst := []`, plus `Step_is_wf` (as Rocq's `destruct vcs1`).

Axioms: no project axioms (HelperLemmas) are used, and there is no `sorry`, `admit` or `native_decide` in the proofs. Ordering rule: every TypeProgress lemma used sits before line 2322 (wf_config_app 65, const_list_concat 97, const_es_exists 110, not_lf_* 353-372, Forall2_Val_ok_is_same_as_map 384, wf_forall_admin_val 404, wf_forall_admin 410, typeof_vals_non_bot 580). Everything else comes from wasm2.0 (`Step_is_wf`, `Step.ctxt_instrs`), TypingLemmas (`construct_instrs_from_ais`, `ais_vals_typing_inversion`, `Vals_ok_non_bot`) and Subtyping (`mkFunctype`, `resulttype_sub_empty`, `resulttype_sub_non_bot`).

Brief discrepancy (FYI): the brief says TypePreservation is not imported, but TypeProgress.lean line 7 does `import TypePreservation`. The final proofs use nothing from it; `Store_ok_wf_store` was replaced by `(by cases hstore; assumption)`.

## Final Lean checks

1. Work.lean (header copies + `type_of%` rfl guards), `timeout 900 lake env lean Work.lean`: exit 0 with no output, so no errors or warnings. `#print axioms` of the four `_proof` copies:

```
'TLC.t_progress_be_instr_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_be_seq_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_sub_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_frame_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

   (The `sorryAx` comes only from the still-`sorry` dependencies listed above.)

2. Integration: scratch copy TPmerged.lean, which is TypeProgress.lean with the four `:= sorry` replaced by `:= by` plus the bodies above (generated by merge.py). `lake env lean TPmerged.lean`: exit 0, 0 errors. Warnings in lines 2310-2500, where the targets are at 2322/2335/2415/2439 and `t_progress_be` is at 2481:

```
TPmerged.lean:2315:8: warning: declaration uses `sorry`
```

   (That is `t_progress_be_empty`, not a C22 target. The four targets and the assembled `t_progress_be` produce no warnings.) Last lines of that run:

```
TPmerged.lean:2774:8: warning: declaration uses `sorry`
TPmerged.lean:2782:8: warning: declaration uses `sorry`
TPmerged.lean:2790:8: warning: declaration uses `sorry`
```

## Safety check (END)

```
safety check [prove-C22] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T140713.281530244Z-prove-C22-1522043.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

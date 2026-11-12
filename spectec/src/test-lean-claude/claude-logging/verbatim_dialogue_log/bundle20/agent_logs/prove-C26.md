# prove-C26 log (bundle20 progress port, proof batch C26)

Agent label: prove-C26. Brief: scratchpad/briefs/progress_prove_brief.md; task: scratchpad/briefs/task_prove-C26.md.
Only files written: this log, and scratch files under scratchpad/agents/prove-C26/ (instr.txt, seq.txt, sub.txt,
gen.py, Work.lean, merge.py, TPmerged.lean, merged_out.txt). No repo file was edited, TypeProgress.lean included.
No state-changing git, no agents spawned, one Lean process at a time (`lake env lean` only, never `lake build`).

## Safety check (START)

```
safety check [prove-C26] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T140853.186553176Z-prove-C26-1522941.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Results

All three targets were proved, and each compiled on the first attempt.

### `t_progress_e_instr`: proved

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro C v_admininstr t_1_lst t_2_lst a a_1 a_2 a_3 ih
  exact ih
```

- Still-`sorry` lemmas it relies on: none
- Notes: Rocq has no separate bullet here (closed by the `=> //` of the `Admin_instrs_ok_ind'` application).
  The motives `t_progress_e_P s C e tf a` and `t_progress_e_P0 s C [e] tf (Instrs_ok2.instr ..)` coincide
  definitionally (`es := [e]`), so the IH closes the goal. Axioms: [propext, Classical.choice, Quot.sound], with no `sorryAx`.

### `t_progress_e_seq`: proved

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro C admininstr_1_lst admininstr_2_lst t_1_lst t_3_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih1 ih2
  unfold t_progress_e_P0 at ih1 ih2 ⊢
  intro f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  rw [← e1] at hts
  by_cases hconst : const_list admininstr_1_lst = true
  · -- Rocq: the first sequence is all values; continue with the second one under `vcs ++ vs1`
    obtain ⟨vs1, hvs1⟩ := const_es_exists _ hconst
    have hadmin1 : Instrs_ok2 s C admininstr_1_lst (mkFunctype t_1_lst t_2_lst) := a
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
      have h := a_4
      rw [hvs1] at h
      exact (wf_forall_admin_val vs1).mpr h
    have hwfv' : Forall (fun e => wf_val e) (vcs ++ vs1) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hwfv x hx
      · exact hwfvs1 x hx
    rw [hvs1, ← List.append_assoc, ← List.map_append]
    exact ih2 f C' (vcs ++ vs1) t_2_lst t_3_lst lab ret hwf hwfv' rfl hctx hmod heqts2 hstore hnotbr2 hnotret2
  · -- Rocq: the first sequence is not all values; it reduces (or is a trap), in the context of the second
    have hnotbr1 := not_lf_br_right _ _ hnotbr
    have hnotret1 := not_lf_return_right _ _ hnotret
    rw [← List.append_assoc] at hwf
    obtain ⟨hwf1, _hwf2⟩ := (wf_config_app _ _ _).mp hwf
    have ih1r :=
      ih1 f C' vcs t_1_lst t_2_lst lab ret hwf1 hwfv rfl hctx hmod hts hstore hnotbr1 hnotret1
    rw [← List.append_assoc]
    rcases admininstr_2_lst with _ | ⟨a2, es2⟩
    · rw [List.append_nil]
      exact ih1r
    · rcases ih1r with hterm | ⟨s', f', es1', hstep⟩
      · rcases hterm with hc | htrap
        · exfalso
          rw [const_list_cat, Bool.and_eq_true] at hc
          exact hconst hc.2
        · -- Rocq: `v_e_trap` gives `vcs = []`, `es1 = [TRAP]`; then `trap_vals` with `val_lst := []`
          right
          refine ⟨s, f, [admininstr.TRAP], ?_⟩
          rw [htrap]
          exact Step.pure _ _ _ (Step_pure.trap_vals [] (a2 :: es2) (Or.inr (List.cons_ne_nil _ _)))
      · right
        refine ⟨s', f', es1' ++ (a2 :: es2), ?_⟩
        have hwf' := Step_is_wf (state.mk_state s f) _ _ hwf1 hstore hstep
        exact Step.ctxt_instrs (state.mk_state s f) [] (List.map admininstr_val vcs ++ admininstr_1_lst)
          (a2 :: es2) (state.mk_state s' f') es1' hstep (Or.inr (List.cons_ne_nil _ _)) hwf1 hwf'
```

- Still-`sorry` lemmas it relies on (all earlier in TypeProgress.lean): `wf_config_app` (65),
  `const_list_cat` (93), `const_es_exists` (110), `not_lf_br_right` (353), `not_lf_br_left` (359),
  `not_lf_return_right` (366), `not_lf_return_left` (372), `Forall2_Val_ok_is_same_as_map` (384),
  `wf_forall_admin_val` (404), `typeof_vals_non_bot` (580). Also the generated `Step_is_wf` (wasm2.0.lean,
  proved there, but `#print axioms` shows it transitively depends on `sorryAx`, through the `sorry`
  `Step_read_is_wf`, which is Admitted in Rocq too).
- Notes: This ports Rocq type_progress.v:5875-5949 step by step and mirrors the proved `t_progress_be_seq`
  (prove-C22). The proof cases on `const_list es1`.
  (1) Const: `const_es_exists` gives `vs1`. Then `ais_vals_typing_inversion` (applied directly to
  `a`, since there is no `construct_instrs_from_ais` step at the admin level), `resulttype_sub_empty`,
  `resulttype_sub_non_bot` (with `typeof_vals_non_bot` / `Vals_ok_non_bot`) and
  `Forall2_Val_ok_is_same_as_map` give `map typeof (vcs ++ vs1) = t_2`. The wf of `vs1` comes from
  `a_4` via `wf_forall_admin_val`. IH2 on `vcs ++ vs1` then closes the goal once it is rewritten to
  `map admininstr_val (vcs ++ vs1) ++ es2`. Rocq's case split of IH2 into const/trap/step and its re-rewriting
  in each branch collapse into a single `rw` + `exact`.
  (2) Non-const: IH1 on `map vcs ++ es1` (wf via `wf_config_app`, `not_lf_*_right`). If `es2 = []`, IH1
  is the goal (Rocq `rewrite cats0; apply IH'`). Otherwise:
  - a const IH1 result contradicts `hconst` (`const_list_cat`);
  - a TRAP result `map vcs ++ es1 = [TRAP]` is rewritten in the goal directly. That gives `[TRAP] ++ es2`,
    which steps by `Step.pure` + `Step_pure.trap_vals [] es2` (Rocq first uses `v_e_trap` +
    `v_to_e_const` to get `vcs = []`, `es1 = [TRAP]`; the direct rewrite makes that unnecessary, so neither
    lemma is used);
  - a step `es1'` lifts by `Step.ctxt_instrs` with `val_lst := []`, `admininstr_1_lst := es2`. The
    post-state wf comes from `Step_is_wf`, as in Rocq.
  Axioms: [propext, sorryAx, Classical.choice, Quot.sound]. The `sorryAx` comes only from the
  dependencies listed above.

### `t_progress_e_sub`: proved

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro C admininstr_lst t'_1_lst t'_2_lst t_1_lst t_2_lst a a_1 a_2 a_3 a_4 a_5 ih
  unfold t_progress_e_P0 at ih ⊢
  intro f C' vcs ts1 ts2 lab ret hwf hwfv htf hctx hmod hts hstore hnotbr hnotret
  have e1 : t'_1_lst = ts1 := by
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at htf
    exact htf.1
  have hnb : Forall (fun t => t ≠ valtype.BOT) t'_1_lst := by
    rw [e1]; exact typeof_vals_non_bot vcs ts1 hts
  have e2 : t'_1_lst = t_1_lst := resulttype_sub_non_bot _ _ hnb a_1
  exact ih f C' vcs t_1_lst t_2_lst lab ret hwf hwfv rfl hctx hmod (by rw [hts, ← e1, e2]) hstore hnotbr
    hnotret
```

- Still-`sorry` lemmas it relies on: `typeof_vals_non_bot` (TypeProgress.lean:580)
- Notes: This ports Rocq type_progress.v:5949-5958. `t'_1 = ts1 = map typeof vcs` is non-BOT, so
  `resulttype_sub_non_bot` gives `t'_1 = t_1`, and the IH applies at `t_1 -> t_2` (Rocq: `eapply IH; eauto`).
  Axioms: [propext, sorryAx, Classical.choice, Quot.sound], where `sorryAx` comes only from `typeof_vals_non_bot`.

Axioms summary: no project axioms (HelperLemmas) are used, and the proofs contain no `sorry`, `admit` or `native_decide`.
Ordering rule: every TypeProgress lemma used sits before line 2563 (lines 65-580). Everything else comes
from wasm2.0 (`Step_is_wf`, `Step.pure`, `Step_pure.trap_vals`, `Step.ctxt_instrs`), TypingLemmas
(`ais_vals_typing_inversion`, `Vals_ok_non_bot`) and Subtyping (`mkFunctype`, `resulttype_sub_empty`,
`resulttype_sub_non_bot`). Nothing comes from TypePreservation (which TypeProgress.lean:7 does import).

## Final Lean checks

1. Work.lean (headers copied verbatim from TypeProgress.lean by gen.py, renamed `_proof`, with
   `example : type_of% @X_proof = type_of% @X := rfl` guards). `timeout 900 lake env lean Work.lean` exited 0 and
   printed no errors or warnings, only the `#print axioms` lines:

```
'TLC.t_progress_e_instr_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_e_seq_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_e_sub_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

2. Integration: TPmerged.lean is a scratch copy of TypeProgress.lean with the three `:= sorry` replaced by
   `:= by` + the bodies above (made by merge.py), plus `#print axioms` lines before `end TLC`.
   `timeout 900 lake env lean TPmerged.lean` exited 0 with 0 errors. All 277 warnings are
   "declaration uses `sorry`" on other declarations. None are at the targets (merged lines 2563, 2576, 2657).
   The nearby warnings are 2547 (`t_progress_e_ref`), 2556 (`t_progress_e_trap`), 2681
   (`t_progress_e_Instrs_ok2_frame`) and 2693 (`t_progress_e_mk_Expr_ok2`), all of which are other batches' targets.
   The assembled `t_progress_e` (2706) gets no warning. Last lines of that run:

```
'TLC.t_progress_e_instr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_e_seq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_e_sub' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.ais_vals_typing_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.Vals_ok_non_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.resulttype_sub_non_bot' depends on axioms: [propext]
'TLC.resulttype_sub_empty' depends on axioms: [propext]
'Step_is_wf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Safety check (END)

```
safety check [prove-C26] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T141343.707724544Z-prove-C26-1526460.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

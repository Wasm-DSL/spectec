# prove-C02 log (bundle20 progress port, proof batch C02)

Targets (in order): `t_progress_be_loop` (TypeProgress.lean:1588), `t_progress_be_if` (:1610), `t_progress_be_br` (:1642);
Rocq `type_progress.v:3229-3344` (bullets `Instr_ok__loop`, `Instr_ok__if`, `Instr_ok__br` of `t_progress_be`).

Writes: only this log file and scratch files under
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C02/`.
No repo file edited (TypeProgress.lean untouched), no state-changing git, no agents spawned, no `lake build`,
one Lean process at a time.

## Safety check at START
```
safety check [prove-C02] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T131211.646689724Z-prove-C02-1489614.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
Scratch `Work.lean` = `import TypeProgress` + `namespace TLC` + each target's header copied verbatim from
TypeProgress.lean by `awk` (only the name renamed to `<name>_proof`, `:= sorry` -> `:= by`) + the proof +
the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl`. Checked with
`timeout 900 lake env lean Work.lean` (TypeProgress.olean 20:18:19 is newer than TypeProgress.lean 20:18:16,
so the guard compares against the current statements). TypeProgress.lean contains no `@[simp]`, `attribute`,
`instance`, notation, `open`, `set_option` or `section/variable`, so the later declarations visible in the
scratch environment cannot change tactic behaviour; every lemma used is declared before line 1588
(`wf_config_app`:65, `typeof_append`:188, `invert_typeof_I32`:209, `not_lf_br_singleton`:344,
`lookup_types`:554, `t_progress_be_P`:1486) or in an import (`Step_is_wf`, wasm2.0.lean:16045, proved).
All three compiled on the first attempt.

### `t_progress_be_loop` : proved
Still-`sorry` earlier lemmas relied on: `lookup_types`.
```lean
  intro C bt bes vt1 vt2 HBok HType HWfC HWfinstr HWfC' IHH
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  refine ⟨s, f, [admininstr.LABEL_ vt1.length [instr.LOOP bt bes] (List.map admininstr_val vcs ++ List.map admininstr_instr bes)], ?_⟩
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  have Hfun : fun_blocktype (state.mk_state s f) bt = functype.mk_functype (list.mk_list vt1) (list.mk_list vt2) := by
    cases HBok with
    | valtype valtype_opt _ _ => cases valtype_opt <;> rfl
    | typeidx x _ _ _ Hty _ _ =>
      show f.MODULE.TYPES[proj_uN_0 x]! = _
      rw [← lookup_types s f C' (List.map typeof f.LOCALS) lab ret _ Hmod, ← Hcontext]
      exact Hty
  have Hlen : vcs.length = vt1.length := by rw [← Hts, List.length_map]
  exact Step.read _ _ _ (Step_read.loop (state.mk_state s f) vt1.length vcs bt bes vt1 vt2.length
    vt2 Hfun Hlen.symm rfl rfl)
```
Notes: same shape as C01's `t_progress_be_block`, with Rocq's `Step_read__loop` instantiation
`(k := |vt1|)`: `Step_read.loop z k val_lst bt instr_lst t_1_lst v_n t_2_lst` with `k = vt1.length`,
`v_n = vt2.length`; premises `Hfun`, `vt1.length = vcs.length` (`Hlen.symm`), `rfl`, `rfl`. Witness
`[LABEL_ |vt1| [LOOP bt bes] (vals ++ bes)]` as in Rocq. `fun_blocktype` goal: Rocq's
`inversion HBok; destruct valtype_opt` / `erewrite <- lookup_types` = `cases HBok` (C is an inductive
parameter of `Blocktype_ok`, so no slot for it) + `show f.MODULE.TYPES[proj_uN_0 x]! = _` +
`rw [← lookup_types .. Hmod, ← Hcontext]`. IH unused, as in Rocq.

### `t_progress_be_if` : proved
Still-`sorry` earlier lemmas relied on: `typeof_append`, `invert_typeof_I32`, `wf_config_app` (plus imported `Step_is_wf`, which transitively uses sorryAx in wasm2.0.lean).
```lean
  intro C bt bes1 bes2 vt1 vt2 HBok HType HType2 HWfC HWfinstr HWfC' IHH IHH2
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  obtain ⟨v, Hvcs, Hvs1, Hvs2⟩ := typeof_append vt1 valtype.I32 vcs Hts
  generalize List.take vt1.length vcs = vs1 at Hvcs Hvs1
  subst Hvcs
  have HWfv : wf_val v := HWfVals v (by simp)
  obtain ⟨n, Heqv⟩ := invert_typeof_I32 v Hvs2 HWfv
  simp only [List.map_append, List.append_assoc, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, admininstr_instr] at HWfConfig ⊢
  rw [Heqv] at HWfConfig ⊢
  have Hwf1 := ((wf_config_app _ _ _).mp HWfConfig).2
  cases n with
  | zero =>
    have HStep : Step (config.mk_config (state.mk_state s f)
        [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)), admininstr.IFELSE bt bes1 bes2])
        (config.mk_config (state.mk_state s f) [admininstr.BLOCK bt bes2]) :=
      Step.pure _ _ _ (Step_pure.if_false _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]))
    have Hwf2 := Step_is_wf _ _ _ Hwf1 Hstore HStep
    cases vs1 with
    | nil => exact ⟨s, f, _, HStep⟩
    | cons x xs =>
      exact ⟨s, f, _, Step.ctxt_instrs _ (x :: xs) _ [] _ _ HStep (Or.inl (List.cons_ne_nil _ _)) Hwf1 Hwf2⟩
  | succ n' =>
    have HStep : Step (config.mk_config (state.mk_state s f)
        [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (n' + 1))), admininstr.IFELSE bt bes1 bes2])
        (config.mk_config (state.mk_state s f) [admininstr.BLOCK bt bes1]) :=
      Step.pure _ _ _ (Step_pure.if_true _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]))
    have Hwf2 := Step_is_wf _ _ _ Hwf1 Hstore HStep
    cases vs1 with
    | nil => exact ⟨s, f, _, HStep⟩
    | cons x xs =>
      exact ⟨s, f, _, Step.ctxt_instrs _ (x :: xs) _ [] _ _ HStep (Or.inl (List.cons_ne_nil _ _)) Hwf1 Hwf2⟩
```
Notes: follows Rocq: `case: Htf`, `typeof_append` (split `vcs = vs1 ++ [v]`), `Forall` gives `wf_val v`,
`invert_typeof_I32` gives `admininstr_val v = CONST I32 (mk_num__0 I32 (mk_uN n))`, rewrite the config as
`map admininstr_val vs1 ++ [CONST .., IFELSE ..]`, `case: n` (`zero` -> `Step_pure.if_false` to
`BLOCK bt bes2`, `succ n'` -> `Step_pure.if_true` to `BLOCK bt bes1`), then either the bare `pure` step
(no values below) or `Step.ctxt_instrs` with `admininstr_1_lst := []` (Rocq's `cats0` trick + `ctxt_instrs`).
Deviations (Lean-way simplifications, same intuition):
- Rocq splits on `vt1` (`case Hvt1s: vt1`) and then derives `vcs = []` (`map_eq_nil`) / `vcs ≠ []`;
  here I `generalize` `take |vt1| vcs` to `vs1`, `subst` `vcs = vs1 ++ [v]`, and split on `vs1` directly,
  which gives both facts for free (no `map_eq_nil` needed).
- Rocq proves the `wf_config` premises of `ctxt_instrs` once by `Step_is_wf` (false branch) and once by
  hand via `wf_config_app` + inversions (true branch). Here both branches do the same: the source premise is
  `((wf_config_app _ _ _).mp HWfConfig).2` and the target premise is `Step_is_wf _ _ _ Hwf1 Hstore HStep`
  (bundle19 `Step_is_wf` takes a `Store_ok (fun_store z)` premise; `Hstore : Store_ok s` fits by defeq).
- Both IHs are unused, as in Rocq.

### `t_progress_be_br` : proved
Still-`sorry` earlier lemmas relied on: `not_lf_br_singleton`.
```lean
  intro C l ts1 ts ts2 Hlablen Hlablookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  exact (not_lf_br_singleton _ l Hnotbr rfl).elim
```
Notes: Rocq `move/not_lf_br_singleton: Hnotbr => Hnotbr. by move/(_ l): Hnotbr.` =
`not_lf_br_singleton _ l Hnotbr : admininstr_instr (BR l) ≠ BR l` applied to `rfl` (defeq), `.elim`.
Sorry-free alternative (VERIFIED, Work3.lean): replace the last line by `exact (Hnotbr [] l [] rfl).elim`
(directly from the definition of `not_lf_br`); `#print axioms` of that variant = [propext, Classical.choice,
Quot.sound] (no sorryAx). I report the faithful Rocq version as the main proof; the main thread may pick either.

## Final Lean check output
`timeout 900 lake env lean Work.lean` (3 proofs + 3 rfl guards): no output (no errors, no warnings).
Same file with `#print axioms` appended (Work2.lean):
```
'TLC.t_progress_be_loop_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_if_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_br_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
No `sorry`/`admit`/`native_decide`/new axiom in the proofs themselves; no HelperLemmas axiom used directly.
`sorryAx` sources: loop -> `lookup_types`; br -> `not_lf_br_singleton`; if -> `typeof_append`,
`invert_typeof_I32`, `wf_config_app` AND, transitively, `Step_is_wf` (wasm2.0.lean:16045; proved itself, but
Work4.lean shows `Step_read_is_wf` and `Step_pure_is_wf` both depend on `sorryAx`). Rocq's proof also uses
`Step_is_wf`, so this is faithful; to drop that dependency one would build `wf_config [BLOCK bt bes]` by hand
from the IFELSE well-formedness (as Rocq's true branch does) — not done.
Extra checks (Work3.lean / Work4.lean):
```
'TLC.t_progress_be_br_alt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Step_is_wf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Step_read_is_wf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Step_pure_is_wf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Safety check at END
```
safety check [prove-C02] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T131659.511517413Z-prove-C02-1492903.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

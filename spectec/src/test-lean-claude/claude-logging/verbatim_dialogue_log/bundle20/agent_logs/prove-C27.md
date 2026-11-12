# prove-C27 log (bundle20 progress port, proof batch C27)

Agent label: `prove-C27`. Brief: `scratchpad/briefs/progress_prove_brief.md`; task: `scratchpad/briefs/task_prove-C27.md`.
Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C27/`
(`Work.lean` = header-copy + `rfl` guard for both targets; `Axioms.lean` = `#print axioms` of used lemmas).
No repo file was edited (TypeProgress.lean untouched; the main thread merges). Only this log file was written
inside the repo. One Lean process at a time (`lake env lean`), no `lake build`.

## Safety check at START

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C27`

```
safety check [prove-C27] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T141137.162246208Z-prove-C27-1524870.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Target 1: `t_progress_e_Instrs_ok2_frame` (TypeProgress.lean:2604; Rocq type_progress.v:5958-6005)

Status: **proved**.

Proof body (goes after `:= by`, exactly as compiled):

```lean
  intro C es ts ts1 ts2 Hadmin HWfS HWfC HWfAIs IH
  unfold t_progress_e_P0 at IH ⊢
  intro f C' vcs ts1' ts2' lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  -- Rocq: `Heqts` / `cat_take_drop`: split `vcs` at `size ts`
  have Htf1 : ts ++ ts1 = ts1' := by
    unfold mkFunctype at Htf
    injection Htf with h1 h2
    injection h1
  obtain ⟨vcs1, vcs2, rfl, Hts1, Heqts⟩ := List.map_eq_append_iff.mp (Hts.trans Htf1.symm)
  rw [List.map_append, List.append_assoc] at HWfConfig
  obtain ⟨_HWfC1, HWfC2⟩ := (wf_config_app _ _ _).mp HWfConfig
  have HWfV2 : Forall (fun e => wf_val e) vcs2 := fun x hx => HWfVals x (List.mem_append_right _ hx)
  have IH' := IH f C' vcs2 ts1 ts2 lab ret HWfC2 HWfV2 rfl Hcontext Hmod Heqts Hstore Hnotbr Hnotret
  rw [List.map_append, List.append_assoc]
  rcases IH' with (Hconst | Htrap) | ⟨s', f', es', IH'⟩
  · left; left
    exact const_list_concat _ _ (v_to_e_const vcs1) Hconst
  · rw [Htrap]
    cases vcs1 with
    | nil => left; right; rfl
    | cons vc1 vcs1 =>
      right
      exact ⟨s, f, [admininstr.TRAP],
        Step.pure _ _ _ (Step_pure.trap_vals (vc1 :: vcs1) [] (Or.inl (List.cons_ne_nil _ _)))⟩
  · right
    refine ⟨s', f', List.map admininstr_val vcs1 ++ es', ?_⟩
    have HWfStep := Step_is_wf _ _ _ HWfC2 Hstore IH'
    cases vcs1 with
    | nil => simpa using IH'
    | cons vc1 vcs1 =>
      have H := Step.ctxt_instrs _ (vc1 :: vcs1) (List.map admininstr_val vcs2 ++ es) [] _ es' IH'
        (Or.inl (List.cons_ne_nil _ _)) HWfC2 HWfStep
      simp only [List.append_nil] at H
      exact H
```

Still-`sorry` earlier TypeProgress lemmas used: `wf_config_app` (:65), `v_to_e_const` (:84),
`const_list_concat` (:97). Also uses the imported `Step_is_wf` (wasm2.0.lean:16045, bundle19 hand-edited
version with the `Store_ok (fun_store z)` premise), which itself transitively depends on `sorryAx`.

Notes: follows the Rocq bullet step for step (IH on the suffix `drop (size ts) vcs` with `Heqtf`/`Heqts`;
`wf_config_app` split; const case via `const_list_concat`/`v_to_e_const`; trap case `destruct vcs1` +
`pure`/`trap_vals`; step case `Step_is_wf` + `destruct vcs1` + `ctxt_instrs` with `admininstr_1_lst := []`).
Lean deviation: Rocq's `cat_take_drop`/`map_drop`/`drop_cat` arithmetic is replaced by one
`List.map_eq_append_iff` destructuring of `map typeof vcs = ts ++ ts1` into `vcs = vcs1 ++ vcs2` with
`map typeof vcs1 = ts`, `map typeof vcs2 = ts1`; Rocq's `v_to_e_cat`/`catA` rewrites are core
`List.map_append`/`List.append_assoc`.

## Target 2: `t_progress_e_mk_Expr_ok2` (TypeProgress.lean:2616; Rocq type_progress.v:6006-6062)

Status: **proved**.

Proof body (goes after `:= by`, exactly as compiled):

```lean
  intro C es ts Hadmin HWfS HWfC HWfAIs IH
  unfold t_progress_e_P0 at IH
  unfold t_progress_e_P1
  intro f C' ret HWfConfig HEq HFrameOk Hstore Hnotbr Hnotret
  have Hloc := frame_t_context_local_types _ _ _ HFrameOk
  have Hlab := frame_t_context_label_empty _ _ _ HFrameOk
  cases HFrameOk
  rename_i val_lst v_moduleinst t_lst C0 Hmod _ _ _ _ _ _
  have HEq' : C = upd_local_label_return C0 (List.map typeof val_lst) [] ret := by
    rw [HEq]
    unfold upd_return upd_local_label_return upd_label upd_local
    congr 1
  have IH' := IH { LOCALS := val_lst, MODULE := v_moduleinst } C0 [] [] ts [] ret HWfConfig
    (iswf_Forall_nil _) rfl HEq' Hmod rfl Hstore Hnotbr Hnotret
  rcases IH' with (Hconst | Htrap) | Hprog
  · left
    refine ⟨Hconst, ?_⟩
    obtain ⟨vs, rfl⟩ := const_es_exists _ Hconst
    obtain ⟨v_ts, HSub, HVals⟩ := ais_vals_typing_inversion _ _ _ [] ts Hadmin
    have HSub' := (instrtype_sub_iff_resulttype_sub v_ts ts []).mpr HSub
    cases HSub' with
    | mk_Resulttype_sub _ _ HSizets _ =>
      simp only [proj_list_0, List.length_map]
      rw [← HVals.1, HSizets]
  · right; left; exact Htrap
  · right; right; exact Hprog
```

Still-`sorry` earlier TypeProgress lemmas used: `const_es_exists` (:110), `frame_t_context_local_types` (:392),
`frame_t_context_label_empty` (:398). Other lemmas used are proved: `ais_vals_typing_inversion`
(TypingLemmas), `instrtype_sub_iff_resulttype_sub` (Subtyping), `iswf_Forall_nil` (wasm2.0).

Notes: follows the Rocq bullet (invert `Frame_ok`; build `HEq' : upd_return (C_tlst ++ C0) ret =
upd_local_label_return C0 (map typeof locals) [] ret`; apply IH with `vcs = []`, `ts1 = []`, `lab = []`;
const case via `const_es_exists` + `ais_vals_typing_inversion` + `instrtype_sub_iff_resulttype_sub` and the
`Resulttype_sub` length premise; trap/step cases direct). Lean deviation: Rocq proves the LOCALS part of
`HEq'` by inverting `Moduleinst_ok` (`C0.LOCALS = []`) and a `Forall2` induction (`t_lst = map typeof
val_lst`); here both are replaced by `frame_t_context_local_types` applied to the `Frame_ok` hypothesis (taken
before `cases`), and the field-by-field equality is closed by `congr 1` (it discharges the LOCALS/LABELS
fields with the `Hloc`/`Hlab` hypotheses and the others by `rfl` since `[] ++ l` reduces to `l`).
Pitfall hit: `Frame_ok`'s store index is auto-promoted to a parameter, so `rename_i` takes 11 names, not 12.

## Checks

- Ordering rule: every TypeProgress declaration used precedes its target (lines 65, 84, 97, 110, 392, 398,
  2426 `t_progress_e_P0`, 2446 `t_progress_e_P1` < 2604 / 2616). No later TypeProgress lemma used.
- Statement guards: `example : type_of% @<name>_proof = type_of% @<name> := rfl` for both targets
  compile, so both headers are identical to the real ones.
- No `sorry`/`admit`/`native_decide`/new `axiom` in the proof text. No project axioms used directly; the
  `sorryAx` in `#print axioms` comes only from the still-`sorry` lemmas listed above (and `Step_is_wf`).
- `#print axioms` of used lemmas (scratch `Axioms.lean`):
  ```
  'TLC.wf_config_app' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'TLC.const_list_concat' depends on axioms: [propext, sorryAx]
  'TLC.v_to_e_const' depends on axioms: [propext, sorryAx]
  'Step_is_wf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'TLC.frame_t_context_local_types' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'TLC.frame_t_context_label_empty' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'TLC.const_es_exists' depends on axioms: [propext, sorryAx]
  'TLC.ais_vals_typing_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
  'TLC.instrtype_sub_iff_resulttype_sub' depends on axioms: [propext, Quot.sound]
  'iswf_Forall_nil' does not depend on any axioms
  ```

### Final Lean check

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/prove-C27/Work.lean`
gave exit 0; full output (no errors, no warnings):

```
'TLC.t_progress_e_Instrs_ok2_frame_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_e_mk_Expr_ok2_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Safety check at END

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C27`

```
safety check [prove-C27] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T141754.298536536Z-prove-C27-1527690.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

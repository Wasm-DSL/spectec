# prove-M01 log (bundle20 progress port: proof batch M01, 2 targets)

Brief: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/progress_prove_brief.md`
Task:  `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/task_prove-M01.md`
Scratch: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-M01/Work.lean`

Files written by this agent: this log only (in the repo); `Work.lean`, `Axioms.lean`, `hdr_*.txt` in the
scratch dir. No repo file edited (TypeProgress.lean untouched), no git state changes, no agents spawned.

## Safety check — START

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-M01`

```
safety check [prove-M01] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T121954.798257226Z-prove-M01-1446593.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Results

### 1. `Instr_ok_Instrs_ok` (TypeProgress.lean:2398; Rocq type_progress.v:5515-5521) — PROVED

Direct port of the Rocq proof (`apply instr_ok_context_wf in Hinstr`, then `apply Instrs_ok__instr`).

```lean
  intro hinstr
  obtain ⟨hwfC, hwfi⟩ := instr_ok_context_wf C be _ hinstr
  exact Instrs_ok.instr C be ts1 ts2 hinstr hwfC hwfi
```

- Still-`sorry` earlier lemmas used: none. (`instr_ok_context_wf` is proved, TypingLemmas.lean:200.)
- `#print axioms Instr_ok_Instrs_ok_proof`: `[propext, Classical.choice, Quot.sound]` (no sorryAx).

### 2. `t_progress` (TypeProgress.lean:2653; Rocq type_progress.v:6064-6094) — PROVED

Port of the Rocq proof: invert `Config_ok` / `State_ok` / the expression typing (Lean's `Config_ok`
has `Expr_ok2` directly where Rocq's `Hthread` is), then apply `t_progress_e` with
`lab := []`, `ret := none`, `vcs := []`, `ts1 := []`, `ts2 := t_lst`,
`C' := upd_local_label_return C [] [] none` exactly as Rocq. The four Rocq side goals:
- context equation: from `frame_t_context_local_types` / `_label_empty` / `_return_empty`
  (destruct the 10-field context, `subst`, `rfl`);
- `Moduleinst_ok s f.MODULE C'`: invert `Frame_ok` (Rocq `inversion HFrame`), the module context
  `C0` has `LOCALS = []`, `LABELS = []`, `RETURN = none` (Rocq `inversion Hmod`; here each by
  `cases hminst; rfl`), after which the goal is definitionally `hminst`;
- `not_lf_br` / `not_lf_return`: `s_typing_not_lf_br'` / `s_typing_not_lf_return` as in Rocq.

```lean
  intro hconfig
  cases hconfig with
  | mk_Config_ok _ _ _ t_lst C hstate hexpr _ hwfconfig _ =>
  cases hstate with
  | mk_State_ok _ _ _ hstore hframe _ _ =>
  cases hexpr with
  | mk_Expr_ok2 _ _ _ hadmin _ _ _ =>
  have hloc := frame_t_context_local_types s f C hframe
  have hlab := frame_t_context_label_empty s f C hframe
  have hret := frame_t_context_return_empty s f C hframe
  have hC : C = upd_local_label_return (upd_local_label_return C [] [] none)
      (List.map typeof f.LOCALS) [] none := by
    rcases C with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    simp only at hloc hlab hret
    subst hloc hlab hret
    rfl
  have hmod : Moduleinst_ok s f.MODULE (upd_local_label_return C [] [] none) := by
    cases hframe with
    | mk_Frame_ok val_lst v_minst t_lst0 C0 hminst _ _ _ _ _ _ =>
      have hl : C0.LOCALS = [] := by cases hminst; rfl
      have hb : C0.LABELS = [] := by cases hminst; rfl
      have hr : C0.RETURN = none := by cases hminst; rfl
      rcases C0 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
      simp only at hl hb hr
      subst hl hb hr
      exact hminst
  exact t_progress_e s C (upd_local_label_return C [] [] none) f [] es (mkFunctype [] t_lst) [] t_lst [] none
    hwfconfig hadmin (fun x hx => by cases hx) rfl hC hmod rfl hstore
    (s_typing_not_lf_br' s f C es [] t_lst hframe hadmin)
    (s_typing_not_lf_return s f C es [] t_lst hframe hadmin)
```

- Still-`sorry` earlier lemmas used (all BEFORE `t_progress` in TypeProgress.lean):
  `frame_t_context_local_types` (:392), `frame_t_context_label_empty` (:398),
  `frame_t_context_return_empty` (:432), `s_typing_not_lf_br'` (:490),
  `s_typing_not_lf_return` (:506), `t_progress_e` (:2629).
- No TypePreservation.lean lemma is used (an early draft used `inst_t_context_local_empty` /
  `inst_t_context_labels_empty`; replaced by inline `cases hminst; rfl` so the proof only needs
  wasm2.0 + earlier TypeProgress declarations).
- Pitfall hit once: `Expr_ok2`'s store is a promoted parameter of the mutual block, so
  `mk_Expr_ok2` takes 7 binder slots, not 8 (first attempt: "Too many variable names provided").

No new axioms, no `sorry`/`admit`/`native_decide` in either proof.

## Lean check (final)

Statement guards (in Work.lean, both compiled):
```
example : type_of% @Instr_ok_Instrs_ok_proof = type_of% @Instr_ok_Instrs_ok := rfl
example : type_of% @t_progress_proof = type_of% @t_progress := rfl
```
Also a textual `diff` of each copied header against TypeProgress.lean: identical (HDR1_SAME, HDR2_SAME).
TypeProgress.olean (2026-10-05 20:18:19) is newer than TypeProgress.lean (20:18:16).

Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/Work.lean`

Output: (empty — no errors, no warnings), `EXIT=0`.

## Safety check — END

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-M01`

```
safety check [prove-M01] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T122331.411649851Z-prove-M01-1449209.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

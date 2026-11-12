# prove-C17 log (bundle20 progress port, proof batch C17)

Agent label: `prove-C17`. Scope: fill `t_progress_be_memory_copy` (TypeProgress.lean:2151), porting the
`Instr_ok__memory_copy` bullet of Rocq `t_progress_be` (type_progress.v:4820-4917).
Only files written: this log + scratch dir
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C17/`
(`Work.lean`, `Axioms.lean`, `proof_body.txt`). No repo file edited (TypeProgress.lean untouched), no git,
no agents spawned, one Lean process at a time (`lake env lean` only).

## Safety check — START

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C17`

```
safety check [prove-C17] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134801.327662004Z-prove-C17-1510223.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Target 1/1: `t_progress_be_memory_copy` — status: PROVED

### Port notes
- Follows the Rocq bullet step by step: intro the 7 `Instr_ok.memory_copy` premises, `unfold t_progress_be_P`, intro
  Rocq's motive binders (`s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret`),
  `right`; `Htf` gives `ts1 = [I32; I32; I32]`; destruct `vcs` into exactly three values (Rocq `invert_typeof_vcs` +
  `inv_Forall`); `invert_typeof_I32` three times (as Rocq) to get `n1 n2 n3`; rewrite the config to
  `[CONST I32 n1, CONST I32 n2, CONST I32 n3, MEMORY_COPY]`.
- Same 4-way case split as Rocq: (1) `n2+n3 > |mem| ∨ n1+n3 > |mem|` → `Step_read.memory_copy_trap` (to `[TRAP]`);
  otherwise both bounds hold (`omega`, Rocq's `orb_false_elim`/`N.ltb_ge`); (2) `n3 = 0` → `memory_copy_zero` (to `[]`);
  (3) `n1 ≤ n2` → `memory_copy_le`; (4) else → `memory_copy_gt`.
- Simplification vs Rocq: the Lean `Step_read` rules have no negated `Step_read_before_*` premises, and the goal is
  `∃ s' f' es'`, so `es'` is left as `_` and unified with the rule's own right-hand side. This avoids Rocq's
  `n3 = (N.succ n3 - 1)` rewriting, `add_sub_parens`, and the `Z` side goals entirely (Rocq's `N.peano_ind` on
  `n3` becomes a plain `by_cases n3 = 0`).
- Rule argument order checked against wasm2.0.lean:14651-14675: rules take `(z j i v_n)` with config
  `[CONST I32 j, CONST I32 i, CONST I32 (mk_uN v_n), MEMORY_COPY]`, so `j = n1`, `i = n2` (matching Rocq).
- `wf_uN 32 (uN.mk_uN 0)` premise of the trap rule: `wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩`.

### Dependencies
- Earlier TypeProgress lemmas used: `invert_typeof_I32` (TypeProgress.lean:209 < 2151; still `sorry`),
  `t_progress_be_P` (def, :1486). From imports: `mkFunctype` (Subtyping), wasm2.0 constructors/defs.
- Machine check (`Axioms.lean`, transitive walk over all 1825 reachable constants listing those whose own
  type/value mentions `sorryAx`): `reachable=1825; decls directly using sorryAx: [TLC.invert_typeof_I32]`.
- `#print axioms`: `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` only via `invert_typeof_I32`;
  no project (HelperLemmas) axioms used. No `sorry`/`admit`/`native_decide`/new axioms in the proof.

### Proof body (tactic block after `:= by`, exactly as compiled)

```lean
  intro C mt Hlen Hlookup HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  subst Htf1
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vs⟩⟩⟩⟩ <;>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
      List.nil_eq, and_true] at Hts
  obtain ⟨Ht1, Ht2, Ht3⟩ := Hts
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 (HWfVals v2 (by simp))
  obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 (HWfVals v3 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [Heqv1, Heqv2, Heqv3]
  show ∃ s' f' es', Step (config.mk_config (state.mk_state s f)
    [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)),
     admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)),
     admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n3)),
     admininstr.MEMORY_COPY]) (config.mk_config (state.mk_state s' f') es')
  by_cases Hs : n2 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length ∨
      n1 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
  · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
      (Step_read.memory_copy_trap _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
        (by simpa [proj_num__0, proj_uN_0] using Hs)
        (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
  · have HB : n2 + n3 ≤ (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length ∧
        n1 + n3 ≤ (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length := by
      omega
    by_cases H0 : n3 = 0
    · exact ⟨s, f, [], Step.read _ _ _
        (Step_read.memory_copy_zero _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using HB) H0)⟩
    · by_cases Hle : n1 ≤ n2
      · exact ⟨s, f, _, Step.read _ _ _
          (Step_read.memory_copy_le _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0]) H0
            (by simpa [proj_num__0, proj_uN_0] using HB)
            (by simpa [proj_num__0, proj_uN_0] using Hle))⟩
      · exact ⟨s, f, _, Step.read _ _ _
          (Step_read.memory_copy_gt _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
            (by simp only [proj_num__0, proj_uN_0, Option.get!_some]; omega) H0
            (by simpa [proj_num__0, proj_uN_0] using HB))⟩
```

### Lean check
Scratch file `Work.lean` = `import TypeProgress` / `namespace TLC` / theorem `t_progress_be_memory_copy_proof` with
the header copied verbatim from TypeProgress.lean:2151-2156 / guard
`example : type_of% @t_progress_be_memory_copy_proof = type_of% @t_progress_be_memory_copy := rfl` / `end TLC`.

Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/Work.lean`

Iteration 1: one error (`typeof v3 = valtype.I32 ∧ True` — the empty-tail conjunct; fixed by adding `and_true`
to the `simp only` set and dropping the unused `false_and`).
Iteration 2 (final) output:
```
(no output — no errors, no warnings)
EXIT=0
```
The `rfl` guard passed, so the statement is identical to the real one and the block drops in unchanged.

## Safety check — END

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C17`

```
safety check [prove-C17] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T135149.240021715Z-prove-C17-1512880.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

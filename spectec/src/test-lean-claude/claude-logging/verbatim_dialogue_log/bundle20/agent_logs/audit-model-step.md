# audit-model-step — bundle20 preservation audit, generated-model part 2 (instruction typing + reduction)

## Task

Compare the backend-generated Lean model `spectec/src/test-lean-claude/wasm2.0.lean` against
the Rocq backend's generated model `spectec/test-rocq/theories/wasm.v` for: (1) admin typing
`Instr_ok2`/`Instrs_ok2`/`Expr_ok2` (every constructor and premise); (2) validation
`Instr_ok`/`Instrs_ok`/`Expr_ok` (constructor counts/names fully, full premises for list
relations, context indexing, block types, branches, calls, memory/table instrs; spot-check
the rest); (3) reduction `Step_pure`/`Step_read`/`Step` (counts/names fully; full premises for
store/memory-touching rules and congruence rules; spot-check the rest); (4) backend-sensitive
helpers (`with_mem` vs `fun_with_mem`/`list_slice_update`, `splice`, `rat_to_nat`, `l[i]!` vs
`lookup_total`, `Option.get!`/`≠ none`, and every `opaque` used by these rules); (5) the
hand-edited `Step_read_is_wf`/`Step_is_wf` statements vs Rocq's. Read-only; no Lean run.

## Safety check — START (verbatim)

```
safety check [audit-model-step] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress log (written incrementally)

- Read brief `scratchpad/briefs/audit_brief.md` (lines 1-147) and task file
  `scratchpad/briefs/task_model_instr_step.md` (lines 1-31).

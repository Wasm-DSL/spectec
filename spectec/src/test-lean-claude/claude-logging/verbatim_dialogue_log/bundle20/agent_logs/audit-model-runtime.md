# audit-model-runtime — bundle20 preservation audit, generated-model part 1 (runtime/configuration typing)

## Task

Subagent `audit-model-runtime` of the bundle20 preservation audit. Read-only audit comparing the
generated Lean definitions (`spectec/src/test-lean-claude/wasm2.0.lean`) that the meaning of
`TLC.t_preservation : Step c1 c2 -> Config_ok c1 ts -> Config_ok c2 ts` depends on, against the
generated Rocq (`spectec/test-rocq/theories/wasm.v`): `Forall`/`Forall₂`/`Forall₃`, `Config_ok`,
`State_ok`, `Frame_ok`, `Store_ok`, `Moduleinst_ok`, the `*inst_ok` relations, `Externaddr_ok`,
`Val_ok`, `Ref_ok`, `Extend_store` + all `Extend_*`, the `wf_*` premises, the project's `Vals_ok`,
and the top-level statement vs Rocq `t_preservation` and Isabelle `preservation`. Special attention:
every use of the zip-based `Forall₂`/`Forall₃` and whether an explicit or structural length
equality accompanies it. No Lean was run; files were only read (grep/sed/Read).

## Safety check — START

```
safety check [audit-model-runtime] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052753Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress notes (written incrementally)

- Read brief `audit_brief.md` (all 146 lines) and task `task_model_runtime.md` (all 38 lines).

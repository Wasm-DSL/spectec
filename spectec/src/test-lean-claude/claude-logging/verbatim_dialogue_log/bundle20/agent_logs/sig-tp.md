# sig-tp — signature audit: TypePreservation.lean vs type_preservation.v (bundle20)

## Task

Subagent "sig-tp" of the bundle20 preservation audit. Enumerate every (non-commented-out)
declaration in Rocq `spectec/test-rocq/theories/type_preservation.v`, match each to its Lean
counterpart (TypePreservation.lean, the other five hand-written Lean files, or wasm2.0.lean),
compare statements (binders, premises, conclusion), list Rocq-only and Lean-only declarations,
spot-check ~15 doc-comment citations, and list trust-expanding constructs (`sorry`, `axiom`,
`native_decide`, `admit`, `implemented_by`, `unsafe`) in TypePreservation.lean. Read-only; no Lean.

## Safety check (START)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" sig-tp
safety check [sig-tp] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress log

- Read shared brief (audit_brief.md, 147 lines) and task file (task_sig_tp.md, 31 lines).

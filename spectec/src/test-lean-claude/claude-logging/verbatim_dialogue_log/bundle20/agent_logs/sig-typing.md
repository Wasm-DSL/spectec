# sig-typing — signature audit of TypingLemmas.lean vs typing_lemmas.v (bundle20)

## Task

Subagent "sig-typing" of the bundle20 preservation audit. Enumerate every (non-commented)
declaration in the Rocq `typing_lemmas.v`, match each to its Lean counterpart (mostly in
`TypingLemmas.lean`), compare statements (binders, premises, conclusion), list Rocq
declarations without Lean counterpart and Lean declarations without Rocq counterpart (checking
doc comments), spot-check ~15 doc-comment citations, and note any trust-expanding constructs
(`sorry`, `axiom`, `native_decide`, `admit`, `implemented_by`, `unsafe`) in `TypingLemmas.lean`.
Read-only; Lean not run. Only this log file is written inside the repo.

## Safety check (START)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" sig-typing
safety check [sig-typing] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress notes (incremental)

- Read brief and task file.

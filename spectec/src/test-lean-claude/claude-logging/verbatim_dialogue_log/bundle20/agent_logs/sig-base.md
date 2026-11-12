# sig-base — signature audit: Subtyping.lean + HelperLemmas.lean vs subtyping.v, helper_lemmas.v, axioms.v

(bundle20 preservation audit, subagent label `sig-base`; written incrementally)

## Task

Enumerate every (non-commented-out) declaration in the Rocq files `subtyping.v`,
`helper_lemmas.v` and `axioms.v` (in `/home/zhengyew/spectec/spectec/test-rocq/theories/`),
match each to its Lean counterpart (`Subtyping.lean`, `HelperLemmas.lean`, other hand-written
Lean files, or `wasm2.0.lean`), compare statements (binders, premises, conclusion), list
Rocq declarations without a Lean counterpart and Lean declarations without a Rocq counterpart
(checking the Lean-only doc labels), spot-check ~15 doc-comment Rocq citations, and note every
`sorry`/`axiom`/`native_decide`/`admit`/`implemented_by`/`unsafe` in the two Lean files
(comparing each Lean axiom to its Rocq `Axiom`). Read-only; Lean not run.

## Safety check — START (verbatim)

```
safety check [sig-base] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress

- (in progress) reading files ...

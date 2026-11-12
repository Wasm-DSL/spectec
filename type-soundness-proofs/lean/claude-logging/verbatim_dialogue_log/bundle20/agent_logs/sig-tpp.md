# sig-tpp — signature audit: TypePreservationPure.lean vs type_preservation_pure.v (bundle20)

## Task

Subagent "sig-tpp" of the bundle20 preservation audit. Read-only signature audit of the
hand-written Lean file `spectec/src/test-lean-claude/TypePreservationPure.lean` against the Rocq
original `spectec/test-rocq/theories/type_preservation_pure.v`: enumerate every (non-commented)
Rocq declaration, match it to its Lean counterpart, compare statements (binders, premises,
conclusion), list Rocq declarations with no Lean counterpart and Lean declarations with no Rocq
counterpart (checking Lean-only documentation), spot-check ~15 doc-comment citations, and note
every trust-expanding construct (`sorry`, `axiom`, `native_decide`, `admit`, `implemented_by`,
`unsafe`) in TypePreservationPure.lean. No Lean was run; files were only read.

## Safety check (START)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" sig-tpp
safety check [sig-tpp] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress (incremental)

- Read shared brief + task file. Started safety check: VERIFIED.
- Read `spectec/test-rocq/theories/type_preservation_pure.v` in full (l.1-1583). Nested-comment-aware
  scan (python, scratch dir): 76 `Lemma`/`Theorem` declarations, none commented out; plus
  `Opaque instrtype_sub` (l.14) and `Ltac resolve_wfness` (l.16-31), which are not declarations
  in the task's sense.
- Read `spectec/src/test-lean-claude/TypePreservationPure.lean` in full (l.1-1977): 79 `theorem`s
  (76 Rocq ports + 3 Lean-only helpers). No `def`/`axiom`/`instance`/`opaque`/attributes/options.
- Read the generated support definitions the statements depend on: `wasm2.0.lean` l.40-52 (`N`,`n`
  = Nat), l.125-135 (`list`,`proj_list_0`), l.487-517 (`idx`,`labelidx`,`localidx`), l.618
  (`resulttype`), l.775 (`dim`), l.11642-11728 (`admininstr_instr/_ref/_val`), l.13726-13990
  (`Step_pure`), l.14076-14310 (`Step_pure_is_wf`); Rocq `wasm.v` l.1-40 (`lookup_total`,`the`),
  l.295-312 (notations `|x|`, `!(x)`, `[| |]`), l.342-348 (`res_N`,`n`), l.424-447 (`res_list`,
  `mk_list`,`proj_list_0`), l.833-863 (idx types), l.15524-15797 (`Step_pure`, `Step_pure_is_wf`);
  `subtyping.v` l.1-60 vs `Subtyping.lean` l.30-60 (`:->`/`mkFunctype`, `Resulttype_subtype`/
  `ResulttypeSub`, `instrtype_sub`: identical definitions).
- Citation check (python over every doc comment): 47 correct, 27 stale, 2 with no line, 3 Lean-only.
  All 27 stale citations equal the declaration lines of `git show 5b03ae067:.../type_preservation_pure.v`
  ("Repaired preservation pure (except return frame)"), i.e. they were written against that older
  revision and never refreshed after the file was reflowed (current lines are 7-28 lower).

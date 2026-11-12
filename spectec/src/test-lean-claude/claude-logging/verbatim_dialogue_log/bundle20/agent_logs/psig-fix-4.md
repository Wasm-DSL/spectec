# psig-fix-4 log (bundle20 progress port: fix signature-audit problems in chunk 4)

## Task
Fix the auditor's problems in chunk 4 (type_progress.v:1761-2212, 32 declarations). The audit lists
one problem: `Forall2_size_eq` (severity "suspicious"). The suggested fix: replace the tautological
theorem with a NOT PORTED comment, following the HelperLemmas.lean:293 `Forall2_seq_size` precedent.
Do not edit any repo file except this log. Scratch dir:
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-fix-4/`.

## Safety check (START), verbatim
```
safety check [psig-fix-4] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T120855.260689566Z-psig-fix-4-1443382.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## What I read
- Briefs: `briefs/progress_sig_brief.md`, `briefs/task_psig_4.md`.
- Rocq: `spectec/test-rocq/theories/type_progress.v` 1860-1885 (`Forall_exists_Forall2`,
  `Forall2_size_eq`), 1975-1990 (Ltac `vunop_case`, use at 1982), 3935-3945 (use at 3941).
- Lean precedent: `HelperLemmas.lean` 280-305 (`Forall2_seq_size` NOT PORTED comment at 293).
- Earlier logs: `psig-4.md` (the translator already said "main thread may prefer NOT PORTED"),
  `psig-audit-4.md` row 10.

## Audit item 1: `Forall2_size_eq` (type_progress.v:1874), severity "suspicious". ACCEPTED
- Rocq: `forall A B R la lb, List.Forall2 R la lb -> (|la|) = (|lb|)`. The proof gets the length
  from the inductive `Forall2`.
- Lean's generated `Forall₂` is zip-based, so the literal statement is false in Lean
  (`la = []`, `lb = [b]`). The translator's `hlen` version
  `Forall₂ R la lb → la.length = lb.length → la.length = lb.length` returns its own premise.
- Rocq uses: 1982 (Ltac `vunop_case`, `apply/eqP; exact: (Forall2_size_eq _ _ _ _ _ H2)`, where `H2`
  comes from `Forall_iabs_total`) and 3941 (`Nnat.Nat2N.inj; apply: (Forall2_size_eq ... H2)`, where
  `H2` comes from `Forall_exists_Forall2`). Both only extract the length. In the Lean chunk both
  sources already give `... ∧ vs.length = ls.length` / `la.length = l.length` as a conjunct.
- Project precedent: HelperLemmas.lean:293 marks the identical `Forall2_seq_size`
  (helper_lemmas.v:159) NOT PORTED for this exact reason.
- Fix: replaced the theorem with a NOT PORTED comment under the kept `-- @@ Forall2_size_eq` marker.
  Coverage entry changed to NOT PORTED.
- Related doc-only tweak: the `Forall_exists_Forall2` doc comment said "Downstream Rocq uses
  (`Forall2_size_eq` at 1982/3941) need exactly this length fact". It now reads "Downstream Rocq uses
  of `Forall2_size_eq` (1982/3941; NOT PORTED in Lean) need exactly this length fact, which Lean
  callers take from this conjunct." The signature is unchanged. No other declaration changed.

## Rejected audit items
- None (the audit listed one problem, and it was accepted).

## Lean check
`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/psig-fix-4/Chunk.lean`
gave exit=0. The output has 31 lines, all `declaration uses \`sorry\`` warnings (31 theorems). There are
no errors and no other warnings. 32 `-- @@` markers kept (one per Rocq declaration, in Rocq order).
Last lines:
```
.../psig-fix-4/Chunk.lean:245:8: warning: declaration uses `sorry`
.../psig-fix-4/Chunk.lean:252:8: warning: declaration uses `sorry`
.../psig-fix-4/Chunk.lean:262:8: warning: declaration uses `sorry`
```

## Safety check (END), verbatim
```
safety check [psig-fix-4] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T121103.450803035Z-psig-fix-4-1444066.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```
Files written: this log (inside the target dir), plus `Chunk.lean` and `check.out` in my scratch dir
(outside the repo). No repo file was edited, and TypeProgress.lean was not touched.

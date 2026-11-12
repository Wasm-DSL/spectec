# audit-proofmap — bundle20 preservation audit subagent log

## Task (one paragraph)

Produce a structured, human-followable map of the Lean preservation proof in
`/home/zhengyew/spectec/spectec/src/test-lean-claude/`: (1) a top-down tree from
`TLC.t_preservation` through its main lemmas (file:line, plain-words statement, Rocq counterpart
file:line, key dependencies, proof technique); (2) the custom infrastructure/design patterns a
reviewer must recognise; (3) a ranked top-10 list of things to understand/check to trust the proof plus a
suggested reading order; (4) size statistics (decls/lines per file, Rocq ports vs Lean-only helpers).
READ-ONLY w.r.t. the repo (only this log file is written); no Lean is run. Findings only for real
problems noticed along the way (e.g. doc comments misstating a lemma).

## Safety check — START (verbatim)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" audit-proofmap
safety check [audit-proofmap] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress (written incrementally)

- [start] Read brief `scratchpad/briefs/audit_brief.md` (147 lines, all) and task
  `scratchpad/briefs/task_proofmap.md` (31 lines, all). Ran start safety check (above).
- [step 1] Sizes: `wc -l` of the 7 Lean files + lakefile; import DAG read from each file's
  `import` lines. Declaration index via `grep -nE '^\s*(private |...)*(theorem|lemma|def|...)'`.
- [step 2] Read `TypePreservation.lean` 2400-2751 (`t_preservation_type_aux` tail,
  `t_preservation_type`, `t_preservation`) and Rocq `type_preservation.v` 3405-3480.
- [step 3] Wrote a read-only citation checker
  (`scratchpad/agents/audit-proofmap/check_cites.py`, output `cites_report.txt` in the same dir):
  for every `<file>.v:<N> \`name\`` citation in the 6 hand-written Lean files, checks whether
  `name` is declared within +-2 lines of N in the current Rocq checkout.
  Result: **ok=92, wrong line=166, not declared anywhere in current Rocq=20** (the 20 are
  HelperLemmas lemmas removed upstream after `0c9a5417a`, documented in NOTES.md 2026-09-23).
  The wrong-line ones match OLD checkouts: e.g. `typing_lemmas.v:1184 ais_composition_typing`
  is the `5b03ae067`/`dac300994` (2026-07-01) position (now 1143); `type_preservation.v:2668
  t_preservation` is the `a094a13af` (2026-05-04) position (now 3412). Per-file wrong counts:
  TypingLemmas 60, Subtyping 41, HelperLemmas 27, TypePreservationPure 27, TypePreservation 7,
  ExtensionLemmas 4. Not disclosed in the Lean headers (Subtyping/HelperLemmas headers claim
  "every declaration cites its Rocq source line number").
- [step 4] Read TypePreservation.lean 40-2416 in full (all main lemmas, store plumbing,
  per-rule `*_store_ok`, `pt_*`/`ais_*`/`inv_*` helpers, `t_read_preservation` all 47 cases),
  compared statements of `t_preservation`, `t_preservation_type`, `t_read_preservation`,
  `store_extension_reduce`, `reduce_inst_unchanged`, `t_preservation_vs_type(')`,
  `step_moduleinst` against Rocq `type_preservation.v` (100-170, 437-448, 1504-1512, 1661-1675,
  3120-3152, 3412-3420): all match (only the documented `Vals_ok` deviation in
  `t_read_preservation`). Constructor counts verified: Step 23, Step_read 47 (= 47 cases in
  `t_read_preservation`), Step_pure 63.
- [step 5] Read wasm2.0.lean 1-30 (Forall/Forall₂/splice/rat_to_nat), 14699-14740 (Step),
  15991-16064 (Store_ok, Step_read_is_wf sorry, Step_is_wf), located the 5 hand-written helper
  blocks (302, 3042, 5878, 12045, 13998). Rocq wasm.v: Step 16355 (same wf_config premises in
  congruence rules), Step_read_is_wf 17354 (`Admitted` at 17698), Step_is_wf 17702 (`Qed` 18147).
- [step 6] Read TypePreservationPure.lean 1500-1976 (`vec_preserves_*`, SIMD lemmas,
  `t_pure_preservation`), decl/doc index of the whole file; Rocq `t_pure_preservation` at
  type_preservation_pure.v:1526 (statement matches).
- [step 7] Read ExtensionLemmas.lean 1-225, 478-547, 1720-1919 (`Extend_store_moduleinst`,
  `Extend_store_ais` via `Instrs_ok2.rec`), decl/doc index of the whole file; Rocq
  `Extend_store_ais` at extension_lemmas.v:2580 uses `Scheme ais_ok_ind'` (2574).
- [step 8] Read TypingLemmas.lean 1-120, 268-475 (`ai_principal_typing`), 672-821, 1000-1090,
  1140-1459 (`_gen` scaffolds, `ais_seq_typing_inversion`, `ais_composition_typing`,
  `ais_single_typing_inversion`), Subtyping.lean 1-160, HelperLemmas.lean 1-180, 240-305,
  672-799 (axioms, Forall₂ bridges). Rocq `ai_principal_typing` is at typing_lemmas.v:377
  (current), 427 at `5b03ae067`.

# bundle21 subagent logs

Every subagent got the user's safety order verbatim, plus this turn's stricter rule: write nothing
anywhere inside the repository (writes under `spectec/src/test-lean-claude` had been denied by the
auto-mode permission classifier). Each ran the scratch-output safety check
(`scratchpad/safety/verify.sh`, same `git status` comparison as
`safety-checks/verify_against_baseline.sh` against the bundle21 baseline
`safety-checks/check-20261015T044132Z.txt`) at start and end, and wrote only its own log plus
scratch files in the session scratchpad. The logs and check outputs were copied here afterwards.

| Workflow (run id) | Purpose | Agents | Outcome | Logs |
|---|---|---|---|---|
| `bundle21-log-digest` (`wf_bcf5b848-c82`) | read the rest of the dialogue log exhaustively (bundle20 agent logs + JSON results, older bundles' documents, living docs) and digest it | 9 (Sonnet), 3 at a time | all 9 done (3 batches of 3), 0 errors; ≈3.36M subagent tokens, 579 tool uses, ≈3 h 26 min wall clock | `digest-*.md` |
| `bundle21-prove-step-read-is-wf` (`wf_13021607-9e1`) | port Rocq's now-`Qed` `Step_read_is_wf` (47 `Step_read` rules) | 1 (Opus) | **proved**, no `sorry` of its own (uses only `extend___is_wf`, `inv_lanes__is_wf`, `lanes__is_wf`, all Rocq-`Admitted`); statement guard + splice test into a copy of `wasm2.0.lean` passed; ~22 min, ≈303k subagent tokens | `prove-stepread.md` |

`safety_checks/` holds every check output produced this turn (main thread and agents).

Final note (after the digest workflow completed, 2026-10-15 ~16:15 local): two of the last readers
(`digest-old2`, `digest-living`) observed, at 16:05:35, the four bundle21 Lean files appearing in
the repo (the user applied `bundle21_lean_changes.patch`) followed by a full rebuild; their end-of-run
safety checks therefore list those files as modified inside `spectec/src/test-lean-claude`, and
still verify zero changes outside it.

Written for: you. The full report is `bundle21/user_requested_documents/resync_6582b3a_and_sorry_report.md`.

## The blockers are solved upstream; the Lean changes are ready but not applied yet

**1. Blocking issues: solved.**
- The two stuck vector instructions are now invalid. `SHAPE` needs `M > 1`; `TRUNC_SAT` needs an
  `Inn` destination.
- The `Step_read_is_wf` 2^32 corner case is gone. The fill/copy/init rules now use wrapping
  `iadd_`.
- Rocq's `Step_read_is_wf` and `t_progress_be` are both `Qed` now.
- Still open upstream, but none of them blocks a `sorry`: (B) `Moduleinst_ok`'s `> 0` premise,
  (C) mutable-only globals, and the `vstore_lane` typo. The bundle20 non-vacuity witness still
  checks against the new model and re-confirms B and C.

**2. `sorry`s, as checked in a scratch copy of the project** (full build clean, 3006 jobs):
- **`Step_read_is_wf` is proved.** An agent ported Rocq's new proof covering all 47 rules. It adds
  no `sorry` of its own.
- **`TypeProgress.lean` has no `sorry`.** The two stuck subcases are now impossible, and the file
  mirrors Rocq's deletions and re-signings exactly. Your readability rewrites are untouched.
- **What cannot be done: 62 `sorry`s remain in the generated `wasm2.0.lean`.** Each says an
  uninterpreted builtin (`iand_`, `fadd_`, `lanes_`, …) returns a well-formed value. Those
  functions are `opaque` in Lean (`Axiom`s in Rocq), so nothing about their outputs can be
  proved. Rocq leaves exactly the same 62 `Admitted`. They go away only if the generator gives
  the builtins real definitions, as you did for `rat_to_nat`.
- **The 16 you marked for deletion are left as you asked.**

**3. What the theorems rest on now:**
- `t_preservation`: 32 of those opaque-builtin facts, and no project axiom.
- `t_progress`: 56 such facts, plus 15 axioms that mirror Rocq's.

**4. Needs you: apply the patch.**
- Even after your clarification, the permission classifier refused to overwrite the repo's `.lean`
  files. Your regenerated `wasm2.0.lean` is uncommitted, so overwriting it can't be undone by git.
  New files are fine, so the bundle21 logs, report and patch are in the repo.
- To land the changes, run from the repo root:
  ```sh
  git apply spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/user_requested_documents/bundle21_lean_changes.patch
  cd spectec/src/test-lean-claude && lake build
  ```
  `git apply -R` undoes it exactly. Alternatively, add a permission rule for edits there and tell
  me to go ahead; I'll then apply it, rebuild in the repo and update NOTES/SUMMARY/is_wf.
- The patch was self-tested: applied to the repo's current files, it reproduces the checked files
  byte for byte.

**Also checked:**
- Your regenerated `wasm2.0.lean` is byte-identical to the current generator's output.
- The bundle19 hand-proofs re-applied cleanly. Only `vshiftop__is_wf` needed a fix, for the
  modulo shift.
- A new `wasm2.0_hand_edits.patch` and README are in bundle21, for the next regeneration.
- Every safety check confirmed nothing outside `spectec/src/test-lean-claude` changed.
- An untracked `.lake/build/lib/lean/wasm2.0.trace.nobuild` appeared inside it at 12:52. It's a
  harmless Lake stub, probably from the IDE's Lean server; delete it whenever you like.
- The last 3 of 9 log-digest readers are still running. I'll file their logs when they finish.

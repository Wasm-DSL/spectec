# Response 31 (verbatim)

---

Written for: you. The full report is also meant for later sessions.

The rest of the proof is repaired. All seven downstream modules compile against the current `wasm2.0.lean` with 0 errors and 0 `sorry`. I installed `HelperLemmas`, `ExtensionLemmas`, `TypePreservation` and `TypeProgress`; the other three modules needed no change, and `wasm2.0.lean` is untouched.

**Checks**, run on a fresh build of all nine modules from the repo sources:
- None of the 5,517 theorems in the eight project modules depends on `sorryAx`.
- No theorem reads an `Inhabited` default. This is the kernel replay with every `Inhabited` instance opaque, now run over all eight modules.
- No axioms were added:
  - `t_preservation` uses the three standard axioms plus 32 of the model's `*_is_wf` axioms.
  - `t_progress` uses the three standard axioms, 56 of the model's `*_is_wf` axioms and 15 existing project axioms from Rocq's `axioms.v`.
- The main theorems and all progress cases keep their statements.

**What broke, and the fix**
- 104 declarations broke. Functions such as `$table`, `$mem`, `$with_*`, `$blocktype`, the bit widths, `$default_` and `$fzero` are now relations. Names disappeared, relations were applied as functions, and constructor shapes changed. Progress must now prove the index bounds itself, from validation and module-instance typing.
- I added shared lemmas first:
  - **Function views:** `lsize`, `sizenn`, …, `fzero` and `default_`, with the old definitions and lemmas tying each to its relation. With these, 16 declarations compile unchanged.
  - **Lookup inversion lemmas** for the state lookups.
  - **Bound lemmas:** `Moduleinst_ok_*_addr` and `fun_*_typed`.
- Nine agents re-proved the remaining 86 declarations in scratch copies, with Lean running one process at a time, and I merged their work.
- Ten statements changed: `bt_inversion`, `wf_config_mem_bytes`, `mem_bytes_wf`, the three store lemmas, `unop_not_none`, `testop_not_none`, `zero_lane_wf` and `vstore_lane_progress`. The list is in §5 of the report.
- The default audit caught two proofs that read defaults: `t_read_preservation`'s `call` case and `mem_bytes_wf`. Both are fixed.

**Report:** `claude-logging/verbatim_dialogue_log/bundle31/user_requested_documents/downstream_repair_report.md`.
- It covers each of the 105 affected constructs: what broke and why, the original proof sketch and the current one, in Wasm 2.0 terms. The 47 new constructs are covered too.
- Each group's section was written by one agent and checked against the code by another, then checked again against the installed files.

**Worth knowing (nothing here blocks the proof)**
1. **Spec issue, upstream and pre-existing.** In `8-reduction.spectec:550-579`, the `store-*-val` rules have no in-bounds premise. Read as relations, an out-of-bounds store can either trap or succeed. Also `vstore_lane-oob` compares with `N` bits, where Wasm uses `N/8` bytes. The theorems still hold.
2. **Two ATTENTION verdicts from the safety checks, both caused by your editor.** Its git refresh touched the package `.git` lock files, with no content change. Its Lake wrote `spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild`, which I left in place for you to delete or keep. Both are documented under `claude-logging/safety-checks/*note*`, and every later check is OK.
3. **`lake build` will rebuild all modules,** about 70 s, because the repo's `.lake/build` is stale.

The exchange, agent results and evidence are logged in `claude-logging/verbatim_dialogue_log/bundle31/`.

If you'd like to read the report in a browser, I can publish it as a private page.

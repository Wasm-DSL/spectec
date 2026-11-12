# Prompt 29 (verbatim)

Context notes (not part of the user's message):
- Same session as bundles 23-28 (conversation `14eafe93-c912-45da-8e28-e9b09c1a6ef6`). Opus 5.5
  (`claude-opus-5-5`).
- The message arrived as an invocation of the `/workflow-authoring` skill, with the text below as its
  body. "Ultracode" is on (system reminder); the session is in auto mode.
- Date: 2026-11-03 local (00:21 +0800; 2026-11-02 16:21Z). Branch `lean-backend-proof`, HEAD
  `810776a7e`.
- State at the start (the user's own changes, not this session's):
  - `spectec/src/test-lean-claude/wasm2.0.lean` is byte-identical (md5 `83ce8797…`) to
    `spectec/test-lean/todaywasm2.0_shouldwork` (bundle27): `Sideconditions` both before and after
    `DefToRel`, `sideconditions_on_defs = true`, no `wfopt` hint on `$fzero`; 89 `sorry`s.
  - `spectec/src/test-lean-claude/wasm2.0_prevattempt.lean` (untracked) is byte-identical (md5
    `72748a07…`) to the regenerated model of bundle23 *before* any proofs (90 `sorry`s), i.e. the
    file that was in the repo during bundle23. The bundle23 half-finished attempt (85 of 90 proved)
    was never installed in the repo; it exists only in the session scratchpad
    (`merge1/wasm2.0.lean`, `work/final_wasm2.0.lean`) and its saved copy.
- Start-of-turn safety check: `safety-checks/check-20261102T162151.480714566Z-bundle29-start-225864.txt`.

---

I've pasted todaywasm2.0_shouldwork.lean into wasm2.0.lean in `spectec/src/test-lean-claude`, and your earlier halfway-attempted version in wasm2.0_prevattempt.lean.

For this turn, I want you to ONLY mutate `wasm2.0.lean`, and `spectec/src/test-lean-claude/claude-logging` as needed for logging purposes. I want you to:
- Prove all `sorry`s in `wasm2.0.lean`
    - You will probably need to make the same hand edits to the signatures of `Step_read_is_wf` and `Step_read`
- Create any helper lemmas you might require. These need not map to those in `OLD_wasm2.0.lean`.
    - For all helper lemmas, you must place them directly above the first top-level definition that calls them.
    - For all helper lemmas, you must clearly mark them with `/- HELPER LEMMA CREATED BY CLAUDE -/`.

After you're done, give me a report detailing:
- All additions to `wasm2.0.lean`, and its status, and sorry count
- A rough estimate of the impact to the rest of the proof in `spectec/src/test-lean-claude`.

Run a check afterwards to make sure you have ONLY mutated `wasm2.0.lean` and logging files. Remember your standing instructions.

Importantly, if you encounter any blocking issues, issues with the Lean model such as the previous issues with `fzero` or length premises, you should immediately try and confirm them, and if they are real, stop and let me know instead of continuing with other things.

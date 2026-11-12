# Follow-up reply (verbatim), sent after the log-digest workflow completed

Written for: you.

## Your patch application checks out, and bundle21 is now fully landed

- **The Lean changes are in.**
  - The four files you patched at 16:05 are byte-identical to the versions I built and checked.
  - Your rebuild recompiled all nine modules (16:08 to 16:10), so it succeeded.
  - So the bundle21 result now holds in the repo: `Step_read_is_wf` is proved, `TypeProgress.lean`
    has no `sorry`, and the only `sorry`s left are the 62 opaque-builtin facts and your 16 marked
    lemmas.
- **Logging is finished.**
  - `NOTES.md`, `SUMMARY.md` and `is_wf_theorems.md` describe the new state. I had held them back
    until the code was in.
  - All nine digest logs, the prover's log and every safety-check output are in
    `bundle21/agent_logs/`.
  - The report has a note that the patch was applied.
  - The final safety check verified that nothing outside `spectec/src/test-lean-claude` changed.
- **Housekeeping.** Your build removed the stray `wasm2.0.trace.nobuild`. Lake also deleted the
  committed `.lake/build/lib/lean/TypingLemmas.trace.nobuild`; it shows as `D` in `git status`, so
  restore it with `git checkout` if you want to keep it.
- **The digest of the rest of the log changed none of my conclusions.** It did surface three older
  open items, none of which blocks anything:
  1. Rocq's `ai_principal_typing` doesn't exclude F32/F64 for packed `STORE`, while its own
     `Instr_ok` does. The Lean version is the stricter, consistent one. This is worth reporting
     upstream.
  2. The generated `wf_store` ignores `ELEMS`, and there is no `wf_eleminst`. This may be a
     generator omission.
  3. `VLOAD … SPLAT`'s typing rule may under-constrain the lane width. This was flagged on
     2026-09-23 and never followed up.
- **Still yours to decide:**
  - whether to delete the 16 marked `sorry`s;
  - B and C upstream;
  - whether the generator should give the opaque builtins real definitions. That is the only way
    the last 62 `sorry`s go away.

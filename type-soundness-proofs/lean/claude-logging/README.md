# claude-logging index

This directory tracks progress on translating the Rocq WASM 2.0 type-safety
proof (`spectec/test-rocq/theories/`) into Lean 4, in
`spectec/src/test-lean-claude/`.

- `for-humans/` — short, intuitive summaries. Read this if you're a person
  checking in on progress.
- `for-claude/` — verbose, precise technical notes for a future Claude
  session with zero context. Read this if you're picking up this task cold.
- `safety-checks/` — timestamped output of the periodic check that verifies
  nothing outside `spectec/src/test-lean-claude/` has been modified.
- `is_wf_theorems.md` (in `for-claude/`) — tracks which `*_is_wf` theorems
  from the backend-generated `wasm2.0.lean` were relied upon, and whether
  they're believed true/false/unknown.

Start with `for-claude/NOTES.md`.

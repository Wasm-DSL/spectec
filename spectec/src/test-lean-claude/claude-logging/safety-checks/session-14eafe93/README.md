# Scratchpad-only safety checks from session 14eafe93 (bundle23-24)

During bundle23 only `wasm2.0.lean` could be written, so the safety checks ran read-only from the
session scratchpad (`tools/only_wasm_check.sh <label>`). Each compared the repository with a
session-start baseline: `git status`, HEAD, every path newer than a start marker, `.git` entries,
and checksums under `test-lean-claude`. These are their `git status`/newer-path outputs, copied here
in bundle28:
- `interim1`: during bundle23.
- `recovery1`: after the Claude Code restart.
- `after-expB`: after bundle24's generator experiment.

Each found the repository unchanged since the baseline (the `git status` entries are the user's own
uncommitted changes, present at session start).

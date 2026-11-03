# Model / session metadata for response_25

## Model identity
- **Model:** Opus 5.5 (`claude-opus-5-5`); knowledge cutoff June 2026 (system prompt).
- Reasoning effort, sampling parameters, plan/billing tier and wall-clock limits are not stated in a
  form I can verify.

## Session / harness
- Same session as bundle23 (conversation `14eafe93-c912-45da-8e28-e9b09c1a6ef6`); Claude Code, VSCode native extension, auto mode. Ultracode off;
  no subagents or workflows in this bundle.
- Work: read only. The experiment's commands were recovered from the session transcript, and
  the scratch generator copy (`scratchpad/expB/spectec`) was diffed against the repo's `main.ml`.
  No Lean was run.
- **Scratchpad:** `/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad`.
- Lean, when used, ran only through `scratchpad/tools/lrun.sh` (`flock`-serialized,
  `systemd-run` 12 GB cap, the toolchain's `lean` directly; never `lake` in the repo).

## Environment
- Working directory `/home/zhengyew/spectec`; branch `lean-backend-proof`, HEAD `810776a7e`.
- Lean `leanprover/lean4:v4.32.0`. External network: none in this bundle.

## Token / usage accounting
- Not shown in a form I can verify.

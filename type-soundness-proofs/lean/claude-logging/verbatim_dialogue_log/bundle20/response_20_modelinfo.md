# Model / session metadata for response_20

## Model identity
- **Model:** Opus 5.5 (`claude-opus-5-5`); knowledge cutoff June 2026.
  - The turn began right after `/model opus` ("Set model to `claude-opus-5-5`").
  - The environment block described the model as Opus 5 / `claude-opus-5` before a later update
    named Opus 5.5.
- **Subagents:**
  - inherited the session model, except the 15 helper-lemma proof batches, which were explicitly
    run on Sonnet (`model: 'sonnet'`) to save usage;
  - the system prompt lists Sonnet 5.5 as `claude-sonnet-5-5`;
  - reasoning effort was not overridden.

## Session / harness
- **Harness:** Claude Code, VSCode native extension, in **auto mode**, with **Ultracode** on (use
  the Workflow tool for substantive tasks).
- **Session:** the session that wrote bundle16 (conversation `159a29a7-9080-4c0e-830f-ae0ec8fb4c8d`),
  resumed after a `/compact`. Bundles 17-19 were written by another session (uid-1002 scratchpad);
  this session caught up on them by reading every bundle17-19 file, as instructed.
- **Scratchpad (outside the repo; temp files only):**
  `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad`.
  It holds the Isabelle download, the side-by-side extracts, briefs, chunk files, merge scripts
  and the agents' scratch dirs.
- **Interruptions and mid-turn messages:** see `prompt_20.md`.
  1. **Usage limit.** The first audit workflow (11 agents) died on the account usage limit at
     ~13:33; the user's "continue" came at ~18:47.
  2. **Mid-turn inputs 3 and 4.** Questions about status and issues. The replies are logged in
     `response_20_midturn3_status.md` and `response_20_midturn4_issues.md`.
- **Token counter:** reset to 15,000,000 at each user message; ≈14.95M remained at the end.

## Workflows run (orchestration)

| Run | Agents | Subagent tokens | Duration | Result |
|---|---|---|---|---|
| `preservation-audit` `wf_19300dcc-f8c` | 11 | ≈2.12M | ≈6.5 min | all failed (usage limit) |
| `preservation-audit-v2` `wf_67c8bfe9-04b` | 10 | ≈1.74M | ≈39 min | all done |
| `progress-signatures` `wf_88e0cc43-5d4` | 13 | ≈1.56M | ≈51 min | all done |
| `progress-proofs` `wf_cb22b074-0c2` | 43 | ≈5.86M | ≈1 h 58 min | all done; 280/280 proved |

Total ≈11.3M subagent tokens, 77 agents (66 successful).

## Lean / tooling
- Lean `leanprover/lean4:v4.32.0` with Mathlib `v4.32.0`. Final `lake build`: clean, 3006 jobs.
- Each `lake env lean` peaks at ≈3.6 GB RSS, mostly shared olean pages; the machine has 31 GB,
  and the user's editor runs 6 Lean servers. Lean-running agents were therefore capped at 3
  concurrent.
- **External network, read-only:**
  - `git ls-remote upstream` (upstream `rocq-backend-proof-final` still at `95c256c2c`, identical
    to the local copy);
  - `gh api` downloads of `isabelle-mech-backend` @ `41e27cc54`
    `spectec/isabelle_type_safety_proof/*` into the scratchpad.
- **Safety:** baseline `safety-checks/check-20261005T051653Z.txt`. Every main-thread and subagent
  check verified zero changes outside `spectec/src/test-lean-claude`.
  - One spurious `DIFFERENCE FOUND` in the first wave came from a race on second-resolution
    filenames when agents ran checks concurrently. It was diagnosed by the agents and fixed by
    making `verify_against_baseline.sh` race-free.

# bundle20 checkpoints (for recovery if the session dies mid-turn)

- `TypeProgress_with_proofs_checkpoint.lean.txt`: `TypeProgress.lean` with every prover-agent proof
  returned so far spliced in, validated with `lake env lean` (no errors) at the time of copying.
  The `.txt` extension keeps it out of any Lean tooling. To use it: copy it over
  `spectec/src/test-lean-claude/TypeProgress.lean` and run `lake build`.
- `merge_proofs.py`: splices the proofs from the `progress-proofs` workflow journal into a
  `TypeProgress.lean`. The journal is at
  `~/.claude/projects/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/subagents/workflows/wf_cb22b074-0c2/journal.jsonl`.
  Usage: `python3 merge_proofs.py <journal> <in.lean> <out.lean>`.
- `merge.py`: the script that assembled `TypeProgress.lean` from the signature chunks (scratch
  paths inside).

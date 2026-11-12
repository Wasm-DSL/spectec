# bundle23 subagent logs

- `<label>/safety_start.txt`, `safety_end.txt`: the safety check each agent ran at its start and end
  (repo `git status` compared with the session baseline). Round-2 agents (`r2-*`) were stopped before
  finishing, so `r2-vunop-vbinop` has no end check and `r2-vcvtop`'s end check was written before
  the stop.
- `<label>/result.json`: the structured result each round-1 agent returned (theorem name, status,
  proof text, notes).
- Full transcripts, and every agent's probe and final files: see `response_23_modelinfo.md`
  (*Workflows run*) and `~/.claude/projects/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/saved_work_bundle23/`.

# Prompt 20 (verbatim)

Context notes (not part of the user's message):
- This turn is in the **bundle16 session** (the Opus session that wrote bundle16),
  resumed after a `/compact` and a `/model opus` switch (harness output:
  "Set model to `claude-opus-5-5`"). Bundles 17-19 were written by a *different*
  session (Opus 5.5, `claude-opus-5-5`); per the message below, this session is
  addressed as if it had done all of that work. See `response_20_modelinfo.md`.
- The message arrived as an invocation of the `/workflow-authoring` skill whose body
  was pasted content (reproduced verbatim below). An `<ide_selection>` note
  accompanied it: lines 1-26 of `spectec/src/temp_zy_dev/scraps.md` were selected,
  containing the same text, noted as "may or may not be related to the current task".
- A system note says "Ultracode" is on for the session (use the Workflow tool for
  substantive tasks; token cost is not a constraint).
- Session in "auto mode" (prefer `Bash` for reads/edits where simpler).

---

Note: This prompt is being written for the session whose last response was in bundle16.

There has been significant work done in a different section. Catch up with all the work that has been done by exhaustively reading all the files in all the bundles after the one you last created. Update yourself with any refinements that have been made to instructions in them. Also check the actual state of the Lean code, and check the latest state of the live upstream `rocq-backend-proof-final` branch.

For convenience, you will be addressed as if the entire project has been done by your session.

___

Now, your instructions are to:

1. In response to bundle19: "There are no new blocking issues. One question from bundle18 is still open: can I delete the 16 unused sorrys (15 in HelperLemmas, plus Val_ok_store)?" -- don't delete them, but mark them all with the comment `TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED`.

2. Double check if preservation has been meaningfully completed and makes sense. You should do this by:
  1. Checking against the Rocq proof in `https://github.com/Wasm-DSL/spectec/tree/rocq-backend-proof-final/spectec/test-rocq/theories`
  2. Checking against the Isabelle proof in `https://github.com/Wasm-DSL/spectec/tree/isabelle-mech-backend/spectec/isabelle_type_safety_proof`
  3. Checking if the Lean proof itself of preservation makes sense.
  4. Since Lean has proof irrelevance, you can save effort by just checking the signatures -- no need to delve into the details of proofs (apart from if they use axioms etc). If you create agents for this, make sure they note this too.
  4. Note that there are some known deviations (should be noted in previous bundles) of Lean from the Rocq proof, for example including length facts in certain theorems, etc. There is also a known `sorry` in `Step_read_is_wf` that is waiting for a spec-side change. If you create agents for this, make sure they note this too.
  5. Be aware that the goal has shifted from exact precise correspondance to the Rocq proof, to just making the Lean proof itself correct and watertight, although there is still a strong preference for direct correspondance to the Rocq proof, both for maintenance and human readibility / checkability reasons. If you create agents for this, make sure they note this too.
  6. Finally, synthesize a report in the new bundle as a user-requested document, and suggest how I should go about checking the preservation proof manually -- what is the overall shape of the proof, what are the most important parts of the proof to understand, any custom infrastructure or design patterns to recognize etc.

3. If preservation presents no further significant issues, move on to progress -- try and prove progress by referencing the Rocq and Isabelle proofs. Try as far as possible to exactly match the Rocq proof, but you can deviate (and explicitly list the deviations in a user-requested document if so) if needed. You should:
    1. Check what new theorems / defs / etc are needed for proving progress in the Rocq proof, and create them in Lean with signatures only (use `sorry` for the bodies), and audit that the signatures line up first.
    2. Move on to proving the bodies. Remember my guidance as to how to approach porting proofs from Rocq: If you encounter difficulties in the proof, you might gain some help by trying to replicate closely the tactics used by Rocq in the Rocq proof, and diverge only when needed. If that still fails, take a step back and try and understand the Rocq proof body as a whole before proceeding to translate the intuition into Lean.

Remember all your standing orders regarding safety and logging.

---

## Mid-turn input 2 (verbatim)

Context notes (not part of the user's message):
- Arrived after the background preservation-audit workflow (`wf_19300dcc-f8c`, 11 read-only
  auditor subagents) reported that **all 11 agents failed** with
  "You've hit your session limit · resets 6:10pm (Asia/Singapore)" (≈2.12M subagent tokens,
  460 tool uses, ~6.5 min elapsed, 0 results returned).
- State at that moment: the 16 unused `sorry`s were already marked (task 1 done, build clean,
  safety check clean); progress definitions drafted in the session scratchpad; an axiom
  inconsistency had been found and machine-checked (`TLC.ibytes_len'` and `TLC.ibytes_len''`
  each derive `False`; unused by any proof).
- An `<ide_opened_file>` note accompanied the message: the user had
  `bundle20/prompt_20.md` open in the editor ("may or may not be related").
- The session's token counter was back at 15,000,000 after this message.

```
You were interrupted due to usage limits. Please continue from where you left off. Remember your standing instructions to log this.
```

---

## Mid-turn input 3 (verbatim)

Context notes (not part of the user's message):
- An `<ide_opened_file>` note accompanied it: the user had `spectec/src/test-lean-claude/wasm2.0.lean`
  open in the editor ("may or may not be related").
- The session's token counter was back at 15,000,000 after this message.
- State at that moment: the preservation audit was complete and the report written; the
  progress signatures were done and installed (`TypeProgress.lean`, 280 `sorry`s); the
  `progress-proofs` workflow (43 batches) was running, with 3 batches returned (M01, H01, H02:
  29/29 targets proved and validated in a scratch merge).
- The status reply to this message is logged verbatim in `response_20_midturn3_status.md`.

```
Please let me know what is currently going on; you seem to be running a lot longer than previous turns. Remember to log this exchange. No need to interrupt your ongoing work just yet, but I would like a status report and what you have left to do.
```

---

## Mid-turn input 4 (verbatim)

Context notes (not part of the user's message):
- An `<ide_opened_file>` note accompanied it: the user had `spectec/src/test-lean-claude/wasm2.0.lean`
  open ("may or may not be related").
- The session's token counter was back at 15,000,000 after this message.
- State at that moment: the `progress-proofs` workflow was running, with 32 of 43 batches
  returned. 249/280 targets were proved and validated in a scratch merge (all 188 helper lemmas,
  `t_progress`, `Instr_ok_Instrs_ok`, and 59 of the 90 instruction cases). No target had failed.
- The reply to this message is logged verbatim in `response_20_midturn4_issues.md`.

```
So far, have you encountered any errors or issues or design choices?
```

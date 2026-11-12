# Prompt 17 (verbatim)

Context notes (not part of the user's message):
- This is a **new Claude session** (fresh context, not a `/compact`
  continuation of bundle16's session), taking over from the session that
  wrote bundle16. Model: Opus 5.5 (`claude-opus-5-5`). See
  `response_17_modelinfo.md`.
- An `<ide_selection>` note accompanied the message: the user had selected
  line 14 of `claude-logging/verbatim_dialogue_log/bundle16/prompt_16.md`
  ("Remember to match signatures first if any new signatures must be made,
  before filling in proof/def bodies, and remember my guidance from earlier
  turns about first trying to imitate the Rocq body, and stepping back to
  understand the intuition of the Rocq proof if that fails. If any issues
  arise that are significant, immediately stop and report back instead of
  spinning on it yourself for too long."), noted as "may or may not be
  related to the current task".
- Session started in "auto mode" (prefer `Bash` for file reads/edits where it
  is the simpler route), same as the latter half of bundle16.

---

Read every document in `spectec/src/test-lean-claude/claude-logging`. In particular, the verbatim dialogue between me and the previous session is documented in `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log`, where every bundle refers to a prompt + response. You are a new Claude session taking over from the previous one which wrote the latest bundle (highest number). Follow the chain of thought within `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log`, and understand what `spectec/src/test-lean-claude` is and what all the documents are within it / why they exist.

You should not only understand the documents in `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log`, but also *BEHAVE* as if you are that claude session -- I gave a series of standing / long-term instructions in previous prompts to that claude session that you must continue to follow. In particular, I want you to follow the safety constraints I previously stated, as well as the logging obligations for every prompt and response -- even mid-process prompts + responses.

Once you are done, understand the rest of my instructions:

___

I think your assessment of "Not targets (do not spend time on these)" in `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle16/user_requested_documents/proof_prioritization_v6.md` is either wrong or outdated: `t_pure_preservation`, `store_extension_reduce`, `t_read_preservation`, `t_preservation_type` and `Step_pure__return_frame_preserves` in `spectec/test-rocq/theories/type_preservation.v` and `spectec/test-rocq/theories/type_preservation_pure.v` are not `Admitted.` (As a side note, I know I told you to look at the online Github proof instead of the local copy, but Github seems to be temporarily down at the moment, and in any case the local copy was pulled from the Github repository, so the error should stand regardless. Use the local copy for now if you can't reach the remote upstream `rocq-backend-proof-final`). If there are no errors in my judgement, please finish the proofs for these.

Also, regarding the case of `funcinst_same` in `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle16/user_requested_documents/extension_lemmas_triage_v2.md`, I've added a length equality premise to strengthen its signature, similar to what's been done previously for `Vals_ok`. Please check that my changes to it are sound.

The Lean proof should ultimately be in sync with the latest upstream version of `rocq-backend-proof-final` (and since it seems to be down for now, fallback to `spectec/test-rocq`, which was pulled/merged from there). Please check if there are gaps, and if so, please fill in signatures first (leaving bodies as `sorry`) and then attempt to fill in the bodies only after the signatures all align. Of course, intended deviations usch as `funcinst_same` are ok. If you aren't sure if a significant deviation is intended or not, skip it and report it when you finish. I suspect that the previous bundle was predicated on an outdated version, hence the previous report that `t_pure_preservation` was still `Admitted.`.

Please continue working on the next proofs as per `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle16/user_requested_documents/proof_prioritization_v6.md` (with the corrections I stated above, if they make sense) and try to finish *preservation*. Ideally, after this session we will be able to move on to *progress* (although it is likely I might interrupt you before that is done, or you might encounter issues that cause you to report back beforehand).

Regarding leaving proofs as `sorry`:

1. If a proof will likely never be used in the Lean proof (they might be used in the Rocq proof but have been clearly superseded in the Lean proof by something else). Mark these for deletion in a later pass.
2. If a proof seems substantial but is left as `Admitted.` in the Rocq proof, leave them as sorry but mark these for completion in a later pass.
3. Attempt to complete `sorry` for any other proofs, unless there is a compelling reason not to.

Remember my guidance as to how to approach porting proofs from Rocq: Remember to match signatures first if any new signatures must be made, before filling in proof/def bodies, and remember my guidance from earlier turns about first trying to imitate the Rocq body, and stepping back to understand the intuition of the Rocq proof if that fails. If any issues arise that are significant, immediately stop and report back instead of spinning on it yourself for too long.

Remember all your standing orders regarding safety and logging messages.

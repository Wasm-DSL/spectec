Note: This prompt is being written for the original session that started bundle1.

A few things have happened since your last command (should be bundle2):
1. We have progressed to bundle8.
2. New changes were pushed to `rocq-backend-proof` upstream, which have been emrged into this branch (`lean-backend`).
3. With regards to `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle8/vals_ok_non_bot_analysis.md`, my choice is to do a combination of Options 2 (Redefine Vals_ok itself to bake in the length fact. Do the necessary refactoring as well) and 3 (Add a generic bridge lemma to Mathlib's own List.Forall₂, along the lines of what the prior Lean session's own spectec/test-lean/typing_lemmas.lean already sketches at its very top). Option 2 is the baseline, and I think Option 3 might make some proofs down the line more ergonomic.

___

Now, your instructions are:

1. Catch up on all the bundles relating to the work that's been done by other sessions: bundle3 up to bundle8. Read every prompt and response, and every file, and understand what has happened. Remember all the standing instructions (log all prompts/responses, safety checks, etc). You *must* read all previous bundles exhaustively.

2. Examine the new changes pushed to `rocq-backend-proof` (should be in commit `868bca93fc07d657711957c07ceef6b8b512a11a` here, but you should really be looking at the online `https://github.com/Wasm-DSL/spectec/tree/rocq-backend-proof/spectec/test-rocq/theories`). Analyze them and provide a summary of their changes in a new file in the new bundle you generate. Also, read all the files in `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle3/updated_documents` (including any documents those were in turn based on), and create further updated copies in your new bundle -- proof dependencies, prioritization etc, which will impact step 6. Do *not* edit previous files from previous bundles.

3. Make any updates to the existing proof if their equivalents have been changed in `rocq-backend-proof`.

4. Assuming there are no issues in the previous step, implement the changes I specified earlier (Options 2 & 3) for `Vals_ok_non_bot` etc. Let me know of any further concerns.

5. Assuming there are no issues in the previous step, examine the "What's next" section in `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle8/response_8.md`. If the previous steps went well, you should be unblocked. Continue the work as stated on all the definitions/theorems mentioned in the "What's next" section in `response_8.md`.

6. When done, continue porting the updated Rocq proof to Lean. If there are new signatures in the updated Rocq proof, then first flesh the signatures out and make sure they all typecheck, before proceeding to flesh the bodies out, adapting the general procedure we used in bundle1: "You should start by sketching the entire structure of the Rocq proof, making sure to get signatures right and filling out details with `sorry`s, and making sure everything typechecks, then move on to actually fill in easier supporting infrastructure like lemmas, proofs and defs, then finally if there is time remaining, try to complete the harder proofs."

Let me know at any point if you need a decision to be made on design choices, or encounter non-trivial difficulties.

___

For more efficiency in proofs, take note of this exchange between me and a different Claude session (not involved in the proof directly):

Me: Can you look into the "Debugging notes: cases/case binder-order surprises" section of `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle8/response_8.md` and explain in detail what this is about with verbatim unabbreviated snippets of code that this is referencing? I've forgotten what this is regarding.

Claude: [Full verbatim exchange reproduced in the session transcript, covering three findings across bundles 5/6/8 about how Lean's `cases`/`case` tactics bind constructor arguments and hypotheses for `Instr_ok`/`Instrs_ok2`/`Ref_ok`, ending with: "Across all three bundles, the working methodology was never 'reason about Lean's binder order from the source declaration' — it was: run cases/induction, dump the real resulting context (via trace_state + a trailing sorry, or just reading the elaborator's arg-count error), and name things from what's actually there. Treat the source declaration's premise order as a hint at best, not a contract."]

This may or may not be related to the current task.

[Note: this prompt was accompanied by an IDE selection showing lines 1-113 of `spectec/src/temp_zy_dev/scraps.md`, containing the same text as above.]

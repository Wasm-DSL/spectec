# Prompt 18 (verbatim)

Context notes (not part of the user's message):
- Same session as bundle17 (context retained; not a new session). The token counter
  was back at 15,000,000 at the start of this turn.
- An `<ide_selection>` note accompanied the message: lines 1-11 of
  `spectec/src/temp_zy_dev/scrap.md` were selected, containing an earlier draft of this
  same message (it lacks "To address your blocking issue", "The `val` rules are
  untouched for now", the upstream-reference sentence and the "Ditto for theories..."
  sentence, and adds "The aim should now be to prove preservation without `sorry`s;
  strict adherence to the Rocq proof is ideal but not necessary." in the same place as
  the final text). Noted as "may or may not be related to the current task".

---

I've made changes:

1. Removed the extra premise in `Step_pure__br_table_ge_preserves` -- I think it is redundant.

2. To address your blocking issue, I've regenerated `wasm2.0.lean` using `splice` -- hopefully this is sound and fixes the `with_mem` issue. The `val` rules are untouched for now.

Check that my changes make sense, are correct and safe, and if so, continue your work. The aim should now be to prove preservation without `sorry`s; strict adherence to the Rocq proof is ideal but not necessary. Try and reference the upstream live `rocq-backend-proof-final`, and if that is unreachable, use the local `test-rocq`, which was pulled from there.

Let me know if I've missed any blocking issues / more blocking issues arise. Ditto for theories that are unprovable / can derive False.

Remember your standing instructions as well as guidance on how to prove theorems referencing the Rocq proof.

## Mid-turn input 1 (verbatim)

Context note (not part of the user's message): an `<ide_selection>` note accompanied it,
reporting lines 82-86 of `claude-logging/verbatim_dialogue_log/bundle16/prompt_16.md` selected
(the same text, i.e. bundle16's mid-turn input 5, re-sent), "may or may not be related to the
current task"; the text itself arrived as pasted content. State at the moment of this message:
`lake build` clean; `store_extension_reduce` fully proved (modulo the flagged
`rat_to_nat_natCast` and generated `*_is_wf`); `t_read_preservation` still `sorry` (planning
only, no code written).

```
I'd like you to stop soon.

Please finish up the proofs that you / your agents are currently actively working on, and then report the current status / changes. Please create new updated copies of each file from `spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle15/user_requested_documents` (don't mutate documents from previous bundles!). If you have any insights that would be useful to the next turn (especially if the next turn is done using a less powerful model or a different session altogether), please document them extensively and as verbosely as necessary in a `insights_for_next_turn.md` auxiliary document to give it the benefit of your work that is not yet directly reflected in the Lean code.

Remember your standing instructions.
```

## Mid-turn input 2 (verbatim)

```
You might be interrupted soon due to session limits.
```

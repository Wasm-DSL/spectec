# Response 29 (verbatim)

---

Written for: you. The detailed document in the log is also meant for later sessions.

All 89 `sorry`s in `wasm2.0.lean` are proved, and the file is installed. I found no model issue that required stopping: the restored length premises are enough. The one oddity I list below already existed before this regeneration, and no proof depends on it.

**Status**
- `wasm2.0.lean` has 0 `sorry`s. The word appears only inside the two commented-out original statements, as in `OLD_wasm2.0.lean`. The file is 17,527 lines; the generated one was 15,848.
- It compiles with 0 errors. All 89 warnings are unused-variable linter warnings on generated definitions, the same 89 the generated file produces.
- `#print axioms` on all 181 theorems shows only `propext`, `Classical.choice`, `Quot.sound` and the model's own axioms for opaque functions. None uses `sorryAx`.
- Replaying everything in the kernel with every `Inhabited` instance opaque finds 0 of 3,625 theorems that need a default value.
- The 87 theorems without hand edits have exactly their generated statements, and all generated text other than theorems is unchanged.

**Additions**
- **Hand edits**, as in `OLD_wasm2.0.lean`: `Step_read_is_wf` and `Step_is_wf` are moved below `Store_ok` and given the premise `Store_ok (fun_store z)`.
  - The `Step_read` relation itself needs no edit, and OLD doesn't edit it either, so I took "`Step_read`" in your message to mean `Step_is_wf`.
  - I re-checked on this model that the unedited statements are false: a table with 2^32 entries makes `table.size` produce an invalid `u32`.
- **89 proofs:**
  - 81 come unchanged from my bundle23 attempt.
  - 2 are adapted: `zero_is_wf` and `default__is_wf` now invert `fun_fzero` and `fun_default_`.
  - 6 are new:
    - `vunop__is_wf`, `vbinop__is_wf` and `vcvtop___is_wf` use the restored length premises.
    - In `Step_pure_is_wf`, the restored premise closes the `vshiftop` gap.
    - `Step_read_is_wf` and `Step_is_wf` now pick premises by type, so they no longer depend on premise order.
- **92 helper lemmas**, each marked `/- HELPER LEMMA CREATED BY CLAUDE -/` and placed directly above its first user (checked by script):
  - 81 come from bundle23.
  - 10 are new: lane and setproduct lemmas for the vector theorems, and `iswf_fun_growmemory_pages_lt` for `Step_is_wf`.
  - 1 is adapted: `iswf_store_I32_8`, for the restored STORE premises.
- The full table of theorems and helpers, with line numbers, is in `claude-logging/verbatim_dialogue_log/bundle29/user_requested_documents/wasm2.0_additions_and_impact.md`.

**Impact on the rest of the proof**

I compiled each downstream module against the new model in the scratchpad. Proofs that break become `sorry`, and declarations whose statements no longer elaborate are deleted:

| module | declarations | broken |
|---|---|---|
| `HelperLemmas`, `Subtyping`, `TypingLemmas`, `TypePreservationPure` | 295 | 0 |
| `ExtensionLemmas` | 128 | 1 |
| `TypePreservation` | 135 | 12 |
| `TypeProgress` | 298 | 91 |

- In total, 104 of 856 declarations break (12%), against 101 for the bundle23 model.
  - The 5 newly broken ones all use `fzero` or `default_`, which are now relations.
  - Two declarations no longer break: `vcvtop_step_full` and `vcvtop_step_half`.
- The main cause is the same as before: model functions that are now relations but are still used downstream as functions. Examples are field access on `fun_table`/`fun_mem`/`fun_global` results, `lsize`/`sizenn`, `with_*`, `vv*op_`, and the results of `unop_`/`testop_`.
- The preservation side is mostly mechanical. Most of the work is in `TypeProgress`:
  - 44 progress cases must now build `Step` derivations whose premises are relations. That needs new existence lemmas, such as `∃ t, fun_table z x t` and `∃ v, fun_default_ t (some v)`.
  - 47 auxiliary lemmas need restating over the relations.

**Things to know**
- `wasm2.0_prevattempt.lean` is not my half-finished attempt. It is the bare bundle23 model, with 90 `sorry`s. The attempt only ever existed in my scratchpad, which is where I took the proofs from.
- I found one non-blocking issue in the model. The float constructors of `fun_vunop_`/`fun_vbinop_` use `Option.get! (proj_lane__1 l)` without a `≠ none` premise, which the integer constructors have.
  - It is also in OLD and in the bundle23 model.
  - It only matters for ill-formed lanes, and no proof relies on it.
  - It is still one `get!` with no bound premise, i.e. a place where indexing isn't yet principled.
- The repo's `.lake/build` oleans are stale. `lake build` would rebuild `wasm2.0` and then hit the downstream breakage above.

**Checks and logs**
- The final safety check finds that the only changed paths are `wasm2.0.lean` and new files under `claude-logging/`. It is `claude-logging/safety-checks/check-20261102T170252.546900404Z-bundle29-final-241330.txt`. The four agents' start and end checks are in the same folder, and all are OK.
- This exchange is logged in `claude-logging/verbatim_dialogue_log/bundle29/`: the prompt, this reply, model info, the document above, the agents' results and the evidence files.

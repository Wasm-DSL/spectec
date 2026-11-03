# Response 24 (verbatim)

Reply to the main message (`forall_postmortem.lean`, length-checking Foralls, running Sideconditions
twice). The follow-up's reply is in `response_24_followup_pass_ordering.md`.

---

Both approaches work, and I tested each in a scratch copy, not just in theory. Running `Sideconditions` again after `DefToRel` is a one-line change and needs no memory of what it already generated. Length-checking Foralls are possible too, but need a special case for self-referencing relations.

**What the postmortem says.** The Foralls are custom, zip-based, non-inductive definitions for a kernel reason. Lean rejects a relation whose own constructor contains it inside an inductive "container" (`List.Forall₂`, `Prod`, and also `And`, i.e. `∧`). A plain `∀ t ∈ …` (a Pi type) is always accepted. The earlier attempt put `length = length ∧ …` into the shared `Forall₂`/`Forall₃` definitions, and that broke `fun_utf8_case_4`, which calls `fun_utf8` through a `Forall₂`. The postmortem recommended relying on the separate length premises from `Sideconditions` instead, and those are what the pass reorder lost.

**1. Can the Foralls check lengths?** Yes for WebAssembly 2.0, with one special case. I compiled your regenerated file with the length conjunct added to the shared definitions:
- **Kernel:** only `fun_utf8_case_4` is rejected. The 230 other errors are follow-on failures, because `wf_name` uses `fun_utf8`. When that one rule uses a plain unchecked variant, the whole model compiles with no errors.
- **My merged proofs:** only 4 small helpers needed adjusting, to read the length and the zip parts separately. The `Step_pure_is_wf` gap then closes from the length the premise now carries, leaving only the 4 known `sorry`s.
- **Cost:**
  - the backend must detect relations that refer to themselves (or a mutual sibling) through `Forall₂`/`Forall₃`, and use the unchecked variant plus a separate length premise there; the postmortem drafted that analysis but never used it;
  - every downstream use changes meaning, about 170 `Forall₂`/`Forall₃` uses and about 300 length-hypothesis sites;
  - WebAssembly 3.0 may have more self-referencing relations, so the kernel check would have to be rerun there.
- **Gain:** Lean would match Rocq's `Forall2` and Isabelle's `list_all2`, and this whole class of bug would stop depending on pass order.

**2. Running `Sideconditions` again after `DefToRel`.** It needs no record of earlier work. The pass already removes duplicate premises within each rule, and its equality check (`Il.Eq.eq_prem`) compares only structure and names, not source positions (`sideconditions.ml:110–126`). Also, `DefToRel` lists its fresh result list first in each iteration (`deftorel.ml:120`), so a second run produces exactly the old `|var_k_lst| = |x_lst|` form.

I tested it: I built a copy of the generator in the scratchpad (the unmodified copy reproduces your `wasm2.0.lean` byte for byte), listed `Sideconditions` a second time after `DefToRel` in `all_passes`, and regenerated.

| | Now | Run twice | Old model |
|---|---|---|---|
| Length premises on `var_k_lst` | 0 | 284 | 283 |
| `Forall₂`/`Forall₃` premises with no length premise | 171 | 15 (the old 13, plus 2 option cases now covered by `↔` premises) | 13 |
| STORE size bound enforced | no | yes | yes |
| Duplicate premises / premises lost | | 0 / 0 | |
| Compiles; theorem statements | yes | yes; all 90 unchanged | |

Side effects:
- Surviving premises change order in 100 rules (vector operators, `Step_read`, `Step_pure`, `Step`). That shifts binder positions in proofs: 81 of my 85 proofs compile unchanged on the twice-run model, and 4 need binder fixes (`Step_pure_is_wf`, `Step_read_is_wf`, `Step_is_wf`, `iswf_store_I32_8`).
- `fun_instantiate` gets back 4 redundant index bounds that differ only in variable names; the old model had them too.
- The change also affects the Rocq output, since both targets share the pass list. Use a separate pass name enabled only for Lean if you want it Lean-only.
- If you also want to avoid the reordering, have `DefToRel` emit the length premises itself for the lists it creates, instead of rerunning the whole pass.

**My recommendation:** run `Sideconditions` again. It's the smallest change, I verified it end to end, and it gives back the old model's shape on top of the new bounds. The Forall change is the more robust long-term fix, and the two combine without conflict.

The repo is unchanged (final check clean) and nothing is running. The experiments are in the saved folder under `scratchpad/expA*` and `scratchpad/expB`, and this exchange's log is staged as `bundle24_staging/`.

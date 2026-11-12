Your changes check out, and `store_extension_reduce` is now proved. `t_read_preservation` is the one real proof left. I stopped before starting it, as you asked, and wrote up how to do it.

**Your changes: correct and safe**
- **`br_table_ge`:** removing the extra premise was right. The lemma now matches Rocq and is proved.
- **`splice` regeneration:** sound. `splice` is clamped, so it never changes the memory's length. I proved it equals Rocq's `list_slice_update` (`HelperLemmas.splice_eq_list_slice_update`), and the store rules go through with it.
- **`val` rules:** leaving them untouched is fine. `with_mem` ignores its length argument now.

**Proved this turn** (sorries 26 → 18; bundle 17 made no Lean edits)
- **`TypingLemmas` and `TypePreservationPure`:** now 0 sorries. That includes the whole SIMD section, the control lemmas, and `t_pure_preservation`.
- **`TypePreservation`:**
  - `t_preservation_type`
  - `mem_store_extension`
  - the SIMD load/store lemmas
  - `store_extension_reduce`, with one lemma per store-writing rule
- **`ExtensionLemmas.construct_meminsts_grow`:** now takes an optional maximum, as Rocq does. It used to assume a maximum always exists, which made it unusable for memories without one.
- **No more `Step_is_wf` in `store_extension_reduce`.** Rocq's proof uses it, but `Step_is_wf` is false (issue 2 below). The new store components' well-formedness comes from the instructions, the old store, and the grow relations' own premises instead.

**What's left**

| Sorry | Status |
|---|---|
| `t_read_preservation` | Real work: 47 rules. The plan is in `insights_for_next_turn.md` §3. |
| `rat_to_nat_natCast` | Can't be proved; see issue 1. |
| 15 in `HelperLemmas`, plus `Val_ok_store` | Dead (your rule 1). Nothing uses them, and most are false for the zip-based `Forall₂`. Can I delete them? |

`t_preservation` now rests on three groups of sorries. I traced these with a dependency walk, not just `#print axioms`:
- `t_read_preservation`
- `rat_to_nat_natCast`
- generated theorems: `Step_is_wf`, `Step_pure_is_wf`, and the `nbytes_`/`ibytes_`/`vbytes_`/`wrap__` `_is_wf`

**Blocking issues**
1. **`rat_to_nat` is `opaque`, so nothing about its values can be proved.**
   - The `memory.grow` case needs `rat_to_nat (n : Rat) = n`. I isolated that as one flagged lemma, `rat_to_nat_natCast`.
   - The lemma can't contradict the rest of the model: it holds for `r.floor.toNat`.
   - Fix: generate `rat_to_nat` as a real function, e.g. `fun r => r.floor.toNat`. The lemma then takes one line.
2. **`t_read_preservation` and `t_preservation` are false in one corner case, in Rocq too.** This is the issue I noted in bundle 17.
   - Take a memory of exactly 2^16 pages, `i = 2^32 − 1` and `n = 1`. Then `memory.fill`, `memory.copy` and `memory.init` take a step that pushes `CONST I32 2^32`.
   - That constant isn't a valid i32, so the result can't be typed. The generated `Step_read_is_wf` and `Step_is_wf` are false for the same reason.
   - Rocq's proof only goes through because its `Step_read_is_wf` is `Admitted`. The plan for `t_read_preservation` uses `Step_read_is_wf` the same way.
   - Fix: a spec side condition on the `succ` rules, or wrapping i32 arithmetic.
3. **Possible signature deviation.** `t_read_preservation`'s locals hypothesis has no length fact, and the `local.get` case probably needs one. The likely fix is to take `Vals_ok` instead, like the `hlen` deviations in `funcinst_same` and friends. Not decided yet.

**Safety and logging**
- Everything outside `test-lean-claude` is identical to the baseline, and `lake build` is clean.
- In `bundle18/user_requested_documents/`, written for the next Claude session:
  - `insights_for_next_turn.md`
  - updated copies of bundle 15's three files: `proof_prioritization_v7.md`, `proof_dependencies_v6.md`, `extension_lemmas_triage_v3.md`
- `NOTES.md`, `is_wf_theorems.md` and `SUMMARY.md` are updated.
- I also fixed the stale doc comments in `TypePreservation.lean` and `TypePreservationPure.lean` that still called lemmas "Admitted". They were doc-only changes; the rebuild and safety check after them were clean.

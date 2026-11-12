## `TypePreservationPure.lean`: 20 → 11 real sorries, plus the requested prioritization correction

Continued the same pattern from bundle11. Done this bundle: `unop_val_preserves`, `binop_val_preserves`, `testop_preserves`, `relop_preserves`, `cvtop_val_preserves`, `local_tee_preserves`, `ref_is_null_helper` (+ its two corollaries `_true`/`_false`).

Found and fixed two more Phase-1 signature bugs along the way (same class as the `ai_principal_typing`/`REF_HOST_ADDR` gap from bundle9): `Step_pure__testop_preserves` and `Step_pure__relop_preserves`'s Lean stubs were both missing a `wf_admininstr` hypothesis that Rocq's actual signature has — without it, neither lemma is provable (there's no other way to establish the freshly-produced boolean result is well-formed). Fixed both signatures to match Rocq before proving them. Given this is the third such gap found incidentally, I think a dedicated signature audit against live Rocq would be worthwhile at some point, though I haven't done one yet.

**As requested, updated the prioritization document**: `bundle12/user_requested_documents/proof_prioritization_v3.md`. The correction: `select_preserves_helper` and `if_preserves_helper` were grouped together as "medium" in the original doc, but they're not comparable in difficulty. `if` composes two fixed-shape principal typings in a single step; `select` needs an *exact* equality between two independently-typed values (via non-bot pinning) before any of the composition lemmas apply cleanly — a genuinely different, harder proof shape. I've reclassified it and moved it later in the suggested order, now: `frame_vals` → `return_label` → `br_zero` → `select` cluster → `br_succ` → `br_table_lt`/`_ge`, with the two deliberate permanent gaps (`return_frame`, `t_pure_preservation`) last as before.

`lake build` clean throughout, safety check confirms nothing touched outside `test-lean-claude/`.

**Current tally**: `Subtyping.lean` 0, `TypingLemmas.lean` 0, `TypePreservationPure.lean` **11** (down from 29 at the start of bundle11), `ExtensionLemmas.lean` 76, `TypePreservation.lean` 12.

Continuing with `frame_vals_preserves` next per the corrected ordering.

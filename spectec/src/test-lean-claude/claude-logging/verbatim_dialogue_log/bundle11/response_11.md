## `TypePreservationPure.lean`: 9 lemmas done (29 → 20 real sorries)

Started Tier D following your guidance closely: for each lemma, read Rocq's actual tactic proof first, worked out what its custom `helper_tactics.v` macros (`resolve_wfness`, `invert_ais_typing`, `resolve_all_pt`, `join_subtyping_*`, `construct_ais_typing`) were actually doing mathematically by matching their *result types* against this project's own `instrtype_sub_compose*` family, then wrote the Lean tactic sequence — diverging only where a cleaner route was clearly available once I understood the content.

**Done, all verified against `lake build`**: `Step_pure__nop_preserves`, `_drop_preserves`, `_if_preserves_helper` (+ its two trivial corollaries `_if_true`/`_if_false`), `_label_vals_preserves`, `_br_if_true_preserves`, `_br_if_false_preserves`, `proj_identity`.

One clean divergence worth flagging: `_label_vals_preserves` skips Rocq's second decomposition step entirely by reusing `construct_ais_vals'` (context-irrelevance for value lists, already proved) to jump straight from the label-extended context back to the outer one — shorter than replicating Rocq's own path.

**Deliberately set aside, not attempted**: the `select_preserves_helper`/`select_true`/`select_false` cluster. It's genuinely harder than the prioritization doc estimated — it needs an *exact* equality between two values' types (not just a subtyping bound), established via `Val_ok_non_bot` + `valtype_sub_non_bot`, threaded through four composed principal-typing facts where the straightforward compose-family tools don't directly line up until *after* that pinning happens. I've left a concrete idea for a cleaner attempt in `NOTES.md` (using `ais_vals_typing_inversion` on the two values as a pair, rather than inverting each separately) rather than force a rushed proof now.

Also logged a debugging pattern worth keeping: `subst` on an equation between two free local variables doesn't always eliminate the one you expect, which produced several "unknown identifier" errors this bundle when I kept referring to a name that had actually been substituted away. Fix was consistently to use `rw` against the goal instead of `subst` whenever both sides of an equation are plain local variables I care about keeping.

`lake build` clean after every lemma. Safety check clean.

**Current tally**: `HelperLemmas.lean` 28 (dead), `Subtyping.lean` 0, `TypingLemmas.lean` 0, `TypePreservationPure.lean` **20** (down from 29), `ExtensionLemmas.lean` 76, `TypePreservation.lean` 12.

Continuing with the `unop`/`binop`/`testop`/`relop`/`cvtop_val` cluster next (looks like the most mechanical remaining batch), then `local_tee`, `ref_is_null_*`, `frame_vals`, `return_label`, saving `br_zero`/`br_succ`/`br_table_*` (confirmed genuinely hardest in the file) and `select` for last.

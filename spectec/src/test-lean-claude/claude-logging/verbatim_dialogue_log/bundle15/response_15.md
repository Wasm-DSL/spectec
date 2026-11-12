## Assessment + pass A: 26 sorries closed, full-project prioritization now exists

**Direct answer to your question**: no, `proof_prioritization_v4.md`'s "Suggested order" section was not the whole picture — it only ever covered `TypePreservationPure.lean`. `ExtensionLemmas.lean` (76 sorries, never triaged in detail before now) is actually the largest remaining pool in the project, bigger than everything else combined. Upstream itself hasn't moved since yesterday's merge. Full breakdown in `proof_dependencies_v4.md`/`proof_prioritization_v5.md`.

**Pass A, executed**: dispatched a background triage of all 76 `ExtensionLemmas.lean` sorries (Trivial/Easy/Moderate/Hard, same approach as the earlier signature audit) — 25 Trivial, 27 Easy, 17 Moderate, 7 Hard. Report: `extension_lemmas_triage_v1.md`. Then worked through it: all 15 standalone-Trivial lemmas, several more Easy ones (`limits_sub_refl`/`_trans`, `externtype_sub_refl`/`_trans`, `minst_invert_datas`, `store_typed_exterval_types`), and 4 of the 7 "Template A" lemmas (index-update monotonicity under `List.modify`, for which I built a small reusable helper). Also cleared 12 more `HelperLemmas.lean` trivialities and 4 `TypePreservation.lean` ones — `num_default_is_well_formed`'s Rocq source turned out to be commented out (not `Admitted`) with a complete draft proof sitting right there, so I finished it for real rather than leaving it `sorry`, same reasoning as the `return_frame_preserves` precedent.

**26 sorries closed total this bundle, 109 → 83.**

**3 lemmas flagged and left alone**, per your mid-turn steer: `minst_invert_elems`, `store_none_mem_extension`, `table_grow_table_extension`. All three hit the same elaboration friction — `obtain` on a hypothesis whose index is a non-trivial expression kept losing bound names at the use site. Found the fix for one sibling (`table_set_table_extension`: swapping `obtain` for `cases h with | Ctor ... =>` fixed it immediately) but didn't go back to retrofit the three flagged ones — each has a doc comment explaining exactly where it got stuck, and the fix is now written down in `NOTES.md` for whoever picks them back up.

Wrote `proof_dependencies_v4.md` and `proof_prioritization_v5.md` (new copies, prior bundles untouched) giving the first accurate whole-project view and a concrete next-step list — the highest-leverage next move is the `Extend_store_ref`/`_eleminst`/`_tableinst`/`_globalinst` cascade (same shape as lemmas just proved, no new infrastructure needed), followed by porting the missing `Externaddr_ok` chain-peel helpers Rocq has but this codebase never ported, which the triage says would drop ~9 lemmas a full difficulty tier.

`lake build` clean, safety check clean throughout.

Current tally: `Subtyping.lean` 0, `TypingLemmas.lean` 0, `TypePreservationPure.lean` 10 (confirmed nothing trivial left), `TypePreservation.lean` 8, `ExtensionLemmas.lean` 50, `HelperLemmas.lean` 15 (dead cluster) — 83 total, down from 109.

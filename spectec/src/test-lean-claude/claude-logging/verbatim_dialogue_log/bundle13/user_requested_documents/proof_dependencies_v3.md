# Proof dependencies — consolidated update (bundle13)

Written for: a future Claude session (primary audience). Supersedes
`bundle9/user_requested_documents/proof_dependencies_v2.md` as the
reference to read going forward (kept, untouched, as historical record).
Not driven by the `rocq-backend-proof-final` resync itself — see
`rocq_changes_summary_v2.md` for that; this file's dependency *shape* is
confirmed unchanged by the resync — it's a refresh because three bundles
(10, 11, 12) of substantial progress since v2 made its status table
badly stale (`TypingLemmas`/`Subtyping` were at 13/32 remaining `sorry`s in
v2; both are now fully `Qed`'d at 0).

## File-level dependency graph (unchanged in shape since bundle3, reconfirmed this bundle)

```
                              ┌── TypePreservationPure → TypePreservation
HelperLemmas → Subtyping → TypingLemmas ─┤
                              └── ExtensionLemmas ──┘   (Extension feeds both
                                                          Preservation and,
                                                          separately, Progress)
                                        │
                                        └── TypeProgress   (needs TypingLemmas +
                                                             ExtensionLemmas +
                                                             Subtyping + Axioms,
                                                             NOT Preservation;
                                                             not started — out of
                                                             scope for now, see
                                                             `rocq_changes_summary_v2.md` §1)
```

## Within-file status, ground truth as of bundle13 (direct `sorry`/decl grep, 2026-09-30, post-resync)

| File | Total decls | Still `sorry` | Status |
|---|---:|---:|---|
| `HelperLemmas.lean` | 63 | 28 | Mostly the dead `helper_lemmas.v`-removed cluster (see v2's note, still accurate — 22 of the 28 are unreferenced anywhere downstream). 3 axioms (`nbytes_len`/`nbytes_len'`/`nbytes_inv`) resynced this bundle for `nbytes_`'s new totality; not sorries, unaffected by this count. |
| `Subtyping.lean` | 46 | **0** | **Fully done** (bundle10) — first fully-complete file. |
| `TypingLemmas.lean` | 81 | **0** | **Fully done** (bundle10) — includes `instr_of`, `ai_principal_typing`, `construct_ais_vals` (the hardest lemma in the source file). Both v2's listed blockers (`instr_of`'s body, the `*_single_typing_inversion` family) are resolved. |
| `TypePreservationPure.lean` | 30 | 11 | Down from 27 (v2) → 20 (bundle11) → 11 (bundle12). 9 genuine targets left + 2 deliberate permanent gaps (`return_frame_preserves`, `t_pure_preservation`, both mirror real Rocq `Admitted`s). See `proof_prioritization_v4.md` for order. |
| `ExtensionLemmas.lean` | 92 | 76 | Still **Tier E, essentially untouched** beyond the `extend_*_refl` reflexivity family (11 lemmas) done in bundles 1-2. `construct_meminsts_grow`'s signature resynced this bundle (no longer permanently blocked — see `rocq_changes_summary_v2.md` §2) but body still `sorry`. Single largest remaining pool of work in the project by lemma count. |
| `TypePreservation.lean` | 13 | 12 | Untouched since v2 (still needs `ExtensionLemmas.lean` substantially done first — ~10 of its 12 `sorry`s are the capstone lemmas that call into `Extend_store_ais`/`construct_*`). 3 of the 12 are deliberate permanent gaps (`store_extension_reduce`, `t_read_preservation`, `t_preservation_type` — all Rocq `Admitted`, all exclusively for SIMD reasons, confirmed still accurate post-resync). |

**Total across the project: 351 declarations, 127 still `sorry`** (down from
v2's ~315/195 — the total-declaration count also grew slightly, mostly from
`to_mathlib_forall₂`/`from_mathlib_forall₂` and other bundle9+ additions
that aren't Rocq ports).

## What's now unblocked and ready (superseding v2's version of this section)

- **`TypePreservationPure.lean` is the highest-leverage remaining track**:
  every one of its 9 genuine remaining targets now has full machinery
  available (`TypingLemmas.lean`/`Subtyping.lean` both done). Ordered in
  `proof_prioritization_v4.md`.
- **`ExtensionLemmas.lean` remains the largest pool (76 `sorry`s) and is
  fully independent of the above** — it depends on `Extend_*`/`Store_ok`
  machinery already available since `TypingLemmas.lean` completed, not on
  anything `TypePreservationPure.lean`-specific. Can run in parallel with
  finishing that file. `construct_meminsts_grow` specifically needs one new
  prerequisite (`Forall₂` length-matching, see `rocq_changes_summary_v2.md`
  §2) not needed by its siblings.
- **`TypePreservation.lean`'s 12 `sorry`s are the last tier**, gated on
  `ExtensionLemmas.lean` being substantially further along — unchanged
  ordering from v2, just further away in absolute terms now that
  `ExtensionLemmas.lean`'s 76 remain essentially where they were.
- `type_progress.v` (not started, out of current scope) — no change from
  v2's assessment; still would need `TypingLemmas`/`Subtyping`/
  `ExtensionLemmas`, not `Preservation`, if ever picked up.

## Dead lemmas (unchanged from v2, reconfirmed)

Same 22-lemma dead cluster in `HelperLemmas.lean` as v2 documented
(`leadd`, `list_update_func_split*`, `length_app_lt`, `Forall_nth'`,
`Forall2_nth`/`_lookup`, `lookup_list_update_func`, `In2_split`,
`Forall2_forall2*` ×5, `Forall2_list_update*` ×5, `add_false`,
`concat_cancel_last_n`, `ltsize`) — reconfirmed still unreferenced by any
currently-live signature via grep this bundle. Not touched by the resync.

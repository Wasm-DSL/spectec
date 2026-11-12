# Proof dependencies — consolidated update (bundle15)

Written for: a future Claude session (primary audience). Supersedes
`bundle13/user_requested_documents/proof_dependencies_v3.md` as the
reference to read going forward (kept, untouched, as historical record).
v3's dependency *shape* is still accurate; this is a refresh because this
bundle's work (26 `sorry`s closed) and — more importantly — the first-ever
detailed triage of `ExtensionLemmas.lean` changed the picture materially
for that file specifically.

## File-level dependency graph (unchanged in shape since bundle3)

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
                                                             not started, out of
                                                             current scope)
```

## Within-file status, ground truth as of bundle15 (direct grep, 2026-10-01)

| File | Total decls | Still `sorry` | Status |
|---|---:|---:|---|
| `HelperLemmas.lean` | 63 | 15 | Down from 27 (bundle13) → 15 this bundle. All 15 remaining are the dead `nat→N`-refactor cluster (unreferenced anywhere downstream, confirmed again). Not blocking anything. |
| `Subtyping.lean` | 46 | 0 | Fully done since bundle10. |
| `TypingLemmas.lean` | 81 | 0 | Fully done since bundle10 (bundle13's signature audit found and fixed 3 real bugs in it without reopening any sorries). |
| `TypePreservationPure.lean` | 30 | 10 | Unchanged this bundle — rechecked all 8 genuine remaining targets for triviality (none qualified), confirmed this file has nothing left for a pass-A sweep. 8 genuine + 2 deliberate permanent gaps (`return_frame_preserves`, `t_pure_preservation`). |
| `ExtensionLemmas.lean` | 92 | 50 | **The big one.** Was 76 at the start of bundle15 (only the `extend_*_refl` reflexivity family — 11 lemmas — done before this bundle). Now 50, i.e. 26 fixed in one pass-A sweep. First-ever full difficulty triage done this bundle — see `extension_lemmas_triage_v1.md` for the complete per-lemma breakdown; still the single largest remaining pool of work in the project by a wide margin. |
| `TypePreservation.lean` | 13 | 8 | Down from 12 → 8 this bundle (`zero_is_well_formed`, `num_default_is_well_formed`, both `inst_t_context_*_empty`). 5 genuine + 3 deliberate permanent gaps (`store_extension_reduce`, `t_read_preservation`, `t_preservation_type` — all three SIMD-only Rocq `Admitted`s). |

**Total across the project: 313 declarations, 83 still `sorry`** (down from
bundle13's 350/125 — bundle13 itself didn't move the sorry count much since
its focus was resync/audit fixes to *signatures*, not new proofs; bundle15
is the first bundle to meaningfully move the raw count down).

## `ExtensionLemmas.lean`'s internal structure (new this bundle)

Per the triage report, the file's 50 remaining `sorry`s break down as:
- **16 Trivial** remaining (was 25 at triage time; 9 done this bundle —
  wait, see note below) — the 10 that were "gated on an Easy sibling" per
  the triage are now mostly unblocked since several siblings landed.
- **23 Easy** remaining (was 27; 4 done this bundle via "Template A").
- **17 Moderate** (untouched this bundle — gated on either "Template B",
  the `Forall₂`/list-index position-correlation bridge needed by the whole
  `construct_*` family, or "Template C", the missing `Externaddr_ok`
  chain-peel infrastructure).
- **7 Hard** (untouched — `Val_ok_store`/`funcinst_same` need a signature
  rethink before any proof attempt makes sense; `Extend_store_ais` needs
  new mutual-induction infrastructure; `addrs_tables_extension`/
  `addrs_mems_extension`/`construct_tableinsts_grow`/`construct_meminsts_grow`
  are each individually long/intricate even with every prerequisite in
  place).

(Exact count reconciliation: the triage's original 25/27/17/7 totals 76;
this bundle closed 9 Trivial-tier and 4 Easy-tier for 13 Moderate-and-above
stay untouched at 17+7=24, Trivial+Easy remaining = 76-13-24=39, split
16 Trivial/23 Easy per above — these are estimates based on which named
lemmas were closed, not a re-run of the triage; treat as approximate until
someone re-triages or the next pass-A sweep naturally confirms them by
attempting each.)

## What's now unblocked and ready (superseding v3's version of this section)

- **`ExtensionLemmas.lean`'s remaining Trivial/Easy tier is still the
  highest-leverage pass-A target** — see `proof_prioritization_v5.md` for
  the specific next items and the two infrastructure investments
  (Template B, Template C) that would unblock the largest further chunks.
- **`TypePreservationPure.lean`'s 8 genuine targets are now confirmed
  pass-B-only** (none are trivial — rechecked this bundle). Unchanged
  ordering from `proof_prioritization_v4.md`: `return_label` → `br_zero` →
  `select` cluster → `br_succ` → `br_table_lt`/`_ge`.
- **`TypePreservation.lean`'s remaining 5 genuine targets** are still
  gated on `ExtensionLemmas.lean` being substantially further along (most
  directly call into `Extend_store_ais`/`construct_*`, both still deep in
  Moderate/Hard territory) — unchanged from v3's assessment.
- `type_progress.v` (not started, out of current scope) — unchanged.

## 3 lemmas flagged this bundle, not yet resolved

`minst_invert_elems`, `store_none_mem_extension`, `table_grow_table_extension`
— all hit `obtain`/`cases`-on-dependent-structure elaboration friction past
reasonable effort within this bundle, per explicit user instruction to skip
and flag rather than keep fighting. Each has an in-file doc comment at the
exact point it got stuck. `table_set_table_extension`'s equivalent issue
*was* resolved (switching `obtain` to `cases ... with` fixed it
immediately) — worth trying that exact substitution first on the other two
before anything more invasive. See `NOTES.md`'s bundle15 entry for the
full tactic-idiom writeup.

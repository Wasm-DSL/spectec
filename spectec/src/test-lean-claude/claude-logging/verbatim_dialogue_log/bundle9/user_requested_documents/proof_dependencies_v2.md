# Proof dependencies — consolidated update (bundle9)

Written for: a future Claude session (primary audience). Supersedes
`bundle2/user_requested_documents/proof_dependencies.md` +
`bundle3/updated_documents/proof_dependencies_addendum.md` as the
reference to read going forward (those are kept, untouched, as historical
record — do not edit them). This is a consolidation, not just another
addendum, because two rounds of addenda on top of a stale original was
starting to cost more reading effort than a fresh, accurate statement.

The Rocq checkout is now **current** (`58af2e2f9`, verified live via `gh
api`/`curl` this bundle — see `rocq_changes_summary.md`), so unlike
`proof_dependencies.md`'s original staleness caveat, this document is not
scoped to a stale snapshot.

## File-level dependency graph (unchanged in shape since bundle3, now confirmed current)

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
                                                             not started — Tier I)
```

`HelperLemmas` depends only on `wasm2.0.lean`. `Subtyping` depends on
`HelperLemmas`. `TypingLemmas` depends on both. `TypePreservationPure` and
`ExtensionLemmas` both depend on `TypingLemmas` (and transitively the
above); `TypePreservation` depends on both of those.  `TypeProgress` (not
started) depends on `HelperLemmas`/`Subtyping`/`TypingLemmas`/
`ExtensionLemmas` but *not* on either Preservation file — confirmed twice
now (bundle3's dependency read of `type_progress.v`'s own `Require Import`
list, and this bundle's diff showing `type_progress.v`'s only changes this
round were internal, not a new dependency).

## Within-file status, as of this bundle (ground truth: direct `sorry` grep, 2026-09-30)

This replaces the tier-by-tier "already proved" callouts scattered across
bundle2/3's documents with one authoritative snapshot. counts are
declarations still containing `sorry` (some are dead lemmas no longer in
current Rocq — see notes).

| File | Total decls | Still `sorry` | Notably DONE this round (bundles 5-9) |
|---|---:|---:|---|
| `HelperLemmas.lean` | ~53 | 29 | tier-0 cluster (18, bundle5); `to_mathlib_forall₂`/`from_mathlib_forall₂` (2 new, bundle9, not a Rocq port) |
| `Subtyping.lean` | ~45 | 32 | `instr_subtyping_strengthen2` (bundle5) |
| `TypingLemmas.lean` | ~90 | 13 | huge round: `inst_match` cluster (6, bundle5); wellformedness-projection (4+2 helpers, bundle5); context-update (7, bundle6); `*_seq_typing_inversion`/`ais_composition_typing` (bundle6); 15-lemma easy-Tier-B batch (bundle7); **`ai_principal_typing`, `instr_typing_inversion`, `ai_typing_inversion`, `principal_typing_conversion`, `injective_admininstr_instr`** (bundle8, ported+fixed from `spectec/test-lean/typing_lemmas.lean`); `Vals_ok` redefinition + `Vals_ok_non_bot` (bundle9) |
| `TypePreservationPure.lean` | ~29 | 27 | none yet — **still fully open**, Tier E |
| `ExtensionLemmas.lean` | ~85 | 79 | reflexivity family (Tier A, bundle1-2); `Extend_store_refl` |
| `TypePreservation.lean` | ~13 | 12 | none yet — **still fully open**, Tier G |

**Key structural change since bundle3's addendum**: `ai_principal_typing`
and its two direct dependents (`instr_typing_inversion`, `ai_typing_inversion`)
— previously "Tier C/D, the single highest-leverage blocker" — are now
**done**. This unblocks a large fraction of what was previously gated. The
new bottleneck is `instr_of`'s own body (`TypingLemmas.lean:105`, still
`sorry` — a plain `def`, not proved via `ai_principal_typing`'s route, so
porting the latter did not automatically resolve the former).

## What `instr_of` (still open) blocks

Grepped every reference to `instr_of` in `TypingLemmas.lean`:
- `construct_ai_maybe` (line 1202) — directly needs `instr_of ai ≠ none` as a
  hypothesis premise.
- Nothing else in the currently-stated signatures references it directly,
  but per `typing_lemmas.v`'s own structure `instr_of` is also implicitly
  what several `Step_pure__*`/`Step_read__*` reduction-rule case proofs in
  `TypePreservationPure.lean`/`TypePreservation.lean` need (to go from "an
  administrative instruction reduced" to "the corresponding static
  instruction was well-typed") — not yet directly referenced in our stubs
  since those proof *bodies* haven't been written yet, but expect it to
  come up repeatedly once Tier E starts.

## What's now unblocked and ready (no remaining blocker other than effort)

- `TypingLemmas.lean`'s remaining 13 `sorry`s split into: (a) `instr_of`
  itself (mechanical transcription, no dependency), (b) the
  `*_single_typing_inversion` family (lines 676-708, needs `ai_typing_inversion`
  — now available) and `ai_val_principal_typing_inversion` (needs `Vals_ok_non_bot`
  — now available, bundle9), (c) `construct_ai_maybe`/`ais_vals_typing_inversion`/
  `construct_ais_vals`/`construct_ais_vals'` (needs `instr_of`'s body first).
- **All 28 `TypePreservationPure.lean` lemmas are now unblocked** (they all
  ultimately need `ai_typing_inversion`/`ai_val_principal_typing_inversion`-style
  facts, which are now provable modulo (b) above) — this is the single
  largest block of ready work in the project by lemma count.
- `ExtensionLemmas.lean`'s remaining 79 `sorry`s are mostly independent of
  the `TypingLemmas.lean` blockers (they depend on `Extend_*`/`Store_ok`
  machinery, not typing-inversion) — genuinely parallel track, unblocked
  the whole time, just not yet worked through in bundle order.
- `TypePreservation.lean`'s 12 `sorry`s need both of the above (Tier E done,
  most of `ExtensionLemmas.lean` done) — still the last tier, unchanged.
- `type_progress.v` (Tier I, not started) needs `TypingLemmas`/`Subtyping`/
  `ExtensionLemmas` — with `ai_principal_typing` now ported, this tier is
  more ready to start than the original prioritization assumed, though
  still deliberately sequenced after Preservation per the original
  author's own apparent priority (see `rocq_proof_intuition.md`).

## Dead lemmas (no longer worth tracking as blocking anything)

Per bundle3's resync notes, `helper_lemmas.v` upstream removed ~24 lemmas
our Phase-1 skeleton had already stubbed. These remain `sorry` in
`HelperLemmas.lean` (`leadd`, `list_update_func_split`/`_strong`,
`length_app_lt`, `Forall_nth'`, `Forall2_nth`/`_lookup`,
`lookup_list_update_func`, `In2_split`, `Forall2_forall2*` (5 variants),
`Forall2_list_update*` (5 variants), `add_false`, `concat_cancel_last_n`,
`ltsize`) — 22 of `HelperLemmas.lean`'s 29 remaining `sorry`s are this dead
cluster. **Not blocking anything downstream** (nothing in the currently-live
lemma set calls them — confirmed by grep). Safe to leave indefinitely;
would only need attention if some future lemma turns out to need one as a
building block, at which point `to_mathlib_forall₂` (bundle9) makes several
of them cheap.

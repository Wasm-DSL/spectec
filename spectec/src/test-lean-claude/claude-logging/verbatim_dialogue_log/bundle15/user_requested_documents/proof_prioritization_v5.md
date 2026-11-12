# Proof prioritization — update v5 (bundle15)

Written for: a future Claude session (primary audience) and the user.
Supersedes `bundle13/user_requested_documents/proof_prioritization_v4.md`
as the document to read for "what's next, across the whole project" — v4
only ever covered `TypePreservationPure.lean`'s ordering (still accurate,
restated at the bottom), not the full picture. This is the first
prioritization doc to give a true whole-project view, now that
`ExtensionLemmas.lean` — the largest file by a wide margin — has an actual
difficulty triage behind it (`extension_lemmas_triage_v1.md`, this bundle)
instead of being an unexamined wall of 76 `sorry`s.

## Direct answer to "is the old doc the whole remaining-work picture?"

No. As of bundle15: **83 `sorry`s remain project-wide**, split
`ExtensionLemmas.lean` 50, `TypePreservationPure.lean` 10,
`TypePreservation.lean` 8, `HelperLemmas.lean` 15 (dead, optional).
`ExtensionLemmas.lean` alone is larger than the other three combined.

## Recommended order, pass-A style (trivial/easy first)

1. **Keep working `ExtensionLemmas.lean`'s Easy tier directly reachable
   without new infrastructure** — per `extension_lemmas_triage_v1.md` plus
   this bundle's actual results:
   - `Extend_store_ref` (Easy — 3-case `Ref_ok` inversion; needs
     `Extend_store_externaddrs_func`, below) then its one-line cascade
     `Extend_store_refs`/`Extend_store_refs'`/`Extend_store_val`/
     `Extend_store_vals`.
   - `Extend_store_eleminst` (Easy) → `Extend_store_eleminsts`,
     `Extend_store_eleminsts'` (needs `se_invert_elems`, already proved).
   - `Extend_store_tableinst`/`Extend_store_globalinst` (Easy, same
     `Extend_store_val`/`Extend_store_ref`-style shape) → their plural
     cascades.
   - `Extend_store_datainsts'` (Easy, `Datainst_ok` is content-independent
     so this is lighter than it looks).
2. **Build "Template C" next** (port Rocq's `Externaddr_invert_funcs`/
   `_tables`/`_mems`/`_globals` — `extension_lemmas.v:1065-1159` — as new
   standalone lemmas; **no Lean counterpart exists at all yet**, confirmed
   by grep). The triage report's assessment: this single piece of new
   infrastructure is what turns `addrs_tables_extension`/
   `addrs_mems_extension` from Hard back to Moderate, and
   `minst_invert_funcs`/`_tables`/`_globals`/`_mems` plus
   `addrs_store_funcs_extension`/`addrs_store_globals_extension` (9
   lemmas total) from Moderate down to Easy. Highest-leverage single
   investment left in the file.
3. **Then the `addrs_*`/`addrss_*` family** (8 lemmas, now Easy-or-better
   with Template C in place) → **`Extend_store_exts`** → **`Extend_store_moduleinst`**
   ("the key assembly lemma", per its own doc comment — everything else in
   this group feeds it) → `Extend_store_funcinst`/`_funcinsts`.
4. **"Template B"** (the `Forall₂`-position-correlation bridge the whole
   `construct_*` family needs — port `HelperLemmas.Forall2_nth`, itself
   still `sorry` but tractable via the zip-based `Forall₂` def directly)
   unblocks `construct_tableinsts`/`construct_globalinsts`/
   `construct_meminsts`/`construct_datainsts`/`construct_eleminsts` (5
   lemmas, Moderate) in one move — do this once, not per-lemma.
5. **3 flagged-and-reverted lemmas** (`minst_invert_elems`,
   `store_none_mem_extension`, `table_grow_table_extension`) — retry each
   with the `cases h with | Ctor ... => ...` idiom (not `obtain`) now
   established as more reliable for this codebase's dependent-index
   inversions; `table_set_table_extension`'s identical-shaped issue
   resolved immediately with exactly this substitution.
6. **Last in `ExtensionLemmas.lean`**: the genuinely Hard 7
   (`Val_ok_store`/`funcinst_same` need a signature discussion first —
   both flagged in-file as possibly unprovable as currently stated;
   `Extend_store_ais`, the big mutual-induction theorem; the two
   `_grow`-suffixed `construct_*` lemmas; `addrs_tables_extension`/
   `addrs_mems_extension` if Template C doesn't fully flatten them).
7. **`TypePreservationPure.lean`'s 8 genuine targets** — unchanged from
   `proof_prioritization_v4.md`, all confirmed non-trivial this bundle:
   `return_label_preserves` → `br_zero_preserves` → `select` cluster →
   `br_succ_preserves` → `br_table_lt_preserves`/`_ge_preserves`. This is
   pass-B material whenever the user wants it — nothing here is a pass-A
   candidate.
8. **`TypePreservation.lean`'s 5 genuine targets** — last, as always;
   needs `ExtensionLemmas.lean` (specifically `Extend_store_ais`,
   `Extend_store_moduleinst`) substantially further along first.

## What a future pass A should actually execute, concretely

If resuming with another pass-A request, the single best next move is
**item 1 above** (the `Extend_store_ref`/`_eleminst`/`_tableinst`/
`_globalinst` cascades) — no new infrastructure needed, same proof shape
as lemmas already done this bundle (`extend_X_refl_0`-reuse for the
untouched case, direct constructor application for the changed one), and
unblocks ~10 lemmas for the cost of really only 4-5 genuinely new proofs
(the cascades are one-liners once their base case lands).

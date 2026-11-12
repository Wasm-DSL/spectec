# Proof prioritization — update v4 (bundle13)

**Status update, same bundle**: item 1 of v3's queue, `frame_vals_preserves`,
was proved for real later in this same bundle (while waiting on the
signature-audit background task) — confirmed structurally identical to
`label_vals_preserves` as predicted. `return_label_preserves` (item 2) was
read but deliberately deferred after finding Rocq's proof genuinely more
involved than `frame_vals`/`label_vals` (needs `RETURN`'s principal typing
reconciled against `v_C.RETURN` via `resulttype_sub_app`-style reasoning,
not just a context-crossing trick) — correctly next in queue, not stuck.
See `NOTES.md`'s bundle13 entry for detail. Order below (`return_label` →
`br_zero` → `select` → `br_succ` → `br_table_lt`/`_ge`) otherwise unchanged.

Written for: a future Claude session (primary audience). Supersedes
`bundle12/user_requested_documents/proof_prioritization_v3.md` only where
noted below (the resync's effect on prioritization) — v3's own ordering of
`TypePreservationPure.lean`'s 9 remaining targets (`frame_vals` →
`return_label` → `br_zero` → `select` cluster → `br_succ` →
`br_table_lt`/`_ge`) is **unaffected by the `rocq-backend-proof-final`
resync** (confirmed: none of those lemmas' Rocq counterparts changed in the
merge — see `rocq_changes_summary_v2.md` §1) and is **not** revised here.
Read v3 for that ordering; this document only layers on what changed.

## What the resync changes about priorities

1. **`construct_meminsts_grow` (`ExtensionLemmas.lean`) moves from
   "permanently blocked, don't bother" to "genuine target, but not
   low-hanging fruit."** Previously excluded entirely from any tier (v2's
   Tier F/`ExtensionLemmas.lean` discussion didn't single it out beyond
   "gained `wf_*` premises"; the in-file comment said outright "Still
   `Admitted` ... the sole remaining Preservation-side gap"). Now that
   Rocq's own version is `Qed`'d, it's promotable — **but it has a real
   prerequisite** (establishing `s.MEMS.length = ts.length`-style reasoning
   for this codebase's zip-based `Forall₂`, the same class of gap solved
   for `Vals_ok` in bundle9) that none of `ExtensionLemmas.lean`'s other
   `sorry`s need in the same way. Recommendation: **don't front-load it**
   just because it's newly unblocked — treat it as roughly comparable in
   difficulty to `TypePreservationPure.lean`'s `br_succ_preserves` (v3's
   hardest-ranked item), not as easy filler.
2. **Nothing else in the resync changes any existing priority ranking** —
   confirmed via `rocq_changes_summary_v2.md`'s file-by-file pass: the SIMD
   restructuring doesn't touch anything in scope, the `axioms.v` additions
   are `type_progress.v`-only (out of scope), `Datainst_ok`/`Eleminst_ok`'s
   new bound doesn't require a signature change to any `sorry`'d
   `ExtensionLemmas.lean` lemma (just adds proof-body work once someone gets
   there — noted for whoever picks up `construct_datainsts`/
   `construct_eleminsts` eventually, not a reprioritization).

## Suggested order, this bundle onward

Given `TypePreservationPure.lean` is close to done (11 `sorry`s, 9 genuine)
and `ExtensionLemmas.lean` is the large untouched pool (76 `sorry`s, only
the `extend_*_refl` reflexivity family done), and both are now fully
unblocked by `TypingLemmas.lean`/`Subtyping.lean` being complete:

1. **Finish `TypePreservationPure.lean`'s 9 remaining genuine targets**
   per v3's order — closest to done, highest leverage per lemma, and
   momentum/pattern-familiarity from bundles 11-12 is fresh. Do this before
   opening up `ExtensionLemmas.lean` in earnest.
2. **Then start `ExtensionLemmas.lean` in earnest** (currently only the
   Tier A reflexivity cluster is done). This is genuinely a fresh area —
   unlike `TypePreservationPure.lean`, no prior bundle has established
   reusable proof shapes for this file's `Extend_store_*`/`construct_*`
   lemma families yet. Suggest starting with the simplest-looking
   `Extend_store_*` monotonicity lemmas (structurally similar to each
   other — `Extend_store_eleminst`, `Extend_store_datainsts'`, etc. — Rocq's
   own proofs for these are short, ~10-20 lines each per the diffs read
   this bundle) before attempting `Extend_store_ais` (explicitly flagged
   in-file as "THE big monotonicity theorem," proved in Rocq via a custom
   mutual induction scheme) or `construct_meminsts_grow` (needs the new
   `Forall₂`-length prerequisite from item 1 above).
3. **`construct_meminsts_grow`**: attempt once the `Forall₂`-length
   prerequisite exists (either build it specifically for this lemma, or
   check whether `ExtensionLemmas.lean`'s other `construct_*_grow`/list-
   update lemmas end up needing the same thing — if so, worth generalizing
   once rather than per-lemma).
4. **`TypePreservation.lean`'s 12 `sorry`s** — unchanged from v2/v3,
   correctly last, needs `ExtensionLemmas.lean` substantially further along
   first. 3 of the 12 are deliberate permanent gaps, unaffected.

## Signature-audit findings (fold in here once available)

The bundle13 signature audit (`signature_audit_v1.md`, background task) may
surface additional small signature fixes beyond `construct_meminsts_grow`.
Any genuine target whose *signature* the audit had to correct should be
treated as having its difficulty re-baselined from scratch (a signature fix
can make a previously-"easy"-looking lemma harder, or vice versa, the same
way `construct_meminsts_grow` did) rather than assumed to slot into
whatever tier it was in before the audit. If this document's own bundle
closes before the audit's fixes are triaged, a `v5` update should record
what actually happened, per the project's "leave it be and reassess in your
new bundle" convention for anything that turns out harder than expected.

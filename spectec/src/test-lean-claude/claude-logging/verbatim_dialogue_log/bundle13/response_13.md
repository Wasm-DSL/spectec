## Resynced onto `rocq-backend-proof-final`

**One real build break, found and fixed.** The merge's regenerated
`wasm2.0.lean` made `nbytes_`/`ibytes_`/`fbytes_`/`vbytes_` total (`List
byte`, no longer `Option (List byte)`) — traced to `853b8863c` ("Made wfopt
be an optin hint for functions"). Three `HelperLemmas.lean` axioms
(`nbytes_len`, `nbytes_len'`, `nbytes_inv`) were written against the old
partial signature and broke — `lake build` had 5 real errors before the
fix, 0 after. Since `Subtyping.lean`/`TypingLemmas.lean` are fully `Qed`'d
(not just `sorry`'d), the now-clean build is strong evidence nothing else
broke.

**`construct_meminsts_grow` is no longer permanently blocked.** Rocq's
version went from `Admitted` (a missing `lim_old + v_n ≤ 2^16` bound) to
fully `Qed`'d, because `$growmemory` gained that bound as a premise
upstream — traced it through `Memtype_ok`/`Limits_ok` in the regenerated
file to confirm exactly why it's needed. Added the matching hypothesis to
the Lean signature; left the body `sorry` (needs a `Forall₂`-length
prerequisite this codebase doesn't have yet, same class of gap as
`Vals_ok`). Also spotted and flagged (pre-existing, unrelated to this
merge): the signature hard-codes the memory max as always-present where
Rocq's is a genuine `Option`.

**Everything else checked and needed no change**: the merge is ~95% a SIMD
restructuring (`vloadop`/`vextunop_`/`vextbinop_`/`vcvtop` all reshaped) —
confirmed via grep this project's Lean files reference zero SIMD names, by
design (stated in-file). 9 new Rocq axioms are all `type_progress.v`-only
(no Lean port exists). `Datainst_ok`/`Eleminst_ok`'s new `< 2^32` bound is
auto-inherited through the regenerated `inductive`s with no textual
signature change needed anywhere.

**Regeneration double-check, done properly**: found the actual Lean-backend
CLI invocation and ran it independently against the merged spec sources,
output to a scratch file. Diffed against the committed `wasm2.0.lean`:
**zero lines of difference, byte-for-byte identical** (14760 lines both).
Stronger than spot-checking — this confirms the manual regeneration exactly
reproduces what the toolchain itself produces.

**Systematic signature audit**: dispatched as a background task per your
request, comparing every Lean signature in all 6 files against its named
Rocq counterpart. It's still running as I write this (large task, ~350
declarations) — I'll report findings and fix anything it surfaces as soon
as it lands, rather than guess at its output now.

New docs, all in `bundle13/user_requested_documents/`: `rocq_changes_summary_v2.md`
(full detail on everything above), `proof_dependencies_v3.md` (refreshes
bundle9's now badly-stale status table), `proof_prioritization_v4.md`
(layers the resync's effect onto bundle12's ordering, otherwise unchanged),
and `signature_audit_v1.md` (once the background task finishes writing it).

While waiting on the audit, also proved `Step_pure__frame_vals_preserves`
(first item in the queue) — confirmed structurally identical to
`label_vals_preserves` as predicted, modulo one extra `Expr_ok2` inversion.
Read `return_label_preserves` next and found it genuinely more involved
(needs `RETURN`'s principal typing reconciled against `v_C.RETURN`), so
left it correctly queued rather than rushing it.

`lake build` clean throughout (0 errors). Safety check clean — confirmed
nothing touched outside `spectec/src/test-lean-claude/` this bundle.

Current tally: `Subtyping.lean` 0, `TypingLemmas.lean` 0,
`TypePreservationPure.lean` **10** (down from 11), `ExtensionLemmas.lean`
76, `TypePreservation.lean` 12, `HelperLemmas.lean` 28 (dead cluster).

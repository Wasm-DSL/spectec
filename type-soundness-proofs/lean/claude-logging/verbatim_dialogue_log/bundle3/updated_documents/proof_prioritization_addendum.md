# Addendum to `bundle2/user_requested_documents/proof_prioritization.md`

Do not edit that file. This records tier-by-tier deltas from the 2026-09-23
resync (see `resync_impact_report.md` for full evidence). Read it alongside
the original, not instead of it — most tiers are unaffected.

## Tier A (already done) — unaffected in substance, stale in name

The 13 `Subtyping.lean` lemmas are fine (subtyping.v only grew additively).
The `ExtensionLemmas.lean` reflexivity-family lemmas (`func_extension_refl0`
etc.) are proved facts that still hold, but every Rocq name they cite has
been renamed upstream (see `resync_impact_report.md` §3b's mapping table).
**Action**: a rename pass over `ExtensionLemmas.lean`'s existing lemma names
(not their proofs) is warranted before adding more to this file, so new work
doesn't compound on top of stale names. Low cost, not urgent, but do it
before Tier F work resumes.

## Tier B — mostly fine, two corrections

- **#2 (`HelperLemmas.lean` tier-0 cluster)**: `leadd`, `length_app_lt`,
  `add_false` are among the 24 lemmas removed from upstream `helper_lemmas.v`
  entirely (full list in `resync_impact_report.md` §3e). Drop these from the
  target list — there's no longer a Rocq lemma to be faithful *to*. The rest
  of the cluster (`length_same_split_zero`, `length_app_both_nil`,
  `length_app_nil`, `split_append_*`, `empty_append`, `sizecat_le1`/`_le2`,
  `drop_size_cat`/`take_size_cat`, `add_sub`/`add_sub'`,
  `option_orElse_*`) is unaffected — still real, still cheap, still worth
  doing first.
- **#7/#8 (`ExtensionLemmas.lean` inversion lemmas / per-instruction
  extension facts)**: same stale-name issue as Tier A — `Val_ok_store` was
  removed with no obvious direct replacement (check how the new
  `Extend_store_val`/`_vals` proofs get this fact instead), `funcinst_same`
  was also removed (possibly meaning the representational gap Tier F #22
  flagged has been resolved a different way upstream — worth reading the new
  `Extend_store_funcinst`/`_ref` proofs before re-deriving our own fix).

Everything else in Tier B (`TypingLemmas.lean` items #3–#10) is unaffected —
none of those lemma names were touched by the resync.

## Tier C, D — unaffected

`instr_of`, `ai_principal_typing`, `instr_typing_inversion`,
`ai_typing_inversion`, and the rest of Tier D's lemmas were not renamed,
removed, or otherwise changed by the resync (the `typing_lemmas.v` changes
were limited to removing the `fun_*idx__nat` conversion family and adding a
handful of `construct_instr_from_ai*`/`revert_to_*` lemmas — check whether
any Tier C/D lemma signature referenced the removed `fun_*idx` family before
starting; if so it needs re-deriving against `wasm2.0.lean`'s current index
handling instead). No tier reordering needed here.

## Tier E — reframed, not just corrected

Item #17's list of 28 `Step_pure__*_preserves` lemmas is still the right set
to work through for the **non-vector** cases. But per
`resync_impact_report.md` §3a, there are now ~20 additional
`Step_pure__v*_preserves` lemmas (one per vector-instruction family) that are
**fully proved upstream** and were not in scope before (previously believed
permanently gapped). This is new, real, tractable work — propose treating it
as a new **Tier E2**, done after Tier E's existing 28 (so the non-vector
"spine" of the file closes first, matching the original author's own
apparent priority — vector cases were the *last* thing closed, per the
commit message), consisting of: porting each `ais_v*_typing_inversion` +
`Step_pure__v*_preserves` pair, then updating `t_pure_preservation`'s master
dispatch to cover these cases for real instead of `sorry`. Item #19
(`t_pure_preservation`) should move to *after* Tier E2, not before it — the
master theorem can only stop being "minus SIMD cases" once Tier E2 is done.

## Tier F — several items need the Tier A/B rename fix first, plus one new item

- #20 (`limits_sub`/`externtype_sub` cluster): **better than before** — these
  now have real Rocq statements (`limits_sub_refl`/`_trans`,
  `externtype_sub_refl`/`_trans`, `externtype_func_eq`/`_global_eq`) to port
  against directly, rather than relying solely on a prior Lean session's
  reuse-only proofs. Do this first within the tier, same priority as before,
  just on firmer ground.
- #21–#26: unaffected in *shape*, but every `store_extension_*` name in their
  descriptions is now `Extend_store_*` — see the Tier A rename-pass note.
  Do the rename pass before resuming this tier.
- #27 (`construct_meminsts_grow`): **still the single remaining Preservation-
  side gap upstream**, exactly as described — but new supporting lemmas
  (`pagediv`, `pagediv_ge_0`/`_Z`, `update_holds_upto_le`/`_lt`,
  `holds_upto_*`, `Qfloor_add_Z`) were added alongside it, apparently the
  author's own partial progress toward closing it. Worth a genuinely fresh
  attempt using these, higher expected payoff than before.

## Tier G — unaffected

None of `TypePreservation.lean`'s existing Tier G items (#28–35) were touched
by renames or removals. `t_preservation`'s SIMD-case caveat (in #34) should
be read the same way as the Tier E correction above — those cases are now
real closeable work, not a permanent gap, once Tier E2 exists.

## Tier H — #36 done, #37 unblocked with a real plan available

- **#36 (re-sync) is done** — verified in `resync_impact_report.md` §1.
- **#37 (port `type_progress.v`)** is unblocked: the file exists, has been
  digested (`claude-logging/for-claude/digest_type_progress.md`), and its
  dependency scope is now known precisely (needs only `HelperLemmas`,
  `Subtyping`, `TypingLemmas`, `ExtensionLemmas` — **not** either
  Preservation file, see `proof_dependencies_addendum.md`). Proposing this as
  a new **Tier I**, sequenced by the digest's own suggested internal order
  (list/admin-instr plumbing → `typeof`/`invert_typeof_*` → numeric-operator
  totality → br/return machinery → `call_indirect_progress` →
  `t_progress_be` [skip/`sorry` the 5 SIMD sites] → `t_progress_e` →
  `t_progress`), startable in parallel with Tier E/F/G work once the Tier
  A/B rename pass and Tier C/D (which Progress's layer-1/2 lemmas partially
  overlap/reuse) are in reasonable shape — not gated on finishing
  Preservation first.

## Suggested revised top-level ordering (supersedes nothing, just sequences the deltas above)

1. Tier A/B rename pass over `ExtensionLemmas.lean` (cheap, unblocks clean
   further work in that file).
2. Tier B (corrected list), Tier C, Tier D as originally ordered.
3. Tier E (28 non-vector lemmas) — as originally ordered.
4. **New: Tier E2** (vector `Step_pure__v*_preserves` family) — real work
   that didn't exist as an option before this resync.
5. Tier E's #19 (`t_pure_preservation`, now genuinely gap-free except
   nothing, once E2 lands).
6. Tier F (corrected names), including a fresh attempt at #27
   (`construct_meminsts_grow`) with the new supporting lemmas.
7. Tier G, with #34's "minus SIMD cases" caveat now closeable given Tier E2's
   analogue exists in `TypePreservation.lean` too (the vload/vstore lemmas
   from `resync_impact_report.md` §3a).
8. **New: Tier I** (`type_progress.v` port) — can run in parallel with 3–7
   rather than strictly after, per the corrected dependency graph.

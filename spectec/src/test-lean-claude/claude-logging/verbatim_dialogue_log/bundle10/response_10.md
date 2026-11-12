## Two files fully complete: `Subtyping.lean` and `TypingLemmas.lean` (0 sorries each)

Following your guidance — replicate Rocq's tactics first, diverge only when needed, and step back to understand the whole proof if that fails — I finished the two lemmas left over from bundle9 (`ais_vals_typing_inversion`, `construct_ais_vals`). Getting there required first filling in `Subtyping.lean`'s `instrtype_sub_compose*` family (14 lemmas), which turned out to be the real prerequisite. Net result:

**`Subtyping.lean`: 0 real `sorry`s left** — the first fully-complete lemma file in the project. Ported `Forall2_app'`, `resulttype_sub_app'`, `Forall2_take`/`_drop`, `resulttype_sub_split`, `resulttype_sub_empty`/`_empty_sub`, the full `instrtype_sub_compose`/`_le`/`_ge`/`_eq`/`_le'`/`_ge'`/`1`/`0`/`2` family, `instrtype_sub_cancel_left`, the `instrtype_sub_*empty*` cluster, both `instrtype_sub_iff_resulttype_sub` variants, `instrtype_sub_extend`, `instrtype_sub_add_same`, `resulttype_sub_cons`, plus `valtype_sub_non_bot`/`resulttype_sub_non_bot`/`resulttype_sub_app_trans`.

Reading each Rocq proof in full first (as you suggested) paid off directly: most of the apparent complexity in `compose_le`/`compose_ge` turned out to be ssreflect/mathcomp size-arithmetic bookkeeping that Lean's `omega` absorbs in one line, and Rocq's own `cat_take_drop` gymnastics for splitting a list at a known point turned out to already exist as `resulttype_sub_split_sup`/`_sup'` in this file (proved back in bundle1-2) — using those directly made several proofs shorter than Rocq's own.

**`TypingLemmas.lean`: 0 real `sorry`s left.** `ais_vals_typing_inversion` fell out via ordinary left-induction once the compose family existed. `construct_ais_vals` — the longest, most intricate proof in the whole Rocq file (~125 lines, induction from the *right* via `last_ind`) — I ported with a genuinely different strategy: ordinary left-induction, matching every other proof in this file, instead of replicating Rocq's right-induction. The piece that made Rocq need `last_ind` (splitting a codomain type at exactly the right point via `take`/`drop` and size arithmetic) has a clean left-recursive analogue using `resulttype_sub_split_sup'` directly on the domain's `t :: ts'` shape — well under half of Rocq's line count, no arithmetic bookkeeping needed. Documented the divergence in the lemma's own comment.

### What this unblocks

`TypePreservationPure.lean`'s 27 `Step_pure__*_preserves` lemmas (Tier D) are now **fully** unblocked — every fact they need from `TypingLemmas.lean`/`Subtyping.lean` has a real proof now, not just a signature.

### Current tally

`HelperLemmas.lean` 28 (all dead/no-longer-in-Rocq, per bundle9), `Subtyping.lean` **0**, `TypingLemmas.lean` **0**, `TypePreservationPure.lean` 29, `ExtensionLemmas.lean` 76, `TypePreservation.lean` 12.

`lake build` clean throughout (checked after every lemma), safety check clean — nothing touched outside `test-lean-claude/`.

### Next

Starting on `TypePreservationPure.lean`'s 27 lemmas in Rocq's own file order, per the prioritization doc — this is now the highest-leverage unblocked work. Will flag `Step_pure__return_frame_preserves` for a real attempt (historically `Admitted` in Rocq for a non-mathematical reason, not intrinsic difficulty) rather than deferring it by default. Continuing unless redirected.

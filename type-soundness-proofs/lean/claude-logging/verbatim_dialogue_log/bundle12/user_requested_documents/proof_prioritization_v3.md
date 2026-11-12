# Proof prioritization — update v3 (bundle12)

Written for: a future Claude session (primary audience). Supersedes
`bundle9/.../proof_prioritization_v2.md` as the document to follow for
`TypePreservationPure.lean` specifically (v2's Tiers A–C, E, F, G still
stand unchanged — `Subtyping.lean` and `TypingLemmas.lean` are now fully
done per bundle10, superseding v2's "Tier C/D" framing entirely). Not a
full rewrite of v2, just its Tier D section, corrected against what
bundles 11–12 actually found. v2's originals, and everything before it,
are left untouched per the project's standing "don't edit previous
bundles" rule.

## Why this update: the difficulty estimate for one item was wrong

v2's Tier D said (quoting): "the [`Step_pure__*_preserves` lemmas'] non-vector
'spine'... `select`/`if` (medium)". Having now actually completed `if` and
attempted `select`, this pairing was wrong — they are not comparable
difficulty. `if_preserves_helper` composes two *already-fixed-shape*
principal typings (`CONST`'s domain/codomain is always a single concrete
type; `IFELSE`'s block-typing components come pre-packaged together) and
closes in one `instrtype_sub_compose_le` call. `select_preserves_helper`
requires reconciling *two independently-typed values* against a shared
slot in a third instruction's principal type, which needs an exact
(non-subtyping) equality established via `Val_ok_non_bot`/
`valtype_sub_non_bot` before any composition lemma applies cleanly — a
qualitatively different (and harder) proof shape. Corrected below.

## What actually happened, bundles 11–12 (ground truth, direct count)

`TypePreservationPure.lean` real-`sorry` count: **29 (start of bundle11) →
20 (end of bundle11) → 11 (end of bundle12, this bundle)**.

Done, in the order actually completed (not necessarily v2's predicted
order): `nop`, `drop`, `if_preserves_helper` (+ `if_true`/`if_false`),
`label_vals_preserves`, `br_if_true_preserves`, `br_if_false_preserves`,
`proj_identity`, `unop_val_preserves`, `binop_val_preserves`,
`testop_preserves`, `relop_preserves`, `cvtop_val_preserves`,
`local_tee_preserves`, `ref_is_null_helper` (+ `_true`/`_false`).

**Two more Phase-1 signature bugs found and fixed while doing this work**
(same class as bundle9's `ai_principal_typing` `REF_HOST_ADDR` gap):
`Step_pure__testop_preserves` and `Step_pure__relop_preserves`'s Lean
stubs were both missing the `wf_admininstr (admininstr.CONST numtype.I32
v_c) →` hypothesis that Rocq's actual signature has (needed to derive
`wf_num_` for the freshly-synthesized boolean/comparison result — without
it the lemma is unprovable, since `wf_num_ I32 c` doesn't hold for
arbitrary `c`). Fixed both signatures to match Rocq exactly before proving
them. Flagged in `NOTES.md`; worth a systematic signature audit of the
remaining unproven lemmas at some point, since Phase 1 evidently missed a
few hypotheses here and there when transcribing from the digest rather
than the live Rocq source.

## Remaining items, reordered by *actual* difficulty (not v2's estimate)

**11 real targets left**, 2 of them deliberate permanent gaps (mirroring
`Admitted` in Rocq for non-mathematical reasons, per the file's own header
comment — not reprioritized, just excluded from the ordering below):
`Step_pure__return_frame_preserves`, `t_pure_preservation`.

That leaves **9 genuine targets**:

1. **`Step_pure__frame_vals_preserves`.** Justification: structurally
   almost identical to the already-done `label_vals_preserves` (same
   "use `construct_ais_vals'` to cross a context boundary" trick, just for
   `FRAME_`'s `LOCALS`/`RETURN`-extended context instead of `LABEL_`'s
   `LABELS`-extended one) — should be comparably easy, do it first to
   confirm the pattern generalizes.
2. **`Step_pure__return_label_preserves`.** Justification: per the file's
   own header comment, this is fully proved in Rocq (unlike its
   `_frame_` sibling) and structurally resembles `label_vals_preserves`/
   `br_zero`-adjacent reasoning (RETURN propagating outward through one
   label, unchanged) — likely comparable to items already done, not
   attempted yet only because it was queued after the ref_is_null cluster.
3. **`Step_pure__br_zero_preserves`.** Justification: per v2's original
   note, this one doesn't even need the `Step_pure` reduction hypothesis
   (only the typing fact + a length side-condition) — one fewer moving
   part than `br_succ`/`br_table`. Still genuinely involved (needs
   `lookup_label_0`-style context reasoning per the Rocq proof's own
   `rewrite lookup_label_0`), but a reasonable next step up in difficulty
   from items 1–2.
4. **`select_preserves_helper`** (+ its two corollaries `select_true`/
   `select_false`, free once the helper is done). **Reclassified from
   "medium" to "hard"** — see the analysis above and in bundle11's
   `NOTES.md` entry. The concrete plan noted there (use
   `ais_vals_typing_inversion` on `[val v1, val v2]` as a pair to get a
   single `Vals_ok`-based length-and-Forall₂ fact, rather than inverting
   each value separately and manually reconciling two independent
   subtyping facts) is still the best lead; worth a dedicated attempt now
   that the rest of the file's easier items are done and this is one of
   the few remaining blockers.
5. **`Step_pure__br_succ_preserves`.** Justification: v2 correctly
   flagged this as "longest/most involved, ~80 lines" — nothing in
   bundles 11–12 found reason to revise that downward. Genuinely the
   hardest *typing-inversion-shaped* lemma left (as opposed to `select`,
   which is hard for a *construction*-shaped reason).
6. **`Step_pure__br_table_lt_preserves`** and
   **`Step_pure__br_table_ge_preserves`**. Justification: unchanged from
   v2 — `Forall_nth`-style reasoning over the label list, `~70` lines each
   in Rocq. Do last: both need the same `BR_TABLE` principal-typing
   machinery, and by this point in the file the easier composition idioms
   (`instrtype_sub_compose`/`_le`/`_eq`) will be very familiar from having
   used them ~15 times already.

**Deliberately last, unchanged from v2**: the 2 permanent gaps
(`return_frame_preserves`, `t_pure_preservation`) — attempt
`return_frame_preserves` for real once everything else in this file is
done (per v2's original reasoning: it's `Admitted` in Rocq for a lost-proof
historical reason, not intrinsic difficulty, so this Lean port isn't
bound by whatever made it inconvenient to fix upstream), then
`t_pure_preservation` (pure dispatch, mechanical once all 26 non-SIMD
cases exist for real).

## Other factors (updated)

- **Pattern reuse is now the dominant "ease" signal**, more than raw Rocq
  line count. Every lemma done in bundles 11–12 follows one of two shapes:
  (a) "split via `ais_seq_typing_inversion`, get each piece's principal
  type, recombine via one `instrtype_sub_compose*` call, construct the
  result and widen" (nop/drop/unop/binop/testop/relop/cvtop/ref_is_null),
  or (b) "cross a context boundary via `construct_ais_vals'`"
  (label_vals, and presumably frame_vals). `select` and `br_succ`/
  `br_table_*` don't fit either shape cleanly, which is *why* they're
  harder, not just longer.
- **The `subst`-direction gotcha from bundle11's `NOTES.md` entry recurred
  zero times in bundle12** after adopting the "use `rw` on the goal
  instead of `subst` when both sides of an equation are free local
  variables" fix pattern consistently from the start — worth keeping as
  the default habit going forward, not just a fix-when-it-breaks reflex.

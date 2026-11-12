# Digest: `type_progress.v` (new as of the 2026-09-23 resync)

Written by the session that performed the resync (see `NOTES.md`'s
2026-09-23-later update and
`verbatim_dialogue_log/bundle3/updated_documents/resync_impact_report.md`).
This file did not exist in the local checkout before the resync — the closest
prior artifact was a 3131-line staging draft at
`spectec/test-rocq/folder-to-exclude/type_progress.v` as of the old commit
(`5b03ae067`); the live/current file (`a8b585cdb`) is 4260 lines and lives in
`theories/` proper, i.e. it has graduated out of staging.

Read directly at `spectec/test-rocq/theories/type_progress.v`. This digest is
a structural map, not a line-by-line transcription — go to the source for
exact statements when porting.

## What this file is

The **Progress** half of type safety (Preservation is `type_preservation.v`/
`type_preservation_pure.v`, already ported). Progress says: a well-typed,
non-trivial configuration can always take a step (it's not "stuck" unless
it's already a value or trap). This is proved by structural analysis on the
instruction sequence — the classic "canonical forms" style proof.

## Dependency fact (corrects a guess in `proof_prioritization.md` Tier H #37)

Imports: `wasm`, `helper_lemmas`, `helper_tactics`, `typing_lemmas`,
`extension_lemmas`, `subtyping`, `axioms`. **Does NOT import
`type_preservation` or `type_preservation_pure`.** Progress and Preservation
are independent consumers of the same shared infrastructure
(helper/subtyping/typing/extension/axioms), not a chain — `proof_prioritization.md`
had guessed Progress would need "everything `type_preservation.v` needs, plus
its own machinery," which overstates the coupling. Practically: once
`HelperLemmas.lean`/`Subtyping.lean`/`TypingLemmas.lean`/`ExtensionLemmas.lean`
are solid, Progress and Preservation can be worked on in parallel by
independent efforts (or interleaved arbitrarily), not strictly Preservation-
then-Progress.

## Structure (108 top-level Lemma/Theorem declarations, 1 Fixpoint, 10 Definitions)

Roughly five layers, in file order:

1. **Generic list/admin-instr plumbing** (lines ~25–260): `cat_nil`,
   `length_size`, `const_list`/`is_const`/`terminal_form`,
   `const_list_cat`/`_concat`/`_split`, `const_es_exists`,
   `v_to_e_const`/`_cat`, `be_to_e_cat`, `to_e_list_cat`, `cat_split`,
   `concat_cancel_last`, `extract_list1`, `split_vals` (the one `Fixpoint`:
   splits a list of admin-instrs into a leading run of values + the rest) +
   `split_vals_inverse`/`_prefix`. Mechanical, low-difficulty, high-reuse —
   several are near-duplicates of facts already in `helper_lemmas.v`/our
   `HelperLemmas.lean` (e.g. `concat_cancel_last` here vs
   `concat_cancel_last_n` there — check for overlap before porting both).
2. **Canonical-forms / `typeof` family** (lines ~262–555): `typeof`
   (`Definition`, admin-value → its `valtype`), `typeof_append`/`_cat`,
   `invert_typeof_I32`/`_I64`/`_numtype`/`_numtype_wf`/`_V128`/`_reftype`/
   `_reftype'` — "if a value has this static type, it must be this specific
   runtime shape." **This is the load-bearing family for progress on any
   instruction that pattern-matches its operand's runtime constructor**
   (e.g. numeric ops needing "the operand typed `i32` really is a `V_I32`").
   Directly analogous in spirit to `TypingLemmas.lean`'s inversion lemmas,
   but about values, not instruction typing.
3. **Branch/return label-finding machinery** (lines ~590–1137):
   `br_reduce`/`return_reduce`/`not_lf_br`/`not_lf_return` (`Definition`s —
   predicates for "does this sequence contain a not-yet-caught `br`/`return`
   admin-instr"), their decidability lemmas, `not_lf_br_singleton`/`_left`/
   `_right` and return counterparts, `Admin_instrs_ok_cons`/`_cat`/`_all`
   (composition/decomposition of `Instrs_ok2`-shaped typing — direct
   counterparts of our `TypingLemmas.lean`'s `ais_seq_typing_inversion`/
   `ais_composition_typing`, worth checking for reuse), and the
   `s_typing_lf_br`/`_lf_return` family (7 lemmas — "if this frame-typed
   config contains an unresolved br/return, X follows"). This layer is
   control-flow-specific plumbing progress needs that preservation doesn't
   (preservation gets to assume a step already happened; progress has to
   *find* which step, including "a `br` deep inside nested labels reduces
   by first finding its target label").
4. **Numeric-operator totality lemmas** (lines ~1300–1810, ~35 lemmas):
   `unop_not_none`, `binop_total`/`_before`/`_not_none`, `relop_total`/
   `_before`/`_not_none`, `cvtop_total`/`_before`/`_not_none`,
   `testop_not_none`, `idiv_total`, `irem_total`, `ilt_total`/`igt_total`/
   `ile_total`/`ige_total`, `signed_total`/`_nonzero`, `invsigned_total`/
   `_total_32m1`, plus small arithmetic facts (`two_pow_pos`/`_succ`,
   `wf_uN_lt`/`_lt'`, `Zsub1_toN`, `Zquot_abs_le`/`_ge_inv`) and vector-lane
   analogues (`packnum_not_none`, `lanes_nth_wf`). Pattern: "given
   well-formed operands, the operator's partial function always returns
   `Some`, unless [documented side condition]" — needed so progress can
   conclude a numeric instruction always steps (never silently stuck) when
   well-typed. Mechanical once `wf_*`/`*_is_wf` facts about the operand
   are in hand; likely a good early-porting target within this file (no
   dependency on the two big case-split lemmas below).
5. **The two capstone case-split lemmas + top theorem** (lines 1816–4260):
   - `call_indirect_progress` (line 1816, ~70 lines) — progress for one
     specific instruction (`call_indirect`) that has enough side conditions
     (table lookup, type match) to warrant its own lemma rather than being
     inlined as a case of the next one.
   - **`t_progress_be`** (line 1888, **~1793 lines**, by far the largest
     single lemma in the file) — the per-instruction-constructor case split:
     "a single basic instruction, well-typed under an empty label/return
     context with these operand values on the stack, either is a value/trap
     or takes a step." This is the Progress analogue of preservation's
     `ai_typing_inversion`/`instr_of` — expect the same "large, bounded,
     mechanical, no open math" character once ported, EXCEPT for the 5
     genuinely unresolved cases (see below). **Fully `Admitted`** in the
     current source (the only `Admitted` lemma in the whole file).
   - `Instr_ok_Instrs_ok` (line 3681, small bridging lemma between the two
     capstones).
   - `t_progress_e` (line 3702, ~528 lines) — lifts `t_progress_be` from a
     single basic instruction to a full instruction sequence, handling
     nested labels/frames via the br/return machinery from layer 3. Fully
     proved (`Qed`) in the current source.
   - `Theorem t_progress` (line 4230, the capstone, small) — top-level:
     ties `t_progress_e` to a full `Config_ok`-typed configuration. Fully
     proved.

## The remaining gap: `t_progress_be`'s 5 `admit.` sites

All 5 are annotated in-line by the author as the **same diagnosed bug**
already covered in `rocq_proof_intuition.md` (found there via commit-history
archaeology, before this file was even available to read directly — now
confirmed word-for-word against the actual source comments):

> the distinction between `num_`/`pack_`/`iN` and `lane_` is not preserved by
> the Coq encoding. So `proj_lane__2 l <> None` is not derivable, and no axiom
> can repair it: `vextract_lane_num` wants the `mk_lane__0` form of the very
> same list that `vtestop_true` wants in `mk_lane__2` form.

Concretely, the 5 sites (all vector/SIMD instruction cases) are: a cluster of
8 cases needing `1-8: admit.` (vextract/vtestop-adjacent), one more `1: admit.`
(similar shape, packed-form obstacle), a `1-4: admit.` cluster (VEXTUNOP/
VEXTBINOP/VNARROW/VCVTOP, same lane-injection obstacle), a `1-2: admit.`
(VLOAD with a `SPLAT` memarg — the typing rule doesn't bound the lane width
the way VLOAD_LANE/VSTORE_LANE's `wf_sz` premise does, so a too-wide splat is
well-typed but has no reduction rule — this one reads more like a possible
**spec gap** than a proof gap, worth flagging separately if pursued), and a
final `1: admit.` (same `lane_`-union issue). Per the intuition doc's
diagnosis, this is a generator-level encoding limitation, not something a
cleverer Coq tactic fixes — and since our Lean port is free to use a
completely different proof strategy (Lean's `lane_`/`Jnn`-union types may not
have the same encoding collapse — **worth checking directly**, this could be
a case where the Lean port genuinely closes a gap Rocq can't), this is
flagged as a live opportunity, not just a gap to mirror. If the Lean encoding
turns out to have the identical collapse, mirror the gap faithfully with
`sorry`, same as we already do for the (now-closed-upstream, see `NOTES.md`)
old Preservation SIMD gaps.

## Suggested porting order within this file (not yet cross-referenced against
the full project-wide `proof_prioritization.md` — that update is a `Tier I`-
scale addition, flagged in `resync_impact_report.md` rather than fully
re-derived here to avoid duplicating effort under time pressure)

1. Layer 1 (list/admin-instr plumbing) — cheapest, mirrors already-familiar
   `HelperLemmas.lean` idioms, dedupe against existing lemmas first.
2. Layer 2 (`typeof`/`invert_typeof_*`) — needed by almost everything else
   in this file; no blockers.
3. Layer 4 (numeric-operator totality) — independent of layers 3/5, only
   needs layer 2 plus existing `wf_*`/`*_is_wf` facts from `wasm2.0.lean`.
4. Layer 3 (br/return machinery) — needed before attempting `t_progress_e`;
   check `Admin_instrs_ok_cons`/`_cat`/`_all` against our existing
   `TypingLemmas.lean` lemmas for reuse first.
5. `call_indirect_progress`, then `t_progress_be` (skip/`sorry` the 5 SIMD
   sites per above), then `Instr_ok_Instrs_ok`, `t_progress_e`,
   `t_progress`.

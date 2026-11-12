# Proof prioritization — consolidated update (bundle9)

Written for: a future Claude session deciding what to work on next (primary
audience — meant to be followed top-to-bottom). Supersedes
`bundle2/.../proof_prioritization.md` + `bundle3/.../proof_prioritization_addendum.md`
as the document to actually follow (those are kept, untouched, as historical
record). Same four weighting factors as the original (dependencies, ease,
importance to the intuition doc, other factors — see that document if you
want the full explanation of the weighting scheme; not repeated here).

Ground truth for "done" vs "open" below is a direct `sorry` grep across all
6 files performed this bundle (2026-09-30) — see `proof_dependencies_v2.md`'s
table. The Rocq checkout is current (`58af2e2f9`); nothing here is scoped to
a stale snapshot.

---

## Tier A — done (bundles 1–9), listed so nobody re-derives these

**`Subtyping.lean`** (13): `valtype_sub_refl`/`_trans`, `forall2_valtype_sub_refl`/`_trans`,
`resulttype_sub_refl`/`_size_eq`/`_trans`/`_app`/`_split_sup`/`_split_sup'`,
`instrtype_sub_refl`/`_trans`, `instr_subtyping_weaken2`, **`instr_subtyping_strengthen2`**
(bundle5).

**`ExtensionLemmas.lean`** (7 + 3 helpers): the `*_extension_refl0`/`_refl`
family for all 6 store components, `Extend_store_refl`, plus
`forall_range_lt`/`forall_range_refl`/`forall_range_refl_noWf`.

**`HelperLemmas.lean`** (18, bundle5): `length_same_split_zero`,
`length_app_both_nil`, `length_app_nil`, `split_append_last`/`_1`/`_2`/`_left_1`,
`empty_append`, `option_orElse_none`/`option_none_orElse`/`option_some_orElse`,
`add_sub`/`_'`, `sizecat_le1`/`_le2`, `drop_size_cat`/`take_size_cat`, `size_eq_cat`.
Plus (bundle9, new infra not a Rocq port) `to_mathlib_forall₂`/`from_mathlib_forall₂`.

**`TypingLemmas.lean`** (the big one — ~77 done across bundles 5-9):
- bundle5: `inst_match` cluster (6: `construct_inst_match_label`/`_return`/
  `_local`/`_local_label_return`/`_local_return`, `construct_inst_prepend_label`);
  wellformedness-projection (`instr_ok_context_wf`, `ainstr_ok_context_store_wf`,
  `instrs_ok_context_wf`, `ainstrs_ok_context_store_wf`, + helpers
  `wf_admininstr_ref`, `wf_instr_admininstr`).
- bundle6: context-update (7: `upd_label_overwrite`, `upd_label_is_same_as_append`,
  `upd_local_is_same_as_append`, `upd_local_return_is_same_as_append`,
  `upd_return_is_same_as_append`, `upd_label_unchanged`, `upd_label_unchanged_typing`);
  `instrs_ok_nil_sub_gen`/`_sub`/`_refl`, `instrs_ok_widen_in`/`_out`, `instrs_ok_cons_gen`
  + administrative-side re-derivations + `ais_composition_typing`.
- bundle7 (15): `construct_instrs_typing_single`, `construct_ais_typing_single`,
  `instrs_empty_typing`, `ais_empty_typing`, `construct_ais_subtyping`,
  `construct_ais_instrtype_sub`, `injective_valtype_numtype`,
  `injective_admininstr_instr`, `construct_ais_compose`, `construct_ai_const_I32`,
  `construct_ai_ref`, `construct_ai_val`, `adminval_val_ref`, `construct_ais_trap`,
  `resulttype_sub_single_inversion`, `Val_ok_non_bot`, `Ref_ok_non_bot`.
- **bundle8 (the big unblock)**: `ai_principal_typing` (~340-line, 50+ case
  central definition — ported from `spectec/test-lean/typing_lemmas.lean`,
  one real bug found+fixed in its `BR_TABLE` case), `principal_typing_conversion`,
  `instr_typing_inversion`, `ai_typing_inversion`.
- bundle9: `Vals_ok` redefined (length-carrying), `Vals_ok_non_bot` proved.

**Note**: `instr_of` (`TypingLemmas.lean:105`) — a *different* central
definition from `ai_principal_typing` — is **NOT** in this done list. It was
never blocked by anything; it just hasn't been transcribed yet. See Tier C
below — this is now the single most important remaining piece of
structural work in the project, having taken over that title from
`ai_principal_typing`.

---

## Tier B — next: `instr_of`'s body (the new top blocker)

1. **`TypingLemmas.lean`: transcribe `instr_of`'s real body** (`instr_of
   (ai : admininstr) : Option instr`, currently `:= sorry`, a ~50-case match,
   each `admininstr` constructor ↦ `some` of the corresponding `instr`
   constructor where one exists, `none` for purely-administrative forms
   like `TRAP`/`REF`/`CALL_ADDR` that have no static-instruction
   counterpart). Justification: **directly blocks `construct_ai_maybe`**
   (the last remaining piece needed to close the `ais_vals_typing_inversion`/
   `construct_ais_vals` cluster below), and — per the original Rocq file's
   own structure — is presumed to be needed again throughout Tier E's 28
   `Step_pure__*_preserves` lemmas (going from "this administrative
   instruction reduced" back to "the corresponding static instruction was
   well-typed"). Purely mechanical transcription (direct constructor
   correspondence, exhaustively enumerable from `wasm2.0.lean`'s `admininstr`/
   `instr` constructor lists side by side) — no open mathematical content,
   should be a bounded, single-sitting task. Check
   `spectec/test-lean/typing_lemmas.lean` first for a usable prior version
   before writing from scratch (the same file bundle8 successfully mined
   for `ai_principal_typing` — check whether it also has `instr_of`
   transcribed; if so, verify correctness the same way bundle8 did for
   `ai_principal_typing` before porting).

## Tier C — TypingLemmas.lean's remaining 12 sorries, now unblocked

2. **`instrs_single_typing_inversion`, `ais_single_typing_inversion'`,
   `ais_single_typing_inversion`, `ais_single_ref_typing_inversion`,
   `ais_single_val_typing_inversion`, `split_single_append`, `val_ref_null_is_ref`**
   (lines 676-708). Justification: chain directly off `ai_typing_inversion`
   (done, bundle8) and `instrs_seq_typing_inversion`/`ais_seq_typing_inversion`
   (done, bundle6) — genuinely unblocked now, independent of `instr_of`.
   Do this tier first within Tier C since it needs nothing from Tier B.
3. **`ai_val_principal_typing_inversion`** (line 1084). Justification: needs
   `ai_principal_typing` (done) + `Vals_ok_non_bot`/`Val_ok_non_bot` (both
   done, the latter since bundle7, the former since bundle9) — fully
   unblocked, do alongside #2.
4. **`construct_ai_maybe`** (line 1202). Justification: needs `instr_of`
   (Tier B) — the one item in this cluster still gated.
5. **`ais_vals_typing_inversion`, `construct_ais_vals`, `construct_ais_vals'`**
   (lines 1209, 1263, 1269). Justification: `construct_ais_vals` is flagged
   in the original digest as the single longest/most intricate proof in the
   whole Rocq file (~125 lines, `last_ind` over two lists simultaneously,
   read in full during this bundle's rocq-changes review — still present
   and unchanged at current HEAD). Needs `Vals_ok` (done, bundle9),
   `resulttype_sub_app`/`_trans`/`Forall2_app'`-style machinery (all done,
   `Subtyping.lean` Tier A), and — per the Rocq proof's own structure, which
   routes through `construct_ai_maybe`/`Val_ok_non_bot` inside its inductive
   step — `instr_of` transitively (Tier B). Attempt last within this tier.

## Tier D — `TypePreservationPure.lean`'s 27 lemmas, now fully unblocked

All 27 remaining `sorry`s (everything from `Step_pure__nop_preserves` through
`t_pure_preservation`, plus the small helper `proj_identity`) are now
unblocked by Tier A's `ai_principal_typing`/`ai_typing_inversion` landing in
bundle8 — this is unchanged in substance from the original document's Tier
E, just renumbered since Tiers B/C above are new. Recommended order (from
the original prioritization, still valid — informed by Rocq file order and
per-lemma difficulty notes in `digest_typing_lemmas_and_type_preservation_pure.md`):

6. Work through the 26 non-`return_frame` `Step_pure__*_preserves` lemmas in
   Rocq's own file order: `nop`/`drop` (trivial) → `select`/`if` (medium,
   needs their own `_helper` lemmas first, also still `sorry`) →
   `label_vals`/`br_zero` (medium) → `br_succ`/`br_table_lt`/`br_table_ge`
   (hardest three) → `frame_vals`/`return_label` (medium) →
   `unop`/`binop`/`testop`/`relop`/`cvtop_val` (repetitive medium cluster) →
   `local_tee` (medium-high) → `ref_is_null_*` (medium-high, has its own
   `_helper`). `proj_identity` is a small standalone helper needed by the
   `br_*` cluster — do it first when reached.
7. **`Step_pure__return_frame_preserves`** — per the intuition doc, `Admitted`
   in Rocq not from intrinsic difficulty but from a lost proof during the
   July 1 `Admin_instrs_ok`→`Instrs_ok2` rename; this Lean port is free of
   that specific historical accident. Worth a real dedicated attempt before
   deferring, same reasoning as the original document.
8. **`t_pure_preservation`** (master dispatch, minus SIMD cases per the
   permanent-gap exclusion — see "other factors" below). Mechanical
   case-matching once #6/#7 exist.

## Tier E — `ExtensionLemmas.lean` remainder (79 sorries, independent track)

Unchanged in substance from the original document's Tier F (renumbered).
Can run in parallel with Tiers B–D at any point — depends only on
`Extend_*`/`Store_ok`/`wasm2.0.lean` machinery, not on anything in
`TypingLemmas.lean` beyond what's already done. Original sub-ordering still
applies (inversion lemmas → per-instruction extension facts → `funcinst_same`
resolution → `addrs_*`/`addrss_*` → assembly lemmas → `Extend_store_ais`
capstone → `construct_meminsts_grow` arithmetic gap); see the original
document's Tier F (#20-27) for full per-item justification, still accurate.
One update: #20's `limits_sub_refl`/`externtype_sub_refl` etc. are **already
signature-stated with real Rocq statements to port against** (confirmed
present in current-HEAD `extension_lemmas.v`, unchanged since the bundle3
resync) — still `sorry`, still first in this tier, just no longer needing
the "free reuse from a prior session" framing since they're directly portable
now.

## Tier F — `TypePreservation.lean` (12 sorries, last tier)

Unchanged in substance from the original document's Tier G (#28-35,
renumbered here as a block) — gated on Tier D (Preservation-Pure) and most
of Tier E (Extension) being done first. See the original document for full
per-item justification (`t_preservation_vs_type'`/`_type`,
`store_extension_reduce`, `t_read_preservation`, `step_moduleinst`,
`t_preservation_type`, `t_preservation` — the capstone, pure composition of
everything before it).

## Tier G — `type_progress.v` port (not started)

Unblocked earlier than the original document assumed (`ai_principal_typing`
being done removes one of the two things it needed from `TypingLemmas.lean`
being complete), but still deliberately sequenced after Tiers B-D since the
original author's own commit history treats it as the last major branch of
work (see `rocq_proof_intuition.md`), and this bundle's `rocq_changes_summary.md`
shows the upstream author is *currently, actively* working on exactly this
file (2 more SIMD lane-cases closed since the last check) — worth waiting
for more of that upstream progress to land before committing significant
effort to porting a file that's still visibly in flux. When started: begin
with the non-SIMD "spine" (list plumbing → `typeof`/`invert_typeof_*` →
numeric-operator totality → br/return machinery → `call_indirect_progress`)
per `digest_type_progress.md`'s layer breakdown, treat `t_progress_be`'s
6-8 remaining lane-op admits the same way Tier D treats SIMD (permanent-gap
exclusion, revisit only if the upstream author closes more of them first).

## Other factors (unchanged from the original document, restated for completeness)

- **Free reuse** always jumps the queue — check `spectec/test-lean/` and
  `spectec/test-lean/test-lean-claude/` before deriving anything from
  scratch (this is exactly how `ai_principal_typing` got done in one
  bundle instead of many).
- **Deliberately-permanent gaps**: all SIMD/vector-instruction cases remain
  excluded from every tier above, in both Preservation (now closed
  upstream, so no longer permanent for us — see `rocq_changes_summary.md`
  §1, this reverses part of what bundle3's addendum said: SIMD Preservation
  work, i.e. the ~90 new vector lemmas across `type_preservation_pure.v`/
  `type_preservation.v`, is real portable work whenever Tiers D/F are
  otherwise done, not a permanent gap — just not prioritized ahead of the
  non-vector spine, per the original author's own visible ordering) and
  Progress (`t_progress_be`'s lane-op cases, genuinely still open upstream,
  actively being worked on by the Rocq author — see Tier G).
- **"Close a file" motivation**: `Subtyping.lean` (32 sorries, mostly the
  `instrtype_sub_compose*` family — none currently referenced as blocking
  anything else, per `proof_dependencies_v2.md`) and the dead cluster in
  `HelperLemmas.lean` (22 of its 29 remaining sorries, per the same doc) are
  the two files where "close it out" would require deliberately picking up
  low-leverage work — not recommended ahead of Tiers B-D, which have far
  higher leverage per lemma right now.

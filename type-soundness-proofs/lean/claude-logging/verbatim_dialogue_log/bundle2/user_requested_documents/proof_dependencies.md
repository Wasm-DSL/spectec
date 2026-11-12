# Proof dependency map

Written for: a future Claude session planning proof work (primary
audience), and the user (secondary — to see the shape of the dependency
graph at a glance).

**⚠ CRITICAL CAVEAT, read this first**: this document describes
dependencies as they exist in the **local, checked-out copy** of
`spectec/test-rocq/theories/` (git commit `5b03ae067`, "Repaired
preservation pure (except return frame)", 2026-07-01), which this whole
Lean-porting project has been working from. That local copy is **badly
stale relative to the live `rocq-backend-proof` branch on GitHub**
(confirmed HEAD as of this writing: `a8b585cdb`, 2026-09-22, "Vector
Instructions for Preservation proven, and most well-formedness lemmas
done."). Diffing the two directly:

```
 axioms.v                  |   56 +-
 extension_lemmas.v        | 3435 +++++---
 helper_lemmas.v           |  744 +-
 helper_tactics.v          |   42 +
 subtyping.v               |  194 +-
 type_preservation.v       | 2752 +++---
 type_preservation_pure.v  |  764 +-
 type_progress.v           | 4260 +++++++++  (does not exist locally AT ALL)
 typing_lemmas.v           |  418 +-
 wasm.v                    | 9182 +++++++++++++++-----
 wasm1.v                   | 1089 +--
 11 files changed, 17303 insertions(+), 5633 deletions(-)
```

`type_progress.v` (the Progress half of type safety) is entirely absent
locally and exists as a real, substantial, 4260-line file upstream.
Every other file has grown or been substantially reworked since the
local snapshot was taken (`extension_lemmas.v` and `wasm.v` especially —
both roughly 60% bigger at HEAD). **This dependency map — and the whole
6-file Lean skeleton this project built — reflects only the local, stale
snapshot.** See the end-of-session report to the user for the decision
this raises (re-sync vs. continue on the local snapshot). Everything
below is still accurate *for that snapshot*, and the file-level
dependency *shape* (which file needs which) is very unlikely to have
changed even where line counts have — but line/lemma counts and any
lemma-name references below should be treated as "true as of Jul 1
2026," not "true today."

---

## 1. File-level dependency graph (Rocq `Require Import` chains, confirmed by reading each file's preamble)

```
wasm.v  (no local deps — this is the SpecTec-generated base)
  │
  ├──> helper_lemmas.v          (deps: wasm)
  │      │
  │      ├──> subtyping.v       (deps: wasm, helper_lemmas, helper_tactics)
  │      │      │
  │      │      ├──> typing_lemmas.v         (deps: wasm, helper_lemmas, helper_tactics, subtyping)
  │      │      │      │
  │      │      │      ├──> type_preservation_pure.v  (deps: wasm, helper_lemmas, helper_tactics, typing_lemmas, subtyping)
  │      │      │      │      │
  │      │      │      │      └──> extension_lemmas.v  (deps: wasm, helper_lemmas, helper_tactics,
  │      │      │      │             typing_lemmas, subtyping, type_preservation_pure)
  │      │      │      │             │
  │      │      │      │             └──> axioms.v  (deps: wasm, helper_lemmas, helper_tactics,
  │      │      │      │                    typing_lemmas, subtyping, type_preservation_pure,
  │      │      │      │                    extension_lemmas)
  │      │      │      │                    │
  │      │      │      │                    └──> type_preservation.v  (deps: wasm, helper_lemmas,
  │      │      │      │                           helper_tactics, typing_lemmas, subtyping,
  │      │      │      │                           type_preservation_pure, extension_lemmas, axioms)
  │      │      │      │
  │      │      │      └── (type_preservation_pure also feeds extension_lemmas directly, shown above)
  │      │      │
  │      │      └── (typing_lemmas also feeds type_preservation_pure directly, shown above)
  │      │
  │      └── helper_tactics.v  (deps: wasm, helper_lemmas — a peer of subtyping.v in the import
  │             chain; provides Ltac automation used by everything downstream, contributes no
  │             standalone lemmas/defs of its own for other files to depend on by name)
  │
  └── (wasm1.v exists as a sibling WASM-1.0 development; confirmed NOT imported by any of the
       WASM-2.0 files above — self-contained, out of scope for this port)

type_progress.v  (upstream only, not in local checkout — per its own likely import list, almost
  certainly depends on everything above it, i.e. the same transitive closure as
  type_preservation.v, since Progress needs the same typing/store-extension infrastructure
  Preservation does; CANNOT be confirmed from the local checkout since the file isn't present)
```

This is a **strict linear chain**, not a DAG with real branching — every
file's only "new" dependency, relative to the file before it in the
chain, is exactly one more file. This matches the git-history finding in
`rocq_proof_intuition.md` §2 that the author built these in almost
exactly this order. The practical upshot for a Lean port: **there is
only one sensible file-completion order**, and it's the one this project
already chose (`HelperLemmas.lean` → `Subtyping.lean` → `TypingLemmas.lean`
→ `TypePreservationPure.lean` → `ExtensionLemmas.lean` → (axioms folded
into `HelperLemmas.lean`) → `TypePreservation.lean`).

## 2. Within-file dependency structure (what depends on what *inside* each file)

This is coarser than a full per-lemma citation graph (that would be
hundreds of edges and not more useful than the file-level view above for
planning purposes) — it groups each file into dependency *tiers*: tier 0
lemmas can be proved with nothing else in the file, tier 1 needs tier 0,
etc. Proof work should proceed tier-by-tier within a file, same as
file-by-file across files.

### `HelperLemmas.lean` (← `helper_lemmas.v` + `axioms.v`)
- **Tier 0** (no in-file deps): `leadd`, `list_update_length`,
  `list_update_length_func`, `split_append_*` family, `empty_append`,
  `sizecat_le1`/`_le2`, `drop_size_cat`/`take_size_cat`, `add_sub`/`add_sub'`,
  `add_false`, `option_orElse_none`/`option_none_orElse`/`option_some_orElse`.
  Essentially everything except the `Forall2_*`/`prepend_label` families.
- **Tier 1**: `Forall_nth'`, `Forall2_nth`, `Forall2_lookup` (need
  `lookup_total` only — a def, not a lemma, so still effectively tier 0
  in terms of *lemma* dependencies), `list_update_func_split`/`_strong`
  (need nothing extra either, but are individually nontrivial).
- **Tier 2**: `Forall2_list_update*` family (5 lemmas) — plausibly reuse
  each other or a shared "update-at-index" pattern; `list_slice_update_length`
  needs `list_slice_update`'s definition only.
- **Tier 3**: `lookup_label_0`/`lookup_label_1` need `prepend_label`
  (tier 0 def) and, per the Rocq proof, unfold the `context` append
  instance — no other in-file lemma dependency, but the *proof* itself
  (not just the statement) may be fiddly.
- **Tier 4 (independent)**: `concat_cancel_last_n`/`size_eq_cat` — these
  two are noted in the digest as *semantically the same fact*, proved two
  different ways in Rocq; proving one and deriving the other from it is a
  legitimate shortcut (see `proof_prioritization.md`).
- **`axioms.v`'s 2 axioms** (`nbytes_len`, `ibytes_len`): no in-file
  dependency (they're `axiom`s, asserted not proved) — depend only on
  `wasm2.0.lean`'s `nbytes_`/`ibytes_`/`wrap__`/`size` opaques existing,
  which they already do.

### `Subtyping.lean` (← `subtyping.v`)
- **Tier 0**: `valtype_sub_refl`, `valtype_sub_trans`, `valtype_sub_non_bot`.
  **Already proved** (reused from a prior session, see
  `proof_prioritization.md`'s "already done" list).
- **Tier 1**: `resulttype_sub_refl` (needs `valtype_sub_refl` +
  `forall2_valtype_sub_refl`, a new helper), `resulttype_sub_size_eq`,
  `resulttype_sub_non_bot` (needs `valtype_sub_non_bot`). **`resulttype_sub_refl`
  already proved.**
- **Tier 2**: `resulttype_sub_trans` (needs `resulttype_sub_refl`'s
  supporting `forall2_valtype_sub_trans` helper + `valtype_sub_trans`).
  **Already proved.**
- **Tier 3**: `resulttype_sub_app_trans`, `resulttype_sub_app` (needs
  `Forall2_app'`, a generic list lemma stated in this file), `Forall2_app'`,
  `Forall2_take`/`Forall2_drop`, `resulttype_sub_split`,
  `resulttype_sub_app'`. **`resulttype_sub_app` already proved**; the rest
  in this tier are still `sorry`.
- **Tier 4**: `resulttype_sub_split_sup`/`_sup'` (need `resulttype_sub_trans`
  transitively via the `List.zip_append`/`take`/`drop` argument, but not
  any *other* lemma in this tier). **Both already proved.**
- **Tier 5**: `instrtype_sub_refl` (needs `resulttype_sub_refl`),
  `instrtype_sub_trans` (needs `resulttype_sub_split_sup`,
  `resulttype_sub_split_sup'`, `resulttype_sub_app`, `resulttype_sub_trans`
  — the single most dependency-heavy lemma in this file). **Both already
  proved.**
- **Tier 6**: `resulttype_sub_empty`/`resulttype_empty_sub` (need only
  `resulttype_sub_size_eq`-style reasoning, no instrtype dependency —
  could actually be tier 2, listed here just because of file position).
- **Tier 7**: the whole `instrtype_sub_compose*` family (9 lemmas) — each
  depends on `instrtype_sub_trans` plus various `resulttype_sub_split*`
  lemmas; `instrtype_sub_compose0`/`_compose1`/`_compose2` are explicitly
  *derived* from `_compose_le`/`_compose_ge` in Rocq (so prove those two
  general forms first, the rest should follow quickly).
- **Tier 8**: `instrtype_sub_cancel_left`, `instrtype_sub_empty`,
  `instrtype_sub_sub_empty*`, `instrtype_sub_iff_resulttype_sub*`,
  `instrtype_sub_extend`, `instrtype_sub_add_same`,
  `resulttype_sub_cons` — mostly need `instrtype_sub_trans` and/or basic
  `instrtype_sub_refl`, fairly independent of each other.
- **Tier 9 (top)**: `instr_subtyping_strengthen2` (needs
  `resulttype_sub_split_sup`), `instr_subtyping_weaken2` (needs
  `resulttype_sub_split_sup'`). **`instr_subtyping_weaken2` already
  proved**; `instr_subtyping_strengthen2` still `sorry` but should be a
  near-mirror-image of it (dual split lemma, same shape of proof).

### `TypingLemmas.lean` (← `typing_lemmas.v`)
- **Tier 0 (blocking almost everything else in this file)**: `instr_of`
  and `ai_principal_typing` — currently **signature-only stubs with
  `sorry` bodies**, not just `sorry` proofs. Nothing past this tier can
  be *proved* for real until these two definitions have real bodies,
  because their statements are literally about case-matching on these
  defs. This is the single biggest blocker in the whole project — see
  `proof_prioritization.md`.
- **Tier 1**: context-update helpers (`upd_label` etc., all defs, no
  proof deps) and their `_is_same_as_append`/`_unchanged` lemmas (need
  only the defs, not `ai_principal_typing`).
- **Tier 2**: `instr_ok_context_wf`/`ainstr_ok_context_store_wf`/
  `instrs_ok_context_wf`/`ainstrs_ok_context_store_wf` — trivial
  `inversion`-style lemmas, no dependency on `ai_principal_typing`,
  provable NOW independent of tier 0.
- **Tier 3**: `instrs_empty_typing` — needs `Subtyping.lean`'s
  `resulttype_sub_*` family (already largely proved) but NOT
  `ai_principal_typing`. Provable now.
- **Tier 4 (blocked on tier 0)**: `instr_typing_inversion`,
  `ai_typing_inversion` — the two "soundness" theorems connecting
  `Instr_ok`/`Instr_ok2` to `ai_principal_typing`; structurally cannot be
  proved until `ai_principal_typing`'s body exists.
- **Tier 5 (blocked on tier 4, transitively tier 0)**:
  `instrs_single_typing_inversion`, `ais_single_typing_inversion'`,
  `ais_single_typing_inversion` (needs `instrtype_sub_trans` from
  `Subtyping.lean` too, already available), `ais_single_ref_typing_inversion`,
  `ais_single_val_typing_inversion`.
- **Tier 5b (NOT blocked on tier 0)**: `instrs_seq_typing_inversion`,
  `ais_seq_typing_inversion`, `ais_composition_typing` — these are pure
  structural-induction-on-`Instrs_ok`/`Instrs_ok2` facts and do NOT need
  `ai_principal_typing` at all (confirmed: a prior session's
  `SeqTypingInversion.lean` proves the `Instrs_ok`-only version with zero
  dependency on any principal-typing definition). **High-value,
  immediately-provable target** — see prioritization doc.
- **Tier 6**: `construct_instrs_typing_single`/`construct_ais_typing_single`/
  `construct_ais_subtyping`/`construct_ais_instrtype_sub`/`construct_ais_compose`
  — pure construction-direction lemmas, need only the `Instrs_ok`/`Instrs_ok2`
  constructors + `Subtyping.lean`, NOT `ai_principal_typing`. Provable now.
- **Tier 6b (blocked on tier 0)**: `ai_val_principal_typing_inversion`,
  `construct_ai_maybe` (needs `instr_of`'s real body).
- **Tier 7**: `construct_ai_const_I32`, `construct_ai_ref`,
  `construct_ai_val`, `adminval_val_ref` — simple, need only `Instr_ok2`'s
  constructors, not blocked on tier 0.
- **Tier 8**: `value_extra`/`Vals_ok` (defs), `Val_ok_non_bot`,
  `Vals_ok_non_bot`, `Ref_ok_non_bot` — need only `Val_ok`/`Ref_ok`'s
  constructors, not blocked on tier 0.
- **Tier 9**: `ais_vals_typing_inversion`/`construct_ais_vals`/
  `construct_ais_vals'` — the hardest lemma in the file
  (`construct_ais_vals`, ~125 lines in Rocq via `last_ind`); needs
  `Vals_ok` (tier 8) and `instrtype_sub` machinery, NOT `ai_principal_typing`.
- **Tier 10 (independent cluster)**: `inst_match` and its 6
  `construct_inst_match_*`/`construct_inst_prepend_label` lemmas — pure
  record-equality bookkeeping, no dependency on anything else in this
  file. Provable immediately, any time.
- **Tier 11**: `resulttype_sub_single_inversion` — needs only `Subtyping.lean`.

### `TypePreservationPure.lean` (← `type_preservation_pure.v`)
Almost flat — each of the 28 `Step_pure__*_preserves` lemmas depends
primarily on `TypingLemmas.lean`'s `ais_single_typing_inversion`/
`ais_vals_typing_inversion`/`construct_ais_*` family (tier 5/6/9 above),
i.e. **this entire file is blocked on `TypingLemmas.lean`'s tier 0**
(`ai_principal_typing`'s real body), transitively, EXCEPT where a lemma
only needs the tier-5b/tier-6/tier-9/tier-10 lemmas that don't need
`ai_principal_typing` — worth double-checking case by case once tier 0
is unblocked, since some of the simpler `Step_pure__*` lemmas (`nop`,
`drop`) may only need `ais_single_typing_inversion'` (which itself is
blocked) rather than the full principal-typing machinery, but this needs
verification once `instr_of`/`ai_principal_typing` have real bodies.
Within the file: a few explicit intra-file dependencies —
`Step_pure__select_true/false_preserves` both need
`Step_pure__select_preserves_helper`; `Step_pure__if_true/false_preserves`
both need `Step_pure__if_preserves_helper`;
`Step_pure__ref_is_null_true/false_preserves` both need
`Step_pure__ref_is_null_helper`. The master theorem
`t_pure_preservation` needs literally all 26 non-admitted lemmas in the
file (it's a dispatch table). `Step_pure__return_frame_preserves` is
independent of everything else (deliberately `sorry`, matching Rocq's
own gap — see `rocq_proof_intuition.md` §2 for why it's plausibly
tractable despite the Rocq gap).

### `ExtensionLemmas.lean` (← `extension_lemmas.v`)
- **Tier 0**: the 12 `*_extension_refl0`/`*_extension_refl`
  (per-component + list-lifted) lemmas plus `store_extension_refl` and
  the 3 new `forall_range_*` helpers. **All already proved this session**
  (see prioritization doc). `funcinst_same` sits at tier 0 too
  (structurally) but is flagged with a real representational caveat (the
  zip-based `Forall₂` doesn't force equal length) — still `sorry`.
- **Tier 1**: `Val_ok_store`, `s_invert_funcs`/`_globals`/`_mems`/`_tables`,
  `se_invert_funcs`/`_tables`/`_mems`/`_store_globals`/`_elems`/`_datas` —
  pure inversion lemmas on `Store_ok`/`Extend_store`'s single constructor,
  no dependency on tier 0.
- **Tier 2**: `store_extension_ref`/`_refs`/`_val`/`_vals` (need
  `funcinst_same` — currently blocked by the same caveat as above —
  and `se_invert_funcs`).
- **Tier 3**: the 7 per-instruction "extension fact" lemmas
  (`global_set_global_extension`, `store_none_mem_extension`,
  `memory_grow_mem_extension`, `table_set_table_extension`,
  `table_grow_table_extension`, `elem_drop_elem_extension`,
  `data_drop_data_extension`) — each needs only the corresponding
  `Extend_*inst` constructor directly, no dependency on tiers 0-2. **High
  value, independently provable, matches this file's most "obviously
  achievable" cluster** per the git-history evidence that this section
  (not the reflexivity family) was the bulk of the July 22 "done except
  meminst grow" commit.
- **Tier 4**: `minst_invert_*` family (7 lemmas) — need `Moduleinst_ok`'s
  constructor directly; `minst_invert_tables`/`_mems` additionally need
  `Limits_sub`/`Memtype_sub` facts NOT currently declared anywhere in
  this project (see prioritization doc's note on the missing
  `limits_sub_refl`/`externtype_sub_*` cluster).
- **Tier 5**: `lookup_global`, `bt_inversion`, `tc_func_reference2`,
  `store_typed_exterval_types` — assorted, mostly need tier 4.
- **Tier 6**: `addrs_*_extension` (4 lemmas, need tier 2's `Externaddr_ok`
  reasoning is actually independent — these need `se_invert_*` (tier 1)
  directly, not tier 2) and their pointwise-list lifts `addrss_*_extension`
  (4 more, need the singular versions).
- **Tier 7**: `store_extension_exts`, `store_extension_eleminst`,
  `store_extension_eleminsts'`/`_eleminsts`, `store_extension_datainsts'`/
  `_datainsts` (need tier 6), culminating in **`store_extension_moduleinst`**
  (needs tiers 4, 6, 7 all together — the file's own "key assembly
  lemma").
- **Tier 8**: `store_extension_funcinst`/`_funcinsts`,
  `_globalinst`/`_globalinsts`, `_tableinst`/`_tableinsts`,
  `_meminst`/`_meminsts`, `store_extension_externaddrs_func` — need tier
  7's `store_extension_moduleinst` (for funcinst) or tier 2 (for the
  others).
- **Tier 9 (top)**: `store_extension_ais` — needs a custom mutual
  induction over `Instrs_ok2`/`Instr_ok2` plus tiers 2, 7, 8 — the file's
  capstone, and itself a direct dependency of `type_preservation.v`.
- **Tier 10 (independent cluster, mirrors tier 3)**: the 7 `construct_*`
  lemmas (`construct_tableinsts`, `construct_tableinsts_grow`,
  `construct_globalinsts`, `construct_meminsts`, `construct_meminsts_grow`,
  `construct_datainsts`, `construct_eleminsts`) — each needs only the
  corresponding `*_ok` judgment's constructor plus (for the two `_grow`
  variants) basic arithmetic; **NOT dependent on tiers 0-9 above**,
  genuinely independent, provable any time. This is where the Rocq
  `admit` (memory-growth page bound) lives, in `construct_meminsts_grow`'s
  Rocq counterpart.

### `TypePreservation.lean` (← `type_preservation.v`)
Almost entirely a **linear chain of composition**, each lemma needing the
ones before it in file order:
`zero_is_well_formed`/`num_default`/`num_default_is_well_formed`
(independent, tier 0) → `inst_t_context_local_empty`/`_labels_empty`
(independent, tier 0, need only `Moduleinst_ok`) →
`t_preservation_vs_type'` (needs `TypingLemmas.lean`'s `Vals_ok`,
`ExtensionLemmas.lean`'s `inst_match`) → `t_preservation_vs_type` (needs
`t_preservation_vs_type'` + `ExtensionLemmas.lean`'s `store_extension_vals`)
→ `store_extension_reduce` (needs essentially all of
`ExtensionLemmas.lean`'s tier 3/10 per-instruction lemmas, dispatched one
per `Step` case; **deliberately `sorry` for 2 SIMD cases, matching
Rocq**) → `reduce_inst_unchanged` (independent, tier 0) →
`t_read_preservation` (needs `TypingLemmas.lean`'s full inversion/
construction machinery, dispatched one per `Step_read` case; **deliberately
`sorry` for 5 SIMD cases**) → `step_moduleinst` (needs
`reduce_inst_unchanged` + `ExtensionLemmas.lean`'s `store_extension_moduleinst`
+ `store_extension_reduce`) → `t_preservation_type` (needs
`TypePreservationPure.lean`'s `t_pure_preservation`,
`t_read_preservation` above, `ExtensionLemmas.lean`'s `store_extension_ais`;
**deliberately `sorry` for 2 SIMD cases, and transitively inherits every
SIMD gap from its dependencies**) → **`t_preservation`** (needs
`store_extension_reduce`, `t_preservation_vs_type`, `t_preservation_type`,
`reduce_inst_unchanged`, `store_extension_moduleinst` — pure composition,
no case analysis of its own, per Rocq's own proof shape).

## 3. Cross-file "missing infrastructure" dependency (flagged, not yet a blocker)

`ExtensionLemmas.lean`'s `minst_invert_tables`/`minst_invert_mems` need
`Limits_sub`/`Memtype_sub` reflexivity/transitivity/inversion facts
(`limits_sub_refl`, `limits_sub_trans`, `externtype_sub_refl`,
`externtype_sub_trans`, `externtype_global_eq`, `externtype_func_eq`) that
**do not exist anywhere in the current Rocq source** (confirmed by direct
grep — see the naming note added to `ExtensionLemmas.lean` during this
session) but ARE needed, and a prior Lean session already proved exactly
these facts (in its own `Subtyping.lean`, misattributed to a stale Rocq
line range — see `digest_prior_lean_attempts.md`). These should be added
as new supporting lemmas (their underlying relations `Limits_sub`/
`Externtype_sub`/`Tabletype_sub`/`Memtype_sub` genuinely exist in
`wasm2.0.lean`) before `minst_invert_tables`/`_mems` can be proved — see
`proof_prioritization.md` for where this slots in.

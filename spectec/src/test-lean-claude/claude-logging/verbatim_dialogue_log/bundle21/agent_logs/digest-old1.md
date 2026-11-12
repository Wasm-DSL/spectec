# digest-old1: digest of the historical planning/analysis documents of bundles 2, 3, 8, 9, 12, 13

Label `digest-old1`. Read-only digest. Only writes: this file (and an empty scratch dir
`/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/work/digest-old1/`).
Nothing was written inside `/home/zhengyew/spectec`. No agents spawned, no lake, no git writes, no builds.
Base dir for all assigned files (abbreviated `VDL/` below):
`/home/zhengyew/spectec/spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/`

Convention used in this log: statements without a prefix come from the 17 assigned documents. Statements
prefixed **OBSERVED** (and all of section 8) come from my own read-only greps of the current Lean files (NOT from the
assigned documents) and are only there to say whether an old claim is still true. A reference like `(#6 sec.3b)` means
document number 6 of the table in section 1, section 3b of it; `#36` style numbers inside quotes of the prioritization
documents are their own tier-item numbers.

## 0. Safety check (START), verbatim

Command: `bash /tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/verify.sh digest-old1-start`

```
safety check [digest-old1-start] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T053059.929649054Z-digest-old1-start-463816.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
2a4
> ?? spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/
```

(The NOTE lines were already present at start, before I ran anything else; they come from other activity, not from me.)

## 1. Files read (all 17, every line; 3147 lines total)

| # | file (under `VDL/`) | lines |
|---|---|---:|
| 1 | bundle2/user_requested_documents/proof_dependencies.md | 355 |
| 2 | bundle2/user_requested_documents/proof_prioritization.md | 353 |
| 3 | bundle2/user_requested_documents/rocq_proof_intuition.md | 513 |
| 4 | bundle3/updated_documents/proof_dependencies_addendum.md | 63 |
| 5 | bundle3/updated_documents/proof_prioritization_addendum.md | 126 |
| 6 | bundle3/updated_documents/resync_impact_report.md | 275 |
| 7 | bundle3/updated_documents/rocq_proof_intuition_addendum.md | 43 |
| 8 | bundle8/vals_ok_non_bot_analysis.md | 147 |
| 9 | bundle9/user_requested_documents/proof_dependencies_v2.md | 117 |
| 10 | bundle9/user_requested_documents/proof_prioritization_v2.md | 210 |
| 11 | bundle9/user_requested_documents/rocq_changes_summary.md | 161 |
| 12 | bundle9/user_requested_documents/vals_ok_non_bot_resolution.md | 128 |
| 13 | bundle12/user_requested_documents/proof_prioritization_v3.md | 128 |
| 14 | bundle13/user_requested_documents/proof_dependencies_v3.md | 75 |
| 15 | bundle13/user_requested_documents/proof_prioritization_v4.md | 92 |
| 16 | bundle13/user_requested_documents/rocq_changes_summary_v2.md | 228 |
| 17 | bundle13/user_requested_documents/signature_audit_v1.md | 133 |

Skimmed: none. (Other files in bundle8 such as prompt_8.md/response_8*.md are not mine.)

## 2. Orientation and timeline (what these documents are)

All 17 are historical snapshots written when the Lean port had 6 files (HelperLemmas, Subtyping, TypingLemmas,
TypePreservationPure, ExtensionLemmas, TypePreservation) and no TypeProgress.lean. Their `sorry` counts, line
numbers, Rocq names, SIMD-scope statements and "Rocq has an `Admitted` here" statements are snapshots; several
are STALE or WRONG for bundle20/21 (section 5). The mathematically durable content is the pitfall/technique material
(section 6), the lane_/Forall2 representation diagnoses, and the standing rules (section 4).

Timeline reconstructed from the documents:

- bundle1-2: Phase 1 = all signatures stated, proofs `sorry`. Tier A done: 13 `Subtyping.lean` lemmas
  (`valtype_sub_refl/_trans`, `forall2_valtype_sub_refl/_trans`, `resulttype_sub_refl/_size_eq/_trans/_app/_split_sup/_split_sup'`,
  `instrtype_sub_refl/_trans`, `instr_subtyping_weaken2`) and the `ExtensionLemmas.lean` reflexivity family
  (`*_extension_refl0/refl` x 6 components, `store_extension_refl`, helpers `forall_range_lt/_refl/_refl_noWf`).
  Docs written against LOCAL STALE Rocq checkout `5b03ae067` (2026-07-01).
- bundle3 (2026-09-23): user merged upstream (`b78d56eeb` merges `26d40070b` with `a8b585cdb`); resync report; addenda.
- bundle5: HelperLemmas tier-0 cluster (18), `instr_subtyping_strengthen2`, TypingLemmas `inst_match` cluster (6) + wf-projection lemmas.
- bundle6: context-update lemmas (7), `instrs_ok_*` family, `*_seq_typing_inversion`, `ais_composition_typing`.
- bundle7: 15-lemma batch (`construct_*`, `injective_*`, `resulttype_sub_single_inversion`, `Val_ok_non_bot`, `Ref_ok_non_bot`, ...).
- bundle8: `ai_principal_typing` (~340 lines, 50+ cases), `principal_typing_conversion`, `instr_typing_inversion`,
  `ai_typing_inversion`, `injective_admininstr_instr` ported from `spectec/test-lean/typing_lemmas.lean`; one real bug found and
  fixed in its `BR_TABLE` case; `import Mathlib.Tactic` added; `vals_ok_non_bot_analysis.md` written (user said: leave it for now).
- bundle9: user chose Option 2 + 3 for `Vals_ok`; `Vals_ok_non_bot` proved; Rocq checkout confirmed current at `58af2e2f9`
  (merged into lean-backend as `868bca93f`); `ai_principal_typing` `REF_HOST_ADDR` gap fixed (mentioned by bundle12).
- bundle10: `Subtyping.lean` and `TypingLemmas.lean` fully done (0 sorry), incl. `instr_of`, `construct_ais_vals`.
- bundle11-12: `TypePreservationPure.lean` real-sorry count 29 -> 20 -> 11; select found hard; testop/relop signature bugs.
- bundle13: user merged `rocq-backend-proof-final` (merge `8ac6699ac`; diff `da555377a..95c256c2c`, 15 files, +8249/-3961);
  `nbytes_` totality build break fixed; `construct_meminsts_grow` gained the `2^16` bound hypothesis; signature audit
  (12 mismatches, 20 orphan citations); `frame_vals_preserves` proved at the end of the bundle.

## 3. Per-file digests

### 3.1 bundle2 `proof_dependencies.md` (355 lines) - historical, superseded by #9 and #14

- Banner (l.7-46): written against LOCAL checkout git `5b03ae067` (2026-07-01 "Repaired preservation pure (except return frame)");
  live branch tip then `a8b585cdb` (2026-09-22 "Vector Instructions for Preservation proven, and most well-formedness lemmas done.").
  Quoted diffstat, 11 files +17303/-5633: axioms.v 56, extension_lemmas.v 3435, helper_lemmas.v 744, helper_tactics.v 42,
  subtyping.v 194, type_preservation.v 2752, type_preservation_pure.v 764, type_progress.v 4260 (absent locally),
  typing_lemmas.v 418, wasm.v 9182, wasm1.v 1089.
- Sec.1 (l.48-97): Rocq `Require Import` chain, strict linear: wasm.v -> helper_lemmas.v -> subtyping.v (helper_tactics peer) ->
  typing_lemmas.v -> type_preservation_pure.v -> extension_lemmas.v -> axioms.v -> type_preservation.v; wasm1.v is a
  self-contained sibling, never imported. Lean order identical (axioms folded into HelperLemmas.lean). Later docs (#4, #9, #14)
  redraw ExtensionLemmas as a sibling of TypePreservationPure (both feed TypePreservation) and add TypeProgress as a parallel branch.
- Sec.2 (l.99-339) tier lists per file. Still-useful facts:
  * HelperLemmas: `concat_cancel_last_n` and `size_eq_cat` are "semantically the same fact" (prove one, derive the other);
    `axioms.v` had only `nbytes_len`, `ibytes_len` then.
  * Subtyping: `instrtype_sub_compose0/1/2` are derived from `_compose_le/_compose_ge` in Rocq (prove those two first);
    `instr_subtyping_strengthen2` is the dual of `weaken2` (`resulttype_sub_split_sup` vs `_sup'`).
  * TypingLemmas: Tier 0 blocker was `instr_of` + `ai_principal_typing` being signature-only `sorry` stubs; Tier 5b
    (`instrs_seq_typing_inversion`, `ais_seq_typing_inversion`, `ais_composition_typing`) NOT blocked by it (prior session's
    `SeqTypingInversion.lean` proves the `Instrs_ok` version); Tier 9 `construct_ais_vals` (~125 lines Rocq, `last_ind` over two lists)
    is the hardest lemma of the file; Tier 10 `inst_match` + 6 `construct_inst_*` independent.
  * TypePreservationPure: 28 `Step_pure__*_preserves`; intra-file deps: `select_true/false` <- `select_preserves_helper`,
    `if_true/false` <- `if_preserves_helper`, `ref_is_null_true/false` <- `ref_is_null_helper`; `t_pure_preservation` needs all 26
    non-admitted lemmas; `Step_pure__return_frame_preserves` independent.
  * ExtensionLemmas tiers: 0 refl family; 1 `Val_ok_store`, `s_invert_*`, `se_invert_*`; 2 `store_extension_ref/_refs/_val/_vals`
    (needed `funcinst_same`); 3 seven per-instruction extension facts (`global_set_global_extension`, `store_none_mem_extension`,
    `memory_grow_mem_extension`, `table_set_table_extension`, `table_grow_table_extension`, `elem_drop_elem_extension`,
    `data_drop_data_extension`); 4 `minst_invert_*` (7); 6 `addrs_*_extension`/`addrss_*_extension`; 7 `store_extension_moduleinst`
    "key assembly lemma"; 9 `store_extension_ais` capstone (custom mutual induction over `Instrs_ok2`/`Instr_ok2`);
    10 seven `construct_*` lemmas (`construct_tableinsts(_grow)`, `construct_globalinsts`, `construct_meminsts(_grow)`,
    `construct_datainsts`, `construct_eleminsts`), independent; the Rocq `admit` (memory-growth bound) lives in `construct_meminsts_grow`.
  * TypePreservation: linear chain `zero_is_well_formed`/`num_default(_is_well_formed)` -> `inst_t_context_*_empty` ->
    `t_preservation_vs_type'` -> `t_preservation_vs_type` -> `store_extension_reduce` -> `reduce_inst_unchanged` ->
    `t_read_preservation` -> `step_moduleinst` -> `t_preservation_type` -> `t_preservation` (pure composition).
- Sec.3 (l.341-355): `minst_invert_tables/_mems` need `limits_sub_refl`, `limits_sub_trans`, `externtype_sub_refl/_trans`,
  `externtype_global_eq`, `externtype_func_eq` which did not exist in Rocq then (bundle3: now they do).

### 3.2 bundle2 `proof_prioritization.md` (353 lines) - historical, superseded by #10, #13, #15

- Weighting: dependencies (hard), ease, importance (unblocks most), others (free reuse jumps the queue; mirror the Rocq author's
  order; "close a file" motivation; deliberately-permanent gaps = SIMD at that time).
- Tier A done-list (13 Subtyping + ExtensionLemmas refl family). Tier B #1-10 (easy/independent: `instr_subtyping_strengthen2`;
  HelperLemmas tier-0 cluster; `inst_match` cluster; wf-projection lemmas; context-update lemmas; seq-typing inversions (#6, "highest-value");
  `Store_ok`/`Extend_store` inversions; ExtensionLemmas tiers 3+10 (#8); `construct_*` typing lemmas; tier-7 `construct_ai_*`).
  Tier C #11 `instr_of`, #12 `ai_principal_typing` ("single most important piece of remaining structural work", pure transcription).
  Tier D #13-16 inversion lemmas + `Vals_ok` family (`construct_ais_vals` last). Tier E #17-19: 28 `Step_pure` lemmas in Rocq file order
  (nop/drop trivial -> select/if medium -> label_vals/br_zero -> br_succ/br_table_lt/ge hardest three -> frame_vals/return_label ->
  unop..cvtop_val -> local_tee -> ref_is_null_*); **#18 "make a real, dedicated attempt at `Step_pure__return_frame_preserves`"**
  (Rocq proof existed once, lost in the July-1 `Admin_instrs_ok` -> `Instrs_ok2` rename repair); #19 `t_pure_preservation` last.
  Tier F #20-27: `limits_sub`/`externtype_sub` cluster (`limits_sub_refl`, `limits_sub_trans`, `functype_sub_eq`, `globaltype_sub_eq`,
  `externtype_sub_refl/_trans`, `externtype_global_eq`, `externtype_func_eq`), `minst_invert_*`, #22 resolve `funcinst_same`
  (zip-based `Forall₂` does not force equal length: needs an added length hypothesis or another strategy; "flag any recurrence for a
  shared lemma"), `addrs_*`, assembly lemmas, `store_extension_ais`, #27 `construct_meminsts_grow` arithmetic gap
  (`TODO - Find some way of showing lim_old + v_n <= 2 ^ 16`; idea: bound may just restate an existing hypothesis).
  Tier G #28-35 TypePreservation. Tier H #36 re-sync Rocq checkout (not done by that session: "would mean modifying files outside
  `spectec/src/test-lean-claude/`, outside this project's safety boundary without explicit user authorization"), #37 port `type_progress.v`.

### 3.3 bundle2 `rocq_proof_intuition.md` (513 lines) - mostly still valid background

- Goal: type safety = preservation (`t_preservation`, type_preservation.v) + progress (`t_progress`, type_progress.v).
- Author `DCupello1`/`DCupello`, 33 commits 2026-03-10..2026-09-22. Staging dir `spectec/test-rocq/folder-to-exclude/` (no dune file ->
  skipped by Dune); a file in `theories/` is a claim that it compiles.
- Graduation table: helper_tactics/helper_lemmas/subtyping 2026-03-10 "Port proofs from wasm2.0, works up to subtyping file.";
  typing_lemmas 2026-04-13; type_preservation_pure 2026-04-22; extension_lemmas+axioms 2026-04-28 "Wasm 2.0 store extension done";
  type_preservation 2026-05-04, demoted 2026-07-29 "Preservation in progress", re-promoted 2026-08-24 "Type preservation basically done
  (without wfness lemmas done)", "Removed some admits, only one left" 2026-08-27, vector work 2026-09-22; type_progress 2026-09-21.
- July-1 break: `Admin_instrs_ok` silently renamed to `Instrs_ok2` (June "Update rocq output" commits); commits `dac300994` "Repaired
  typing lemmas", `5b03ae067` "Repaired preservation pure (except return frame)"; `typing_lemmas.v` got new `instr_ok_context_wf`,
  `ainstr_ok_context_store_wf`, `instrs_ok_context_wf`. `Step_pure__return_frame_preserves` proof commented out -> bare `Admitted.`
  Lesson: "When a file that built cleanly yesterday suddenly doesn't, check for a rename first before assuming a logic error."
- Context: first commit seeded from a private "wasm2.0" proof; PR #222 "[IL Semantics] Meta-theory in rocq" (Rossberg fixed two spec
  bugs reported by the mechanisation); PR #207 "Rocq backend" (tracking, "Not meant to be merged"). Takeaway: if a generated
  definition looks flatly wrong, check whether it is a known spec/generator bug before working around it silently.
- Per-file intuition (see section 6): helper_lemmas = mathcomp-`seq` vs stdlib-`List` bridging (no Lean counterpart; many become
  `simp`/`omega`); subtyping = frame-rule algebra, `Valtype_sub` has exactly two cases (refl, BOT <= everything), `instrtype_sub` is an
  existential-split formula (not inductive); typing_lemmas = one big `ai_principal_typing` + two soundness theorems
  (`instr_typing_inversion`, `ai_typing_inversion`), naive seq-lemma is false (typing_lemmas.v:1080 is the correct form);
  type_preservation_pure = one lemma per rule; extension_lemmas = `Extend_store`, main content written in commit `+1816/-1073`
  2026-07-22 "extension lemmas done - except meminst grow", admit near extension_lemmas.v ~3026; axioms.v = escape hatches with
  spec-level explanatory comments, grew `+32/-0` on 2026-09-22 (five SIMD-support axioms `vbytes_len'`, `ibytes_len''`, `truncz_quot`,
  `lanes_len` + inverse-bijection axioms for `nbytes_`/`ibytes_`/`vbytes_`); type_preservation = assembly; type_progress = 30+ TODOs,
  6 `admit`s, all traced to the `lane_` union encoding (quote in section 6, T14).
- Synthesis items 1-8 (l.469-513): keep dependency order; Step_pure is the easiest substantial chunk; expect `wasm2.0.lean` to change
  by renames; return_frame sorry "plausibly tractable"; memory-growth bound is ordinary arithmetic; SIMD/lane gaps may be generator-level;
  fetch and port type_progress.v.

### 3.4 bundle3 `proof_dependencies_addendum.md` (63 lines)

- Six-file chain unaffected by the resync. `type_progress.v` is a 7th file PARALLEL to Preservation: its `Require Import` list is `wasm`,
  `helper_lemmas`, `helper_tactics`, `typing_lemmas`, `extension_lemmas`, `subtyping`, `axioms`; no import of `type_preservation(_pure)`.
  So TypePreservationPure->TypePreservation and TypeProgress can proceed in parallel. New vector lemmas
  (`Step_pure__v*_preserves` <- `ais_v*_typing_inversion`; vload/vstore lemmas) follow the existing pattern. Within type_progress.v:
  layer 1 list plumbing, layer 2 `typeof`/`invert_typeof_*`, layer 3 br/return machinery (needed before `t_progress_e`), layer 4 numeric
  totality (needs layer 2); `call_indirect_progress`, `t_progress_be` need layers 1-4; `t_progress_e` needs `t_progress_be`+layer 3;
  `t_progress` needs `t_progress_e`.

### 3.5 bundle3 `proof_prioritization_addendum.md` (126 lines)

- Tier A names stale -> do a rename pass over ExtensionLemmas.lean names first (not proofs). Tier B #2: `leadd`, `length_app_lt`,
  `add_false` removed upstream (drop from targets). `Val_ok_store` and `funcinst_same` removed upstream with no direct replacement (read the
  new `Extend_store_val/_vals/_funcinst/_ref` proofs). Tier C/D unaffected (typing_lemmas.v lost the `fun_*idx__nat` family, gained
  `construct_instr_from_ai*`/`revert_to_*`). Tier E reframed: ~20 new fully-proved `Step_pure__v*_preserves` lemmas -> propose Tier E2
  (port each `ais_v*_typing_inversion` + `Step_pure__v*_preserves` pair, then `t_pure_preservation` dispatch), `t_pure_preservation`
  moves after E2. Tier F: `limits_sub`/`externtype_sub` cluster now has real Rocq statements; `construct_meminsts_grow` was the single
  remaining Preservation-side gap upstream, new helpers `pagediv`, `pagediv_ge_0/_Z`, `update_holds_upto_le/_lt`, `holds_upto_*`,
  `Qfloor_add_Z` added (author's partial progress). Tier H #36 done, #37 unblocked -> new Tier I (port type_progress.v; sequence:
  list plumbing -> `typeof`/`invert_typeof_*` -> numeric totality -> br/return -> `call_indirect_progress` -> `t_progress_be`
  [skip/sorry the 5 SIMD sites] -> `t_progress_e` -> `t_progress`), parallel to E/F/G. Suggested revised ordering 1-8 at l.110-126.

### 3.6 bundle3 `resync_impact_report.md` (275 lines) - the master resync document

- Sec.1: verification that the user's merge `b78d56eeb` (merges `26d40070b` with `a8b585cdb`) was correct: `gh api repos/Wasm-DSL/spectec/branches/
  rocq-backend-proof --jq '.commit.sha'` = `a8b585cdb536b2b2e53ff45fa8010de88f05a042` (second parent, still tip); no conflict markers in
  `spectec/test-rocq/theories/`, `spectec/src/backend-rocq/`, `spectec/src/frontend/elab.ml`, `spectec/src/middlend/typefamilyremoval.ml`,
  `specification/wasm-2.0/`; only untracked `spectec/test-rocq/_CoqProject`, `test-rocq.opam`. The user's instruction was "if not, stop here and report".
- Sec.2: reading `spectec/test-rocq/theories/` IS reading the repo; the problem was only that the local copy lagged the live branch. Repeat the
  `gh api` check whenever in doubt; user said to prioritise the live GitHub source.
- Sec.3a SIMD Preservation gap CLOSED upstream: `Admitted` count `type_preservation_pure.v` 2 -> 0, `type_preservation.v` 3 -> 0.
  `type_preservation_pure.v` 29 -> 76 declarations (new `ais_v*_typing_inversion`/`Step_pure__v*_preserves` for vbinop, vunop, vrelop,
  vtestop, vshiftop, vbitmask, vsplat, vextract_lane, vreplace_lane, vcvtop, vextunop, vextbinop, vnarrow, vswizzle, vshuffle, vvunop,
  vvbinop, vvternop, vvtestop; helpers `const_result_typing`, `vconst_result_typing`, `vec_preserves_1/2/3`). `type_preservation.v` 13 -> 37
  (`ais_vload_typing_inversion`, `ais_vload_lane_typing_inversion`, `Step_read__vload_preserves`, `Step_read__vload_lane_preserves`,
  `ais_vstore_typing_inversion`, `ais_vstore_lane_typing_inversion`, `Step__vstore_preserves`, `Step__vstore_lane_preserves`,
  `vec_store_preserves_2`, `mem_store_extension`, `wf_context_*`, `wf_store_mem_update*`, `wf_*insts_preserves`). NOTES.md item "e.
  Deliberately-kept gaps (mirror Rocq, do not 'fix')" became wrong for SIMD.
- Sec.3b rename table (old -> new Rocq name): `store_extension_refl` -> `Extend_store_refl`; `func/table/mem/global/elem/data_extension_refl0|refl` ->
  `extend_funcinst_refl_0`/`extend_func_refl`, `extend_tableinst_refl_0`/`extend_table_refl`, `extend_meminst_refl_0`/`extend_mem_refl`,
  `extend_globalinst_refl_0`/`extend_global_refl`, `extend_eleminst_refl_0`/`extend_elem_refl`, `extend_datainst_refl_0`/`extend_data_refl`;
  `store_extension_ais` -> `Extend_store_ais`; `_moduleinst` -> `Extend_store_moduleinst`; `_funcinst/_globalinst/_tableinst/_meminst` (+lists) ->
  `Extend_store_*`; `store_extension_ref/_refs/_val/_vals` -> `Extend_store_ref/_refs/_val/_vals` (+new `_refs'`); `_exts/_eleminst/_eleminsts(')/
  _datainsts(')` -> `Extend_store_*`; `_externaddrs_func` -> `Extend_store_externaddrs_func`; `Val_ok_store`, `funcinst_same` removed.
  New: `limits_sub_refl/_trans`, `externtype_sub_refl/_trans`, `externtype_func_eq/_global_eq`, `Externaddr_invert_funcs/_globals/_mems/_tables`,
  `holds_upto_*`, `update_holds_upto_*`, `pagediv*`, `iota_snocN`, `nth_iotaN`, `size_iotaN`, `repeat_forall`, `Qfloor_add_Z`, `Zle_Nle`,
  `list_update_func_subst/_unchanged`, `forall_preserved_bytes`, `invert_meminst`.
- Sec.3c `extension_lemmas.v` had exactly 1 `Admitted`: `construct_meminsts_grow` (the `lim_old + v_n <= 2^16` bound).
- Sec.3d `type_progress.v` arrived: 4260 lines (3131-line staging draft existed at the old commit), 108 top-level Lemma/Theorem, exactly 1
  `Admitted` (`t_progress_be`, 5 internal `admit.`), imports as in #4. All 5 sites are the `lane_`-union obstacle per the author's comments;
  **one (a "VLOAD + oversized SPLAT memarg" case) "reads more like a possible under-constrained typing rule than a proof-tactic gap"**
  (flagged for a closer look). Advice: check early whether Lean's `lane_`/`Jnn` encoding in wasm2.0.lean collapses the same way.
- Sec.3e: `axioms.v` 2 -> 9 axioms (`nbytes_len`/`ibytes_len` byte-identical; the report says "7 new" but lists 9 names: `nbytes_len'`, `ibytes_len'`,
  `ibytes_len''`, `vbytes_len'`, `truncz_quot`, `lanes_len`, `nbytes_inv`, `ibytes_inv`, `vbytes_inv`). `helper_lemmas.v` 850 -> 657 lines, 63 -> 53
  decls; removed 24 (`add_false`, `concat_cancel_last_n`, `Forall2_forall2`/`weak`/`weak2`/`weak3`/`weak4`, `Forall2_list_update`/`2`/`_both`/`_func`,
  `Forall2_lookup`/`2`, `Forall2_nth`/`2`, `Forall_nth'`, `leadd`, `length_app_lt`, `list_update_func_split`/`_strong`, `list_update_map`,
  `lookup_list_update_func`, `lt_irrefl`, `ltsize`, `repeat_size`), added 14 (`add_subBN`/`'`, `append_label`/`_local`/`_return`, `cvt_succ`/`'`,
  `Forall2_seq_size`/`_size`/`_size2`, `id_succ_N`, `prepend_local`/`_return`, `sizecat'`, `sizeN_inj`). `subtyping.v` purely additive
  (`cvt_N_to_ssrnat`, `cvt_ssrnat_to_N_le`, `size0nil'`). `typing_lemmas.v` 2222 -> 2384 lines: removed the 14-lemma `fun_*idx__nat`/`fun_nat__*idx`/
  `fun_u32__nat`/`fun_nat__u32` family; added `ai_typing_inversion'`, `construct_instr_from_ai`/`_single`, `construct_instrs_from_ais`,
  `revert_to_instr_from_ai`/`_instrs_from_ais`, `seq_mid_not_null`, `wf_admininstr_instr`. `helper_tactics.v` Ltac not ported 1:1 by convention.
  `wasm2.0.lean` was NOT touched by this merge.
- Sec.5 safety: all via read-only git/gh/grep/wc/awk on scratch copies under `/tmp/rocq_diff/`; writes only under `claude-logging/`.

### 3.7 bundle3 `rocq_proof_intuition_addendum.md` (43 lines)

- Still holds: staging-dir workflow, `lane_`-union diagnosis (now confirmed by type_progress.v's own `admit.` comments), build order.
  Correction: SIMD gaps no longer span Preservation (zero `Admitted` upstream); "it is only Progress (`t_progress_be`) where the gap remains".
  "SIMD Preservation is real, portable work; SIMD Progress is the one place a faithful `sorry` is still justified" (pending the Lean-encoding check).

### 3.8 bundle8 `vals_ok_non_bot_analysis.md` (147 lines)

- Shows that the generated `Forall₂ P xs1 xs2 := ∀ t ∈ xs1 |>.zip xs2, P t.1 t.2` is vacuous on the tail of the longer list, so
  `Vals_ok_non_bot` as first stated (`Forall₂ (fun t v => Val_ok S v t) ts vals -> Forall (· ≠ BOT) ts`) is FALSE (`ts = [BOT]`, `vals = []`).
  Rocq's inductive `Forall2` implies equal length. Same phenomenon as `funcinst_same`. `ais_vals_typing_inversion` and `construct_ais_vals`
  inherit it (Rocq's induction keeps the lists in lockstep). Options: (1) add `hlen : v_ts.length = v_val.length` to the theorem; (2) bake the
  length into `Vals_ok` (`v_ts.length = v_vals.length ∧ Forall₂ ...`); (3) bridge to Mathlib `List.Forall₂` (`to_mathlib_forall₂` /
  `from_mathlib_forall₂`, prior file `spectec/test-lean/typing_lemmas.lean` lines 15-26, via `List.forall₂_iff_zip`); (4) patch statements lemma by lemma.
  Suggestion: start with (1), switch to (2) if length threading becomes a recurring tax. Not acted on in bundle8 (user: leave it be).
  Mathlib context: `import Mathlib.Tactic` added to TypingLemmas.lean for the `ai_principal_typing` port; prebuilt oleans via `lake exe cache get` (~6.4 GB).

### 3.9 bundle9 `proof_dependencies_v2.md` (117 lines) - consolidated, superseded by #14

- Rocq checkout current at `58af2e2f9`. Status table (grep 2026-09-30): HelperLemmas ~53 decls/29 sorry; Subtyping ~45/32; TypingLemmas ~90/13;
  TypePreservationPure ~29/27; ExtensionLemmas ~85/79; TypePreservation ~13/12. `ai_principal_typing` done; new bottleneck `instr_of`
  (`TypingLemmas.lean:105`, plain `def`, blocks `construct_ai_maybe` (l.1202) and indirectly `ais_vals_typing_inversion`/`construct_ais_vals(')`).
  Dead lemmas (no longer in Rocq, unreferenced): `leadd`, `list_update_func_split*`, `length_app_lt`, `Forall_nth'`, `Forall2_nth`/`_lookup`,
  `lookup_list_update_func`, `In2_split`, `Forall2_forall2*` (5), `Forall2_list_update*` (5), `add_false`, `concat_cancel_last_n`, `ltsize` = 22 of the 29
  HelperLemmas sorries.

### 3.10 bundle9 `proof_prioritization_v2.md` (210 lines) - consolidated, superseded by #13/#15

- Tier A done list (HelperLemmas 18 incl. `length_same_split_zero`, `length_app_both_nil`, `length_app_nil`, `split_append_last/_1/_2/_left_1`,
  `empty_append`, `option_orElse_*`, `add_sub/'`, `sizecat_le1/_le2`, `drop_size_cat/take_size_cat`, `size_eq_cat`; TypingLemmas ~77 across bundles 5-9).
  Tier B `instr_of`; Tier C remaining TypingLemmas items (l.676-708 `*_single_typing_inversion` family, `split_single_append`, `val_ref_null_is_ref`,
  `ai_val_principal_typing_inversion` l.1084, `construct_ai_maybe`, `ais_vals_typing_inversion`, `construct_ais_vals(')`); Tier D 27 TypePreservationPure
  lemmas (`proj_identity` first for the `br_*` cluster); Tier E ExtensionLemmas (79 sorries, independent track); Tier F TypePreservation (12);
  Tier G type_progress (deliberately after B-D; "treat `t_progress_be`'s 6-8 remaining lane-op admits the same way Tier D treats SIMD").
  Rule: "Free reuse always jumps the queue - check `spectec/test-lean/` and `spectec/test-lean/test-lean-claude/` before deriving anything from scratch."

### 3.11 bundle9 `rocq_changes_summary.md` (161 lines) - upstream delta `a8b585cdb` -> `58af2e2f9`

- Tip `58af2e2f9135fcee4cd1aaf9c94695007910fb2f` "Some more cases done" (DCupello, 2026-09-24T11:55:57Z) = already merged (`868bca93f`). Diff only
  `type_progress.v` (318 changed lines) and `wasm.v` (43 changed lines); total 343 insertions, 18 deletions; nothing in test-lean-claude changed; no update needed.
- `type_progress.v`: `t_progress_be` VUNOP proved (3 new lemmas `vunop_real`, `vunop_total`, `vunop_not_none`, ~110 lines; sidesteps the `lane_` ambiguity
  by splitting on Jnn vs Fnn up front; `vunop_not_none` keeps ONE internal `admit.` "not derivable as stated"); VTESTOP proved directly (the reduction
  has a catch-all `~ Step_pure_before_vtestop_false`, so no need to pin the `lane_` injection). Remaining admitted: VBINOP, VRELOP, VSHIFTOP, VBITMASK,
  VSWIZZLE, VSHUFFLE (7 textual `admit.` in file; `N-M: admit.` selector counts several goals). Helper lemmas added: `Forall_all`/`all_Forall`,
  `all_and_Forall`/`Forall_and_all`, `Forall_exists_Forall2`, `Forall2_size_eq`.
- `wasm.v`: one wf_uN-bound lemma (unsigned remainder case) now `Qed` via new helper `Hrem`. Five (text) / six (table) new comments at existing
  `Admitted`/`admit.` sites say "Mechanised: `<name>` in `wf_counterexamples.v`": `fone_is_wf_false` (N=7 counterexample, inverse direction of `fone_is_wf`),
  `utf8_is_wf_false` (wf_byte/UTF-8 admit), `Step_pure_is_wf_false` (VBITMASK `Step_pure` admit), **`Step_read_is_wf_false` (described as "the packed-load
  `Step_read` admit")**, `runelem_is_wf_false` (RUNELEM/element-init `wf_instr`), `rundata_is_wf_false` (RUNDATA/data-init `wf_instr`). `wf_counterexamples.v`
  did not exist anywhere on GitHub (forward reference to an unpushed local file); recommended asking the Rocq author for it; none of the 6 Lean files used these.

### 3.12 bundle9 `vals_ok_non_bot_resolution.md` (128 lines)

- User decision (verbatim in doc): Option 2 as baseline, Option 3 for ergonomics. Implemented: `import Mathlib.Tactic` in HelperLemmas.lean;
  `to_mathlib_forall₂` (needs `hlen`) and `from_mathlib_forall₂` (no hlen) in a "`Forall₂` bridge" section at the end of HelperLemmas.lean
  (both via `List.forall₂_iff_zip`); `def Vals_ok S vals ts := ts.length = vals.length ∧ Forall₂ (fun t v => Val_ok S v t) ts vals`; call sites
  (`ExtensionLemmas.lean:508`, `TypePreservation.lean:60,61,69,70,123`, `ais_vals_typing_inversion`/`construct_ais_vals`) were all `sorry` so nothing broke.
  `Vals_ok_non_bot` restated through `Vals_ok` (documented deviation under the "obvious optimizations" allowance); Rocq source `typing_lemmas.v:2071`
  at `58af2e2f9` (an older digest said `:1927`). Full proof text in section 6, T2. Build exit 0, 3005 jobs. `grep -c sorry` went 17 -> 15 because a doc
  comment also contained the word. NOT done: dead `Forall2_*` family (same gap, removed upstream); `funcinst_same` not revisited.

### 3.13 bundle12 `proof_prioritization_v3.md` (128 lines) - TypePreservationPure only

- `TypePreservationPure.lean` real-sorry count 29 -> 20 (bundle11) -> 11 (bundle12). Done: `nop`, `drop`, `if_preserves_helper` (+ `if_true/false`),
  `label_vals_preserves`, `br_if_true_preserves`, `br_if_false_preserves`, `proj_identity`, `unop_val`, `binop_val`, `testop`, `relop`, `cvtop_val`, `local_tee`,
  `ref_is_null_helper` (+ `_true/_false`). Two more Phase-1 signature bugs fixed: `testop`/`relop` stubs lacked `wf_admininstr (admininstr.CONST numtype.I32
  v_c) ->` (needed for `wf_num_` of the synthesised boolean; otherwise unprovable). Remaining 9 targets in order: `frame_vals`, `return_label`, `br_zero`,
  `select_preserves_helper` (+ `select_true/false`; reclassified HARD), `br_succ`, `br_table_lt`, `br_table_ge`; plus the 2 "permanent gaps"
  `return_frame_preserves`, `t_pure_preservation` (this doc says they mirror Rocq `Admitted`; see section 5, O1: that is WRONG after `a8b585cdb`).

### 3.14 bundle13 `proof_dependencies_v3.md` (75 lines)

- Status table 2026-09-30 post-resync: HelperLemmas 63/28 sorry; Subtyping 46/0; TypingLemmas 81/0; TypePreservationPure 30/11; ExtensionLemmas 92/76;
  TypePreservation 13/12; "Total 351 declarations, 127 sorry" (the six rows sum to 325, not 351; 127 is right). TypePreservation's "3 of 12 are
  deliberate permanent gaps (`store_extension_reduce`, `t_read_preservation`, `t_preservation_type`, all Rocq `Admitted` for SIMD reasons)" - stale/wrong
  (O1). HelperLemmas 3 axioms `nbytes_len`/`nbytes_len'`/`nbytes_inv` resynced for `nbytes_` totality. Dead cluster unchanged (22 of 28).

### 3.15 bundle13 `proof_prioritization_v4.md` (92 lines)

- Status update: `frame_vals_preserves` proved (as predicted, same trick as `label_vals`); `return_label_preserves` deferred (Rocq proof more involved: needs
  `RETURN`'s principal typing reconciled with `v_C.RETURN` via `resulttype_sub_app`-style reasoning). Order: return_label -> br_zero -> select -> br_succ -> br_table_lt/ge.
  `construct_meminsts_grow` newly a genuine target but "not low-hanging fruit" (needs `s.MEMS.length = ts.length`-style reasoning for zip-based `Forall₂`;
  comparable to `br_succ`). Then start ExtensionLemmas in earnest (simple `Extend_store_*` monotonicity lemmas first, `Extend_store_ais` "THE big monotonicity
  theorem" and `construct_meminsts_grow` last), then TypePreservation. A signature fix can re-baseline a lemma's difficulty. Convention: "leave it be and reassess
  in your new bundle".

### 3.16 bundle13 `rocq_changes_summary_v2.md` (228 lines) - merge of `rocq-backend-proof-final`

- Merge `8ac6699ac`; diff `da555377a..95c256c2c`, 15 files +8249/-3961: 1-syntax/3-numerics/8-reduction .spectec (SIMD restructuring: `vloadop`,
  `vextunop_`/`vextbinop_`, `vcvtop` indexed by shape pairs; `VEXTUNOP`/`VEXTBINOP`/`VCVTOP` argument order swapped; three `Step_pure/vcvtop-*` rules collapsed to one),
  5-runtime-aux (`$growmemory` new side condition `-- if i' <= $(2^16)`), B-soundness (`Datainst_ok`/`Eleminst_ok`: `|b*| < $(2^32)` / `|ref*| < $(2^32)`),
  C-hints (163), print.ml (12), undep.ml (197), axioms.v (45), extension_lemmas.v (59), type_preservation.v (25), type_preservation_pure.v (16),
  type_progress.v (1853), typing_lemmas.v (6), wasm.v (9623) (numbers = changed lines per the doc's diffstat). The session declared the Lean ports SIMD-free (grep found no SIMD names) - no longer true.
- Real build break: byte-encoding opaques `nbytes_`/`ibytes_`/`fbytes_`/`vbytes_` became TOTAL (`List byte`, not `Option (List byte)`) because of commit
  `853b8863c` "Made wfopt be an optin hint for functions" (2026-09-28; C-hints.spectec + undep.ml): a function gets an `Option` result only if hinted `wfopt`.
  HelperLemmas.lean axioms `nbytes_len`, `nbytes_len'`, `nbytes_inv` had `nbytes_ ... ≠ none` guards + `Option.get!` -> 5 lake errors; fixed by dropping the guard and
  `Option.get!` for `nbytes_` only (`size` stays `Option Nat`). Build then clean.
- `construct_meminsts_grow`: Rocq now `Qed`; added Lean hypothesis `lim_old + v_n ≤ 2 ^ 16` (Nat); proof left `sorry` (Rocq's `Q`/`Z` route has no Lean analogue; zip-based
  `Forall₂` forbids Rocq's structural induction without `s.MEMS.length = ts.length`). Noticed pre-existing: Lean hard-coded the maximum as `some (uN.mk_uN v_j)`
  where Rocq has `v_j_opt : option u32` -> fix when proving.
- `axioms.v` new axioms: `ibits_inv`, `feq_bit`/`fne_bit`/`flt_bit`/`fgt_bit`/`fle_bit`/`fge_bit`, `ishl_wf`/`ishr_wf`, `trunc_sat_total`/`demote_nonempty`/
  `promote_nonempty` (the doc says "9 new" but names 12). All consumed exclusively inside `type_progress.v` (lines 1687-4306: `ishl_wf`/`ishr_wf` for I64 shift totality,
  `feq_bit`..`fge_bit` for float RELOP wf, `trunc_sat_total` etc. for CVTOP totality) so none were added to HelperLemmas.lean then.
  `Datainst_ok`/`Eleminst_ok` bounds appear automatically in regenerated wasm2.0.lean (~l.14204-14225: `List.length b_lst < 2^32`, `List.length ref_lst < 2^32`); matter for the
  proofs of `construct_datainsts`/`construct_eleminsts`. `wf_admininstr_instr` tactic-only change; Lean ports it as `instr_of_admininstr_instr` with proof `cases i <;> rfl`.
  `type_preservation_pure.v`: helper arg types renamed (`wasm.vextunop_` -> `wasm.vextunop__`, `wasm.vcvtop` -> `wasm.vcvtop__`), `t_pure_preservation` dispatch
  renumbered (`24: ... local_tee` -> `22:`; three `vcvtop_preserves` bullets -> one).
- wasm2.0.lean regeneration verified byte-for-byte: `_build/default/src/exe-spectec/main.exe <all 12 wasm-2.0 .spectec files in order> --lean -o <scratch file>`; the `--lean`
  target auto-enables the passes `HandleExplicitIgnores`, `Sideconditions`, `Totalize`, `Else`, `TypeFamilyRemoval`, `Undep`, `Uncaseremoval`, `Sub`, `SubExpansion`, `ImproveIds`,
  `AliasDemut`, `DefToRel`, `Ite`, `ElseSimp`, `PatSimp`, `LetIntroMech`; `diff` against committed `spectec/src/test-lean-claude/wasm2.0.lean`: zero lines (both 14760 lines).

### 3.17 bundle13 `signature_audit_v1.md` (133 lines)

- Manual hypothesis-by-hypothesis audit of ~260 cited declarations (of ~325): 12 mismatches, 20 orphaned citations; `Subtyping.lean` and `TypePreservationPure.lean` clean.
  Mismatches (Lean location at that time -> fix):
  1 `HelperLemmas.lean:192-194` `list_slice_update_length` extra hypothesis `n = l'.length` (Lean `list_slice_update` at `HelperLemmas.lean:45-46` is take/append/drop, Rocq's
    `wasm.v:66-74` is recursive/early-stopping; target `(list_slice_update l i n l').length = l.length`).
  2 `ai_principal_typing` GLOBAL_SET (`TypingLemmas.lean:376-377`): must be exactly `some MUT` (Rocq `typing_lemmas.v:498-501`; `Instr_ok` `global_set` at `wasm.v:15041-15046`).
  3 `ai_principal_typing` RETURN (`:353-354`): missing 3rd conjunct `Instr_ok v_C RETURN ((t++t_lst):->t')` (Rocq `typing_lemmas.v:433-437`).
  4 `ai_principal_typing` FRAME_ (`:446-449`): arity `v_n` discarded; needs 4th conjunct `ts.length = v_n` (Rocq `:614-619`).
  5 packed STORE (`:418-421`): Lean stricter (requires Inn); current Rocq's F32/F64 exclusion arms are COMMENTED OUT (`typing_lemmas.v:562-563`) while `Instr_ok`'s `store_pack` is typed
    `(v_Inn : Inn)` (`wasm.v:15176-15183`) -> Rocq's `ai_principal_typing` is inconsistent with its own `Instr_ok`; NO Lean change, report upstream.
  6-9 missing first hypothesis `wf_config (config.mk_config (state.mk_state ..) ..)` in `store_extension_reduce` (Rocq `type_preservation.v:437-444`), `t_read_preservation` (`:1661-1669`),
    `step_moduleinst` (`:3120-3128`), `t_preservation_type` (`:3137-3148`); `wf_config` is a real predicate (`wasm2.0.lean:11029` then).
  10-12 hard-coded `some (uN.mk_uN v_m)` maximum in `s_invert_mems` (Rocq `extension_lemmas.v:106-116`), `s_invert_tables` (`:175-187`), `memory_grow_mem_extension` (`:1753-1768`);
    Rocq uses `Option N`/`option_map`/`option_to_list`; fix: bind `v_m : Option Nat`, route through `v_m.map uN.mk_uN` and `Forall (...) v_m.toList`.
  Orphans: HelperLemmas 19 (`leadd`, `list_update_func_split(_strong)`, `length_app_lt`, `Forall2_nth(2)`, `Forall2_lookup(2)`, `lookup_list_update_func`, `Forall2_forall2`, `Forall2_forall2weak/2/3/4`,
  `Forall2_list_update_func` (alpha direction), `Forall2_list_update`/`2`/`_both`, `add_false`, `concat_cancel_last_n`, `ltsize`); TypePreservation 1: `num_default_is_well_formed`
  (`TypePreservation.lean:45` cites `type_preservation.v:28`, but the Rocq lemma is entirely commented out at `type_preservation.v:74-84`, so the file header's "everything else is `Qed` in Rocq" was inaccurate).
  Out of scope: SIMD (VCONST and the `_ => True` catch-all of `ai_principal_typing`; `vbytes_len'`, `vbytes_inv`, `lanes_len`), type_progress.v, undocumented plumbing.
  Safety section: ran `claude-logging/safety-checks/check.sh` at 20260930T145632Z; many out-of-tree dirty files (`spectec/test-lean/todaywasm*.lean`, `spectec/wasm{1,2,3}.0*_ast_*.il`,
  `spectec/diegowasm*.lean`, `spectec/check_wasm2.0.*`, `spectec/test-rocq/_opam/`, `specification/bleh/`) shown to be pre-existing via `find ... -newermt '-30 minutes'` returning zero matches.

## 4. Standing instructions / rules recorded in these files

(S1-S17 are also returned in the structured output; wording kept close to the sources.)

- S1 SAFETY: never modify anything outside `spectec/src/test-lean-claude/` (bundle2 #2 Tier H #36 "outside this project's safety boundary without explicit user authorization"; bundle3 #6 sec.5; bundle13 #17
  safety section). Run the programmatic check periodically, log under `claude-logging/safety-checks/`. bundle13 technique: for pre-existing out-of-tree dirt, prove non-attribution with
  `find <path> -newermt '-30 minutes'` and by listing the session's own tool calls (only Read + read-only Bash outside the dir).
- S2 "Do not edit previous bundles" (bundle3 addenda: "Do not edit that file"; bundle9 #9: "kept, untouched, as historical record - do not edit them"; bundle12 #13: "the project's standing 'don't edit
  previous bundles' rule"). New knowledge goes in a new addendum / `_vN` document in the new bundle.
- S3 Lemma-for-lemma fidelity: "signatures must be directly from the Rocq proof" (bundle3 #6 sec.3b), "the project's 'lemma-for-lemma' mandate" (sec.3e); but the original task allows a different proof strategy
  (sec.3d). Deviations only as documented "obvious optimizations" for representational gaps (inductive `Forall2` vs zip-based `Forall₂`; `Extend_*` `wf_*` hypotheses; `holds_upto`; `Nat` for `N`/`Q`)
  (bundle9 #12) and they must be recorded in the lemma's doc comment (the bundle13 audit does not flag documented deliberate deviations).
- S4 Convention (implied by the audit's scoping rule, bundle13 #17): put a doc comment "Rocq `<file>.v[:line]` `<name>`" on every ported declaration; the audit only checks cited declarations, so uncited ones escape verification.
- S5 Prefer the live GitHub source of `rocq-backend-proof`; cheap read-only check `gh api repos/Wasm-DSL/spectec/branches/rocq-backend-proof --jq '.commit.sha'`; cross-check with `curl` on the REST API because
  `gh` sometimes goes silent (bundle3 #6 sec.2; bundle9 #11).
- S6 Resync verification procedure the user asked for (bundle3 #6 sec.1): merge parent equals live tip; no conflict markers in `spectec/test-rocq/theories/`, `spectec/src/backend-rocq/`,
  `spectec/src/frontend/elab.ml`, `spectec/src/middlend/typefamilyremoval.ml`, `specification/wasm-2.0/`; `git status --porcelain` on those; "if not [correct], stop here and report".
- S7 Regeneration verification (bundle13 #16): regenerate to a SCRATCH file with the exe and `diff` against the committed `wasm2.0.lean`; never touch the real file while checking.
- S8 User decision on `Vals_ok`: Option 2 baseline + Option 3 bridge (bundle9 #12, verbatim quote).
- S9 `wasm2.0.lean` is maintained by the user's parallel `*_is_wf` audit effort (bundle2 #3 l.138-141, bundle3 #6 sec.3e, bundle9 #11); expect it to change, including by renames; `is_wf_theorems.md` tracks it.
- S10 Operating constraint "may be interrupted" (bundle3 #4): keep work in resumable, individually-building units.
- S11 Convention "leave it be and reassess in your new bundle" for anything harder than expected (bundle13 #15); keep a `NOTES.md` entry per bundle.
- S12 Free reuse first: check `spectec/test-lean/` and `spectec/test-lean/test-lean-claude/` (e.g. `typing_lemmas.lean`, `SeqTypingInversion.lean`) before deriving anything (bundle9 #10).
- S13 Do not leave half-migrated files wired into the lakefile globs; keep `lake build` clean for finished files (bundle2 #3 sec.2).
- S14 `helper_tactics.v` Ltac is not ported 1:1 by convention (bundle3 #6 sec.3e).
- S15 NOTES.md item "e. Deliberately-kept gaps (mirror Rocq, do not 'fix')" applies only to gaps that still exist in the CURRENT upstream (bundle3 #6 sec.3a said the SIMD part became wrong).
- S16 Record safety-check output after each bundle (bundle3 #6 sec.5).
- S17 NOTE: the repeated "SIMD is out of scope" statements (bundle2/9/13) are superseded by the current task (remove every `sorry`, SIMD included).

## 5. Open issues, contradictions, errors found in the documents

- O1 (important) CONTRADICTION about Rocq `Admitted`s in the preservation files. #6 sec.3a (and #7, #10): at `a8b585cdb` `type_preservation_pure.v` has 0 `Admitted` (was 2) and `type_preservation.v` has 0 (was 3).
  Yet #13, #14, #15, #16 call `Step_pure__return_frame_preserves`, `t_pure_preservation`, `store_extension_reduce`, `t_read_preservation`, `t_preservation_type` "deliberate permanent gaps
  mirroring Rocq `Admitted`" and #16 says `store_extension_reduce` "remains `Admitted` overall (purely SIMD cases)". OBSERVED: the current headers say the opposite and call the older text stale:
  `TypePreservationPure.lean` l.17-21 ("Upstream `type_preservation_pure.v` is fully `Qed` since `a8b585cdb`; the 'two `Admitted` obligations' this header used to list described an older Rocq checkout") and
  `TypePreservation.lean` l.14-25 ("Upstream `type_preservation.v` has **no** `Admitted` lemmas ... modulo the generated `Step_is_wf`/`Step_read_is_wf`"). So bundle12/13's justification for leaving those five as
  `sorry` was wrong; they were all proved in bundle18/19 per those headers.
- O2 Internal count errors in the documents: #6 says "7 new axioms (2 -> 9)" but lists 9 names; #16 says "9 new axioms" but lists 12 names; #11 says "five comments" but the table has six rows; #14 says "351 declarations"
  but its rows sum to 325 (the audit #17 says ~325). Nothing depends on these numbers, but do not quote them.
- O3 Dead-lemma cluster in HelperLemmas.lean (#9, #14, #17): zip-based `Forall₂` makes several statements FALSE as stated (see section 8, X2). #12 left them untouched on purpose ("not worth matching a target that no longer exists").
- O4 `wf_counterexamples.v` (#11): six Rocq `wasm.v` sites claim provable falsity of `fone_is_wf` (N=7), `utf8_is_wf`, `Step_pure_is_wf` (VBITMASK), `Step_read_is_wf` ("packed-load"), `runelem_is_wf`, `rundata_is_wf`; the file was never
  pushed (as of bundle9). Status of the other five after the current upstream change is NOT determinable from these files; only `Step_read_is_wf` is stated (by the task text) to be `Qed` now. If any of the others is still `Admitted`
  upstream and the Lean theorem exists, it may be genuinely unprovable (the "tell the user it cannot be done" case).
- O5 Possible upstream spec bug flagged early (#6 sec.3d): one of the 5 `t_progress_be` admits (a "VLOAD + oversized SPLAT memarg" case) "reads more like a possible under-constrained typing rule". Whether this is the same case as the later
  `VLOAD SHAPE 64x1` stuck case (fixed upstream by `M > 1`) cannot be decided from these files.
- O6 Open upstream bug candidate (#17 finding 5): packed `STORE` in Rocq `ai_principal_typing` (commented-out F32/F64 exclusion arms `typing_lemmas.v:562-563`) is inconsistent with Rocq's own `Instr_ok`; Lean is right, do not "fix" Lean; report upstream.
- O7 `num_default_is_well_formed` has no Rocq statement (commented out at `type_preservation.v:74-84`) - the Lean lemma has nothing to be faithful to (#17).
- O8 `Val_ok_store` and `funcinst_same` were removed upstream with no replacement found (#6, #10, #12, #17); ExtensionLemmas.lean kept `Val_ok_store` as an orphan `sorry`.
- O9 `lane_`-union diagnosis (#3, #7, #11): the three constructors `mk_lane__0/1/2` of generated `lane_` lose the spec-level subtyping, so `proj_lane__2 l <> None` is not derivable from `wf_lane_`; whether Lean's encoding collapses the same way
  was never checked in these files (recommended early check).
- O10 `construct_meminsts_grow` (#16): needs `s.MEMS.length = ts.length`-style length reasoning and the `Option` maximum; `Datainst_ok`/`Eleminst_ok` `< 2^32` bounds must be used when proving `construct_datainsts`/`construct_eleminsts`.
- O11 `Step_pure__return_frame_preserves` (#2 #18, #3): flagged as "plausibly tractable"; #13 deferred it last. (OBSERVED: now proved per the TypePreservationPure.lean header.)
- O12 Graph inconsistency: #1 says Rocq `extension_lemmas.v` imports `type_preservation_pure`; #4/#9/#14 draw ExtensionLemmas as a sibling of TypePreservationPure (only `type_progress.v`'s imports were re-read at the new HEAD). Immaterial for the Lean port.

## 6. Techniques and pitfalls recorded (with the lemma they came from)

- T1 (`Vals_ok_non_bot`, #8/#12) Generated `Forall₂` is zip-based; `Forall₂ P xs ys` is vacuous beyond the shorter list; any Rocq `Forall2` fact used length-sensitively is false/unprovable if transcribed literally. Fix used: length-carrying `Vals_ok`
  + bridge lemmas `to_mathlib_forall₂ (hlen : l1.length = l2.length) (h : Forall₂ R l1 l2) : List.Forall₂ R l1 l2` (`List.forall₂_iff_zip.mpr ⟨hlen, fun hab => h _ hab⟩`) and `from_mathlib_forall₂ (h : List.Forall₂ R l1 l2) : l1.length = l2.length ∧ Forall₂ R l1 l2`.
- T2 (`Vals_ok_non_bot` proof, #12, compiled first try):
  `rintro ⟨hlen, hforall⟩; have h2 : List.Forall₂ (fun t v => Val_ok v_S v t) v_ts v_val := to_mathlib_forall₂ hlen hforall; clear hforall hlen; induction h2 with | nil => intro t ht; simp at ht | cons hval _ ih => intro t ht; rcases List.mem_cons.mp ht with rfl | ht; · exact Val_ok_non_bot v_S _ t hval; · exact ih t ht`.
- T3 Mathlib: `import Mathlib.Tactic` (TypingLemmas.lean bundle8, HelperLemmas.lean bundle9); `lake exe cache get` (~6.4 GB, minutes) instead of compiling Mathlib; Mathlib already a resolved dependency in `lakefile.lean`.
- T4 (`ais_seq_typing_inversion`, `typing_lemmas.v:1080`, #3) The singular-`Instr_ok` head version of the sequence-splitting lemma is FALSE (CONST's rule fixes its input to `[]` so it cannot absorb a shared prefix); state it with the sequence-level `Instrs_ok`/`Instrs_ok2`.
  A prior Lean `instrs_seq_typing_inversion_fixed` (`SeqTypingInversion.lean`) is a complete proof of the `Instrs_ok` version; adapt with `Instrs_ok2`/`Instr_ok2` for the admin version.
- T5 (Step_pure proofs, #13) Two proof shapes: (a) split via `ais_seq_typing_inversion`, take each piece's principal type, recombine with ONE `instrtype_sub_compose*` call, construct the result, widen (nop/drop/unop/binop/testop/relop/cvtop/ref_is_null/if);
  (b) cross a context boundary with `construct_ais_vals'` (`label_vals`, `frame_vals`; `frame_vals` is the `FRAME_` analogue with `LOCALS`/`RETURN`-extended context). `select`, `br_succ`, `br_table_*` fit neither.
- T6 (`select_preserves_helper`, #13) Hard because two independently typed values must be reconciled with a shared slot of a third instruction's principal type: establish an exact (non-subtyping) equality via `Val_ok_non_bot`/`valtype_sub_non_bot` before any composition lemma applies.
  Plan: apply `ais_vals_typing_inversion` to `[val v1, val v2]` as a pair to get ONE `Vals_ok` length-and-`Forall₂` fact rather than inverting each value separately. `if_preserves_helper` is easy: two fixed-shape principal typings, one `instrtype_sub_compose_le` call.
- T7 (`subst` direction, bundle11 NOTES.md via #13) When both sides of an equation are free local variables, `rw` on the goal instead of `subst`; adopted from the start in bundle12 and it never recurred.
- T8 (`return_label_preserves`, #15) Needs `RETURN`'s principal typing reconciled against `v_C.RETURN` via `resulttype_sub_app`-style reasoning, not just a context-crossing trick.
- T9 (signature bugs found by comparing with live Rocq) `testop`/`relop` need `wf_admininstr (admininstr.CONST numtype.I32 v_c) ->` (else `wf_num_ I32 c` unprovable for arbitrary c); `ai_principal_typing`: `REF_HOST_ADDR` gap (bundle9), `BR_TABLE` bug (bundle8),
  GLOBAL_SET must pin `some MUT`, RETURN needs the `Instr_ok` conjunct, FRAME_ needs to bind the arity and conjunct `ts.length = v_n`; Preservation lemmas need the leading `wf_config` hypothesis; `s_invert_mems`/`s_invert_tables`/`memory_grow_mem_extension`/`construct_meminsts_grow`
  must keep the declared maximum as `Option` (never `some`). Transcribe from the LIVE Rocq source, not from a digest.
- T10 (regeneration hazard, #16) A new `wfopt`-hint/undep pass can flip a generated function between `Option`-wrapped and total (`nbytes_` etc.); every HelperLemmas.lean axiom mentioning such a function must be re-checked (drop `≠ none` guards and `Option.get!`); `lake build` is the detector (5 errors then).
- T11 (`grep -c sorry` pitfall, #12) it also counts doc comments containing the word (17 -> 15 for one proof); count `:= sorry` / `by sorry` / `sorry` as a tactic with a precise pattern.
- T12 (`list_slice_update_length`, #17) A def written with take/append/drop is length-preserving only when `n = update.length`; match Rocq's recursive early-stopping definition (`wasm.v:66-74`) or the unconditional lemma is false.
- T13 (`construct_meminsts_grow`, #16) Rocq's route is `Q`/`Z`/`Qfloor`/`Zdiv` bookkeeping plus `induction Hold` on the `Forall2` witness; neither exists in Lean (Nat, zip-based); new spec bound `-- if i' <= $(2^16)` in `$growmemory` supplies `lim_old + v_n <= 2^16`; #17 notes `table_grow_table_extension`/`construct_tableinsts_grow` already take a genuine `Option` maximum (the pattern to copy; OBSERVED: the current `construct_meminsts_grow` docstring says its proof follows `construct_tableinsts_grow`).
- T14 (`lane_` union, type_progress.v, #3 quote) "the spectec subtyping between `num_`/`pack_`/`iN` and `lane_` is not preserved by the Coq encoding. So `proj_lane__2 l <> None` is not derivable, and no axiom can repair it: `vextract_lane_num` wants the `mk_lane__0` form of the very same list that `vtestop_true` wants in `mk_lane__2` form."
  Workarounds Rocq used (#11): VUNOP by splitting Jnn/Fnn up front (`vunop_real`, `vunop_total`, `vunop_not_none`); VTESTOP by using the catch-all `~ Step_pure_before_vtestop_false` so the injection need not be known.
- T15 (reuse) `ai_principal_typing` etc. were ported in one bundle by mining `spectec/test-lean/typing_lemmas.lean`; check it first for `instr_of`; verify a mined definition with a real build and expect a bug (the `BR_TABLE` case).
- T16 (rename detection, #3) After a regeneration, if previously-building files fail, check for a renamed constructor/relation first (`Admin_instrs_ok` -> `Instrs_ok2` precedent); table of Rocq renames in #6 sec.3b.
- T17 (`wf_admininstr_instr`, #16) Lean `instr_of_admininstr_instr` is proved by `cases i <;> rfl`; Rocq's tactic edits (`all: try (econstructor; eauto)`) need no Lean counterpart.
- T18 (axioms, #3) Each Rocq axiom has a spec-level justification comment; mirror with the same comment; new primitives need hand-written characterising axioms, not derivation from the encoding.
- T19 (`instrtype_sub`, #3) defined as an existential-split formula, so frame-rule bookkeeping is ordinary list algebra; do not introduce an inductive subtyping.

## 7. Relevance to the upstream changes (vcvtop/TRUNC_SAT, vloadop/SHAPE, ishl_/ishr_/vshiftop, iadd_/fill-copy-init, Step_read_is_wf, stuck cases, bundle19 hand edits)

- vcvtop/TRUNC_SAT: #16 sec.1/3 record the PREVIOUS reshaping (`vcvtop` -> shape-pair-indexed `vcvtop__`, `VCVTOP` argument order swapped, three `vcvtop-full/-half/-zero` rules merged, `t_pure_preservation` dispatch renumbering `24 -> 22`,
  type_preservation_pure.v helper arg types `wasm.vcvtop` -> `wasm.vcvtop__`). #6 sec.3a lists `ais_vcvtop_typing_inversion`/`Step_pure__vcvtop_preserves` among the ~47 new vector lemmas. #16 sec.3 lists axioms `trunc_sat_total`, `demote_nonempty`,
  `promote_nonempty` (axioms.v) as used only by type_progress.v CVTOP totality. #11 documents the `lane_`-union approach to VUNOP/VTESTOP.
- vloadop/SHAPE: #6 sec.3a lists the Rocq vload/vstore lemmas (`ais_vload_typing_inversion`, `ais_vload_lane_typing_inversion`, `Step_read__vload_preserves`, `Step_read__vload_lane_preserves`, `ais_vstore_*`, `Step__vstore_*`, `vec_store_preserves_2`, `mem_store_extension`);
  #16 sec.1 records the earlier reshaping of `vloadop`. #6 sec.3d flagged a "VLOAD + oversized SPLAT memarg" `t_progress_be` admit as a possible under-constrained typing rule (O5).
- ishl_/ishr_/vshiftop: #16 sec.3 says `ishl_wf`/`ishr_wf` (axioms.v) were used only for I64 shift totality in type_progress.v; #6 sec.3a lists `ais_vshiftop_typing_inversion`/`Step_pure__vshiftop_preserves` in type_preservation_pure.v. Nothing else.
- iadd_/memory fill-copy-init, Step_read_is_wf: #11 is the only mention: wasm.v `Admitted` site "the packed-load `Step_read` admit" carried the comment `Mechanised: Step_read_is_wf_false in wf_counterexamples.v` (claimed counterexample, file never pushed);
  OBSERVED `TypePreservation.lean` l.17-19 later attributes the falsity to the "memory.fill/copy/init corner case" (`CONST I32 2^32`), i.e. the bundle9 "packed-load" label was inexact (or there were several cases). No other document mentions fill/copy/init or `iadd_`.
- Stuck cases (`vload_shape64_*`, `vcvtop_trunc_sat_i16_*`): not named in these 17 files. Closest: #6 sec.3d (O5) and #3/#7/#11 (lane_ union). (My inference, not stated in the files: the 5 (bundle3) -> 7 (bundle9) `admit.` counts of `t_progress_be` are the Rocq predecessor of the two stuck subcases.)
- bundle19 wasm2.0 hand edits: not mentioned (they postdate these files). Relevant precedents: (1) #16's byte-for-byte regeneration recipe (S7); (2) the `nbytes_` totality build break (T10): any change of Option-wrapping in the regenerated file breaks HelperLemmas.lean axioms; (3) #3/#6/#11: `wasm2.0.lean`
  is the parallel `*_is_wf` effort's file and `wasm.v` `*_is_wf` admits are where Rocq itself is stuck (O4).
- Rocq renames worth knowing when diffing the regenerated file: section 3.6 table.

## 8. OBSERVED cross-checks (own read-only greps of the current Lean files; NOT from the assigned documents)

- X1 Signature-audit findings: all fixed in the current files except #5 (intentionally unchanged): `list_slice_update_length` is unconditional (HelperLemmas.lean:436-439, via `list_slice_update.induct`); `ai_principal_typing` GLOBAL_SET uses `some r_MUT.MUT`
  (TypingLemmas.lean:382-384), RETURN has the `Instr_ok` conjunct (357-360), FRAME_ binds `v_n` and has `ts.length = v_n` (453-457); `store_extension_reduce` (TypePreservation.lean:1614-1619), `step_moduleinst` (1626-1631), `t_preservation_type` (2682-2689),
  `t_read_preservation` (2031) all take `wf_config`; `s_invert_mems`/`s_invert_tables` use `Option Nat` (ExtensionLemmas.lean:268-291), `memory_grow_mem_extension` (1267-1276) and `construct_meminsts_grow` (2196-2207) use `Option`; `num_default_is_well_formed` is proved (TypePreservation.lean:47-48).
- X2 Dead cluster is still there: HelperLemmas.lean has 15 real `:= sorry` (l.187, 192, 330, 338, 346, 367, 372, 377, 382, 387, 397, 404, 410, 416, 422) and ExtensionLemmas.lean l.137 (`Val_ok_store`), each annotated `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED`.
  Against the zip-based `Forall₂` (still `∀ t ∈ xs₁ |>.zip xs₂, ...` in the regenerated wasm2.0.lean:21-22), these are FALSE as stated (counterexample `l = [a]`, `l' = []`, or `l = []`, `l' = [b]`): `Forall2_nth` (330), `Forall2_lookup` (338), `Forall2_forall2` (367, forward direction),
  `Forall2_forall2weak` (372), `Forall2_forall2weak2` (377). By my reading the others are provable even with zip semantics: `list_update_func_split(_strong)` (187, 192), `lookup_list_update_func` (346), `Forall2_forall2weak3/4` (382, 387; they assume the length equation),
  `Forall2_list_update_func/_func2` (397, 404), `Forall2_list_update/2/_both` (410, 416, 422).
- X3 Current upstream-sensitive places: `ishl_wf`/`ishr_wf` axioms with `k : u32` at HelperLemmas.lean:842-847, used at TypeProgress.lean:1664-1665 and 1850-1851; `trunc_sat_total`/`demote_nonempty`/`promote_nonempty` at HelperLemmas.lean:849-856, used at TypeProgress.lean:3371-3372, 3383, 3390;
  `feq_bit` etc. at HelperLemmas.lean:824-; `ibits_inv` at 819-821. `vcvtop_trunc_sat_i16` defs/premises/counterexamples at TypeProgress.lean:3287-3298, 3370, 3400, 3547, 3570, 3605-3652, 3704-3742, 5653-5656, 7981-8010; `vload_shape64_*` at 6726, 7935-7978; header status l.9-60.
  TypePreservationPure.lean: `ais_vcvtop_typing_inversion` 1498, `Step_pure__vcvtop_preserves` 1811, dispatch 1971; `ais_vshiftop_typing_inversion` 1398, `Step_pure__vshiftop_preserves` 1688, dispatch 1949. TypePreservation.lean: `ais_vload_typing_inversion` 545, `Step_read__vload_preserves` 584; `Step_read_is_wf` used at 2039.
- X4 Regenerated wasm2.0.lean (current): `ishl_` is `opaque ishl_ (v_N) (v_iN iN_0 : iN) : iN` (3003) with generated `ishl__is_wf` (3010-3015, `sorry`; hypotheses `wf_uN v_N v_iN`, `wf_uN v_N iN_0`); `ishr_` opaque (3018); `iadd_` is a regular `def` (2877) with `iadd__is_wf` at 2881;
  `wf_vloadop_.vloadop__case_0` now ends `... ∧ (v_M > 1)` (1777-1780); `vcvtop__Fnn_1_M_1_Inn_2_M_2` (1548-1599) with `mk_vcvtop___2 (Fnn_1) (M_1) (Inn_2) (M_2)`; `Step_pure_is_wf` (12879) and `Step_read_is_wf` (13274-13279, `(var_0 : config) (var_1 : List admininstr) : wf_config var_0 -> Step_read var_0 var_1 -> Forall wf_admininstr var_1 := sorry`, no `Store_ok` premise) are `sorry`; the file has 152 `*_is_wf` theorems and 152 `sorry` lines;
  the bundle19 hand-edited predecessor (OLD_wasm2.0.lean:16045-16057) moved `Step_read_is_wf` after `Store_ok` and gave it a `Store_ok (fun_store z)` premise (its comment: false in the memory.fill/copy/init corner case `CONST I32 (i+1)`, `i = 2^32 - 1`, on a 2^16-page memory, pending a spec-side fix), and
  `Step_is_wf` (same file, 16058-) passes `hsok` to it; the call site `TypePreservation.lean:2039` (`Step_read_is_wf _ _ _ hwfc hsok hstep`) still has the old shape. There are no theorems named `fone_is_wf`, `utf8_is_wf`, `runelem_is_wf`, `rundata_is_wf` (so of the six bundle9 counterexample names only `Step_pure_is_wf` and `Step_read_is_wf` have Lean counterparts by name).
- X5 TypeProgress.lean header (l.9-60, status end of bundle20): everything proved except the two false-as-specced subcases (VLOAD V128 SHAPE 64x1 in `t_progress_be_vload_pack`; F32x4 -> I16x8 TRUNC_SAT ZERO in `t_progress_be_vcvtop`), plus `Step_read_is_wf` and 56 generated numeric `*_is_wf` as `#sorry_deps`; 17 project axioms.

## 9. Safety check (END), verbatim

(Appended by the final command below, which runs the check and tees its output into this file.)

Command: bash /tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/verify.sh digest-old1-end (exit code 0)

```
safety check [digest-old1-end] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T080454.668807583Z-digest-old1-end-473367.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
2a4
> ?? spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/
```

(The NOTE lines, if any, are the same pre-existing differences already visible in the START check: the .lake trace file and the bundle21 directory were created by other activity, not by this digest. This session wrote nothing under /home/zhengyew/spectec.)

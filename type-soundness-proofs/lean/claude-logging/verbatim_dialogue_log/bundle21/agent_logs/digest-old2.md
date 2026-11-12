# digest-old2: digest of bundle15/16/17 user_requested_documents and three bundle18 documents

Label: `digest-old2`. Read-only digest. Writes: this file only, plus the two safety-check output files that
`verify.sh` itself writes into the scratchpad `safety/` directory, plus three small analysis scripts in
`/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/work/digest-old2/`
(`cmp_ctors.py`, `cmp_ctors2.py`, `cmp_ctors3.py`; all run with `python3 -I`, read-only on the repo).
Nothing was written inside `/home/zhengyew/spectec`. No agents spawned, no lake, no git writes.

Provenance tags used throughout:

- `[DOC file section/lines]` = stated in one of my 12 assigned files. Line numbers are the docs' own and are often
  stale relative to the current Lean files.
- `[CHECK]` = my own read-only check of the working tree (grep, `sed -n`, `python3 -I`). NOT stated in the docs.
  Line numbers tagged `[CHECK]` are current-tree line numbers as of ~16:10 (+08) on 2026-10-15 unless marked `(12:34 snapshot)`.
- `[INFERENCE]` = my own reasoning, flagged because it is neither in the docs nor directly observed.

IMPORTANT, the tree moved while I was working: at 2026-10-15 16:05:35 (+08) someone else (not me) rewrote
`wasm2.0.lean` (14698 -> 16612 lines, hand edits and `iswf_*` helpers back in, `Step_read_is_wf` proved),
`HelperLemmas.lean` (`ishl_wf`/`ishr_wf` deleted), `TypePreservation.lean` (header and `t_read_preservation` doc rewritten as
"bundle21") and `TypeProgress.lean` (7948 lines, no `sorry`, stuck-case lemmas removed). My first `[CHECK]` pass saw the
12:34 regenerated-but-unedited `wasm2.0.lean`; I re-ran every check that matters against the 16:10 tree, and where an
observation only holds for the 12:34 snapshot I say so. Expect further drift.

## 0. Safety check (START), verbatim

Command: `bash /tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/verify.sh digest-old2-start`

```
safety check [digest-old2-start] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T053101.381210611Z-digest-old2-start-463932.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
2a4
> ?? spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/
```

The two NOTE entries are not mine (a lake trace file and the main session's bundle21 folder; both existed before my
first command).

## 1. Files read (completely)

Directory: `/home/zhengyew/spectec/spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/`

| file | lines | bytes |
|---|---:|---:|
| bundle15/user_requested_documents/extension_lemmas_triage_v1.md | 228 | 26764 |
| bundle15/user_requested_documents/proof_dependencies_v4.md | 96 | 6581 |
| bundle15/user_requested_documents/proof_prioritization_v5.md | 86 | 5194 |
| bundle16/user_requested_documents/extension_lemmas_triage_v2.md | 110 | 6049 |
| bundle16/user_requested_documents/insights_for_next_turn.md | 488 | 26042 |
| bundle16/user_requested_documents/proof_dependencies_v5.md | 84 | 5770 |
| bundle16/user_requested_documents/proof_prioritization_v6.md | 96 | 4970 |
| bundle17/user_requested_documents/gap_analysis_v1.md | 239 | 15772 |
| bundle17/user_requested_documents/with_mem_slice_update_issue.md | 148 | 8412 |
| bundle18/user_requested_documents/extension_lemmas_triage_v3.md | 38 | 1960 |
| bundle18/user_requested_documents/proof_dependencies_v6.md | 67 | 3888 |
| bundle18/user_requested_documents/proof_prioritization_v7.md | 51 | 3184 |

Total 1731 lines. Every line was read with the Read tool; the longest line in any of them is 718 characters, so no
line was truncated by the viewer. `bundle18/user_requested_documents/insights_for_next_turn.md` was skipped as
instructed. No file was only skimmed.

## 2. Executive summary (the things that matter most)

1. All 12 documents are HISTORICAL snapshots (bundle15 to bundle18). Sorry trajectory: 83 (end bundle15) -> 27
   (bundle16) -> 26 (bundle17, `funcinst_same` closed) -> 18 declarations at the end of bundle18
   (`t_read_preservation`, `rat_to_nat_natCast`, 15 dead `HelperLemmas`, `Val_ok_store`).
2. Current tree `[CHECK 16:10]`: real `sorry` proof bodies exist ONLY in (a) `HelperLemmas.lean`: the same 15 dead lemmas
   (lines 187, 192, 330, 338, 346, 367, 372, 377, 382, 387, 397, 404, 410, 416, 422); (b) `ExtensionLemmas.lean`: 1,
   `Val_ok_store` (line 137); (c) `wasm2.0.lean`: exactly 62 generated `*_is_wf` theorems, every one about an `opaque` function
   (`ishl__is_wf` 3212, `ishr__is_wf` 3227, `wrap___is_wf` 2868, `ibytes__is_wf` 4182, `nbytes__is_wf` 4210, `vbytes__is_wf` 4224, ...).
   `Subtyping`, `TypingLemmas`, `TypePreservationPure`, `TypePreservation` and `TypeProgress` have no `sorry` body (grep hits there
   are comment text). `rat_to_nat_natCast` is proved (`TypePreservation.lean:1318`); `Step_pure_is_wf` (14016), `Step_read_is_wf`
   (16101), `Step_is_wf` (16325) and `iadd__is_wf` (3075) are proved in `wasm2.0.lean`.
3. The blocker for "knock out every last sorry" (docs plus my check): the 16 dead lemmas (15 in `HelperLemmas` + `Val_ok_store`) each carry
   the user's own comment `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED` `[CHECK]`. The standing instruction (bundle16 insights
   s1.6) says to IGNORE `TODO FROM USER` comments (they are the user's notes to self), and the docs say "ask the user, then delete"
   (bundle18 v3 line 17, v7 lines 17-18). `Val_ok_store` and 5 of the 15 (`Forall2_nth`, `Forall2_lookup`, `Forall2_forall2`,
   `Forall2_forall2weak`, `Forall2_forall2weak2`) are FALSE as stated for the zip-based `Forall₂` (docs say "several"; the five names are
   my own check). The other 10 look provable as stated (`[INFERENCE]`, s5.B). So these cannot be eliminated by proof without a user
   decision (delete, or restate with a length premise / `wf_store` premises). The 62 generated `*_is_wf` of opaque functions are
   `Admitted` in Rocq too and cannot be proved from an `opaque` definition either (they are the `Axiom`s' well-formedness).
4. Upstream change (4) (`iadd_ 32 i 1`) removes EXACTLY the corner case that bundle18 had recorded as making `Step_read_is_wf`,
   `Step_is_wf`, `t_read_preservation` and `t_preservation` false (`CONST I32 (i+1)` at `i = 2^32 - 1` on a full 2^16-page memory;
   bundle18 v7 lines 47-51, with_mem issue lines 139-146). The tree already reflects this: the rewritten `TypePreservation.lean` header
   (lines 8-21) and `Step_read_is_wf`'s hand-edit comment (`wasm2.0.lean:16095-16100`) say so.
5. The docs record that Rocq's hand-edited `wasm.v` gives `Step_read_is_wf` and `Step_is_wf` an extra `Store_ok (fun_store z)` premise
   ("the store bounds are needed for table.size, memory.size and the bulk rules"; with_mem issue lines 139-141). `[CHECK]` the
   12:34 regenerated file had NO such premise and all three `*_is_wf` were plain generated `sorry` (lines 12879, 13274, 13383 then);
   as of 16:10 the hand-edited shapes `Step_read_is_wf (z : state) (admininstr_lst : List admininstr) (var_1 : List admininstr)` and
   `Step_is_wf (z) (admininstr_lst) (var_1 : config)`, both with `Store_ok (fun_store z) →`, are back and proved.
6. The preservation lemmas about vcvtop / vshiftop / vload (gap_analysis s3a/s3b) treat `vcvtop__`, `vshiftop_`, `vloadop_` as opaque
   parameters; `[CHECK 12:34 snapshot vs OLD]` `Instr_ok.vcvtop` and `Step_pure.vshiftop` are textually unchanged by the upstream
   regeneration, so they are expected to survive (and the 16:10 tree still contains them unchanged: `TypePreservationPure.lean` mtime Oct 3; I did not build anything).
   The docs never mention the stuck cases (Progress-only; Progress was "not started" in all 12 docs).
7. Gap analysis s3g lists 12 Progress-only axioms of Rocq `axioms.v`, among them `ishl_wf`, `ishr_wf`, `trunc_sat_total`; "a
   mis-transcribed axiom is an inconsistency, not just a gap". `[CHECK]` `ishl_wf`/`ishr_wf` were deleted from `HelperLemmas.lean` at 16:05
   (explanatory comment at line 844); `trunc_sat_total` (850), `demote_nonempty` (853), `promote_nonempty` (856) remain.
8. The most valuable Lean knowledge is in bundle16 `insights_for_next_turn.md`: s2 opaque-index inversion via bare-variable
   lemmas, s3 binder-count recipe for `cases ... with`, s4 encoding of `dependent induction`, s5 `Instrs_ok2.rec` as a term,
   s6 zip-based `Forall₂` facts, s7 elaboration gotchas, s9 dead ends.
9. Doc errors NOT to inherit: (a) "5 deliberate gaps mirror Rocq `Admitted`" (bundle16 v5/v6) is false since upstream `a8b585cdb`
   (2026-09-22); (b) "`cases h with | Ctor ...` fixes `obtain`" (bundle15 v4/v5) is refuted by bundle16 insights s9; (c) "`rat_to_nat` is
   opaque" (bundle18 v6/v7) is no longer true: it is a `def` (`wasm2.0.lean:9-10`, same in `OLD_wasm2.0.lean`); (d) "no Rocq counterpart" for
   `funcinst_same`/`Val_ok_store` (bundle15 v1, bundle16 v2): both existed at `5b03ae067` and were removed at `a8b585cdb` (bundle17 s2, s5).
10. The `with_mem` out-of-bounds falsity (bundle17) stays resolved: `with_mem` uses `splice` (`wasm2.0.lean:12332-12340`; `splice` at 12-15) and
    `splice_eq_list_slice_update` bridges it (`HelperLemmas.lean:467`).

## 3. Per-file digests

### 3.1 bundle15/extension_lemmas_triage_v1.md (228 lines): HISTORICAL, still the only per-lemma proof-idea catalogue

- Read-only triage of all 76 `:= sorry` theorems of `ExtensionLemmas.lean` against `test-rocq/theories/extension_lemmas.v`.
  Tiers: Trivial 25 / Easy 27 / Moderate 17 / Hard 7 = 76 (lines 213-222). Hard 7 = `Val_ok_store`, `funcinst_same` (both
  "flagged as likely unprovable/uncertain as currently stated"), `addrs_tables_extension`, `addrs_mems_extension`,
  `Extend_store_ais`, `construct_tableinsts_grow`, `construct_meminsts_grow`.
- Representation facts (lines 8-46): `Forall₂ P l1 l2 := ∀ t ∈ l1.zip l2, P t.1 t.2` (zip-based, not length-forcing), so a pointwise lift
  is trivial but anything that correlates a specific list index needs a length bridge; `list_update_func := List.modify` so core
  `List.getElem_modify_eq` / `List.getElem?_modify_ne` (`Init/Data/List/Nat/Modify.lean`) replace Rocq's
  `list_update_func_subst/unchanged`; `Extend_meminst`/`Extend_tableinst` constructors carry the declared max `Option m` as a shared
  unsplit parameter so `_grow`/`_set` extension lemmas need no Option split; Rocq's `Externaddr_invert_funcs/_tables/_mems/_globals`
  (`extension_lemmas.v:1065-1159`) had no Lean counterpart; `HelperLemmas.Forall2_nth/_lookup/_forall2*` were `sorry`.
- 15 "standalone Trivial" starters (lines 133-138): `se_invert_funcs/_tables/_mems/_store_globals/_elems/_datas`,
  `externtype_global_eq`, `externtype_func_eq`, `minst_invert_functypes`, `tc_func_reference2`, `config_same`, `config_same2`,
  `update_global_unchanged`, `Extend_store_datainsts`, `Extend_store_meminst`.
- Templates A (index-update `holds_upto`), B (`Forall₂` position correlation for `construct_*`), C (`Externaddr_ok` sub-chain peel)
  are described at lines 159-211 (reproduced in s6).
- Outcome: everything closed in bundle16 except `Val_ok_store` and `funcinst_same` (the latter closed in bundle17 after the user
  added `hlen`). Stale: all line numbers; "no Rocq counterpart found" (see s2 item 9d); the Template B recommendation to "port
  `HelperLemmas.Forall2_nth`" was impossible (statement false for zip-based `Forall₂`), bundle16 built `Forall2_nth_of_length` instead.
- Relevance to upstream changes: none.

### 3.2 bundle15/proof_dependencies_v4.md (96 lines): HISTORICAL

- Status at bundle15 (2026-10-01): HelperLemmas 63 decls/15 sorry (dead `nat->N` cluster); Subtyping 46/0; TypingLemmas 81/0;
  TypePreservationPure 30/10 (8 genuine + `return_frame_preserves`, `t_pure_preservation`); ExtensionLemmas 92/50 (was 76);
  TypePreservation 13/8 (5 genuine + `store_extension_reduce`, `t_read_preservation`, `t_preservation_type`). Total 313 decls, 83
  sorry (bundle13: 350/125). File graph: HelperLemmas -> Subtyping -> TypingLemmas -> {TypePreservationPure -> TypePreservation;
  ExtensionLemmas}; TypeProgress needs TypingLemmas + ExtensionLemmas + Subtyping + Axioms and NOT Preservation.
- Lines 62-68 admit the tier counts for the remaining Extension lemmas are estimates; lines 47-48 contain an editing artifact
  ("wait, see note below").
- Lines 86-96: 3 lemmas flagged and reverted (`minst_invert_elems`, `store_none_mem_extension`, `table_grow_table_extension`) after
  `obtain`/`cases`-on-dependent-structure friction, "per explicit user instruction to skip and flag rather than keep fighting";
  `table_set_table_extension` was fixed by switching `obtain` to `cases ... with` (later shown not to be the real fix, bundle16 insights s9).

### 3.3 bundle15/proof_prioritization_v5.md (86 lines): HISTORICAL

- 83 sorry = Extension 50 + TPP 10 + TP 8 + HelperLemmas 15. 8-step plan: Easy tier of Extension (`Extend_store_ref` cascade, `eleminst`,
  `tableinst`/`globalinst`, `datainsts'`), build Template C (`Externaddr_invert_*`), `addrs_*`/`addrss_*` -> `Extend_store_exts` ->
  `Extend_store_moduleinst` -> `Extend_store_funcinst(s)`, Template B, the 3 reverted lemmas "with the `cases h with | Ctor ...` idiom (not
  `obtain`)" (wrong), the Hard 7, TPP's 8 genuine targets (`return_label` -> `br_zero` -> `select` cluster -> `br_succ` -> `br_table_lt/_ge`),
  TP's 5 genuine targets last.
- Nothing here is still actionable.

### 3.4 bundle16/extension_lemmas_triage_v2.md (110 lines): CLOSEOUT of v1

- `ExtensionLemmas.lean` sorry 76 -> 50 (bundle15 end) -> 2; declarations 92 -> 129 (+37 helpers). All of v1's Trivial/Easy/Moderate/Hard are
  proved incl. the 3 reverted lemmas, both `_grow` construct lemmas and `Extend_store_ais`.
- Remaining 2 were SIGNATURE problems: `Val_ok_store` (line ~136) and `funcinst_same` (line ~1054), analysed in s5.
- Template A complete (key helper `getElem!_modify_eq_or_ne`, HelperLemmas, bundle15). Template B built: `mem_modify`, `mem_zip_modify`,
  `mem_zip_modify₂`, `mem_zip_modify_right`, `mem_zip_getElem!`, `Forall2_nth_of_length` (NOT a port of `Forall2_nth`, which stays
  `sorry` because its Rocq statement derives the length equality). Template C built: `Externaddr_invert_funcs/_tables/_mems/_globals` + four
  private `..._aux` lemmas; it unblocked ~30 lemmas (v1 predicted ~9).
- New-infrastructure list (lines 93-110): chain-peel; `Extend_store_wf_store`, `Extend_store_wf_store'`; `extend_funcinst_eq`,
  `extend_globalinst_type_eq`, `extend_tableinst_sub`, `extend_meminst_sub`, `extend_meminst_bytes`; bare-variable inverters
  `funcinst_ok_invert`, `globalinst_ok_invert`, `meminst_ok_invert`, `meminst_ok_raw`, `tableinst_ok_invert`, `eleminst_ok_invert`,
  `limits_ok_invert`, `Store_ok_globalinst`, `Ref_ok_wf_store`, `Val_ok_wf_val`, `wf_tableinst_parts`, `wf_meminst_parts`; transport steps
  `Extend_store_externaddr`, `Extend_store_eleminst_ext`, `Extend_store_datainst_ext`, `Extend_store_frame`; rebuild steps
  `eleminst_ok_drop`, `datainst_ok_drop`, `globalinst_ok_set`, `tableinst_ok_set`, `meminst_ok_store`. All have no Rocq counterpart by name
  (Rocq inlines via `inversion`/`econstructor`).

### 3.5 bundle16/proof_dependencies_v5.md (84 lines): HISTORICAL (one big error)

- Status at bundle16 (2026-10-02): HelperLemmas 62/15/0 genuine; Subtyping 47/0; TypingLemmas 81/0; TypePreservationPure 30/7 (5 genuine:
  `br_zero`, `br_succ`, `br_table_lt`, `br_table_ge`, `return_label`); ExtensionLemmas 129/2; TypePreservation 17/3. Total 366 decls, 27
  sorry = 5 genuine + 5 "deliberate permanent gaps mirroring Rocq `Admitted`" + 2 bad signatures + 15 dead. The "5 deliberate gaps" claim is
  FALSE (bundle17 gap_analysis s1).
- Dependency closure of `t_preservation` (lines 47-65): `store_extension_reduce` (gap then), `reduce_inst_unchanged`, `Extend_store_moduleinst`,
  `t_preservation_vs_type`/`'`, `Extend_store_vals`, `t_preservation_type` (gap then; `t_pure_preservation`, `t_read_preservation`,
  `Extend_store_ais`), `Step_is_wf` ("`sorry` in `wasm2.0.lean` (GENERATED FILE, outside the editable directory)"), `inst_t_context_local_empty`.
- Progress: "not started", gate on `ExtensionLemmas` now gone.

### 3.6 bundle16/proof_prioritization_v6.md (96 lines): HISTORICAL; per-lemma routes still instructive

- Order: `br_table_ge` -> `br_table_lt` -> `br_zero` -> `br_succ` -> `return_label` (routes in s6.9). "Not targets" list wrongly includes
  `t_pure_preservation`, `store_extension_reduce`, `t_read_preservation`, `t_preservation_type`, `Step_pure__return_frame_preserves` as Rocq
  `Admitted` (false, see 3.5). `Val_ok_store`, `funcinst_same`: "Only touch these if the user asks for a signature change". Next project after
  the five: `type_progress.v`.

### 3.7 bundle16/insights_for_next_turn.md (488 lines): THE RICHEST FILE (details in s4 and s6)

- s0 status; s1 seven STANDING INSTRUCTIONS; s2 opaque-index inversion; s3 binder counts; s4 `dependent induction` encoding; s5 mutual-inductive
  recursor; s6 zip-based `Forall₂`; s7 syntax/elaboration gotchas; s8 iteration tooling; s9 dead ends; s10 proof machinery; s11 things worth
  double-checking.

### 3.8 bundle17/gap_analysis_v1.md (239 lines): KEY (corrects bundle13/15/16; lists everything still unported as of bundle17)

- s0 upstream status; s1 the user's correction is right (no `Admitted` upstream, table of `Admitted` counts); s2 `funcinst_same (hlen)` sound;
  s3a-s3h missing declarations per Rocq file; s4 signature problems; s5 sorrys classified by the user's three rules; s6 plan. Details in s4-s8.

### 3.9 bundle17/with_mem_slice_update_issue.md (148 lines): KEY (resolved in bundle18 by the user's backend change; contains the `Step_read_is_wf` note)

- Found during the gap analysis; work stopped per the standing instruction "if any issues arise that are significant, immediately stop and report
  back". Claim: Lean `with_mem` rendered `BYTES[i : j] = b*` as `(take i ++ b*) ++ drop (i+j)`, NOT length-preserving out of bounds, so the four
  `-val` store rules (`store_num_val`, `store_pack_val`, `vstore_val`, `vstore_lane_val`; no bounds premise) could break `Meminst_ok`, making
  `store_extension_reduce` and `t_preservation` false in Lean (Rocq's `list_slice_update` is length-preserving). Four options listed (fix Lean
  backend recommended; fix spec; weaken theorem; leave 4 cases `sorry`). Resolution: see s5 item J. Lines 137-148: the `Step_read_is_wf` note (s7).

### 3.10 bundle18/extension_lemmas_triage_v3.md (38 lines)

- `ExtensionLemmas.lean` sorry 76 -> 2 -> 1. `funcinst_same` closed (user added `hlen` in bundle17, sound, proved). `Val_ok_store` still `sorry`, dead
  (rule 1), "Recommend deletion (ask the user)". bundle18 change: `construct_meminsts_grow` generalized from `some (uN.mk_uN v_j)` to Rocq's genuine
  `v_j_opt : Option uN` with premise `Forall (fun v_j => lim_old + v_n ≤ proj_uN_0 v_j) (Option.toList v_j_opt)` (proof adapted from
  `construct_tableinsts_grow`); used by `TypePreservation.memory_grow_store_ok`. New store plumbing (`Store_ok_parts`, `Extend_store_of_parts`, ...) lives in
  `TypePreservation.lean`. Pitfalls (lines 34-38) in s6.7.

### 3.11 bundle18/proof_dependencies_v6.md (67 lines)

- Lemma-level dependency tree of `t_preservation` at end of bundle18 (reproduced in s8) and the measured transitive `sorry` dependencies from the
  `#sorry_deps` meta-program: `store_extension_reduce` -> `rat_to_nat_natCast`, `ibytes__is_wf`, `nbytes__is_wf`, `vbytes__is_wf`, `wrap___is_wf`;
  `t_pure_preservation` -> `Step_pure_is_wf`; `t_preservation_type` -> `Step_is_wf`, `Step_pure_is_wf`, `t_read_preservation`; `t_preservation` -> all 8. No custom
  `axiom` (e.g. `HelperLemmas.nbytes_len`) on the preservation path; `#print axioms TLC.t_preservation` = `propext, sorryAx, Classical.choice, Quot.sound`.
  Lines 53-67: inputs for `t_read_preservation` (list in s8).

### 3.12 bundle18/proof_prioritization_v7.md (51 lines)

- 18 sorry declarations (26 at bundle18 start): `t_read_preservation` (genuine, ~47 cases), `rat_to_nat_natCast` (unprovable while `rat_to_nat` opaque; user decision
  suggested `r.floor.toNat`), 15 dead `HelperLemmas`, `Val_ok_store`. Generated-file sorrys the chain uses: `Step_pure_is_wf` (believed true, `Qed` upstream),
  `Step_is_wf`/`Step_read_is_wf` (false in one corner case), `nbytes__is_wf`/`ibytes__is_wf`/`vbytes__is_wf`/`wrap___is_wf` (opaque byte functions, believed true).
  Priority for `t_read_preservation` (lines 29-39): 15 trap cases, 6 zero cases, single-constant results (`table_size`, `memory_size`, `load_num_val`,
  `load_pack_val`) + 5 vector-load value cases, `local_get` (locals-length deviation decision), `global_get` (via `lookup_global`), `table_get_val`, `ref_func`,
  the 8 sequence cases (`*_fill_succ`, `*_copy_le/gt`, `*_init_succ`; write `instrtype_sub_prefix` first), `block`, `loop`, `call`, `call_indirect_call`,
  `call_addr` last. Then doc-comment cleanup, then Progress.

## 4. Standing instructions and refinements still binding

1. SAFETY (bundle16 insights s1.1, lines 30-44). "Never modify anything outside `spectec/src/test-lean-claude`." Run
   `bash spectec/src/test-lean-claude/claude-logging/safety-checks/check.sh` after every batch of edits (auto-writes a timestamped log into
   `claude-logging/safety-checks/`). "Verify the output, don't just run it": diff `grep -E "^( M | D |A )"` lines, excluding `src/test-lean-claude`, of the
   FIRST check of the turn against the LATEST; identical output means no out-of-target change. Pre-existing at bundle16 and NOT to be "fixed": `M spectec/test-lean/todaywasm2.0.lean`,
   `D spectec/test-lean/todaywasm3.0.lean`, and many untracked `??` scratch files at the repo root.
2. SUBAGENTS (s1.2). If you spawn any subagent / other LLM you MUST brief it on #1 and require it to run its own `check.sh` and log the result.
3. LOGGING (s1.3). New folder per exchange `claude-logging/verbatim_dialogue_log/bundleN/` with `prompt_N.md`, `response_N.md`, `response_N_modelinfo.md`; mid-turn user messages and subagent hand-backs
   are appended to `prompt_N.md` in chronological order, verbatim and clearly labelled; NEVER edit a previous bundle's files; one-off deliverables go in `bundleN/user_requested_documents/`.
4. PROOF FIDELITY (s1.4). Signatures must match Rocq's EXACTLY; proof method/tactics may diverge freely (proof irrelevance). A non-Rocq helper lemma must say so in its doc comment and say what Rocq does
   inline. REFINEMENT (gap_analysis s2, s3b, s3e; mirrored in the current `t_read_preservation` doc): an INTENDED deviation is allowed, and documented as such, when Rocq's inductive `Forall2` forces equal lengths
   but Lean's zip-based `Forall₂` does not: add an explicit length premise `hlen` (the user did this to `funcinst_same` and the docs call it "sound" and "faithful", "the same move as `Vals_ok`'s baked-in length").
5. WHEN A PROOF FIGHTS BACK (s1.5). First check the signature and its dependencies; if the problem persists SKIP and FLAG (revert to `sorry` with a doc comment saying exactly where it got stuck). Do not spin. Report
   significant issues immediately (with_mem issue lines 7-9: "Per the standing instruction ('if any issues arise that are significant, immediately stop and report back'), work stopped here").
6. `TODO FROM USER` comments (s1.6): IGNORE them, they are the user's notes to self. `[CHECK]` they currently mark `Val_ok_store` (`ExtensionLemmas.lean:128`) and all 15 dead `HelperLemmas` (lines 184, 189, 325, 332, 343, 364, 369,
   374, 379, 384, 392, 399, 406, 412, 418) as "MARKED FOR DELETION BECAUSE UNUSED"; other TODOs: `HelperLemmas.lean:32` (`lookup_total`), `TypingLemmas.lean:44, 359`, `ExtensionLemmas.lean:306`. Do not act on them.
7. BUILD (s1.7, s8). `lake build` after every lemma or small batch (30-60 s warm); the only build command needed: `timeout 1800 lake build 2>&1 | grep -E "error:" -A 20 | head -60` (raw output is dominated by `wasm2.0.lean`
   linter warnings). (This turn's harness forbids lake for the digest agents; follow whatever the current turn allows for the main session.)
8. THE USER'S THREE RULES for classifying a `sorry` (gap_analysis s5, lines 205-222): Rule 1 = mark for deletion (unused, superseded, not upstream); Rule 2 = Rocq-`Admitted`, mark for later (the set is currently EMPTY because upstream has no `Admitted`); Rule 3 = attempt.
9. ASK THE USER before: deleting `Val_ok_store` or the dead `HelperLemmas` (triage v3 line 17, prioritization v7 lines 17-18); changing the Lean backend's `rat_to_nat` (prioritization v7 line 16, now moot); changing signatures of unprovable lemmas ("Only touch these if the user asks for a signature change", prioritization v6 lines 83-86;
   "Do not 'fix' it speculatively", triage v2 line 39). Axioms: "port ... carefully: a mis-transcribed axiom is an inconsistency, not just a gap" (gap_analysis s3g).
10. THE GENERATED FILE. bundle16 v5 (lines 61-62, 70-72) calls `Step_is_wf`'s home "GENERATED FILE, outside the editable directory; a pre-existing upstream gap, not ours"; bundle18 v7 (lines 20-21) says the generated-file `sorry`s are "not ours to prove". Physically `wasm2.0.lean` sits inside `test-lean-claude` `[CHECK]`; the convention was "do not edit, the user regenerates it", relaxed later by the bundle19 hand edits. Confirm the current permission before hand-editing again.
11. Edit mechanics (s8 lines 392-397): all edits were done with `python3 - <<'PYEOF'` exact-string replacement with `assert old in s` (fails loudly if the anchor drifted); the Rocq source is `spectec/test-rocq/theories/*.v`; Lean doc-comment line numbers are from an older revision, so always `grep -n "^Lemma <name>"` instead of trusting them.
12. For `t_read_preservation`-style work (prioritization v7 lines 29-30, 50-51): leave a `sorry` per unfinished case and keep the build green; take the reduct's well-formedness from `Step_read_is_wf` / `Step_is_wf` "exactly as Rocq does".

## 5. Open issues (status per the docs, then my current-tree check)

A. `Val_ok_store` (`ExtensionLemmas.lean:136`, `:= sorry` at 137). Statement: `Val_ok (store.MKstore f1 g1 t1 m1 e1 d1) v t ↔ Val_ok (store.MKstore f1 g2 t2 m2 e2 d2) v t`. [DOC triage v2 lines 22-41] Not provable as stated: every
   `Val_ok` constructor carries `wf_store s` and `wf_store` constrains all six fields, so the right-to-left direction needs `wf_store (MKstore f1 g1 ...)`, independent of the other store's. The intent (only `FUNCS` matters) is true. Fix if
   wanted: add `wf_store` premises for both stores, then `cases` the `Val_ok`, re-apply the constructor, route the `Ref_ok`/`Externaddr_ok` `FUNCS` lookups through unchanged. Dead (nothing uses it), no upstream counterpart (removed at `a8b585cdb`). [CHECK] still `sorry`, marked by the user for deletion.
B. The 15 dead `HelperLemmas` sorrys [DOC gap_analysis s5, prioritization v7 rows 3-17]: `list_update_func_split`, `list_update_func_split_strong`, `Forall2_nth`, `Forall2_lookup`, `lookup_list_update_func`, `Forall2_forall2`, `Forall2_forall2weak`...`weak4`, `Forall2_list_update_func`,
   `Forall2_list_update_func2`, `Forall2_list_update`, `Forall2_list_update2`, `Forall2_list_update_both`. Docs: "several are false for the zip-based `Forall₂`", replaced by `Forall2_nth_of_length`, `mem_zip_modify*`, `getElem!_modify_eq_or_ne`; "Ask the user, then delete, or add `hlen` premises if ever needed".
   [CHECK] current sorry lines 187, 192, 330, 338, 346, 367, 372, 377, 382, 387, 397, 404, 410, 416, 422. [INFERENCE, my own analysis of the statements at `HelperLemmas.lean:186-422`]:
   - FALSE as stated (counterexample `R := fun _ _ => False`, `l = [0]`, `l' = []`, where `Forall₂ R l l'` holds vacuously): `Forall2_nth`, `Forall2_lookup` (both conclude `l.length = l'.length`), `Forall2_forall2` (the `→` direction needs the length), `Forall2_forall2weak` (`∃ y, R x y` for every `x ∈ l`), `Forall2_forall2weak2` (symmetric). Fix would be an `hlen` premise.
   - Provable AS STATED (no signature change; each is a `List.modify`/`List.set` plus zip-membership argument, and `HelperLemmas.mem_zip_modify`, `mem_zip_modify_right`, `mem_zip_modify₂`, `getElem!_modify_eq_or_ne` supply the zip reasoning): `list_update_func_split`, `list_update_func_split_strong`, `lookup_list_update_func`, `Forall2_forall2weak3`,
     `Forall2_forall2weak4` (their premise already gives the property for every `x`/`y`), `Forall2_list_update_func`, `Forall2_list_update_func2`, `Forall2_list_update`, `Forall2_list_update2`, `Forall2_list_update_both`.
   - Since they are user-marked for deletion, effort spent proving the ten is optional; the five false ones plus `Val_ok_store` cannot be closed without a user decision. This is the "tell the user it cannot be done" item for "every last sorry".
C. `rat_to_nat_natCast` [DOC prioritization v7 line 16, dependencies v6 line 30]: "unprovable as the model stands (`rat_to_nat` is `opaque`)". [CHECK] RESOLVED: `rat_to_nat` is `def rat_to_nat (r : Rat) : Nat := (r.num.tdiv (Int.ofNat (r.den))).toNat` at `wasm2.0.lean:9-10` (same in `OLD_wasm2.0.lean:9-10`) and
   `rat_to_nat_natCast` is proved at `TypePreservation.lean:1318` (used at 1397 and in `TypeProgress.lean`).
D. Stale "Admitted in Rocq" / "false in a corner case" doc comments [DOC gap_analysis s4.2; prioritization v7 item 2]. [CHECK] RESOLVED at 16:05: the `TypePreservation.lean` header (lines 8-21) now reads "Status (bundle21, 2026-10-15)... Since upstream `6582b3a39` that includes the generated `Step_read_is_wf` ... fixed by spec commit `4cf9f29c5`, which makes those rules push `$iadd_(32, i, 1)`", and the `t_read_preservation` doc (line ~2019) says `Step_read_is_wf` "is proved since bundle21". (At 12:34 these still said "`Admitted` upstream ... pending on the spec side".)
E. `Extend_store_datainsts'` signature diverges from Rocq [DOC insights s11 lines 462-469; gap_analysis s4.3]: Rocq has `Forall2 (λ a t, Datainst_ok ...) aa ts`; Lean hard-codes `datatype.OK` and drops `ts`; not documented in its comment; left alone because `Extend_store_moduleinst` does the `Forall₂` version inline. [CHECK] still so (`ExtensionLemmas.lean:1733-1739`, file untouched since Oct 6).
F. `table_grow_table_extension` takes `j : Option uN` while `memory_grow_mem_extension` takes `v_j : Option Nat` + `.map uN.mk_uN` [DOC insights s11 lines 475-478]; harmless inconsistency. [CHECK] unchanged (`ExtensionLemmas.lean:1346`, `1267`).
G. `construct_meminsts_grow` hard-coded the max as present [DOC insights s11; gap_analysis s4.3]: FIXED in bundle18 (generalized, triage v3 lines 21-26). `Step_pure__br_table_ge_preserves` extra premise `v_l.length ≤ ...` [DOC gap_analysis s4.1]: [CHECK] FIXED (current signature at `TypePreservationPure.lean:599-603` has no such premise).
H. Generated-file sorrys the preservation chain uses [DOC prioritization v7 lines 20-25]: `Step_pure_is_wf`, `Step_is_wf`, `Step_read_is_wf`, `nbytes__is_wf`, `ibytes__is_wf`, `vbytes__is_wf`, `wrap___is_wf`. [CHECK 16:10] `Step_pure_is_wf` (14016), `Step_read_is_wf` (16101), `Step_is_wf` (16325) are PROVED (hand-edited with `Store_ok (fun_store z)`); the four byte/wrap functions' `*_is_wf` (`wrap___is_wf` 2868, `ibytes__is_wf` 4182, `nbytes__is_wf` 4210, `vbytes__is_wf` 4224) are still `sorry`, together with 58 more (62 in total, all about `opaque` functions; `iadd__is_wf` is proved).
I. Missing declarations (gap_analysis s3, as of bundle17): 47 in TypePreservationPure (SIMD section), 23 to port in TypePreservation, 8 in TypingLemmas, plus Extension/Helper bridging lemmas. [CHECK] the SIMD set is present: 20 `Step_pure__v*_preserves` (counted), `ais_vshiftop_typing_inversion` 1399, `ais_vcvtop_typing_inversion` 1499, `vec_preserves_1/2/3` 1510/1528/1551 in `TypePreservationPure.lean`; `ais_vload_typing_inversion` 544, `ais_vload_lane_typing_inversion` 554, `ais_vstore_typing_inversion` 564, `Step_read__vload_preserves` 583, `Step_read__vload_lane_preserves` 596 in `TypePreservation.lean`. The other inversions and the Extension/Helper "cheap ports" (`prepend_local`, `Forall_size`, `holds_upto_*`) were not individually verified by me.
J. `with_mem` out-of-bounds falsity of `store_extension_reduce`/`t_preservation` [DOC with_mem issue]: resolved by the user's bundle18 backend change (a `splice` prelude helper; `HelperLemmas.lean:461-466` doc says "added to `wasm2.0.lean` by the user's bundle18 backend change"); [CHECK] `with_mem` (`wasm2.0.lean:12332`) uses `splice (elem_1.BYTES) var_0_lst nat`, `splice` is at `wasm2.0.lean:12-15`.
K. The with_mem counterexample was never built as a formal Lean term [DOC with_mem issue lines 89-91]; moot after J.
L. `Step_pure_is_wf` "believed true", opaque byte-function `*_is_wf` "believed true" [DOC prioritization v7 lines 22-25]: not machine-checked claims (the first is now proved in the tree; the others are the unprovable-from-`opaque` family).

## 6. Techniques and pitfalls (with the lemma each came from)

### 6.1 Inverting a hypothesis whose inductive index is an opaque term [bundle16 insights s2, lines 67-137]
- Symptom: `Dependent elimination failed: Failed to solve equation v_S.ELEMS.get!Internal p.1 = { TYPE := ..., REFS := ... }`. `cases`/`obtain`/`rcases` work by dependent elimination and succeed cheaply only when each index is a BARE FREE VARIABLE. They fail when the index is an opaque application: `l[i]!` (`getElem!`), `p.1`/`p.2`, `x.TYPE` (structure projection on a variable), or anything built with `OMap`/`Option.map` over a variable (unfolds to a `match`). This single issue explains every lemma bundle15 flagged (`minst_invert_elems`, `store_none_mem_extension`, `table_grow_table_extension`).
- FIX (always): do the inversion once in a separate lemma whose arguments are bare variables and apply it at the opaque site.
  ```lean
  theorem eleminst_ok_invert (s : store) (e : eleminst) (t : elemtype) :
      Eleminst_ok s e t →
      ∃ ref_lst, Forall (fun r => Ref_ok s r t) ref_lst ∧ e = eleminst.MKeleminst t ref_lst := by
    intro h
    cases h with
    | mk_Eleminst_ok _ ref_lst hrefs _ _ => exact ⟨ref_lst, hrefs, rfl⟩
  -- use site, subject is `v_S.ELEMS[p.1]!`:
  obtain ⟨ref_lst, hrefs, heq⟩ := eleminst_ok_invert v_S _ p.2 (h16 p hp)
  ```
- Existing inverters (look there first; `[CHECK]` current lines in `ExtensionLemmas.lean`): `funcinst_ok_invert` 151, `globalinst_ok_invert` 157, `limits_ok_invert` 172, `meminst_ok_invert` 187, `tableinst_ok_invert` 202, `eleminst_ok_invert` 213, `Store_ok_globalinst` 829, `Val_ok_wf_val` 1938, `Ref_ok_wf_store` 2029, `wf_tableinst_parts` 2039, `wf_meminst_parts` 2053, `meminst_ok_raw` 2159. "Transport" variants that bundle inversion with reconstruction so the caller never inverts: `Extend_store_eleminst_ext` 1683, `Extend_store_datainst_ext` 1698, `Extend_store_frame` 1856, `Extend_store_externaddr` 1633; rebuild steps `eleminst_ok_drop` 1950, `datainst_ok_drop` 1958, `globalinst_ok_set` 1969, `tableinst_ok_set` 1983, `meminst_ok_store` 2004, `extend_meminst_bytes` 974.
- `OMap` sub-case (lines 122-137): `Limits_ok`'s index contains `OMap (fun e => uN.mk_uN e) m_opt` = `Option.map`, a `match` on `m_opt`, so `cases` on a `Limits_ok` with a compound limits argument always fails. Repo fix `limits_ok_invert (lim : limits) (k : Nat) (h : Limits_ok lim k) : ∀ (v_n : Nat) (m_opt : Option Nat), lim = limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN) → v_n ≤ k ∧ Forall (fun m' => v_n ≤ m' ∧ m' ≤ k) (Option.toList m_opt)`, recovering `m_opt` by an explicit `rcases m_opt <;> rcases m_opt' <;> simp_all [OMap]` injectivity step; call as `limits_ok_invert _ _ h v_n m_opt rfl`.
- Dead ends (s9 lines 403-405): any combination of `cases`/`obtain`/`rcases`, including `set x := ... with hx; clear_value x; obtain ...`.

### 6.2 How many binder names does `cases h with | Ctor ...` take? [insights s3, lines 141-196]
- The count is NOT "constructor args + hypotheses": some args take no slot, some take a slot whose NAME is silently discarded (it was unified with an existing variable). Too few names is always safe (rest become inaccessible); too many is a hard error giving the exact count (`Too many variable names provided at alternative 'mk_Frame_ok': 12 provided, but 11 expected`). A name can be accepted and still not exist: you then get `Unknown identifier 'rt'` at the USE site with no error on the `cases` line (bundle15 misread this as an "`obtain` loses identifiers" bug).
- Recipe: (1) write the pattern with a deliberately too large number of `_`; (2) build, read `N expected`; (3) rewrite with exactly N entries naming only what you need; (4) if you then get `Unknown identifier 'foo'`, that slot's name was discarded; find what it was unified with (usually one of your own lemma's variables) and use that name.
- Calibration table (old generation, may differ after regeneration): `Extend_store.mk_Extend_store` 20 slots (the 2 store args take no slot; hyps: globals 1-3, mems 4-6, tables 7-9, funcs 10-12, datas 13-15, elems 16-18, `wf_store s` 19, `wf_store s'` 20); `Store_ok.mk_Store_ok` 25+ (12 list args then hyps, `s = {...}` is hyp 13 so slot 25); `Moduleinst_ok.mk_Moduleinst_ok` 40 (14 list args + 26 hyps, hyp k is slot 14+k); `Frame_ok.mk_Frame_ok` 11 (`s` no slot; `val_lst v_minst t_lst C` + 7 hyps); `Expr_ok2.mk_Expr_ok2` 7 (`s` no slot); `Config_ok.mk_Config_ok` 10; `State_ok.mk_State_ok` 7; `wf_uN.uN_case_0` 2 (`v_N` no slot, unified with literal 32); `wf_limits.limits_case_0` 4; `wf_tabletype.tabletype_case_0` 3; `wf_meminst.meminst_case_` 4; `Meminst_ok.mk_Meminst_ok` 8; `Tableinst_ok.mk_Tableinst_ok` 10; `Globalinst_ok.mk_Globalinst_ok` 7; `Eleminst_ok.mk_Eleminst_ok` 5 (`rt`'s name discarded); `Extend_eleminst.mk_Extend_eleminst` 4 (first two names discarded); `Extend_datainst.mk_Extend_datainst` 5 (first name discarded); `Blocktype_ok.valtype` / `.typeidx` 3 / 7.
- Trap: `induction h` and `cases h` do NOT agree on slot counts (`induction` forms one motive over all constructors, generalizes indices that `cases` would have unified away, so it gives MORE slots; `Externaddr_ok`'s `sub` case is 9 slots under `induction`, fewer under `cases`). Never reuse a `cases` pattern inside `induction` or vice versa.
- STALE ADVICE: bundle15's "use `cases h with | Ctor ...` instead of `obtain`" does not fix anything (same slot semantics) [insights s9 lines 412-415].

### 6.3 Encoding Rocq's `dependent induction` [insights s4, lines 200-240]
- Lean's `induction` refuses non-variable indices. Uniform encoding: a `private theorem foo_aux (c1 c2 : config) (h : Step c1 c2) : ∀ (s : store) (f : frame) ..., c1 = config.mk_config (state.mk_state s f) ais -> c2 = config.mk_config (state.mk_state s' f') ais' -> ... -> <conclusion>`; `induction h`; explicit `case` arms for the constructors needing the IH (`ctxt_label`, `ctxt_frame`, `local_set`); then `all_goals (intro s f ais s' f' ais' ... h1 h2 ...; injection h1 with hz1 _; injection h2 with hz2 _; subst hz1; try simp only [with_global, with_table, with_tableinst, with_elem, with_mem, with_meminst, with_data] at hz2; injection hz2 with _ hf; subst hf; exact hvals)`; the public theorem is `fun ... => foo_aux _ _ h s f ais s' f' ais' ... rfl rfl ...`. The `try` matters: where the state is unchanged `simp only` has nothing to do and would fail with "simp made no progress".
- Live instances: `reduce_inst_unchanged_aux`, `t_preservation_vs_type'_aux` (`TypePreservation.lean`), the four `Externaddr_invert_*_aux` (`ExtensionLemmas.lean`); later `t_preservation_type_aux` (2424), `store_extension_reduce_aux` (1441) (bundle18).
- Fact about `Step` (old generation, 23 constructors; re-check after regeneration): only `local_set` touches the frame (`with_local` rewrites `LOCALS`; every other `with_*` touches only the store), `ctxt_frame` changes only the inner frame, only `ctxt_label` and `ctxt_instrs` need the IH.

### 6.4 Mutual inductives `Instr_ok2` / `Instrs_ok2` / `Expr_ok2` [insights s5, lines 244-279]
- Rocq needs a hand-written `Scheme ais_ok_ind'`; Lean already generates the recursor. `@Instrs_ok2.rec` takes `{a : store}` as a PARAMETER (so the store is fixed across the induction; no need to generalize it into the motive), THREE motives (`motive_1` for `Instr_ok2`, `motive_2` for `Instrs_ok2`, `motive_3` for `Expr_ok2`) and 12 minor premises in declaration order: `Instr_ok2`'s 6 (`plain`, `label`, `Instr_ok2_frame`, `call_addr`, `ref`, `trap`), `Instrs_ok2`'s 5 (`empty`, `instr`, `seq`, `sub`, `Instrs_ok2_frame`), `Expr_ok2`'s 1 (`mk_Expr_ok2`); in each minor premise the IHs come AFTER all args and hypotheses.
- `Extend_store_ais` is `exact Instrs_ok2.rec (motive_1 := fun C ai ft' _ => Instr_ok2 s' C ai ft') (motive_2 := fun C ais' ft' _ => Instrs_ok2 s' C ais' ft') (motive_3 := fun C ae ts _ => Expr_ok2 s' C ae ts) (fun C vi t1 t2 hok _ hwfC hwfi => Instr_ok2.plain s' C vi t1 t2 hok hwfS' hwfC hwfi) ... 12 lambdas ... h`. To see the shape: put `set_option pp.explicit false in #check @Instrs_ok2.rec` just before `end TLC`, build, read the `info:` line, DELETE it (huge message). Tactic-mode precedent: `induction h using Instrs_ok2.rec (motive_1 := ...) (motive_3 := ...) with | ...` in `TypingLemmas.lean`'s `ais_single_typing_inversion'_gen`.

### 6.5 The zip-based `Forall₂` [insights s6 lines 283-321; triage v1 lines 8-16; gap_analysis s3b/s3e]
- `wasm2.0.lean:17-21` `[CHECK]` (docs say line 18): `Forall P xs := ∀ x ∈ xs, P x` (17-18), `Forall₂ P xs ys := ∀ p ∈ xs.zip ys, P p.1 p.2` (20-21).
- Pointwise lifts are free (`fun h p hp => ... (h p hp)`): every `Extend_store_*s` plural lemma is a one-liner; do not write an induction. Length is NOT implied: `Forall₂ P [a] []` holds vacuously. So `HelperLemmas.Forall2_nth`, `Forall2_lookup`, `Forall2_forall2` and friends are unprovable as stated, and so is `funcinst_same` without `hlen`; the usable replacement is `Forall2_nth_of_length` (takes the length as a hypothesis). Same for `wf_tableinsts_preserves`/`wf_memoryinsts_preserves` (false when `tbts` is longer; plan `(hlen : tbinsts.length = tbts.length)`) and the `Forall2_size`, `Forall2_size2`, `Forall2_seq_size` family (port with an explicit length premise; `t_read_preservation`/`store_extension_reduce` use them ~20 times in Rocq).
- To get the element at an index you must exhibit the zip pair: `HelperLemmas.mem_zip_getElem! l l' i hi hi' : (l[i]!, l'[i]!) ∈ l.zip l'`. To get `p.1 ∈ l1` from `p ∈ l1.zip l2`: `(List.of_mem_zip hp).1` (works even though `p` is not syntactically `(a,b)`, by structure eta).
- "Template B" `List.modify` bridge (all in `HelperLemmas.lean`; `[CHECK]` lines: `getElem!_modify_eq_or_ne` 50, `mem_modify` 76, `mem_zip_modify` 96, `mem_zip_modify₂` 120, `mem_zip_getElem!` 251, `Forall2_nth_of_length` 271, `mem_zip_modify_right` 298): `mem_modify f l : ∀ idx x, x ∈ l.modify idx f → x ∈ l ∨ (x = f (l[idx]!) ∧ l[idx]! ∈ l)`; `mem_zip_modify f l : ... p ∈ (l.modify idx f).zip ts → p ∈ l.zip ts ∨ (p.1 = f (l[idx]!) ∧ (l[idx]!, p.2) ∈ l.zip ts)`; `mem_zip_modify_right g l : ... p ∈ l.zip (ts.modify idx g) → p ∈ l.zip ts ∨ (p.1 = l[idx]! ∧ p.2 = g (ts[idx]!) ∧ (l[idx]!, ts[idx]!) ∈ l.zip ts)`; `mem_zip_modify₂ f g l` (both lists modified at the same index). Usage pattern: `intro p hp; rcases mem_zip_modify _ l ts idx p hp with hp' | ⟨h1, h2⟩; · exact h p hp'; · rw [h1]; exact <rebuild> (h _ h2)`. Used by all 7 `construct_*` lemmas and `t_preservation_vs_type'`'s `local_set` case.
- Mathlib bridge `to_mathlib_forall₂` / `from_mathlib_forall₂` (`HelperLemmas.lean` `[CHECK]` 879, 888; triage v1 says lines 508-525 then) convert zip-based `Forall₂` + length hypothesis into Mathlib's inductive `List.Forall2` (which supports `induction`).
- `Vals_ok v_S v_vals v_ts := v_ts.length = v_vals.length ∧ Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals`: types FIRST, values SECOND, length baked in (deliberate bundle9 strengthening). `obtain ⟨hlen, hall⟩ := hvals` destructs; `refine ⟨?_, ?_⟩` constructs.

### 6.6 Template A and C details, plus other reusable facts from triage v1
- Template A (lines 161-177) applies to `global_set_global_extension`, `store_none_mem_extension`, `memory_grow_mem_extension`, `table_set_table_extension`, `table_grow_table_extension`, `elem_drop_elem_extension`, `data_drop_data_extension`. Given `l' = list_update_func l idx f` (= `l.modify idx f`), prove `holds_upto (fun a => Extend_X (l[a]!) (l'[a]!)) l.length`: (1) `intro a ha` from `Forall`/`List.range` membership, get `a < l.length`; (2) `by_cases h : a = idx`; (3) `a ≠ idx`: `l'[a]! = l[a]!` via the `getElem!_modify` family (core has the non-`!` forms; bridge with `getElem!_pos`), then the already-proved `extend_X_refl_0`; (4) `a = idx`: `l'[idx]! = f (l[idx]!)`, rewrite with the `lookup_total l idx = ...` hypothesis, apply the `Extend_X` constructor with `Nat` arithmetic (`Nat.le_add_right`, `List.length_append`, `List.length_replicate`, `Nat.le_refl`). No Option split is needed. In practice bundle15/16 packaged this as `HelperLemmas.getElem!_modify_eq_or_ne`.
- Template C (lines 198-211): `Externaddr_invert_funcs/_tables/_mems/_globals` (ports of `extension_lemmas.v:1065-1159`; Rocq's `dependent induction` on `Externaddr_ok`'s `sub` constructor accumulating an `Externtype_sub` composed with `externtype_sub_trans`); `[CHECK]` current lines `ExtensionLemmas.lean` 551, 593, 635, 677.
- `Limits_sub` has 2 constructors (`max`/`eps`); `cases` on both hypotheses auto-discharges the impossible cross cases because the shared middle value is pinned; `Extend_store`'s constructor literally carries the `holds_upto` triples (so `se_invert_*` are `cases h; exact` of the field); `list_slice_update_length` is `induction ... using list_slice_update.induct; simp_all` (and `list_slice_update_forall` the same way); Lean's `pagediv` is plain `Nat` division, so no `Q`/`Z` floor bookkeeping (most of what made Rocq's `construct_meminsts_grow` long).

### 6.7 Syntax / elaboration gotchas [insights s7, lines 325-371; triage v3 lines 34-38; insights s9]
- Multi-line structure-instance literals are indentation-sensitive: continuation fields must be indented at least to the column of the FIRST field, else `unexpected identifier; expected '}'` (the reported position is NOT where the problem is). Put the first field on its own line (working layout in `TypePreservation.lean`'s `inst_match_locals_append` / `locals_append_eq`).
- `rw` is syntactic: `lookup_total l i` is a plain `def` for `l[i]!` and will not match; normalise first with `simp only [lookup_total] at h ⊢` or bridge `rw [show (l[i]! : α) = lookup_total l i from rfl]`.
- `simp` "made no progress" often means the goal is already `rfl`-true; `simp [append_context]` could not see through the `HAppend`/`Append` instance while `rfl` / `show ...; rw [h]` could.
- `OMap f o` and `o.map f` are defeq (and `(fun e => uN.mk_uN e)` is eta-equal to `uN.mk_uN`): `exact`/`refine` cope, `rw`/`simp only` do not. When a constructor wants `OMap f m_opt` and you have `j_opt`, first derive `j_opt = m_opt.map uN.mk_uN` and `subst`; unification cannot invent `m_opt`.
- `congrArg f h` elaborates `h`'s expected type from the goal: `exact congrArg frame.MODULE hf` can fail where `subst hf; rfl` works.
- `rcases ... with rfl` can delete the variable you wanted to keep (e.g. `hx : x = tv1 ∨ ...` may eliminate `tv1`); use `rcases hx with hx | ...` then `rw [hx]`.
- `injection h with ...` only works on constructor-headed equations; for `some (uN.mk_uN a) = Option.map f o` `rcases o` first (or `have : a = b := by simpa using h`).
- `Int.toNat ((2 ^ 32 : Int) - 1)` is the SAME expression in `wf_uN 32`'s bound and in `Tabletype_ok`'s `Limits_ok _ k`; that is how `construct_tableinsts_grow` gets `|v_r| + v_n ≤ 2^32-1` (from `Forall wf_tableinst tbinsts` via `wf_tableinst_parts`), exactly as Rocq's `inv_Forall HWftbinsts`.
- `simp_all` in a context holding `Meminst_ok`/`Store_ok` facts can hit `maximum recursion depth`: use targeted `simp only [...] at h` plus `subst` (fixed this way in `construct_meminsts_grow`) [triage v3 lines 34-36].
- `omega` will not unfold `Ki` (a `def`): use `Nat.add_mul` / `Nat.mul_div_cancel` explicitly; an `omega` "No usable constraints found" on an obviously true goal means an earlier metavariable leaked, fix the earlier step [s9 lines 407-411].
- `simp [Option.toList]` does not reliably unfold `Option.toList (some a)`; `rcases o with _ | a <;> simp_all` does [s9 lines 406-407].

### 6.8 Iteration tooling [insights s8, lines 375-397]
- IDE diagnostics (shown after `Edit`) are more informative than the CLI for binder-count / unknown-identifier errors and less informative for goal states. To see a full local context, provoke an "Application type mismatch" (apply a hypothesis to a wrongly typed argument); a bare `exact trivial` prints only the goal. `grep -c 'sorry$'` per file is the progress metric; the awk recipe at lines 386-391 prints the enclosing theorem of each `sorry`. Temporary `#print axioms TLC.t_preservation` at the end of `TypePreservation.lean` (remove afterwards) reports `[propext, sorryAx, Classical.choice, Quot.sound]` (insights s11 lines 481-488).

### 6.9 Machinery for the preservation proofs [insights s10 lines 419-456; prioritization v6]
- Splitting: `ais_seq_typing_inversion` (head + tail), `ais_composition_typing` (arbitrary prefix); one instruction's principal type: `ais_single_typing_inversion` + `unfold ai_principal_typing` (big `match` at `TypingLemmas.lean` ~311; `BR_TABLE` ~342 then); values: `ais_single_val_typing_inversion`, `Val_ok_non_bot`, `valtype_sub_non_bot`, `resulttype_sub_non_bot`; composing subtyping: `instrtype_sub_compose_le/_ge/_eq/1/2` (`Subtyping.lean`; the `_eq` form also returns the `ResulttypeSub` between the two middle types, which is how you learn the value's type IS the expected type once it is not `BOT`); rebuilding: `construct_ai_val`, `construct_ai_const_I32`, `construct_ai_ref`, `construct_ai_maybe`, `construct_ais_typing_single`, `construct_ais_subtyping`, `construct_ais_compose`, `construct_ais_vals'`, `ais_empty_typing`; context plumbing: `prepend_label`, `construct_inst_prepend_label`, `construct_inst_match_label`, `lookup_label_0`, `lookup_label_1`, `proj_identity`; wf side conditions: `ainstrs_ok_context_store_wf` returns `wf_context ∧ wf_store ∧ Forall wf_admininstr` IN THAT ORDER.
- Templates: `Step_pure__select_preserves_helper` (peel with three `ais_seq_typing_inversion`s, pin `CONST`'s principal type, case-split the `SELECT` annotation: `some [t]`/`none` give the type, `some []` and `some (_::_::_)` are `False`, compose with `instrtype_sub_compose_ge` twice then `instrtype_sub_compose_eq`, then `resulttype_sub_non_bot`), `Step_pure__if_preserves_helper`, `Step_pure__br_if_preserves`, `Step_pure__label_vals_preserves`, `Step_pure__frame_vals_preserves`.
- Routes (v6): `br_table_ge`: `ai_principal_typing` for `BR_TABLE ls l'` gives `∃ t1s ts t2s, ft = mkFunctype (t1s ++ ts ++ [I32]) t2s ∧ (∀ l ∈ ls, ...) ∧ (∃ r', C.LABELS[l']? = some r' ∧ Resulttype_sub (.mk_list ts) r')`; `BR l` gives `∃ t1s ts t2s, ft = mkFunctype (t1s ++ ts) t2s ∧ C.LABELS[l]? = some (.mk_list ts)`; copy the shape of `br_if`; rebuild `BR l'` via `construct_ai_maybe` + `Instr_ok.br` writing `r'` as `.mk_list (proj_list_0 valtype r')` with `proj_identity`; widen with `construct_ais_subtyping`; chain `resulttype_sub_trans`/`resulttype_sub_app`; the `v_l.length ≤ ...` premise is NOT needed. `br_table_lt`: instantiate `∀ l ∈ ls, ...` at `ls[i]!` (`i = proj_uN_0 (Option.get! (proj_num__0 v_i))`) using `HelperLemmas.Forall_nth'` or `getElem!_pos` + `List.getElem_mem`; the `i < ls.length` premise IS needed. `br_zero`/`br_succ`/`return_label`: `LABEL_` principal typing as in `Step_pure__label_vals_preserves`, `ais_composition_typing` the body three ways, `lookup_label_0` / `lookup_label_1`, rebuild with `construct_ais_vals'`/`construct_ais_compose`/`construct_ais_subtyping`; `RETURN` reads `C.RETURN` not `C.LABELS`, and `prepend_label` leaves it untouched, which is why `return_label` goes through (all five are proved by now).

### 6.10 Misc modelling facts
- Lean model uses `Nat` and `rat_to_nat` where Rocq uses `Q`/`Z` (`pagediv`, `Qfloor_add_Z`, `Zle_Nle` need no Lean counterpart; gap_analysis s3d, s3b). `list_update := List.set`, `list_update_func := List.modify`. Rocq bool-vs-Prop `<?`/`<` bridges (`update_forall_lt/le/le_u32`), mathcomp `iotaN` lemmas (`nth_iotaN`, `size_iotaN`, `iota_snocN`), `in_same_as_In`, `cvt_*`, `sizecat'` etc. have no counterpart (one list library, one `Nat`).
- with_mem: the Lean backend's rendering of `SliceSeg` matters; `list_slice_update` (Rocq prelude, `print.ml:919`, `wasm.v:66-74`; Lean copy `HelperLemmas.lean:159`) is length-preserving; the regenerated `with_mem` uses `splice`, bridged by `splice_eq_list_slice_update (l b : List α) (i : Nat) : splice l b i = list_slice_update l i b.length b` (467) and `splice_length` (492).

## 7. Relevance to the upstream changes (vcvtop/TRUNC_SAT, vloadop/SHAPE, ishl_/ishr_/vshiftop, iadd_/memory bulk rules, Step_read_is_wf, stuck cases, bundle19 hand edits)

STATUS NOTE: by 16:05 the tree already contains the re-synchronisation (bundle21: hand edits re-applied, `Step_read_is_wf` proved, TypeProgress fully proved). The entries below give what the DOCS say and where things are now, so the main session can verify rather than redo.

### 7.1 Step_read_is_wf, Step_is_wf, Step_pure_is_wf, and the memory.fill/copy/init `iadd_` change (upstream items 4 and 5)
- [DOC with_mem issue lines 137-148] Upstream `wasm.v` has hand-edited `Step_read_is_wf` and `Step_is_wf` to take an extra `Store_ok (fun_store z)` premise ("the store bounds are needed for table.size, memory.size and the bulk rules"). `Step_read_is_wf` was `Admitted` with the author's note that 3 cases (4 goals: memory.fill-succ, memory.copy-le, memory.init-succ) are NOT derivable even under `Store_ok`: they push `CONST I32 (i + 1)` where `i = 2^32 - 1` is allowed, and `2^32` is not a `u32`. The generated Lean versions lacked the `Store_ok` premise and were `sorry`. `t_preservation` depends on `Step_is_wf`; `t_pure_preservation` on `Step_pure_is_wf` (`Qed` upstream).
- [DOC prioritization v7 lines 44-51] Corner-case falsity: on a memory of exactly 2^16 pages, `memory.fill/copy/init` with `i = 2^32 - 1`, `n = 1` push `CONST I32 2^32`, not well-formed; so `Step_read_is_wf`, `Step_is_wf`, `t_read_preservation`, `t_preservation` are false there, in Rocq too (a spec issue). "Proofs should take wf of the reduct from `Step_read_is_wf` / `Step_is_wf`, exactly as Rocq does." [DOC dependencies v6 lines 32, 36] `Step_is_wf (generated; FALSE in a corner case)`.
- WHAT CHANGES WITH UPSTREAM (4): the corner case disappears (`iadd_ 32 i 1` wraps, so the constant stays a valid `u32`); those four statements become true; every "false in a corner case" / "pending a spec-side fix" / "Admitted upstream" note is stale (already rewritten in `TypePreservation.lean`; `claude-logging/for-claude/is_wf_theorems.md` not checked by me).
- [CHECK 12:34 snapshot] the freshly regenerated `wasm2.0.lean` had `Step_pure_is_wf` 12879, `Step_read_is_wf` 13274, `Step_is_wf` 13383 as plain generated `sorry` without `Store_ok`, in `(var_0 ...) (var_1 ...)` shape, while the Lean callers used the hand-edited 3-underscore-plus-`hsok` convention. `[CHECK 16:10]` the hand-edited shapes are back: `Step_pure_is_wf (var_0 var_1 : List admininstr)` 14016 (proved); `theorem Step_read_is_wf (z : state) (admininstr_lst : List admininstr) (var_1 : List admininstr) : wf_config (config.mk_config z admininstr_lst) → Store_ok (fun_store z) → Step_read (config.mk_config z admininstr_lst) var_1 → Forall (fun var_1_elem => wf_admininstr var_1_elem) var_1` 16101 (proved, comment: "Proved here (bundle21), as in Rocq since upstream `6582b3a39`: spec commit `4cf9f29c5` made memory.fill/copy/init push `CONST I32 $iadd_(32, i, 1)` (wrapping)"); `Step_is_wf (z) (admininstr_lst) (var_1 : config)` 16325 (proved, after `Store_ok`). Callers: `TypePreservation.lean:2038` `Step_read_is_wf _ _ _ hwfc hsok hstep`, `:2692`, `:2746` `Step_is_wf ...`; `TypeProgress.lean:3859, 4087, 4097, 4266, 4316, 7141, 7203, 7429, 7523, 7727, 7792`.
- [CHECK 16:10] `Step_read` rules in `wasm2.0.lean`: `memory_fill_succ` (14586), `memory_copy_le` (14603), `memory_init_succ` (14629) push `CONST I32 (num_.mk_num__0 Inn.I32 (iadd_ 32 (Option.get! (proj_num__0 i)) (uN.mk_uN 1)))` (copy_le and init_succ push such a pair for `j` and `i`); `memory_copy_gt` (14610) is unchanged (`Int.toNat ((... + v_n : Int) - 1)`); the TABLE twins `table_fill_succ` (14429), `table_copy_le` (14445), `table_init_succ` (14470) STILL push `uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)`; their premises bound `i + v_n ≤ |REFS|` with `v_n ≠ 0`, so their wf needs the table-size bound from `Store_ok`, consistent with the docs' "store bounds needed for table.size, memory.size and the bulk rules". Hypothesis counts are unchanged (fill_succ 3, copy_le 5, init_succ 5), matching the case patterns in `t_read_preservation` (`TypePreservation.lean:2339, 2361, 2401`; table cases 2205, 2234, 2278; `memory_copy_gt` 2378). The `Step_read_is_wf` proof has matching case arms (16159-16309) and uses `iswf_I32_iadd1` / `iswf_I32_const` / `iswf_I32_const_lt` helpers.
- [INFERENCE] The existing `t_read_preservation` proofs of those cases take every pushed constant's wf from `hwf' := Step_read_is_wf ...` (`ais_const1 ... (wf_const_num (hwf' _ (by simp)))`), so they need no change; the real work was `Step_read_is_wf` itself, which needs `iadd__is_wf` (proved, `wasm2.0.lean:3075`) for the three memory cases and the `Store_ok`-derived bounds (`Tabletype_ok`/`Limits_ok` size <= 2^32-1; memory <= 2^16 pages) for table.size / memory.size / the table bulk cases.
- bundle19 hand edits (not described in the 12 docs, which predate bundle19): `OLD_wasm2.0.lean` holds 54 hand-written `iswf_*` helper theorems; `[CHECK 16:10]` the current `wasm2.0.lean` has 65 `iswf_*` theorems (e.g. `iswf_uN_of_lt` 359, `iswf_I32_const` 13971, `iswf_rat_to_nat_floor` 13990, `iswf_rat_to_nat_le` 14000, `iswf_grow_pages` 14006, `iswf_I32_const_lt` 16064). The 12:34 snapshot had none of them.

### 7.2 vcvtop / TRUNC_SAT (upstream items 1 and 5)
- The docs contain nothing about the stuck F32->I16 TRUNC_SAT case or `vcvtop_trunc_sat_i16` (Progress-only; Progress "not started" in all 12 docs). What they do contain: gap_analysis s3a lists `ais_vcvtop_typing_inversion` and `Step_pure__vcvtop_preserves` among the 47 SIMD lemmas to port ("each inversion is `ais_single_plain_typing_inversion` then invert `Instr_ok`, each `Step_pure__v*` is one `vec_preserves_k` application"; "The Lean `Instr_ok`/`Step_pure` vector constructors line up with Rocq's statements (checked `Instr_ok.vconst ... vcvtop`, `Step_pure.vvunop ... vcvtop`)"; "`TypingLemmas.ai_principal_typing` needs no change", Rocq still sends vector instructions to `_ => True`). And s3g lists `trunc_sat_total`, `demote_nonempty`, `promote_nonempty` among the 12 Progress-only axioms ("a mis-transcribed axiom is an inconsistency").
- [CHECK 16:10] `wasm2.0.lean`: `inductive vcvtop__Fnn_1_M_1_Inn_2_M_2` (1648) with `TRUNC_SAT (v_sx : sx) (zero_opt : Option zero)`, and `vcvtop__.mk_vcvtop___2 (Fnn_1) (M_1) (Inn_2) (M_2) (var_x : vcvtop__Fnn_1_M_1_Inn_2_M_2)`; `wf_vcvtop__.vcvtop___case_2` has `shape_2 = shape.X (lanetype_Inn Inn_2) ...`. (12:34 snapshot vs OLD, by structural diff: `fun_zeroop` and `fun_halfop` went from 41 to 37 constructors, the four F32/F64 -> I8/I16 TRUNC_SAT cases 28-31 removed and `..._before_..._case_40` renamed `_case_36`; `fun_lcvtop__` stays at 37 with the TRUNC_SAT constructor type renamed; old name was `vcvtop__Fnn_1_M_1_Jnn_2_M_2`.)
- [CHECK] The preservation lemmas (`TypePreservationPure.lean`): `ais_vcvtop_typing_inversion` 1499, `Step_pure__vcvtop_preserves` 1812, `vec_preserves_1/2/3` 1510/1528/1551; `Instr_ok.vcvtop` (now `wasm2.0.lean:13047`) is textually identical to the old one and takes `vcvtop : vcvtop__` as an opaque parameter, so these are unaffected (file untouched since Oct 3). The affected Lean code was Progress; `[CHECK 16:10]` `TypeProgress.lean` already uses `vcvtop__Fnn_1_M_1_Inn_2_M_2_case_0` (3371, 3724, 3768), has dropped the `~~ vcvtop_trunc_sat_i16` premises (comments at 3295-3302, 3398, 3551, 3575, 3610, 3631, 3653) and its counterexample lemmas (7942-7946), and has no `sorry`; `HelperLemmas.lean:850` `axiom trunc_sat_total` remains (re-verify against upstream `axioms.v`).

### 7.3 vloadop / SHAPE (upstream items 2 and 5)
- Docs: gap_analysis s3b lists `ais_vload_typing_inversion`, `ais_vload_lane_typing_inversion`, `Step_read__vload_preserves`, `Step_read__vload_lane_preserves`, `ais_vstore*` as lemmas to port; bundle18 v6 (line 62) says the two `Step_read__vload*` exist; v7 (line 33) says "the 5 vector-load value cases (two lemmas already exist)" for `t_read_preservation`. No mention of the 64x1 stuck case.
- [CHECK 16:10] `wf_vloadop_.vloadop__case_0` (`wasm2.0.lean:1877-1881`) now has `(... = vsize/2) ∧ (v_M > 1)`; `Instr_ok.vload_pack` (13227) and `Step_read.vload_shape_oob/val` (14515/14520) use `vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx`. Lean consumers: `TypePreservation.lean` 544, 554, 564, 583, 596; the proof arms `vload_shape_oob`/`vload_shape_val` in `Step_read_is_wf` (16241, 16243); `TypeProgress.lean` `t_progress_be_vload_pack` (its header says it now refutes `SHAPE 64 X 1` via `M > 1`). [INFERENCE] the preservation lemmas use `wf_instr`/`Instr_ok` hypotheses abstractly and do not care about `M > 1`; their Lean signatures must still match Rocq's regenerated statements (rule 4).

### 7.4 ishl_ / ishr_ / vshiftop (upstream items 3 and 5)
- Docs: gap_analysis s3g lists `ishl_wf` and `ishr_wf` as Progress-only axioms to port; s3a lists `ais_vshiftop_typing_inversion` and `Step_pure__vshiftop_preserves`. Nothing else.
- [CHECK 16:10] `opaque ishl_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN` (3205) with `ishl__is_wf` (3212, still `sorry`; premises `wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val = ishl_ ... → wf_uN v_N ret_val`) and `ishr_` (3220, extra `v_sx`) with `ishr__is_wf` (3227, `sorry`); the old version took `(v_u32 : u32)`. `fun_binop_` now passes `iN_2` directly (old: `(uN.mk_uN (proj_uN_0 iN_2))`); `fun_vshiftop_` (from 11138) uses `ishl_ (lsizenn (lanetype_Jnn J)) lane (uN.mk_uN (v_n % (lsizenn (lanetype_Jnn J))))` and the same shape for `ishr_` (8 occurrences of `v_n % (lsizenn`). `Step_pure.vshiftop` (13838) is textually identical to the OLD rule, so `Step_pure__vshiftop_preserves` (`TypePreservationPure.lean:1689`) and `ais_vshiftop_typing_inversion` (1399) are unaffected.
- `HelperLemmas.lean`: `axiom ishl_wf`/`ishr_wf` (with `(k : u32)`) are GONE as of 16:05 (comment at line 844: "bundle21: Rocq's `ishl_wf`/`ishr_wf` (95c256c2c `axioms.v:83-86`) were deleted upstream..."); `TypeProgress.lean`'s header (line 54) says the generated `ishl__is_wf`/`ishr__is_wf` apply directly. Those two generated theorems are `sorry` over an `opaque` function and cannot be proved from the Lean model (same family as the other 60).

### 7.5 The stuck cases
- Not discussed in any of the 12 documents. Context only (current file headers): `TypeProgress.lean` (header lines 28-31, 46-52) says the counterexample families `vload_shape64_*` and `vcvtop_trunc_sat_i16_*` were ruled out by spec commit `4cf9f29c5` (`SHAPE` now needs `M > 1`; `TRUNC_SAT` needs an `Inn` destination) and Rocq `6582b3a39`, and that `t_progress_be` is now fully proved, "no `sorry` in this file"; `#sorry_deps TLC.t_progress` lists only generated numeric `*_is_wf` of opaque functions.

## 8. Other notable

- Upstream history [DOC gap_analysis s0-s1]: tip of `rocq-backend-proof-final` was `95c256c2c` (2026-09-29, "Updated rocq output and proofs. No more admits on preservation!"), merged locally at `8ac6699ac`; `git diff 95c256c2c HEAD -- spectec/test-rocq/theories` was empty. `Admitted` counts (`type_preservation.v`/`type_preservation_pure.v`/`extension_lemmas.v`): `5b03ae067` (session-1 checkout, 07-01) 3/2/0; `a8b585cdb` (09-22) 0/0/1; `58af2e2f9`...`ee6365844` (09-24...09-29) 0/0/1; `95c256c2c` 0/0/0. `t_pure_preservation`, `store_extension_reduce`, `t_read_preservation`, `t_preservation_type`, `Step_pure__return_frame_preserves` (body at `type_preservation_pure.v:490-547`) are all `Qed` upstream since `a8b585cdb`. How the error survived: session 1 digested the old checkout and wrote "mirror the Rocq gap" in the Lean headers; bundle3 correctly reported zero `Admitted` but headers were never updated; bundle13's resync asserted without re-checking that `store_extension_reduce` "remains `Admitted` overall"; bundles 15-16 inherited it.
- Rocq line anchors cited by the docs: SIMD section `type_preservation_pure.v:883-1524`; `br_table_ge` at `:432`; `extension_lemmas.v:1065-1159` (`Externaddr_invert_*`), `:787` (`funcinst_same` at `5b03ae067`); `backend-rocq/print.ml:467` and `:919`, `wasm.v:66-74` (`list_slice_update`); `backend-lean/backend.ml:795-834` (`SliceSeg`); spec `specification/wasm-2.0/5-runtime-aux.spectec:108` (`$with_mem`), `8-reduction.spectec:546-552` (store rules), `554-576` (`store-pack`, `vstore`, `vstore_lane`).
- gap_analysis s3 lists (as of bundle17): s3a 47 SIMD lemmas missing in TypePreservationPure (the doc says "21 `Step_pure__v*`" but names 20: 5 + 19 + 3 + 20 = 47; `[CHECK]` the tree has 20); s3b 24 missing in TypePreservation, 23 to port: `wf_context_app`, `wf_context_tab`, `wf_context_mem`, `wf_tableinsts_preserves`, `wf_memoryinsts_preserves`, `list_update_func_preserves_prop`, `list_update_func_forall_inv`, `Forall_list_update_func`, `wf_store_mem_update`, `wf_store_mem_update'`, `mem_store_extension`, `ais_seq3_last_typing`, `ais_vstore_mems_inversion`, `ais_vstore_lane_mems_inversion`, `ais_vload_typing_inversion`, `ais_vload_lane_typing_inversion`, `ais_vstore_typing_inversion`, `ais_vstore_lane_typing_inversion`, `Step_read__vload_preserves`, `Step_read__vload_lane_preserves`, `vec_store_preserves_2`, `Step__vstore_preserves`, `Step__vstore_lane_preserves` (not ported: `Qfloor_add_Z`); s3c 8 TypingLemmas to port: `ai_typing_inversion'`, `wf_admininstr_instr` (the `↔` version), `seq_mid_not_null`, `construct_instr_from_ai`, `construct_instr_from_ai_single`, `construct_instrs_from_ais`, `revert_to_instr_from_ai`, `revert_to_instrs_from_ais` (intended deviations: `fun_res_list__list` = `proj_list_0`, `fun_list__res_list` = `list.mk_list`, `functype_from_lists` = `mkFunctype`); s3d 28 Extension names (port cheaply: `holds_upto_lookup/_S/_all/_all_strong/_all_strong'/_lt/_lt_refl`, `update_holds_upto_lt/_le`; no counterpart needed: `update_forall_lt/le/le_u32`, `nth_iotaN`, `size_iotaN`, `iota_snocN`, `pagediv*`, `Qfloor_add_Z`, `Zle_Nle`; superseded: `list_update_func_subst/unchanged`, `forall_preserved_bytes` (= `list_slice_update_forall`), `invert_meminst` (= `wf_meminst_parts`)); s3e 27 Helper names (port: `prepend_local`, `prepend_return`, `append_local`, `append_label`, `append_return`, `Forall_size`, `Forall2_size`, `Forall2_size2`, `Forall2_seq_size` with explicit length premises; already ported renamed: `_append_option_none*` -> `option_orElse_none`/`option_none_orElse`/`option_some_orElse`); s3f 10 Subtyping names none needed (`Resulttype_subtype` = `ResulttypeSub`).
- Plan when resumed [DOC gap_analysis s6]: signatures first (TypingLemmas 8, fix `br_table_ge`, TypePreservationPure 47, TypePreservation 23, helpers), fix stale doc comments, then proofs cheapest and most-depended-on first. [CHECK] largely executed in bundles 18-21.
- Lemma-level tree of `t_preservation` at end of bundle18 [DOC dependencies v6 lines 19-37]: `store_extension_reduce` (PROVED; `store_extension_reduce_aux` by induction on `Step`; `global_set_store_ok`, `table_set_store_ok`, `table_grow_store_ok`, `elem_drop_store_ok`, `data_drop_store_ok` via `minst_invert_*`, `Store_ok_parts`/`of_parts`, `Extend_store_of_parts`, `*_extension`, `construct_*`; `with_mem_store_ok` -> `mem_store_extension` (PROVED) <- `splice_eq_list_slice_update` + generated `nbytes__is_wf`/`ibytes__is_wf`/`vbytes__is_wf`/`wrap___is_wf`; `memory_grow_store_ok` -> generalized `construct_meminsts_grow`, `memory_grow_mem_extension`, `rat_to_nat_natCast`), `t_preservation_type` (PROVED via `t_preservation_type_aux`; `Step_is_wf`, `t_pure_preservation` (PROVED) with `Step_pure_is_wf`, `t_read_preservation`), `t_preservation_vs_type`, `reduce_inst_unchanged`, `Extend_store_moduleinst` (PROVED), `Step_is_wf` again for the post-config's wf.
- Inputs listed for `t_read_preservation` [DOC dependencies v6 lines 53-67]: `Step_read_is_wf`; `ainstrs_ok_context_store_wf`; `construct_ais_trap`; `ais_empty_typing`; `ais_args{1,2,3}_typing` and the `inv_*` operator inversions; `construct_ai_const_I32`, `construct_ai_val`, `construct_ai_ref`, `construct_ais_compose`, `construct_ais_subtyping`, `construct_ais_vals`, `ais_vals_typing_inversion`, `construct_instrs_from_ais`; `bt_inversion`, `minst_invert_*`, `lookup_global`, `s_invert_*`, `Externaddr_invert_*`, `tableinst_ok_invert`; `Step_read__vload_preserves`, `Step_read__vload_lane_preserves`, `externtype_table_sub_inv`, `getElem?_eq_some_bang`, `Moduleinst_ok_lengths`. Missing then: `instrtype_sub_prefix`, a general-`nt` constant constructor, the remaining `inv_*` inversions (`TABLE_FILL`, `TABLE_COPY`, `TABLE_INIT`, `MEMORY_FILL`, `MEMORY_COPY`, `MEMORY_INIT`, `LOAD`, `TABLE_GET`, ...), `Val_ok` of `default_` values (for `call_addr`). All done by bundle19 per the current `TypePreservation.lean`.
- Internal inconsistencies in the docs: proof_dependencies_v4 lines 47-48 editing artifact; gap_analysis "21" vs 20 names; triage v1 and v2 say "no Rocq counterpart" for two lemmas that existed at `5b03ae067`.

## 9. Cross-check tables of the working tree (my own read-only checks, NOT from the docs)

- Files at ~16:10 [CHECK]: `wasm2.0.lean` 16612 lines, 1,338,199 bytes, mtime 16:05:35 (hand edits re-applied, 65 `iswf_*` helpers, 152 `*_is_wf` theorems of which 62 have a `sorry` body, all about `opaque` functions; 64 `opaque` defs in the file); `OLD_wasm2.0.lean` 16351 lines (bundle19 version, Oct 15 00:56); `HelperLemmas.lean` 896 lines (mtime 16:05:35); `TypePreservation.lean` 2888 (16:05:35); `TypeProgress.lean` 7948 (16:05:35); `ExtensionLemmas.lean` 2271 (Oct 6); `TypePreservationPure.lean` 1976 (Oct 3); `TypingLemmas.lean` 1960 (Oct 15 00:56); `Subtyping.lean` 681 (Oct 2).
- The 62 sorry'd generated `*_is_wf` (all about `opaque` functions; `Admitted` in Rocq): `s33_to_u32`, `extend__`, `fabs_`, `fceil_`, `ffloor_`, `fnearest_`, `fneg_`, `fsqrt_`, `ftrunc_`, `iclz_`, `ictz_`, `ipopcnt_`, `wrap__`, `fadd_`, `fcopysign_`, `fdiv_`, `fmax_`, `fmin_`, `fmul_`, `fsub_`, `iand_`, `ior_`, `irotl_`, `irotr_`, `ishl_`, `ishr_`, `ixor_`, `feq_`, `fge_`, `fgt_`, `fle_`, `flt_`, `fne_`, `convert__`, `demote__`, `promote__`, `reinterpret__`, `trunc__`, `trunc_sat__`, `narrow__`, `ibits_`, `fbits_`, `ibytes_`, `fbytes_`, `nbytes_`, `vbytes_`, `inv_ibits_`, `inv_fbits_`, `inv_ibytes_`, `inv_fbytes_`, `inv_nbytes_`, `inv_vbytes_`, `inot_`, `irev_`, `iandnot_`, `ibitselect_`, `iavgr_`, `iq15mulr_sat_`, `fpmin_`, `fpmax_`, `lanes_`, `inv_lanes_`.
- Structural diff OLD vs the 12:34 regenerated-unedited file (python3 -I, scratch scripts in the work dir; `deriving` lines and comments ignored): only 14 generated definition blocks differed semantically: `vcvtop__`, `wf_vcvtop__`, `wf_vloadop_`, `fun_idiv_` (OLD only had hand `example`s), `fun_binop__before_fun_binop__case_38`, `fun_binop_`, `fun_zeroop`, `fun_halfop`, `fun_lcvtop___before_fun_lcvtop___case_36`, `fun_lcvtop__`, `fun_vshiftop_`, `Step_read`, `fun_instantiate` (cosmetic bound-variable renames `i_90093` -> `i_82780`), `Store_ok` (only a hand comment removed). 65 declaration headers existed only in OLD (54 `iswf_*` hand helpers, the old `vcvtop__Fnn_1_M_1_Jnn_2_M_2` triple, old `ishl_`/`ishr_` + `_is_wf`, `fun_zeroop_before_...case_40`, `fun_halfop_before_...case_40`, hand-edited `Step_read_is_wf`/`Step_is_wf`); 11 only in the regenerated file. The regenerated file also adds `deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq` clauses (about 120 inductive blocks differ only by that).
- Current locations of the helper lemmas the docs name (all exist): `ExtensionLemmas.lean`: `Externaddr_invert_funcs` 551, `_tables` 593, `_mems` 635, `_globals` 677, `Extend_store_externaddr` 1633, `Extend_store_eleminst_ext` 1683, `Extend_store_datainst_ext` 1698, `Extend_store_frame` 1856, `Extend_store_ais` 1875, `extend_funcinst_eq` 1088, `funcinst_same` 1110 (with `hlen`), `Extend_store_wf_store` 1122, `Extend_store_wf_store'` 1127, `extend_meminst_bytes` 974, `construct_meminsts_grow` 2196; `HelperLemmas.lean`: `getElem!_modify_eq_or_ne` 50, `mem_modify` 76, `mem_zip_modify` 96, `mem_zip_modify₂` 120, `Forall_nth'` 235, `mem_zip_getElem!` 251, `Forall2_nth_of_length` 271, `mem_zip_modify_right` 298, `list_slice_update` 159, `list_slice_update_length` 436, `list_slice_update_forall` 449, `splice_eq_list_slice_update` 467, `splice_length` 492, `prepend_label` 586, `lookup_label_0` 623, `lookup_label_1` 628, `to_mathlib_forall₂` 879, `from_mathlib_forall₂` 888; `TypingLemmas.lean`: `ainstrs_ok_context_store_wf` 265; `TypePreservationPure.lean`: `proj_identity` 548, `Step_pure__br_table_ge_preserves` 599; `TypePreservation.lean`: `store_extension_reduce_aux` 1441, `store_extension_reduce` 1614, `t_read_preservation` 2030, `t_preservation_type_aux` 2424, `t_preservation_type` 2681, `t_preservation` 2701.
- `HelperLemmas.lean` project axioms [CHECK 16:10] (lines 725-856, 21 of them): `nbytes_len`, `ibytes_len`, `nbytes_len'`, `ibytes_len'`, `ibytes_len''`, `vbytes_len'`, `truncz_quot`, `lanes_len`, `nbytes_inv`, `ibytes_inv`, `vbytes_inv`, and the Progress-only block `ibits_inv`, `feq_bit`, `fne_bit`, `flt_bit`, `fgt_bit`, `fle_bit`, `fge_bit`, `trunc_sat_total`, `demote_nonempty`, `promote_nonempty` (it was 23 before 16:05, with `ishl_wf`/`ishr_wf` at 844/847).

## 10. Safety check (END), verbatim

(Appended below by the final command, which runs the check and tees its output into this file.)

Command: `bash /tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/verify.sh digest-old2-end` (exit code 0)

```
safety check [digest-old2-end] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T081413.584560240Z-digest-old2-end-498020.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
0a1,40
>  M spectec/src/test-lean-claude/.lake/build/ir/TypeProgress.c
>  M spectec/src/test-lean-claude/.lake/build/ir/TypeProgress.c.hash
>  M spectec/src/test-lean-claude/.lake/build/ir/wasm2.0.c
>  M spectec/src/test-lean-claude/.lake/build/ir/wasm2.0.c.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/ExtensionLemmas.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/ExtensionLemmas.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/ExtensionLemmas.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/HelperLemmas.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/Subtyping.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservation.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservationPure.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservationPure.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypePreservationPure.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypeProgress.trace
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.trace
>  D spectec/src/test-lean-claude/.lake/build/lib/lean/TypingLemmas.trace.nobuild
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.ilean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.ilean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.olean
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.olean.hash
>  M spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace
>  M spectec/src/test-lean-claude/HelperLemmas.lean
>  M spectec/src/test-lean-claude/TypePreservation.lean
>  M spectec/src/test-lean-claude/TypeProgress.lean
2a43
> ?? spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/
```

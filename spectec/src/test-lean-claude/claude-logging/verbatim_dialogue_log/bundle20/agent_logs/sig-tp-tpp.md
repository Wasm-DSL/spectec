# sig-tp-tpp — signature audit: TypePreservation.lean + TypePreservationPure.lean vs type_preservation.v + type_preservation_pure.v (bundle20, v2 relaunch)

## Task

Subagent "sig-tp-tpp" of the bundle20 preservation audit (v2 relaunch, merging the first-wave
labels `sig-tp` and `sig-tpp`). For every Rocq declaration in `type_preservation.v` and
`type_preservation_pure.v`, judge whether its Lean counterpart (in `TypePreservation.lean` /
`TypePreservationPure.lean`) has an equivalent statement (binders, premises, conclusion, modulo the
notation table of brief §6) and whether any difference is documented in the Lean doc comment. For
every Lean-only declaration, check it is labelled as a Lean-only helper and that its statement is
plausible. Primary input: the pre-extracted side-by-side files `scratchpad/sigs/sbs_tp.md` (1777
lines) and `scratchpad/sigs/sbs_tpp.md` (1602 lines); real sources opened only to resolve doubts.
Read-only w.r.t. the repo; only this log file is written. No Lean is run.

## Safety check (START)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" sig-tp-tpp
safety check [sig-tp-tpp] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T105046.386631709Z-sig-tp-tpp-1402870.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Resumed (v2 relaunch)

First-wave partial logs read: `agent_logs/sig-tp.md` (only read the brief; no findings) and
`agent_logs/sig-tpp.md` (read both TPP files, counted 76 Rocq `Lemma`/`Theorem` + 79 Lean
`theorem`s = 76 ports + 3 Lean-only; citation check: 27 stale line numbers, all from Rocq revision
`5b03ae067` — stale line numbers are a KNOWN issue per brief §6b and are not re-reported). No
statement comparison had been done by either; this run does it from scratch.

## Progress (incremental)

- Read shared brief v2 (169 lines) and task file (14 lines).
- Read `scratchpad/sigs/sbs_tpp.md` in full (l.1-1602): 76 Rocq declarations (all match=EXACT) + 1
  Ltac (skipped) + 3 Lean-only theorems. Compared every pair statement-by-statement (binders,
  premises, conclusion). Items flagged for source check: `proj_identity` (Rocq polymorphic over
  `A : eqType`, Lean fixed to `valtype`), `Step_pure__br_table_lt_preserves` (`!(..)`/`:> N`/`<?`
  notation), `Step_pure__ref_is_null_true_preserves` (Rocq `admininstr_REF_NULL v_rt` vs Lean
  `admininstr_instr (instr.REF_NULL v_rt)`), `res_N` vs `N`.
- Read `scratchpad/sigs/sbs_tp.md` in full (l.1-1777): 36 Rocq declarations (35 EXACT, 1 NONE =
  `Qfloor_add_Z`) + ~95 Lean-only declarations (last entry `for` at l.2673 is an extractor artifact:
  the word "lemma" inside `t_preservation_type`'s doc comment).
- Source checks done (sed/grep ranges only):
  - trust constructs: `grep sorry|axiom|native_decide|admit|implemented_by|unsafe|extern|set_option`
    over both files -> hits only inside comments (TP l.21,26,2016-2017,2697; TPP l.23). None in code.
  - `_is_wf` uses: TPP l.1863 `Step_pure_is_wf`; TP l.1552/1561/1571/1579 `nbytes__is_wf`,
    `ibytes__is_wf`, `wrap___is_wf`, `vbytes__is_wf` (inside `store_extension_reduce_aux`; all four are
    in the known list of 32 numeric sorries), l.1982 `default__is_wf`, l.2036 `Step_read_is_wf`,
    l.2690 `Step_is_wf`.
  - Rocq `type_preservation.v` l.70-86: `num_default_is_well_formed` is commented out upstream (Lean
    header l.24 documents this). `Qfloor_add_Z` exists at Rocq TP l.28 and EL l.2895; used at TP
    l.1335; no Lean mention.
  - Rocq `wasm.v` l.50-75 (`list_update_func`, `list_slice_update` with `(i j : N)`), l.112 (`@@` =
    `_append`), l.310 (`!( x )` = `the x`). Lean `HelperLemmas.lean` l.40 (`list_update_func` =
    `List.modify`), l.150-168 (`list_slice_update`, same structural recursion as Rocq);
    `wasm2.0.lean` l.125-133 (`list X` generic), l.11511-11523 (`wf_store`: no premise on ELEMS),
    l.11642/11684 (`admininstr_instr (instr.REF_NULL x0) => admininstr.REF_NULL x0`), l.12651
    (`Append context`).
  - TP l.37-46 (`num_default` body = Rocq's), l.298-305/660-670/687/900-903/1635 (section headers),
    l.355-366 (`wf_store_parts`); TPP l.1-30 (header), l.546-549 (`proj_identity`).
- Independent declaration scan (python, nested-comment-aware, scratch
  `scratchpad/agents/sig-tp-tpp/decls.py`): Rocq TP 36 decls (only `Qfloor_add_Z` unmatched), Rocq TPP
  77 (only Ltac `resolve_wfness` unmatched); Lean TP 135 decls, Lean TPP 79; every Lean declaration
  appears in the side-by-side files (no unexamined Lean-only helper); no duplicate names.
- Extra checks: `num_default` used only by `num_default_is_well_formed` (both unused, Lean and Rocq);
  `proj_identity` unused in Lean (Rocq uses it at TPP l.425/468); Rocq Ltac macros live in
  `typing_lemmas.v` l.2106/2186/2241/2374 and `type_preservation_pure.v` l.16; residual numeric-sorry
  dependency of `store_extension_reduce` is recorded in `for-claude/is_wf_theorems.md` l.75.

## Method

For every pair: compared binders (names/types, modulo `N`/`n`/`res_N` = Lean `Nat` abbrevs), every
premise (order and content) and the conclusion, using the brief's notation table (`:->` =
`mkFunctype`, `<ti:` = `instrtype_sub`, `[| i |]`/`lookup_total` = `[i]!`, `!(x)` = `the x` ~
`Option.get!`, `:> N` = `proj_uN_0`, `<?`/`|l|` = `<`/`.length`, `@@` = `++` via `Append context`).
For Lean-only declarations: checked a Lean-only label (per-decl doc or enclosing `/-! ... -/` section
header) and plausibility; all are proved with no `sorry` in their bodies, so their statements are
true modulo the known generated `*_is_wf` sorries.

## Findings

**No signature MISMATCH.** All 35 TP pairs and all 76 TPP pairs are equivalent statements (or carry a
documented, meaning-preserving deviation). No `sorry`/`axiom`/`native_decide`/`admit`/
`implemented_by`/`unsafe` in the code of either file. All 103 Lean-only declarations are labelled
(directly or by section header) and plausible.

1. **minor / new — `proj_identity` silently specialised** (TPP l.546-549). Rocq
   `type_preservation_pure.v:358`: `forall (A : eqType) a, mk_list A (proj_list_0 A a) = a`. Lean:
   `theorem proj_identity (a : resulttype) : list.mk_list (proj_list_0 valtype a) = a`. Lean's
   generated `list (X : Type)` (wasm2.0.lean l.126) is generic, so the generic form is statable; the
   doc comment does not mention the specialisation. Weaker than Rocq but harmless: unused in Lean.
   Fix: state it as `{X : Type} (a : list X) : list.mk_list (proj_list_0 X a) = a` (proof `cases a; rfl`
   unchanged) or note the specialisation.
2. **minor / new — `num_default` doc claims a use that does not exist** (TP l.38-39: "used to build
   default locals in `t_read_preservation`'s Call_addr/frame-invocation case"). `num_default` is only
   referenced by `num_default_is_well_formed` (TP l.48), itself unused; the call_addr case uses the
   generated `default_` via `default_val_ok`/`default_vals_ok` (TP l.1979-2003). In Rocq, its only use is
   the commented-out `num_default_is_well_formed` (TP.v l.74-84). Body matches Rocq exactly.
3. **minor / new — stale/contradictory file headers.** TP l.26 and TPP l.23 still say "Phase 1 (this
   file, first pass): every signature stated, proofs `sorry`." right below status paragraphs saying
   everything is proved. TPP l.12-15 "Scope: ... Excludes store-mutating instructions (→
   `type_preservation.v`) and SIMD." contradicts TPP l.17 "including the SIMD section" and the ~45 SIMD
   lemmas in the file (l.1283-1840).
4. **minor / new — two inaccurate per-lemma doc claims in TPP.** (a) `Step_pure__return_label_preserves`
   l.723-724: "Fully proved in Rocq (unlike the `_frame_` sibling above)" — the sibling
   `Step_pure__return_frame_preserves` is `Qed` upstream (Rocq TPP.v l.490), as its own corrected Lean
   doc (l.672) says. (b) `Step_pure__nop_preserves` l.28-31 attributes
   `resolve_wfness`/`invert_ais_typing`/`resolve_all_pt`/`resolve_subtyping`/`construct_ais_typing` to
   `helper_tactics.v`; they are defined in `typing_lemmas.v` l.2106-2374 and (`resolve_wfness`)
   `type_preservation_pure.v` l.16.
5. **minor / new — Lean-only labelling/doc precision in TP.** (a) `wf_store_parts` doc (TP l.358) says
   "`Store_ok s` stated for a store `s` gives ..." but the hypothesis is `(h : wf_store s)`. (b) The
   l.900 section header ("`store_extension_reduce`: per-rule store cases (bundle18)") explains the
   split but, unlike the l.298/687/1635 headers, lacks the explicit "(Lean-only ...)" tag; ~30 helpers
   below it (`getElem?_eq_some_bang`, `wf_store_with_*`, `valtype_reftype_inj`,
   `externtype_table_sub_inv`, `datatype_eq_OK`, `datainsts_*`, `Store_ok_wf_store`, `wf_num_Inn_proj`,
   `wf_vconst_parts`, `*_store_ok`) have no per-declaration Lean-only label. Statements all plausible
   (e.g. `wf_store_with_elems` needs no premise on `es` because generated `wf_store`, wasm2.0.lean
   l.11511-11523, has no ELEMS premise).
6. **info / known-documented — `Qfloor_add_Z` not ported** (Rocq TP.v l.28; duplicate in
   extension_lemmas.v l.2895; used at TP.v l.1335 in the memory-grow case). Intentional per brief §5
   (Q-bridging lemmas); its role in Lean is played by `rat_to_nat_natCast` (TP l.1315, labelled
   Lean-only). The Lean file never names `Qfloor_add_Z`; a one-line note near `rat_to_nat_natCast`
   would close the loop.
7. **info / known-documented — documented deviations re-verified as correct and meaning-preserving:**
   `wf_tableinsts_preserves`/`wf_memoryinsts_preserves` `hlen` (TP l.240/255); `mem_store_extension`
   `len : Q` → `Nat` (TP l.418-422, doc l.420; equivalent because both versions pin `len` to `|b_lst|` and Rocq's
   `list_slice_update` takes `j : N`); `t_read_preservation` `Vals_ok` (TP l.2021-2028);
   `store_extension_reduce` proved without `Step_is_wf` (TP l.1608-1611) — note it still depends on 4 of
   the 32 known numeric sorries (`nbytes__is_wf`, `ibytes__is_wf`, `wrap___is_wf`, `vbytes__is_wf`, used
   at TP l.1552-1579), recorded in `for-claude/is_wf_theorems.md` l.75 but not in its doc comment.
   Also `num_default_is_well_formed` (Lean-only, cites a Rocq lemma commented out upstream; header
   l.24 documents it).

## Coverage (one line per Rocq declaration)

type_preservation.v (36):
zero_is_well_formed -> zero_is_well_formed : OK
num_default -> num_default : OK (def body identical; doc usage claim wrong, F2)
Qfloor_add_Z -> (none) : MISSING(undoc'd in Lean; intentional Q-bridging per brief §5)
wf_context_app -> wf_context_app : OK
wf_context_tab -> wf_context_tab : OK
wf_context_mem -> wf_context_mem : OK
inst_t_context_local_empty -> inst_t_context_local_empty : OK
inst_t_context_labels_empty -> inst_t_context_labels_empty : OK
t_preservation_vs_type' -> t_preservation_vs_type' : OK
t_preservation_vs_type -> t_preservation_vs_type : OK
wf_tableinsts_preserves -> wf_tableinsts_preserves : DEVIATION(doc'd, hlen)
wf_memoryinsts_preserves -> wf_memoryinsts_preserves : DEVIATION(doc'd, hlen)
list_update_func_preserves_prop -> same : OK
list_update_func_forall_inv -> same : OK
Forall_list_update_func -> same : OK
wf_store_mem_update -> same : OK
wf_store_mem_update' -> same : OK
mem_store_extension -> same : DEVIATION(doc'd, len Q->Nat, equivalent)
ais_seq3_last_typing -> same : OK
ais_vstore_mems_inversion -> same : OK
ais_vstore_lane_mems_inversion -> same : OK
store_extension_reduce -> same : OK (proof route differs, doc'd)
reduce_inst_unchanged -> same : OK
ais_vload_typing_inversion -> same : OK
ais_vload_lane_typing_inversion -> same : OK
ais_vstore_typing_inversion -> same : OK
ais_vstore_lane_typing_inversion -> same : OK
Step_read__vload_preserves -> same : OK
Step_read__vload_lane_preserves -> same : OK
vec_store_preserves_2 -> same : OK
Step__vstore_preserves -> same : OK
Step__vstore_lane_preserves -> same : OK
t_read_preservation -> same : DEVIATION(doc'd, Vals_ok)
step_moduleinst -> same : OK
t_preservation_type -> same : OK
t_preservation -> same : OK

type_preservation_pure.v (77):
resolve_wfness (Ltac) -> (none) : MISSING(doc'd: Ltac automation not ported, nop_preserves doc)
Step_pure__nop/drop/select_preserves_helper/select_true/select_false/if_preserves_helper/if_true/
if_false/label_vals/br_zero/br_succ/br_if_true/br_if_false_preserves -> same : OK (13)
proj_identity -> proj_identity : DEVIATION(undoc'd, specialised A:=valtype; F1)
Step_pure__br_table_lt/br_table_ge/frame_vals/return_frame/return_label/unop_val/binop_val/testop/
relop/cvtop_val/local_tee_preserves, Step_pure__ref_is_null_helper/true/false -> same : OK (14)
ais_single_plain_typing_inversion, vconst_result_typing, const_result_typing,
ais_vconst/const/vvunop/vvbinop/vvternop/vvtestop/vunop/vbinop/vtestop/vrelop/vshiftop/vbitmask/
vswizzle/vshuffle/vsplat/vextract_lane/vreplace_lane/vextunop/vextbinop/vnarrow/vcvtop_typing_inversion
-> same : OK (24)
vec_preserves_1/2/3 -> same : OK (3)
Step_pure__vvunop/vvbinop/vvternop/vvtestop/vunop/vbinop_val/vtestop/vrelop/vshiftop/vbitmask/
vswizzle/vshuffle/vsplat/vreplace_lane/vextunop/vextbinop/vnarrow/vcvtop/vextract_lane_num/
vextract_lane_pack_preserves -> same : OK (20)
t_pure_preservation -> same : OK

## Unsure / side notes

- `for-claude/is_wf_theorems.md` l.31 table row still says `Step_is_wf` is `sorry` / "Lean statement
  has no `Store_ok` premise"; a later section (l.66) supersedes it. Outside this task's scope; not
  reported as a finding.
- I did not re-derive `append_context` vs Rocq's `_append` field by field (only `wf_context`'s
  TABLES/MEMS premises matter for `wf_context_app`, and both are list appends).

## Safety check (END)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" sig-tp-tpp
safety check [sig-tp-tpp] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T105834.343499008Z-sig-tp-tpp-1407122.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written by this agent: this log only (in the repo); scratch files only under
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/sig-tp-tpp/`
(`decls.py`, `*.names`, `*.seen`). No Lean was run; no git state was changed.

# digest-audit: digest of the bundle20 "audit" agent logs (19 files)

Label: `digest-audit`. Date: 2026-10-15. Read-only task: no repo writes, no agents, no lake, no git writes.
Only writes: this log (and nothing else). Source dir (all 19 files, every line read):
`/home/zhengyew/spectec/spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle20/agent_logs/`

## Safety check START (verbatim)

```
safety check [digest-audit-start] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T045148.324830285Z-digest-audit-start-448722.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
VERIFIED: nothing inside spectec/src/test-lean-claude changed either (apart from safety-check files)
```

## 0. Reading status and file classification

Read completely: README.md, audit-hygiene.md, audit-isabelle.md, audit-model.md, audit-model-runtime.md,
audit-model-step.md, audit-nonvacuity.md, audit-proofmap.md, v2verify-audit-isabelle-F1-factual.md,
v2verify-audit-nonvacuity-NV-F1-factual.md, v2verify-audit-nonvacuity-NV-F2-factual.md,
v2verify-sig-ext-SE-1-factual.md, sig-base.md, sig-ext.md, sig-tp.md, sig-tpp.md, sig-tp-tpp.md,
sig-typing-base.md, sig-typing.md. Nothing skimmed. (A keyword grep for vcvtop|trunc_sat|vloadop|SHAPE|ishl|ishr|vshiftop|
iadd_|memory.fill|memory.copy|memory.init|stuck|bundle19|hand-edit|ExtendedDeriveDecEq|lakefile was run over all 19 to be sure
nothing was missed; hits are all quoted below.)

Complete / substantive (11): README, audit-isabelle, audit-model, audit-nonvacuity, sig-ext, sig-tp-tpp, sig-typing-base, and the
four v2verify-* logs.
PARTIAL, killed by the account usage limit in the first wave, NO findings (8): audit-hygiene (only the false-positive diagnosis of
the safety script; ends at an empty "Work log" heading, l.324), audit-model-runtime (24 lines: task + start check + "read brief"),
audit-model-step (26 lines, same), audit-proofmap (64 lines: progress notes steps 1-8, citation-checker statistics; no tree,
no top-10, no size stats, no end check), sig-base (25 lines), sig-tp (22 lines), sig-tpp (42 lines: counts + citation statistics),
sig-typing (23 lines). audit-model-runtime and audit-model-step were merged into audit-model (v2); sig-tp and sig-tpp into
sig-tp-tpp; sig-typing and sig-base into sig-typing-base. audit-hygiene and audit-proofmap were NOT relaunched in v2 (README lists
6 v2 auditors: audit-model, audit-isabelle, audit-nonvacuity, sig-tp-tpp, sig-typing-base, sig-ext), so there is NO completed
hygiene audit of ExtendedDeriveDecEq.lean / lakefile.lean and NO proof-map tree in these logs.

## 1. README.md (18 lines)

- Every subagent was given the user's safety order verbatim, ran the start/end baseline check (outputs in its log), wrote only its
  own log + scratch in the session scratchpad; every final check VERIFIED (l.3-7).
- Workflows (l.9-14): `preservation-audit` wf_19300dcc-f8c (11 agents, all killed after ~6 min by the usage limit);
  `preservation-audit-v2` wf_67c8bfe9-04b (6 auditors + 4 verifiers, max 3 concurrent, all done, "all 4 major findings confirmed",
  structured results in preservation_audit_v2_results.json); `progress-signatures` wf_88e0cc43-5d4 (translate the 190 Rocq
  progress lemma statements in 6 chunks, audit each, fix; 6+6+1 agents; 1 audit problem in chunk 4, fixed; psig-*.md,
  psig-audit-*.md, psig-fix-4.md, progress_signatures_results.json); `progress-proofs` wf_cb22b074-0c2 (prove the 280 `sorry`
  targets in 43 batches, Sonnet for helper batches; "280/280 proved (2 with one documented known-false `sorry` each)";
  prove-*.md, progress_proofs_results.json).
- l.16-18: `progress_trust_boundary.txt` = `#print axioms` / `#sorry_deps` for `t_progress`, `t_progress_e`, `t_progress_be`,
  `t_preservation` at the end of bundle20 (not among my files).
- INFERENCE (not stated in README): the "2 known-false sorries" are the two Rocq-false progress cases that audit-isabelle.md:264-266
  names (VLOAD `SHAPE 64 X 1`; VCVTOP `I16X8<-F32X4 TRUNC_SAT ZERO`). Those are exactly the cases removed by upstream 6582b3a.

## 2. audit-isabelle.md (287 lines): Isabelle vs Lean vs Rocq

Upstream reference: Isabelle branch `isabelle-mech-backend` @ `41e27cc54`, dir `spectec/isabelle_type_safety_proof`.
- Item 1: Isabelle `preservation` (Preservation.thy:5940-5943, `Config_ok cfg ts => Step cfg cfg' => Config_ok cfg' ts`) equals
  Lean `t_preservation` (TypePreservation.lean:2699, `Step c1 c2 -> Config_ok c1 ts -> Config_ok c2 ts`), same fixed `ts`; Config_ok/
  State_ok/Frame_ok/Store_ok/Moduleinst_ok/Instr(s)_ok2/Expr_ok2/Extend_* identical rule-for-rule (model l.13511-13895 vs Lean
  15547-16335). `Vals_ok` (in `t_read_preservation`/`t_preservation_type`) = Isabelle `list_all2 (\t v. Val_ok s v t) (context_LOCALS C')
  (LOCALS f)`. `e_preservation` (:969) vs Lean `t_preservation_type` (:2679): Lean has an extra `wf_config` premise (also in Rocq).
  `t_inst_match` (Context_Store_Agreement.thy:5) = Lean `inst_match` (TypingLemmas.lean:1886), same 7 fields.
- Length-premise scan (l.71-87): Isabelle 262 `list_all2` premises, 0 without explicit length premise. Lean: 274 `Forall2` premise
  lines, 13 flagged without adjacent length equality, all hand-checked: `wf_instr`/`wf_admininstr` case 57 (STORE; lengths of
  `Option.toList Inn_opt`/`sz_opt` forced equal by `(Inn_opt = none) <-> (sz_opt = none)`), `Module_ok` (has its length premise, parse
  miss), `Step_read.vload_shape_val` l.14580 (has `v_N = List.length j_lst`, first list `List.range v_N`), 9 in `fun_instantiate`.
  `Forall3`: 129 lines, all have length equalities; the 16 unparsed hits are proof lines `iswf_Forall3_eq_of_func` ~wasm2.0.lean
  l.7605-7665 (a hand-written proof inside wasm2.0.lean).
- Item 5 model differences (l.103-119): slices `list_slice` = `take n (drop i l)` = Lean; `with_mem` (Lean wasm2.0.lean:12392 =
  `splice BYTES b* i`, ignores `j`, always length-preserving) vs Isabelle `list_slice_update` (clause `(x # l) _ 0 _ = []` truncates) vs
  Rocq (returns rest) - all agree when `|b*| = j`; the four store `*_val` rules carry no in-bounds premise in ANY model (Isabelle
  l.12943, Rocq wasm.v:16403, Lean l.14747; NOTES.md:146-155; "fixed by the user's clamped splice"). `rat_to_nat r = (r.num.tdiv
  r.den).toNat` (wasm2.0.lean:9) = floor on non-negatives = Isabelle `div`. Limits bounds: `Memtype_ok` k = 2^16, `Tabletype_ok` k = 2^32-1
  in both. 2^32 corner case independently hit by Isabelle at Preservation.thy:5197 (memory_fill_succ needs `i'+1 <= 2^32-1` from
  `i'+v_n <= v_len*64Ki`, `v_len <= 2^16`, `v_n != 0`; comment "check if Limits_ok needs a <= instead of <"); memory.copy/init cases
  5294-5310 are `sorry (* see memory_fill cases *)`.
- F1 [major, new] Moduleinst_ok `> 0` premise (see section 8, M1). F2 [info] 2^32 corner (above; "corroborates the Lean
  `Step_read_is_wf` note"). F3 [info] Isabelle `step_wf` (Preservation.thy:8-11) and model `Step_read_is_wf` (l.12885) have NO
  `Store_ok` premise and are false as stated: `Step_read__table_size` pushes `CONST I32 (mk_uN |REFS|)` and `wf_tableinst` (model l.10327)
  does not bound `|REFS|`; so Lean/Rocq's hand-added `Store_ok (fun_store z)` is NEEDED (argued from the rules, no machine check).
  F4 [info] zip `Forall2` vs `list_all2`: equivalent because of the generator-emitted length equalities. F5 [minor] `fun_instantiate`
  (wasm2.0.lean:15355ff, l.15370/15410/15411) has `Forall2 ... (List.range n_D) var_4_lst` with no `List.length var_k_lst = n_D/n_E`
  (var_3/7/8/9/10 analogues); off the preservation and progress paths. F6 [info] `Extend_store_ais` (ExtensionLemmas.lean:1842)
  carries Rocq's two `Store_ok` premises, unused (`intro hext _ _ h`); Isabelle `reduce_store_extension` (Properties.thy:372) is
  over-restricted and unused (20/23 cases sorry); Lean `store_extension_reduce` proves all 23. F7 [info] slice-update differences (above).
- Item 2 decomposition map (l.199-218): `e_preservation` (one `Step.induct` l.991, nested `Step_pure.induct` l.996, `Step_read.induct`
  l.3011) -> `t_preservation_type`/`t_preservation_type_aux` dispatching to `t_pure_preservation` (TypePreservationPure.lean:1858) and
  `t_read_preservation` (:2028); `e_preservation_locals` :90 -> `t_preservation_vs_type` :227 (+ `'` :216, `Extend_store_vals`
  ExtensionLemmas:1138), `reduce_inst_unchanged` :536; `step_wf` :8 (sorry) -> `Step_is_wf` wasm2.0.lean:16045 (proved, +Store_ok),
  `Step_read_is_wf` :16034 (sorry), `Step_pure_is_wf` (proved); sorry :5989 -> `store_extension_reduce` :1611 +
  `Extend_store_moduleinst` EL:1724; Limits_sub_refl/_trans -> `limits_sub_refl/_trans` EL:350/363; Type_Inversion.thy ->
  TypingLemmas `instr_typing_inversion` :467, `ai_typing_inversion` :711, `ais_seq_typing_inversion` :1244, `ais_composition_typing` :1254,
  `ais_vals_typing_inversion` :1788, per-op `ais_*_typing_inversion` in TPP from :1274.
- Item 3 sorry inventory (l.220-239): Preservation.thy has 15 live sorries (l.11 step_wf; 769/774 Limits_sub (Lean proves); 4408
  table_init_succ wf of `CONST I32 (i+1)` (true given Store_ok: Eleminst_ok `|refs| < 2^32`, Tabletype_ok `n <= 2^32-1`); 4619/4627/4659/
  4842 load_num_val/load_pack_val/vload_val/vload_lane_val wf of loaded value (`load_num_val` carries `wf_num_ nt c` in both models);
  5197 memory_fill_succ (2^32 corner, FALSE in Isabelle); 5294/5297/5300 memory_copy_zero/le/gt and 5307/5310 memory_init_zero/succ
  (whole cases); 5989 (Store_ok s'/Extend_store/Moduleinst_ok s')). Properties.thy 20 (all in unused `reduce_store_extension`);
  store_extension_typing.thy 3 (l.220, 241, 321). Lean says: typing proved in `t_read_preservation`, the wf parts go through
  `Step_read_is_wf` (+ numeric opaque `*_is_wf`). Model: 140 `*_is_wf` all sorry in Isabelle; Lean has 152 `*_is_wf` theorems, "only the 33
  listed in the brief remain sorry on the preservation path".
- Item 6 progress intelligence (l.241-271): Isabelle `progress` (Progress.thy:1116) `Config_ok (mk_config s es) ts => exists cfg'. Step ...
  \/ es = [TRAP] \/ (exists vs. es = map admininstr_val vs)`; Rocq `t_progress` (type_progress.v:6064) `Config_ok ... -> terminal_form es \/
  exists s' f' es', Step ...`, `terminal_form es := const_list es \/ es = [TRAP]`; equivalent. Rocq at that time: `t_progress` Qed (6094),
  `t_progress_e` Qed (6062), `t_progress_be` Admitted (5512). Isabelle structure: `State_ok_strip` (l.27) => top context = `strip C`;
  `typecheck_strip_not_return` (l.92 via `br_type_not_strip`/`return_type_not_strip` l.48/70) => `not_br_return es` = the same syntactic
  predicate as Rocq `not_lf_br`/`not_lf_return` (type_progress.v:599/604); mutual induction
  `Instr_ok2_Instrs_ok2_Expr_ok2.inducts(3)` with motives over an arbitrary typed value prefix `vs` (`list_all2 Valtype_sub (map typeofval vs) t1`,
  `list_all wf_val vs`) + State_ok/strip/not_br_return/wf; plain case by contradiction with nested `Instr_ok_Instrs_ok.inducts(1)`; label case
  (l.3115) splits on `not_br_return body` (IH + `ctxt_label`/`label_vals`, else `br_zero` with `Resulttype_sub_length`+`list_splitable`, `br_succ`,
  `return_label`); frame case (l.3394) likewise (`frame_vals`, `return_frame`; BR impossible); seq case (l.3860) with
  `br_return_contaminate_left/right` (l.98/123), `reducible_right` (l.944), `trap_vals`, `reducible_left_v` (l.924). Helpers `fun_*_total`
  (l.165-632), `typeofval_is_nt/_i32/_rt` (l.999-1062), `default_not_bot` (151). Isabelle's own progress has 33 sorries: l.291 `truncz_spec`
  (`truncz x = x`, analogue of Rocq/Lean `truncz_quot`), l.1826 cvtop, l.1920-1974 all 19 vector cases, l.2460 memory_size
  `0 < length memtype_lst` (proof gap), l.2817-2847 all 11 load/store/vload/vstore cases; label/frame cases use `step_wf` (sorry) 5x.
  Porting insights: (a) Lean `Step.ctxt_label/ctxt_frame/ctxt_instrs` (wasm2.0.lean:14706/14711/14716) need `wf_config` of inner pre AND
  post config => progress needs `Step_is_wf` (Store_ok from Config_ok) and so inherits the `Step_read_is_wf` sorry. (b) TWO GENUINELY FALSE
  Rocq progress cases (mechanised counterexamples): VLOAD `SHAPE 64 X 1` (`vload_shape64_stuck`, type_progress.v:6107) and VCVTOP
  `I16X8<-F32X4 TRUNC_SAT ZERO` (`vcvtop_trunc_sat_i16_stuck`, :6132); Isabelle never reaches them. (c) Rocq axioms.v "has 22 axioms" (but see
  discrepancy D2: 23), Lean 11; missing in Lean: `ibits_inv`, `feq/fne/flt/fgt/fle/fge_bit`, `ishl_wf`, `ishr_wf`, `trunc_sat_total`, `demote_nonempty`,
  `promote_nonempty` (used by Rocq progress). (d) Lean has no `typeof : val -> valtype` (Rocq type_progress.v:262; Isabelle `typeofval` comes
  from an Isabelle-only aux spec). (e) neither theorem applies to `fun_invoke` configs (F1). (f) mirror Rocq (equality `map typeof vcs = ts1` +
  `Admin_instrs_ok_ind'`); Isabelle's subtype-generalised prefix is an alternative that absorbs `Instrs_ok2__sub` directly.
- Caveats (l.273-280): F1's IL-pass origin not traced by this agent (the verifier traced it, see section 8); Lean names for Isabelle's
  `blocktype_ok_agree`/`context_*_agree` not matched 1:1 (handled via `inst_match`); `step_wf` falsity argued from rules.

## 3. audit-model.md (196 lines): generated Lean model vs generated Rocq model

Method: read side-by-side extracts, scripts `scan2.py`, `fpall.py` (premise fingerprint over all 346 inductives common to both files).
- F4 (l.149-158) 1:1 correspondence: constructor names/order identical for Instr_ok 73, Instrs_ok 5, Expr_ok 1, Instr_ok2 6, Instrs_ok2 5, Expr_ok2 1,
  Step_pure 54, Step_read 47, Step 23 (Rocq prefixes only reserved words `res_if`, `res_return`, `res_seq`, and `Rel__x`); datatypes instr 68,
  admininstr 74, val 5, ref 3. Premise fingerprints identical for every constructor of all 346 common inductives, except 5 differences all
  explained by renderings: `holds_upto P n` <-> `Forall P (List.range n)`; `List_Foralli` <-> `Forall2 _ (List.range n) l` + `n = |l|` (Step_pure
  vswizzle/vshuffle, Step_read vload_shape_val, Extend_store) or `fun_instantiate`. Also `mkseqN` <-> `List.range n |>.map`, `list_slice` <->
  take/drop, `list_update_func` <-> `List.modify`, `list_repeat` <-> `List.replicate`, Q->N (`Z.to_N . Qfloor`) <-> `rat_to_nat` (equal for all
  signs), `lookup_total`/`!` <-> `[i]!`/`Option.get!`. Match-arm comparison of 142 common `def`s: only single-arm-match vs direct renderings (24).
  Accessors/defs identical to Rocq include `ine_`, `iadd_`, `sat_u_`, `canon_`, `size`/`res_size`, `jsize`, `sizenn`, `isize`, `fun_store/frame/...`, context `Append`
  (Lean `Option.orElse` = Rocq left-biased `option_append`), `Resulttype_sub`.
- F3 (l.137-147): of 404 `Forall2`/`Forall3` uses inside generated inductive constructors, 391 have a premise equating the lengths of exactly the paired lists
  (identical premise also in Rocq next to its inductive Forall2: Frame_ok, Store_ok x6, Moduleinst_ok x6, Resulttype_sub, Step_pure vshiftop/vbitmask, Step_read
  vload_shape_val, ...); 13 exceptions = wasm2.0.lean:2162-2163 and 11912-11913 (STORE case 57, forced equal; also wasm.v:3548), `Module_ok` (parse miss), 10 in
  `fun_instantiate`. None of the 63 sorried theorems mentions Forall2/Forall3. `Vals_ok` (TypingLemmas.lean:1775) bakes in the length.
- F7 (l.171-173), l.90-97: 64 Lean `opaque` = exactly the 64 Rocq `Axiom`s (same names; no function opaque in Lean but defined in Rocq). No `axiom`/
  `native_decide`/`implemented_by`/`extern`/`unsafe` in wasm2.0.lean. The 63 Lean sorries = Rocq's 62 admitted `*_is_wf` lemmas + `Step_read_is_wf`; Rocq's
  extra `Admitted` `res_list_eq_dec` (wasm.v:429-431) has no Lean counterpart (Lean derives DecidableEq). `List.contains` on the path is only over `num_`, `vec_`=`uN`,
  `lane_`, `externaddr`, `name` (all `deriving ... LawfulBEq`); 13 types derive only BEq (instr, elemmode, datamode, func, global, elem, data, module, funcinst, store,
  state, admininstr, config) and none is used with `List.contains`/`disjoint_` on the path.
- l.102-105 and l.178: Rocq's ONLY definition hand-edit in wasm.v is the placement + `Store_ok (fun_store z)` premise of `Step_read_is_wf` (comment at wasm.v:17351-17353) and
  `Step_is_wf` (comment :17701); mirrored in Lean; statements identical to Rocq's hand-edited ones. Other wasm.v comments are generator `FIXME - Non-trivial append` on record
  Append instances (memarg, exportinst, funcinst, ...), not used by the soundness relations.
- F1 (l.111-126) Moduleinst_ok `> 0` (see M1; this agent additionally gives the example frame MODULE := {TYPES=[],FUNCS=[],GLOBALS=[],TABLES=[],MEMS=[],ELEMS=[0],DATAS=[],EXPORTS=[]}
  = a module with only a passive element segment: `Config_ok` false in all three formalisations but true in the spec; recommends reporting upstream as a SpecTec middle-end issue,
  no Lean-side action needed for Rocq correspondence).
- F2 (l.128-135) Lean `with_mem` (wasm2.0.lean:12391-12398) ignores its length argument `nat_0` (`BYTES := splice (elem_1.BYTES) var_0_lst nat`); Rocq `with_mem` (wasm.v:14420-14424)
  uses `list_slice_update (BYTES var_1) i j b_lst`; Rocq writes min(j,|b|,|l|-i) bytes, Lean min(|b|,|l|-i); coincide when j >= |b*|; both length-preserving, Store_ok/Meminst_ok/
  Extend_meminst only constrain lengths => `t_preservation` unaffected. Documented HelperLemmas.lean:439-445 (`splice_eq_list_slice_update`), bundle17 `with_mem_slice_update_issue.md`; user decision (bundle18).
- F5 (l.160-165) `vstore_lane_oob` traps when `i + OFFSET + v_N > |BYTES|` with N in BITS (wasm2.0.lean:14776, wasm.v:16432, spec 8-reduction.spectec:573 `$(i + ao.OFFSET + N)`), while `vload_lane-oob`
  (spec 536) and the `-val` rule use N/8. Spec typo faithfully transcribed; only adds nondeterminism (TRAP typable at any type; `with_mem` preserves length) => no effect on `t_preservation`.
- F6 (l.167-169) the brief's "already established" `Step_pure 63` is wrong: both wasm2.0.lean (13744-13997) and wasm.v (15540-15793) have 54. (Early note l.49 says 63; corrected at l.73.)
- Unchecked (l.181-185): no concrete Config_ok witness (done by audit-nonvacuity); Lean derived `Inhabited` defaults vs Rocq `default_val` not compared per record type; datatypes compared only by
  constructor counts for instr/admininstr/val/ref.
- Answers (l.175-179): no weakening/strengthening vs Rocq on the path apart from F2 (no effect); all backends share F1; Rocq's only hand-edit is mirrored; top-level statements Lean/Rocq/Isabelle equivalent.

## 4. audit-nonvacuity.md (451 lines): machine-checked non-vacuity witness for `TLC.t_preservation`

- Constraints given to this agent (l.8-11): Lean only via `timeout 900 lake env lean <abs path>` on ONE scratch file, never `lake build`, never two Lean processes at once.
- Design (l.61-72): all-empty module instance is impossible (M1) and every `Store_ok` global must be mutable (M2); witness = store with one MUTABLE i32 global `CONST I32 0`, module instance
  `GLOBALS := [0]` (all else empty), frame without locals, `ts = []`; witness 1 `[NOP] ~> []` via `Step.pure` + `Step_pure.nop`; witness 2 `[CONST I32 0, DROP] ~> []` via `Step_pure.drop`.
- Lean runs (l.74-83): 6 runs (run 1 compiled first time, ~2 s wall, max RSS 3.6 GB; run 2 recomputed Lake source hashes via a temporary `#eval`: wasm2.0.lean = `711b692ecbe2b7e3`, TypePreservation.lean =
  `4868dd4c31f381cf`, identical to `.lake/build/lib/lean/{wasm2.0,TypePreservation}.trace`; runs 3-4 failed on positional `cases ... with` patterns (see pitfalls); run 6 final clean). Olean freshness
  (l.91-94): wasm2.0.lean mtime newer than oleans but content identical: `git status` clean vs HEAD `0a7507f41` (committed 2026-10-05 00:21).
- The final `Witness.lean` (282 lines, sha256 prefix bf19d3956a35e023) is quoted VERBATIM at audit-nonvacuity.md:104-385; run-6 output l.391-402. All of `c1_ok`, `c1_step`, `hyps_satisfiable`, `d1_ok`,
  `d1_step`, `emptyMI_not_ok`, `invoke_config_not_ok`, `s_imm_not_ok` use only `[propext, Classical.choice, Quot.sound]`; `immutable_globaltype_not_ok` uses no axioms; `c2_ok`/`d2_ok`
  (applying `TLC.t_preservation`) add `sorryAx` (the 33 known generated sorries).
- Findings F0 (non-vacuity established), F1 (= M1), F2 (= M2), F3 (build freshness; no staleness). Notes (l.439-442): F1 root-cause attribution from reading code only; spot check:
  `Resulttype_sub` (wasm2.0.lean:12735-12739) carries an explicit length premise so `Instrs_ok2.sub` cannot retype `[]` as `[] -> [t]` through the zip `Forall2`. The other 13 `> 0` premises in wasm2.0.lean
  (l.2082/11832 trivially true constant lists; l.9556-9637 and 13798-13874 accompany real memberships) were glanced at, not audited in depth.
- Scratch dir `/tmp/claude-1000/...` is GONE now (verified: `/tmp/claude-1000` does not exist), so the verbatim copy in the log is the only surviving Witness.lean.

## 5. The four verifier logs (v2verify-*), all CONFIRMED major, unchanged severity

- v2verify-audit-isabelle-F1-factual.md (129 lines, 12 claims) and v2verify-audit-nonvacuity-NV-F1-factual.md (110 lines, 14 claims): M1 confirmed claim by claim. Root cause traced to
  `spectec/src/middlend/sideconditions.ml`: l.62-63 `| MemE (_exp, exp) -> ([IfPr (CmpE (`GtOp, `NatT, LenE exp ..., NumE (`Nat Z.zero) ...) ...) $ e.at], true)` adds `|xs| > 0` for every `x <- xs` (not under `NegPr`); `iterPr` (l.22-28)
  `if iter <= List1 && vars' = [] then pr.it else IterPr ...` drops the iteration when the condition mentions no iteration variable (`il/ast.ml:16-20` iter order `Opt | List | List1 | ListN`,
  so `List <= List1`); sound only for `List1`; `Sideconditions` is enabled for `Rocq | Lean` (`exe-spectec/main.ml:317-319`); `flatten_empty_iter` (l.114-120) would re-strip an `IterPr(_, (List, []))`
  if only `iterPr` were fixed. Recommended fix: SpecTec `iterPr` must not drop a `List`/`Opt` iteration (or keep the MemE side condition inside), or document the exclusion.
  EXTRA (strengthens impact): `reduce_inst_unchanged` (TypePreservation.lean:536-539, `f.MODULE = f'.MODULE`) => by induction NO configuration reachable from an `$invoke` configuration is `Config_ok`,
  not just the initial one. Spec `$invoke` = 9-module.spectec:196-198 (`-- if f = { MODULE {} }`). Nit: `fun_invoke` spans 15452-15484 and its record ends 15466; Isabelle premise is at .thy:13634.
- v2verify-audit-nonvacuity-NV-F2-factual.md (86 lines, 15 claims): M2 confirmed. Root cause now traced: `spectec/src/middlend/undep.ml:162-164` `(* HACK - Change IterE of option and list with no iteration variable
  into a OptE *) | IterE (e1, (Opt, [])) -> OptE (Some e1)`; pass `Undep` enabled for `Rocq | Lean` (`main.ml:317-323`). Additions: imports are blocked too (`Import_ok` -> `Externtype_ok` ->
  `Externtype_ok/global` -> `Globaltype_ok`, spec 50-52/644-646, Lean 12714-12717); `Extend_globalinst`'s immutable branch (`-- if mut = MUT \/ val = val'`, spec B-soundness:258-260, Lean 16177) is never
  exercised on `Store_ok` stores; all Isabelle proof theories import the generated `isabelle_reference_output_wasm2` directly (Properties.thy:241 uses `mk_Globaltype_ok`); 0 occurrences of `Globaltype_ok` in the 6
  hand-written Lean files; `ExtensionLemmas.lean:162` discards the `Globaltype_ok` premise with `_`; `global_set_global_extension` (EL:1167-1181) takes mutability as a hypothesis (caller TypePreservation.lean ~1100-1112
  gets it from `minst_invert_globals` + the GLOBAL.SET instruction type). Previously flagged only as "possibly unusual" in `for-claude/digest_wasm_v.md:255-270`.
- v2verify-sig-ext-SE-1-factual.md (104 lines): SE-1 confirmed (10 claims). Refinement: `s_invert_funcs` is a tautology in Rocq too (funcinst has exactly 3 fields TYPE/MODULE/CODE in both; Rocq predicate holds by
  record eta with `t := funcinst_TYPE f`; Rocq's own `(* May add more here *)`), so the content loss is only in globals/mems/tables; finding's blanket "materially different from Rocq" is over-broad for funcs. Rocq's
  preservation uses these lemmas (type_preservation.v:775 tables, 1247 mems, 1824 funcs, 2039 globals, 2071 tables); the Lean port reaches the same facts via `globalinst_ok_invert`/`meminst_ok_invert`/`tableinst_ok_invert`.
  Severity kept `major` because brief defines `minor` as "no effect on meaning" and this changes meaning, `critical` not warranted because preservation does not use the four lemmas.

## 6. sig-ext.md (370 lines): ExtensionLemmas.lean vs extension_lemmas.v

128 Rocq declarations: 91 EXACT, 2 CITED (`pagediv`, `holds_upto_lt_refl` via `forall_range_lt` Ext:98), 27 NONE, 8 Ltac skipped; + 40 Lean-only entries (one, `terms`, is an extractor artefact). 77 of 91 EXACT are
statement-equivalent. Findings:
- SE-1 [major, confirmed] `s_invert_funcs/_globals/_mems/_tables` vacuous (Ext:223/232/254/269 vs v:42/74/106/175): `∃ xs, Forall₂ P s.X xs` provable by `fun _ => ⟨[], by simp [Forall₂]⟩`. Unused; docs falsely claim
  "signature confirmed identical" (l.220-222, 231) / "Unaffected by the resync". Fix: `∃ gts, s.GLOBALS.length = gts.length ∧ Forall₂ … s.GLOBALS gts` using the `List.length _ = List.length _` premises already in the generated `Store_ok`
  (wasm2.0.lean:15994ff, currently bound as `_` in the four proofs).
- SE-2 [minor] `minst_invert_funcs/_tables/_globals/_mems/_elems` (Ext:684/704/722/740/763 vs v:421/456/493/529/564) drop Rocq's `Forall2` length; strictly weaker; call sites recover the length via Lean-only
  `Moduleinst_ok_lengths` (TypePreservation.lean:404-408, used e.g. :435-438); docs do not mention it (`minst_invert_datas` already carries the length). Fix: add `minst.X.length = C'.X.length ∧` or a doc pointer.
- SE-3 [minor] `datatype.OK` hard-coded in the datas cluster: `Extend_store_datainsts'` (Ext:1702 vs v:2360), `Extend_store_datainsts` (Ext:1713 vs v:2408), `construct_datainsts` (Ext:2217 vs v:3041) drop Rocq's `ts`/`dt : list datatype`;
  equivalent because `inductive datatype | OK` is a singleton (wasm2.0.lean:750-751); Rocq-shaped version exists as Lean-only `Extend_store_datainsts₂` (TypePreservation.lean:365-370), bridged by `datainsts_Forall{,₂}_of_Forall{₂,}`
  (:1062-1074). The primed lemma's doc ("Datainst_ok is content-independent/always-true in Rocq") is inaccurate: Rocq `Datainst_ok` (wasm.v:17130-17135) needs `|b_lst| < 2^32`, `wf_store s`, `wf_datainst`.
- SE-4 [info] `table_grow_table_extension` `j : Option uN` is faithful (Rocq `mk_limits (v_u32 : u32) (u32_opt : option u32)`, `u32 := uN`, wasm.v:582, 1190-1191).
- SE-5 [minor] `memory_grow_mem_extension` (Ext:1234 vs v:1753) restated equivalently with `v_i v_n : Nat`, `v_j : Option Nat` (Q->Nat undocumented; doc says Rocq's `v_j_opt` is `option N`, it is `option u32`).
- SE-6 [minor] labelling gaps: `Ref_ok_wf_store` (:1996), `wf_tableinst_parts` (:2006), `wf_meminst_parts` (:2020, supersedes Rocq `invert_meminst` :1731 without saying so), `meminst_ok_raw` (:2126) sit under the "construct_*"
  header (:1985) without a Lean-only label; `HelperLemmas.list_slice_update_forall` (HelperLemmas.lean:419-428) is labelled "Not a Rocq port" though it is the generalised Rocq `forall_preserved_bytes` (v:1663).
- SE-7 [info] 27 NONE all justified: 26 in bundle17 gap_analysis_v1 §3d (its 28-list minus `pagediv`, `holds_upto_lt_refl`), plus `Scheme ais_ok_ind'` (v:2574; Lean uses `Instrs_ok2.rec`); 8 Ltac skipped by standing decision.
- SE-8 [info] hygiene: ExtensionLemmas.lean has exactly ONE `sorry` (l.137 `Val_ok_store`, under `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED` l.128); no axiom/admit/native_decide/implemented_by/unsafe/set_option/macros; references none of the 11
  HelperLemmas axioms; `funcinst_same` (hlen, documented) has no uses. All 68 distinct Rocq names cited exist upstream except `funcinst_same`/`Val_ok_store` (docs say so).
- SE-0 false-positive safety diagnosis (l.15-77): see section 9. Facts checked: `wasm.v:107-108 holds_upto P n := Forall P (iotaN N0 n)`; coercions `Qfloor : Q >-> Z`, `Z.to_N` (wasm.v:192-200); `Meminst_ok` multiplicative `|b_lst| = v_n * (64 * Ki)` (wasm2.0.lean:15937);
  `list_update_func := l.modify` (HelperLemmas.lean:40).
- Full per-declaration coverage list at sig-ext.md:218-349.

## 7. sig-tp-tpp.md (210 lines), sig-typing-base.md (432 lines)

sig-tp-tpp (TypePreservation.lean + TypePreservationPure.lean vs type_preservation.v + type_preservation_pure.v): NO signature mismatch. TP: 36 Rocq decls (35 EXACT, 1 NONE = `Qfloor_add_Z`), 135 Lean decls;
TPP: 77 Rocq (76 + Ltac `resolve_wfness`), 79 Lean theorems (76 ports + 3 Lean-only); 103 Lean-only declarations in total, all labelled (directly or by section header) and plausible (sig-tp-tpp.md:84). No sorry/axiom/native_decide/admit/implemented_by/unsafe in code of either (hits only in comments TP l.21,26,2016-2017,2697; TPP l.23).
`_is_wf` uses: TPP l.1863 `Step_pure_is_wf`; TP l.1552/1561/1571/1579 `nbytes__is_wf`, `ibytes__is_wf`, `wrap___is_wf`, `vbytes__is_wf` (inside `store_extension_reduce_aux`; in the known 32 numeric sorries), TP l.1982 `default__is_wf`, TP l.2036
`Step_read_is_wf`, TP l.2690 `Step_is_wf`. Findings: (1) `proj_identity` (TPP l.546-549) silently specialised to `valtype` vs Rocq's polymorphic `forall (A : eqType)` (type_preservation_pure.v:358); fix `{X : Type} (a : list X) : list.mk_list (proj_list_0 X a) = a`
(proof `cases a; rfl`); unused in Lean. (2) `num_default` doc (TP l.38-39) claims a use in `t_read_preservation` that does not exist (only used by `num_default_is_well_formed`, itself unused; Rocq's is commented out upstream, TP.v l.70-86). (3) stale
headers: TP l.26 and TPP l.23 "Phase 1 ... proofs `sorry`" under status paragraphs saying all proved; TPP l.12-15 "Excludes ... SIMD" contradicts TPP l.17 and ~45 SIMD lemmas (l.1283-1840). (4) TPP `Step_pure__return_label_preserves` l.723-724 says "Fully proved in Rocq
(unlike the `_frame_` sibling)" but the sibling is Qed upstream (Rocq TPP.v l.490; Lean doc l.672 already corrected); TPP l.28-31 attributes `resolve_wfness`/`invert_ais_typing`/`resolve_all_pt`/`resolve_subtyping`/`construct_ais_typing` to helper_tactics.v but they live in typing_lemmas.v
l.2106-2374 (+ `resolve_wfness` in TPP.v l.16). (5) TP: `wf_store_parts` doc (l.358) says `Store_ok s` but hypothesis is `wf_store s`; l.900 section header lacks the "(Lean-only ...)" tag unlike l.298/687/1635. (6) `Qfloor_add_Z` not ported (TP.v l.28, EL.v:2895, used TP.v:1335);
role played by `rat_to_nat_natCast` (TP l.1315). (7) documented deviations re-verified meaning-preserving: `wf_tableinsts_preserves`/`wf_memoryinsts_preserves` `hlen` (TP l.240/255); `mem_store_extension` `len : Q` -> `Nat` (TP l.418-422); `t_read_preservation` `Vals_ok`
(TP l.2021-2028); `store_extension_reduce` proved without `Step_is_wf` (TP l.1608-1611) but still depends on 4 numeric sorries (recorded in `for-claude/is_wf_theorems.md` l.75, not in its doc). Unsure: `for-claude/is_wf_theorems.md` l.31 row still says `Step_is_wf` sorry/no `Store_ok` (superseded at l.66).
Coverage list at sig-tp-tpp.md:135-190; TPP SIMD lemmas include (names reconstructed from the slash-abbreviated coverage lines sig-tp-tpp.md:183-188, so the exact spelling is unverified) `ais_vshiftop_typing_inversion`, `ais_vcvtop_typing_inversion`, `Step_pure__vshiftop_preserves`, `Step_pure__vcvtop_preserves`. TP (spelled out in the list, l.161-166): `Step_read__vload_preserves`, `Step_read__vload_lane_preserves`, `ais_vload_typing_inversion`,
`ais_vload_lane_typing_inversion`.

sig-typing-base (TypingLemmas.lean, Subtyping.lean, HelperLemmas.lean vs typing_lemmas.v, subtyping.v, helper_lemmas.v, axioms.v; coverage list at l.206-414). Findings:
- F1 [minor] `ibytes_inv` (HelperLemmas.lean:753) NOT equivalent to Rocq (axioms.v:53-55): Lean premise `(bs.length : Rat) = (v_N : Rat) / 8` (exact) is unsatisfiable unless 8 | v_N, so strictly weaker/vacuous, safe direction; unused. Rocq premise is `|bs| = Z.to_N (Qfloor (v_N/8))`.
  Other 8 axioms equivalent: `nbytes_len`, `ibytes_len` (Nat floor), `nbytes_len'`, `vbytes_len'`, `nbytes_inv`, `vbytes_inv` (exact vs floor coincide because `size` is concrete 32/64/128, wasm2.0.lean:798-805), `truncz_quot` (`Z.quot` = `Int.tdiv`), `lanes_len`.
  `ibytes_len'`/`ibytes_len''` (axioms.v:24/32) = KNOWN inconsistent (exact vs floor), "already established", planned floor fix.
- F2 [minor] axiom-block docs wrong: HelperLemmas.lean:674-681 "brought axioms.v up from 2 to 9 axioms" (Lean has 11; Rocq axioms.v then had 23 incl. 12 Progress-only); :683-684 says `size` is a backend opaque (it is a concrete `def`, wasm2.0.lean:798); :701-704, :709-710 call the primed axioms
  "Rat-valued restatement without the floor" (Rocq's `|x| = q` floors via `Qfloor`/`Z.to_N`): the same misreading is the root of the known `ibytes_len'/''` inconsistency and of F1.
- F3 [minor] `ai_principal_typing` (TypingLemmas.lean; the agent read 311-466) LOAD packed arms (:412-416) and STORE packed arms (:421-424) differ from Rocq (typing_lemmas.v:544-555 / :564-568, :622): Lean strictly stronger (False where Rocq has `True`/real type), only in cases where `Instr_ok2` is uninhabited
  (`loadop_`/`loadop_Inn`/`sz` are single-constructor: wasm2.0.lean:1839-1855, 992); STORE documented (TL:300-310), LOAD not; no preservation effect.
- F4 [minor] `upd_*_is_same_as_append` (4 lemmas, TypingLemmas.lean:69-84) state a record-update tautology (`rfl`) instead of Rocq's `... @@ C`; unused; doc (:65-68) misdescribes Rocq's near-empty context. Faithful restatement `({ ... } : context) ++ C` expressible and should close by `rfl`/`simp` (reasoned, not machine-checked).
- F5 [minor] most not-ported Rocq decls only recorded in bundle17 gap_analysis_v1 (§3c/§3e/§3f/§3g), no in-file NOT PORTED notes (subtyping.v: `cvt_N_to_ssrnat`, `cvt_ssrnat_to_N_le`, `size_length`, `all2_cat'`, `all2_cat`, `size0nil'`, `*_preorder`; typing_lemmas.v: `fun_res_list__list`, `fun_list__res_list`,
  `functype_from_lists`; helper_lemmas.v: `id_succ_N`, `cvt_succ`, `cvt_succ'`, `Forall2_seq_size`, `Forall2_size`, `Forall2_size2`, `split_cons`, `app_cat`, `add_subBN(')`, `sizecat'`, `sizeN_inj`; axioms.v: the 12 Progress-only axioms `ibits_inv` (:64), `feq_bit`..`fge_bit` (:72-77), `ishl_wf` (:83), `ishr_wf` (:85),
  `trunc_sat_total` (:95), `demote_nonempty` (:97), `promote_nonempty` (:99)). `Forall2_seq_size`/`Forall2_size`/`Forall2_size2` are FALSE for zip `Forall₂`; replaced by Lean-only `Forall2_nth_of_length` (HelperLemmas.lean:271).
- F6 [minor] stale headers claiming `sorry` stubs: TypingLemmas.lean:26-36 ("MAJOR TODO ... `instr_of` and `ai_principal_typing` bodies are sorry stubs"; "~57 cases" vs actual ~60 arms), Subtyping.lean:22, HelperLemmas.lean:24.
- F7 [info] zip-`Forall₂` deviations here are the documented ones (`Vals_ok` TL:1775; `Forall2_app'/take/drop` Subtyping.lean:196/222/231 true but lack implicit length; `ResulttypeSub` faithful since generated `Resulttype_sub` has explicit length premise wasm2.0.lean:12735-12739).
- F8 [info] 20 citations of helper_lemmas.v lemmas that no longer exist in Rocq: 14 are marked-for-deletion `sorry` lemmas, 6 are live proved Lean lemmas needing a "Lean-only (Rocq lemma removed upstream)" relabel: `leadd` (:182), `length_app_lt` (:195), `Forall_nth'` (:235), `add_false` (:546), `concat_cancel_last_n` (:659), `ltsize` (:666).
  No documented decl cites a wrong Rocq declaration; renames `_append_option_none`/`_none_left`/`_some_left` -> `option_orElse_none`/`option_none_orElse`/`option_some_orElse` checked.
- Observation (l.181-185): several of the 15 marked-for-deletion sorry lemmas are FALSE for zip `Forall₂`: `Forall2_nth`/`Forall2_lookup` (HelperLemmas.lean:307/315) conclude `l.length = l'.length` from Forall₂ alone (counterexample `l=[x]`, `l'=[]`), `Forall2_forall2weak` (:349) fails for the same lists with empty `R`; unused, off-path; deleting is correct; must not be revived as stated.
- Trust constructs (l.187-192): TypingLemmas/Subtyping: none (sorry hits only in stale docs). HelperLemmas: 15 `sorry`, all preceded by `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED` (15/15), 11 `axiom`s (HelperLemmas.lean:691-757), none used by any proof; no native_decide/implemented_by/unsafe/admit.
  (`Forall2_list_update_func2`, helper_lemmas.v:202, is one of the 15: "statement true under zip".)

## 8. Findings catalogue and status (what is and is not fixed per these logs)

M1 [MAJOR, confirmed x2, shared by all 3 backends, not a Lean-port deviation] `Moduleinst_ok` hoisted premise `List.length (GLOBAL addrs ++ MEM addrs ++ TABLE addrs ++ FUNC addrs) > 0` (wasm2.0.lean:15690; wasm.v:17174 `>? 0%N`; Isabelle ref .thy:13634;
spec B-soundness.spectec:230 only per-export membership under `*`). `fun_invoke` (wasm2.0.lean:15452-15484) builds the frame with the EMPTY module instance, so `Moduleinst_ok s {} C` is false (`NonVacuity.emptyMI_not_ok`, `NonVacuity.invoke_config_not_ok`), hence Frame_ok/State_ok/Config_ok
(single constructors) fail for every `$invoke` configuration and (via `reduce_inst_unchanged`) every configuration reachable from one; `t_preservation` and the progress theorem never apply to them. Does NOT make preservation false or vacuous. Root cause sideconditions.ml (section 5). Status in logs: open, "report upstream".
M2 [MAJOR, confirmed] `Globaltype_ok` only admits `some r_MUT.MUT` (wasm2.0.lean:12688-12689; wasm.v:14685-14686; .thy:11392-11394) vs spec `|- MUT? t : OK` (6-typing.spectec:35-36); every `Store_ok` global must be mutable; imports blocked too. Root cause undep.ml:162-164. Status: open.
M3 [MAJOR, confirmed] SE-1 (section 6). Status in logs: open (recommended fix given); unused so no preservation effect.
Others by severity: minor/new: audit-isabelle F5; sig-ext SE-2, SE-3, SE-5, SE-6; sig-tp-tpp 1-5; sig-typing-base F1-F6; info: audit-model F2/F3/F4/F5/F6/F7, audit-isabelle F2/F3/F4/F6/F7, sig-ext SE-4/SE-7/SE-8, sig-tp-tpp 6-7, sig-typing-base F7/F8.
audit-proofmap (partial, l.32-41): citation checker over the 6 hand-written Lean files: ok=92, wrong line=166, not declared in current Rocq=20 (HelperLemmas lemmas removed upstream after `0c9a5417a`, documented NOTES.md 2026-09-23); wrong-line per file TypingLemmas 60, Subtyping 41, HelperLemmas 27, TypePreservationPure 27, TypePreservation 7,
ExtensionLemmas 4; they match OLD checkouts (e.g. `typing_lemmas.v:1184 ais_composition_typing` is the 5b03ae067/dac300994 (2026-07-01) position, now 1143; `type_preservation.v:2668 t_preservation` is a094a13af (2026-05-04), now 3412); not disclosed in the Lean headers (Subtyping/HelperLemmas headers claim every declaration cites its Rocq line number).
sig-tpp (partial, l.37-42): citation check TPP: 47 correct, 27 stale, 2 no line, 3 Lean-only; all 27 stale = declaration lines of `git show 5b03ae067:.../type_preservation_pure.v`.

## 9. Safety-script race documented in these logs

audit-hygiene.md:33-37 / 298-313, audit-isabelle.md:20-47, sig-ext.md:15-77: at 05:27:54Z about 11 agents ran `check.sh` in the same second; it named its output `check-<UTC second>.txt` and wrote with `> "$OUT"`, so concurrent writers left NUL holes, `grep` reported
"binary file matches", the filtered NEW side was empty and `diff` printed `1,256d0` ("DIFFERENCE FOUND") although nothing had changed (file later `ASCII text`, 0 NUL bytes; manual re-diff clean; `verify_against_baseline.sh` also picked `NEW` via `ls -t | head -1`, possibly another agent's file). Handling: agents stopped audit work, diagnosed read-only,
re-ran the official check (clean), flagged it. Recommended fixes: `grep -a`, unique per-call file names (sub-second/PID/label), compare the file the call produced instead of `ls -t | head -1`. The v2 logs show the naming fix was adopted (names like `check-20261005T105050.478255929Z-audit-isabelle-1403015.txt`); whether `grep -a` was adopted is not shown in these logs.
The verify.sh used in the present session (read by me) already uses `grep -a`, sub-second + label + PID names and writes `.partial` then `mv`.

## 10. Relevance to the upstream changes (Rocq 6582b3a39, spec 4cf9f29c5)

R1 [vcvtop TRUNC_SAT / Inn destination] The Rocq-false case `vcvtop_trunc_sat_i16_stuck` (type_progress.v:6132 at that time) is exactly the "stuck" VCVTOP case (audit-isabelle.md:265-266). Lean counterparts to re-check against the renamed constructors `vcvtop__Fnn_1_M_1_Inn_2_M_2`:
TypePreservationPure.lean `ais_vcvtop_typing_inversion` and `Step_pure__vcvtop_preserves` (SIMD section l.1283-1840; sig-tp-tpp.md:184,188). The logs say nothing about how those proofs destructure the vcvtop constructors, so I cannot say whether they break. Also `trunc_sat_total` (axioms.v:95) may have changed.
R2 [vloadop SHAPE M > 1] The stuck case `vload_shape64_stuck` (type_progress.v:6107). Lean: `Step_read.vload_shape_val` (wasm2.0.lean:14580; premises include `v_N = List.length j_lst` and a `Forall₂ _ (List.range v_N) ...` rendering of Rocq `List_Foralli`; audit-isabelle.md:79-80, audit-model.md:53,80), TP lemmas `ais_vload_typing_inversion`, `ais_vload_lane_typing_inversion`, `Step_read__vload_preserves`,
`Step_read__vload_lane_preserves` (sig-tp-tpp.md:161-166). The new `M > 1` premise adds a hypothesis to the SHAPE `vloadop_`/wf/Instr_ok path (inference).
R3 [ishl_/ishr_/vshiftop] `ishl_wf` (axioms.v:83) and `ishr_wf` (:85) were listed as the Progress-only axioms NOT yet ported to Lean (sig-typing-base.md:144-145,407-408; audit-isabelle.md:267): upstream deleted them, so only 10 of the 12 remain to be ported/avoided: `ibits_inv` (:64), `feq_bit`/`fne_bit`/`flt_bit`/`fgt_bit`/`fle_bit`/`fge_bit` (:72-77), `trunc_sat_total` (:95), `demote_nonempty` (:97), `promote_nonempty` (:99).
Whether Lean's `ishl_`/`ishr_` are `opaque` is not stated (64 Lean opaque = 64 Rocq Axiom, audit-model.md:90). `Step_pure.vshiftop` has an explicit length premise beside its `Forall₂` (audit-model.md:139-141), and TPP has `ais_vshiftop_typing_inversion` and `Step_pure__vshiftop_preserves`: re-check them against the new `n mod lsize` rule.
R4 [iadd_ / memory.fill-succ, memory.copy-le, memory.init-succ] `iadd_` is a concrete `def` identical to Rocq's (audit-model.md:84-87), so `CONST I32 (iadd_ 32 i 1)` should have a `Nat.mod_lt`-style wf proof (verify in the regenerated file that `iadd_` is not opaque). The old problem the change removes: the 2^32 corner (`i'+1 <= 2^32-1` can fail when
`Memtype_ok` k = 2^16 pages, Isabelle Preservation.thy:5197, 5294-5310; audit-isabelle.md:114-116,157-159,227-229; NOTES.md `Step_read_is_wf` note). The logs ALSO record the table analogue: Isabelle Preservation.thy:4408 `table_init_succ` needs wf of `CONST I32 (i+1)`, true given `Store_ok` (Eleminst_ok `|refs| < 2^32`, Tabletype_ok `n <= 2^32-1`); upstream's
list names only the memory rules, so check whether table.fill/copy/init-succ in the regenerated model still push `i+1`.
R5 [Step_read_is_wf] Old Lean location wasm2.0.lean:16034 (`sorry`), directly after `Store_ok` (15992-16025) and before `Step_is_wf` (16045, proved). Statement = Rocq's hand-edited one: hand-added `Store_ok (fun_store z)` premise and moved after `Store_ok` (wasm.v:17351-17353 comment; Rocq proof was `Admitted` at wasm.v:17698; `Step_is_wf` comment 17701, `Qed` 18147; `Step` at wasm.v:16355).
Store_ok premise is genuinely needed (`Step_read__table_size` pushes `CONST I32 (mk_uN |REFS|)`; `wf_tableinst` does not bound `|REFS|`; audit-isabelle.md:117-119,161-163). Users in Lean: TypePreservation.lean:2036 (`t_read_preservation`), :2690 (`t_preservation` via `Step_is_wf`), `Step.ctxt_label/ctxt_frame/ctxt_instrs` (wasm2.0.lean:14706/14711/14716, need `wf_config` pre and post)
so the progress port also needs `Step_is_wf`. Facts the proof needs, per the Isabelle sorry list: load_num_val/load_pack_val/vload_val/vload_lane_val wf of loaded values (numeric opaque `*_is_wf`; `load_num_val` carries `wf_num_ nt c`), table_init_succ, memory_copy/init cases, table_size. Even after it is proved, `t_preservation` still depends on the 4 numeric sorries
`nbytes__is_wf`, `ibytes__is_wf`, `wrap___is_wf`, `vbytes__is_wf` via `store_extension_reduce` (TP:1552-1579). Rocq's `Admitted` lemmas may be used inside the Rocq `Qed`; the Lean analogue leaves those `sorry` in `#sorry_deps`.
R6 [stuck cases / t_progress_be] Old Rocq status `t_progress_be` Admitted (type_progress.v:5512), `t_progress_e` Qed (6062), `t_progress` Qed (6094); the two documented counterexamples were `vload_shape64_stuck` (6107) and `vcvtop_trunc_sat_i16_stuck` (6132). README.md:14 says the Lean progress port proved 280/280 "(2 with one documented known-false `sorry` each)": per the inference in section 1 these are the two cases upstream
removed; they become provable/deletable once the regenerated model is installed. Lean `typeof : val -> valtype` does not exist (Rocq type_progress.v:262).
R7 [bundle19 wasm2.0 hand edits: what the logs say] (i) `Step_read_is_wf`/`Step_is_wf` placement + `Store_ok (fun_store z)` premise (R5). (ii) the proofs of the `*_is_wf` theorems: wasm2.0.lean has 152 `*_is_wf`, 63 `sorry` (62 Rocq-Admitted `*_is_wf` + `Step_read_is_wf`; Rocq also admits `res_list_eq_dec`, wasm.v:429-431, not needed in Lean), of which 33 are on the preservation path
(logs state "32 known numeric sorries" and "33 known generated sorries"; 32 numeric + Step_read_is_wf = 33 is my reconciliation). (iii) audit-proofmap.md:50-51 located "5 hand-written helper blocks" in wasm2.0.lean at lines 302, 3042, 5878, 12045, 13998 (contents not described), and `iswf_Forall₃_eq_of_func` proof lines at ~7605-7665 (audit-isabelle.md:78-79).
(iv) Prelude l.1-30 (Forall, zip-based Forall₂ at l.20-21, `Map = List.map` l.26-27, `splice`, `rat_to_nat` l.9) and `with_mem` = `splice` (l.12391-12398) are described as backend output / user decision, not hand edits. HEAD at audit time was `0a7507f41`.
R8 [regression checklist for the regenerated wasm2.0.lean, from the audit's verified invariants] constructor names/counts (Instr_ok 73, Instrs_ok 5, Expr_ok 1, Instr_ok2 6, Instrs_ok2 5, Expr_ok2 1, Step_pure 54, Step_read 47, Step 23; instr 68, admininstr 74, val 5, ref 3); Lean `opaque` count = Rocq `Axiom` count (64 before) and sorry set = Rocq Admitted set (62 + Step_read_is_wf); every zip `Forall₂`/`Forall₃` premise beside an
explicit length equality (404 uses, 391 paired, 13 documented exceptions); `Moduleinst_ok` `> 0` premise and `Globaltype_ok` `some MUT` (M1/M2) still present or fixed; `Resulttype_sub` carries an explicit length premise; `Step_read_is_wf` placement/premise; the audit's scripts (`scan2.py`, `fpall.py`, `check_cites.py`) and side-by-side extracts lived under the deleted `/tmp/claude-1000/...` scratch, only the method is in the logs
(audit-model.md:64-81, audit-proofmap.md:32-41). All Rocq line numbers in these logs refer to the PRE-pull Rocq tree and are stale after 6582b3a39.
R9 [hygiene state before the upstream pull] Lean trust surface seen by the audits: 11 `axiom`s (HelperLemmas.lean:691-757, none used by any proof; `ibytes_len'/''` known inconsistent as stated), 15 marked-for-deletion `sorry` lemmas in HelperLemmas.lean + 1 in ExtensionLemmas.lean:137, 63 `sorry` theorems in wasm2.0.lean (33 on the preservation path), 64 `opaque` functions in wasm2.0.lean; TypingLemmas/Subtyping/TypePreservation/TypePreservationPure have no sorry/axiom in code.
Since Rocq itself leaves the `*_is_wf` of opaque numeric/vector functions `Admitted` (sorry set = Rocq Admitted set, audit-model.md:92-93) and Isabelle sorries all 140 of its `*_is_wf` (audit-isabelle.md:237-238), eliminating those in Lean needs either bodies for the opaques or new axioms (inference, not stated in the logs).

## 11. Discrepancies between the logs

D1 Step_pure constructor count: 63 (audit-proofmap.md:49, audit-model.md:49 early note, the audit brief) vs 54 (audit-model.md:73,167-169, script-verified, wasm2.0.lean 13744-13997 and wasm.v 15540-15793). Use 54.
D2 Rocq axioms.v size: "22 axioms" (audit-isabelle.md:266) vs 23 (sig-typing-base.md:94; its coverage list shows 11 pre-progress + 12 Progress-only = 23 at audit time). Use 23 (now 21 with ishl_wf/ishr_wf deleted, if no others changed).
D3 `Moduleinst_ok` premise line: 15690 (findings) vs 15688 (audit-nonvacuity.md:63 progress note); verifier confirms 15690.
D4 SE-1 "materially different from Rocq" is over-broad for `s_invert_funcs` (tautology in Rocq too, verifier).
D5 `for-claude/is_wf_theorems.md:31` row for `Step_is_wf` stale (sig-tp-tpp.md:194-196).

## 12. Standing instructions / refinements found in these files

- User safety order (verbatim in the task; README.md:3-7 confirms all agents got it): never modify anything outside spectec/src/test-lean-claude; periodic programmatic check logged in claude-logging; any spawned agent must be told and must run + log the same checks.
- Audit-brief rule (sig-ext.md:68): if the safety check prints `DIFFERENCE FOUND`, stop immediately and report (diagnose false positives read-only, re-run, flag).
- User markers `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED` (15 HelperLemmas sorries, ExtensionLemmas.lean:128/137): deletion is the user's intent; do not revive the false ones as stated.
- Standing decision: Rocq Ltac automation not ported (Lean tactics instead); `Extend_store_wf_store`/`'` stand in for `invert_extend_store`.
- Accepted/known (not to be re-reported): stale Rocq line-number citations (brief §6b), Q-bridging lemmas not ported (brief §5), bundle17 gap_analysis_v1 §3d 28 missing decls, `with_mem` clamped splice = user decision (bundle18).
- Rocq `|x| = q` (`q : Q`) means FLOOR; state axioms with Nat floor.
- Severity rubric: minor = no effect on meaning; major = meaning changes or undocumented coverage restriction; critical = theorem false/vacuous.

## 13. Techniques and pitfalls recorded

- Lean 4 promotes leading inductive indices that every constructor uses as the same bare variable into PARAMETERS, so `Store_ok`, `Frame_ok`, `Moduleinst_ok`, `Globalinst_ok` (the store `s`) and `fun_invoke` (`s`, `fa`) have fewer constructor fields than the generated binder lists show; positional `cases ... with | ctor _ _ ...` must omit them (audit-nonvacuity run 3-4 failures);
  `Config_ok`/`State_ok` (first index is a constructor application) are unaffected. Example proofs: `NonVacuity.s_imm_not_ok` (`cases hs with | mk_Store_ok gl gts _ _ _ _ _ _ _ _ _ _ hlen hgl _ _ _ _ _ _ _ _ _ _ heq`, then `congrArg store.GLOBALS heq`), `invoke_config_not_ok` (`cases hinv with | fun_invoke_case_0 _ _ f _ _ hf => subst hf; cases hc ...`), `emptyMI_not_ok` (`intro h; cases h; simp_all [Map]`).
- Witness-construction recipe (audit-nonvacuity.md:104-385): `forall_nil` (`intro x hx; cases hx`), `forall2_nil` (`intro t ht; simp at ht`), `Store_ok.mk_Store_ok s0 [gi0] [gt0] [] ... rfl ...`, `Moduleinst_ok.mk_Moduleinst_ok`, `Frame_ok.mk_Frame_ok`, `State_ok.mk_State_ok`, `Expr_ok2.mk_Expr_ok2`, `Instrs_ok2.instr/.seq`, `Instr_ok2.plain`, `Instr_ok.nop/const/drop`, `Config_ok.mk_Config_ok`, `Step.pure ... Step_pure.nop/drop`; wf constructors `wf_instr.instr_case_0` (NOP), `_2` (DROP), `_13` (CONST), `wf_admininstr.admininstr_case_*`, `wf_num_.num__case_0`, `wf_uN.uN_case_0`.
- The IDE (VS Code Lean extension, default toolchain v4.30.0-rc2) opens scratch files outside the lake project after an `Edit` and shows a spurious `unknown module prefix 'TypePreservation'`; scratch edits were done with `sed` to avoid triggering editor Lean processes. Import of TypePreservation costs ~3.6 GB RSS, ~2 s.
- Staleness check: recompute Lake's source hash with a temporary `#eval` and compare to `.lake/build/lib/lean/*.trace` inputs.
- Zip `Forall₂ P xs ys := ∀ t ∈ xs.zip ys, P t.1 t.2` (wasm2.0.lean:20-21): statements with an existentially chosen list are vacuous (`List.zip xs [] = []`, `List.zip_nil_right`); length equality cannot be derived from it (`Forall2_nth`, `Forall2_lookup`, `Forall2_forall2weak`, `Forall2_seq_size`, `Forall2_size`, `Forall2_size2` are false/need an `hlen`); recover lengths from the generated `List.length _ = List.length _` premises (Store_ok x6, Moduleinst_ok x6, Frame_ok, Resulttype_sub,
  Step_pure vshiftop/vbitmask, Step_read vload_shape_val); project helpers: `Moduleinst_ok_lengths` (TP:404-408), `Vals_ok` (TL:1775), `Forall2_nth_of_length` (HL:271), `Extend_store_datainsts₂` (TP:365-370).
- `datatype` is a singleton (`inductive datatype | OK`), so `Forall (fun a => Datainst_ok .. a datatype.OK)` is equivalent to Rocq's `Forall2` over `ts`.
- Rocq <-> Lean renderings (audit-model F4): `holds_upto P n` = `Forall P (List.range n)`, `List_Foralli` = `Forall₂ _ (List.range n) l`, `mkseqN`, `list_slice` = take/drop, `list_update_func` = `List.modify` (HL:40), `splice_eq_list_slice_update` (HL:439-445), Q->N `rat_to_nat` (wasm2.0.lean:9), `Option.orElse` = left-biased `option_append`; `pagediv` inlined as Nat `/`, `Qfloor_add_Z` replaced by `rat_to_nat_natCast` (TP:1315).
- `List.contains` <-> `∈` needs `LawfulBEq`; 13 types derive only BEq (list in section 3).
- `wf_store_with_elems` needs no ELEMS premise because generated `wf_store` (wasm2.0.lean:11511-11523) has none.
- Isabelle progress proof design to mirror/adapt (section 2, Item 6): `not_br_return`, typed value prefix, `br_return_contaminate_*`, `reducible_*`, `fun_*_total`, `typeofval_*`; Rocq uses `Admin_instrs_ok_ind'`, `Scheme ais_ok_ind'` for Extend_store_ais (Lean: `Instrs_ok2.rec`).
- Cross-check of generated models: premise fingerprint comparison per constructor over all 346 common inductives (audit-model.md:77-81).

## Safety check END (verbatim)

```
safety check [digest-audit-end] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T050350.137716568Z-digest-audit-end-455036.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
```

Remark on the NOTE line in the first END check above (written after that check; read-only inspection only):
the check reported one entry inside spectec/src/test-lean-claude that is not in the baseline:
`?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild`. It is inside the permitted directory (the
user's safety order is NOT violated; the line outside the directory still says VERIFIED), but it was not created by this agent:
this agent ran only reads, one `ls`, the safety script, and writes to this log. The file's mtime is 2026-10-15 12:52:21 +0800
(= 04:52:21Z), i.e. 33 s after my START check (04:51:48Z, which still reported nothing inside the directory changed) and ~11 min
before my first END check (05:03:50Z). `ps` shows a Lean language server for the project running (`lake serve -- .../test-lean-claude`,
`lean --server`, several `lean --worker` processes incl. TypeProgress.lean/TypePreservation.lean/ExtensionLemmas.lean), and the other
`.trace.nobuild` markers in that directory (e.g. TypingLemmas.trace.nobuild, mtime 2026-10-15 00:56) are of the same kind; so the
most likely creator is the IDE/language server (or another concurrent session) noticing that wasm2.0.lean changed (INFERENCE, not verified).
Because the first END check was no longer literally the last action after this remark, the check is re-run below as the final action.

## Safety check END (final re-run, last action, verbatim)

```
safety check [digest-audit-end] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T050433.419030578Z-digest-audit-end-455619.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
```

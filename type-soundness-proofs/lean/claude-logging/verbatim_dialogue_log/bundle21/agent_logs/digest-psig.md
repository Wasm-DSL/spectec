# digest-psig: digest of the bundle20 progress-signature agent logs

Label: `digest-psig`. Read-only digest. Only writes: this file and scratch dumps under
`/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/work/digest-psig/`
(the six `final_chunkN.lean` / `tr_chunkN.lean` / `fx_chunk4.lean` dumps of the JSON `lean_code` fields).
Nothing was written inside `/home/zhengyew/spectec`. No agents spawned, no lake, no git writes.

## 0. Safety check (START), verbatim

Command: `bash /tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/verify.sh digest-psig-start`

```
safety check [digest-psig-start] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T045149.087491283Z-digest-psig-start-448790.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
VERIFIED: nothing inside spectec/src/test-lean-claude changed either (apart from safety-check files)
```

## 1. Files read (completely)

Directory: `/home/zhengyew/spectec/spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle20/agent_logs/`

- `psig-1.md` .. `psig-6.md` (translators, one per chunk), `psig-audit-1.md` .. `psig-audit-6.md` (independent
  auditors), `psig-fix-4.md` (fixer for the one audit problem).
- `progress_signatures_results.json` (275 KB; dict with keys `summary`, `agentCount`, `logs`, `result`,
  `workflowProgress`, `totalTokens`, `totalToolCalls`). All 6 `result[i]` records (`chunk`, `tr`, `au`, `fx` (chunk 4
  only), `final`) were parsed with `python3 -I`; every non-code field of `tr`/`au`/`fx`/`final` was read;
  the `final.lean_code` of all six chunks was read in full (dumped to the scratch dir); `tr.lean_code` was compared with
  `final.lean_code` by `cmp`/`diff` (identical for chunks 1,2,3,5,6; chunk 4 differs only in the `Forall2_size_eq` block and one
  doc-comment sentence of `Forall_exists_Forall2`, see section 4). `workflowProgress` entries only carry metadata and
  401-character previews (truncated in the file itself).

Extra read-only lookups OUTSIDE the assignment (grep / sed ranges, to locate impact; flagged "observed" below):
`TypeProgress.lean` (lines 1-60, 3280-3300, 3515-3545, 5640-5690, 6715-6740, 7198-7212, 7925-8030 and greps),
`wasm2.0.lean` (greps, lines 1777-1800), `ls`/`find` for the `wasm2.0.lean` copies.

## 2. What the run was

bundle20 "progress port", signature phase: translate the 190 Rocq `Lemma` declarations (in file order; defs, Ltacs and Schemes are handled elsewhere) of
`spectec/test-rocq/theories/type_progress.v` lines 25-6159 into Lean 4 signatures with `sorry` bodies, in `namespace TLC`,
each preceded by a `-- @@ <rocq_name>` merge marker (the main thread merges), then audit each chunk independently, then fix.
13 agents, all model `claude-opus-5-5` (workflowProgress), 1,564,415 tokens, 485 tool calls. Phases: Translate (psig-1..6),
Audit (psig-audit-1..6), Fix (psig-fix-4). Completion order in `logs`: chunk 1, 3, 2, 5, 4, 6.

| chunk | Rocq lines | Rocq decls | Lean theorems | Lean defs | NOT PORTED | substantive deviations | audit (ok_count / problems) |
|---|---|---|---|---|---|---|---|
| 1 | 25-650 | 32 | 31 | 0 | length_size | const_es_exists (sig -> exists) | 32 / 0 |
| 2 | 652-1278 | 31 | 29 | 2 (`br_reduce_decidable`, `return_reduce_decidable`) | none | 2x Decidable def, Forall2_Val_ok_is_same_as_map (hlen) | 31 / 0 |
| 3 | 1280-1759 | 32 | 32 | 0 | none | none | 32 / 0 |
| 4 | 1761-2212 | 32 | 31 (after fix; 32 before) | 0 | Forall2_size_eq (after fix) | Forall_exists_Forall2, Forall_iabs_total (length conjunct) | 31 / 1 (Forall2_size_eq, suspicious) |
| 5 | 2214-2624 | 31 | 31 | 0 | none | none forced | 31 / 0 |
| 6 | 2636-6159 | 32 | 32 | 0 | none | vcvtop_lanes_total (length conjunct) | 32 / 0 |

Totals: 190 Rocq declarations -> 188 Lean declarations (186 theorems + 2 defs) + 2 NOT PORTED (`length_size`, `Forall2_size_eq`).
Lean check of each scratch `Chunk.lean` (all by `cd .../test-lean-claude && timeout 900 lake env lean <scratch file>`): exit 0, only
`declaration uses sorry` warnings (31/31/32/32 -> 31 after fix/31/32), zero errors. Audits did NOT run Lean (reading only).

### Rocq declarations and line numbers per chunk (Lean name = Rocq name in every case; no `_p` suffix needed anywhere)

1. (25-629): cat_nil 25, length_size 33 (NOT PORTED), LOCAL_injective 37, default_not_none 43, wf_config_app 53, v_to_e_const 83,
   const_list_cat 95, const_list_concat 104, const_list_split 114, const_es_exists 124, map_eq_nil 143, map_neq_nil 151,
   reduce_trap_left 159, v_e_trap 174, concat_cancel_last 186, extract_list1 197, v_to_e_cat 206, be_to_e_cat 214, to_e_list_cat 222,
   cat_split 231, terminal_form_v_e 246, typeof_append 271, typeof_cat 295, invert_typeof_I32 416, invert_typeof_I64 434,
   invert_typeof_numtype 452, invert_typeof_numtype_wf 467, invert_typeof_V128 482, invert_typeof_reftype 498,
   invert_typeof_reftype' 530, list_slice_size 560, split_vals_inverse 629.
2. (652-1221): split_vals_prefix 652, br_reduce_decidable 666, return_reduce_decidable 692, not_br_reduce_not_lf_br 717,
   not_return_reduce_not_lf_return 725, not_lf_br_singleton 733, not_lf_return_singleton 741, not_lf_br_right 749, not_lf_br_left 760,
   not_lf_return_right 772, not_lf_return_left 783, Forall2_Val_ok_is_same_as_map 795, frame_t_context_local_types 808,
   frame_t_context_label_empty 819, wf_forall_admin_val 829, wf_forall_admin 846, wf_config_label 857, wf_config_frame 870,
   frame_t_context_return_empty 885, Admin_instrs_ok_cons 895, Admin_instrs_ok_cat 912, Admin_instrs_ok_all 949, s_typing_lf_br' 972,
   s_typing_lf_br 1009, s_typing_lf_return 1045, s_typing_not_lf_br' 1072, s_typing_not_lf_br 1094, s_typing_not_lf_return 1116,
   size_eq1_cat 1137, br_reduce_extract_vs 1159, return_reduce_extract_vs 1221.
3. (1280-1735): lookup_types 1280, funcs_size 1290, admininstr_CONST_eq_arg 1300, typeof_non_bot 1308, typeof_vals_non_bot 1317,
   unop_not_none 1333, two_pow_pos 1348, Zsub1_toN 1351, wf_uN_lt 1357, two_pow_succ 1368, signed_total 1376, invsigned_total 1405,
   Zquot_abs_le 1425, Zquot_ge_inv 1435, wf_uN_lt' 1456, signed_nonzero 1459, lt_wf_uN 1467, inv_signed_wf 1475, idiv_total 1485,
   irem_total 1535, ilt_total 1562, igt_total 1572, ile_total 1582, ige_total 1592, idiv_wf 1612, wf_uN_mk_proj 1621, wf_fN_num_ 1624,
   wf_opt_num_ 1629, binop_total 1663, relop_total 1691, cvtop_total 1715, binop_before 1735.
4. (1761-2200): binop_not_none 1761, relop_before 1774, relop_not_none 1787, cvtop_before 1800, cvtop_not_none 1824,
   testop_not_none 1836, Forall_all 1854, all_Forall 1858, Forall_exists_Forall2 1865, Forall2_size_eq 1874 (NOT PORTED after fix),
   wf_lane_Jnn_inv 1884, wf_lane_Jnn_some 1897, wf_lane_Fnn_inv 1905, Forall_lane_Jnn 1916, Forall_lane_map_wf 1927,
   Forall_lane_fop_wf 1938, iabs_lane_total 1953, Forall_iabs_total 1968, vunop_real 2004, vunop_total 2032, vunop_not_none 2059,
   sat_s_range 2092, imin_total_wf 2103, imax_total_wf 2119, iadd_sat_total_wf 2135, isub_sat_total_wf 2149, lanes_Jnn_form 2170,
   lanes_Fnn_form 2179, jlane_some 2187, flane_some 2190, lanes_size_eq 2193, zip_lane_wf 2200.
5. (2214-2619): zip_flane_wf 2214, zip_lane_rel 2230, vbinop_some 2282, mk_uN_eta 2327, res_bool_bit 2332, ieq_bit 2335, ine_bit 2338,
   icmp_total_bit 2341, Forall_zipWith 2360, Forall2_all 2367, Forall_map_P 2375, vrelop_some 2400, invsigned_total_32m1 2442,
   Forall_list_slice 2447, mem_bytes_wf 2458, wf_config_mem_bytes 2471, all_and_Forall 2486, Forall_and_all 2494, packnum_not_none 2503,
   lanes_nth_wf 2513, vstore_lane_progress 2527, Forall2_map_l 2551, invert_typeof_I32_wf 2556, size_list_repeat 2568,
   Forall_list_repeat 2575, bit_of_wf1 2579, wf_dim_le16 2587, wf_ishape_inv 2594, holds_upto_intro 2604, jlane_proj_wf 2614,
   jlane_map_proj 2619.
6. (2636-6132): evens_odds_ind 2636, evens_odds_concat 2645, evens_odds_size 2652, Forall_evens 2658, Forall_odds 2664,
   Forall2_of_Forall 2670, list_slice_size_eq 2679, zip_lane_wf2 2687, zip_wf 2701, size_zipWith_eq 2710, shape_lanes_even 2715,
   add_sub_parens 2727, call_indirect_progress 2734, vcvtop_lane_total 2817, vcvtop_lanes_total 2849, setproduct2_Forall 2871,
   setproduct1_Forall 2875, setproduct_Forall 2882, setproduct_nonempty 2889, setproduct_pick 2897, halfop_total 2943,
   zeroop_total 2951, zero_lane_wf 2959, vcvtop_step_full 2969, vcvtop_step_half 2991, vcvtop_step_zero 3012, vcvtop_zero_numtype 3064,
   vcvtop_full_lsize 3076, vload_shape64_wf 6103, vload_shape64_stuck 6107, vcvtop_trunc_sat_i16_wf_instr 6124,
   vcvtop_trunc_sat_i16_stuck 6132.

Not in the chunk lists (handled by the main thread / already in TypeProgress.lean at the time): `is_const`, `const_list`, `terminal_form`,
`typeof`, `split_vals`, `br_reduce`, `return_reduce`, `not_lf_br`, `not_lf_return`, `instr_eqb`, `eqinstrP`, `Instr_ok_ind'`, `jlane`/`flane`
(v:2165/2167), `evens`/`odds`, `vcvtop_trunc_sat_i16` (v:2811), `halfop_of` (v:2912), `zeroop_of` (v:2921); Ltacs `invert_typeof_vcs`,
`num_shapes` (1602), `binop_wf` (1641), `vunop_case` (1980), `vlane_close` (2252), `bit_close` (2380), `vrelop_close` (2386),
`vcvtop_cases`, `vcvtop_cases_full`; and `t_progress_be`, `Instr_ok_Instrs_ok`, `Instr_ok2_ind'`, `t_progress_e`, `t_progress`.

## 3. All deviations (translator decisions that are not literal)

1. `const_es_exists` (v:124): Rocq returns a `sig` `{vs | es = map admininstr_val vs}`; Lean states `∃ vs, es = List.map admininstr_val vs` (Prop), per the
   brief's table. Doc comment has **Deviation:**. Harmless: all 8 Rocq uses (v:165, 767, 790, 5405, 5677, 5737, 5880, 6052) only destructure it.
2. `br_reduce_decidable` (v:666), `return_reduce_decidable` (v:692): stated as `def ... : Decidable (br_reduce es) := sorry` (not `theorem`).
   Reason: Rocq's `decidable` there is ssrbool's sumbool `{P}+{~P}` (type_progress.v:13 imports mathcomp ssrbool LAST; mathcomp ssrbool
   re-exports Corelib `ssr/ssrbool.v:597 Definition decidable P := {P} + {~ P}`; Stdlib's Prop-valued `P \/ ~P` is shadowed). Lean ctor order is
   `isFalse`/`isTrue` (Rocq: left : P / right : ~P). Not an `instance`. A classical proof needs `noncomputable` (Rocq's proof is constructive via
   `split_vals`). Weaker alternative offered: `br_reduce es ∨ ¬ br_reduce es`. Auditor psig-audit-2 verified the sumbool reading on disk.
3. `Forall2_Val_ok_is_same_as_map` (v:795): extra premise `v_t1.length = v_local_vals.length →` right after the `Forall₂ (fun v s => Val_ok v_S s v) v_t1 v_local_vals`
   premise (hlen). Counterexample without it: `v_t1 = [t, t']`, `v_local_vals = [v]`. Precedents: `funcinst_same` (ExtensionLemmas.lean:1077), `Vals_ok`.
4. `Forall_exists_Forall2` (v:1865): conclusion `∃ la, (Forall₂ R la l ∧ la.length = l.length) ∧ Forall P la`; literal zip-based `Forall₂` would hold with `la = []`.
5. `Forall2_size_eq` (v:1874): translator first gave `Forall₂ R la lb → la.length = lb.length → la.length = lb.length` (tautology, `fun _ h => h`) and said "main
   thread may prefer NOT PORTED"; audit flagged it; fix agent replaced it by a NOT PORTED comment (section 4).
6. `Forall_iabs_total` (v:1968): conclusion `∃ vs, (Forall₂ (fun v l => fun_iabs_ (lsizenn (lanetype_Jnn J)) (Option.get! (proj_lane__0 l)) v) vs ls ∧ vs.length = ls.length) ∧ Forall ... vs`.
   Needed by the generated `fun_vunop_` iabs cases (wasm2.0.lean 5622-5626, 5637ff) which carry a separate `List.length var_0_lst = List.length lane_1_lst` premise.
7. `vcvtop_lanes_total` (v:2849): added conjunct `vs.length = L.length` right after the `Forall₂ (fun v ci => fun_lcvtop__ sh_1 sh_2 op ci v) vs L` conjunct. Translator says it is
   "easy to drop if the main thread prefers the literal form (precedent `s_invert_funcs` in ExtensionLemmas.lean kept an existential Forall₂ without a length conjunct)".
8. `length_size` (v:33): NOT PORTED (Rocq-only stdlib `length` vs mathcomp `size` bridge; `Iff.rfl` in Lean; unused elsewhere in the Rocq theories per auditor grep).
9. Representation choices recorded as "not deviations": `eqType` binders -> `Type` (`evens_odds_concat`, `setproduct2_Forall`, `setproduct1_Forall`, `setproduct_Forall`,
   `setproduct_nonempty`, because Lean's generated `concat_`/`setproduct*_` take plain `Type`); `vstore_lane_progress` Rocq `Qeq_bool (M:Q) ((128%num:Q)/(jsize J:Q))%Q = true`
   -> `(M : Rat) = ((128 : Rat) / (jsize J : Rat))` (same as generated `Step.vstore_lane_val`, old wasm2.0.lean:14779); `res_bool_bit` uses `nat_of_bool` (same spectec def
   3-numerics.spectec:9.1-9.22 as Rocq `res_bool`); `Zsub1_toN` writes Rocq `(1%num : Z)` as `(1 : Int)`; `v' : N` -> `Nat`; `size_list_repeat` kept (= core `List.length_replicate`)
   because Rocq proofs use it by name (translator: main thread may switch to NOT PORTED).
10. Cases where NO hlen was needed (Forall₂ only in a conclusion whose length is already a premise / part of the conclusion / automatic): `zip_lane_wf`, `zip_flane_wf`,
   `zip_lane_rel` (Forall₃, with `vs.length = L1.length` in the conclusion), `Forall2_all`, `Forall2_of_Forall`, `zip_lane_wf2`, `Forall2_map_l`; and `frame_t_context_local_types`
   (Lean `Frame_ok` carries `t_lst.length = val_lst.length`), `funcs_size`/`lookup_types` (Lean `Moduleinst_ok` carries `funcaddr_lst.length = functype_F_lst.length`).

## 4. Audit problems (all of them) and their resolution

Only ONE problem in the whole run: chunk 4, `Forall2_size_eq`, severity `suspicious`.
- Description (psig-audit-4): the hlen premise makes the Lean statement a tautology whose conclusion is literally a premise; the project already marks the identical Rocq lemma
  `Forall2_seq_size` (helper_lemmas.v:159) NOT PORTED at HelperLemmas.lean:293. Rocq uses (Ltac `vunop_case` at v:1982 and v:3941) only extract the length.
- Suggested fix: replace by a NOT PORTED comment under the kept `-- @@ Forall2_size_eq` marker; coverage entry -> NOT PORTED.
- Resolution (psig-fix-4): "AUDIT RESOLUTION: 1 audit item, ACCEPTED; 0 rejected." Final chunk 4 has the comment
  "`Forall2_size_eq` (type_progress.v:1874, `Forall2 R la lb -> (|la|) = (|lb|)`) NOT PORTED: Rocq's inductive `Forall2` carries the length but Lean's zip-based `Forall₂` does not
  (the literal statement is false in Lean, e.g. `la = []`, `lb = [b]`), so adding `hlen` would make the lemma return its own premise (same as `Forall2_seq_size`, HelperLemmas.lean:293).
  Its Rocq uses (Ltac `vunop_case` at 1982 and 3941) only extract the length; Lean callers take it from the length conjunct of `Forall_iabs_total` / `Forall_exists_Forall2`."
  Also the `Forall_exists_Forall2` doc comment sentence changed ("Downstream Rocq uses of `Forall2_size_eq` (1982/3941; NOT PORTED in Lean) need exactly this length fact, which Lean
  callers take from this conjunct"); signature unchanged; no other declaration touched. Fix-check: exit 0, 31 sorry warnings.

Audit remarks that were deliberately NOT recorded as problems (all other audits: `problems=[]`):
- audit-1: generic lemmas (`cat_nil`, `map_eq_nil`, `concat_cancel_last`, `extract_list1`, `cat_split`, `list_slice_size`) use `Type` (level 0) whereas Rocq's `Type` is universe generic; immaterial (also `size_eq1_cat` per audit-2).
- audit-3: `lt_wf_uN` writes `(v_N : Nat)` where siblings write `(v_N : N)` (same type, `abbrev N := Nat`); `wf_opt_num_` uses `Option.map` where generated premises use `OMap` (`OMap f o` unfolds to `o.map f`, defeq).
- audit-4: translator's coverage note for `Forall_exists_Forall2` claims the "Vals_ok / from_mathlib_forall₂ precedent" but those put the length FIRST (TypingLemmas.lean:1776, HelperLemmas.lean:889), the new lemmas put it AFTER; cosmetic, Lean doc comment does not repeat the claim.
- audit-5: usability note on `Forall_zipWith` vs generated `Map₂` (section 5).
- audit-6: `setproduct_pick` states `c ∈ ...` while Lean's `fun_vcvtop__` premise uses `List.contains` (section 5).

## 5. Facts, conventions, techniques and pitfalls recorded

Translation table used (from the brief as quoted in the logs):
`seq`->`List`; Rocq `N`/`res_N` (`Definition res_N := N`, wasm.v:342) ->`N` (Lean `abbrev N := Nat`); scope keys: after mathcomp `ssrnat`, `%num`/`%BN` denote binary `N` and `%N` denotes `nat`, all -> `Nat`;
`binN_scope` (wasm.v:141-155): `+` `N.add`, `-` `N.sub` (truncated), `^` `N.pow`, `<=`/`<` are Prop `N.le`/`N.lt`, `>?` is bool `N_gtb`; `|x|` = `N.of_nat (seq.size x)` (wasm.v:309) -> `x.length`;
`!(x)` = `the x` (wasm.v:310) -> `Option.get! x`; `x [| k |]` = `lookup_total` -> `x[k]!`; `(u :> N)` (coercion `proj_uN_0_coercion`, wasm.v:529) -> `proj_uN_0 u`;
`is_true b` -> `b = true`; Rocq bool `!=` in Prop position -> `≠`, inside a bool predicate -> `!=` (bne); `~~ b` -> `¬ ...` / `... = false`; mathcomp `all P l` -> `l.all P`; `\in` -> `∈`;
`list_slice l i j` (wasm.v:57, drop i then take j) -> `List.take j (List.drop i l)`; `list_zipWith` (map over truncating `seq.zip`, wasm.v:22) -> `List.zipWith`; `list_repeat x n` -> `List.replicate n x`;
`List.Forall` -> `Forall` (membership-based, wasm2.0.lean:17); `List.Forall2` -> `Forall₂` (ZIP-based, wasm2.0.lean:20); `List_Forall3` (wasm.v:88, args `R l l' l''`) -> `Forall₃` (wasm2.0.lean:23, same order);
`option_to_list`/`option_map` -> `Option.toList`/`Option.map`; `(ts1 :-> ts2)` -> `mkFunctype ts1 ts2` (Subtyping.lean:32); `Z.to_N` -> `Int.toNat`; `Z.of_N` -> `Nat -> Int` cast; `Z.quot` -> `Int.tdiv`
(precedent `truncz_quot`, HelperLemmas.lean:772-779); `Z.abs` -> Mathlib `|·|`; `res_size` -> Lean `size`; `res_bool` -> `nat_of_bool`; `sig` -> `∃`; sumbool `decidable` -> `Decidable` def.
Rocq `((2%num ^ (v_N - 1)%BN)%BN : Z)` -> `((2 ^ (v_N - 1) : Nat) : Int)`; Rocq `(0 - _)%Z` is kept as `(0 : Int) - _` (not `-_`).

hlen rule (project rule from the brief): Rocq inductive `Forall2` implies equal lengths, Lean's generated `Forall₂` is `∀ t ∈ l.zip l', P t.1 t.2` and does not.
Rocq `Forall2` as a PREMISE -> add `la.length = lb.length →` immediately after the `Forall₂` premise (`Forall2_Val_ok_is_same_as_map`).
Rocq `Forall2` in a CONCLUSION -> add a length conjunct right after the `Forall₂` (`Forall_exists_Forall2`, `Forall_iabs_total`, `vcvtop_lanes_total`), unless the length is already a premise/conjunct (section 3 item 10).
If hlen would make the conclusion a copy of a premise, mark NOT PORTED (`Forall2_size_eq`, precedent `Forall2_seq_size`, HelperLemmas.lean:293).

Pitfalls / techniques (lemma they came from):
- `size` clash (psig-2): Lean's generated `size : valtype → Option Nat` (old wasm2.0.lean:798) is Rocq `res_size`, NOT mathcomp `size`; always translate `size l`/`|l|` to `.length`. On a `resulttype` Rocq
  uses the global native coercion `fun_res_list__list : res_list >-> list` (typing_lemmas.v:17), so `|ts|`/`size t` -> `(proj_list_0 valtype ts).length` (`br_reduce_extract_vs`, `return_reduce_extract_vs`, precedent `t_progress_e_P1`).
- `lookup_total (LABELS C) 0` -> `C.LABELS[0]!` (same idiom as Lean `Instr_ok.br`); derived `Inhabited` default `mk_list []` = Rocq default (`br_reduce_extract_vs`).
- Lean `Frame_ok` (old 15743) has the premise `List.length t_lst = List.length val_lst` and conclusion `{LOCALS := t_lst, LABELS := [], RETURN := none} ++ C`; `Moduleinst_ok` conclusion has `LOCALS`/`LABELS = []`, `RETURN = none`;
  `append_context` (old 12623-12652) is fieldwise `++` with `RETURN` via `orElse`; these settle `frame_t_context_label_empty`, `frame_t_context_return_empty`, `frame_t_context_local_types`.
- `Resulttype_sub` (old 12735) has a length premise, so `Admin_instrs_ok_cat/cons` and the `*_extract_vs` lemmas cannot be broken by the `sub` rule; `Val_ok`/`Ref_ok` assign exact types (no subsumption);
  `Instr_ok.br` needs `l < |LABELS|` (so `s_typing_lf_br'` works: Frame context has no labels), `Instr_ok.return` needs `C.RETURN = some _`.
- `wf_config_label`/`wf_config_frame` (psig-2): Lean `wf_admininstr` LABEL_ case is `Forall wf_instr ∧ Forall wf_admininstr`, FRAME_ is `wf_frame ∧ Forall wf_admininstr` (old 11730 cases 71/72); the name `wf_config_frame` was freed by renaming the Lean-only helper to `wf_config_wf_frame` (TypePreservation.lean:871-875).
- `wf_config_app`: Lean `wf_config` = `wf_state ∧ Forall wf_admininstr`, so the iff is true (audit-1). `reduce_trap_left` is provable from `Step_pure.trap_vals` using `const_es_exists` (audit-1).
- `invert_typeof_I32/I64` are true in Lean because `wf_num_` forces `num_.mk_num__0` with `numtype.I32 = numtype_Inn Inn.I32`; `invert_typeof_reftype` can share one `x` for `REF_FUNC_ADDR`/`REF_HOST_ADDR` because `funcaddr = hostaddr = addr = Nat` are abbrevs;
  `invert_typeof_V128`: `Option.get! (size (valtype_vectype vectype.V128))` is `128` (plain def), `vec_ = vN = iN = uN` abbrevs (audit-1).
- `autoImplicit` is ON in the lakefile (psig-2): psig-2 re-ran its chunk with `set_option autoImplicit false` before `namespace TLC` (exit 0) to prove no misspelled identifier was silently auto-bound.
- `typeof` resolves to `TLC.typeof` (no root `typeof` in wasm2.0.lean); all new names are inside `namespace TLC`, so core/Mathlib names such as `List.map_eq_nil` cannot clash (psig-1/audit-1). Mathlib comes via `HelperLemmas` (`import Mathlib.Tactic`), giving `|a|`, `Odd` (root, confirmed with `pp.fullNames`), `Function.Injective`.
- Binder names `memarg`/`laneidx` (vstore_lane_progress) shadow the types and `M` (wf_dim_le16) shadows the generated `abbrev M`: harmless, kept to mirror Rocq.
- Rocq `type_progress.v` has no `Set Implicit Arguments`, no `Section`/`Variable`/`Hypothesis` (audit-1, audit-4), so `forall T` binders are explicit (`cat_nil (T : Type)`), `{X : Type}` ones implicit (`map_eq_nil`, `concat_cancel_last`, `extract_list1`, `cat_split`, `list_slice_size`, `Forall_list_slice`).
- `add_sub_parens` (psig-6): checked Rocq's elaboration with the local opam `coqc` (`spectec/test-rocq/_opam`) against `spectec/_build/default/test-rocq/theories/wasm.vo` READ-ONLY, in scratch `agents/psig-6/rocq/Chk2.v`: result
  `∀ (n1 n2 : N) (n3 : Z), (n3 <= Z.of_N n2)%Z -> (n1 + Z.to_N (Z.of_N n2 - n3))%BN = Z.to_N (Z.of_N (n1 + n2)%BN - n3)`; Lean: `n3 ≤ (n2 : Int) → n1 + ((n2 : Int) - n3).toNat = (((n1 + n2 : Nat) : Int) - n3).toNat`.
  The compiled `wasm.vo` is STALE (no `BN` scope, no `N`/`Z` coercions), so the notations/coercions were re-declared verbatim in the scratch file. A first attempt including `vload_shape64_stuck` hung in `:>` typeclass search and was abandoned;
  cleanup `pkill -f <pattern>` matched its own shell (exit 144) and killed only that coqc job. Lesson: never `pkill -f` a pattern that occurs in your own command line.
- `Forall_zipWith` vs `Map₂` (audit-5): generated `fun_vrelop_` writes lane results as `Map₂ f l1 l2` (= `List.zipWith (· ·) (List.map f l1) l2`, old wasm2.0.lean:27-28, 8410) where Rocq has `list_zipWith f l1 l2`;
  `apply Forall_zipWith` against `Map₂` would unify `f := fun g x => g x` and leave an unprovable side goal. When proving `vrelop_some`, first rewrite with a small lemma `Map₂ f l1 l2 = List.zipWith f l1 l2`.
- `setproduct_pick` / `vcvtop_step_full` (audit-6): Lean's `fun_vcvtop__` premise uses `List.contains (Map ..) v128`, so proofs need `List.contains_iff`/`elem_iff` (uN derives `LawfulBEq`); `fun_vcvtop__` rules also carry explicit `List.length var_lst = List.length c_1_lst` premises.
- Opaque/trust base (audits 3-6): `lanes_` and `inv_lanes_` are `opaque` in Lean (old 4644/4659) as `Axiom` in Rocq (wasm.v:6117); `lanes__is_wf` (old 4651, sorry) + `axiom lanes_len` (HelperLemmas.lean:785 = axioms.v:43) make `lanes_Jnn_form`, `lanes_Fnn_form`,
  `lanes_size_eq`, `lanes_nth_wf`, `shape_lanes_even` provable. `truncz` opaque + `axiom truncz_quot` (HelperLemmas.lean:778 = axioms.v:38) make `idiv_total`/`irem_total` provable as in Rocq. `trunc_sat_total`/`demote_nonempty`/`promote_nonempty`
  (HelperLemmas.lean:849-856 = axioms.v:95-99) are what `vcvtop_lane_total` needs. Opaque int/float ops have `_is_wf` lemmas `sorry` in Lean / `Admitted` in Rocq (e.g. `ior__is_wf`, wasm.v:4579). `idiv_` has no generated `_is_wf` (checked in both files).
- `meminst` derives `Inhabited` (old 11458; BYTES = []), so the out-of-range case of `mem_bytes_wf` (`ms[k]!`) is trivial; `fun_mem` (old 12237) uses `[..]!`; chain `wf_config -> wf_state -> wf_store -> Forall wf_meminst MEMS` (old 11964/11554/11516) gives `wf_config_mem_bytes`.
- `Step.vstore_lane_val` (old 14779) has no bounds premise, like Rocq (`vstore_lane_progress`).
- Numeric side: `wf_uN N (mk_uN i)` is `i ≤ Int.toNat (2^N - 1)` (⇔ `i < 2^N`) vs Rocq `i <= Z.to_N (2^N - 1)`; `fun_idiv_` case 3 uses Rat `=` where Rocq uses `Q ==` (same, Rat normalised); `sat_s_range` bound equals the one used inside `sat_s_` (`Int.toNat (v_N - 1)`);
  `fun_inv_signed_` has 2 cases and for `-1` at N=32 case_1 applies (`invsigned_total_32m1`); `Forall_all`/`all_Forall` are `List.all_eq_true` once `Forall` is unfolded (kept because `vunop_real`'s bool premise needs the bridge).
- Shape of the generated before-predicates relied on by chunks 3-4 (identical structure Rocq vs Lean, checked by constructor/premise counts): `fun_binop__before_fun_binop__case_38` (38 ctors, 68 premise lines), `fun_binop_` (39 ctors, 69 premise lines, catch-all
  `¬ before -> none`), `fun_relop__before_..._case_24` (24 premise-free ctors) / `fun_relop_` (25), `fun_cvtop___before_..._case_36` / `fun_cvtop__` (37 ctors, 25 premise lines), `fun_vunop__before_..._case_26`; `fun_testop_` is a plain `def : Option num_`.
- `vunop_real` form: premise `∀ J M, sh = shape.X (lanetype_Jnn J) (dim.mk_dim M) → (lanes_ sh val).all (fun l : lane_ => proj_lane__0 l != none) = true` (elaborates to `bne (proj_lane__0 l) none`), conclusion `(∃ vs, fun_vunop_ sh vunop val (some vs)) ∧ fun_vunop__before_fun_vunop__case_26 sh vunop val`.
- `holds_upto` is `TLC.holds_upto P n := Forall P (List.range n)` (ExtensionLemmas.lean:89 abbrev).

## 6. Relevance to the upstream changes (6582b3a39 / 4cf9f29c5)

Nothing in these files mentions `ishl_`, `ishr_`, `vshiftop`, `memory.fill/copy/init`, `Step_read_is_wf`, or "bundle19" (0 hits in the logs and in the JSON); `iadd_` only appears as `iadd_sat_total_wf`/`fun_iadd_sat_` (unrelated to the `iadd_ 32 i 1` change).
Everything affected is in chunk 6 (and the defs TypeProgress.lean already had):

(1) vcvtop TRUNC_SAT -> Inn destination; `vcvtop_trunc_sat_i16` removed. Rocq's `~~ vcvtop_trunc_sat_i16 op` was translated as `vcvtop_trunc_sat_i16 op = false →` placed right after the `wf_vcvtop__` premise in these 9 signatures, which must LOSE that premise (and the
    "(non `F32 → I16 TRUNC_SAT`)" wording): `vcvtop_lane_total` (v:2817), `vcvtop_lanes_total` (2849), `halfop_total` (2943), `zeroop_total` (2951), `vcvtop_step_full` (2969), `vcvtop_step_half` (2991), `vcvtop_step_zero` (3012),
    `vcvtop_zero_numtype` (3064), `vcvtop_full_lsize` (3076). Delete `vcvtop_trunc_sat_i16_wf_instr` (6124) and `vcvtop_trunc_sat_i16_stuck` (6132): they spell `vcvtop__.mk_vcvtop___2 Fnn.F32 4 Jnn.I16 8 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT sx (some zero.ZERO))`
    and `wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2`, which no longer exist. The Lean def `vcvtop_trunc_sat_i16` (TypeProgress.lean, Rocq v:2811; audited clause by clause by psig-audit-6) and `halfop_of`/`zeroop_of` (v:2912/2921; same audit) pattern-match on
    `.mk_vcvtop___2 ...`/`.TRUNC_SAT`. Audit-6 evidence that the old stuck lemma was true: Lean `fun_lcvtop__` TRUNC_SAT cases existed only for I32/I64 destinations (old wasm2.0.lean 9463-9478).
    Dependencies of the vcvtop lemmas named in the logs: `fun_halfop`, `fun_zeroop`, `fun_lcvtop__`, `fun_vcvtop__`, `wf_vcvtop__`, `Step_pure.vcvtop` (old 13990), `packnum_`, `fun_zero`, `fzero_is_wf`, axioms `trunc_sat_total`/`demote_nonempty`/`promote_nonempty`, `lanes_len`.
    Observed (own read-only grep, NOT from the assigned files): current TypeProgress.lean has `def vcvtop_trunc_sat_i16` at 3287-3292 (`| .mk_vcvtop___2 Fnn.F32 _ Jnn.I16 _ (.TRUNC_SAT _ _) => true`), `halfop_of` 3523-3530, `zeroop_of` 3532-3540, the premise in
    `vcvtop_lane_total` 3297-3298 (proof uses `vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0` + `simp [vcvtop_trunc_sat_i16] at Hts` at 3365-3370), `vcvtop_lanes_total` 3398-3400 (+ call 3415), `halfop_total` 3546-3548, `zeroop_total` 3569-3571,
    `vcvtop_step_full` 3602-3615, `_half` 3624-3637, `_zero` 3646-3689, `vcvtop_zero_numtype` 3701-3723, `vcvtop_full_lsize` 3740-3764, the consumer `t_progress_be_vcvtop` 5652-5681 (`cases Hti : vcvtop_trunc_sat_i16 op` at 5653, `| true =>` branch with a commented `sorry` at 5654-5656, every call passes `Hti`/`Hts`),
    and the counterexamples at 7935-8010. The regenerated wasm2.0.lean already has `vcvtop__Fnn_1_M_1_Inn_2_M_2` and `mk_vcvtop___2 (Fnn_1 : Fnn) (M_1 : M) (Inn_2 : Inn) (M_2 : M) ...` (lines 1548-1599).
(2) vloadop_ SHAPE needs M > 1. Delete `vload_shape64_wf` (v:6103: `wf_vloadop_ vectype.V128 (vloadop_.SHAPEX_ (sz.mk_sz 64) 1 sx)`; audit-6 noted it held via the case_0 premise `64*1 = 128/2`) and `vload_shape64_stuck` (v:6107, premise
    `proj_uN_0 i + proj_uN_0 ao.OFFSET + 8 ≤ (fun_mem z (uN.mk_uN 0)).BYTES.length`, conclusion `¬ Step_read ...`; it used `Step_read.vload_shape_oob`/`vload_shape_val`, old 14575-14590). Observed: the regenerated `wf_vloadop_.vloadop__case_0` (wasm2.0.lean:1777-1780) now ends in
    `... ∧ (v_M > 1)`, so `vload_shape64_wf` would be unprovable; current TypeProgress.lean has them at 7935-7978 and the `sorry` bullet in `t_progress_be_vload_pack` at ~6726 ("FALSE subcase ... see vload_shape64_stuck"); header comments at TypeProgress.lean:24, 45, 7204.
(3) ishl_/ishr_/vshiftop: no signature in these chunks mentions them (the `vbinop_some`, `vunop_*`, `vrelop_some` lemmas quantify over generated `fun_vbinop_`/`fun_vunop_`/`fun_vrelop_`; recheck only that those generated relations still have the same shapes after regeneration).
(4) memory.fill/copy/init succ + `Step_read_is_wf`: not mentioned; the memory-related signatures (`list_slice_size`, `Forall_list_slice`, `mem_bytes_wf`, `wf_config_mem_bytes`, `vstore_lane_progress`) do not depend on those rules. (Observed: regenerated wasm2.0.lean now has `theorem Step_read_is_wf` at 13274 and `Step_is_wf` at 13383.)
(5) bundle19 wasm2.0 hand edits: not mentioned. Every `wasm2.0.lean:NNNN` line number cited in these logs (e.g. Forall/Forall₂/Forall₃ 17-24, `uN` 166, `size` 798, `lanes_` 4644, `fun_vunop_` 5636, `fun_vbinop_` 6862, `fun_vrelop_` 8404, `Step_pure.vcvtop` 13990,
    `Step_read.vload_shape_*` 14575-14590, `Step.vstore_lane_val` 14779, `Moduleinst_ok` 15671, `Frame_ok` 15743, `Instr_ok2` 15785) refers to the PRE-regeneration file and is stale. Names the 188 signatures depend on (re-check shapes after regeneration): `Forall`, `Forall₂` (zip-based), `Forall₃`, `Map`, `Map₂`, `OMap`,
    `N`, `uN`/`wf_uN`/`proj_uN_0`, `fN`/`wf_fN`, `lane_`/`wf_lane_`/`proj_lane__0/1`, `lanes_`/`inv_lanes_` (opaque), `shape.X`/`wf_shape`/`lsize`/`lsizenn`/`lsizenn2`/`sizenn`, `fun_signed_`/`fun_inv_signed_`/`fun_idiv_`/`fun_irem_`/`fun_ilt_`..`fun_ige_`, `fun_binop_*`/`fun_relop_*`/`fun_cvtop__*`/
    `fun_testop_`/`fun_vunop_*`/`fun_vbinop_`/`fun_vrelop_`, `fun_iabs_`/`fun_imin_`/`fun_imax_`/`fun_iadd_sat_`/`fun_isub_sat_`, `sat_s_`, `Moduleinst_ok`, `Frame_ok`, `Instr_ok2`/`Instrs_ok2`, `Val_ok`, `Resulttype_sub`, `wf_config`/`wf_admininstr`/`wf_state`, `Step_pure.trap_vals`, `Step.vstore_lane_val`, `meminst`, `fun_mem`.
(6) The stuck cases: `vload_shape64_stuck` and `vcvtop_trunc_sat_i16_stuck` are the two machine-checked counterexample lemmas (psig-6 signatures) that justified the two `sorry` subcases of `t_progress_be` in the old Lean port; upstream deleted the corresponding Rocq lemmas, so both lemmas and both `sorry` subcases go away.

## 7. Other notable

- Merge-ready Lean text for every chunk lives in `result[i].final.lean_code` of `progress_signatures_results.json` (markers `-- @@ <rocq_name>`); observed: the current TypeProgress.lean has no `-- @@` markers (0), has the two `Decidable` defs proved with `by` (lines 595, 622) and the `Forall2_size_eq`/`length_size` NOT PORTED comments (2060, 64).
- Observed: TypeProgress.lean header says status end of bundle20: everything proved except two false-as-specced subcases (VLOAD 64x1 in `t_progress_be_vload_pack` and F32->I16 TRUNC_SAT in `t_progress_be_vcvtop`), `Step_read_is_wf` and 56 generated numeric `*_is_wf`; 17 project axioms.
- Observed: three `wasm2.0.lean` copies exist (`spectec/test-lean/wasm2.0.lean`, `spectec/src/test-lean-claude/wasm2.0.lean` (1,216,345 bytes, modified Oct 15 12:34), `spectec/src/temp_zy_dev/wasm2.0.lean`) plus `spectec/src/test-lean-claude/OLD_wasm2.0.lean` (1,325,954 bytes, modified Oct 15 00:56); psig-6 mentions "both `wasm2.0.lean` copies" in its name-clash grep (at bundle20 time).
- Safety: all 13 agents ran the START and END baseline check (26 checks), every one printed `VERIFIED: zero new changes outside spectec/src/test-lean-claude` against baseline `check-20261005T051653Z.txt`; every agent prompt begins "SAFETY FIRST (user standing order): you must NEVER modify anything outside
  /home/zhengyew/spectec/spectec/src/test-lean-claude. Inside it you may only write your own log file ...; scratch files go only in your scratch dir under /tmp/claude-1000/...".
- Run statistics (workflowProgress): psig-1 95,619 tok/35 calls/390 s; psig-2 118,719/39/559 s; psig-3 110,075/36/470 s; psig-4 137,828/43/614 s; psig-5 120,146/38/491 s; psig-6 171,816/53/849 s; audits 97,093-145,900 tok; psig-fix-4 65,661/15/223 s.

## 8. Safety check (END), verbatim

(Appended below by the final command, which runs the check and tees its output into this file.)
Command: `bash /tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/verify.sh digest-psig-end` (exit code 0)

```
safety check [digest-psig-end] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T050020.890769223Z-digest-psig-end-453076.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
```

# audit-isabelle — bundle20 preservation audit: Isabelle comparison

(Log written incrementally by subagent `audit-isabelle`. READ-ONLY w.r.t. the repo except this file.)

## Task

Compare the upstream Isabelle Wasm 2.0 type-safety development (branch `isabelle-mech-backend` @ `41e27cc54`,
directory `spectec/isabelle_type_safety_proof`, downloaded to the session scratchpad `isabelle/*.thy`) with the
Lean port (`TypePreservation.lean`, `TypePreservationPure.lean`, `wasm2.0.lean`, ...) and, where useful, Rocq
(`spectec/test-rocq/theories/type_preservation.v`): (1) equivalence of Isabelle `preservation` vs Lean
`t_preservation` and of the generated soundness relations; (2) proof-decomposition map; (3) every `sorry` in
Preservation.thy and its imports, and whether Lean proves the corresponding fact; (4) hypothesis differences;
(5) model differences (with_mem/slices, rat_to_nat/page arithmetic, store val bounds, the 2^32 corner case);
(6) progress-phase intelligence (Isabelle `progress` vs Rocq `t_progress`, helpers, sorries, porting insights).

## Safety check — START (verbatim)

### First run (13:27:54 local) — FALSE POSITIVE, diagnosed

```
safety check [audit-isabelle] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
grep: spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt: binary file matches
DIFFERENCE FOUND (lines outside spectec/src/test-lean-claude differ from baseline):
grep: spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt: binary file matches
1,256d0
< --- git status (porcelain) ---
<  M spectec/test-lean/todaywasm2.0.lean
<  D spectec/test-lean/todaywasm3.0.lean
< ?? Irreducible.lean
... (all 256 baseline lines shown as deleted, NOTHING added; full output elided for length)
< spectec/zy_sandbox.v
```

Diagnosis (read-only, before doing anything else; I had made zero modifications at that point):
- The diff is `1,256d0`: every baseline line "deleted", nothing added, i.e. grep produced NO output for the new
  file because it classified it as binary ("binary file matches").
- Afterwards the same file is plain ASCII: `file` says `ASCII text`, it has 0 NUL bytes and no byte >= 0x80.
- Two check files were written one second apart (`check-20261005T052753Z.txt`, `...052754Z.txt`) by parallel
  subagents. `check.sh` names its output by a 1-second timestamp and writes it with `> "$OUT"`; when two agents
  run in the same second they truncate/write the SAME file concurrently, which can leave a transient hole
  (reads as NUL bytes) that grep sees as binary. Also, `verify_against_baseline.sh` picks `NEW` with
  `ls -t ... | head -1`, which may be another agent's file.
- Re-running the script's own comparison (read-only) against every completed bundle20 check file
  (`052302Z`, `052315Z`, `052753Z`, `052754Z`) printed NO difference for any; and the LIVE
  `git status --porcelain` lines outside the target dir are identical to the baseline's.
- Conclusion: tooling race, not a real out-of-target change. Since my task is read-only, I re-ran the official
  check (below, clean) and continued, flagging this here and in my structured result.

### Second run (13:29:13 local) — official, clean

```
safety check [audit-isabelle] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052913Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## What I read (filled in as I go)

(First wave was killed by the account usage limit before anything below the safety check was logged.)

## Resumed (v2 relaunch)

Read brief `audit_brief_v2.md` and tasks `task2_isabelle.md` / `task_isabelle.md` in full; read this partial log first.

### Safety check — START of v2 (verbatim)

```
safety check [audit-isabelle] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T105050.478255929Z-audit-isabelle-1403015.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

### Progress notes (v2)

Reused first-wave scratch outputs in `scratchpad/agents/audit-isabelle/` (comment-depth sorry scan per .thy;
length-premise scripts). Re-ran the scripts (read-only):

- Isabelle model: 262 `list_all2` premises in inductive rules, **0** without an explicit `length = length` premise.
- Lean `wasm2.0.lean`: 274 `Forall₂` premise lines; 13 flagged without an adjacent length equality, all checked by hand:
  `wf_instr`/`wf_admininstr` case 57 (length implied by `(Inn_opt = none) ↔ (sz_opt = none)` on `Option.toList`),
  `Module_ok` (has `(List.length import_lst) = (List.length ixt_lst)`, parse miss), `Step_read.vload_shape_val`
  l.14580 (has `v_N = (List.length j_lst)`, first list is `List.range v_N`), and 9 in `fun_instantiate` (module
  instantiation, off the preservation path). `Forall₃` (129 lines): every premise has length equalities; the 16
  unparsed hits are proof lines (`iswf_Forall₃_eq_of_func`, ~l.7605-7665).
- Conclusion for item 1 (definitions): `Config_ok`, `State_ok`, `Frame_ok`, `Store_ok`, `Moduleinst_ok`,
  `Instr_ok2`/`Instrs_ok2`/`Expr_ok2`, `*inst_ok`, `Extend_*` are rule-for-rule the same in Isabelle
  (isabelle_reference_output_wasm2.thy l.13511-13895) and Lean (wasm2.0.lean l.15547-16335), and every zip-based
  `Forall₂` premise in them sits next to an explicit generator-emitted length equality, so they mean the same as
  Isabelle's length-strict `list_all2`.

- Top-level statements: Isabelle `theorem preservation` (Preservation.thy:5940-5943: `Config_ok cfg ts ⟹ Step cfg cfg' ⟹
  Config_ok cfg' ts`) vs Lean `t_preservation` (TypePreservation.lean:2699: `Step c1 c2 → Config_ok c1 ts →
  Config_ok c2 ts`): same quantifiers (all-universal, fixed `ts : resulttype`), same hypotheses (argument order
  swapped only), and `Config_ok`/`State_ok`/`Frame_ok`/`wf_config`/`wf_state`/`wf_store`/`wf_frame` identical rule-for-rule.
- Isabelle `t_inst_match` (Context_Store_Agreement.thy:5) = Lean `inst_match` (TypingLemmas.lean:1886): same 7 fields.
- `Extend_store`: Isabelle `holds_upto P n ≡ ∀i<n. P i` (model l.84) vs Lean `Forall P (List.range n)`: equivalent.
- Sorries read so far: Preservation.thy l.11 (step_wf), 769/774 (Limits_sub refl/trans; Lean proves
  `limits_sub_refl`/`limits_sub_trans` ExtensionLemmas.lean:350/363), 4408 (table_init_succ wf of `CONST I32 (i+1)`),
  4619/4627/4659/4842 (load/vload wf), 5197 (memory_fill_succ: `i'+1 ≤ 2^32-1` — SAME 2^32 corner case, Isabelle comment
  "check if Limits_ok needs a ≤ instead of <"), 5294-5310 (memory.copy/init cases, "see memory_fill cases"),
  5989 (Store_ok s' / Extend_store / Moduleinst_ok s' — "should come from A's proof"). Properties.thy 387-444: 20 of 23
  Step cases of `reduce_store_extension` (unused anywhere). store_extension_typing.thy 220 (`store_extension_typing`),
  241 (inside `store_extension_Funcinst_ok`), 321 (`store_extension_Moduleinst_ok`).

- Item 5 (model differences), verified:
  - Slices: Isabelle `list_slice l i n` (model l.46) = `take n (drop i l)` = Lean `List.take n (List.drop i l)`.
    Slice update: Isabelle `with_mem` (l.11218) uses `list_slice_update BYTES i j b*` (l.66), clamped but with clause
    `list_slice_update (x # l) _ 0 _ = []` (drops the tail if `|b*| > j`); Rocq `list_slice_update` (wasm.v:66) returns
    the rest at `j = 0`; Lean `with_mem` (wasm2.0.lean:12392) = `splice BYTES b* i`, ignores `j`, always length-preserving.
    All agree in bounds with `|b*| = j`. Store `*_val` rules carry no in-bounds premise in ANY model (Isabelle l.12943,
    Rocq wasm.v:16403, Lean l.14747) — known & documented (NOTES.md:146-155), fixed by the user's clamped splice.
  - Division: Isabelle `nat div 8`; Lean `rat_to_nat ((x:Rat)/8)` with `rat_to_nat r = (r.num.tdiv r.den).toNat`
    (wasm2.0.lean:9) = floor on non-negatives, so identical on every use. `growmemory`: Isabelle
    `|b| div (64*Ki) + n` (nat), Lean `(|b|:Rat)/(64*Ki) + n` then `rat_to_nat`; identical under Meminst_ok
    (`|b| = n*64Ki`). Limits bounds: `Memtype_ok` k = 2^16, `Tabletype_ok` k = 2^32-1 in both.
  - 2^32 corner case: Isabelle hits it independently at Preservation.thy:5197 (memory_fill_succ: needs
    `i'+1 ≤ 2^32-1` from `i'+v_n ≤ v_len*64Ki`, `v_len ≤ 2^16`, `v_n ≠ 0`; comment "check if Limits_ok needs a ≤ instead
    of <"), and memory.copy/init cases 5294-5310 are `sorry (* see memory_fill cases *)`.
  - Isabelle `step_wf` (l.8-11, sorry) has NO Store_ok premise and is false as stated: `Step_read__table_size`
    pushes `CONST I32 (mk_uN |REFS|)` while `wf_tableinst` (model l.10327) does not bound `|REFS|`. Lean's
    `Step_is_wf`/`Step_read_is_wf` carry `Store_ok (fun_store z)` (as Rocq's hand edit) — needed.

## What I read (v2)

- Isabelle (scratchpad `isabelle/`): Preservation.thy l.1-13, 88-108, 739-782, 965-985, 991-996, 3011, 4396-4410,
  4610-4660, 4838-4843, 5170-5200, 5286-5312, 5936-6073; Properties.thy l.372-456; store_extension_typing.thy
  l.205-245, 300-322; Context_Store_Agreement.thy l.5-31; Progress.thy l.1-147, 286-294, 924-950, 999-1065,
  1116-1175, 1822-1828, 2440-2466, 3115-3394 (skimmed), 3394-4007 (grep-skimmed); model
  isabelle_reference_output_wasm2.thy l.40-108, 640-645, 10327-10445, 10899-10906, 11218-11231, 11307-11318,
  11379-11410, 11444-11456, 12512-12516, 12610-12670 (table_size), 12730-12737, 12885-12889, 12909-12915,
  12937-12950, 13511-13895, 14067. Lemma-name inventories of all .thy files (comment-stripped).
- Lean: wasm2.0.lean l.1-26, 56, 2159-2175, 11511-11560, 11964-11968, 12392-12400, 12557-12570, 14411 ff (selected
  rules), 14580-14592, 14699-14722, 14741-14750, 15355-15420, 15452-15485, 15547-15782, 15992-16050, 16175-16335;
  TypePreservation.lean l.216-236, 536-542, 1600-1625, 2020-2040, 2670-2720; ExtensionLemmas.lean l.345-368,
  1128-1141, 1724-1730, 1753-1756, 1823-1826, 1842-1845; TypingLemmas.lean l.1886-1896; HelperLemmas.lean l.728-738.
- Rocq: type_progress.v l.92-94, 590-608, 1485-1492, 3086-3100, 4300-4320, 5196-5210, 5515-5552, 6064-6140;
  extension_lemmas.v l.2580-2584; wasm.v l.66-72, 16403-16408, 17155-17185; axioms.v (axiom names).
- Spec: specification/wasm-2.0/B-soundness.spectec l.200-232. Project NOTES.md l.140-160.

## Method

Signatures only (proof bodies opened only to locate `sorry`s and the case they sit in). Live/commented `sorry`s
from the first-wave nested-comment-aware scan (re-checked by reading each site). Length-premise coverage by script
(re-run) plus manual check of every flagged rule. Each claim below was checked against source.

## Findings

F1 [major, NEW] `Moduleinst_ok` has a hoisted premise `List.length (GLOBAL-addrs ++ MEM-addrs ++ TABLE-addrs ++
FUNC-addrs) > 0` (wasm2.0.lean:15690; Isabelle model in the `mk_Moduleinst_ok` rule after l.13615; Rocq wasm.v:17174
`>? 0`), which the spec does not state (B-soundness.spectec:230 is only
`-- (if exportinst.ADDR <- (GLOBAL globaladdr)* (MEM memaddr)* (TABLE tableaddr)* (FUNC funcaddr)*)*`, i.e.
per-export membership, vacuous when there are no exports). `fun_invoke` (wasm2.0.lean:15452-15485) builds the
initial frame with the EMPTY module instance, so `Moduleinst_ok s {} C`, hence `Frame_ok`/`State_ok`/`Config_ok`,
can never hold for an invocation configuration: `t_preservation` (and a future progress theorem) never apply to
the configuration `$invoke` produces. Shared by all three backends (an IL/backend rendering artifact of `<-`),
so NOT a Lean porting deviation; not mentioned anywhere in claude-logging. Does not make preservation false or
vacuous (configs whose module has >=1 global/mem/table/func are fine), but narrows end-to-end coverage.

F2 [info, known-documented] The 2^32 corner case is independently hit by Isabelle: Preservation.thy:5197
(`memory_fill_succ`, `sorry (* by force *) (* check if Limits_ok needs a ≤ instead of < *)` for
`i' + 1 ≤ 2^32 - 1`), memory.copy/init at 5294-5310 deferred to it. Corroborates the Lean `Step_read_is_wf` note.

F3 [info, new] Isabelle `step_wf` (Preservation.thy:8-11) and model `Step_read_is_wf` (l.12885) have no
`Store_ok` premise and are false as stated: `Step_read__table_size` pushes `CONST I32 (mk_uN |REFS|)` and
`wf_tableinst` (l.10327) does not bound `|REFS|`. Confirms Lean/Rocq need the hand-added `Store_ok (fun_store z)`.

F4 [info, known-documented] zip-based `Forall₂` vs length-strict `list_all2`: every `Forall₂`/`Forall₃` premise
in the soundness relations and Step rules sits next to a generator-emitted length equality (scripted check + manual
review; see progress notes), so Config_ok/State_ok/Frame_ok/Store_ok/Moduleinst_ok/Instr(s)_ok2/Expr_ok2/Result_ok
mean exactly what Isabelle's do. `Vals_ok` in `t_read_preservation`/`t_preservation_type` = Isabelle's
`list_all2 (λt v. Val_ok s v t) (context_LOCALS C') (LOCALS f)` exactly.

F5 [minor, new] `fun_instantiate` (wasm2.0.lean:15355 ff, e.g. l.15370/15410/15411) uses
`Forall₂ … (List.range n_D) var_4_lst` (and var_3/7/8/9/10 analogues over n_E/n_D) with no
`List.length var_k_lst = n_D/n_E`; Isabelle's `list_all2` and Rocq's `Forall2` force it. Off the preservation
and progress paths (module instantiation only).

F6 [info, new] Hypothesis differences (no Lean problem): Lean `t_preservation_type` has an extra `wf_config`
premise vs Isabelle `e_preservation` (same as Rocq; discharged from `Config_ok`). Lean `Extend_store_ais`
(ExtensionLemmas.lean:1842) carries Rocq's two `Store_ok` premises, unused in its proof (`intro hext _ _ h`);
Isabelle `store_extension_typing` has none. Isabelle `reduce_store_extension` (Properties.thy:372) is
over-restricted (Moduleinst_ok on `append_res_context ⟨LOCALS = map typeofval (LOCALS f), LABELS = lbl,
RETURN = rtn⟩ C` forces empty locals/labels/return), unused, 20/23 cases sorry; Lean `store_extension_reduce`
has Rocq's general form and is proved.

F7 [info, known-documented] Slice update: Isabelle `list_slice_update` (model l.66) returns `[]` on clause
`(x # l) _ 0 _` (truncates memory if `|b*| > j`); Rocq's returns the rest; Lean `with_mem` uses clamped
`splice` and ignores `j`. All three agree in bounds with `|b*| = j`; Lean's is length-preserving unconditionally,
which is what makes the 4 store-`val` cases (no in-bounds premise in any model) preservation-safe (NOTES.md:146-155).

## Item 1 — statement equivalence (summary)

Isabelle `preservation` (Preservation.thy:5940) `Config_ok cfg ts ⟹ Step cfg cfg' ⟹ Config_ok cfg' ts` ≡ Lean
`t_preservation` (TypePreservation.lean:2699) `Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts`: same universal
quantification, same fixed `ts : resulttype`, identical `Config_ok`/`State_ok`/`Frame_ok`/`Store_ok`/`Instrs_ok2`/
`Expr_ok2`/`Moduleinst_ok`/`wf_*` rules (see progress notes and F4). Lean adds the needed length premises
everywhere Isabelle relies on `list_all2` (the generator emits them in both; Lean's lemma-level `hlen`/`Vals_ok`
are the documented extras). `e_preservation` (969) vs `t_preservation_type` (2679): same hypotheses except Lean's
extra `wf_config` (= Rocq) and `Vals_ok` ≡ Isabelle's length-strict `list_all2`.

## Item 2 — proof decomposition map

| Isabelle | Lean |
|---|---|
| `preservation` Preservation.thy:5940 | `t_preservation` TypePreservation.lean:2699 |
| `e_preservation` :969 (one `Step.induct` l.991, nested `Step_pure.induct` l.996, `Step_read.induct` l.3011) | `t_preservation_type` :2679 / `t_preservation_type_aux`, dispatching to `t_pure_preservation` TypePreservationPure.lean:1858 and `t_read_preservation` :2028 |
| `e_preservation_locals` :90 (|LOCALS| kept, MODULE kept, locals typed in s') | `t_preservation_vs_type` :227 (+ `t_preservation_vs_type'` :216, `Extend_store_vals` ExtensionLemmas:1138), `reduce_inst_unchanged` :536; length inside `Vals_ok` |
| `step_wf` :8 (sorry) | `Step_is_wf` wasm2.0.lean:16045 (proved, +Store_ok), `Step_read_is_wf` :16034 (sorry), `Step_pure_is_wf` (proved) |
| sorry :5989 (Store_ok s', Extend_store, Moduleinst_ok s') | `store_extension_reduce` :1611 + `Extend_store_moduleinst` EL:1724 (Rocq `step_moduleinst` composition) |
| `reduce_store_extension` Properties.thy:372 (20/23 sorry, unused) | `store_extension_reduce` (all 23 cases proved) |
| `*_extension_refl`/`store_extension_refl` Properties.thy:7-74 | `Extend_store_refl` EL:1018 |
| `store_extension_wf` set.thy:7 | `Extend_store_wf_store'` EL:1094 |
| `store_extension_externaddrok_func`, `_refok`, `_valok` :148/180/199 | `Extend_store_externaddr(s_func)` EL:1600/1812, `Extend_store_ref` :1099, `Extend_store_val` :1128 |
| `store_extension_typing` :216 (sorry) | `Extend_store_ais` EL:1842 |
| `store_extension_{Funcinst,Globalinst,Tableinst,Meminst,Eleminst,Datainst,Moduleinst}_ok` | `Extend_store_{funcinst,globalinst,tableinst,meminst,eleminst,datainst_ext,moduleinst}` EL:1753/1767/1781/1795/1635/1665/1724 |
| (Frame variant commented out) | `Extend_store_frame` EL:1823 |
| `t_inst_match`(+`_refl`,`_is`) Context_Store_Agreement.thy:5-31 | `inst_match` TypingLemmas:1886, `construct_inst_match_*` :1893 ff |
| `Limits_sub_refl/_trans` :766/772 (sorry) | `limits_sub_refl/_trans` EL:350/363 |
| Type_Inversion.thy (30: `inv_one_admininstr`, `inv_plain`, `inv_label`, `inv_frame`, `inv_call_addr`, `inv_ref`, `inv_seq`, `inv_const_list`, `inv_expr`, `Val_ok_sub`, ...) | TypingLemmas `instr_typing_inversion` :467, `ai_typing_inversion` :711, `ais_seq_typing_inversion` :1244, `ais_composition_typing` :1254, `ais_single_*_typing_inversion` :1344-1386, `ais_vals_typing_inversion` :1788, per-op `ais_*_typing_inversion` TPP:1274 ff |
| Typing_Simplified.thy / Subtyping_*.thy | TypingLemmas `construct_ais_*`, wf-extraction lemmas; Subtyping.lean (`ResulttypeSub`, `construct_ais_subtyping` TL:1509) |

## Item 3 — sorry inventory (live only)

Preservation.thy (15): l.11 `step_wf` → Lean `Step_is_wf` proved (needs Store_ok; Isabelle's form is false, F3)
but through `Step_read_is_wf` (sorry, known). l.769/774 `Limits_sub_refl/_trans` → proved in Lean. l.4408
table_init_succ `wf_instr (CONST I32 (i+1))` → covered by `Step_read_is_wf` (true here given Store_ok:
Eleminst_ok `|refs| < 2^32`, Tabletype_ok `n ≤ 2^32-1`). l.4619/4627/4659/4842 load_num_val/load_pack_val/
vload_val/vload_lane_val wf of loaded value → typing proved in `t_read_preservation`; wf via `Step_read_is_wf`
(+ numeric opaque `*_is_wf`; `load_num_val` carries `wf_num_ nt c` in both models). l.5197 memory_fill_succ
(2^32 corner, FALSE there) → `Step_read_is_wf` (same documented corner). l.5294/5297/5300 memory_copy_zero/le/gt and
5307/5310 memory_init_zero/succ (whole cases) → typing proved in Lean; wf via `Step_read_is_wf`. l.5989 → proved
(`store_extension_reduce`, `Extend_store_moduleinst`).
Properties.thy (20): all in unused `reduce_store_extension` (local_set, table_set ×2, table_grow ×2, elem_drop,
store_num ×2, store_pack ×2, vstore ×2, vstore_lane ×2, memory_grow ×2, data_drop, ctxt_label/frame/instrs) →
Lean `store_extension_reduce` proves all.
store_extension_typing.thy (3): l.220, 241, 321 → `Extend_store_ais`, `Extend_store_funcinst`,
`Extend_store_moduleinst`, all proved. Context_Store_Agreement/Type_Inversion/Typing_Simplified/Subtyping*: none
live (7 commented out).
Generated model: 140 `*_is_wf`, all sorry (numeric/vector operator results ~95; byte/bit conversions; store/frame
projections and `with_*` updates; growtable/growmemory; `Step_pure_is_wf`; `Step_read_is_wf`; alloc*/invoke).
Lean: 152 `*_is_wf` theorems; only the 33 listed in the brief remain sorry on the preservation path.

## Item 6 — progress intelligence

- Statements: Isabelle `progress` (Progress.thy:1116) `Config_ok (mk_config s es) ts ⟹ ∃cfg'. Step (mk_config s es)
  cfg' ∨ es = [TRAP] ∨ (∃vs. es = map admininstr_val vs)`; Rocq `t_progress` (type_progress.v:6064)
  `Config_ok … ts -> terminal_form es \/ exists s' f' es', Step …` with `terminal_form es := const_list es \/ es =
  [TRAP]`. Equivalent. Rocq: `t_progress` Qed (6094), `t_progress_e` Qed (6062), `t_progress_be` Admitted (5512).
- Isabelle structure: `State_ok_strip` (l.27) ⇒ top context = `strip C` (no labels/return); `typecheck_strip_not_return`
  (l.92, via `br_type_not_strip`/`return_type_not_strip` l.48/70) ⇒ `not_br_return es` — the SAME top-level syntactic
  predicate as Rocq's `not_lf_br`/`not_lf_return` (type_progress.v:599/604); mutual induction
  `Instr_ok2_Instrs_ok2_Expr_ok2.inducts(3)` with motives over an arbitrary typed value prefix `vs`
  (`list_all2 Valtype_sub (map typeofval vs) t1`, `list_all wf_val vs`) plus State_ok/strip/not_br_return/wf; plain
  case by contradiction with nested `Instr_ok_Instrs_ok.inducts(1)`; label case (l.3115) splits on
  `not_br_return body` (IH + `ctxt_label`/`label_vals`, else `br_zero` with `Resulttype_sub_length`+`list_splitable`,
  `br_succ`, `return_label`); frame case (l.3394) likewise (`frame_vals`, `return_frame`; BR impossible); seq case
  (l.3860) with `br_return_contaminate_left/right` (l.98/123), `reducible_right` (l.944), `trap_vals`,
  `reducible_left_v` (l.924). Helpers: `fun_*_total` (l.165-632), `typeofval_is_nt/_i32/_rt` (l.999-1062),
  `default_not_bot` (151).
- Isabelle sorries (33): l.291 `truncz_spec` (`truncz x = x`; Isabelle's truncz is `nat ⇒ nat`, model l.2499;
  analogue of Rocq/Lean `truncz_quot`); l.1826 cvtop; l.1920-1974 all 19 vector cases; l.2460 memory_size
  `0 < length memtype_lst` (proof gap); l.2817-2847 all 11 load/store/vload/vstore cases. Label/frame cases use
  `step_wf` (sorry) 5×.
- Porting insights: (a) Lean `Step.ctxt_label/ctxt_frame/ctxt_instrs` (wasm2.0.lean:14706/14711/14716) need
  `wf_config` of inner pre AND post config ⇒ progress will need `Step_is_wf` (Store_ok available from Config_ok) and
  hence inherit the `Step_read_is_wf` sorry. (b) Two genuinely FALSE progress cases in Rocq (mechanised
  counterexamples): VLOAD `SHAPE 64 X 1` (`vload_shape64_stuck` 6107) and VCVTOP `I16X8←F32X4 TRUNC_SAT ZERO`
  (`vcvtop_trunc_sat_i16_stuck` 6132); Isabelle never reaches them. (c) Rocq axioms.v has 22 axioms, Lean 11;
  missing in Lean: ibits_inv, feq/fne/flt/fgt/fle/fge_bit, ishl_wf, ishr_wf, trunc_sat_total, demote_nonempty,
  promote_nonempty (used by Rocq progress). (d) Lean has no `typeof : val → valtype` (Rocq type_progress.v:262;
  Isabelle `typeofval` is generated from an Isabelle-only aux spec). (e) F1: neither theorem applies to
  `fun_invoke` configurations. (f) Mirror Rocq (equality `map typeof vcs = ts1` + `Admin_instrs_ok_ind'`); Isabelle's
  subtype-generalised prefix is an alternative that absorbs `Instrs_ok2__sub` directly.

## Unsure / caveats

- F1's origin (which IL pass hoists the `> 0` out of the per-export iteration) was not traced in the SpecTec
  sources; only its presence in all three generated models and its absence from B-soundness.spectec:230 were checked.
- Lean names for Isabelle's `blocktype_ok_agree`/`context_*_agree` were not matched 1:1 (handled via `inst_match`).
- Isabelle `step_wf` falsity (F3) is argued from the rules (no machine check; no Isabelle/Lean was run).
- Scratch files (outside the repo): `scratchpad/agents/audit-isabelle/` (`len3.py`, `isa_model_sorry_names.txt`,
  first-wave `len_check*.py`, `comment_depth.py`, `cd_*.txt`).

## Safety check — END of v2 (verbatim)

```
safety check [audit-isabelle] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T110613.091248193Z-audit-isabelle-1410267.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

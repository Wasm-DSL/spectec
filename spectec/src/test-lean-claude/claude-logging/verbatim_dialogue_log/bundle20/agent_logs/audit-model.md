# audit-model — bundle20 preservation audit (v2 relaunch), generated-model audit

## Task

Subagent `audit-model` (v2 relaunch, merging the first-wave tasks `audit-model-runtime` and
`audit-model-step`). Read-only audit comparing the backend-generated Lean model
`spectec/src/test-lean-claude/wasm2.0.lean` against the Rocq backend's generated model
`spectec/test-rocq/theories/wasm.v` for everything the meaning of
`TLC.t_preservation : Step c1 c2 -> Config_ok c1 ts -> Config_ok c2 ts` depends on:
`Forall`/`Forall₂`/`Forall₃`, runtime typing (`Config_ok`, `State_ok`, `Frame_ok`, `Store_ok`,
`Moduleinst_ok`, the `*inst_ok`, `Externaddr_ok`, `Val_ok`, `Ref_ok`), `Extend_store` + all
`Extend_*`, the `wf_*` premises, the project's `Vals_ok`, admin typing `Instr_ok2`/`Instrs_ok2`/
`Expr_ok2`, validation `Instr_ok`/`Instrs_ok`/`Expr_ok` (name lists), reduction
`Step_pure`/`Step_read`/`Step`, backend-sensitive helpers (`with_mem`, `splice`, `rat_to_nat`,
`l[i]!`, opaque functions), the hand-edited `Step_read_is_wf`/`Step_is_wf`, and the top-level
statement vs Rocq and Isabelle. Key question: does any Lean definition admit configurations Rocq
rejects (zip-based `Forall₂`/`Forall₃` without a length premise) or reject ones Rocq accepts, in a
way that changes what `t_preservation` means. No Lean was run; files were only read.

## Safety check — START (verbatim)

```
safety check [audit-model] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T105044.711769660Z-audit-model-1402775.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Resumed (v2 relaunch)

First-wave partial logs `agent_logs/audit-model-runtime.md` and `agent_logs/audit-model-step.md`
were read first: both contain only the task paragraph, a START safety check, and "read the brief" —
no findings. Work therefore restarts from scratch here.

## Progress notes (written incrementally)

- Read `scratchpad/briefs/audit_brief_v2.md` (1-169), `task2_model.md` (1-14),
  `task_model_runtime.md` (1-38), `task_model_instr_step.md` (1-31).
- Read `scratchpad/sigs/model_runtime.md` fully (1-1591): Forall/Forall₂/Forall₃, splice,
  rat_to_nat, Config_ok, State_ok, Frame_ok, Store_ok, Moduleinst_ok, Funcinst_ok, Globalinst_ok,
  Tableinst_ok, Meminst_ok, Eleminst_ok, Datainst_ok, Exportinst_ok, Externaddr_ok, Val_ok, Ref_ok,
  Extend_store + 6 Extend_*, wf_config/state/store/frame/moduleinst/context, Step_read_is_wf,
  Step_is_wf, Step_pure_is_wf.
  Preliminary: every `Forall₂` in Frame_ok / Store_ok (6) / Moduleinst_ok (6) is preceded by an
  explicit generated `List.length _ = List.length _` premise (Rocq has the same `(|..|) == (|..|)`
  premise in addition to its inductive Forall2). Config_ok/State_ok/Val_ok/Ref_ok/Externaddr_ok/
  *inst_ok/Extend_* match constructor-by-constructor. Extend_store: Lean `Forall P (List.range n)`
  vs Rocq `holds_upto P n` (to check). Step_read_is_wf/Step_is_wf statements identical to Rocq.
- Read `scratchpad/sigs/model_step.md` fully (1-1874): Instr_ok2/Instrs_ok2/Expr_ok2 (identical
  constructor-by-constructor: plain/label/frame/call_addr/ref/trap; empty/instr/seq/sub/frame;
  mk_Expr_ok2), Step_pure (Lean 63 ctors = Rocq), Step_read (47), Step (23), with_mem/
  with_meminst/with_table/with_tableinst/with_global/with_local/with_elem/with_data,
  fun_growtable, fun_growmemory, Rocq list_slice_update.
  Systematic backend differences to verify in wasm.v: `holds_upto` vs `Forall _ (List.range n)`;
  `List_Foralli` vs `Forall₂ _ (List.range n) l` (vload_shape_val); `list_slice` vs
  `List.take j (List.drop i l)`; `list_update_func` vs `List.modify`; `mkseqN` vs
  `List.range n |>.map`; `list_repeat` vs `List.replicate`; `lookup_total` vs `[i]!`; Rocq Q->N
  coercion vs `rat_to_nat`; Lean `with_mem` ignores its length argument `nat_0` (clamped splice).
- Rocq helpers (wasm.v 1-206) read: `lookup_total l n = seq.nth default_val l n`; `list_repeat`;
  `list_update_func` (out-of-range = no-op, same as `List.modify`); `list_slice l i j` =
  take j (drop i l); `list_slice_update`; `List_Foralli f xs` = `Foralli_help f 0 xs` (indexed
  Forall); `mkseqN f n` = [f 0..f (n-1)]; `holds_upto P n := Forall P (iotaN 0 n)`; coercions
  Q->Z = `Qfloor`, Z->N = `Z.to_N`. All are equivalent to the Lean renderings
  (`Forall P (List.range n)`, `List.range n |>.map f`, `List.take j (List.drop i l)`,
  `rat_to_nat` = toNat of truncating division, which equals Z.to_N∘Qfloor for every sign).
- Script `scratchpad/agents/audit-model/scan2.py` (+ stricter pairwise variant): 404
  `Forall₂`/`Forall₃` uses inside generated inductive constructors; 391 have a premise
  relating the lengths of exactly the paired lists. The 13 others: `wf_instr`/`wf_admininstr`
  case 57 (STORE; `Option.toList Inn_opt`/`Option.toList sz_opt`, lengths forced equal by the
  generated premise `(Inn_opt = none) ↔ (sz_opt = none)`, also present in Rocq wasm.v:3548),
  `Module_ok` (has `|import_lst| = |ixt_lst|`; parser miss on a multi-line lambda; module
  validation, not on the preservation path), 10 in `fun_instantiate` (instantiation only; not
  reachable from Step/Config_ok).
- None of the 63 sorried theorems in wasm2.0.lean has `Forall₂`/`Forall₃` in its statement.
- Constructor lists (script): Instr_ok 73/73, Instrs_ok 5/5, Step_pure 54/54 (NOT 63 as the brief
  says), Step_read 47/47, Step 23/23, Instr_ok2 6/6, Instrs_ok2 5/5, Expr_ok2 1/1, identical names
  and order (Rocq prefixes reserved words: `res_if`, `res_return`, `res_seq`, and `Rel__` for
  clashes). Datatypes instr 68/68, admininstr 74/74, val 5/5, ref 3/3.
- Script `fpall.py`: premise fingerprint (premise count, Forall/Forall2/range/length/lookup/
  ≠none/wf_/</≤/>/≥/∨/∧ counts) for every constructor of all 346 inductives common to both files:
  only 5 differences, all explained by `holds_upto`→`Forall _ (List.range n)` / `List_Foralli`→
  `Forall₂ _ (List.range n) l` renderings (Step_pure vswizzle/vshuffle, Step_read vload_shape_val,
  Extend_store) or `fun_instantiate` (off-path). No Prop-valued relation differs in ctor count.
- Spot-checked full premises (identical): Instr_ok br_table, call_indirect, block, local_get,
  table_init; all Step/Step_read/Step_pure store/memory rules read side by side in model_step.md.
- Accessors `fun_store/frame/funcaddr/funcinst/type/global/table/mem/elem/data/local`,
  `fun_blocktype`, `default_`, `size`/`res_size`, `jsize`, `sizenn`, `isize`, `ine_`, `iadd_`,
  `sat_u_`, `canon_`, `E`, `fun_M`, `min`, `disjoint_`, context `Append` (Lean
  `Option.orElse` = Rocq left-biased `option_append`), `Resulttype_sub`: identical to Rocq.
  Match-arm comparison of 142 common `def`s: only single-arm-`match` vs direct-expression
  renderings (24, all spot-checked equal).
- 64 Lean `opaque` functions = exactly the 64 Rocq `Axiom`s (no function opaque in Lean but
  defined in Rocq). No `axiom`/`native_decide`/`implemented_by`/`extern`/`unsafe` in wasm2.0.lean.
  The 63 Lean sorries = Rocq's 62 admitted `*_is_wf` lemmas + `Step_read_is_wf`; Rocq's 64th
  `Admitted` (`res_list_eq_dec`, wasm.v:429-431) has no Lean counterpart (Lean derives DecidableEq).
- `List.contains` (Lean rendering of Rocq `\in`) on the path is over `num_`, `vec_`=`uN`, `lane_`,
  `externaddr`, `name`: all `deriving … LawfulBEq`, so `contains` ↔ `∈`. (13 types derive only
  `BEq`: instr, elemmode, datamode, func, global, elem, data, module, funcinst, store, state,
  admininstr, config — none is used with `List.contains`/`disjoint_` on the path.)
- Top-level: Lean `t_preservation (c1 ts c2) : Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts`
  (TypePreservation.lean:2699) = Rocq type_preservation.v:3412 = Isabelle Preservation.thy:5940
  (premises swapped). Isabelle's generated Config_ok/State_ok/Frame_ok have the same shape
  (`list_all2` plus explicit length premises).
- Rocq hand-edits in wasm.v: only the placement + `Store_ok (fun_store z)` premise of
  `Step_read_is_wf` (17351-17353 comment) / `Step_is_wf` (17701 comment); mirrored in Lean.
  The other comments are generator `FIXME - Non-trivial append` on record Append instances
  (memarg, exportinst, funcinst, …), not used by the soundness relations.
- Spec source checked (specification/wasm-2.0/B-soundness.spectec:198-230, 8-reduction.spectec
  534-579): see findings F1/F5.

## Findings

F1 (minor, model-vs-spec, NEW; common to Lean, Rocq and Isabelle; not a port deviation).
`Moduleinst_ok` carries a generated premise `List.length (globaladdrs ++ memaddrs ++ tableaddrs ++
funcaddrs) > 0` (wasm2.0.lean:15690; wasm.v:17174; Isabelle reference output, same rule). The
SpecTec source (B-soundness.spectec:230) only says `(if exportinst.ADDR <- (GLOBAL globaladdr)*
(MEM memaddr)* (TABLE tableaddr)* (FUNC funcaddr)*)*`, i.e. per-export membership; the non-emptiness
side condition was hoisted OUTSIDE the iteration over exports, so it applies even when
`exportinst_lst = []`. Effect: `Moduleinst_ok`, hence `Frame_ok`/`State_ok`/`Config_ok` (and
`Funcinst_ok`, `Instr_ok2.frame`), reject every module instance with no global, memory, table or
function addresses, which the spec accepts. Example: frame with MODULE := {TYPES=[],FUNCS=[],
GLOBALS=[],TABLES=[],MEMS=[],ELEMS=[0],DATAS=[],EXPORTS=[]} (a module that only has a passive
element segment, e.g. evaluating its `ref.null` element expression): `Config_ok` is false in all
three formalisations, but true in the spec. `t_preservation` therefore says nothing about such
configurations (a small narrowing of scope; it does not make the theorem vacuous: any module
instance with at least one address passes). Recommendation: report upstream as a SpecTec
middle-end issue (translation of `x <- xs` under an iteration); no Lean-side action needed for
Rocq correspondence.

F2 (info, model, known-documented). Lean `with_mem` (wasm2.0.lean:12391-12398) ignores its length
argument `nat_0`: `BYTES := splice (elem_1.BYTES) var_0_lst nat`, whereas Rocq `with_mem`
(wasm.v:14420-14424) uses `list_slice_update (BYTES var_1) i j b_lst`. Rocq writes min(j, |b|, |l|-i)
bytes, Lean writes min(|b|, |l|-i); they coincide whenever j ≥ |b*| (under the intended semantics
|nbytes_ nt c| = size/8 = j always). Both are length-preserving, and `Store_ok`/`Meminst_ok`/
`Extend_meminst` only constrain lengths, so `t_preservation`'s meaning is unaffected. Documented in
HelperLemmas.lean:439-445 (`splice_eq_list_slice_update`: equals `list_slice_update l i b.length b`)
and the bundle17 `with_mem_slice_update_issue.md`; user decision (bundle18).

F3 (info, model, known-documented). Zip-based `Forall₂`/`Forall₃`: of 404 uses inside generated
inductive constructors, 391 have a generated premise equating the lengths of exactly the paired
lists (identical premise also present in Rocq next to its inductive Forall2: Frame_ok, Store_ok ×6,
Moduleinst_ok ×6, Resulttype_sub, Step_pure vshiftop/vbitmask, Step_read vload_shape_val, …). The
13 others: `wf_instr`/`wf_admininstr` case 57 (wasm2.0.lean:2162-2163, 11912-11913: lengths of the
two `Option.toList` forced equal by the generated `(Inn_opt = none) ↔ (sz_opt = none)`, also in
wasm.v:3548), `Module_ok` (has its length premise; parser miss) and 10 in `fun_instantiate`
(instantiation only, not reachable from `Step`/`Config_ok`). No sorried statement mentions
`Forall₂`/`Forall₃`. `Vals_ok` (TypingLemmas.lean:1775) bakes in the length, documented in its doc
comment. Conclusion: no Lean definition on the preservation path admits a configuration that Rocq
rejects (or vice versa) because of zip-based `Forall₂`.

F4 (info, model, NEW-confirmation). Generated relations correspond 1:1: constructor names/order
identical for Instr_ok (73), Instrs_ok (5), Expr_ok (1), Instr_ok2 (6), Instrs_ok2 (5), Expr_ok2 (1),
Step_pure (54), Step_read (47), Step (23) (Rocq prefixes only: `res_if`, `res_return`, `res_seq`,
`Rel__x`); premise fingerprints identical for every constructor of all 346 common inductives up to
the verified-equivalent renderings `holds_upto P n` ↔ `Forall P (List.range n)`, `List_Foralli` ↔
`Forall₂ _ (List.range n) l` + `n = |l|`, `mkseqN` ↔ `List.range n |>.map`, `list_slice` ↔
`take/drop`, `list_update_func` ↔ `List.modify`, `list_repeat` ↔ `List.replicate`, Q→N
(`Z.to_N ∘ Qfloor`) ↔ `rat_to_nat` (equal for all signs), `lookup_total`/`!` ↔ `[i]!`/`Option.get!`
(defaults only reached out of range; every rule lookup is guarded by a bound/`≠ none` premise or by
typing). `Step_read_is_wf`/`Step_is_wf` statements identical to Rocq's hand-edited ones.

F5 (info, model-vs-spec, NEW detail; common to all backends). `vstore_lane_oob` traps when
`i + OFFSET + v_N > |BYTES|` with N in BITS (wasm2.0.lean:14776, wasm.v:16432, spec
8-reduction.spectec:573 `$(i + ao.OFFSET + N)`), while `vload_lane-oob` (spec 536) and the `-val`
rule's width use N/8. Spec typo, faithfully transcribed; together with the already documented
(bundle17) absence of bounds premises on the four store `-val` rules it only adds nondeterminism
(TRAP is typable at any type; `with_mem` preserves lengths), so no effect on `t_preservation`.

F6 (info, doc, NEW). The brief's "already established" constructor count `Step_pure 63` is wrong:
both wasm2.0.lean (13744-13997) and wasm.v (15540-15793) have 54 `Step_pure` constructors
(`Step` 23 and `Step_read` 47 are right).

F7 (info, trust, confirmation). 64 Lean `opaque` = 64 Rocq `Axiom` (same names); sorry set =
Rocq Admitted set (+ Rocq-only admitted `res_list_eq_dec`); no trust-expanding constructs in
wasm2.0.lean.

Answers to the four runtime questions: (1) no weakening/strengthening vs Rocq on the path (F3/F4),
apart from F2 (no effect) — but all backends share the F1 over-strengthening vs the spec; (2) no
Lean-only unsatisfiable premise found (definitions are 1:1 with Rocq; a module instance with ≥1
address is needed because of F1); (3) Rocq's only definition hand-edit (Step_read_is_wf/Step_is_wf)
is mirrored; (4) top-level statements of Lean/Rocq/Isabelle are equivalent (fixed `ts`).

## Unsure / not checked
- Did not construct a concrete Lean `Config_ok` witness (non-vacuity is another agent's task).
- Did not compare Lean derived `Inhabited` defaults with Rocq `default_val` per record type
  (only reachable out of range; the Lean `*_is_wf` proofs that need wf defaults are complete).
- Datatype definitions compared only by constructor counts for instr/admininstr/val/ref.

## Safety check — END (verbatim)

```
safety check [audit-model] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T110323.296096552Z-audit-model-1409284.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written: only this log (inside the target dir). Scratch scripts (outside the repo):
`scratchpad/agents/audit-model/{scan_forall2.py,scan2.py,fp.py,fpall.py,forall2_scan.txt,scan2_out.txt}`.
No Lean was run; no git state was changed.

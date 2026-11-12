# digest-proveC1: digest of the bundle20 proof-batch logs prove-C01 .. prove-C13

Label: `digest-proveC1`. Read-only digest. Only writes: this file (and nothing in `/home/zhengyew/spectec`; no scratch files were needed, all
analysis was done with `python3 -I` one-liners reading files). No agents spawned, no lake, no git writes.

Source directory: `/home/zhengyew/spectec/spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle20/agent_logs/`
Files read completely (every line): `prove-C01.md` (215 lines), `prove-C02.md` (155), `prove-C03.md` (165), `prove-C04.md` (225),
`prove-C05.md` (206), `prove-C06.md` (189), `prove-C07.md` (195), `prove-C08.md` (220), `prove-C09.md` (259), `prove-C10.md` (246),
`prove-C11.md` (253), `prove-C12.md` (213), `prove-C13.md` (212).

Convention: "bundle20-era line" = line number in the bundle20-time `TypeProgress.lean` (the pre-merge file with `:= sorry` stubs; the logs' target lines run from ~1525 to ~2084) that the logs quote;
"now" = line in the CURRENT repo `TypeProgress.lean` (8044 lines) that I grepped. Everything marked "(my cross-check)" is NOT from the logs; it comes from
read-only greps/scripts I ran on the current repo (`wasm2.0.lean` = regenerated file, 14698 lines, modified Oct 15 12:34; `OLD_wasm2.0.lean` = the
bundle19/20 hand-edited file, 16351 lines) and is explicitly labelled as such.

## 0. Safety check (START), verbatim

Command: `bash /tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/verify.sh digest-proveC1-start`

```
safety check [digest-proveC1-start] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T051157.047196638Z-digest-proveC1-start-458202.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
```

## Executive summary

- The 13 logs cover 53 `t_progress_be_<rule>` lemmas (C01-C13: nop .. table_fill). 52 are fully proved; `t_progress_be_vcvtop` (C12) has ONE documented `sorry` (F32->I16 TRUNC_SAT subcase, Rocq `admit` type_progress.v:4319). Merged verbatim into TypeProgress.lean (my check: 53/53 identical).
- Upstream (1) removes that sorry: delete `cases Hti : vcvtop_trunc_sat_i16 op`, keep the `false` branch, drop every `Hti` argument (helpers `vcvtop_step_half/zero/full`, `vcvtop_zero_numtype`, `vcvtop_full_lsize`). Nothing in C01-C13 touches vload (upstream (2)) or the memory.* succ rules (upstream (4)); table.* rules are unchanged in the regenerated file.
- Upstream (3) hits exactly one proof: C08 `t_progress_be_vshiftop` (shift amount becomes `uN.mk_uN (k % lsizenn (lanetype_Jnn J))` in 4 witness places; the 8 constructors `fun_vshiftop_.fun_vshiftop__case_0..7` are the only referenced generated constructors whose statement changed).
- `Step_is_wf` is used by 4 proofs (unreachable, if, call, call_indirect; 5 call sites) and reaches `sorryAx`; proving `Step_read_is_wf` is not enough (my static closure: `Step_pure_is_wf` also reaches 29 sorry-bodied generated `*_is_wf`; for 8 of them I confirmed the underlying function is `opaque`, so they cannot be proved). Its signature in the regenerated file lost `Store_ok` and the explicit `z`/list args.
- The regenerated wasm2.0.lean lost every bundle19 hand edit that C01-C13 rely on: `iswf_Forall_nil/cons/getElem!`, `iswf_uN_zero` (C03), and the hand proofs of `testop__is_wf`, `relop__is_wf`, `ine__is_wf`, `iadd__is_wf`, `imul__is_wf`, `Step_pure_is_wf`, `Step_is_wf`. Still `sorry` even in OLD and used: `extend___is_wf`, `narrow___is_wf`, `lanes__is_wf`, `inv_ibits__is_wf`.
- Project axioms used (not sorry): `lanes_len` (C08 vbitmask, C09 vswizzle/vshuffle, C10 vextract_lane), `ibits_inv` (C08 vbitmask).
- Apart from those 8 `fun_vshiftop_` constructors, the other 78 generated constructors named in the proofs still exist with identical statements and numbering, and the 53 `Instr_ok` rule statements are unchanged, so the other proofs should re-elaborate as is once the hand-edit dependencies above are restored (I compiled nothing).

## 1. What the 13 files are

Each is the log of one bundle20 sub-agent that ported a batch of bullets of Rocq `t_progress_be` (`spectec/test-rocq/theories/type_progress.v`,
bullets at 3130-4511) into the Lean case lemmas `t_progress_be_<rule>` of `TypeProgress.lean`. Together: 53 lemmas (C01 6, C02 3, C03 2, C04 5, C05 6,
C06 5, C07 4, C08 3, C09 3, C10 3, C11 2, C12 6, C13 5). Result: 52 proved with no `sorry` in the proof text; 1 (`t_progress_be_vcvtop`, C12) proved
except for ONE documented `sorry` (the `Hti = true` / F32->I16 TRUNC_SAT subcase, Rocq `admit` at `type_progress.v:4319`).
No agent edited a repo file (each wrote only its log + `/tmp/claude-1000/.../scratchpad/agents/prove-Cxx/` scratch); the main thread merged the bodies.

(my cross-check) All 53 bodies in the CURRENT `TypeProgress.lean` are whitespace-normalised IDENTICAL to the code blocks in these logs (script comparison, 0 differences).
So the logs are an exact record of the merged proofs, and in the current working tree the merged proofs are still exactly those (no later edits).

### Result table (target -> bundle20-era line / now / Rocq `type_progress.v` lines)

| log | lemma (bundle20-era line -> now) | Rocq lines |
|---|---|---|
| C01 | nop (1525.. -> 3819), unreachable (3837), drop (3862), select_expl (3879), select_impl (3915), block (..1583 -> 3953) | 3130-3229 |
| C02 | loop (1588 -> 3993), if (1610 -> 4033), br (1642 -> 4102) | 3229-3344 |
| C03 | br_if (1651 -> 4115), br_table (1661 -> 4175) | 3344-3393, 3393-3449 |
| C04 | call (1674 -> 4238), call_indirect (4271), return (4321), const (4335), unop (4350) | 3449-3477, 3477-3516, 3516-3521, 3521-3526, 3526-3551 |
| C05 | binop (1726.. -> 4397), testop (4433), relop (4467), cvtop (4504), ref_null (4537), ref_func (..1780 -> 4550) | 3551-3672 |
| C06 | ref_is_null (1783 -> 4572), vconst (1792 -> 4618), vvunop (1800 -> 4631), vvbinop (1810 -> 4659), vvternop (1820 -> 4690) | 3672-3760 |
| C07 | vvtestop (1830 -> 4724), vunop (1840 -> 4756), vbinop (1850 -> 4790), vtestop (1860 -> 4826) | 3760-3851 |
| C08 | vrelop (1870 -> 4883), vshiftop (1880 -> 4917), vbitmask (1890 -> 5003) | 3852-3867, 3867-3917, 3917-3963 |
| C09 | vswizzle (1898 -> 5067), vshuffle (1907 -> 5156), vsplat (1918 -> 5234) | 3963-4068 |
| C10 | vextract_lane (1927 -> 5264), vreplace_lane (1938 -> 5366), vextunop (1948 -> 5398) | 4068-4111, 4112-4131, 4132-4179 |
| C11 | vextbinop (1958 -> 5472), vnarrow (1968 -> 5576) | 4180-4264, 4264-4301 |
| C12 | vcvtop (1978 -> 5629; sorry at 5656), local_get (5688), local_set (5708), local_tee (5732), global_get (5753), global_set (..2031 -> 5774) | 4301-4339 (admit 4319), 4340-4348, 4349-4358, 4359-4367, 4368-4376, 4377-4387 |
| C13 | table_get (2035 -> 5799), table_set (5833), table_size (5872), table_grow (5894), table_fill (..2084 -> 5926) | 4388-4407, 4408-4428, 4429-4447, 4448-4463, 4464-4510 |

`sorryAx`-free already at the time (no still-sorry dependency): drop, const, ref_null, vconst, local_get, local_set, local_tee, global_get, global_set,
table_size (and `br` in its alternative form, see C02). All others inherited `sorryAx` from then-still-`sorry` helper lemmas of `TypeProgress.lean`
(`map_eq_nil`, `wf_config_app`, `invert_typeof_*`, ... : these were other batches' targets) and/or from imported generated `wasm2.0.lean` wf theorems (below).

## 2. Standing instructions / refinements visible in these logs

- Safety order (every agent log starts and ends with it): never modify anything outside `spectec/src/test-lean-claude`; run the baseline check at START and END and
  paste the output into the log. Script used then: `cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" <label>`
  (baseline `claude-logging/safety-checks/check-20261005T051653Z.txt`); every START/END/post-log check printed `VERIFIED: zero new changes outside spectec/src/test-lean-claude`
  (13 agents; C06, C09, C11 added a third "after writing this log" check). Inside the dir the only file an agent wrote was its own log.
  Current-turn rule (stricter): write nothing inside the repo; use the scratchpad `verify.sh` with baseline `check-20261015T044132Z.txt`.
- Each sub-agent: no repo edit, no state-changing git, no agents spawned, no `lake build` (only `timeout 900 lake env lean <abs path>` from `spectec/src/test-lean-claude`),
  one Lean process per agent at a time (C10 also checked that no other batch Lean process was running; the START/END timestamps show 3-5 agents overlapped in time,
  e.g. C02 13:12:11-13:16:59, C03 13:12:42-13:18:55, C04 13:15:25-13:20:56 UTC on 2026-10-05).
- Porting rules: statement is fixed; each proof follows its Rocq bullet step by step (same `left`/`right`, witnesses, lemmas); Rocq's Ltac `invert_typeof_vcs` is NOT ported and is
  done inline; every deviation is documented as a "Lean-way" simplification; list "still-`sorry` earlier lemmas relied on" per target; no `sorry`/`admit`/`native_decide`/new axiom
  (the only `sorry` allowed is the documented known-false vcvtop subcase, mirroring Rocq's `admit`); still-`sorry` earlier lemmas MAY be used because "their statements are fixed" (C04).
- Ordering rule: because a body replaces `:= sorry` in place, it may only use declarations that appear earlier in `TypeProgress.lean` (or imports); TypeProgress.lean then declared no
  `@[simp]`/`attribute`/`set_option`/`open`/`variable`/`instance`, so a scratch file that imports it elaborates in the same context.
- Verification protocol used by every agent: (1) `Work.lean` = header of each target copied VERBATIM from TypeProgress.lean (renamed `<name>_proof`, `:= sorry` -> `:= by`) + proof +
  guard `example : type_of% @<name>_proof = type_of% @<name> := rfl`; (2) negative control (append `example : (1:Nat) = 2 := rfl`, must FAIL) to show the guard is live; (3) check that
  `TypeProgress.olean` is newer than `TypeProgress.lean` (20:18:19 vs 20:18:16) so the guard compares against current statements; (4) "merge simulation" `Head.lean` = real
  TypeProgress.lean up to the target with the proofs substituted, `lake env lean`, `#print axioms`, and no `declaration uses sorry` warning on the targets; (5) mechanical sorry-dependency
  attribution (C06 `Work_sorry.lean`, C07/C10 `Work_deps.lean` via `collectAxioms`, C11 `Expr.getUsedConstants`, C09 `Work_ax.lean` replacing the 7 sorry lemmas by identically-stated local axioms).

## 3. Per-file digest

### C01 (nop, unreachable, drop, select_expl, select_impl, block) - all proved
- Standard prologue of EVERY proof: `intro <binders>; unfold t_progress_be_P; intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret`, then `right`
  (or `left; rfl` for `const_list` goals), `simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf; obtain ⟨Htf1, _⟩ := Htf; rw [← Htf1] at Hts`.
- nop: `map_eq_nil typeof vcs Hts` (then-sorry) gives `vcs = []`; `Step.pure _ _ _ Step_pure.nop`.
- unreachable: split `vcs`; `nil` -> `Step.pure … Step_pure.unreachable` to `[TRAP]`; `cons vc' vcs'` -> witness `List.map admininstr_val (vc' :: vcs') ++ ([TRAP] ++ [])` via
  `Step.ctxt_instrs _ (vc' :: vcs') [UNREACHABLE] [] _ [TRAP] H (Or.inl (List.cons_ne_nil _ _)) HWf1 HWf2` with `HWf1 := ((wf_config_app _ _ _).mp HWfConfig).2` and
  `HWf2 := Step_is_wf _ _ _ HWf1 Hstore H` (uses `Step_is_wf`, which reaches `sorryAx`).
- drop: `match vcs, Hts with | [v], _ => exact ⟨s, f, [], Step.pure _ _ _ (Step_pure.drop v)⟩` (works for length 1). No sorryAx.
- select_expl / select_impl (identical bodies; impl has intro `C t t' nt vt HVsub Hteq HwfC Hwfinstr`): `rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs⟩⟩⟩⟩` + `simp at Hts` for wrong lengths;
  `invert_typeof_I32 v3 Ht3 HP3`; `cases v3 with | CONST nt c => simp only [admininstr_val, admininstr.CONST.injEq] at Hn3; obtain ⟨rfl, rfl⟩ := Hn3; cases n3 …` (zero -> `Step_pure.select_false`,
  succ -> `Step_pure.select_true`, side goals `(by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0])`) `| _ => simp [admininstr_val] at Hn3`.
- block: witness `[LABEL_ vt2.length [] (map admininstr_val vcs ++ map admininstr_instr bes)]`; `Hfun : fun_blocktype (state.mk_state s f) bt = mk_functype (mk_list vt1) (mk_list vt2)` by
  `cases HBok with | valtype valtype_opt _ _ => cases valtype_opt <;> rfl | typeidx x _ _ _ Hty _ _ => show f.MODULE.TYPES[proj_uN_0 x]! = _; rw [← lookup_types s f C' (List.map typeof f.LOCALS) lab ret _ Hmod, ← Hcontext]; exact Hty`;
  `Hlen : vcs.length = vt1.length := by rw [← Hts, List.length_map]`; `Step.read _ _ _ (Step_read.block (state.mk_state s f) vcs.length vcs bt bes vt2.length vt1 vt2 Hfun rfl Hlen rfl)`. IH unused (as in Rocq).
- Merge simulation took 2.759 s; `Step_is_wf` axioms [propext, sorryAx, Classical.choice, Quot.sound].

### C02 (loop, if, br) - all proved
- loop: same shape as block; `Step_read.loop (state.mk_state s f) vt1.length vcs bt bes vt1 vt2.length vt2 Hfun Hlen.symm rfl rfl` (NOTE argument order and orientation differ from block:
  `loop z k val_lst bt instr_lst t_1_lst v_n t_2_lst`, premise `vt1.length = vcs.length`); witness `[LABEL_ vt1.length [LOOP bt bes] (vals ++ bes)]`. Uses `lookup_types`.
- if: `obtain ⟨v, Hvcs, Hvs1, Hvs2⟩ := typeof_append vt1 valtype.I32 vcs Hts; generalize List.take vt1.length vcs = vs1 at Hvcs Hvs1; subst Hvcs`, `invert_typeof_I32 v Hvs2 HWfv`,
  `simp only [List.map_append, List.append_assoc, List.map_cons, List.map_nil, List.cons_append, List.nil_append, admininstr_instr] at HWfConfig ⊢; rw [Heqv] at HWfConfig ⊢`,
  `Hwf1 := ((wf_config_app _ _ _).mp HWfConfig).2`; `cases n` : zero -> `Step_pure.if_false _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0])` to `[BLOCK bt bes2]`,
  succ -> `Step_pure.if_true` to `[BLOCK bt bes1]`; then `cases vs1`: nil -> bare `HStep`, cons -> `Step.ctxt_instrs _ (x :: xs) _ [] _ _ HStep (Or.inl (List.cons_ne_nil _ _)) Hwf1 Hwf2`
  with `Hwf2 := Step_is_wf _ _ _ Hwf1 Hstore HStep`. Deviation: splits on `vs1` directly instead of Rocq's `case Hvt1s: vt1` + `map_eq_nil`; Rocq proves the true-branch target wf by hand
  (C02 notes one could build `wf_config [BLOCK bt bes]` by hand from the IFELSE wf to drop `Step_is_wf`; not done). Uses `Step_is_wf`.
- br: `exact (not_lf_br_singleton _ l Hnotbr rfl).elim` (faithful). VERIFIED sorry-free alternative (Work3.lean): `exact (Hnotbr [] l [] rfl).elim` (directly from the definition of `not_lf_br`),
  `#print axioms` = [propext, Classical.choice, Quot.sound]. C02 left the choice to the main thread; the CURRENT file (4102-4110) uses the faithful `not_lf_br_singleton` form.
- Work4.lean result: `Step_is_wf`, `Step_read_is_wf`, `Step_pure_is_wf` ALL depend on `sorryAx` (so every proof using `Step_is_wf` inherits it). The bundle19 `Step_is_wf` takes a `Store_ok (fun_store z)` premise; `Hstore : Store_ok s` fits by defeq.

### C03 (br_if, br_table) - both proved, deliberately WITHOUT `Step_is_wf`
- Both: peel `Htf`, `typeof_append` -> `vcs = vs ++ [v1]`, `invert_typeof_I32`, `generalize List.take … vcs = vs at Hvcs Hts'; subst Hvcs`, rewrite the config with
  `Hcfg : List.map admininstr_val (vs ++ [v1]) ++ List.map admininstr_instr [BR_IF l] = List.map admininstr_val vs ++ ([CONST I32 (mk_num__0 I32 (mk_uN n)), BR_IF l] ++ []) := by simp [Heqv, admininstr_instr]`.
- Reusable local helper `Hctxt : ∀ es es', Step_pure es es' → Forall wf_admininstr es' → wf_config (mk_config (mk_state s f) (map admininstr_val vs ++ (es ++ []))) → ∃ s' f' es'', Step …` : takes
  `Hst : wf_state`, `Hais` out of the wf_config with `cases Hwf with | config_case_0 _ _ h1 h2 => exact ⟨h1, h2⟩`; `cases vs`: nil -> `Step.pure _ _ _ Hpure`; cons -> `Step.ctxt_instrs _ (v :: vs') es [] _ es' (Step.pure _ _ _ Hpure) (Or.inl (List.cons_ne_nil _ _)) (wf_config.config_case_0 _ _ Hst Hes) (wf_config.config_case_0 _ _ Hst Hes')`.
  This builds the reduct's wf by hand (`[]` or `[BR l]`; `wf_uN 32 l` from `cases a_3 with | instr_case_8 _ h => exact h` for BR_IF, `| instr_case_9 _ _ h1 h2` for BR_TABLE) using the helpers
  `iswf_Forall_nil`, `iswf_Forall_cons`, `iswf_Forall_getElem!` (for `l_lst[n]!`), `iswf_uN_zero`, and `wf_admininstr.admininstr_case_7 _ Hl` (wf of `BR l`).
  (my cross-check: the four `iswf_*` helpers are the bundle19 hand-written lemmas at OLD_wasm2.0.lean:304-386 and are NOT in the regenerated wasm2.0.lean.)
- br_if: `cases n`: zero -> `Step_pure.br_if_false`, succ -> `Step_pure.br_if_true` (side goals `by simp [proj_num__0]`, `by simp [proj_num__0, proj_uN_0]`).
- br_table: `rw [← Htf1, ← List.append_assoc] at Hts` (Rocq `catA`) before `typeof_append`; `generalize List.take (t_1_lst ++ t_lst).length vcs = vs …`; `by_cases Hv1 : n < l_lst.length`:
  `Step_pure.br_table_lt _ _ _ (by simpa [proj_num__0, proj_uN_0] using Hv1) (by simp [proj_num__0])`, else `Step_pure.br_table_ge _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]; omega)` to `[BR l']`.
- Axiom check variant with `typeof_append`/`invert_typeof_I32` as hypotheses (Check.lean) gives [propext, Classical.choice, Quot.sound]: those two (then-sorry) lemmas were the only `sorryAx` sources.

### C04 (call, call_indirect, return, const, unop) - all proved
- Bundle20-era helper line numbers: `wf_config_app` 65, `typeof_append` 188, `invert_typeof_I32` 209, `invert_typeof_numtype` 225, `not_lf_return_singleton` 349, `funcs_size` 563, `unop_not_none` 586, `call_indirect_progress` 1312 (all then `sorry`).
- call: `Hlen : proj_uN_0 x < (fun_funcaddr (state.mk_state s f)).length := by subst Hcontext; rw [funcs_size s f C' _ lab ret Hmod] at Haddr; exact Haddr`;
  `HRead := Step.read _ _ _ (Step_read.call _ x Hlen)` to `[CALL_ADDR ((fun_funcaddr …)[proj_uN_0 x]!)]`; `cases vcs`: nil -> `HRead`; cons -> `HWfConfig2 := ((wf_config_app _ _ _).1 HWfConfig).2`,
  `HWfConfig' := Step_is_wf _ _ _ HWfConfig2 Hstore HRead`, `Step.ctxt_instrs (state.mk_state s f) (v :: vcs) [CALL x] [] (state.mk_state s f) _ HRead (Or.inl …) HWfConfig2 HWfConfig'`, then `rw [List.append_nil, List.append_nil] at HStep`.
- call_indirect: `unfold mkFunctype at Htf; injection Htf with Htf1 _; injection Htf1 with Htf1` (alternative to the `simp only` prologue); `typeof_append`; `invert_typeof_I32`;
  `obtain ⟨es, HStep⟩ := call_indirect_progress s f (num_.mk_num__0 Inn.I32 (uN.mk_uN n)) x y (by simp [proj_num__0])`; `generalize List.take ts1.length vcs = vcs0 at Hvcs; subst Hvcs`;
  `Hlist` rewrite `… = map admininstr_val vcs0 ++ ([CONST I32 (mk_num__0 I32 (mk_uN n))] ++ [CALL_INDIRECT x y]) := by simp [Heqv, admininstr_instr]`; `cases vcs0` (nil -> `HStep`; cons -> `ctxt_instrs` with `Step_is_wf`).
  Deviation: Rocq's `minst_invert_tables`/`Forall2_size2` steps (they derive an unused `Hmod` fact) omitted; split on the value prefix instead of `destruct ts1` (same split).
- return: `exact absurd rfl (not_lf_return_singleton _ Hnotret)` (`List.map admininstr_instr [instr.RETURN]` unifies with `[admininstr.RETURN]` by unfolding).
- const: `left; rfl`. sorryAx-free.
- unop: `rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩`; `invert_typeof_numtype v1 t Hts`; `cases Eunop : fun_unop_ t unop n with | some c => cases c with | nil => Step_pure.unop_trap t n unop (by rw [Eunop]; simp) (by rw [Eunop]; rfl) | cons c' l => Step_pure.unop_val t n unop c' (by rw [Eunop]; simp) (by rw [Eunop]; simp) (by rw [Eunop]; simp)`
  (the `List.contains` premise is closed by `simp` using the derived `LawfulBEq num_`); `none` impossible: `cases v1 <;> simp only [admininstr_val, admininstr.CONST.injEq, reduceCtorEq] at Heqv1; obtain ⟨rfl, rfl⟩ := Heqv1`, invert `wf_val` (`val_case_0 _ _ Hn`) and `wf_instr` (`instr_case_14 _ _ Hu`), `unop_not_none _ _ _ Hn Hu Eunop`.

### C05 (binop, testop, relop, cvtop, ref_null, ref_func) - all proved
- binop: `rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩`; `invert_typeof_numtype_wf v nt Ht HP` gives `⟨n, Heqv, Hwf⟩`; `Hwfb : wf_binop_ nt binop_nt := by cases Hwfinstr; assumption`; `binop_total` -> `lst_opt`;
  `rcases lst_opt with _ | ⟨_ | ⟨a', as'⟩⟩`: none -> `absurd rfl (binop_not_none …)`, `some []` -> `Step_pure.binop_trap nt n1 n2 binop_nt _ HBinop (by simp) (by simp)`, `some (a' :: _)` -> `Step_pure.binop_val … (by simp) (by simp) (by simp)`.
- testop: `Step_pure.testop nt n1 testop_nt c' Hne Hc (testop__is_wf nt testop_nt n1 c' Hwft Hwf1 Hne Hc)` after `cases ENone : fun_testop_ nt testop_nt n1 with | some c' … | none => absurd ENone (testop_not_none …)`;
  `Hne := by rw [ENone]; simp`, `Hc := by rw [ENone]; simp`. Imported `testop__is_wf` axioms: [propext, Quot.sound] (sorry-free).
- relop: `relop_total` gives `c : Option num_`; `rcases c with _ | c'`; `Step_pure.relop nt n1 n2 relop_nt c' (some c') Hrelop Hne Hc (relop__is_wf nt relop_nt n1 n2 c' (some c') Hrelop Hwfr Hwf1 Hwf2 Hne Hc)`.
  Imported `relop__is_wf` axioms [propext, sorryAx, Quot.sound] (transitively sorry; (my cross-check, static closure in OLD) via `feq__is_wf`, `fne__is_wf`, `flt__is_wf`, `fgt__is_wf`, `fle__is_wf`, `fge__is_wf`).
- cvtop: ARGUMENT SWAP: `wf_instr (CVTOP nt_1 nt_2 cvtop)` gives `wf_cvtop__ nt_2 nt_1 cvtop`; the `Step_pure.cvtop_val`/`cvtop_trap` rules are instantiated with `nt_1 := nt_2`, `nt_2 := nt_1`
  (`invert_typeof_numtype_wf v1 nt_2 …`, `cvtop_total nt_2 nt_1 cvtop n1 Hwf1 Hwfc`, `Step_pure.cvtop_val nt_2 n1 nt_1 cvtop c _ Hcvtop (by simp) (by simp) (by simp)`).
- ref_null: `left; rfl`, sorryAx-free. ref_func: `rw [Hcontext] at Hxrange; rw [funcs_size s f C' (List.map typeof f.LOCALS) lab ret Hmod] at Hxrange`; `Step_read.ref_func (state.mk_state s f) x (by simpa [fun_funcaddr] using Hxrange)`.
- Merge simulation: 200 `declaration uses sorry` warnings on earlier lemmas, last at Head.lean line 1716 (`t_progress_be_unop`); none on the six targets.

### C06 (ref_is_null, vconst, vvunop, vvbinop, vvternop) - all proved
- ref_is_null: `rcases invert_typeof_reftype v1 rt Ht1 with Hnull | ⟨x, Hf | Hh⟩`; REF_NULL -> `Step_pure.ref_is_null_true (ref.REF_NULL rt) rt rfl`; REF_FUNC_ADDR / REF_HOST_ADDR -> `Step_pure.ref_is_null_false (ref.REF_FUNC_ADDR x) ?_`
  whose premise is a NEGATED before-predicate: `intro HContra; generalize hl : [admininstr_ref (ref.REF_FUNC_ADDR x), admininstr.REF_IS_NULL] = l at HContra; cases HContra with | ref_is_null_true_0 v_ref rt' h => subst h; simp [admininstr_ref] at hl`
  (the `generalize` avoids a dependent-elimination failure on the index `admininstr_ref v_ref`).
- vconst: `left; rfl`, sorryAx-free. vvunop/vvbinop/vvternop: `invert_typeof_V128 v Ht HP` gives `⟨c, Heqv, _⟩`; witness `[VCONST V128 (vvunop_ V128 v_vvunop c1)]` (resp. vvbinop_/vvternop_), `Step_pure.vvunop c1 v_vvunop _ rfl` (`vvbinop c1 c2 op _ rfl`, `vvternop c1 c2 c3 op _ rfl`).
- Direct sorry users (Work_sorry.lean): ref_is_null -> `invert_typeof_reftype`; vv* -> `invert_typeof_V128`.

### C07 (vvtestop, vunop, vbinop, vtestop) - all proved
- vvtestop: `cases v_vvtestop` (only `ANY_TRUE`); witness `CONST I32 (mk_num__0 I32 (ine_ (Option.get! (size valtype.V128)) c1 (uN.mk_uN 0)))`; `Step_pure.vvtestop c1 _ (by simp [proj_num__0]) (by simp [size]) rfl (wf_num_.num__case_0 _ _ _ (by simp [size, valtype_Inn]) (ine__is_wf _ c1 (uN.mk_uN 0) _ Hwf1 (wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩) rfl) rfl) (wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩)`.
- vunop: `Hwfsh : wf_shape sh`, `Hwfop : wf_vunop_ sh vunop_sh` both `by cases Hwfinstr; assumption`; `vunop_total sh vunop_sh c1 Hwfop Hwf1 Hwfsh` -> `lst_opt`; none -> `vunop_not_none`; `some []` -> `Step_pure.vunop_trap`; `some (v' :: _)` -> `Step_pure.vunop c1 sh vunop_sh v' _ Hvunop (by simp) (by simp) (by simp)`.
- vbinop: `vbinop_some sh vbinop_sh c1 c2 Hwfsh Hwfop Hwf1 Hwf2` gives `r`; `r = []` -> `Step_pure.vbinop_trap`, `r = v :: _` -> `Step_pure.vbinop_val`.
- vtestop: `obtain ⟨v_Jnn, v_N, var_x, Hsh⟩ := Hwfop` (NOTE `wf_vtestop_`'s `v_shape` is an auto-promoted inductive parameter and takes NO slot), `subst Hsh; cases var_x` (only `ALL_TRUE`),
  `Hlall := lanes__is_wf _ _ _ Hwfsh Hwf1 rfl` (imported, sorry body), `cases E : List.all (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) c1) (fun ci => (proj_lane__0 ci != none) && (proj_uN_0 (Option.get! (proj_lane__0 ci)) != 0)) with`;
  true -> `all_and_Forall _ _ _ _ E` + `Step_pure.vtestop_true c1 v_Jnn v_N _ rfl (fun ci hci => by simpa using Hsome ci hci) (fun ci hci => by simpa using Hnz ci hci) Hlall Hwfsh`;
  false -> `Step_pure.vtestop_false c1 v_Jnn v_N ?_` whose premise is a negated before-predicate: PITFALL direct `cases Hb` fails with "Dependent elimination failed" (index contains `lanetype_Jnn v_Jnn`, a stuck match) -> `generalize hl : [VCONST V128 c1, VTESTOP (shape.X …) (vtestop_.mk_vtestop__0 v_Jnn v_N vtestop_Jnn_N.ALL_TRUE)] = l at Hb`,
  `cases Hb with | vtestop_true_0 c' J' N' ls Hls Hsome Hnz Hwl Hsh' =>`, then equalities from `List.cons.inj hl`, `admininstr.VCONST.inj`, `admininstr.VTESTOP.inj`, `subst`, `rw [hsh] at E`, `Forall_and_all … ` and `exact Bool.noConfusion (Hall.symm.trans E)`.
- Sorry users: vvtestop `invert_typeof_V128`; vunop `invert_typeof_V128, vunop_total, vunop_not_none`; vbinop `invert_typeof_V128, vbinop_some`; vtestop `invert_typeof_V128, lanes__is_wf, Forall_and_all, all_and_Forall`.

### C08 (vrelop, vshiftop, vbitmask) - all proved
- vrelop: `vrelop_some sh vrelop c1 c2 Hwfsh Hwfop Hwf1 Hwf2` -> `r`; `Step_pure.vrelop c1 c2 sh vrelop r (some r) Hr (Option.some_ne_none r) rfl`.
- vshiftop (RELEVANT to upstream ishl_/ishr_ change): `invert_typeof_V128 v1 …`, `invert_typeof_I32_wf v2 Ht2 HP0` gives `⟨k, Heqv2, Hwfk⟩`; `obtain ⟨J, M, o, Hsh⟩ := Hwop` (v_ishape auto-promoted: no slot; first attempt `⟨_, J, M, o, Hsh⟩` -> "Unknown identifier Hsh"), `subst Hsh`; `Hwsh := by cases Hwish; assumption` (instead of Rocq's wf_ishape_inv + J'=J/M'=M step);
  `Hl := lanes__is_wf _ _ _ Hwsh Hwf1 rfl` (imported, sorry body, wasm2.0.lean:4651 then); `Hlx` from `wf_lane_Jnn_inv J l (Hl l hl) (wf_lane_Jnn_some J l (Hl l hl))`; `cases o with | SHL | SHR v_sx`.
  Witness (SHL) `inv_lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) (List.map (fun l => lane_.mk_lane__0 J (ishl_ (lsizenn (lanetype_Jnn J)) (Option.get! (proj_lane__0 l)) (uN.mk_uN k))) (lanes_ … c1))` (SHR: `ishr_ (lsizenn …) v_sx …`);
  `Step_pure.vshiftop c1 k J M _ _ (lanes_ … c1) (List.map (fun l => some (lane_.mk_lane__0 J (ishl_ … (uN.mk_uN k)))) (lanes_ … c1)) ?_ ?_ rfl ?_ ?_ Hl Hwsh Hwish Hwfk` with side goals: length `simp`; Forall₂ by `apply Forall2_map_l; intro l hl; obtain ⟨x, rfl, _⟩ := Hlx l hl; cases J` then
  `exact fun_vshiftop_.fun_vshiftop__case_0 M x k M rfl` (cases 0..3 for SHL, `fun_vshiftop__case_4 M v_sx x k M rfl` .. `_7` for SHR); `≠ none` by `Option.some_ne_none`; the `inv_lanes_` equation `simp only [Map, List.map_map]; rfl`.
- vbitmask: `wf_ishape_inv _ Hwish` -> `⟨J, M, Hsh, Hwsh, HM⟩`; `HL := lanes_Jnn_form J M c1 Hwsh Hwf1`; `Hz0 : wf_uN (lsize (lanetype_Jnn J)) (uN.mk_uN 0) := wf_uN.uN_case_0 _ 0 ⟨Nat.zero_le _, Nat.zero_le _⟩`;
  `Forall_exists_Forall2 uN lane_ (fun v l => fun_ilt_ (lsize (lanetype_Jnn J)) sx.S (Option.get! (proj_lane__0 l)) (uN.mk_uN 0) v) (fun v => wf_bit (bit.mk_bit (proj_uN_0 v))) (lanes_ …) (by … icmp_total_bit … bit_of_wf1 …)`;
  `lanes_len` (HelperLemmas.lean:785 PROJECT AXIOM) gives `HlenM`; `obtain ⟨bits, Hbits⟩ : ∃ bits : List bit, bits = Map (fun v => bit.mk_bit (proj_uN_0 v)) vs ++ List.replicate (Int.toNat ((32 : Int) - (M : Int))) (bit.mk_bit 0) := ⟨_, rfl⟩` (Rocq `pose`);
  `Hbl : bits.length = 32` needs PITFALL FIX: `omega` ignores `HM : M ≤ 16` because it is stated at the abbrev type `N`; restate `have HM' : @LE.le Nat instLENat M 16 := HM` before `omega`.
  Final: `Step_pure.vbitmask c1 J M (inv_ibits_ 32 bits) (lanes_ …) vs Hsvs (jlane_some J _ HL) H2 rfl ((ibits_inv 32 bits Hbl Hbw).trans Hbits) (inv_ibits__is_wf 32 bits _ Hbw rfl) Hwsh Hb (wf_bit.bit_case_0 0 (Or.inl rfl))` (`ibits_inv` = PROJECT AXIOM HelperLemmas.lean:821 = Rocq axioms.v:64; `inv_ibits__is_wf` wasm2.0.lean:4239 then, sorry body). Rocq's `two_pow_pos`/`Zsub1_toN` steps and `Forall2_size_eq` not needed in Lean.
- Sorry users: vshiftop `invert_typeof_V128, invert_typeof_I32_wf, wf_lane_Jnn_inv, wf_lane_Jnn_some, Forall2_map_l` + imported `lanes__is_wf`; vbitmask `invert_typeof_V128, wf_ishape_inv, lanes_Jnn_form, Forall_exists_Forall2, icmp_total_bit, bit_of_wf1, jlane_some` + axioms `lanes_len`, `ibits_inv` + imported `inv_ibits__is_wf`.

### C09 (vswizzle, vshuffle, vsplat) - all proved, compiled first try
- vswizzle: `Hsh : sh = ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim 16)) := by cases HWfinstr; assumption; subst Hsh`; `Hwsh := wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (Or.inr rfl)) rfl`; `lanes_Jnn_form Jnn.I8 16 c1/c2 Hwsh Hwf1/2`;
  `obtain ⟨cs, Hcs⟩ : ∃ cs : List iN, cs = List.map (fun l => Option.get! (proj_lane__0 l)) (lanes_ … c1) ++ List.replicate (Int.toNat ((256 : Int) - ((16 : Nat) : Int))) (uN.mk_uN 0) := ⟨_, rfl⟩`; `Hcsw` via `jlane_proj_wf` + `List.eq_of_mem_replicate`; `Hcsl : cs.length = 256` via `lanes_len` then `all_goals decide`;
  `Hidx` via `getElem!_pos` + `List.getElem_mem`; `Hx256 : ∀ x : uN, wf_uN 8 x → proj_uN_0 x < 256` by `cases hx with | uN_case_0 i h => have h2 : i ≤ 255 := h.2; simp only [proj_uN_0]; omega` (replaces Rocq `wf_uN_lt'`);
  `Step_pure.vswizzle c1 c2 packtype.I8 16 _ (lanes_ … c2) cs 0 rfl ?_ ?_ ?_ ?_ ?_ rfl Hwsh ?_ ?_`; Rocq `holds_upto_intro` steps done inline (`intro k hk; rw [List.mem_range] at hk`).
- vshuffle: `Hshlen : sh = ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim 16)) ∧ i_lst.length = 16 := by cases HWfinstr; assumption`; `cs` = proj of `lanes c1 ++ lanes c2` (length 32 via `lanes_len` twice); `Step_pure.vshuffle c1 c2 packtype.I8 16 i_lst _ cs 0 ?_ ?_ ?_ rfl ?_ Hwsh ?_`.
- vsplat: `obtain ⟨Lnn, ⟨Ndim⟩⟩ := sh`; `invert_typeof_numtype_wf v1 (unpack Lnn) Ht1 HP1`; `packnum_not_none Lnn c1 Hwf1`; `Step_pure.vsplat Lnn c1 Ndim _ Hpk rfl Hwfsh` with witness `inv_lanes_ … (List.replicate Ndim (Option.get! (packnum_ Lnn c1)))`.
- Axioms: vswizzle/vshuffle also depend on project axiom `lanes_len`; Work_ax.lean (7 sorry lemmas -> local axioms of identical statement) showed `sorryAx` comes only from those 7 lemmas (`invert_typeof_V128, lanes_Jnn_form, jlane_some, jlane_proj_wf, jlane_map_proj, invert_typeof_numtype_wf, packnum_not_none`).

### C10 (vextract_lane, vreplace_lane, vextunop) - all proved
- vextract_lane: `obtain ⟨lt, ⟨M⟩⟩ := sh`; `Hwsh`, `Hiff : (List.contains [I32, I64, F32, F64] lt = true) ↔ (sx_opt = none) := by cases HWfinstr; assumption`; `Hi' : proj_uN_0 i < M := Hi`, `Hwf1' : wf_uN 128 c1 := Hwf1`;
  `Hl := lanes_nth_wf lt M c1 (proj_uN_0 i) Hwsh Hwf1' Hi'`; `Hlen` via project axiom `lanes_len`; `rcases sx_opt with _ | sx <;> cases lt` yields 12 goals IN THIS ORDER: (none × I32, I64, F32, F64, I8, I16) then (some × same):
  goals 1-4 numtype lanes (`Step_pure.vextract_lane_num c1 numtype.I32 M i _ … Hlen … Hwsh`, with `wf_lane_Jnn_inv Jnn.I32 _ Hl (wf_lane_Jnn_some Jnn.I32 _ Hl)` / `wf_lane_Fnn_inv Fnn.F32 _ Hl` giving `x`); goals 5-6 (none × packed) `exact absurd (Hiff.mpr rfl) (by decide)`;
  goals 7-10 (some × numtype) `exact absurd (Hiff.mp (by decide)) (by simp)`; goals 11-12 packed `Step_pure.vextract_lane_pack c1 packtype.I8 M sx i (mk_num__0 I32 (extend__ 8 32 sx x)) … (wf_num_.num__case_0 _ _ _ (by simp [size, valtype_Inn]) (extend___is_wf 8 32 sx x _ Hwx rfl) rfl) Hwsh`.
  Lean-specific: step premises mention `lanetype_numtype nt`/`lanetype_packtype pt` while `Hx` mentions `lanetype.I32`, so each lane-dependent premise is stated with `show … by rw [Hx]; simp [unpacknum_]` (defeq bridge). `extend___is_wf` (wasm2.0.lean:2714 then) still sorry.
- vreplace_lane: `obtain ⟨Lnn, ⟨Ndim⟩⟩ := sh`; `invert_typeof_numtype_wf v2 _ Ht2 HP2`; `packnum_not_none Lnn c2 Hwf2`; `exact ⟨s, f, _, Step.pure _ _ _ (Step_pure.vreplace_lane c1 Lnn c2 Ndim i _ Hpk rfl Hwfsh)⟩` (result vector left to unification; Lean's generated rule spells Rocq's `list_update_func` as `List.modify`).
- vextunop: `obtain ⟨J1, M1, J2, M2, o, Ho, E1, E2⟩ := Hop; subst E1 E2` (ishape indices auto-promoted, no slots); `obtain ⟨sx, Hsz⟩ := Ho`; `obtain ⟨E, hE⟩ : ∃ E : List iN, E = List.map (fun l => extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx (Option.get! (proj_lane__0 l))) (lanes_ … c1) := ⟨_, rfl⟩`;
  `HEw` via `Forall_map_P … (jlane J1)` + `extend___is_wf`; `HEe : ¬ Odd E.length` via `shape_lanes_even`; `HEs := evens_odds_size`; `HW2` via `Forall2_of_Forall` + `Forall_evens/odds` + `iadd__is_wf`; `HEc` via `evens_odds_concat` after converting `Map₂ (fun a b => [a, b]) (evens E) (odds E)` to `List.zipWith` with
  `hM := by simp [Map₂, List.ap, List.zipWith_map_left]` (Lean's generated `fun_vextunop__` uses `Map₂ f xs ys = List.zipWith (· ·) (map f xs) ys`, Rocq uses `list_zipWith`);
  `Hfun : fun_vextunop__ … (some (inv_lanes_ … (Map₂ (fun a b => lane_.mk_lane__0 J2 (iadd_ (lsizenn2 (lanetype_Jnn J2)) a b)) (evens E) (odds E))))` by `cases J1 <;> cases J2 <;> first | exact absurd Hsz (by decide) | exact fun_vextunop__.fun_vextunop___case_14 M1 M2 sx c1 (evens E) (odds E) M1 M2 _ _ rfl HS HEc rfl Hs1 Hs2 HEs HW2 rfl rfl | exact fun_vextunop__.fun_vextunop___case_3 …`
  (only size-valid pairs: I8->I16 = generated case_14, I16->I32 = case_3); finally `Step_pure.vextunop c1 _ _ _ _ _ Hfun (by simp) rfl`.
- Sorry users: vextract_lane `invert_typeof_V128, lanes_nth_wf, wf_lane_Jnn_inv, wf_lane_Jnn_some, wf_lane_Fnn_inv, extend___is_wf` (+ axiom `lanes_len`); vreplace_lane `invert_typeof_V128, invert_typeof_numtype_wf, packnum_not_none`;
  vextunop `invert_typeof_V128, lanes_Jnn_form, Forall_map_P, extend___is_wf, shape_lanes_even, evens_odds_size, Forall2_of_Forall, Forall_evens, Forall_odds, jlane_some, evens_odds_concat` (`iadd__is_wf` itself is NOT a sorry user: it is hand-proved in OLD).

### C11 (vextbinop, vnarrow) - both proved
- vextbinop: same inversion as vextunop (`wf_vextbinop__ sh_2 sh_1 op`, `⟨J1, M1, J2, M2, o, Ho, E1, E2⟩`, `H128 : lsize (lanetype_Jnn J1) * M1 = 128 := by cases Hs1 with | shape_case_0 _ _ _ h => exact h`); Deviation: proves `Hfun : ∃ c, fun_vextbinop__ … c1 c2 (some c)` first
  (witness fixed by the constructor's `c = inv_lanes_ …` premise closed by `rfl`), then `Step_pure.vextbinop c1 c2 _ _ _ c (some c) Hc (Option.some_ne_none c) rfl`.
  `rcases Ho with ⟨hf, v_sx, Hsz⟩ | ⟨Hsz⟩` (EXTMUL / DOT); EXTMUL facts `Forall_list_slice … (fun_half hf 0 M2) M2`, `list_slice_size_eq`, `zip_lane_wf2 J1 J2 (lanetype_Jnn J2) (fun a b => imul_ … (extend__ …) (extend__ …)) _ _ rfl (… imul__is_wf … extend___is_wf …) HS1 HS2 HSs`;
  `cases J1 <;> cases J2 <;> (try exact absurd Hsz (by decide)) <;> first | exact ⟨_, fun_vextbinop__.fun_vextbinop___case_3 …⟩ | … case_4 … | … case_14 …` (valid pairs (I16,I32), (I32,I64), (I8,I16)); DOT: `obtain ⟨P, HPdef⟩ : ∃ P : List iN, P = List.zipWith (fun a b => imul_ … sx.S … ) (lanes c1) (lanes c2) := ⟨_, rfl⟩`, `zip_wf`, `size_zipWith_eq` + `shape_lanes_even`, `evens_odds_size/concat`,
  `Forall2_of_Forall` + `iadd__is_wf`, then `fun_vextbinop___case_19 M1 M2 c1 c2 (evens P) (odds P) M1 M2 _ _ _ rfl rfl HSo1 HSo2 (by simp only [hMap2]; exact HPc.trans HPdef) rfl Hs1 Hs2 HPs HW2 rfl rfl` with local `hMap2 : ∀ {A B D} (g : A → B → D) l1 l2, Map₂ g l1 l2 = List.zipWith g l1 l2 := by simp [Map₂, List.ap, List.zipWith_map_left]`.
  DOT fixes the extension signedness to `sx.S` (Rocq `res_S`).
- vnarrow: `obtain ⟨J2, N2, rfl, Hs2, _⟩ := wf_ishape_inv _ Hw1` and `obtain ⟨J1, N1, rfl, Hs1, _⟩ := wf_ishape_inv _ Hw2` (so sh_1 = output shape, sh_2 = input shape); `Hnar` via `refine Forall_map_P _ _ _ _ _ _ ?_ HL`;
  PITFALL: the Rocq-style `Forall_map_P _ _ _ _ _ _ _ HL` puts `HL` into the pointwise-hypothesis slot ("introN failed"); use `refine … ?_ HL`. Final `Step_pure.vnarrow c1 c2 J2 N2 J1 N1 v_sx _ (lanes c1) (lanes c2) _ _ rfl rfl (jlane_some _ _ HL1) rfl (jlane_some _ _ HL2) rfl rfl (lanes__is_wf _ _ _ Hs1 Hwf1 rfl) (lanes__is_wf _ _ _ Hs1 Hwf2 rfl) Hs1 Hs2 (Hnar _ HL1) (Hnar _ HL2)`.
- Imported generated wf theorems used: vextbinop `extend___is_wf, imul__is_wf, iadd__is_wf`; vnarrow `narrow___is_wf, lanes__is_wf`. C11 says these have `sorry` bodies in "todaywasm2.0.lean": INACCURATE for `imul__is_wf`/`iadd__is_wf` (see section 5).
- Meta check: neither proof term references `sorryAx` directly; sorryAx only inherited.

### C12 (vcvtop, local_get, local_set, local_tee, global_get, global_set) - 5 sorry-free, vcvtop with ONE documented `sorry`
- vcvtop (bundle20-era TypeProgress.lean:1978; Rocq 4301-4339, `admit` at 4319): after the prologue and `simp only [..., List.cons.injEq, and_true] at Hts`, `invert_typeof_V128 v1 Hts HP`, `Hwf1' : wf_uN 128 c1 := Hwf1` (defeq, `Option.get! (size V128) = 128`),
  `rw [show List.map admininstr_val [v1] = [admininstr.VCONST vectype.V128 c1] by simp [Heqv1]]`; `Hs1 : wf_shape sh_1`, `Hs2 : wf_shape sh_2`, `Hop : wf_vcvtop__ sh_2 sh_1 op` all `by cases HWfinstr; assumption`;
  `cases Hti : vcvtop_trunc_sat_i16 op with | true => sorry | false => …`; false branch: `obtain ⟨L2, ⟨M2⟩⟩ := sh_1; obtain ⟨L1, ⟨M1⟩⟩ := sh_2; cases Hh : halfop_of op with | some h => vcvtop_step_half L1 M1 L2 M2 op c1 h Hwf1' Hs2 Hs1 Hop Hti Hh | none => cases Hz : zeroop_of op with
  | some z => obtain ⟨nt1, nt2, E1, E2⟩ := vcvtop_zero_numtype L1 M1 L2 M2 op z Hop Hti Hz; subst E1 E2; cases z; vcvtop_step_zero nt1 M1 nt2 M2 op c1 Hwf1' Hs2 Hs1 Hop Hti Hz | none => HL := vcvtop_full_lsize L1 M1 L2 M2 op Hop Hti Hh Hz; HM : M1 = M2 (from `lsize L1 * M1 = 128`, `lsize L2 * M2 = 128`, `Hp : 0 < lsize L2 := by cases L2 <;> decide`, `Nat.eq_of_mul_eq_mul_left`); subst HM; vcvtop_step_full L1 L2 _ op c1 Hwf1' Hs2 Hs1 Hop Hti Hh Hz`;
  each branch ends `exact ⟨s, f, [admininstr.VCONST vectype.V128 c], Step.pure _ _ _ Hc⟩`.
  The `true` branch is closed by the single documented `sorry` (comment: "FALSE subcase as the spec stands (Rocq: admit at type_progress.v:4319); see vcvtop_trunc_sat_i16_stuck"). C12 checked that branch is exactly the known-false family: for F32 -> I16 `wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2` only admits `zero_opt = some ZERO` (32 = 2*16) and the `wf_shape` premises force `X 4 -> X 8`, i.e. exactly `vcvtop_trunc_sat_i16_stuck` (for all sx, c).
  Bundle20-era helper line numbers: `vcvtop_trunc_sat_i16` 1320, `halfop_of` 1385, `zeroop_of` 1394, `vcvtop_step_full` 1426, `vcvtop_step_half` 1437, `vcvtop_step_zero` 1450, `vcvtop_zero_numtype` 1469, `vcvtop_full_lsize` 1478. Head.lean: only warning in range is 1978; axioms [propext, sorryAx, Classical.choice, Quot.sound].
- local_get: vcs = []; witness `List.map admininstr_val [fun_local (state.mk_state s f) x]`, `Step.read _ _ _ (Step_read.local_get _ x)`. local_set: `cases Estate : with_local (state.mk_state s f) x v1 with | mk_state s' f' => refine ⟨s', f', [], ?_⟩; rw [← Estate]; exact Step.local_set _ v1 x`.
  local_tee: witness `[admininstr_val v1, admininstr_val v1, LOCAL_SET x]`, `Step.pure _ _ _ (Step_pure.local_tee v1 x)`. global_get: witness `List.map admininstr_val [(fun_global (state.mk_state s f) x).VALUE]`, `Step_read.global_get _ x`. global_set: like local_set with `with_global`, `Step.global_set _ v1 x`.
  All five: axioms [propext, Classical.choice, Quot.sound] only.

### C13 (table_get, table_set, table_size, table_grow, table_fill) - all proved
- table_get: `invert_typeof_I32 v1 Ht1 HP1`, `rw [Heqv]`; `by_cases Es : n < (fun_table (state.mk_state s f) x).REFS.length`: in bounds -> witness `[admininstr_ref ((fun_table …).REFS[n]!)]`, `Step.read _ _ _ (Step_read.table_get_val _ _ x (by simpa [proj_num__0, proj_uN_0] using Es) (by simp [proj_num__0]))`;
  out of bounds -> `[TRAP]`, `Step_read.table_get_trap _ _ x (by simp [proj_num__0]) (by simp [proj_num__0, proj_uN_0]; omega)`.
- table_set: `invert_typeof_I32` (v1 = CONST I32 n1) and `invert_typeof_reftype' v2 rt Ht2` (admininstr_val v2 = admininstr_ref r2); in bounds: `cases Estate : with_table (state.mk_state s f) x n1 r2 with | mk_state s' f' => refine ⟨s', f', [], ?_⟩; rw [← Estate]; exact Step.table_set_val _ _ r2 x …`
  (the rule's RHS state `with_table … (proj_uN_0 (Option.get! (proj_num__0 ..))) r2` is defeq to `with_table … n1 r2`); out of bounds: `Step.table_set_trap _ _ r2 x …` (a plain `Step` rule, not `read`, as in Rocq).
- table_size: no sorry lemma at all; witness `[CONST I32 (mk_num__0 I32 (mk_uN (fun_table (state.mk_state s f) x).REFS.length))]`, `Step_read.table_size _ x _ rfl`. Deviation: Rocq's `minst_invert_tables`/`Forall2_size2`/`resolve_inst_match` detour dropped because `fun_table` is total in Lean.
- table_grow ("always fail"): `invert_typeof_reftype' v1 rt Ht1`, `invert_typeof_I32 v2 Ht2 HP2`; `obtain ⟨r, Hunsigned⟩ := invsigned_total_32m1`; `Step.table_grow_fail _ r1 n2 x r (by simpa using Hunsigned)`
  — PITFALL: `invsigned_total_32m1` is stated at `(0 : Int) - 1` while the generated rule's premise is at `- (1 : Int)`; bridged by `simpa`.
- table_fill: `invert_typeof_I32` for v1 and v3 only (v2 stays `admininstr_val v2`; Rocq's `invert_typeof_reftype'` on v2 dropped since its result was unused); `by_cases Hs : n1 + n3 > (fun_table (state.mk_state s f) x).REFS.length`: true -> `Step_read.table_fill_trap _ _ v2 n3 x …`; false -> `cases n3`: zero -> `Step_read.table_fill_zero _ _ v2 0 x … (by simp [proj_num__0, proj_uN_0]; omega) rfl`;
  succ n3 -> explicit witness `[CONST I32 (mk_uN n1), admininstr_val v2, TABLE_SET x, CONST I32 (mk_uN (n1 + 1)), admininstr_val v2, CONST I32 (mk_uN n3), TABLE_FILL x]`, `have H : Int.toNat (((n3 + 1 : Nat) : Int) - 1) = n3 := by omega`,
  `have Hstep := Step_read.table_fill_succ (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)) v2 (n3 + 1) x (by simp [proj_num__0]) (by simp) (by simp [proj_num__0, proj_uN_0]; omega); rw [H] at Hstep; exact Step.read _ _ _ Hstep`.
- Sorry users: get `invert_typeof_I32`; set `invert_typeof_I32, invert_typeof_reftype'`; grow `invert_typeof_reftype', invert_typeof_I32, invsigned_total_32m1`; fill `invert_typeof_I32`; size none.

## 4. Consolidated techniques / pitfalls (with the lemma they came from)
(see the structured-output list; same content, grouped)

1. Prologue + `invert_typeof_vcs` replacement (all): `rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩` with one extra cons beyond the wanted length, `simp at Hts` kills wrong lengths; canonical forms via `invert_typeof_I32/V128/numtype_wf/reftype/reftype'` after `HWfVals v (by simp)` (= Rocq `inv_Forall HWfVals`).
2. `match vcs, Hts, HWfVals with | [v1, v2, v3], ..` FAILS for the 3-value pattern of select_* (C01): the equation compiler cannot refute the other lengths through `List.map typeof vcs = [t, t, I32]`. Use `rcases` with one extra cons + `simp at Hts` (the 1-value `match vcs, Hts with | [v], _` did work for drop).
3. `Blocktype_ok` context is an inductive parameter: patterns `valtype valtype_opt _ _` / `typeidx x _ _ _ Hty _ _` (C01 block, C02 loop). `fun_blocktype (mk_state s f) (_IDX x)` is `f.MODULE.TYPES[proj_uN_0 x]!` by `show`; Rocq `erewrite <- lookup_types` is `rw [← lookup_types s f C' (List.map typeof f.LOCALS) lab ret _ Hmod, ← Hcontext]`.
4. block vs loop `Step_read` instantiation differs (C01/C02): block `(… vcs.length vcs bt bes vt2.length vt1 vt2 Hfun rfl Hlen rfl)`, loop `(… vt1.length vcs bt bes vt1 vt2.length vt2 Hfun Hlen.symm rfl rfl)`.
5. Value-prefix peeling (C02 if, C03, C04 call_indirect): `generalize List.take n vcs = vs at Hvcs …; subst Hvcs` then `cases vs`; `rw [List.append_nil, List.append_nil] at HStep` after `ctxt_instrs`.
6. wf of `ctxt_instrs` premises without `Step_is_wf` (C03): helper `Hctxt` + `wf_config.config_case_0 _ _ Hst Hes`; reduct wf from `wf_instr` inversion (`instr_case_8/9`). `Step_is_wf` (C01 unreachable, C02 if, C04 call/call_indirect) reaches `sorryAx`.
7. Negated before-predicate premises (C06 ref_is_null_false, C07 vtestop_false): `intro Hb; generalize hl : <index list> = l at Hb; cases Hb with | <ctor>_0 …` to avoid "Dependent elimination failed"; extract equalities with `List.cons.inj`, `admininstr.VCONST.inj`, `admininstr.VTESTOP.inj`, `subst`.
8. Auto-promoted inductive parameters take no pattern slot: `wf_vshiftop_`, `wf_vtestop_`, `wf_vextunop__`, `wf_vextbinop__`, `Blocktype_ok`. `⟨_, J, M, o, Hsh⟩` -> "Unknown identifier Hsh"; correct is `⟨J, M, o, Hsh⟩`.
9. `omega` ignores hypotheses typed at abbrev types (`M ≤ 16` at `N`): restate `have HM' : @LE.le Nat instLENat M 16 := HM` (C08 vbitmask). (Same family: another agent found `v_n ≠ 0` at `n`.)
10. `Forall_map_P _ _ _ _ _ _ _ HL` puts HL in the pointwise slot: write `refine Forall_map_P _ _ _ _ _ _ ?_ HL` (C11 vnarrow).
11. `Map₂ g l1 l2 = List.zipWith g l1 l2 := by simp [Map₂, List.ap, List.zipWith_map_left]` (C10 `hM`, C11 `hMap2`); generated `fun_vextunop__`/`fun_vextbinop__` use `Map₂`.
12. Impossible lane-width pairs: `cases J1 <;> cases J2 <;> first | exact absurd Hsz (by decide) | exact fun_..._case_N …` (C10 vextunop: case_14, case_3; C11 vextbinop EXTMUL: case_3/4/14, DOT: case_19); keep the `∃ c, fun_vextbinop__ … (some c)` formulation to avoid writing the result twice.
13. Rocq `pose x := e` = `obtain ⟨x, hx⟩ : ∃ x, x = e := ⟨_, rfl⟩` (C08 bits, C09 cs, C10 E, C11 P).
14. `getElem!_pos` + `List.getElem_mem`, `List.eq_of_mem_replicate`, `Nat.eq_of_mul_eq_mul_left`, `Option.some_ne_none` replace Rocq's `Forall_size`, `wf_uN_lt'`, etc. (C08, C09, C12).
15. `show` to bridge `lanetype_numtype nt`/`lanetype_packtype pt` vs `lanetype.I32` before `rw [Hx]` (C10 vextract_lane); 12-goal order of `rcases sx_opt with _ | sx <;> cases lt` (none first).
16. `with_local/with_global/with_table` state: `cases Estate : with_local (state.mk_state s f) x v1 with | mk_state s' f' => refine ⟨s', f', [], ?_⟩; rw [← Estate]; exact Step.local_set _ v1 x` (C12 local_set/global_set, C13 table_set).
17. Int/Nat bridging (C13): `simpa using Hunsigned` for `0 - 1` vs `- 1`; `Int.toNat (((n3 + 1 : Nat) : Int) - 1) = n3 := by omega` + `rw [H] at Hstep`; oob bound goals `by simp [proj_num__0, proj_uN_0]; omega`.
18. cvtop argument swap (C05): `wf_instr (CVTOP nt_1 nt_2 cvtop)` gives `wf_cvtop__ nt_2 nt_1 cvtop`, rules instantiated `nt_1 := nt_2`.
19. Verification protocol (section 2): verbatim header guard `type_of% … = type_of% … := rfl` + negative control + olean freshness + merge simulation + mechanical sorry attribution (`collectAxioms`, `Expr.getUsedConstants`, axiom-substituted rerun).

## 5. Open issues / flagged doubts in these logs
- C12: ONE `sorry` (TypeProgress.lean:1978 then, now line 5656), `Hti = true` branch of `t_progress_be_vcvtop`; Rocq `admit` at `type_progress.v:4319`; counterexample `vcvtop_trunc_sat_i16_stuck` (now TypeProgress.lean:7998; `vcvtop_trunc_sat_i16_wf_instr` 7984).
- `Step_is_wf` transitively reaches `sorryAx` (C01/C02/C04; C02 Work4.lean shows `Step_read_is_wf` AND `Step_pure_is_wf` both do): affects unreachable, if, call, call_indirect (now TypeProgress.lean 3855, 4083+4093, 4262, 4312). C02 suggests building `wf_config [BLOCK bt bes]` by hand for `if` (as Rocq's true branch does); C03 shows the `Hctxt` technique.
- C02 `br`: two variants (faithful `not_lf_br_singleton`; sorry-free `exact (Hnotbr [] l [] rfl).elim`); the merged file uses the faithful one.
- Imported generated wf theorems with `sorry` bodies at the time: `lanes__is_wf` (wasm2.0.lean:4651; C07 vtestop, C08 vshiftop, C11 vnarrow), `inv_ibits__is_wf` (:4239; C08 vbitmask), `extend___is_wf` (:2714; C10 vextract_lane/vextunop, C11 vextbinop), `narrow___is_wf` (C11 vnarrow); `relop__is_wf` transitively sorry (C05).
- Project AXIOMS (not `sorry`) used: `lanes_len` (HelperLemmas.lean:785, mirrors Rocq `axioms.v` `lanes_len`) in vbitmask (C08), vswizzle and vshuffle (C09), vextract_lane (C10);
  `ibits_inv` (HelperLemmas.lean:821, = Rocq `axioms.v:64`) in vbitmask only (C08). Axiom lists printed: vswizzle/vshuffle `[propext, sorryAx, Classical.choice, Quot.sound, lanes_len]`, vextract_lane same.
- C11 inaccuracy: it states `imul__is_wf`/`iadd__is_wf` have `sorry` bodies in "todaywasm2.0.lean"; C10 mechanically shows `iadd__is_wf` is not a sorry user and OLD_wasm2.0.lean has them proved (lines 3075, 3142); in the REGENERATED wasm2.0.lean they are `sorry` (lines 2881, 2928) and must be re-proved.
- C13: bridging `invsigned_total_32m1` by `simpa` is form-sensitive (statement at `(0:Int) - 1`).
- No file reports a failed or skipped target; none reports a `declaration uses sorry` warning in a target other than vcvtop.

## 6. Relevance to the upstream changes (what will need changing)  -- partly my cross-check

(A) vcvtop / TRUNC_SAT (C12 `t_progress_be_vcvtop`, now TypeProgress.lean:5629-5686, `cases Hti` at 5653, sorry at 5656): delete `cases Hti … | true => sorry | false =>` and keep the false-branch body; drop the `Hti` argument from `vcvtop_step_half`, `vcvtop_zero_numtype`, `vcvtop_step_zero`, `vcvtop_full_lsize`, `vcvtop_step_full` once those helper lemmas lose their `vcvtop_trunc_sat_i16 op = false` premise.
    Helper lemmas now at TypeProgress.lean: def `vcvtop_trunc_sat_i16` 3289; `vcvtop_lane_total` 3297; `vcvtop_lanes_total` 3398; `halfop_of` 3524; `zeroop_of` 3533; `halfop_total` 3546; `zeroop_total` 3569; `vcvtop_step_full` 3602; `vcvtop_step_half` 3624; `vcvtop_step_zero` 3646; `vcvtop_zero_numtype` 3701; `vcvtop_full_lsize` 3740; counterexamples to delete: `vload_shape64_wf` 7938, `vload_shape64_stuck` 7946, `vcvtop_trunc_sat_i16_wf_instr` 7984, `vcvtop_trunc_sat_i16_stuck` 7998.
    Regenerated wasm2.0.lean: `vcvtop__Fnn_1_M_1_Inn_2_M_2` (line 1548), `wf_vcvtop__Fnn_1_M_1_Inn_2_M_2` (1553; premise `((sizenn1 (numtype_Fnn Fnn_1) = lsizenn2 (lanetype_Inn Inn_2) ∧ lsizenn2 (lanetype_Inn Inn_2) = 32) ∧ zero_opt = none) ∨ (sizenn1 (numtype_Fnn Fnn_1) = 2 * lsizenn2 (lanetype_Inn Inn_2) ∧ zero_opt = some zero.ZERO)`),
    `mk_vcvtop___2 (Fnn_1 M_1 Inn_2 M_2)` (1579), `wf_vcvtop___case_2` with `shape_2 = shape.X (lanetype_Inn Inn_2) (dim.mk_dim M_2)` (1595), `proj_vcvtop___2 : Option vcvtop__Fnn_1_M_1_Inn_2_M_2` (1620). The vcvtop proof body itself names no constructor, but the helper-lemma statements it calls (`vcvtop_zero_numtype` result `⟨nt1, nt2, E1, E2⟩`, `vcvtop_full_lsize` `lsize L1 = lsize L2`) will be restated against `lanetype_Inn`; re-check `subst E1 E2; cases z` and `Hp : 0 < lsize L2 := by cases L2 <;> decide`.
(B) ishl_/ishr_/vshiftop (C08 `t_progress_be_vshiftop`, now 4917; `ishl_/ishr_` text at 4952, 4957, 4976, 4981): the regenerated `fun_vshiftop_.fun_vshiftop__case_0..7` (wasm2.0.lean:10209-10232) now conclude with `ishl_ (lsizenn (lanetype_Jnn J)) lane (uN.mk_uN (v_n % (lsizenn (lanetype_Jnn J))))` (SHR: `ishr_ … v_sx lane (uN.mk_uN (v_n % …))`), whereas the logged proof builds `(uN.mk_uN k)`.
    These 8 are the ONLY constructors (of the 86 generated constructors referenced in the C01-C13 proof bodies) whose statement differs OLD->regenerated (script diff; `local_tee` showed a false positive from trailing text). Fix: in all four spots (SHL/SHR x {the `inv_lanes_` result witness in the `refine ⟨s, f, [VCONST …], ?_⟩`, the explicit `List.map (fun l => some …)` argument to `Step_pure.vshiftop`}) replace `(uN.mk_uN k)` by `(uN.mk_uN (k % lsizenn (lanetype_Jnn J)))`;
    keep `fun_vshiftop_.fun_vshiftop__case_i M x k M rfl` (constructor args `(v_M lane v_n M_0)`, premise `v_M = M_0` unchanged), keep `Hwfk`. `Step_pure.vshiftop` is unchanged (9 premises, wasm2.0.lean:12778). `ishl_`/`ishr_` are `opaque … (iN_0 : iN)` (3003, 3018; formerly `u32`), `uN.mk_uN _` typechecks both ways.
    C08's dependency list for vshiftop (section 3) names no `ishl_wf`/`ishr_wf` (the Rocq axioms deleted upstream; Lean copies at HelperLemmas.lean:844/847, still `k : u32`); (my grep) they are used only at TypeProgress.lean:1664-1665 and 1850-1851, in helper lemmas outside my files. C08 prints no `#print axioms` line, so this is inferred from its dependency list.
(C) vloadop_/SHAPE: none of C01-C13 touches vload (the batch range ends at table_fill); nothing to change from these files.
(D) iadd_ / memory fill-copy-init succ rules: C01-C13 touch no `memory.*` rule (C13 is `table.*`). (my cross-check) The regenerated `Step_read` differs from OLD in exactly `memory_fill_succ`, `memory_copy_le`, `memory_init_succ`; `table_fill_succ` (13064), `table_copy_le` (13080), `table_init_succ` (13105) still push `uN.mk_uN (i + 1)` unchanged, so C13 `t_progress_be_table_fill` (witness `mk_uN (n1 + 1)`) is unaffected; `Step_pure` (54) and `Step` (23) constructors unchanged.
    `iadd_` (def, wasm2.0.lean:2877) appears in C10/C11 only through `iadd__is_wf` (and in the generated `fun_vextunop__/vextbinop__` statements, unchanged).
(E) Step_read_is_wf / Step_is_wf: call sites of `Step_is_wf _ _ _ HWf Hstore H` (OLD hand-edited signature `Step_is_wf (z : state) (admininstr_lst) (var_1 : config) : wf_config (mk_config z admininstr_lst) → Store_ok (fun_store z) → Step … → wf_config var_1`) are at TypeProgress.lean:3855 (unreachable), 4083 and 4093 (if), 4262 (call), 4312 (call_indirect) [other uses outside my files: 7133, 7195, 7422, 7516, 7720, 7785].
    The REGENERATED file has `Step_is_wf (var_0 var_1 : config) : wf_config var_0 → Step var_0 var_1 → wf_config var_1 := sorry` (wasm2.0.lean:13383; no `Store_ok`) and `Step_read_is_wf (var_0 : config) (var_1 : List admininstr) : wf_config var_0 → Step_read var_0 var_1 → Forall … := sorry` (13274), `Step_pure_is_wf` also `sorry` (12879). If the bundle19 signature (with `Store_ok`) is re-applied the call sites stay; if the generated signature is kept they become `Step_is_wf _ _ HWf1 H` and `Hstore` is unused there.
    (my cross-check, static name-based closure in OLD_wasm2.0.lean) proving `Step_read_is_wf` alone does NOT make `Step_is_wf` sorry-free: `Step_pure_is_wf` (hand-proved in OLD) references 29 sorry-bodied theorems and `Step_is_wf` 33 (those + `Step_read_is_wf`, `ibytes__is_wf`, `nbytes__is_wf`, `vbytes__is_wf`):
    convert___is_wf, demote___is_wf, extend___is_wf, fabs__is_wf, fceil__is_wf, ffloor__is_wf, fnearest__is_wf, fneg__is_wf, fsqrt__is_wf, ftrunc__is_wf, iand__is_wf, iandnot__is_wf, ibitselect__is_wf, iclz__is_wf, ictz__is_wf, inot__is_wf, inv_lanes__is_wf, ior__is_wf, ipopcnt__is_wf, irev__is_wf, ishl__is_wf, ishr__is_wf, ixor__is_wf, lanes__is_wf, promote___is_wf, reinterpret___is_wf, trunc___is_wf, trunc_sat___is_wf, wrap___is_wf.
    Checked to be `opaque` ("Axiom Definition", value hidden from the kernel) in the regenerated file: `extend__` (2568), `narrow__` (3899), `inv_ibits_` (3998), `lanes_` (4376), `inv_lanes_` (4391), `irev_` (4097), `ishl_` (3003), `ishr_` (3018); the other functions in the list (fabs_, fceil_, ..., trunc_sat__, wrap__) I did NOT individually check.
    For an opaque function the corresponding `*_is_wf` theorem cannot be proved in Lean, only axiomatised or left `sorry` (the TypeProgress.lean header says the 56 generated numeric ones + `Step_read_is_wf` are `Admitted` in Rocq too). Static analysis only: confirm with `#print axioms`/`#sorry_deps`.
(F) Stuck cases: only C12's `sorry` (A). Nothing else in C01-C13 is a stuck case.
(G) bundle19 wasm2.0 hand edits that C01-C13 depend on (all ABSENT from the regenerated wasm2.0.lean, which has 0 hits for `iswf_`/`bundle19` and 152/152 `*_is_wf` bodies `sorry`, versus 63/152 in OLD):
    - hand-written helper block after `fzero` (OLD_wasm2.0.lean:302-391; four more such blocks at 3042, 5897, 12064, 14017): C03 uses `iswf_Forall_nil`, `iswf_Forall_cons`, `iswf_Forall_getElem!`, `iswf_uN_zero` directly (TypeProgress.lean:4229 etc.); `iswf_uN_of_lt` is needed to re-prove `iadd__is_wf`/`imul__is_wf`.
    - hand-proved generated wf theorems used by these proofs: `testop__is_wf` (C05), `relop__is_wf` (C05), `ine__is_wf` (C07 vvtestop), `iadd__is_wf` (C10, C11), `imul__is_wf` (C11); sorry-free closure for testop/ine/iadd/imul; `relop__is_wf` closure hits the six float comparison wf theorems.
    - `Step_pure_is_wf` and `Step_is_wf` (hand-proved, OLD 14095 and 16064; Store_ok premise on `Step_is_wf`/`Step_read_is_wf`, "moved after `Store_ok`").
    - (my cross-check) Of the 131 `wasm2.0.lean` declarations referenced by the C01-C13 proof bodies, the ones that differ OLD->regenerated are exactly: `Step_is_wf`, `Step_read` (only via the three memory rules, unused here), `fun_vshiftop_`, `ishl_`, `ishr_`, `wf_vcvtop__`; those missing in the regenerated file are `iswf_Forall_cons`, `iswf_Forall_getElem!`, `iswf_Forall_nil`, `iswf_uN_zero`.
    - (my cross-check) All 86 qualified generated constructor names used in the proof bodies exist in the regenerated file with unchanged index numbering (`instr_case_8/9/14/39`, `fun_vextunop___case_3/14`, `fun_vextbinop___case_3/4/14/19`, `ref_is_null_true_0`, `vtestop_true_0`, ...), and all 53 `Instr_ok` rule statements for the C01-C13 range are textually identical OLD vs regenerated; so apart from (A)(B)(E)(G) the logged proofs should elaborate unchanged against the regenerated file (not compiled by me: I ran no Lean).

## 7. Read-only cross-checks I ran (all `python3 -I`/grep/sed on existing files; no writes)
- Compared logged proof bodies with `TypeProgress.lean` (53/53 identical); located target and helper line numbers.
- Compared constructors/declarations referenced by the logged proofs between `OLD_wasm2.0.lean` and the regenerated `wasm2.0.lean` (results in section 6).
- Static name-based closure of sorry-bodied `*_is_wf` theorems from `Step_pure_is_wf`/`Step_is_wf`/the hand-proved wf theorems in `OLD_wasm2.0.lean`.
- Skimmed (not assigned, only for line numbers/context): `wasm2.0.lean`, `OLD_wasm2.0.lean`, `TypeProgress.lean`, `HelperLemmas.lean` (greps), `lakefile.lean`, the scratchpad `safety/verify.sh` and the head/tail of earlier digest logs (convention only), first 40 lines of `scratchpad/logs/prove-stepread.md` (it states the table rules still push `i+1` and are bounded via `Store_ok`, and that `omega` ignores `v_n ≠ 0` at type `n`).

## 8. Safety check (END), verbatim

(Appended below by the final command, which runs the check and tees its output into this file.)

Command: `bash /tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/verify.sh digest-proveC1-end`

```
safety check [digest-proveC1-end] new=/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/safety/check-20261015T052858.828924996Z-digest-proveC1-end-463400.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261015T044132Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
NOTE: entries inside spectec/src/test-lean-claude differ from baseline:
1a2
> ?? spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild
2a4
> ?? spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/
```

(exit code 0)

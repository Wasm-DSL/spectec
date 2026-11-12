# psig-audit-1: independent signature audit of progress chunk 1

**Task.** For each of the 32 Rocq declarations of chunk 1 (`type_progress.v` lines 25-650, `cat_nil` .. `split_vals_inverse`),
check that the translator's (psig-1) Lean signature states the same thing as Rocq: binder order, every premise,
conclusion and quantifiers. Alternatively, check that a NOT PORTED note is justified. Lean was NOT run, as instructed. Nothing was edited
except this log. No scratch files were needed. The scratch dir was created but is empty:
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-audit-1/`.

## Safety check (START), run from `/home/zhengyew/spectec`

```
safety check [psig-audit-1] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113313.927529760Z-psig-audit-1-1429126.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## What I read

- Brief `scratchpad/briefs/progress_sig_brief.md`, task `scratchpad/briefs/task_psig_1.md`.
- Rocq statements `scratchpad/progress/progress_rocq_stmts.md` entries [000]-[044]. Also `type_progress.v:1-60` (header:
  no `Set Implicit Arguments`, so `forall T ...` binders are explicit).
- Rocq `wasm.v`:
  - `list_slice` (57-63)
  - notations `|x|` = `N.of_nat (seq.size x)` and `!(x)` = `the x` (309-310)
  - `binN_scope` `<=` = `N.le` (152)
  - `valtype`, including the bare constructor `BOT` (954)
  - `res_size` (1391), `wf_num_` (1549), `local`/`LOCAL` (3657)
  - `uN`/`iN`/`vN`/`vec_`, `funcaddr`/`hostaddr` = `addr`
  - `wf_val` (13022), `wf_config` (13933), `default_`
- Lean `wasm2.0.lean`:
  - `Forall`/`Forall₂` (17-22), `uN`/`wf_uN` (166-182), `N := Nat` (44)
  - `size` (798), `num_`/`wf_num_` (900-915), `vec_` (964), `«local»` (2239)
  - `ref`/`val` (11305-11320), `wf_val` (11328), `admininstr` constructors
  - `admininstr_instr`/`admininstr_ref`/`admininstr_val` (11642-11730)
  - `config`/`wf_config` (11957-11970), `default_` (11972)
  - `Step_pure.trap_vals` (13744+)
  - `valtype`, `numtype_Inn`, `valtype_{numtype,vectype,reftype}`
- `TypeProgress.lean:8-111` (definitions `is_const`, `const_list`, `terminal_form`, `typeof`, `split_vals`, ...).

## Global checks

- **Coverage.** `type_progress.v` lines 20-651 contain exactly 32 `Lemma`s, the 32 of the task list in this order. The
  translator emits 32 `-- @@` markers in Rocq order: 31 signatures and 1 NOT PORTED. The definitions in the range
  (`is_const`, `const_list`, `terminal_form`, `typeof`, `br_reduce`, ..., `split_vals`) are already in TypeProgress.lean. So are
  the `instr_eqb`/`eqinstrP`/`Instr_ok_ind'` NOT PORTED notes. The Ltac `invert_typeof_vcs` has no Lean counterpart, as expected.
- **Name clashes.** `grep -wF` of all 31 Lean names over every `*.lean` in the target dir (including wasm2.0.lean and
  TypeProgress.lean) gives 0 hits. All names are declared inside `namespace TLC`, so Mathlib/core names such as
  `List.map_eq_nil` cannot clash. `Function.Injective` is available: Mathlib is required, and TypingLemmas.lean:1487 already uses it.
- **Forall2.** Chunk 1 has no `Forall2`/`Forall₂`, so no `hlen` is needed. The unary `Forall` in `default_not_none` is
  the generated `∀ x ∈ l, P x`, which is equivalent to Rocq's inductive `List.Forall`.
- **Opaque functions.** None. `default_`, `size`, `admininstr_val`, `admininstr_instr`, `admininstr_ref`, `typeof`,
  `split_vals` and `const_list` are all plain `def`s, and `wf_uN`, `wf_num_`, `wf_val`, `wf_config` and `Step_pure` are inductives.

## Per-declaration verdicts

| # | Rocq (line) | Lean | Verdict / notes |
|---|---|---|---|
| 1 | `cat_nil` (25) | `cat_nil (T : Type) (s1 s2 : List T)` | OK. T explicit in both. Rocq `T : Type` (any level) vs Lean `Type` (level 0): immaterial here, project convention. |
| 2 | `length_size` (33) | NOT PORTED | OK, justified. In Lean both `length` and `size` are `List.length`, so the statement is `Iff.rfl`. The brief §3 names it explicitly. It is not used anywhere else in the Rocq theories (grep). |
| 3 | `LOCAL_injective` (37) | `Function.Injective «local».LOCAL` | OK. Rocq `LOCAL : valtype -> local` (wasm.v:3658) is the only `LOCAL`. mathcomp `injective` matches `Function.Injective` (strict-implicit binders only). |
| 4 | `default_not_none` (43) | `(ts : List valtype)`, `Forall (· ≠ valtype.BOT)` → `Forall (default_ · ≠ none)` | OK. Rocq `BOT` is the bare valtype constructor. Boolean `!=` maps to `≠` (table), noted in the doc. True in Lean: `default_` is `some` on every constructor except `BOT`. |
| 5 | `wf_config_app` (53) | `(s : state) (ais ais' : List admininstr)`, iff | OK. Both `wf_config` are `wf_state ∧ Forall wf_admininstr`, so the iff is true. |
| 6 | `v_to_e_const` (83) | `const_list (List.map admininstr_val vs) = true` | OK |
| 7 | `const_list_cat` (95) | `= (const_list vs1 && const_list vs2)` | OK. Rocq `&&` (level 40) binds tighter than `=`, so the parenthesisation is right. |
| 8 | `const_list_concat` (104) | two `= true` premises | OK |
| 9 | `const_list_split` (114) | | OK |
| 10 | `const_es_exists` (124) | `∃ vs, es = List.map admininstr_val vs` | DEVIATION, documented and harmless. A sig becomes `∃`, per the brief's table. All 8 Rocq uses (type_progress.v:165, 767, 790, 5405, 5677, 5737, 5880, 6052) only destructure it inside proofs. |
| 11 | `map_eq_nil` (143) | `{A B : Type} (f) (l)` | OK |
| 12 | `map_neq_nil` (151) | | OK |
| 13 | `reduce_trap_left` (159) | `Step_pure (vs ++ [TRAP]) [TRAP]` | OK. Not vacuous: provable from `Step_pure.trap_vals` (`val_lst ≠ [] ∨ ... →`), with the vals from `const_es_exists`. |
| 14 | `v_e_trap` (174) | | OK |
| 15 | `concat_cancel_last` (186) | `{X : Type} (l1 l2) (e1 e2)` | OK |
| 16 | `extract_list1` (197) | | OK |
| 17 | `v_to_e_cat` (206) | folded = unfolded | OK. Same orientation as Rocq. |
| 18 | `be_to_e_cat` (214) | | OK. Same orientation. |
| 19 | `to_e_list_cat` (222) | | OK. Same orientation (unfolded = folded). |
| 20 | `cat_split` (231) | `l1 = List.take l1.length l ∧ l2 = List.drop l1.length l` | OK. mathcomp `take`/`drop`/`size` map to `List.take`/`List.drop`/`length`. |
| 21 | `terminal_form_v_e` (246) | | OK |
| 22 | `typeof_append` (271) | binders `ts t vs`, `∃ v, vs = take ++ [v] ∧ map typeof (take) = ts ∧ typeof v = t` | OK. Precedence checked (`=` looser than `++`, `∧` looser than `=`). |
| 23 | `typeof_cat` (295) | binders `ts1 ts2 vs`, `∃ vs1 vs2, ...` | OK |
| 24 | `invert_typeof_I32` (416) | `∃ v', admininstr_val v = CONST numtype.I32 (mk_num__0 Inn.I32 (mk_uN v'))` | OK. `v' : N` becomes `Nat` (documented). True in Lean: `wf_num_` forces `mk_num__0` with `numtype.I32 = numtype_Inn v_Inn`, hence `Inn.I32`. |
| 25 | `invert_typeof_I64` (434) | | OK. Same as I32. |
| 26 | `invert_typeof_numtype` (452) | `∃ (n : num_), ... = CONST t n` | OK |
| 27 | `invert_typeof_numtype_wf` (467) | `... ∧ wf_num_ t n` | OK |
| 28 | `invert_typeof_V128` (482) | `∃ (c : vec_), ... = VCONST V128 c ∧ wf_uN (Option.get! (size (valtype_vectype V128))) c` | OK. `!(x)` is `the x`, which maps to `Option.get!`, and `res_size` maps to `size`; both documented. `size` is a plain def (`some 128`). `vec_ = vN = iN = uN`, as in Rocq. |
| 29 | `invert_typeof_reftype` (498) | `REF_NULL t ∨ ∃ x, REF_FUNC_ADDR x ∨ REF_HOST_ADDR x` | OK. `∃` scopes over both disjuncts, as in Rocq. A single `x` works for both because `funcaddr = hostaddr = addr = Nat` (abbrevs), as in Rocq. |
| 30 | `invert_typeof_reftype'` (530) | `∃ r, admininstr_val v = admininstr_ref r` | OK |
| 31 | `list_slice_size` (560) | `{T : Type} (bs : List T) (i j : Nat)`, `i + j ≤ bs.length → (List.take j (List.drop i bs)).length = j` | OK. I checked Rocq's Fixpoint `list_slice` (wasm.v:57) case by case: it equals `take j (drop i l)`. `|x|` is `N.of_nat (size x)`, and `%BN` `<=` is Prop `N.le`. All documented. Not a deviation, just the table rule. |
| 32 | `split_vals_inverse` (629) | binders `vs es es'` | OK. Lean `split_vals` (`let p := ...; (_ :: p.1, p.2)`) matches Rocq's `let: (vs', es'') := ...`. |

## Result

- **Problems found: none.** No mismatch, no undocumented deviation, no suspicious statement, no doc-only issue.
- 32/32 declarations verified:
  - 30 are plain OK;
  - 1 is a documented, justified DEVIATION (`const_es_exists`, sig to `∃`);
  - 1 is a justified NOT PORTED (`length_size`).
- I checked each statement that has semantic content against the Lean definitions: `default_not_none`, `wf_config_app`,
  `reduce_trap_left`, the `invert_typeof_*` lemmas and `list_slice_size`. Each is true in Lean, and none is vacuous.
- Minor remark only (not a problem): `cat_nil`, `map_eq_nil`, `concat_cancel_last`, `extract_list1`, `cat_split` and `list_slice_size`
  quantify over `Type` (universe 0), while the Rocq `Type` is universe-generic. This is immaterial for this project and
  follows its convention.

## Safety check (END), run from `/home/zhengyew/spectec`

```
safety check [psig-audit-1] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113833.181503908Z-psig-audit-1-1434109.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

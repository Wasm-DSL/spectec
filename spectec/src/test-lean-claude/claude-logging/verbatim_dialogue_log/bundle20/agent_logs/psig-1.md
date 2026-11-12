# psig-1 log (bundle20 progress port: signature translation, chunk 1 of 6)

## Task

Translate 32 Rocq declarations of `spectec/test-rocq/theories/type_progress.v` (lines 25-650) into
Lean 4 signatures (bodies `sorry`), in Rocq order:
cat_nil, length_size, LOCAL_injective, default_not_none, wf_config_app, v_to_e_const, const_list_cat,
const_list_concat, const_list_split, const_es_exists, map_eq_nil, map_neq_nil, reduce_trap_left,
v_e_trap, concat_cancel_last, extract_list1, v_to_e_cat, be_to_e_cat, to_e_list_cat, cat_split,
terminal_form_v_e, typeof_append, typeof_cat, invert_typeof_I32, invert_typeof_I64,
invert_typeof_numtype, invert_typeof_numtype_wf, invert_typeof_V128, invert_typeof_reftype,
invert_typeof_reftype', list_slice_size, split_vals_inverse

Brief: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/progress_sig_brief.md`
Task file: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/task_psig_1.md`
Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-1/`

Writes allowed: this log file only (inside the repo), plus scratch files in the scratch dir.

## Safety check (START)

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-1`

```
safety check [psig-1] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112642.075481149Z-psig-1-1422370.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Reading

- Read the brief and task file completely.
- Read `TypeProgress.lean` lines 1-200 (style; defs `is_const`, `const_list`, `terminal_form`,
  `typeof`, `split_vals`, ... are in namespace `TLC`; no `open` lines in the file).
- Read the 32 statements from `scratchpad/progress/progress_rocq_stmts.md` (entries [000]-[044]) and
  the original `type_progress.v` lines 1-70, 271-282, 556-566 plus all comment lines in 70-650
  (only TODO/NOTE remarks; none change a statement).
- Confirmed Rocq line numbers of all 32 declarations with `grep -n` (25, 33, 37, 43, 53, 83, 95, 104,
  114, 124, 143, 151, 159, 174, 186, 197, 206, 214, 222, 231, 246, 271, 295, 416, 434, 452, 467,
  482, 498, 530, 560, 629).

### Lean counterparts checked (wasm2.0.lean in the target dir)
- `«local».LOCAL (v_valtype : valtype) : «local»` (line 2240): Rocq `LOCAL`.
- `valtype.BOT` (line 556): Rocq `BOT`; `default_ : valtype → Option val` (line 11972).
- `wf_config : config → Prop` (11964); `config.mk_config : state → List admininstr → config`.
- `Forall` (line 17) is `∀ t_elem ∈ xs, P t_elem`; it has no length subtleties (unary).
- `Step_pure : List admininstr → List admininstr → Prop` (13744).
- `uN.mk_uN (i : Nat)` (166); `num_.mk_num__0 (Inn) (iN)` (901); `vec_ := vN := iN := uN`.
- `size : valtype → Option Nat` (798) is Rocq `res_size`; `valtype_vectype`/`valtype_reftype`
  (568/574); `admininstr.REF_FUNC_ADDR : funcaddr → _`, `REF_HOST_ADDR : hostaddr → _`, both
  `abbrev ... := addr := Nat` (so Rocq's shared `exists x` elaborates in Lean too).
- `admininstr_ref : ref → admininstr` (11714).
- Rocq `list_slice l i j` (wasm.v:57) drops `i` then takes `j`: `List.take j (List.drop i l)`, as
  in the brief's table. There is no Lean `list_slice` def (generated code inlines `List.take`/`List.drop`).
- `((i + j)%BN <= |bs|)%BN`: in `binN_scope` (wasm.v:141-155) `<=` is the Prop `N.le` and `|x|`
  is `N.of_nat (size x)`. Lean: `i + j ≤ bs.length` (Prop; project precedent `i < l.length`).

### Name-clash check
I grepped all 32 names (`-w`) across ExtensionLemmas, HelperLemmas, Subtyping, TypePreservation,
TypePreservationPure, TypeProgress, TypingLemmas and wasm2.0.lean: **0 occurrences**, so no `_p`
suffixes are needed. (Core Lean's `List.map_eq_nil_iff` etc. live in namespace `List`, so there
is no clash with `TLC.map_eq_nil`.)

### Binder explicitness
Rocq binders are mirrored: `cat_nil` has explicit `forall T` → `(T : Type)`. `{X:Type}`/`{A B : Type}`/
`{T : Type}` stay implicit (precedent: `seq_mid_not_null {A : Type}` in TypingLemmas.lean:1550).

## Per-lemma decisions (Rocq order; `-- @@ <name>` merge marker before each block)

| # | Rocq (line) | Lean | Status / note |
|---|---|---|---|
| 1 | `cat_nil` (25) | `cat_nil (T : Type) (s1 s2 : List T)` | OK: Rocq's explicit `forall T` stays explicit |
| 2 | `length_size` (33) | — | **NOT PORTED**: Rocq-only stdlib `length` vs mathcomp `size` bridge. Both are `List.length` in Lean, so the statement is `Iff.rfl` |
| 3 | `LOCAL_injective` (37) | `Function.Injective «local».LOCAL` | OK |
| 4 | `default_not_none` (43) | `Forall (· ≠ valtype.BOT)` → `Forall (default_ · ≠ none)` | OK: bool `!=` rendered as `≠` |
| 5 | `wf_config_app` (53) | `(s : state)`, iff | OK |
| 6 | `v_to_e_const` (83) | `const_list (List.map admininstr_val vs) = true` | OK |
| 7 | `const_list_cat` (95) | Bool equation `= (… && …)` | OK |
| 8 | `const_list_concat` (104) | `= true` premises/conclusion | OK |
| 9 | `const_list_split` (114) | | OK |
| 10 | `const_es_exists` (124) | `∃ vs, es = List.map admininstr_val vs` | **DEVIATION**: Rocq returns `sig` `{vs \| …}`; Lean states `∃` (Prop), per the brief's table |
| 11 | `map_eq_nil` (143) | `{A B : Type} (f) (l)` | OK |
| 12 | `map_neq_nil` (151) | | OK |
| 13 | `reduce_trap_left` (159) | `Step_pure (vs ++ [admininstr.TRAP]) [admininstr.TRAP]` | OK |
| 14 | `v_e_trap` (174) | | OK |
| 15 | `concat_cancel_last` (186) | `{X : Type}` | OK |
| 16 | `extract_list1` (197) | `{X : Type}` | OK |
| 17 | `v_to_e_cat` (206) | | OK |
| 18 | `be_to_e_cat` (214) | `(bes1 bes2 : List instr)` | OK |
| 19 | `to_e_list_cat` (222) | | OK |
| 20 | `cat_split` (231) | `List.take l1.length l` / `List.drop l1.length l` | OK |
| 21 | `terminal_form_v_e` (246) | | OK |
| 22 | `typeof_append` (271) | `List.take ts.length vs ++ [v]` | OK (the Rocq TODO comment proposes an alternative statement; not used) |
| 23 | `typeof_cat` (295) | | OK |
| 24 | `invert_typeof_I32` (416) | `admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v'))` | OK (`v' : N` → `Nat`) |
| 25 | `invert_typeof_I64` (434) | likewise for I64 | OK |
| 26 | `invert_typeof_numtype` (452) | | OK |
| 27 | `invert_typeof_numtype_wf` (467) | `… ∧ wf_num_ t n` | OK |
| 28 | `invert_typeof_V128` (482) | `wf_uN (Option.get! (size (valtype_vectype vectype.V128))) c`, `c : vec_` | OK (`!(res_size …)` → `Option.get! (size …)`) |
| 29 | `invert_typeof_reftype` (498) | `∃ x, … REF_FUNC_ADDR x ∨ … REF_HOST_ADDR x` | OK: `x` elaborates at `funcaddr` (= `hostaddr` = `addr` = `Nat`), as in Rocq |
| 30 | `invert_typeof_reftype'` (530) | `∃ r, admininstr_val v = admininstr_ref r` | OK |
| 31 | `list_slice_size` (560) | `i + j ≤ bs.length → (List.take j (List.drop i bs)).length = j` | OK: `list_slice` → take/drop (brief table), `binN` `<=` is Prop `N.le` |
| 32 | `split_vals_inverse` (629) | | OK |

None of the 32 statements uses `Forall2`, so no `hlen` deviations were needed. No name clashes,
so no `_p` suffixes. Not in this chunk (and already handled in TypeProgress.lean by the main
thread): `is_const`, `const_list`, `terminal_form`, `typeof`, `invert_typeof_vcs` (Ltac),
`instr_eqb`, `eqinstrP`, `Instr_ok_ind'`, `br_reduce`, `return_reduce`, `not_lf_br`,
`not_lf_return`, `split_vals`.

## Lean check

Scratch file: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-1/Chunk.lean`
Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <Chunk.lean>`

The first attempt compiled cleanly: exit 0, **31** `declaration uses 'sorry'` warnings (31 theorems;
`length_size` NOT PORTED) and **no errors or other diagnostics**. Last lines of the output:
```
.../agents/psig-1/Chunk.lean:205:8: warning: declaration uses `sorry`
.../agents/psig-1/Chunk.lean:215:8: warning: declaration uses `sorry`
.../agents/psig-1/Chunk.lean:223:8: warning: declaration uses `sorry`
.../agents/psig-1/Chunk.lean:230:8: warning: declaration uses `sorry`
```
A separate scratch probe (`Probe.lean` = chunk + `#check`s, one Lean process at a time) confirmed the
elaborated forms:
```
invert_typeof_reftype : ∀ (v : val) (t : reftype),
  typeof v = valtype_reftype t →
    admininstr_val v = admininstr.REF_NULL t ∨
      ∃ x, admininstr_val v = admininstr.REF_FUNC_ADDR x ∨ admininstr_val v = admininstr.REF_HOST_ADDR x
cat_nil : ∀ (T : Type) (s1 s2 : List T), s1 ++ s2 = [] ↔ s1 = [] ∧ s2 = []
const_es_exists : ∀ (es : List admininstr), const_list es = true → ∃ vs, es = List.map admininstr_val vs
@list_slice_size : ∀ {T : Type} (bs : List T) (i j : ℕ), i + j ≤ bs.length → (List.take j (List.drop i bs)).length = j
```
I also confirmed that Rocq `valtype_I32`/`valtype_I64`/`valtype_V128`/`BOT` are `valtype` constructors
(wasm.v:947-954), so `valtype.I32` etc. are exact.

## Safety check (END)

```
safety check [psig-1] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113139.523423421Z-psig-1-1428592.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written: this log (inside the target dir); `Chunk.lean`, `Probe.lean`, `check1.txt` in the
scratch dir only. No repo file was edited, no `lake build`, and no git state changes.

# psig-3 — bundle20 progress port: signature translation, chunk 3 of 6

## Task

Translate the 32 Rocq declarations of `spectec/test-rocq/theories/type_progress.v` lines 1280-1759
(`lookup_types` ... `binop_before`; the two `Ltac`s `num_shapes`/`binop_wf` in that range are not
in the task list) into Lean 4 signatures with `sorry` bodies, in a scratch `Chunk.lean` that imports
`TypeProgress`, with `-- @@ <rocq_name>` merge markers. No repo file is edited; the main thread merges.

- Brief: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/progress_sig_brief.md`
- Task file: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/task_psig_3.md`
- Scratch file: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-3/Chunk.lean`

## Safety check (START), verbatim

```
safety check [psig-3] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112641.408650526Z-psig-3-1422194.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## What I read

- The brief and task file (fully).
- `progress_rocq_stmts.md` entries [076]-[109]; `type_progress.v` 1270-1380, 1608-1640, 1735-1760
  (statements, comments, `binop_before` proof), plus the comment lines in 1376-1760.
- `TypeProgress.lean` 1-200 (definitions `typeof` etc., style).
- `wasm2.0.lean`: `Forall`/`Forall₂` (17-22), `list_` (84), `uN`/`wf_uN`/`proj_uN_0` (166-180),
  `valtype` (548, has `BOT`), `num_`/`wf_num_` (900-915), `fun_signed_`/`fun_inv_signed_` (2659-2677),
  `fun_idiv_` (3099), `fun_binop__before_fun_binop__case_38` (3263, same shape as Rocq wasm.v:4733),
  `moduleinst`/`frame`/`context` structures, `Moduleinst_ok` (15671).
- Rocq `wasm.v`: `res_N := N` (342), types of `fun_signed_`, `fun_inv_signed_`, `fun_idiv_`,
  `fun_irem_`, `fun_i{lt,gt,le,ge}_`, `fun_binop_`, `fun_relop_`, `fun_cvtop__` (all match Lean's).
- `HelperLemmas.lean:772-779` (`truncz_quot`: project precedent `Z.quot` ↦ `Int.tdiv`).
- `TypingLemmas.lean:57` (`upd_local_label_return`).

## Facts established before writing

- No name clashes: none of the 32 names is declared in any project `.lean` file (grep over
  `theorem|lemma|def|abbrev|axiom|inductive|structure|opaque|instance`); there is no root `typeof`
  in `wasm2.0.lean`, so `typeof` resolves to `TLC.typeof`.
- Lean's generated `Moduleinst_ok` carries explicit `List.length funcaddr_lst = List.length
  functype_F_lst` premises, so `funcs_size` needs no extra `hlen` (no `Forall₂` in its statement).
- Mathlib is imported transitively (`HelperLemmas` imports `Mathlib.Tactic`), so `|a|` is available.
- Scope keys in `type_progress.v`: after mathcomp's `ssrnat`, `%num`/`%BN` denote binary `N`, `%N`
  denotes `nat`; all map to Lean `Nat`. Rocq `res_N` (= `N`) is written `N` (Lean `abbrev N := Nat`,
  the type the generated `wf_uN`/`fun_signed_` use; project precedent `(v_N : N)`).

## Per-lemma decisions

All 32 declarations are PORTED (no NOT PORTED, no forced deviation; no statement in this chunk
mentions `Forall₂`, so the zip-based `Forall₂` length issue does not arise). Representational
choices (translation-table mappings, not deviations) are recorded in each doc comment.

| # | Rocq (line) | Lean | Status / notes |
|---|---|---|---|
| 076 | `lookup_types` (1280) | `lookup_types` | OK. `lookup_total l idx` ↦ `l[idx]!`; `context_TYPES`/`TYPES (frame_MODULE f)` ↦ `.TYPES`/`f.MODULE.TYPES`. |
| 077 | `funcs_size` (1290) | `funcs_size` | OK. `\|l\|` ↦ `.length`. Lean's `Moduleinst_ok` has explicit `funcaddr_lst.length = functype_F_lst.length`, so no `hlen` needed. |
| 078 | `admininstr_CONST_eq_arg` (1300) | same | OK. `t : numtype`, `i1 i2 : num_` (inferred types). |
| 079 | `typeof_non_bot` (1308) | same | OK. `typeof` = `TLC.typeof` (no root `typeof` exists). |
| 080 | `typeof_vals_non_bot` (1317) | same | OK. mathcomp `map` ↦ `List.map`; `Forall` (unary). |
| 081 | `unop_not_none` (1333) | same | OK. `fun_unop_` is a `def` returning `Option (List num_)`; `<> None` ↦ `≠ none`. |
| 082 | `two_pow_pos` (1348) | same | OK. Binary `N` ↦ `Nat`. |
| 083 | `Zsub1_toN` (1351) | same | OK. Kept (Int/Nat bridging is meaningful in Lean: the generated code uses `Int.toNat ((v_N : Int) - (1 : Int))`). `Z.to_N` ↦ `Int.toNat`; Rocq's `(1%num : Z)` (convertible to `1%Z`) written `(1 : Int)`, the generated Lean form — noted in the doc comment. |
| 084 | `wf_uN_lt` (1357) | same | OK. `res_N` ↦ `N`; `i : Nat`. |
| 085 | `two_pow_succ` (1368) | same | OK. Truncated `m - 1` as `N.sub`. |
| 086 | `signed_total` (1376) | same | OK. `((2 ^ (v_N - 1) : N) : Z)` ↦ `((2 ^ (v_N - 1) : Nat) : Int)`; `0 - x` kept (not `-x`). |
| 087 | `invsigned_total` (1405) | same | OK. Same casts as 086. |
| 088 | `Zquot_abs_le` (1425) | same | OK. `Z.abs` ↦ Mathlib `\|·\|`; `Z.quot` ↦ `Int.tdiv` (project precedent `truncz_quot`, HelperLemmas.lean:772-779). |
| 089 | `Zquot_ge_inv` (1435) | same | OK. As 088; `(-1)%Z` ↦ `-1`, `(- p)%Z` ↦ `-p`. |
| 090 | `wf_uN_lt'` (1456) | `wf_uN_lt'` | OK. Coercion `(u :> N)` (instance `proj_uN_0_coercion`) ↦ `proj_uN_0 u`. |
| 091 | `signed_nonzero` (1459) | same | OK. |
| 092 | `lt_wf_uN` (1467) | same | OK. Rocq infers binary `N` for `v_N` here (first use is `2%num ^ v_N`), so binder is `(v_N : Nat)`; identical type to `N` in Lean. |
| 093 | `inv_signed_wf` (1475) | same | OK. |
| 094 | `idiv_total` (1485) | same | OK. `(i1 i2 : uN)` as Rocq writes them. |
| 095 | `irem_total` (1535) | same | OK. |
| 096-099 | `ilt_total`/`igt_total`/`ile_total`/`ige_total` (1562/1572/1582/1592) | same | OK. Inferred binder types: `v_N : N`, `v_sx : sx`, `i1 i2 : uN` (first use in `wf_uN`). |
| 101 | `idiv_wf` (1612) | same | OK. `List.Forall` ↦ `Forall`; `option_to_list` ↦ `Option.toList`; `a b : iN`, `r : Option iN`. |
| 102 | `wf_uN_mk_proj` (1621) | same | OK. `(x :> N)` ↦ `proj_uN_0 x`. |
| 103 | `wf_fN_num_` (1624) | same | OK. `mk_num__1` ↦ `num_.mk_num__1`. |
| 104 | `wf_opt_num_` (1629) | same | OK. `option_map` ↦ `Option.map`; `list_ num_` (Lean `list_ (X : Type)`). |
| 106 | `binop_total` (1663) | same | OK. |
| 107 | `relop_total` (1691) | same | OK. |
| 108 | `cvtop_total` (1715) | same | OK. |
| 109 | `binop_before` (1735) | same | OK. Checked Lean `fun_binop__before_fun_binop__case_38` (wasm2.0.lean:3263) has the same constructors as Rocq's (wasm.v:4733), and that `fun_binop__case_38` is the `¬ before → none` catch-all. |

(The `Ltac`s `num_shapes` (1602) and `binop_wf` (1641) are in the line range but not in this
chunk's declaration list; nothing was emitted for them.)

## Lean check

Command (one run; no `lake build`, nothing written to `.lake/`):

```
cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-3/Chunk.lean
```

Result: exit 0; output is exactly 32 lines, all `declaration uses \`sorry\`` warnings (one per
theorem), no errors. Last lines:

```
.../agents/psig-3/Chunk.lean:188:8: warning: declaration uses `sorry`
.../agents/psig-3/Chunk.lean:195:8: warning: declaration uses `sorry`
.../agents/psig-3/Chunk.lean:202:8: warning: declaration uses `sorry`
.../agents/psig-3/Chunk.lean:210:8: warning: declaration uses `sorry`
```

`-- @@` markers: 32, in Rocq order (verified by grep).

## Safety check (END), verbatim

```
safety check [psig-3] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113326.142333151Z-psig-3-1429418.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written by psig-3: this log (inside the target dir) and, outside the repo, the scratch files
`agents/psig-3/Chunk.lean` and `agents/psig-3/check1.txt` in the session scratchpad. No repo file
edited, no git state change, no agents spawned.

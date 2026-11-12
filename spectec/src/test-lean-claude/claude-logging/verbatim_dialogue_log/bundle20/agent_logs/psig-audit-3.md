# psig-audit-3: independent signature audit of progress chunk 3

## Task

Independent SIGNATURE AUDIT of the translator's (psig-3) Lean output for chunk 3 of
`spectec/test-rocq/theories/type_progress.v` (lines 1280-1759, 32 declarations: lookup_types ..
binop_before). For each Rocq declaration, check that the Lean signature states the same thing
(binder order, premises, conclusion, quantifiers), and flag mismatch / undocumented-deviation /
suspicious / doc-only. No Lean runs; no repo edits besides this log.

## Safety check (START)

```
safety check [psig-audit-3] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113859.116483595Z-psig-audit-3-1434407.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## What I read

- Brief: scratchpad/briefs/progress_sig_brief.md
- Task: scratchpad/briefs/task_psig_3.md
- Rocq statements: scratchpad/progress/progress_rocq_stmts.md entries [076]-[109]; cross-checked the
  original text in type_progress.v (1280-1300, 1348-1480, 1612-1632, 1735-1738): extraction exact.
- Lean side (grep/sed ranges only): wasm2.0.lean `Forall`/`Forall₂`/`Map`/`OMap` (17-36), `list_` (84),
  `uN`/`proj_uN_0`/`wf_uN` (166-180), `fN`/`wf_fN` (277-290), `sizenn` (853), `wf_num_` (906),
  `wf_unop_` (1034), `fun_signed_`/`fun_inv_signed_` (2659-2675), `truncz` (2652, opaque),
  `fun_unop_` (2875), `fun_idiv_` (3099), `fun_irem_` (3147), `fun_ige_` (3697),
  `fun_binop__before_fun_binop__case_38` (3263), `fun_binop_` (3411), `fun_relop_` (3814),
  `fun_cvtop__` (4038), `Moduleinst_ok` (15671-15740), `context`/`moduleinst` fields (11375);
  TypeProgress.lean `typeof` (66); TypingLemmas.lean `upd_local_label_return` (57);
  HelperLemmas.lean `truncz_quot` axiom (778). Rocq wasm.v counterparts: `fun_unop_` (4352),
  `fun_signed_`/`fun_inv_signed_` (4202-4217), `fun_idiv_` (4534), before-pred (4733), `fun_binop_`
  (4880), `fun_relop_` (5285), `fun_cvtop__` (5494), `ior__is_wf` (4579, Admitted), `truncz` (4199,
  Axiom); axioms.v `truncz_quot` (38).

## Key definition cross-checks (Lean vs Rocq generated code)

| item | Rocq | Lean | verdict |
|---|---|---|---|
| `fun_unop_` result | `option (seq num_)`, 22 Some-cases + `None` | `Option (List num_)`, same 22 cases + `none` | same |
| `fun_signed_`/`fun_inv_signed_` | 2 clauses each, `(v_N - 1)` via `Z.to_N` | 2 clauses each, `Int.toNat ((v_N:Int) - 1)` | same |
| `fun_idiv_` | 5 clauses; case_1/case_4 carry result wf; case_3 Q-`==` | 5 clauses; same wf premises; case_3 Rat `=` (normalized Rat, so = Qeq) | same |
| `truncz` | `Axiom` + `truncz_quot` (axioms.v:38) | `opaque` + `axiom truncz_quot` (HelperLemmas:778) | same trust base |
| `fun_binop__before_..._case_38` | 38 ctors, 68 premise lines | 38 ctors, 68 premise lines | same |
| `fun_binop_` | 39 ctors, 69 premise lines, case_38 `~before` | 39 ctors, 69 premise lines, case_38 `¬ before` | same |
| `fun_relop_` / `fun_cvtop__` | 25 / 37 ctors, 9 / 25 premise lines | 25 / 37 ctors, 9 / 25 premise lines | same |
| opaque int/float ops `_is_wf` | `Axiom op` + `Lemma ... Admitted` | `opaque op` + `theorem ... := sorry` | same trust base |
| `Moduleinst_ok` | Forall2 (inductive) | explicit `funcaddr_lst.length = functype_F_lst.length` premise + zip Forall₂; `C.TYPES = mi.TYPES = functype_lst` | funcs_size/lookup_types true without hlen |
| `wf_uN N (mk_uN i)` | `i <= Z.to_N (2^N - 1)` | `i ≤ Int.toNat (2^N - 1)` (⇔ `i < 2^N`) | same |
| `(u :> N)` | instance `proj_uN_0_coercion` (wasm.v:529) | `proj_uN_0 u` | same |
| `Z.abs`, `Z.quot` | stdlib | Mathlib `|·|` (HelperLemmas imports Mathlib.Tactic), `Int.tdiv` (T-rounding) | same |

## Per-declaration verdicts (32/32 OK, 0 problems)

| # | Rocq (line) | verdict | note |
|---|---|---|---|
| 1 | lookup_types (1280) | OK | binders s f C loc lab ret idx; `lookup_total` -> `[idx]!` both sides `List functype` |
| 2 | funcs_size (1290) | OK | no hlen needed: Lean Moduleinst_ok has explicit length premise (verified); doc claim correct |
| 3 | admininstr_CONST_eq_arg (1300) | OK | |
| 4 | typeof_non_bot (1308) | OK | `typeof` (TypeProgress:66) identical to Rocq 262 |
| 5 | typeof_vals_non_bot (1317) | OK | |
| 6 | unop_not_none (1333) | OK | fun_unop_ bodies identical |
| 7 | two_pow_pos (1348) | OK | |
| 8 | Zsub1_toN (1351) | OK | `(1%num:Z)` -> `(1:Int)`, documented, defeq |
| 9 | wf_uN_lt (1357) | OK | |
| 10 | two_pow_succ (1368) | OK | truncated `m - 1` both sides |
| 11 | signed_total (1376) | OK | N->Z cast as `((… : Nat) : Int)`; `0 - x` kept |
| 12 | invsigned_total (1405) | OK | |
| 13 | Zquot_abs_le (1425) | OK | |
| 14 | Zquot_ge_inv (1435) | OK | `(-1)%Z`, `(-p)%Z` -> `-1`, `-p` |
| 15 | wf_uN_lt' (1456) | OK | |
| 16 | signed_nonzero (1459) | OK | |
| 17 | lt_wf_uN (1467) | OK | cosmetic: `(v_N : Nat)` where siblings write `(v_N : N)`; `abbrev N := Nat`, identical |
| 18 | inv_signed_wf (1475) | OK | |
| 19 | idiv_total (1485) | OK | provable from truncz_quot exactly as in Rocq |
| 20 | irem_total (1535) | OK | same |
| 21-24 | ilt/igt/ile/ige_total (1562-1592) | OK | relations `N → sx → iN → iN → u32 → Prop`, both sides |
| -- | num_shapes (Ltac 1602) | n/a | tactic; nothing to port (not in chunk list) |
| 25 | idiv_wf (1612) | OK | doc "no generated `_is_wf`" verified: no `idiv__is_wf` in either file |
| 26 | wf_uN_mk_proj (1621) | OK | |
| 27 | wf_fN_num_ (1624) | OK | |
| 28 | wf_opt_num_ (1629) | OK | `Option.map` vs generated premises' `OMap` (wasm2.0:35, `o.map f`): defeq |
| -- | binop_wf (Ltac 1641) | n/a | tactic; nothing to port |
| 29 | binop_total (1663) | OK | `lst : Option (List num_)` both sides |
| 30 | relop_total (1691) | OK | `c : Option num_` both sides |
| 31 | cvtop_total (1715) | OK | `c2 : Option (List num_)` both sides |
| 32 | binop_before (1735) | OK | before-predicate structurally identical (38 ctors) |

Name clashes: grep of all 32 names as declarations across wasm2.0.lean and the 7 project files: none.
No Forall2 appears in any chunk statement, so no hlen question arises.

## Result

32/32 declarations OK; 0 mismatch, 0 undocumented-deviation, 0 suspicious, 0 doc-only. Lean was NOT
run (audit by reading only). Repo files edited: none besides this log. Scratch files only under
scratchpad/agents/psig-audit-3/ (extracted relation bodies for constructor/premise counting).

## Safety check (END)

```
safety check [psig-audit-3] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T114453.852916928Z-psig-audit-3-1436860.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

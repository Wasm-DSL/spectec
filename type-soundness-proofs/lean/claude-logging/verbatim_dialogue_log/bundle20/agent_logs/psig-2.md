# psig-2 log (bundle20 progress port: signature translation, chunk 2 of 6)

## Task
Translate 31 Rocq declarations of `spectec/test-rocq/theories/type_progress.v` (lines 652-1278) into
Lean 4 signatures (bodies `sorry`), in Rocq order:
split_vals_prefix, br_reduce_decidable, return_reduce_decidable, not_br_reduce_not_lf_br,
not_return_reduce_not_lf_return, not_lf_br_singleton, not_lf_return_singleton, not_lf_br_right,
not_lf_br_left, not_lf_return_right, not_lf_return_left, Forall2_Val_ok_is_same_as_map,
frame_t_context_local_types, frame_t_context_label_empty, wf_forall_admin_val, wf_forall_admin,
wf_config_label, wf_config_frame, frame_t_context_return_empty, Admin_instrs_ok_cons,
Admin_instrs_ok_cat, Admin_instrs_ok_all, s_typing_lf_br', s_typing_lf_br, s_typing_lf_return,
s_typing_not_lf_br', s_typing_not_lf_br, s_typing_not_lf_return, size_eq1_cat, br_reduce_extract_vs,
return_reduce_extract_vs

Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-2/`
Only files written: this log + scratch files in the scratch dir. No repo file edited.

## Start safety check (verbatim)
```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-2
safety check [psig-2] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112641.404113995Z-psig-2-1422187.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Read
- Brief `briefs/progress_sig_brief.md` (full), task file `briefs/task_psig_2.md`.
- Statements: `progress/progress_rocq_stmts.md` entries [045]-[075]; original `type_progress.v`
  (sed ranges 640-666, 666-716, 795-830, 892-896, 972-976, 1009-1013, 1159-1175, 1221-1240; comment
  lines in 652-1278). Rocq import order (line 1-12): mathcomp `ssrbool` is imported last.
- `TypeProgress.lean` 1-200 (defs/style) and 225-250 (`t_progress_e_P1` precedent for `|ts|`).
- wasm2.0.lean: `Forall`/`Forall₂` (17/20), `abbrev n := Nat` (50), `list` wrapper (127),
  `uN` (166), `labelidx := idx := u32 := uN`, `resulttype := list valtype` (618), `context` (12623),
  `admininstr` ctors `BR`/`RETURN`/`LABEL_ (v_n : n) instrs admininstrs`/`FRAME_ (v_n : n) frame
  admininstrs` (11570-11636), `state`/`config` (11547/11957), `Val_ok` (15597), `Frame_ok` (15743:
  carries an explicit `t_lst.length = val_lst.length` premise), `Instr_ok2`/`Instrs_ok2` (15785/15874).
- HelperLemmas.lean:599 `prepend_return`; Subtyping.lean:32 `mkFunctype`; ExtensionLemmas.lean:1077
  `funcinst_same` (hlen precedent); TypePreservation.lean:871-875 (`wf_config_frame` renamed to
  `wf_config_wf_frame` in bundle20, freeing the name).
- Rocq `typing_lemmas.v:17` native coercion `fun_res_list__list : res_list >-> list`, so Rocq's
  `|ts|` / `size t` on a `resulttype` is the underlying list's length = Lean `(proj_list_0 valtype ts).length`.

## Name-clash check
grep over all project `*.lean` + wasm2.0.lean for each of the 31 names: no existing declaration.
`wf_config_frame` was already freed (TypePreservation.lean:871-875). Confirmed by the clean Lean check.

## Per-lemma decisions (all 31 ported; none NOT PORTED)
Style: Rocq `forall` binders → explicit Lean binders, premises → `→` in Rocq order; Rocq's
right-assoc `++` kept with explicit parentheses; `is_true b` → `b = true`; `(ts1 :-> ts2)` →
`mkFunctype ts1 ts2`; `lookup_total l 0` → `l[0]!`; `\in` → `∈`.

| Rocq (line) | Lean | Decision |
|---|---|---|
| split_vals_prefix (652) | theorem | OK; `~is_const e` → `¬ (is_const e = true)` |
| br_reduce_decidable (666) | **def** | DEVIATION: Rocq `decidable` here is ssrbool's sumbool `{P}+{~P}` (ssrbool imported last; Stdlib `Decidable` not imported); exact Lean counterpart is `Decidable P` (Type), hence `def` not `theorem`; ctor order `isFalse`/`isTrue`. Not an instance. If later proved classically it needs `noncomputable` (Rocq's proof is constructive via `split_vals`). Alternative if main thread prefers uniform theorems: `br_reduce es ∨ ¬ br_reduce es` (weaker). |
| return_reduce_decidable (692) | **def** | DEVIATION: same as above |
| not_br_reduce_not_lf_br (717) | theorem | OK |
| not_return_reduce_not_lf_return (725) | theorem | OK |
| not_lf_br_singleton (733) | theorem | OK (`l : labelidx`) |
| not_lf_return_singleton (741) | theorem | OK |
| not_lf_br_right (749) | theorem | OK |
| not_lf_br_left (760) | theorem | OK; `const_list es1 = true` |
| not_lf_return_right (772) | theorem | OK |
| not_lf_return_left (783) | theorem | OK; `const_list es1 = true` |
| Forall2_Val_ok_is_same_as_map (795) | theorem | DEVIATION: + `v_t1.length = v_local_vals.length →` right after the `Forall₂` premise (zip-based `Forall₂`; conclusion is a list equality, false without it, e.g. `v_t1=[t,t']`, `vals=[v]`). |
| frame_t_context_local_types (808) | theorem | OK (Lean `Frame_ok` already has the length premise, so no hlen) |
| frame_t_context_label_empty (819) | theorem | OK |
| wf_forall_admin_val (829) | theorem | OK (eta-expanded lambdas kept as in Rocq) |
| wf_forall_admin (846) | theorem | OK |
| wf_config_label (857) | theorem | OK (`s : state`, `n : n`) |
| wf_config_frame (870) | theorem | OK (name freed in bundle20; distinct from `wf_config_wf_frame`) |
| frame_t_context_return_empty (885) | theorem | OK (`C.RETURN = none`) |
| Admin_instrs_ok_cons (895) | theorem | OK (`[e] ++ es` kept literally) |
| Admin_instrs_ok_cat (912) | theorem | OK |
| Admin_instrs_ok_all (949) | theorem | OK (`e \in es` → `e ∈ es`) |
| s_typing_lf_br' (972) | theorem | OK |
| s_typing_lf_br (1009) | theorem | OK (`rt : resulttype`, `prepend_return` from HelperLemmas) |
| s_typing_lf_return (1045) | theorem | OK |
| s_typing_not_lf_br' (1072) | theorem | OK |
| s_typing_not_lf_br (1094) | theorem | OK |
| s_typing_not_lf_return (1116) | theorem | OK |
| size_eq1_cat (1137) | theorem | OK (`(A : Type)` explicit as in Rocq; `|l|` → `.length`) |
| br_reduce_extract_vs (1159) | theorem | OK (`ts : resulttype`; `lookup_total (LABELS C) 0` → `C.LABELS[0]!`; `|vcs2| = |ts|` → `vcs2.length = (proj_list_0 valtype ts).length`; `mk_uN 0` → `uN.mk_uN 0`) |
| return_reduce_extract_vs (1221) | theorem | OK (`size vcs2 = size t` → `vcs2.length = (proj_list_0 valtype t).length`) |

## Lean check
Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/psig-2/Chunk.lean`
- Run 1 (Chunk.lean): exit 0, 0 errors, 31 output lines, all `declaration uses \`sorry\`` (one per declaration). Last lines:
```
.../psig-2/Chunk.lean:235:8: warning: declaration uses `sorry`
.../psig-2/Chunk.lean:246:8: warning: declaration uses `sorry`
.../psig-2/Chunk.lean:262:8: warning: declaration uses `sorry`
```
- Run 2 (ChunkStrict.lean = same text plus `set_option autoImplicit false` before `namespace TLC`, to rule
  out silently auto-bound identifiers since the lakefile leaves autoImplicit on): exit 0, 0 errors, 31 sorry warnings only.
- Marker order check: the 31 `-- @@` markers and the 31 declaration names equal the task's list, in order.

## End safety check (verbatim)
```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-2
safety check [psig-2] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113439.594425750Z-psig-2-1430682.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Result
31/31 declarations translated (29 OK, 2 `def` sumbool deviations, 1 hlen deviation); no NOT PORTED.
Scratch outputs: `<scratch>/agents/psig-2/Chunk.lean` (returned text), `ChunkStrict.lean`, `check1.txt`, `check_strict.txt`.
No repo file other than this log was written; no git state-changing commands; no agents spawned.

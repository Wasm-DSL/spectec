# psig-audit-2 — independent SIGNATURE AUDIT of progress chunk 2 (bundle20)

## Task
Audit the translator's (psig-2) Lean signatures for the 31 Rocq declarations of
`spectec/test-rocq/theories/type_progress.v` lines 652-1278 (split_vals_prefix ... return_reduce_extract_vs).
For each: does the Lean signature state the same thing as Rocq (binder order, premises, conclusion,
quantifiers), or is a deviation justified/documented? Flag mismatch / undocumented-deviation /
suspicious / doc-only. Read-only audit; no Lean runs; no repo edits except this log.

## Safety check (START)
```
safety check [psig-audit-2] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T114522.471671328Z-psig-audit-2-1437025.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## What I read
- briefs/progress_sig_brief.md, briefs/task_psig_2.md
- scratchpad/progress/progress_rocq_stmts.md entries [045]-[075]; cross-checked the originals in
  `spectec/test-rocq/theories/type_progress.v` (652-1278; the blanked comments are only TODOs). An awk scan of
  640-1280 lists exactly the 31 Lemmas of the chunk, so nothing is missing, and they are in Rocq order.
- TypeProgress.lean 1-250 (is_const, const_list, terminal_form, typeof, br_reduce, return_reduce, not_lf_br,
  not_lf_return, split_vals, the motives).
- wasm2.0.lean: Forall/Forall₂ (17-21, zip-based), list/proj_list_0 (127-135), resulttype := list valtype (618),
  admininstr (11562; LABEL_ : n → List instr → List admininstr, FRAME_ : n → frame → List admininstr),
  admininstr_val (11721), admininstr_instr (11642: BR↦BR, RETURN↦RETURN), wf_val (11328), wf_admininstr
  (11730; cases 13/20/40/68/69 = wf_val cases; 71 LABEL_ = Forall wf_instr ∧ Forall wf_admininstr; 72 FRAME_
  = wf_frame ∧ Forall wf_admininstr), wf_state (11554), wf_config (11964), context + append_context (12623-12652;
  fieldwise ++, RETURN := orElse), Resulttype_sub (12735, HAS length premise), Instr_ok br/return (12947/12982),
  Val_ok/Ref_ok (15597/15582: exact types, no subsumption), Moduleinst_ok conclusion (LOCALS/LABELS = [],
  RETURN = none), Frame_ok (15743: HAS `List.length t_lst = List.length val_lst`; conclusion
  `{LOCALS := t_lst, LABELS := [], RETURN := none} ++ C`), Instr_ok2/Instrs_ok2/Expr_ok2 (15784-15915:
  plain/label/frame/call_addr/ref/trap; empty/instr/seq/sub/frame).
- Subtyping.lean:32 `mkFunctype t1 t2 = functype.mk_functype (.mk_list t1) (.mk_list t2)` = Rocq `:->`
  (typing_lemmas.v:23 / subtyping.v:8, `mk_functype (mk_list _ tf1) (mk_list _ tf2)`).
- HelperLemmas.lean:599 `prepend_return` = Rocq helper_lemmas.v:485 (`{…; RETURN := Some v_t} @@ v_C`).
- Rocq `decidable`: type_progress.v:13 imports mathcomp ssrbool LAST; mathcomp ssreflect/ssrbool.v:2 is
  `From Corelib Require Export ssrbool.`, and Corelib ssr/ssrbool.v:597 is `Definition decidable P := {P} + {~ P}.`
  (sumbool). Stdlib Logic/Decidable.v:24 (`P \/ ~ P`) is shadowed in any case. So the translator's reading is correct.
- Rocq `|x|` = `N.of_nat (seq.size x)` (wasm.v:309). On `ts : resulttype = res_list valtype` it typechecks via the
  global native coercion `fun_res_list__list : res_list >-> list` (typing_lemmas.v:17, `match x with mk_list l => l`),
  which is definitionally Lean's `proj_list_0 valtype`. `size` in type_progress.v is mathcomp `seq.size` (seq is
  imported last). Lean's `size` is the generated `valtype → Option Nat`, which the translator correctly did NOT use.
- Name clashes: grepped every chunk name in all project .lean files and wasm2.0.lean: none. `wf_config_frame`
  is free (TypePreservation.lean:872-874 renamed the Lean-only helper to `wf_config_wf_frame`). TypeProgress.lean
  does not yet contain any of the names. No `open List` and no shadowing `Forall` def in the project.

## Per-declaration audit (Rocq line → verdict)
| # | Rocq (line) | Verdict | Notes |
|---|---|---|---|
| 1 | split_vals_prefix (652) | OK | binders vs e es; `~is_const e` → `¬(is_const e = true)`; right-assoc `++` kept; true in Lean (admininstr_val/split_vals constructor-for-constructor inverse). |
| 2 | br_reduce_decidable (666) | OK (documented, justified deviation) | Rocq `decidable` = ssrbool sumbool (verified on disk). `def … : Decidable (br_reduce es)` is the exact counterpart; def-not-theorem is forced. Constructor-order note is correct (Lean isFalse/isTrue). |
| 3 | return_reduce_decidable (692) | OK (documented, justified deviation) | same as #2. |
| 4 | not_br_reduce_not_lf_br (717) | OK | |
| 5 | not_return_reduce_not_lf_return (725) | OK | |
| 6 | not_lf_br_singleton (733) | OK | l : labelidx inferred from admininstr_BR. |
| 7 | not_lf_return_singleton (741) | OK | |
| 8 | not_lf_br_right (749) | OK | |
| 9 | not_lf_br_left (760) | OK | `const_list es1` → `= true`. |
| 10 | not_lf_return_right (772) | OK | |
| 11 | not_lf_return_left (783) | OK | |
| 12 | Forall2_Val_ok_is_same_as_map (795) | OK (documented, justified deviation) | Lambda kept literally (`fun v s => Val_ok v_S s v`; v ranges over valtypes, s over vals). hlen is forced: without it the counterexample v_t1=[t,t'], vals=[v] makes the zip-Forall₂ hold and the list equality false. The Rocq proof inducts on the inductive Forall2, which carries the lengths. hlen is placed right after the Forall₂ premise and documented. |
| 13 | frame_t_context_local_types (808) | OK | Verified that Lean Frame_ok carries `length t_lst = length val_lst`, so no hlen is needed and the statement is true in Lean. |
| 14 | frame_t_context_label_empty (819) | OK | true in Lean: [] ++ (Moduleinst_ok C).LABELS = []. |
| 15 | wf_forall_admin_val (829) | OK | The iff holds in Lean (wf_admininstr's value cases mirror wf_val exactly). |
| 16 | wf_forall_admin (846) | OK | |
| 17 | wf_config_label (857) | OK | s : state (mk_config takes a state); `(n : n)` resolves the type before binding. |
| 18 | wf_config_frame (870) | OK | binder order s f' n f es; the name is free (renamed helper verified). Non-vacuous: wf_admininstr FRAME_ gives wf_frame f. |
| 19 | frame_t_context_return_empty (885) | OK | none.orElse(fun _ => none) = none. |
| 20 | Admin_instrs_ok_cons (895) | OK | `[e] ++ es` kept; ∃ ts ts1' ts2' ts3 order kept. |
| 21 | Admin_instrs_ok_cat (912) | OK | true in Lean: Resulttype_sub has a length premise, so `sub` is length-preserving (no zip loophole). |
| 22 | Admin_instrs_ok_all (949) | OK | `e \in es` (eqType reflection of =) ↔ `e ∈ es`. |
| 23 | s_typing_lf_br' (972) | OK | BR is typable only via Instr_ok.br, which needs `l < |LABELS| = 0`. |
| 24 | s_typing_lf_br (1009) | OK | rt : resulttype matches prepend_return's argument type. |
| 25 | s_typing_lf_return (1045) | OK | |
| 26 | s_typing_not_lf_br' (1072) | OK | |
| 27 | s_typing_not_lf_br (1094) | OK | |
| 28 | s_typing_not_lf_return (1116) | OK | |
| 29 | size_eq1_cat (1137) | OK | `|l|` = N.of_nat (size l), which is injective, so the `.length` equality is equivalent; A explicit. Minor, no flag: Lean `Type` = `Type 0`, while Rocq's `Type` is a fresh global universe. This is project-wide convention and every use is at Type 0. |
| 30 | br_reduce_extract_vs (1159) | OK | right-assoc grouping kept; `lookup_total (LABELS C) 0` → `C.LABELS[0]!` (the same idiom as Lean's own Instr_ok.br; derived Inhabited default = mk_list [] = Rocq default); `|vcs2| = |ts|` → `.length = (proj_list_0 valtype ts).length` (see the coercion note). |
| 31 | return_reduce_extract_vs (1221) | OK | `size vcs2 = size t` (seq.size via the coercion) → `.length = (proj_list_0 valtype t).length`. |

Doc comments: all 31 cite the correct Rocq line and name, and the deviation notes are accurate. The 31 merge
markers are present and in order.

Result: 31/31 OK. 0 mismatches, 0 undocumented deviations, 0 suspicious, 0 doc-only. 3 deviations (2 sumbool→Decidable
`def`, 1 hlen), all forced and documented.

## Safety check (END)
```
safety check [psig-audit-2] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T115312.043741700Z-psig-audit-2-1439236.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```
Files written: this log only (plus the empty scratch dir agents/psig-audit-2/). No Lean runs, no repo edits, no git commands.

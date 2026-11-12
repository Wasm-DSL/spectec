# Digest: `test-rocq/theories/type_preservation.v` (2802 lines)

Produced by a research subagent in session 1, verified via full sequential
read (all 2802 lines) + grep cross-checks. Read-only research, no files were
modified by the agent.

Imports (line 9): `wasm helper_lemmas helper_tactics typing_lemmas subtyping
type_preservation_pure extension_lemmas axioms`. So `t_pure_preservation`
(used but not defined here) lives in `type_preservation_pure.v`.

This file has **no `Inductive` and no Progress theorem** — it is
preservation-only. Exactly **13 top-level declarations** (confirmed via grep
for `^\(Lemma\|Theorem\|Corollary\|Definition\|Fixpoint\|Inductive\|Remark\|
Proposition\) `). No `Section`/header-comment structure — purely sequential,
big lemmas split internally into `{ (* CaseName *) ... }` blocks per
reduction rule.

---

## 1. `zero_is_well_formed` (13–17) — Qed
```coq
Lemma zero_is_well_formed:
	wf_num_ I32 (mk_num__0 Inn_I32 (mk_uN 0)).
```
Trivial: `econstructor; eauto; econstructor; eauto.`

## 2. `num_default` (19–26) — Definition
```coq
Definition num_default (nt : numtype) : num_ :=
	match nt with
		| I32 => mk_num__0 Inn_I32 (mk_uN 0)
		| I64 => mk_num__0 Inn_I64 (mk_uN 0)
		| F32 => mk_num__1 Fnn_F32 (fzero 32)
		| F64 => mk_num__1 Fnn_F64 (fzero 64)
	end.
```
Default/zero value per numtype; used to build default locals in
`t_read_preservation`'s Call_addr/frame-invocation case.

## 3. `num_default_is_well_formed` (28–37) — Qed
```coq
Lemma num_default_is_well_formed: forall nt,
	wf_num_ nt (num_default nt).
```
Case split on `nt`, 4 trivial `econstructor` cases.

## 4. `inst_t_context_local_empty` (39–44) — Qed
```coq
Lemma inst_t_context_local_empty: forall s i C,
	Module_instance_ok s i C ->
  context_LOCALS C = [].
```
One-line inversion.

## 5. `inst_t_context_labels_empty` (46–51) — Qed
```coq
Lemma inst_t_context_labels_empty: forall s i C,
	Module_instance_ok s i C ->
  LABELS C = [].
```
One-line inversion.

## 6. `t_preservation_vs_type'` (53–105) — Qed
```coq
Lemma t_preservation_vs_type': forall s f ais s' f' ais' C C' t1s t2s,
	Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
	Store_ok s ->
	Module_instance_ok s (frame_MODULE f) C ->
	Vals_ok s (LOCALS f) (context_LOCALS C') ->
	inst_match C C' ->
	Admin_instrs_ok s C' ais (t1s :-> t2s) ->
	Vals_ok s (LOCALS f') (context_LOCALS C').
```
Locals stay well-typed under one `Step` (store held fixed / pre-store-extension).
Induction on `HReduce`; only 3 non-trivial surviving cases (a label/prepend
case, two local-write cases via `Forall2_list_update_func2`).

## 7. `t_preservation_vs_type` (107–121) — Qed
```coq
Lemma t_preservation_vs_type: forall s f ais s' f' ais' C C' t1s t2s,
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    Store_ok s ->
	Store_extension s s' ->
    Module_instance_ok s (frame_MODULE f) C ->
	Vals_ok s (LOCALS f) (context_LOCALS C') ->
	inst_match C C' ->
    Admin_instrs_ok s C' ais (t1s :-> t2s) ->
    Vals_ok s' (LOCALS f') (context_LOCALS C').
```
Direct composition: `t_preservation_vs_type'` then `store_extension_vals`
(from extension_lemmas) to transport across store extension.

## 8. `store_extension_reduce` (123–995) — **ADMITTED**
```coq
Lemma store_extension_reduce: forall s f ais s' f' ais' C C' tf,
	Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
	Module_instance_ok s (frame_MODULE f) C ->
	Admin_instrs_ok s C' ais tf ->
	inst_match C C' ->
	Store_ok s ->
	Store_extension s s' /\ Store_ok s'.
```
Massive induction on the `Step` derivation. Generic cleanup block
(`all: eq_to_prop; try (...)`) auto-dispatches non-store-mutating cases via
`store_extension_refl`. Explicit `{ (* CaseName *) }` blocks for: Label
Context, Label Frame, Label Seq, Global Set, Table Set, Table Grow, Elem
Drop, Store None, Store Some, **`(* SIMD instructions *) 1-2: admit.` (line
790)**, Memory Grow, Data Drop. Each store-mutating case explicitly
constructs `Store_extension`/`Store_ok` witnesses via `mk_Store_extension
with (...)`/`mk_Store_ok with (...)` plus helper lemmas
(`global_set_global_extension`, `table_set_table_extension`,
`table_grow_table_extension`, `elem_drop_elem_extension`,
`store_none_mem_extension`, `memory_grow_mem_extension`,
`data_drop_data_extension`). Ends `Admitted.` at line 995 because of the 2
SIMD admits.
**Establishes store-extension monotonicity + preservation of `Store_ok` across one reduction step.**

## 9. `reduce_inst_unchanged` (997–1009) — Qed
```coq
Lemma reduce_inst_unchanged: forall s f ais s' f' ais',
    Step (mk_config (mk_state s f) ais) (mk_config (mk_state s' f') ais') ->
    frame_MODULE f = frame_MODULE f'.
```
Induction on `HReduce`: the module-instance component of the frame is
invariant under `Step`.

## 10. `t_read_preservation` (1011–2407) — **ADMITTED**
```coq
Lemma t_read_preservation: forall v_s v_f v_ais v_ais' v_C v_C' t1s t2s,
    Step_read (mk_config (mk_state v_s v_f) v_ais) v_ais' ->
    Store_ok v_s ->
    Module_instance_ok v_s (frame_MODULE v_f) v_C ->
	Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) (context_LOCALS v_C') (LOCALS v_f) ->
	inst_match v_C v_C' ->
    Admin_instrs_ok v_s v_C' v_ais (t1s :-> t2s) ->
    Admin_instrs_ok v_s v_C' v_ais' (t1s :-> t2s).
```
Preservation under the read-only reduction relation `Step_read` (no store
mutation — loads, calls, table/elem reads, etc). Huge case-by-case
induction; `try by eapply construct_ais_trap` handles trap cases generically.
Explicit named case blocks in order: `Block`, `Loop`, `Call`, `Call_indirect`,
`Call_addr` (frame-invocation — nested `(* Thread_ok *)` sub-proof building
callee `Frame_ok`/`Thread_ok` using `num_default_is_well_formed`), `Ref_func`,
`Local_get` (sub-cases CONST/VCONST/NULL/rest-of-vals), `Global_get`,
`Table_get`, `Table_size`, `Table_fill` (zero + succ), `Table_copy` (base +
le + gt), `Table_init` (zero + succ), `Load None`, `Load Inn` (I32/I64
sub-cases), **`(* SIMD instructions *) 1-5: admit.` (line 1981)**,
`Memory_size`, `Memory_fill` (zero + succ), `Memory_copy` (base + le + gt),
`Memory_init` (zero + succ). Proof idiom throughout: `typing_inversion`/
`invert_ais_typing` + `resolve_all_pt` to invert the typing derivation,
`join_subtyping_eq/ge/le` to normalize subtyping, then
`construct_ais_typing_single`/`construct_ais_compose`/`construct_ais_subtyping`
to rebuild the typing derivation for the reduced instruction sequence at the
same type. Ends `Admitted.` (line 2407) due to the 5 SIMD admits.

## 11. `step_moduleinst` (2409–2422) — Qed
```coq
Lemma step_moduleinst: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' v_tf,
	Step (mk_config (mk_state v_s v_f) v_ais)
		(mk_config (mk_state v_s' v_f') v_ais') ->
	Store_ok v_s ->
    Module_instance_ok v_s (frame_MODULE v_f) v_C ->
	inst_match v_C v_C' ->
	Admin_instrs_ok v_s v_C' v_ais v_tf ->
	Module_instance_ok v_s' (frame_MODULE v_f') v_C.
```
Composition: `reduce_inst_unchanged` + `store_extension_moduleinst`
(extension_lemmas) + `store_extension_reduce` (transitively depends on the
Admitted lemma #8).

## 12. `t_preservation_type` (2425–2664) — **ADMITTED**
```coq
Lemma t_preservation_type: forall v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' t1s t2s,
  Step (mk_config (mk_state v_s v_f) v_ais) (mk_config (mk_state v_s' v_f') v_ais') ->
  Store_ok v_s ->
  Store_ok v_s' ->
	Store_extension v_s v_s' ->
  Module_instance_ok v_s (frame_MODULE v_f) v_C ->
  Module_instance_ok v_s' (frame_MODULE v_f) v_C ->
	Vals_ok v_s (LOCALS v_f) (context_LOCALS v_C')->
	inst_match v_C v_C' ->
  Admin_instrs_ok v_s v_C' v_ais (t1s :-> t2s) ->
  Admin_instrs_ok v_s' v_C' v_ais' (t1s :-> t2s).
```
**The central preservation lemma for the whole `Step` relation** (subsumes
`t_read_preservation`). `dependent induction HReduce` with a big generic
`try solve [invert/resolve/join-subtyping/reconstruct]` block for uniform
cases, then explicit dispatch:
- `- (* Step_pure *) eapply t_pure_preservation; eauto.` (external, from
  `type_preservation_pure.v`)
- `- (* Step_read *) eapply t_read_preservation; eauto.` (declaration #10 —
  inherits its admits)

followed by explicit blocks: `Context Label`, `Context Frame` (builds callee
`Thread_ok`/`Frame_ok` via `t_preservation_vs_type`/`step_moduleinst`,
recurses via `IHHReduce`), `Context Instrs` (congruence via
`store_extension_ais`), `Table grow`/`Table grow fail`,
**`(* The rest are all SIMD instructions *) 1-2: admit.` (line 2636)**,
`Memory grow`/`Memory Grow fail`. Ends `Admitted.` (line 2664).

## 13. `t_preservation` (2668–2803) — **Qed** — THE TOP-LEVEL THEOREM

Explicitly flagged by source comment at line 2667: `(* Ultimate goal of project *)`.
```coq
Theorem t_preservation: forall c1 ts c2,
	Step c1 c2 ->
	Config_ok c1 ts ->
	Config_ok c2 ts.
```
This IS the whole-program **preservation theorem**: reduction (`Step`) on a
full `config` (store+frame+admin-instrs) preserves well-typedness of the
configuration at the same fixed result type `ts`. Proof: destructures
c1/c2, inverts `Config_ok` down through `Store_ok`→`Thread_ok`→`Frame_ok`→
`Module_instance_ok` to recover the ambient context `v_C0`; obtains
post-step `Store_extension ∧ Store_ok` via **`store_extension_reduce`** (#8,
Admitted); obtains post-step `Module_instance_ok` via
`reduce_inst_unchanged` + `store_extension_moduleinst`; obtains post-step
locals-typing via **`t_preservation_vs_type`** (#7, fully Qed); obtains
post-step instruction-typing via **`t_preservation_type`** (#12, Admitted);
assembles via `mk_Config_ok`/`mk_Thread_ok`/`mk_Frame_ok`. `Qed.` at line
2803 — but complete **only modulo the 3 Admitted lemmas it transitively
depends on** (#8, #10, #12), which Coq's kernel treats as axioms.

---

## Proof architecture

No single mutual induction. Layered composition:
- `t_preservation` (top) ← `store_extension_reduce` (store side) +
  `t_preservation_vs_type` (locals side) + `t_preservation_type`
  (instruction-typing side)
- `t_preservation_type` ← `t_pure_preservation` (external file) for
  `Step_pure` + `t_read_preservation` (this file) for `Step_read` + its own
  explicit congruence/mutation cases
- `t_preservation_vs_type` ← `t_preservation_vs_type'` + `store_extension_vals`
- `step_moduleinst` ← `reduce_inst_unchanged` + `store_extension_moduleinst`
  + `store_extension_reduce`

Each of the 3 big lemmas (`store_extension_reduce`, `t_read_preservation`,
`t_preservation_type`) is one induction on the reduction-derivation, broken
into one explicit `{ (* CaseName *) }` sub-proof per WASM instruction/
reduction rule (dozens each); consistent idiom: invert typing → join
subtyping → reconstruct typing derivation for the RHS.

No `Fixpoint`, no `Inductive` in this file. Only one helper `Definition`
(`num_default`). **No Progress theorem anywhere in this file** — this file
is preservation-only; Progress must live in one of the other files (check
`typing_lemmas.v`/`type_preservation_pure.v` digests, or grep the whole
theories dir for `Theorem.*progress`/`t_progress`).

## Admitted / admit — exact locations (ALL of them in this file)

| Lemma | `Admitted.` line | `admit` line(s) | What's admitted |
|---|---|---|---|
| `store_extension_reduce` | 995 | 790 (`1-2: admit.`) | 2 SIMD-instruction store-mutation cases |
| `t_read_preservation` | 2407 | 1981 (`1-5: admit.`) | 5 SIMD-instruction read-reduction cases |
| `t_preservation_type` | 2664 | 2636 (`1-2: admit.`) | 2 SIMD-instruction cases |

Verified via `grep -n 'Admitted\|admit'` and `grep -n '^Qed\.'` — exactly
these 3 Admitted lemmas exist in the file; the other 10 declarations
(including the capstone `Theorem t_preservation`) are fully `Qed.`-proved.
Two other comments (`(* fun_nbytes_ not implemented *)` line 598,
`(* fun_ibytes_ wrap__ not implemented *)` line 697) are just naming remarks
next to fully-proved Store-instruction cases — NOT admits.

**Key signal for the Lean port:** every gap is specifically and exclusively
the SIMD/vector-instruction cases. All scalar/numeric, control-flow, table,
memory (non-SIMD), elem, data, global, local, and call-related cases are
fully proved down to the top theorem. For the Lean translation: everything
except SIMD cases should get genuine proofs; only SIMD-instruction cases are
sanctioned to stay as `sorry`, mirroring the Rocq original's own admitted
gaps. **WASM 2.0 has no SIMD instructions in its instruction set at all**
(SIMD was added in a later proposal) — double check whether these
Rocq "SIMD instructions" cases are dead code for the 2.0 subset specifically,
or whether they're for a shared instr type that includes SIMD constructors
even in the 2.0 formalization (check `wasm2.0.lean`'s `instr`/`admininstr`
for any v128/vNN constructors) — if WASM 2.0 truly has no SIMD, these gaps
might be entirely vacuous/unreachable in the Lean 2.0 port and could
potentially be discharged for real rather than kept as `sorry`.

# 8. `t_read_preservation` — the 47-case `Step_read` dispatcher

*(Previous: [07-t-preservation-type-aux.md](07-t-preservation-type-aux.md). Next: [09-helper-glossary.md](09-helper-glossary.md).)*

This is the last leaf of the diagram: the `Step.read` case of `t_preservation_type_aux` (file `07`) hands its whole job to this theorem. It is the longest proof in the tree, but it is highly regular, so this file is organised to make the regularity visible:

- **§8.1** — summary, the theorem header verbatim, the signature, and the preamble.
- **§8.2** — WASM background: the seven instruction families `Step_read` covers, and two recurring patterns in their rules.
- **§8.3** — how every proof case is built (three moves), a worked example, and the small toolkit of helper lemmas written for this proof.
- **§8.4–§8.10** — one section per family: what the instructions do, their `Step_read` rules **verbatim**, a plain reading of the rules, the matching proof cases **verbatim**, and an explanation.
- **§8.11** — the theorem's one `sorry` dependency and the known corner case where it is false.

The proof's 47 cases appear in the same order as the 47 rules of `Step_read`, so §8.4–§8.10 pair them up exactly. Taken together, the header in §8.1 and the proof blocks in §8.4–§8.10 reproduce [TypePreservation.lean:2016-2418](../../../../../src/test-lean-claude/TypePreservation.lean#L2016-L2418) in full, in order; likewise the rule blocks reproduce the whole `Step_read` definition, [wasm2.0.lean:14410-14695](../../../../../src/test-lean-claude/wasm2.0.lean#L14410-L14695).

## 8.1 Summary, header, and signature

**Plain-English summary.** Type preservation for the 47 rules that *read* the store or frame but never write them: entering a block or loop; resolving and performing function calls; reading a local, a global, or a table slot; scalar and SIMD loads from memory; `table.size` and `memory.size`; and the bulk operations `table.fill/copy/init` and `memory.fill/copy/init`. (Those bulk operations never write directly — each step rewrites into a small program that writes *one* element with an ordinary `table.set` or `i32.store8`, followed by the same bulk operation on one fewer element. The writing itself is then done by the store-writing `Step` rules covered in file `02`.) If a read-only step turns the instruction list `ais` into `ais'`, then `ais'` has the same type `t1s → t2s` as `ais`, in the same store and the same context.

**Code — the theorem header** (doc comment, statement, and the preamble up to the case split) — [TypePreservation.lean:2016-2041](../../../../../src/test-lean-claude/TypePreservation.lean#L2016-L2041):
```lean
/-- Rocq `type_preservation.v:1661` `t_read_preservation`: preservation under the read-only
    reduction relation (no store mutation). `Qed` in Rocq; proved here (bundle19), all 47
    `Step_read` rules. As in Rocq, the reduct's well-formedness comes from the generated
    `Step_read_is_wf` (`Admitted` in Rocq, `sorry` in `wasm2.0.lean`), and that is this
    theorem's only `sorry` dependency. The theorem (Rocq's too) is false in the
    memory.fill/copy/init `CONST I32 2^32` corner case, through exactly that dependency; the
    fix is pending on the spec side (`claude-logging/for-claude/is_wf_theorems.md`).

    **Signature deviation (intended, bundle19):** the locals hypothesis is
    `Vals_ok v_s v_f.LOCALS v_C'.LOCALS`, i.e. Rocq's
    `Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) (context_LOCALS v_C') (LOCALS v_f)` plus
    the length equation. Rocq's inductive `Forall2` implies equal lengths; Lean's generated
    `Forall₂` is zip-based and does not, and the `local.get` case needs the length to index the
    locals (the same kind of deviation as `funcinst_same`'s `hlen`). The only caller,
    `t_preservation_type_aux`, already has the `Vals_ok`. -/
theorem t_read_preservation (v_s : store) (v_f : frame) (v_ais : List admininstr)
    (v_ais' : List admininstr) (v_C v_C' : context) (t1s t2s : List valtype) :
    wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →
    Step_read (config.mk_config (state.mk_state v_s v_f) v_ais) v_ais' →
    Store_ok v_s → Moduleinst_ok v_s v_f.MODULE v_C →
    Vals_ok v_s v_f.LOCALS v_C'.LOCALS → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s) → Instrs_ok2 v_s v_C' v_ais' (mkFunctype t1s t2s) := by
  intro hwfc hstep hsok hmi hvals him htype
  have hwf' := Step_read_is_wf _ _ _ hwfc hsok hstep
  obtain ⟨hwfC', hwfS, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
  cases hstep with
```

**Signature, piece by piece.**
- `v_s`, `v_f` — the store and frame. They are the **same on both sides**: `Step_read` relates a configuration to a new instruction list only, and the `Step.read` constructor keeps the state `z` fixed (primer §0.7). That is why the conclusion mentions `v_s` again rather than some `v_s'`.
- `v_ais`, `v_ais'` — the instruction list before and after the step.
- `v_C`, `v_C'`, `inst_match v_C v_C'` — the module-level context that matches the running module instance (`Moduleinst_ok v_s v_f.MODULE v_C`), and the context the instruction list is actually typed in; `inst_match` says they agree on everything except locals, labels, and return (primer §0.3).
- `t1s`, `t2s` — the stack type the instruction list is checked at; preserved exactly.
- `wf_config …` — syntactic well-formedness of the pre-configuration. Its only job here is to feed `Step_read_is_wf`, which yields well-formedness of the reduct (§8.11).
- `Store_ok v_s` — reads need *typed* store contents: a global's current value, a table's references, a callee's code.
- `Moduleinst_ok v_s v_f.MODULE v_C` — translates module-local indices (`global.get 2`) into store addresses whose contents have the types the context claims.
- `Vals_ok v_s v_f.LOCALS v_C'.LOCALS` — the frame's locals have the types the context says. `local.get` and `call_addr` need it. The doc comment flags this as an intended deviation from Rocq: Rocq states it as a bare `Forall2`, which in Rocq implies equal lengths; this repo's generated `Forall₂` is zip-based and does not, and `local.get` needs the length to index the locals, so the Lean version bundles the length equation in (`Vals_ok`, primer §0.5).
- `Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s)` → `Instrs_ok2 v_s v_C' v_ais' (mkFunctype t1s t2s)` — the actual preservation statement.

Compare `t_pure_preservation` (file `07` §7a), which needs none of the store/frame/context hypotheses: pure rules never look at the state, so their typing argument never needs facts about it.

**The preamble** (the four lines after the statement). `intro` names the hypotheses. `hwf'` records that every instruction of the reduct is `wf_admininstr`, obtained from `Step_read_is_wf`; many typing rules demand well-formedness of the instruction they type, so the cases below keep drawing on it. `ainstrs_ok_context_store_wf` extracts `hwfC'` and `hwfS` — any typing derivation implies its context and store are well-formed — which nearly every construction lemma below asks for. Finally `cases hstep with` splits into the 47 rules.

## 8.2 WASM background

### The seven families

| Family | Rules (`Step_read` constructors) | What the instructions do |
|---|---|---|
| A. Entering blocks (§8.4) | `block`, `loop` | Start executing a structured block or loop: wrap its body in a `LABEL_` marker (primer §0.1). |
| B. Function calls (§8.5) | `call`, `call_indirect_call`, `call_indirect_trap`, `call_addr` | Resolve a call to a concrete store function address (`CALL_ADDR a`), then perform it: build the callee's frame and enter its body. |
| C. References, locals, globals (§8.6) | `ref_func`, `local_get`, `global_get` | Push a function reference, a local's value, or a global's value. |
| D. Single table reads (§8.7) | `table_get_trap`, `table_get_val`, `table_size` | Read one table element (trapping if out of bounds), or the table's length. |
| E. Bulk table operations (§8.8) | `table_fill_*`, `table_copy_*`, `table_init_*` | Fill a range of a table, copy a range between tables, or copy from an element segment into a table. |
| F. Loads (§8.9) | `load_num_*`, `load_pack_*`, `vload_*` (five shapes) | Read bytes from memory 0 and decode a number or a 128-bit vector, trapping if out of bounds. |
| G. Memory size and bulk memory (§8.10) | `memory_size`, `memory_fill_*`, `memory_copy_*`, `memory_init_*` | The memory analogues of families D and E, byte by byte. |

### Pattern 1: trap / zero / succ — how bulk operations become loops without loops

Every bulk operation has three rules, distinguished by mutually exclusive side conditions:

- **`_trap`** — some part of the requested range is out of bounds → `[TRAP]`. The check covers the *whole* range up front, so nothing is written before an out-of-bounds access is detected.
- **`_zero`** — in bounds and the count `n` is 0 → `[]` (nothing to do).
- **`_succ`** (or `_le`/`_gt` for copies) — in bounds and `n ≠ 0` → a short program that handles **one** element with a primitive instruction, followed by **the same bulk operation with `n - 1`** and adjusted offsets.

So `table.fill` is not a loop in the semantics; it is a rule that peels off one element and leaves itself behind. Concretely, from the `table_fill_succ` rule in §8.8 (schematically: `v` is the fill value, a reference; arithmetic shown evaluated):

```
[CONST I32 3, v, CONST I32 2, TABLE_FILL x]
  ─ Step_read.table_fill_succ ─→   [CONST I32 3, v, TABLE_SET x,   CONST I32 4, v, CONST I32 1, TABLE_FILL x]
  ─ Step.table_set_val ──────────→ [CONST I32 4, v, CONST I32 1, TABLE_FILL x]           -- store: slot 3 := v
  ─ Step_read.table_fill_succ ─→   [CONST I32 4, v, TABLE_SET x,   CONST I32 5, v, CONST I32 0, TABLE_FILL x]
  ─ Step.table_set_val ──────────→ [CONST I32 5, v, CONST I32 0, TABLE_FILL x]           -- store: slot 4 := v
  ─ Step_read.table_fill_zero ─→   []
```

(The `table_set_val` steps apply to the first three instructions of a longer list, so they go through the `ctxt_instrs` congruence rule.) Once the full range has passed the bounds check, every later step re-checks a smaller sub-range of the same table, so execution never traps midway. The copy operations come in two `succ` flavours: `_le` (destination ≤ source) copies the *first* element and moves forward; `_gt` (destination > source) copies the *last* element and keeps the start offsets — copying backwards when the destination lies above the source is what makes overlapping ranges come out right, exactly like C's `memmove`.

### Pattern 2: "otherwise" premises

SpecTec lets a rule apply only when earlier, overlapping rules do not. The generated Lean has two ways of expressing that. Most rules here carry **explicit complementary side conditions** (`>` versus `≤` for bounds, `v_n = 0` versus `v_n ≠ 0`), so at most one rule of a group can fire. `call_indirect_trap` instead says "trap whenever the `call_indirect_call` conditions do not all hold", which the generator encodes as a premise `¬ Step_read_before_call_indirect_trap …`, where `Step_read_before_call_indirect_trap` is a generated relation bundling exactly `call_indirect_call`'s conditions (shown in §8.5). The file also generates `Step_read_before_*` relations for several bulk operations, but no `Step_read` rule uses them as premises.

## 8.3 How the proof cases are built

**The three moves.** Almost every case does the same three things:

1. **Invert the pre-typing.** The hypothesis `htype` types the redex (`v_ais`) at `t1s → t2s`. Typing derivations are flexible (subtyping, stack framing), so the proof first extracts the redex's *principal* type — the tightest type the operator could have — and an `instrtype_sub` fact saying `t1s → t2s` is a weakening of it. The key definitions:
   - `ai_principal_typing s C ai ft` ([TypingLemmas.lean:311-456](../../../../../src/test-lean-claude/TypingLemmas.lean#L311-L456)) is a big `match` giving, for each administrative instruction, its principal type plus side conditions — e.g. for `TABLE_GET x`: type `[I32] → [rt]` where `C.TABLES[x] = (lim, rt)`; for `CALL_ADDR a`: some `ts1 → ts2` such that the store address `a` holds a function of that type.
   - `instrtype_sub (ts11 → ts12) (ts21 → ts22)` ([Subtyping.lean:43-54](../../../../../src/test-lean-claude/Subtyping.lean#L43-L54)) holds when `ts21 = ts_sub ++ ts11_sub` and `ts22 = ts ++ ts12_sup`, with `ts_sub ≤ ts`, `ts11_sub ≤ ts11`, and `ts12 ≤ ts12_sup` pointwise. In words: you may add untouched stack slots *underneath* (the `ts_sub`/`ts` prefix — the "frame" rule), and inputs/outputs may be related by value subtyping, which in WASM 2.0 is just "equal, or `BOT` on the more specific side" (`Valtype_sub`, [wasm2.0.lean:12729-12731](../../../../../src/test-lean-claude/wasm2.0.lean#L12729-L12731)).
   - `ais_single_typing_inversion` turns a typing of a one-instruction list into "principal type + `instrtype_sub`"; `ais_composition_typing`/`ais_seq_typing_inversion` split a typing of `l1 ++ l2` at an intermediate stack type; `ais_vals_typing_inversion` and `ais_const_typing_inversion` read off the types of pushed values.
2. **Type the reduct at its natural type,** using the facts from step 1 plus whatever the store and frame guarantee (`Store_ok`, `Moduleinst_ok`, `Vals_ok`).
3. **Weaken** to `t1s → t2s` with `construct_ais_subtyping`, using the `instrtype_sub` fact from step 1.

**The case categories** (all 47, by how step 2 goes):

| Category | Count | Cases | How the reduct is typed |
|---|---|---|---|
| Trap | 15 | every `_trap` and `_oob` rule | `construct_ais_trap`: `TRAP` has every type (primer §0.5). No steps 1 or 3 needed. |
| Zero | 6 | every `_zero` rule | Reduct is `[]`. The redex `[c, v, c, op]` has net type `[] → []`, so `ais_args3_typing` gives `instrtype_sub ([] → []) (t1s → t2s)`; `instrtype_sub_empty` turns that into the `ResulttypeSub t1s t2s` that `ais_empty_typing` needs. |
| One result value | 8 | `ref_func`, `local_get`, `global_get`, `table_get_val`, `table_size`, `load_num_val`, `load_pack_val`, `memory_size` | Prove the produced value has the operator's result type (from the store, frame, or rule premise) and type it as a one-element push. |
| SIMD loads | 5 | the five `vload*_val` rules | Delegated to `Step_read__vload_preserves` / `Step_read__vload_lane_preserves` (§8.9). |
| Calls | 3 | `call`, `call_indirect_call`, `call_addr` | Type `CALL_ADDR a` from a store-address fact, or build the callee's `FRAME_`/`LABEL_` (§8.5). |
| Block entry | 2 | `block`, `loop` | Rebuild a `LABEL_` typing from the block's own typing (§8.4). |
| Bulk `succ` | 8 | `table_fill_succ`, `table_copy_le/gt`, `table_init_succ`, `memory_fill_succ`, `memory_copy_le/gt`, `memory_init_succ` | Type the desugared program instruction by instruction with an `ais_cons_pre` chain (worked example below). |

### The toolkit written for this proof

The source introduces a block of Lean-only helpers right before this theorem — [TypePreservation.lean:1638-2014](../../../../../src/test-lean-claude/TypePreservation.lean#L1638-L2014). Its header comment explains the approach (Rocq instead uses its `construct_ais_typing` automation):
```lean
/-! ### Helpers for `t_read_preservation` (Lean-only, bundle19)

    Rocq builds the reduct typings with its `construct_ais_typing` automation and explicit
    `instrtype_sub` witnesses for stack prefixes. Here: `ais_cons_pre` types one instruction at its
    principal type underneath a stack prefix (`instrtype_sub_add_same`) and chains it; the `pt_*`
    lemmas read an operator's principal type off a typing of the one-instruction sequence. -/

theorem ais_cons_pre (s : store) (C : context) (a : admininstr) (rest : List admininstr)
    (pre a1 a2 t3 : List valtype) :
    Instrs_ok2 s C [a] (mkFunctype a1 a2) → Instrs_ok2 s C rest (mkFunctype (pre ++ a2) t3) →
    Instrs_ok2 s C (a :: rest) (mkFunctype (pre ++ a1) t3) := fun ha hr =>
  construct_ais_compose s C [a] rest (pre ++ a1) (pre ++ a2) t3
    (construct_ais_subtyping s C [a] a1 a2 (pre ++ a1) (pre ++ a2) ha (instrtype_sub_add_same a1 a2 pre)) hr

theorem ais_nil_refl (s : store) (C : context) (ts : List valtype) (hC : wf_context C) (hS : wf_store s) :
    Instrs_ok2 s C [] (mkFunctype ts ts) :=
  (ais_empty_typing s C ts ts).mpr ⟨hC, hS, resulttype_sub_refl ts⟩

theorem ais_const1 (s : store) (C : context) (nt : numtype) (c : num_) (hc : wf_num_ nt c)
    (hC : wf_context C) (hS : wf_store s) :
    Instrs_ok2 s C [admininstr.CONST nt c] (mkFunctype [] [valtype_numtype nt]) :=
  construct_ais_typing_single s C _ [] _
    (Instr_ok2.plain s C (instr.CONST nt c) [] [valtype_numtype nt]
      (Instr_ok.const C nt c hC (wf_instr.instr_case_13 nt c hc)) hS hC (wf_instr.instr_case_13 nt c hc))

theorem ais_val1 (s : store) (C : context) (v : val) (t : valtype) (hv : Val_ok s v t)
    (hC : wf_context C) (hS : wf_store s) : Instrs_ok2 s C [admininstr_val v] (mkFunctype [] [t]) :=
  construct_ais_typing_single s C _ [] [t] (construct_ai_val s C v t hv hC hS)

theorem ais_ref1 (s : store) (C : context) (r : ref) (rt : reftype) (hr : Ref_ok s r rt)
    (hC : wf_context C) (hS : wf_store s) :
    Instrs_ok2 s C [admininstr_ref r] (mkFunctype [] [valtype_reftype rt]) :=
  construct_ais_typing_single s C _ [] _ (Instr_ok2.ref s C r rt hr hS hC)

theorem ais_plain1 (s : store) (C : context) (i : instr) (t1 t2 : List valtype) (hS : wf_store s)
    (h : Instr_ok C i (mkFunctype t1 t2)) : Instrs_ok2 s C [admininstr_instr i] (mkFunctype t1 t2) :=
  construct_ais_typing_single s C _ t1 t2 (construct_instr_from_ai_single s C i t1 t2 hS h)
```

- **`ais_cons_pre`** is the workhorse of every bulk `succ` case. Read its statement as a typing rule for "one instruction, then the rest": if `a` alone has type `a1 → a2`, and `rest` takes the stack `pre ++ a2` to `t3`, then `a :: rest` takes `pre ++ a1` to `t3`. The `pre` list is the part of the stack that `a` does not touch (it sits underneath). One `ais_cons_pre` per instruction, nested, types a whole straight-line program by tracking the stack.
- **`ais_nil_refl`** types the empty list `[]` at `ts → ts` — the end of every chain.
- **`ais_const1`, `ais_val1`, `ais_ref1`** type a single pushed constant, value, or reference at `[] → [t]`; **`ais_plain1`** lifts a typing from the static judgment `Instr_ok` (primer §0.5) for a plain instruction such as `TABLE_SET x`.

The seventeen **`pt_*` lemmas** (`pt_table_fill`, `pt_call`, …) each package step 1 for one operator: given a typing of `[op]`, they return its principal type's side conditions and the `instrtype_sub` fact. They all have the same short proof: invert, unfold `ai_principal_typing`, destructure, rewrite. A representative one:
```lean
theorem pt_call (s : store) (C : context) (x : funcidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.CALL x] (mkFunctype u1 u2)) :
    ∃ t1 t2, C.FUNCS[proj_uN_0 x]? = some (mkFunctype t1 t2) ∧
      instrtype_sub (mkFunctype t1 t2) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨t1, t2, heq, hlk⟩ := hpt
  rw [heq] at hs
  exact ⟨t1, t2, hlk, hs⟩
```

The remaining helpers are explained where they are used. For reference, the complete helper block, verbatim:

<details>
<summary>All helpers for <code>t_read_preservation</code> (TypePreservation.lean, lines 1638–2014)</summary>

```lean
/-! ### Helpers for `t_read_preservation` (Lean-only, bundle19)

    Rocq builds the reduct typings with its `construct_ais_typing` automation and explicit
    `instrtype_sub` witnesses for stack prefixes. Here: `ais_cons_pre` types one instruction at its
    principal type underneath a stack prefix (`instrtype_sub_add_same`) and chains it; the `pt_*`
    lemmas read an operator's principal type off a typing of the one-instruction sequence. -/

theorem ais_cons_pre (s : store) (C : context) (a : admininstr) (rest : List admininstr)
    (pre a1 a2 t3 : List valtype) :
    Instrs_ok2 s C [a] (mkFunctype a1 a2) → Instrs_ok2 s C rest (mkFunctype (pre ++ a2) t3) →
    Instrs_ok2 s C (a :: rest) (mkFunctype (pre ++ a1) t3) := fun ha hr =>
  construct_ais_compose s C [a] rest (pre ++ a1) (pre ++ a2) t3
    (construct_ais_subtyping s C [a] a1 a2 (pre ++ a1) (pre ++ a2) ha (instrtype_sub_add_same a1 a2 pre)) hr

theorem ais_nil_refl (s : store) (C : context) (ts : List valtype) (hC : wf_context C) (hS : wf_store s) :
    Instrs_ok2 s C [] (mkFunctype ts ts) :=
  (ais_empty_typing s C ts ts).mpr ⟨hC, hS, resulttype_sub_refl ts⟩

theorem ais_const1 (s : store) (C : context) (nt : numtype) (c : num_) (hc : wf_num_ nt c)
    (hC : wf_context C) (hS : wf_store s) :
    Instrs_ok2 s C [admininstr.CONST nt c] (mkFunctype [] [valtype_numtype nt]) :=
  construct_ais_typing_single s C _ [] _
    (Instr_ok2.plain s C (instr.CONST nt c) [] [valtype_numtype nt]
      (Instr_ok.const C nt c hC (wf_instr.instr_case_13 nt c hc)) hS hC (wf_instr.instr_case_13 nt c hc))

theorem ais_val1 (s : store) (C : context) (v : val) (t : valtype) (hv : Val_ok s v t)
    (hC : wf_context C) (hS : wf_store s) : Instrs_ok2 s C [admininstr_val v] (mkFunctype [] [t]) :=
  construct_ais_typing_single s C _ [] [t] (construct_ai_val s C v t hv hC hS)

theorem ais_ref1 (s : store) (C : context) (r : ref) (rt : reftype) (hr : Ref_ok s r rt)
    (hC : wf_context C) (hS : wf_store s) :
    Instrs_ok2 s C [admininstr_ref r] (mkFunctype [] [valtype_reftype rt]) :=
  construct_ais_typing_single s C _ [] _ (Instr_ok2.ref s C r rt hr hS hC)

theorem ais_plain1 (s : store) (C : context) (i : instr) (t1 t2 : List valtype) (hS : wf_store s)
    (h : Instr_ok C i (mkFunctype t1 t2)) : Instrs_ok2 s C [admininstr_instr i] (mkFunctype t1 t2) :=
  construct_ais_typing_single s C _ t1 t2 (construct_instr_from_ai_single s C i t1 t2 hS h)

theorem pt_table_fill (s : store) (C : context) (x : tableidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.TABLE_FILL x] (mkFunctype u1 u2)) :
    ∃ rt lim, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) ∧
      instrtype_sub (mkFunctype [valtype.I32, valtype_reftype rt, valtype.I32] []) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨rt, lim, heq, hlk⟩ := hpt
  rw [heq] at hs
  exact ⟨rt, lim, hlk, hs⟩

theorem pt_table_copy (s : store) (C : context) (x y : tableidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.TABLE_COPY x y] (mkFunctype u1 u2)) :
    ∃ rt lim1 lim2, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim1 rt) ∧
      C.TABLES[proj_uN_0 y]? = some (tabletype.mk_tabletype lim2 rt) ∧
      instrtype_sub (mkFunctype [valtype.I32, valtype.I32, valtype.I32] []) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨rt, lim1, lim2, heq, hx, hy⟩ := hpt
  rw [heq] at hs
  exact ⟨rt, lim1, lim2, hx, hy, hs⟩

theorem pt_table_init (s : store) (C : context) (x y : tableidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.TABLE_INIT x y] (mkFunctype u1 u2)) :
    ∃ rt lim, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) ∧
      C.ELEMS[proj_uN_0 y]? = some rt ∧
      instrtype_sub (mkFunctype [valtype.I32, valtype.I32, valtype.I32] []) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨rt, lim, heq, hx, hy⟩ := hpt
  rw [heq] at hs
  exact ⟨rt, lim, hx, hy, hs⟩

theorem pt_memory_fill (s : store) (C : context) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.MEMORY_FILL] (mkFunctype u1 u2)) :
    ∃ mt, C.MEMS[0]? = some mt ∧
      instrtype_sub (mkFunctype [valtype.I32, valtype.I32, valtype.I32] []) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨mt, heq, hm⟩ := hpt
  rw [heq] at hs
  exact ⟨mt, hm, hs⟩

theorem pt_memory_copy (s : store) (C : context) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.MEMORY_COPY] (mkFunctype u1 u2)) :
    ∃ mt, C.MEMS[0]? = some mt ∧
      instrtype_sub (mkFunctype [valtype.I32, valtype.I32, valtype.I32] []) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨mt, heq, hm⟩ := hpt
  rw [heq] at hs
  exact ⟨mt, hm, hs⟩

theorem pt_memory_init (s : store) (C : context) (x : dataidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.MEMORY_INIT x] (mkFunctype u1 u2)) :
    ∃ mt, C.MEMS[0]? = some mt ∧ C.DATAS[proj_uN_0 x]? = some datatype.OK ∧
      instrtype_sub (mkFunctype [valtype.I32, valtype.I32, valtype.I32] []) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨mt, heq, hm, hd⟩ := hpt
  rw [heq] at hs
  exact ⟨mt, hm, hd, hs⟩

theorem pt_table_get (s : store) (C : context) (x : tableidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.TABLE_GET x] (mkFunctype u1 u2)) :
    ∃ rt lim, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) ∧
      instrtype_sub (mkFunctype [valtype.I32] [valtype_reftype rt]) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨rt, lim, heq, hlk⟩ := hpt
  rw [heq] at hs
  exact ⟨rt, lim, hlk, hs⟩

theorem pt_table_size (s : store) (C : context) (x : tableidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.TABLE_SIZE x] (mkFunctype u1 u2)) :
    instrtype_sub (mkFunctype [] [valtype.I32]) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, _, heq, _⟩ := hpt
  rw [heq] at hs
  exact hs

theorem pt_memory_size (s : store) (C : context) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.MEMORY_SIZE] (mkFunctype u1 u2)) :
    instrtype_sub (mkFunctype [] [valtype.I32]) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, heq, _⟩ := hpt
  rw [heq] at hs
  exact hs

theorem pt_load_none (s : store) (C : context) (nt : numtype) (ao : memarg) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.LOAD nt none ao] (mkFunctype u1 u2)) :
    instrtype_sub (mkFunctype [valtype.I32] [valtype_numtype nt]) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, _, heq, _⟩ := hpt
  rw [heq] at hs
  exact hs

theorem pt_load_pack (s : store) (C : context) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg)
    {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.LOAD (numtype_Inn v_Inn)
      (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao] (mkFunctype u1 u2)) :
    instrtype_sub (mkFunctype [valtype.I32] [valtype_Inn v_Inn]) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, _, heq, _⟩ := hpt
  rw [heq] at hs
  exact hs

theorem pt_local_get (s : store) (C : context) (x : localidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.LOCAL_GET x] (mkFunctype u1 u2)) :
    ∃ t, C.LOCALS[proj_uN_0 x]? = some t ∧ instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨t, heq, hlk⟩ := hpt
  rw [heq] at hs
  exact ⟨t, hlk, hs⟩

theorem pt_global_get (s : store) (C : context) (x : globalidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.GLOBAL_GET x] (mkFunctype u1 u2)) :
    ∃ t m, C.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype m t) ∧
      instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨t, m, heq, hlk⟩ := hpt
  rw [heq] at hs
  exact ⟨t, m, hlk, hs⟩

theorem pt_ref_func (s : store) (C : context) (x : funcidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.REF_FUNC x] (mkFunctype u1 u2)) :
    ∃ ft, C.FUNCS[proj_uN_0 x]? = some ft ∧
      instrtype_sub (mkFunctype [] [valtype_reftype reftype.FUNCREF]) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨ft, heq, hlk⟩ := hpt
  rw [heq] at hs
  exact ⟨ft, hlk, hs⟩

theorem pt_call (s : store) (C : context) (x : funcidx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.CALL x] (mkFunctype u1 u2)) :
    ∃ t1 t2, C.FUNCS[proj_uN_0 x]? = some (mkFunctype t1 t2) ∧
      instrtype_sub (mkFunctype t1 t2) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨t1, t2, heq, hlk⟩ := hpt
  rw [heq] at hs
  exact ⟨t1, t2, hlk, hs⟩

theorem pt_call_indirect (s : store) (C : context) (x y : idx) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.CALL_INDIRECT x y] (mkFunctype u1 u2)) :
    ∃ t1 t2 lim, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim reftype.FUNCREF) ∧
      C.TYPES[proj_uN_0 y]? = some (mkFunctype t1 t2) ∧
      instrtype_sub (mkFunctype (t1 ++ [valtype.I32]) t2) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨t1, t2, lim, heq, hx, hy⟩ := hpt
  rw [heq] at hs
  exact ⟨t1, t2, lim, hx, hy, hs⟩

theorem pt_call_addr (s : store) (C : context) (a : funcaddr) {u1 u2 : List valtype}
    (h : Instrs_ok2 s C [admininstr.CALL_ADDR a] (mkFunctype u1 u2)) :
    ∃ t1 t2, Externaddr_ok s (externaddr.FUNC a) (externtype.FUNC (mkFunctype t1 t2)) ∧
      instrtype_sub (mkFunctype t1 t2) (mkFunctype u1 u2) := by
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨t1, t2, heq, hea⟩ := hpt
  rw [heq] at hs
  exact ⟨t1, t2, hea, hs⟩

/-- The last operator of a four-instruction sequence has some typing. -/
theorem ais_seq4_last (s : store) (C : context) (a b c op : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 s C [a, b, c, op] (mkFunctype t1s t2s) → ∃ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) := by
  intro h
  obtain ⟨t3s, h1, _⟩ := ais_seq_typing_inversion s C [b, c, op] a t1s t2s h
  obtain ⟨t4s, h2, _⟩ := ais_seq_typing_inversion s C [c, op] b t3s t2s h1
  obtain ⟨t5s, h3, _⟩ := ais_seq_typing_inversion s C [op] c t4s t2s h2
  exact ⟨t5s, t2s, h3⟩

/-- `[CONST I32 i, val v, CONST I32 n, op]` where `op : [I32, t, I32] → []`: the sequence is
    `[] → []` and `v` has type `t`. -/
theorem ais_fill_inv (s : store) (C : context) (i n : num_) (v : val) (op : admininstr) (t : valtype)
    (t1s t2s : List valtype)
    (hop : ∀ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) →
      instrtype_sub (mkFunctype [valtype.I32, t, valtype.I32] []) (mkFunctype u1 u2)) :
    Instrs_ok2 s C [admininstr.CONST numtype.I32 i, admininstr_val v, admininstr.CONST numtype.I32 n, op]
      (mkFunctype t1s t2s) →
    Val_ok s v t ∧ instrtype_sub (mkFunctype [] []) (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t3s, hr1, hc1⟩ := ais_seq_typing_inversion s C [admininstr_val v, admininstr.CONST numtype.I32 n, op] _ t1s t2s h
  obtain ⟨t4s, hr2, hv⟩ := ais_seq_typing_inversion s C [admininstr.CONST numtype.I32 n, op] _ t3s t2s hr1
  obtain ⟨t5s, hop', hc3⟩ := ais_seq_typing_inversion s C [op] _ t4s t2s hr2
  have s1 := ais_const_typing_inversion s C numtype.I32 i t1s t3s hc1
  obtain ⟨tv, s2, hvok⟩ := ais_single_val_typing_inversion s C v t3s t4s hv
  have s3 := ais_const_typing_inversion s C numtype.I32 n t4s t5s hc3
  have s4 := hop t5s t2s hop'
  have c34 := (instrtype_sub_compose_le [] [valtype_numtype numtype.I32] [valtype.I32] [valtype.I32, t] []
    t4s t5s t2s s3 s4 rfl).1
  have c234 := instrtype_sub_compose_le [] [tv] [t] [valtype.I32] [] t3s t4s t2s s2 c34 rfl
  have hteq := valtype_sub_non_bot t tv (resulttype_sub_cons tv t [] [] c234.2).1 (Val_ok_non_bot s v tv hvok)
  subst hteq
  exact ⟨hvok, (instrtype_sub_compose_eq [] [valtype_numtype numtype.I32] [valtype.I32] [] t1s t3s t2s s1
    c234.1 rfl).1⟩

/-- The references of a table the module instance maps `x` to have the context's element type. -/
theorem table_refs_ok (s : store) (minst : moduleinst) (C C' : context) (x : tableidx) (rt : reftype)
    (lim : limits) :
    Store_ok s → Moduleinst_ok s minst C → inst_match C C' →
    C'.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) →
    Forall (fun r => Ref_ok s r rt) (s.TABLES[minst.TABLES[proj_uN_0 x]!]!).REFS := by
  intro hsok hmi him hlkC
  obtain ⟨hx, htt⟩ := getElem?_eq_some_bang hlkC
  have hlenT : minst.TABLES.length = C'.TABLES.length := by
    rw [← him.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.1
  obtain ⟨tbr, tbt', hta, hlk, hsub⟩ := Forall2_nth_of_length minst.TABLES C'.TABLES
    (minst_invert_tables s minst C C' hmi him) hlenT (proj_uN_0 x) (by omega)
  rw [htt] at hsub
  obtain ⟨lim', hlim'⟩ := externtype_table_sub_inv _ _ _ hsub
  rw [hlim'] at hlk
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _, _, _⟩ :=
    Store_ok_parts s hsok
  have htok := Forall2_nth_of_length s.TABLES ttl h6 h5 _ hta
  rw [show (s.TABLES[minst.TABLES[proj_uN_0 x]!]! : tableinst) = lookup_total s.TABLES _ from rfl, hlk] at htok
  obtain ⟨rl0, v_m, rt'', he1, he2, _, hrefs⟩ := tableinst_ok_invert s _ _ htok
  injection he1 with hA hB
  rw [← hA] at he2
  injection he2 with _ hrt
  subst hrt
  show Forall (fun r => Ref_ok s r rt) (lookup_total s.TABLES (minst.TABLES[proj_uN_0 x]!)).REFS
  rw [hlk]
  rw [hB]
  exact hrefs

/-- A module instance's function address at `k` is a valid external function of the context's
    type there (`Moduleinst_ok`'s own `Forall₂`). -/
theorem minst_func_externaddr (s : store) (minst : moduleinst) (C C' : context) (k : Nat) :
    Moduleinst_ok s minst C → inst_match C C' → k < C'.FUNCS.length →
    Externaddr_ok s (externaddr.FUNC (minst.FUNCS[k]!)) (externtype.FUNC (C'.FUNCS[k]!)) := by
  intro hmi him hk
  rw [← him.2.1] at hk ⊢
  cases hmi with
  | mk_Moduleinst_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlen hf =>
    exact Forall2_nth_of_length _ _ hf hlen k (by rw [hlen]; exact hk)

/-- The references of an element segment the module instance maps `y` to have the context's type. -/
theorem elem_refs_ok (s : store) (minst : moduleinst) (C C' : context) (y : elemidx) (rt : reftype) :
    Moduleinst_ok s minst C → inst_match C C' → C'.ELEMS[proj_uN_0 y]? = some rt →
    Forall (fun r => Ref_ok s r rt) (s.ELEMS[minst.ELEMS[proj_uN_0 y]!]!).REFS := by
  intro hmi him hlk
  obtain ⟨hy, hget⟩ := getElem?_eq_some_bang hlk
  have hlenE : minst.ELEMS.length = C'.ELEMS.length := by
    rw [← him.2.2.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.2.2
  obtain ⟨ref_lst, _, hrefs, hlk'⟩ := Forall2_nth_of_length minst.ELEMS C'.ELEMS
    (minst_invert_elems s minst C C' hmi him) hlenE (proj_uN_0 y) (by omega)
  rw [hget] at hrefs hlk'
  show Forall _ (lookup_total s.ELEMS _).REFS
  rw [hlk']; exact hrefs

/-- `memarg0`'s alignment fits an 8-bit access. -/
theorem memarg0_align8 : ((2 : Rat) ^ (proj_uN_0 memarg0.ALIGN)) ≤ ((8 : Nat) : Rat) / (8 : Rat) := by
  norm_num [memarg0, proj_uN_0]

/-- `local.LOCAL` is injective, so mapping it is too (Rocq inlines this as `map_local_inj`). -/
theorem map_local_inj (l1 l2 : List valtype) :
    Map (fun t => local.LOCAL t) l1 = Map (fun t => local.LOCAL t) l2 → l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => intro h; cases l2 with
    | nil => rfl
    | cons _ _ => simp [Map] at h
  | cons a l1 ih => intro h; cases l2 with
    | nil => simp [Map] at h
    | cons b l2 =>
      simp only [Map, List.map_cons, List.cons.injEq, local.LOCAL.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      rw [ih l2 h2]

/-- Inverting `Funcinst_ok` of a literal function instance. -/
theorem funcinst_ok_parts (s : store) (ft : functype) (mm : moduleinst) (fn : func) (ft' : functype) :
    Funcinst_ok s ({ TYPE := ft, MODULE := mm, CODE := fn } : funcinst) ft' →
    ∃ C0, Moduleinst_ok s mm C0 ∧ Func_ok C0 fn ft ∧ wf_context C0 := by
  intro h
  cases h with
  | mk_Funcinst_ok _ _ _ C0 _ hm hf _ hc _ => exact ⟨C0, hm, hf, hc⟩

/-- Inverting `Func_ok`: the body is typed in the function's local context. -/
theorem func_ok_body (C : context) (x : idx) (t_lst : List valtype) (instrs : List instr) (t1 t2 : List valtype) :
    Func_ok C (func.FUNC x (Map (fun t => local.LOCAL t) t_lst) instrs)
      (functype.mk_functype (.mk_list t1) (.mk_list t2)) →
    Instrs_ok (({
      TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
      LOCALS := t1 ++ t_lst, LABELS := [.mk_list t2], RETURN := some (.mk_list t2) } : context) ++ C)
      instrs (mkFunctype [] t2) := by
  intro h
  generalize hfn : func.FUNC x (Map (fun t => local.LOCAL t) t_lst) instrs = fn at h
  generalize hft : functype.mk_functype (.mk_list t1) (.mk_list t2) = ft at h
  cases h with
  | mk_Func_ok x' t_lst' e t1' t2' _ _ _ hexpr _ _ _ =>
    injection hfn with _ hm he
    have ht := map_local_inj _ _ hm
    subst ht he
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨rfl, rfl⟩ := hft
    cases hexpr
    assumption

/-- A local's default value has the local's type (Rocq inlines this in the `call_addr` case). -/
theorem default_val_ok (s : store) (t : valtype) : wf_store s → default_ t ≠ none →
    Val_ok s (Option.get! (default_ t)) t := by
  intro hS hd
  have hwf := default__is_wf t _ hd rfl
  cases t with
  | I32 => exact Val_ok.numtype s numtype.I32 _ hS hwf
  | I64 => exact Val_ok.numtype s numtype.I64 _ hS hwf
  | F32 => exact Val_ok.numtype s numtype.F32 _ hS hwf
  | F64 => exact Val_ok.numtype s numtype.F64 _ hS hwf
  | V128 => exact Val_ok.vectype s vectype.V128 _ hS hwf
  | FUNCREF => exact Val_ok.reftype s _ reftype.FUNCREF (Ref_ok.null s _ hS) hS
  | EXTERNREF => exact Val_ok.reftype s _ reftype.EXTERNREF (Ref_ok.null s _ hS) hS
  | BOT => exact absurd rfl hd

theorem default_vals_ok (s : store) (t_lst : List valtype) : wf_store s →
    Forall (fun t => default_ t ≠ none) t_lst →
    Forall₂ (fun t v => Val_ok s v t) t_lst (Map (fun t => Option.get! (default_ t)) t_lst) := by
  intro hS hd
  have : List.Forall₂ (fun t v => Val_ok s v t) t_lst (t_lst.map (fun t => Option.get! (default_ t))) := by
    induction t_lst with
    | nil => exact List.Forall₂.nil
    | cons t ts ih =>
      exact List.Forall₂.cons (default_val_ok s t hS (hd t (List.mem_cons_self ..)))
        (ih (fun x hx => hd x (List.mem_cons_of_mem _ hx)))
  exact (from_mathlib_forall₂ this).2

theorem Forall2_app_intro {α β : Type} {R : α → β → Prop} {l1 l2 : List α} {l1' l2' : List β} :
    l1.length = l1'.length → Forall₂ R l1 l1' → Forall₂ R l2 l2' → Forall₂ R (l1 ++ l2) (l1' ++ l2') := by
  intro hlen h1 h2 p hp
  rw [List.zip_append hlen] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp
```

</details>

### Worked example: decoding an `ais_cons_pre` chain

Here is how the `table_fill_succ` case (full code in §8.8) types the reduct
`[CONST I32 i, v, TABLE_SET x, CONST I32 (i+1), v, CONST I32 (n-1), TABLE_FILL x]`.
Each row is one `ais_cons_pre _ _ _ _ pre a1 a2 _` in the proof, read straight off the code (`rt` abbreviates `valtype_reftype rt`, the table's element type):

| # | Instruction | `pre` | `a1` (consumes) | `a2` (produces) | Stack before → after | Typed by |
|---|---|---|---|---|---|---|
| 1 | `CONST I32 i` | `[]` | `[]` | `[I32]` | `[]` → `[I32]` | `ais_const1` |
| 2 | `v` | `[I32]` | `[]` | `[rt]` | `[I32]` → `[I32, rt]` | `ais_val1` (needs `Val_ok s v rt`) |
| 3 | `TABLE_SET x` | `[]` | `[I32, rt]` | `[]` | `[I32, rt]` → `[]` | `ais_plain1` + `Instr_ok.table_set` |
| 4 | `CONST I32 (i+1)` | `[]` | `[]` | `[I32]` | `[]` → `[I32]` | `ais_const1` (needs the constant well-formed) |
| 5 | `v` | `[I32]` | `[]` | `[rt]` | `[I32]` → `[I32, rt]` | `ais_val1` |
| 6 | `CONST I32 (n-1)` | `[I32, rt]` | `[]` | `[I32]` | `[I32, rt]` → `[I32, rt, I32]` | `ais_const1` |
| 7 | `TABLE_FILL x` | `[]` | `[I32, rt, I32]` | `[]` | `[I32, rt, I32]` → `[]` | `ais_plain1` + `Instr_ok.table_fill` |
| — | end of list | | | | `[]` → `[]` | `ais_nil_refl` |

So the whole reduct has type `[] → []`. The redex `[CONST I32 i, v, CONST I32 n, TABLE_FILL x]` also has net type `[] → []`, and `ais_fill_inv` extracts from `htype` both `Val_ok s v rt` (needed in rows 2 and 5) and `isub : instrtype_sub ([] → []) (t1s → t2s)`. The final `construct_ais_subtyping … isub` (move 3) weakens the reduct's `[] → []` to `t1s → t2s`. Every bulk `succ` case is this same table with different rows.

## 8.4 Family A — entering a block or loop

**WASM.** `block bt instr*` runs `instr*` as a nested block whose type is given by the *blocktype* `bt`: no result, one result type `t`, or a type index `x` naming any `t1* → t2*` in the module's type section. That last form is why entering a block *reads* state: `fun_blocktype` resolves the index through the module instance (`fun_type`). On entry, the `k` values the block consumes move inside a `LABEL_` together with the body. A `loop` is entered the same way, but a branch to a loop's label **restarts** the loop rather than leaving it, so its `LABEL_` records the loop itself as its continuation and has arity `k` (the number of *inputs*, which a restart needs again); a block's `LABEL_` has an empty continuation and arity `n` (its outputs).

The blocktype resolver, for reference — [wasm2.0.lean:14310-14315](../../../../../src/test-lean-claude/wasm2.0.lean#L14310-L14315):
```lean
/- Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 -/
def fun_blocktype (v_state : state) (v_blocktype : blocktype) : functype :=
  match v_blocktype with
  | blocktype._RESULT none => functype.mk_functype (.mk_list []) (.mk_list [])
  | blocktype._RESULT (some t) => functype.mk_functype (.mk_list []) (.mk_list [t])
  | blocktype._IDX x => fun_type v_state x
```

**Rules** (including the head of the `Step_read` definition) — [wasm2.0.lean:14410-14423](../../../../../src/test-lean-claude/wasm2.0.lean#L14410-L14423):
```lean
/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.109 -/
inductive Step_read : config → List admininstr → Prop where
  | block (z : state) (k : Nat) (val_lst : List val) (bt : blocktype) (instr_lst : List instr) (v_n : n) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (fun_blocktype z bt) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    k = (List.length val_lst) →
    k = (List.length t_1_lst) →
    v_n = (List.length t_2_lst) →
    Step_read (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.BLOCK bt instr_lst])) [admininstr.LABEL_ v_n [] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))]
  | loop (z : state) (k : Nat) (val_lst : List val) (bt : blocktype) (instr_lst : List instr) (t_1_lst : List valtype) (v_n : n) (t_2_lst : List valtype) :
    (fun_blocktype z bt) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    k = (List.length val_lst) →
    k = (List.length t_1_lst) →
    v_n = (List.length t_2_lst) →
    Step_read (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.LOOP bt instr_lst])) [admininstr.LABEL_ k [instr.LOOP bt instr_lst] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))]
```

**Reading the rules.** `block`: `vals ++ [BLOCK bt instrs]` → `[LABEL_ n [] (vals ++ instrs)]`, provided `bt` resolves to `t1 → t2`, `|vals| = |t1| = k` and `n = |t2|`. `loop`: `vals ++ [LOOP bt instrs]` → `[LABEL_ k [LOOP bt instrs] (vals ++ instrs)]`.

**Proof cases** — [TypePreservation.lean:2042-2088](../../../../../src/test-lean-claude/TypePreservation.lean#L2042-L2088):
```lean
  | block z k val_lst bt instr_lst v_n t_1_lst t_2_lst h0 h1 h2 h3 =>
    obtain ⟨t3s, hV, hB⟩ := ais_composition_typing _ _ _ _ t1s t2s htype
    obtain ⟨vts, hsubV, hvok⟩ := ais_vals_typing_inversion _ _ val_lst t1s t3s hV
    obtain ⟨_, _, hpt, hsubB⟩ := ais_single_typing_inversion _ _ _ t3s t2s hB
    unfold ai_principal_typing at hpt
    obtain ⟨bt1, bt2, heq, hbt, hinstrs⟩ := hpt
    rw [heq] at hsubB
    obtain ⟨e1, e2⟩ := bt_inversion _ _ _ _ _ bt1 bt2 t_1_lst t_2_lst hmi hbt h0 him
    rw [e1, e2] at hsubB hbt hinstrs
    have hlen : vts.length = t_1_lst.length := by obtain ⟨hl, _⟩ := hvok; omega
    obtain ⟨hsub, hrs⟩ := instrtype_sub_compose_eq [] vts t_1_lst t_2_lst t1s t3s t2s hsubV hsubB hlen
    have hwfCL := wf_context_app _ _ (wf_context_label_only (list.mk_list t_2_lst)) hwfC'
    exact construct_ais_subtyping _ _ _ [] t_2_lst t1s t2s
      (construct_ais_typing_single _ _ _ [] t_2_lst
        (Instr_ok2.label _ v_C' v_n [] _ t_2_lst t_2_lst
          ((ais_empty_typing _ _ t_2_lst t_2_lst).mpr ⟨hwfC', hwfS, resulttype_sub_refl t_2_lst⟩)
          (construct_ais_compose _ _ _ _ [] t_1_lst t_2_lst
            (construct_ais_vals _ _ val_lst [] t_1_lst vts hwfCL hwfS
              ((instrtype_sub_iff_resulttype_sub vts t_1_lst []).mp hrs) hvok)
            (construct_instrs_from_ais _ _ instr_lst t_1_lst t_2_lst hwfS hinstrs))
          hwfS hwfC' (hwf' _ (List.mem_singleton_self _)) (wf_context_label_only _) h3)) hsub
  | loop z k val_lst bt instr_lst t_1_lst v_n t_2_lst h0 h1 h2 h3 =>
    obtain ⟨t3s, hV, hB⟩ := ais_composition_typing _ _ _ _ t1s t2s htype
    obtain ⟨vts, hsubV, hvok⟩ := ais_vals_typing_inversion _ _ val_lst t1s t3s hV
    obtain ⟨_, _, hpt, hsubB⟩ := ais_single_typing_inversion _ _ _ t3s t2s hB
    unfold ai_principal_typing at hpt
    obtain ⟨bt1, bt2, heq, hbt, hinstrs⟩ := hpt
    rw [heq] at hsubB
    obtain ⟨e1, e2⟩ := bt_inversion _ _ _ _ _ bt1 bt2 t_1_lst t_2_lst hmi hbt h0 him
    rw [e1, e2] at hsubB hbt hinstrs
    have hlen : vts.length = t_1_lst.length := by obtain ⟨hl, _⟩ := hvok; omega
    obtain ⟨hsub, hrs⟩ := instrtype_sub_compose_eq [] vts t_1_lst t_2_lst t1s t3s t2s hsubV hsubB hlen
    have hwfCL := wf_context_app _ _ (wf_context_label_only (list.mk_list t_1_lst)) hwfC'
    have hwfI : wf_instr (instr.LOOP bt instr_lst) :=
      (wf_admininstr_instr _).mpr (wf_config_ais hwfc (admininstr.LOOP bt instr_lst) (by simp))
    exact construct_ais_subtyping _ _ _ [] t_2_lst t1s t2s
      (construct_ais_typing_single _ _ _ [] t_2_lst
        (Instr_ok2.label _ v_C' k [instr.LOOP bt instr_lst] _ t_2_lst t_1_lst
          (construct_ais_typing_single _ _ _ t_1_lst t_2_lst
            (Instr_ok2.plain _ _ (instr.LOOP bt instr_lst) t_1_lst t_2_lst
              (Instr_ok.loop _ bt instr_lst t_1_lst t_2_lst hbt hinstrs hwfC' hwfI (wf_context_label_only _))
              hwfS hwfC' hwfI))
          (construct_ais_compose _ _ _ _ [] t_1_lst t_2_lst
            (construct_ais_vals _ _ val_lst [] t_1_lst vts hwfCL hwfS
              ((instrtype_sub_iff_resulttype_sub vts t_1_lst []).mp hrs) hvok)
            (construct_instrs_from_ais _ _ instr_lst t_1_lst t_2_lst hwfS hinstrs))
          hwfS hwfC' (hwf' _ (List.mem_singleton_self _)) (wf_context_label_only _) h2)) hsub
```

**Explanation.** For `block`: split `htype` into the pushed values and the `BLOCK` (`ais_composition_typing`); the values get types `vts` (`ais_vals_typing_inversion`); the `BLOCK`'s principal type gives its static type `bt1 → bt2`, a `Blocktype_ok` fact, and the body's typing `hinstrs` in the context with the block's label pushed. `bt_inversion` then shows the static `bt1 → bt2` and the runtime `t_1_lst → t_2_lst` agree — the context's type section and the module instance's are the same, by `Moduleinst_ok` and `inst_match`. `instrtype_sub_compose_eq` merges the two subtyping facts into one for the whole sequence (`hsub`) and relates `vts` to `t_1_lst` (`hrs`). The reduct is then built from the inside out: the label's continuation `[]` (typed by `ais_empty_typing`), its body `vals ++ instrs` in the label-extended context (values by `construct_ais_vals`, instructions by `construct_instrs_from_ais`, joined by `construct_ais_compose`), assembled with the `Instr_ok2.label` rule (primer §0.5), lifted to a one-element list, and weakened with `hsub`. The `loop` case is the same, except the label's continuation `[LOOP bt instrs]` must itself be typed (at `t_1_lst → t_2_lst`, via the static `Instr_ok.loop` rule), and the label records the input types `t_1_lst`.

## 8.5 Family B — function calls

**WASM.** `call x` calls function `x` of the current module. `call_indirect x y` pops an `i32` index `i` and reads entry `i` of table `x`; if that entry is a reference to a function whose type equals type `y` of the module, it calls that function, and otherwise — index out of bounds, null entry, or **signature mismatch** — it traps. This runtime signature check is what keeps indirect calls type-safe even though the table's contents are only known at run time. Both forms first resolve to the administrative `CALL_ADDR a`, naming a store function address. `CALL_ADDR a` with the arguments on the stack then performs the call: it looks up the function instance at `a` (type `t1* → t2*`, owning module instance `mm`, code `func x locals body`), builds a frame whose locals are the arguments followed by a default value (zero or null) for each declared local, and replaces the call with `FRAME_ n f [LABEL_ n [] body]`. Because the frame carries the **callee's** module instance `mm`, a call can cross into another module (an imported function) and the callee's indices resolve against its own module.

A concrete instance (schematic): calling a function of type `[i32] → [i32]` that declares one extra local of type `i64`, with argument 7:

```
[CONST I32 7, CALL_ADDR a]
  ─ Step_read.call_addr ─→  [FRAME_ 1 {LOCALS := [CONST I32 7, CONST I64 0], MODULE := mm} [LABEL_ 1 [] body]]
```

The "otherwise" relation used by `call_indirect_trap` (§8.2, pattern 2) — [wasm2.0.lean:14317-14325](../../../../../src/test-lean-claude/wasm2.0.lean#L14317-L14325):
```lean
/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:127.1-129.15 -/
inductive Step_read_before_call_indirect_trap : config → Prop where
  | call_indirect_call_0 (z : state) (i : num_) (x : idx) (y : idx) (a : addr) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    (proj_num__0 i) ≠ none →
    (((fun_table z x).REFS)[proj_uN_0 (Option.get! (proj_num__0 i))]!) = (ref.REF_FUNC_ADDR a) →
    a < (List.length (fun_funcinst z)) →
    (fun_type z y) = (((fun_funcinst z)[a]!).TYPE) →
    Step_read_before_call_indirect_trap (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CALL_INDIRECT x y])
```

**Rules** — [wasm2.0.lean:14424-14463](../../../../../src/test-lean-claude/wasm2.0.lean#L14424-L14463):
```lean
  | call (z : state) (x : idx) :
    (proj_uN_0 x) < (List.length (fun_funcaddr z)) →
    Step_read (config.mk_config z [admininstr.CALL x]) [admininstr.CALL_ADDR ((fun_funcaddr z)[proj_uN_0 x]!)]
  | call_indirect_call (z : state) (i : num_) (x : idx) (y : idx) (a : addr) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    (proj_num__0 i) ≠ none →
    (((fun_table z x).REFS)[proj_uN_0 (Option.get! (proj_num__0 i))]!) = (ref.REF_FUNC_ADDR a) →
    a < (List.length (fun_funcinst z)) →
    (fun_type z y) = (((fun_funcinst z)[a]!).TYPE) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CALL_INDIRECT x y]) [admininstr.CALL_ADDR a]
  | call_indirect_trap (z : state) (i : num_) (x : idx) (y : idx) :
    ¬ Step_read_before_call_indirect_trap (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CALL_INDIRECT x y]) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CALL_INDIRECT x y]) [admininstr.TRAP]
  | call_addr (z : state) (k : Nat) (val_lst : List val) (a : addr) (v_n : n) (f : frame) (instr_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) (mm : moduleinst) (v_func : func) (x : idx) (t_lst : List valtype) :
    a < (List.length (fun_funcinst z)) →
    ((fun_funcinst z)[a]!) = ({
      TYPE := functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)
      MODULE := mm
      CODE := v_func : funcinst
    }) →
    v_func = (func.FUNC x (Map (fun (t_elem : valtype) => local.LOCAL t_elem) t_lst) instr_lst) →
    Forall (fun (t_elem : valtype) => (default_ t_elem) ≠ none) t_lst →
    f = ({
      LOCALS := val_lst ++ (Map (fun (t_elem : valtype) => Option.get! (default_ t_elem)) t_lst)
      MODULE := mm : frame
    }) →
    wf_funcinst ({
      TYPE := functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)
      MODULE := mm
      CODE := v_func : funcinst
    }) →
    wf_func (func.FUNC x (Map (fun (t_elem : valtype) => local.LOCAL t_elem) t_lst) instr_lst) →
    wf_frame ({
      LOCALS := val_lst ++ (Map (fun (t_elem : valtype) => Option.get! (default_ t_elem)) t_lst)
      MODULE := mm : frame
    }) →
    k = (List.length val_lst) →
    k = (List.length t_1_lst) →
    v_n = (List.length t_2_lst) →
    Step_read (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.CALL_ADDR a])) [admininstr.FRAME_ v_n f [admininstr.LABEL_ v_n [] (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst)]]
```

**Reading the rules.** `call`: `[CALL x]` → `[CALL_ADDR (module's function address x)]`. `call_indirect_call`: `[CONST I32 i, CALL_INDIRECT x y]` → `[CALL_ADDR a]` when table `x`'s entry `i` is `REF_FUNC_ADDR a`, `a` is a valid function address, and type `y` equals that function's type; `call_indirect_trap`: otherwise `[TRAP]`. `call_addr`: `vals ++ [CALL_ADDR a]` → `[FRAME_ n f [LABEL_ n [] body]]`, with the frame `f` as described above and the arities matching the function's type (`k = |vals| = |t1|`, `n = |t2|`).

**Proof cases** — [TypePreservation.lean:2089-2166](../../../../../src/test-lean-claude/TypePreservation.lean#L2089-L2166):
```lean
  | call z x h0 =>
    obtain ⟨u1, u2, hlk, hs⟩ := pt_call _ _ x htype
    obtain ⟨hx, hget⟩ := getElem?_eq_some_bang hlk
    have hea := minst_func_externaddr _ _ _ _ _ hmi him hx
    rw [hget] at hea
    exact construct_ais_subtyping _ _ _ u1 u2 t1s t2s
      (construct_ais_typing_single _ _ _ u1 u2 (Instr_ok2.call_addr _ _ _ u1 u2 hea hwfS hwfC'
        (hwf' _ (by simp)) (wf_externtype.externtype_case_0 _))) hs
  | call_indirect_call z i x y a h0 h1 h2 h3 h4 =>
    obtain ⟨t3, hop, hc⟩ := ais_seq_typing_inversion _ _ [admininstr.CALL_INDIRECT x y] _ t1s t2s htype
    obtain ⟨u1, u2, lim, _, hty, hs⟩ := pt_call_indirect _ _ x y hop
    have s1 := ais_const_typing_inversion _ _ numtype.I32 i t1s t3 hc
    have isub := (instrtype_sub_compose_le [] [valtype_numtype numtype.I32] [valtype.I32] u1 u2 t1s t3 t2s s1 hs rfl).1
    simp only [List.append_nil] at isub
    obtain ⟨hy, hgety⟩ := getElem?_eq_some_bang hty
    have htypes := minst_invert_functypes _ _ _ _ hmi him
    have h4' : v_f.MODULE.TYPES[proj_uN_0 y]! = (v_s.FUNCS[a]!).TYPE := h4
    have hfty : (v_s.FUNCS[a]!).TYPE = mkFunctype u1 u2 := by
      rw [← h4', ← htypes]; exact hgety
    have hea0 := Externaddr_ok.func v_s a (v_s.FUNCS[a]!) h3 rfl hwfS
      (by rw [hfty]; exact wf_externtype.externtype_case_0 _)
    rw [hfty] at hea0
    exact construct_ais_subtyping _ _ _ u1 u2 t1s t2s
      (construct_ais_typing_single _ _ _ u1 u2 (Instr_ok2.call_addr _ _ _ u1 u2 hea0 hwfS hwfC'
        (hwf' _ (by simp)) (wf_externtype.externtype_case_0 _))) isub
  | call_indirect_trap z i x y h0 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | call_addr z k val_lst a v_n f instr_lst t_1_lst t_2_lst mm v_func x t_lst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    obtain ⟨t3s, hV, hC⟩ := ais_composition_typing _ _ _ _ t1s t2s htype
    obtain ⟨vts, hsubV, hvok⟩ := ais_vals_typing_inversion _ _ val_lst t1s t3s hV
    obtain ⟨ts1, ts2, hext, hsubC⟩ := pt_call_addr _ _ a hC
    obtain ⟨xt, fi, ha, hfi, hxt, _, hxsub⟩ := Externaddr_invert_funcs _ _ _ hext
    subst hxt
    have hft := externtype_func_eq _ _ hxsub
    have h1' : v_s.FUNCS[a]! = ({
        TYPE := functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst), MODULE := mm, CODE := v_func } : funcinst) := h1
    have hfi' : fi = _ := hfi.symm.trans h1'
    rw [hfi'] at hft
    simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at hft
    obtain ⟨e1, e2⟩ := hft
    rw [← e1, ← e2] at hsubC
    have hlen : vts.length = t_1_lst.length := by obtain ⟨hl, _⟩ := hvok; omega
    obtain ⟨hsub, hrs⟩ := instrtype_sub_compose_eq [] vts t_1_lst t_2_lst t1s t3s t2s hsubV hsubC hlen
    have hvts : vts = t_1_lst := resulttype_sub_non_bot _ _ (Vals_ok_non_bot _ _ _ hvok) hrs
    rw [hvts] at hvok
    obtain ⟨_, _, _, ftl, _, _, _, _, _, _, _, _, hflen, hfok, _⟩ := Store_ok_parts _ hsok
    have hfiok : Funcinst_ok v_s (v_s.FUNCS[a]!) (ftl[a]!) := Forall2_nth_of_length _ _ hfok hflen a ha
    rw [h1'] at hfiok
    obtain ⟨C0, hmi0, hfo, hwfC0⟩ := funcinst_ok_parts _ _ _ _ _ hfiok
    rw [h2] at hfo
    have hIok := func_ok_body _ _ _ _ _ _ hfo
    subst h4
    have hwfF := hwf' _ (List.mem_singleton_self _)
    have hwfL : wf_admininstr (admininstr.LABEL_ v_n [] (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst)) := by
      cases hwfF with | admininstr_case_72 _ _ _ _ hl => exact hl _ (List.mem_singleton_self _)
    have hwfCL : wf_context ({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
        LOCALS := t_1_lst ++ t_lst, LABELS := [], RETURN := none } : context) :=
      wf_context.context_case_ _ _ _ [] [] _ _ _ _ _ (by intro x hx; simp at hx) (by intro x hx; simp at hx)
    have hwfC1 := wf_context_app _ _ hwfCL hwfC0
    have hwfCR := wf_context_app _ _ (wf_context_return_only (list.mk_list t_2_lst)) hwfC1
    have hframe : Frame_ok v_s _ (({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
        LOCALS := t_1_lst ++ t_lst, LABELS := [], RETURN := none } : context) ++ C0) :=
      Frame_ok.mk_Frame_ok v_s _ mm (t_1_lst ++ t_lst) C0 hmi0
        (by simp only [List.length_append, Map, List.length_map]; omega)
        (Forall2_app_intro (by omega) hvok.2 (default_vals_ok _ _ hwfS h3)) hwfS hwfC0 h7 hwfCL
    refine construct_ais_subtyping _ _ _ [] t_2_lst t1s t2s
      (construct_ais_typing_single _ _ _ [] t_2_lst
        (Instr_ok2.Instr_ok2_frame _ v_C' v_n _ _ t_2_lst _ hframe ?_ hwfS hwfC' hwfC1 hwfF
          (wf_context_return_only _) h10)) hsub
    refine Expr_ok2.mk_Expr_ok2 _ _ _ t_2_lst ?_ hwfS hwfCR
      (fun e he => by rw [List.mem_singleton] at he; subst he; exact hwfL)
    exact construct_ais_typing_single _ _ _ [] t_2_lst
      (Instr_ok2.label _ _ v_n [] _ t_2_lst t_2_lst
        ((ais_empty_typing _ _ t_2_lst t_2_lst).mpr ⟨hwfCR, hwfS, resulttype_sub_refl _⟩)
        (construct_instrs_from_ais _ _ instr_lst [] t_2_lst hwfS hIok)
        hwfS hwfCR hwfL (wf_context_label_only _) h10)
```

**Explanation.**
- `call`: `pt_call` gives `C'.FUNCS[x] = u1 → u2` and the subtyping. `minst_func_externaddr` (built from `Moduleinst_ok`'s function-address premises) says the module's function address `x` is a store function of exactly that type, i.e. `Externaddr_ok s (FUNC addr) (FUNC (u1 → u2))` — precisely the premise of the `Instr_ok2.call_addr` typing rule for `CALL_ADDR`. Type it, weaken.
- `call_indirect_call`: `htype` is split into the constant and the `CALL_INDIRECT`, whose principal type is `u1 ++ [I32] → u2` with `C'.TYPES[y] = u1 → u2` (`pt_call_indirect`); combining with the constant's `[] → [I32]` (`instrtype_sub_compose_le`) leaves `u1 → u2` as the type to give `CALL_ADDR a`. The rule's own premise `h4` says type `y` *is* the function's type — the runtime signature check — and `minst_invert_functypes` says the context's type section equals the module instance's, so the function at `a` has type `u1 → u2` (`hfty`). That, with the bound `h3`, builds `Externaddr_ok.func` directly.
- `call_indirect_trap`: `construct_ais_trap`.
- `call_addr`, the most involved case: (1) split `htype` into the arguments (types `vts`) and `CALL_ADDR a` (principal type `ts1 → ts2`, with an `Externaddr_ok` fact). (2) `Externaddr_invert_funcs` and `externtype_func_eq` (for functions, extern subtyping is equality) identify `ts1 → ts2` with the type recorded in the function instance, which the rule's premise `h1` spells out as `t_1_lst → t_2_lst`. (3) Merge the subtyping facts; since values never have type `BOT`, the arguments' types `vts` must *equal* `t_1_lst` (`resulttype_sub_non_bot` with `Vals_ok_non_bot`). (4) From `Store_ok`, the function instance at `a` is `Funcinst_ok` (`Store_ok_parts` + `Forall2_nth_of_length`), which yields its module's `Moduleinst_ok s mm C0` and its code's `Func_ok` (`funcinst_ok_parts`), hence the body's typing in the function's local context: locals `t_1_lst ++ t_lst`, label and return both `t_2_lst` (`func_ok_body`). (5) Build `Frame_ok` for the new frame: its module instance `mm` is fine at `C0`, the argument values have types `t_1_lst` (`hvok`), and the default values have the declared local types (`default_vals_ok`), glued with `Forall2_app_intro`. (6) Assemble from the inside out: the label holding the body (`Instr_ok2.label`, empty continuation), inside an `Expr_ok2` in the callee's context with `RETURN` set, inside the `FRAME_` (`Instr_ok2.Instr_ok2_frame`, which needs the `Frame_ok` from step 5), and weaken. Note the **context switch at the frame boundary**: the `FRAME_` is typed in the caller's context `v_C'`, while everything inside it is typed in the callee's context built from `C0`.

## 8.6 Family C — references, locals, globals

**WASM.** `ref.func x` pushes a reference to function `x` (resolved to its store address, `REF_FUNC_ADDR`). `local.get x` pushes local `x` of the current frame. `global.get x` pushes the current value of global `x`, found through the two-level lookup of primer §0.2.

**Rules** — [wasm2.0.lean:14464-14468](../../../../../src/test-lean-claude/wasm2.0.lean#L14464-L14468):
```lean
  | ref_func (z : state) (x : idx) :
    (proj_uN_0 x) < (List.length (fun_funcaddr z)) →
    Step_read (config.mk_config z [admininstr.REF_FUNC x]) [admininstr.REF_FUNC_ADDR ((fun_funcaddr z)[proj_uN_0 x]!)]
  | local_get (z : state) (x : idx) : Step_read (config.mk_config z [admininstr.LOCAL_GET x]) [admininstr_val (fun_local z x)]
  | global_get (z : state) (x : idx) : Step_read (config.mk_config z [admininstr.GLOBAL_GET x]) [admininstr_val ((fun_global z x).VALUE)]
```

**Proof cases** — [TypePreservation.lean:2167-2185](../../../../../src/test-lean-claude/TypePreservation.lean#L2167-L2185):
```lean
  | ref_func z x h0 =>
    obtain ⟨ft, hlk, hs⟩ := pt_ref_func _ _ x htype
    obtain ⟨hx, _⟩ := getElem?_eq_some_bang hlk
    have hea := minst_func_externaddr _ _ _ _ _ hmi him hx
    have hr : Ref_ok v_s (ref.REF_FUNC_ADDR (v_f.MODULE.FUNCS[proj_uN_0 x]!)) reftype.FUNCREF :=
      Ref_ok.func _ _ _ hea hwfS (wf_externtype.externtype_case_0 _)
    exact construct_ais_subtyping _ _ _ [] _ t1s t2s (ais_ref1 _ _ _ _ hr hwfC' hwfS) hs
  | local_get z x =>
    obtain ⟨t, hlk, hs⟩ := pt_local_get _ _ x htype
    obtain ⟨hx, hget⟩ := getElem?_eq_some_bang hlk
    have hv : Val_ok v_s (v_f.LOCALS[proj_uN_0 x]!) t := by
      have h := Forall2_nth_of_length v_C'.LOCALS v_f.LOCALS hvals.2 hvals.1 (proj_uN_0 x) hx
      rw [hget] at h; exact h
    exact construct_ais_subtyping _ _ _ [] [t] t1s t2s (ais_val1 _ _ _ t hv hwfC' hwfS) hs
  | global_get z x =>
    obtain ⟨t, m, hlk, hs⟩ := pt_global_get _ _ x htype
    obtain ⟨hx, hget⟩ := getElem?_eq_some_bang hlk
    have hv := lookup_global (proj_uN_0 x) v_C v_C' m t v_s v_f.MODULE hx hget hmi him hsok
    exact construct_ais_subtyping _ _ _ [] [t] t1s t2s (ais_val1 _ _ _ t hv hwfC' hwfS) hs
```

**Explanation.** Each case extracts the operator's principal type (`pt_ref_func`, `pt_local_get`, `pt_global_get`), proves the pushed value has that type, types the one-element reduct, and weakens.
- `ref_func`: `minst_func_externaddr` again gives an `Externaddr_ok` fact for the function's store address, which is exactly what `Ref_ok.func` needs; `ais_ref1` types the reference.
- `local_get`: `pt_local_get` says `C'.LOCALS[x] = t`. The hypothesis `hvals : Vals_ok v_s v_f.LOCALS v_C'.LOCALS` pairs each local's value with its declared type, and `Forall2_nth_of_length` reads off position `x` — it needs both halves of `Vals_ok`, the `Forall₂` (`hvals.2`) and the length equation (`hvals.1`). This case is the reason for the signature deviation discussed in §8.1.
- `global_get`: `lookup_global` (built from `Store_ok`, `Moduleinst_ok`, and `inst_match`) says the store's global at the translated address holds a value of the global's declared type.

## 8.7 Family D — single table reads

**WASM.** `table.get x` pops an `i32` index and pushes that element of table `x`, trapping if the index is out of bounds. `table.size x` pushes table `x`'s current length.

**Rules** — [wasm2.0.lean:14469-14479](../../../../../src/test-lean-claude/wasm2.0.lean#L14469-L14479):
```lean
  | table_get_trap (z : state) (i : num_) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) ≥ (List.length ((fun_table z x).REFS)) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.TABLE_GET x]) [admininstr.TRAP]
  | table_get_val (z : state) (i : num_) (x : idx) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    (proj_num__0 i) ≠ none →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.TABLE_GET x]) [admininstr_ref (((fun_table z x).REFS)[proj_uN_0 (Option.get! (proj_num__0 i))]!)]
  | table_size (z : state) (x : idx) (v_n : n) :
    (List.length ((fun_table z x).REFS)) = v_n →
    Step_read (config.mk_config z [admininstr.TABLE_SIZE x]) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))]
```

**Proof cases** — [TypePreservation.lean:2186-2199](../../../../../src/test-lean-claude/TypePreservation.lean#L2186-L2199):
```lean
  | table_get_trap z i x h0 h1 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | table_get_val z i x h0 h1 =>
    obtain ⟨t3, hop, hc⟩ := ais_seq_typing_inversion _ _ [admininstr.TABLE_GET x] _ t1s t2s htype
    obtain ⟨rt, lim, hlk, hs⟩ := pt_table_get _ _ x hop
    have s1 := ais_const_typing_inversion _ _ numtype.I32 i t1s t3 hc
    have isub := (instrtype_sub_compose_eq [] [valtype_numtype numtype.I32] [valtype.I32] [valtype_reftype rt]
      t1s t3 t2s s1 hs rfl).1
    have hrefs := table_refs_ok _ _ _ _ x rt lim hsok hmi him hlk
    have hr := hrefs ((fun_table (state.mk_state v_s v_f) x).REFS[proj_uN_0 (Option.get! (proj_num__0 i))]!)
      (by rw [getElem!_pos (fun_table (state.mk_state v_s v_f) x).REFS _ h0]; exact List.getElem_mem h0)
    exact construct_ais_subtyping _ _ _ [] _ t1s t2s (ais_ref1 _ _ _ rt hr hwfC' hwfS) isub
  | table_size z x v_n h0 =>
    exact const_I32_result _ _ _ t1s t2s (wf_const_num (hwf' _ (by simp))) hwfC' hwfS (pt_table_size _ _ x htype)
```

**Explanation.** `table_get_trap`: `construct_ais_trap`. `table_get_val`: split `htype` into the constant and the `TABLE_GET` (principal type `[I32] → [rt]` for the table's element type `rt`), and compose the subtyping facts. `table_refs_ok` (from `Store_ok`, `Moduleinst_ok`, `inst_match`) states that *every* reference in the store's table at the translated address has type `rt`; the rule's bound `h0` puts the fetched element in that table, so it is `Ref_ok … rt`, and `ais_ref1` types it. `table_size`: `const_I32_result` types the result constant at `[] → [I32]`, weakened by `pt_table_size`'s fact; well-formedness of the constant comes from `hwf'`.

## 8.8 Family E — bulk table operations

**WASM.** `table.fill x` (operands: start `i`, value `v`, count `n`) sets `n` entries of table `x` from `i` onward to `v`. `table.copy x y` (destination `j`, source `i`, count `n`) copies `n` entries from table `y` into table `x`, handling overlap like `memmove`. `table.init x y` (destination `j`, source offset `i`, count `n`) copies `n` references from element segment `y` into table `x`. All three follow pattern 1 of §8.2.

**Rules** — [wasm2.0.lean:14480-14536](../../../../../src/test-lean-claude/wasm2.0.lean#L14480-L14536):
```lean
  | table_fill_trap (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS)) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_FILL x]) [admininstr.TRAP]
  | table_fill_zero (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z x).REFS)) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_FILL x]) []
  | table_fill_succ (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    v_n ≠ 0 →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z x).REFS)) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_FILL x]) [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.TABLE_SET x, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.TABLE_FILL x]
  | table_copy_trap (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z y).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) [admininstr.TRAP]
  | table_copy_zero (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) []
  | table_copy_le (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 j) ≠ none →
    (proj_num__0 i) ≠ none →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    (proj_uN_0 (Option.get! (proj_num__0 j))) ≤ (proj_uN_0 (Option.get! (proj_num__0 i))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.TABLE_GET y, admininstr.TABLE_SET x, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.TABLE_COPY x y]
  | table_copy_gt (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 j) ≠ none →
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 j))) > (proj_uN_0 (Option.get! (proj_num__0 i))) →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) : Int) - (1 : Int))))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) : Int) - (1 : Int))))), admininstr.TABLE_GET y, admininstr.TABLE_SET x, admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.TABLE_COPY x y]
  | table_init_trap (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_elem z y).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_INIT x y]) [admininstr.TRAP]
  | table_init_zero (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_elem z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_INIT x y]) []
  | table_init_succ (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_elem z y).REFS)) →
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_elem z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_INIT x y]) [admininstr.CONST numtype.I32 j, admininstr_ref (((fun_elem z y).REFS)[proj_uN_0 (Option.get! (proj_num__0 i))]!), admininstr.TABLE_SET x, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.TABLE_INIT x y]
```

**Reading the rules.** For each operation: `_trap` when `i + n` or `j + n` exceeds the relevant length; `_zero` when in bounds and `n = 0` → `[]`; and the step that peels one element:
- `table_fill_succ` → `[CONST I32 i, v, TABLE_SET x, CONST I32 (i+1), v, CONST I32 (n-1), TABLE_FILL x]`;
- `table_copy_le` (`j ≤ i`) → `[CONST I32 j, CONST I32 i, TABLE_GET y, TABLE_SET x, CONST I32 (j+1), CONST I32 (i+1), CONST I32 (n-1), TABLE_COPY x y]` — copy the first element, move forward;
- `table_copy_gt` (`j > i`) → the same shape with `j+n-1` and `i+n-1` in front and `j`, `i` kept for the recursive call — copy the last element, so overlapping ranges come out right;
- `table_init_succ` → `[CONST I32 j, (element i of segment y), TABLE_SET x, CONST I32 (j+1), CONST I32 (i+1), CONST I32 (n-1), TABLE_INIT x y]`.

**Proof cases** — [TypePreservation.lean:2200-2298](../../../../../src/test-lean-claude/TypePreservation.lean#L2200-L2298):
```lean
  | table_fill_trap z i v_val v_n x h0 h1 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | table_fill_zero z i v_val v_n x h0 h1 h2 =>
    exact (ais_empty_typing _ _ t1s t2s).mpr ⟨hwfC', hwfS, instrtype_sub_empty _ _
      (ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_val_arg _ _ _) (inv_const_arg _ _ _ _)
        (fun u1 u2 h => let ⟨_, _, _, hs⟩ := pt_table_fill _ _ x h; ⟨_, _, _, hs⟩) htype)⟩
  | table_fill_succ z i v_val v_n x h0 h1 h2 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨rt, lim, hlk, _⟩ := pt_table_fill _ _ x hop
    obtain ⟨hvok, isub⟩ := ais_fill_inv _ _ i _ v_val _ (valtype_reftype rt) t1s t2s
      (fun u1 u2 h => by
        obtain ⟨rt', lim', hlk', hs⟩ := pt_table_fill _ _ x h
        rw [hlk] at hlk'; injection hlk' with h'; injection h' with _ hrt; rw [hrt]; exact hs) htype
    obtain ⟨hx, hget⟩ := getElem?_eq_some_bang hlk
    have hwftt : wf_tabletype (tabletype.mk_tabletype lim rt) := by rw [← hget]; exact wf_context_tab _ _ hx hwfC'
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype_reftype rt] [] (ais_val1 _ _ _ _ hvok hwfC' hwfS)
        (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype_reftype rt] [] []
          (ais_plain1 _ _ (instr.TABLE_SET x) _ _ hwfS (Instr_ok.table_set _ x rt lim hx hget hwfC'
            ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_SET x) (by simp))) hwftt))
          (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
            (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype_reftype rt] [] (ais_val1 _ _ _ _ hvok hwfC' hwfS)
              (ais_cons_pre _ _ _ _ [valtype.I32, valtype_reftype rt] [] [valtype.I32] []
                (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
                (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype_reftype rt, valtype.I32] [] []
                  (ais_plain1 _ _ (instr.TABLE_FILL x) _ _ hwfS (Instr_ok.table_fill _ x rt lim hx hget hwfC'
                    ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_FILL x) (by simp))) hwftt))
                  (ais_nil_refl _ _ [] hwfC' hwfS)))))))
  | table_copy_trap z j i v_n x y h0 h1 h2 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | table_copy_zero z j i v_n x y h0 h1 h2 h3 =>
    exact (ais_empty_typing _ _ t1s t2s).mpr ⟨hwfC', hwfS, instrtype_sub_empty _ _
      (ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
        (fun u1 u2 h => let ⟨_, _, _, _, _, hs⟩ := pt_table_copy _ _ x y h; ⟨_, _, _, hs⟩) htype)⟩
  | table_copy_le z j i v_n x y h0 h1 h2 h3 h4 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨rt, lim1, lim2, hlx, hly, _⟩ := pt_table_copy _ _ x y hop
    have isub := ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
      (fun u1 u2 h => let ⟨_, _, _, _, _, hs⟩ := pt_table_copy _ _ x y h; ⟨_, _, _, hs⟩) htype
    obtain ⟨hx, hgetx⟩ := getElem?_eq_some_bang hlx
    obtain ⟨hy, hgety⟩ := getElem?_eq_some_bang hly
    have hwftt1 : wf_tabletype (tabletype.mk_tabletype lim1 rt) := by rw [← hgetx]; exact wf_context_tab _ _ hx hwfC'
    have hwftt2 : wf_tabletype (tabletype.mk_tabletype lim2 rt) := by rw [← hgety]; exact wf_context_tab _ _ hy hwfC'
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [valtype.I32] [valtype_reftype rt] [] (ais_plain1 _ _ (instr.TABLE_GET y) _ _ hwfS (Instr_ok.table_get _ y rt lim2 hy hgety hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_GET y) (by simp))) hwftt2))
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype_reftype rt] [] [] (ais_plain1 _ _ (instr.TABLE_SET x) _ _ hwfS (Instr_ok.table_set _ x rt lim1 hx hgetx hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_SET x) (by simp))) hwftt1))
      (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32, valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.TABLE_COPY x y) _ _ hwfS (Instr_ok.table_copy _ x y lim1 rt lim2 hx hgetx hy hgety hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_COPY x y) (by simp))) hwftt1 hwftt2))
      (ais_nil_refl _ _ [] hwfC' hwfS)))))))))
  | table_copy_gt z j i v_n x y h0 h1 h2 h3 h4 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨rt, lim1, lim2, hlx, hly, _⟩ := pt_table_copy _ _ x y hop
    have isub := ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
      (fun u1 u2 h => let ⟨_, _, _, _, _, hs⟩ := pt_table_copy _ _ x y h; ⟨_, _, _, hs⟩) htype
    obtain ⟨hx, hgetx⟩ := getElem?_eq_some_bang hlx
    obtain ⟨hy, hgety⟩ := getElem?_eq_some_bang hly
    have hwftt1 : wf_tabletype (tabletype.mk_tabletype lim1 rt) := by rw [← hgetx]; exact wf_context_tab _ _ hx hwfC'
    have hwftt2 : wf_tabletype (tabletype.mk_tabletype lim2 rt) := by rw [← hgety]; exact wf_context_tab _ _ hy hwfC'
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [valtype.I32] [valtype_reftype rt] [] (ais_plain1 _ _ (instr.TABLE_GET y) _ _ hwfS (Instr_ok.table_get _ y rt lim2 hy hgety hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_GET y) (by simp))) hwftt2))
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype_reftype rt] [] [] (ais_plain1 _ _ (instr.TABLE_SET x) _ _ hwfS (Instr_ok.table_set _ x rt lim1 hx hgetx hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_SET x) (by simp))) hwftt1))
      (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32, valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.TABLE_COPY x y) _ _ hwfS (Instr_ok.table_copy _ x y lim1 rt lim2 hx hgetx hy hgety hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_COPY x y) (by simp))) hwftt1 hwftt2))
      (ais_nil_refl _ _ [] hwfC' hwfS)))))))))
  | table_init_trap z j i v_n x y h0 h1 h2 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | table_init_zero z j i v_n x y h0 h1 h2 h3 =>
    exact (ais_empty_typing _ _ t1s t2s).mpr ⟨hwfC', hwfS, instrtype_sub_empty _ _
      (ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
        (fun u1 u2 h => let ⟨_, _, _, _, hs⟩ := pt_table_init _ _ x y h; ⟨_, _, _, hs⟩) htype)⟩
  | table_init_succ z j i v_n x y h0 h1 h2 h3 h4 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨rt, lim, hlx, hly, _⟩ := pt_table_init _ _ x y hop
    have isub := ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
      (fun u1 u2 h => let ⟨_, _, _, _, hs⟩ := pt_table_init _ _ x y h; ⟨_, _, _, hs⟩) htype
    obtain ⟨hx, hgetx⟩ := getElem?_eq_some_bang hlx
    obtain ⟨hy, hgety⟩ := getElem?_eq_some_bang hly
    have hwftt : wf_tabletype (tabletype.mk_tabletype lim rt) := by rw [← hgetx]; exact wf_context_tab _ _ hx hwfC'
    have hrefs := elem_refs_ok _ _ _ _ y rt hmi him hly
    have hr := hrefs ((fun_elem (state.mk_state v_s v_f) y).REFS[proj_uN_0 (Option.get! (proj_num__0 i))]!)
      (by rw [getElem!_pos (fun_elem (state.mk_state v_s v_f) y).REFS _ h0]; exact List.getElem_mem h0)
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype_reftype rt] [] (ais_ref1 _ _ _ rt hr hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype_reftype rt] [] [] (ais_plain1 _ _ (instr.TABLE_SET x) _ _ hwfS (Instr_ok.table_set _ x rt lim hx hgetx hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_SET x) (by simp))) hwftt))
      (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32, valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.TABLE_INIT x y) _ _ hwfS (Instr_ok.table_init _ x y lim rt hx hgetx hy hgety hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_INIT x y) (by simp))) hwftt))
      (ais_nil_refl _ _ [] hwfC' hwfS))))))))
```

**Explanation.** The `_trap` and `_zero` cases follow the categories table in §8.3. Each `succ` case is the worked example of §8.3 with different rows:
- `table_fill_succ`: `ais_seq4_last` isolates the `TABLE_FILL` to get the table's type `(lim, rt)` (`pt_table_fill`); `ais_fill_inv` gives both `Val_ok s v rt` — the fill value has the table's element type, needed because the reduct pushes `v` twice — and the overall `[] → []` subtyping. (`ais_args3_typing` would not do here: it forgets the argument types.) The primitive instructions are typed by the static rules `Instr_ok.table_set`/`Instr_ok.table_fill`, which need the table's type to be well-formed (`hwftt`, via `wf_context_tab`).
- `table_copy_le`/`_gt`: all three operands are `i32` constants, so `ais_args3_typing` suffices for the subtyping, and the re-pushed constants are typed afresh by `ais_const1` (with well-formedness from `hwf'`). `pt_table_copy` provides *both* tables' types, which share the element type `rt` — that shared `rt` is what lets the intermediate `TABLE_GET y` (`[I32] → [rt]`) feed `TABLE_SET x` (`[I32, rt] → []`). Note the third row of the chain: `ais_cons_pre … [valtype.I32] [valtype.I32] [valtype_reftype rt]` — `TABLE_GET y` consumes the source index on top while the destination index stays underneath as `pre`.
- `table_init_succ`: like copy, but the element pushed comes from the element segment, so `elem_refs_ok` (from `Moduleinst_ok` and `inst_match`) shows every reference in segment `y` has the table's element type, and the fetched one is typed by `ais_ref1`.

## 8.9 Family F — loads

**WASM.** `t.load memarg` pops an `i32` address `i` and reads bytes from memory 0 starting at `i + memarg.offset`, decoding a value of type `t`. "Packed" loads such as `i32.load8_s` read fewer bytes and sign- or zero-extend them. The `v128.load` family reads a whole 128-bit vector, or 8×8/16×4/32×2 values each extended to a wider lane (`vload_shape`), or one value copied into every lane (`vload_splat`), or one value into lane 0 with the rest zero (`vload_zero`), or one value replacing a single lane of a vector already on the stack (`vload_lane`). Every form traps if any accessed byte is out of bounds.

**Rules** — [wasm2.0.lean:14537-14631](../../../../../src/test-lean-claude/wasm2.0.lean#L14537-L14631):
```lean
  | load_num_trap (z : state) (i : num_) (nt : numtype) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.LOAD nt none ao]) [admininstr.TRAP]
  | load_num_val (z : state) (i : num_) (nt : numtype) (ao : memarg) (c : num_) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    (nbytes_ nt c) = (List.take (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_num_ nt c →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.LOAD nt none ao]) [admininstr.CONST nt c]
  | load_pack_trap (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_n : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.LOAD (numtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao]) [admininstr.TRAP]
  | load_pack_val (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) (c : iN) :
    (size (valtype_Inn v_Inn)) ≠ none →
    (proj_num__0 i) ≠ none →
    (ibytes_ v_n c) = (List.take (rat_to_nat ((v_n : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN v_n c →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.LOAD (numtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao]) [admininstr.CONST (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (extend__ v_n (Option.get! (size (valtype_Inn v_Inn))) v_sx c))]
  | vload_oob (z : state) (i : num_) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 none ao]) [admininstr.TRAP]
  | vload_val (z : state) (i : num_) (ao : memarg) (c : vec_) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    (vbytes_ vectype.V128 c) = (List.take (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 128 c →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 none ao]) [admininstr.VCONST vectype.V128 c]
  | vload_shape_oob (z : state) (i : num_) (v_M : M) (v_N : N) (v_sx : sx) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((v_M * v_N) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx)) ao]) [admininstr.TRAP]
  | vload_shape_val (z : state) (i : num_) (v_M : M) (v_N : N) (v_sx : sx) (ao : memarg) (c : vec_) (j_lst : List iN) (v_Jnn : Jnn) :
    Forall (fun (k : Nat) => (proj_num__0 i) ≠ none) (List.range v_N) →
    Forall₂ (fun (k : Nat) (j_elem : iN) => (ibytes_ v_M j_elem) = (List.take (rat_to_nat ((v_M : Rat) / (8 : Rat))) (List.drop (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((k * v_M) : Rat) / (8 : Rat)))) ((fun_mem z (uN.mk_uN 0)).BYTES)))) (List.range v_N) j_lst →
    (jsize v_Jnn) = (v_M * 2) →
    c = (inv_lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) (Map (fun (j_elem : iN) => lane_.mk_lane__0 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j_elem)) j_lst)) →
    wf_uN 32 (uN.mk_uN 0) →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    Forall (fun (j_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N))) (lane_.mk_lane__0 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j_elem))) j_lst →
    v_N = (List.length j_lst) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx)) ao]) [admininstr.VCONST vectype.V128 c]
  | vload_splat_oob (z : state) (i : num_) (v_N : N) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_N : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop_.SPLAT (sz.mk_sz v_N))) ao]) [admininstr.TRAP]
  | vload_splat_val (z : state) (i : num_) (v_N : N) (ao : memarg) (c : vec_) (j : iN) (v_Jnn : Jnn) (v_M : M) :
    (proj_num__0 i) ≠ none →
    (ibytes_ v_N j) = (List.take (rat_to_nat ((v_N : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    v_N = (jsize v_Jnn) →
    (v_M : Rat) = ((128 : Rat) / (v_N : Rat)) →
    c = (inv_lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) (List.replicate v_M (lane_.mk_lane__0 v_Jnn (uN.mk_uN (proj_uN_0 j))))) →
    wf_uN 32 (uN.mk_uN 0) →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (lane_.mk_lane__0 v_Jnn (uN.mk_uN (proj_uN_0 j))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop_.SPLAT (sz.mk_sz v_N))) ao]) [admininstr.VCONST vectype.V128 c]
  | vload_zero_oob (z : state) (i : num_) (v_N : N) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_N : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop_.ZERO (sz.mk_sz v_N))) ao]) [admininstr.TRAP]
  | vload_zero_val (z : state) (i : num_) (v_N : N) (ao : memarg) (c : vec_) (j : iN) :
    (proj_num__0 i) ≠ none →
    (ibytes_ v_N j) = (List.take (rat_to_nat ((v_N : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    c = (extend__ v_N 128 sx.U j) →
    wf_uN v_N j →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop_.ZERO (sz.mk_sz v_N))) ao]) [admininstr.VCONST vectype.V128 c]
  | vload_lane_oob (z : state) (i : num_) (c_1 : vec_) (v_N : N) (ao : memarg) (j : laneidx) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_N : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c_1, admininstr.VLOAD_LANE vectype.V128 (sz.mk_sz v_N) ao j]) [admininstr.TRAP]
  | vload_lane_val (z : state) (i : num_) (c_1 : vec_) (v_N : N) (ao : memarg) (j : laneidx) (c : vec_) (k : iN) (v_Jnn : Jnn) (v_M : M) :
    (proj_num__0 i) ≠ none →
    (ibytes_ v_N k) = (List.take (rat_to_nat ((v_N : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    v_N = (jsize v_Jnn) →
    (v_M : Rat) = ((128 : Rat) / (v_N : Rat)) →
    c = (inv_lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) (List.modify (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c_1) (proj_uN_0 j) (fun elem_1 => lane_.mk_lane__0 v_Jnn (uN.mk_uN (proj_uN_0 k))))) →
    wf_uN 32 (uN.mk_uN 0) →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (lane_.mk_lane__0 v_Jnn (uN.mk_uN (proj_uN_0 k))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c_1, admininstr.VLOAD_LANE vectype.V128 (sz.mk_sz v_N) ao j]) [admininstr.VCONST vectype.V128 c]
```

**Reading the rules.** Each operation has an out-of-bounds rule (`_trap`/`_oob`) → `[TRAP]`, and a value rule. The value rules are **declarative**: they do not compute the result from the bytes; they say the result is *any* constant `c` whose byte encoding equals the bytes in memory (`nbytes_ nt c = take … (drop … bytes)`), together with a well-formedness premise such as `wf_num_ nt c`. That is convenient for the proof — it never needs to know how decoding works, only that `c` is a well-formed constant of the right type.

**Proof cases** — [TypePreservation.lean:2299-2331](../../../../../src/test-lean-claude/TypePreservation.lean#L2299-L2331):
```lean
  | load_num_trap z i nt ao h0 h1 h2 h3 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | load_num_val z i nt ao c h0 h1 h2 h3 h4 =>
    have isub := ais_args1_typing _ _ _ _ [valtype_numtype nt] t1s t2s (inv_const_arg _ _ _ i)
      (fun u1 u2 h => ⟨_, pt_load_none _ _ nt ao h⟩) htype
    exact construct_ais_subtyping _ _ _ [] _ t1s t2s (ais_const1 _ _ nt c h3 hwfC' hwfS) isub
  | load_pack_trap z i v_Inn v_n v_sx ao h0 h1 h2 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | load_pack_val z i v_Inn v_n v_sx ao c h0 h1 h2 h3 h4 =>
    have isub := ais_args1_typing _ _ _ _ [valtype_Inn v_Inn] t1s t2s (inv_const_arg _ _ _ i)
      (fun u1 u2 h => ⟨_, pt_load_pack _ _ v_Inn v_n v_sx ao h⟩) htype
    have hc := wf_const_num (hwf' _ (List.mem_singleton_self _))
    cases v_Inn <;> exact construct_ais_subtyping _ _ _ [] _ t1s t2s (ais_const1 _ _ _ _ hc hwfC' hwfS) isub
  | vload_oob z i ao h0 h1 h2 h3 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | vload_val z i ao c h0 h1 h2 h3 h4 =>
    exact Step_read__vload_preserves _ _ i _ ao c _ htype (hwf' _ (by simp))
  | vload_shape_oob z i v_M v_N v_sx ao h0 h1 h2 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | vload_shape_val z i v_M v_N v_sx ao c j_lst v_Jnn h0 h1 h2 h3 h4 h5 h6 h7 =>
    exact Step_read__vload_preserves _ _ i _ ao c _ htype (hwf' _ (by simp))
  | vload_splat_oob z i v_N ao h0 h1 h2 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | vload_splat_val z i v_N ao c j v_Jnn v_M h0 h1 h2 h3 h4 h5 h6 h7 =>
    exact Step_read__vload_preserves _ _ i _ ao c _ htype (hwf' _ (by simp))
  | vload_zero_oob z i v_N ao h0 h1 h2 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | vload_zero_val z i v_N ao c j h0 h1 h2 h3 h4 =>
    exact Step_read__vload_preserves _ _ i _ ao c _ htype (hwf' _ (by simp))
  | vload_lane_oob z i c_1 v_N ao j h0 h1 h2 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | vload_lane_val z i c_1 v_N ao j c k v_Jnn v_M h0 h1 h2 h3 h4 h5 h6 h7 =>
    exact Step_read__vload_lane_preserves _ _ i c_1 _ ao j c _ htype (hwf' _ (by simp))
```

**Explanation.** The seven `_trap`/`_oob` cases are `construct_ais_trap`. `load_num_val`: `ais_args1_typing` with `pt_load_none` gives `instrtype_sub ([] → [nt]) (t1s → t2s)`, and `ais_const1` types `CONST nt c` using the rule's own premise `h3 : wf_num_ nt c`. `load_pack_val` is the same with result type `valtype_Inn v_Inn` (`i32` or `i64`), and the result constant's well-formedness taken from `hwf'`; the `cases v_Inn <;>` is needed because `valtype_numtype (numtype_Inn v_Inn)` and `valtype_Inn v_Inn` only become syntactically equal once Lean knows whether `v_Inn` is `I32` or `I64`. The five SIMD value cases delegate to two helpers from earlier in the file, which reduce to the generic "operands in, one vector out" lemmas `vec_preserves_1`/`vec_preserves_2` from the pure-preservation file — [TypePreservation.lean:583-609](../../../../../src/test-lean-claude/TypePreservation.lean#L583-L609):
```lean
/-- Rocq `type_preservation.v:1569` `Step_read__vload_preserves`. -/
theorem Step_read__vload_preserves (v_S : store) (v_C : context) (i : num_) (vlo : Option vloadop_)
    (ao : memarg) (c : vec_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 vlo ao] v_ft →
    wf_admininstr (admininstr.VCONST vectype.V128 c) →
    Instrs_ok2 v_S v_C [admininstr.VCONST vectype.V128 c] v_ft := by
  intro h hwfc
  obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C _ v_ft h
  exact vec_preserves_1 v_S v_C _ _ _ (valtype_numtype numtype.I32) valtype.V128 v_ft h
    (ais_const_typing_inversion v_S v_C numtype.I32 i)
    (ais_vload_typing_inversion v_S v_C vlo ao)
    (vconst_result_typing v_S v_C c hwfS hwfC hwfc)

/-- Rocq `type_preservation.v:1583` `Step_read__vload_lane_preserves`. -/
theorem Step_read__vload_lane_preserves (v_S : store) (v_C : context) (i : num_) (c_1 : vec_)
    (v_sz : sz) (ao : memarg) (l : laneidx) (c : vec_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c_1,
      admininstr.VLOAD_LANE vectype.V128 v_sz ao l] v_ft →
    wf_admininstr (admininstr.VCONST vectype.V128 c) →
    Instrs_ok2 v_S v_C [admininstr.VCONST vectype.V128 c] v_ft := by
  intro h hwfc
  obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C _ v_ft h
  exact vec_preserves_2 v_S v_C _ _ _ _ (valtype_numtype numtype.I32) valtype.V128 valtype.V128 v_ft h
    (ais_const_typing_inversion v_S v_C numtype.I32 i)
    (ais_vconst_typing_inversion v_S v_C c_1)
    (ais_vload_lane_typing_inversion v_S v_C v_sz ao l)
    (vconst_result_typing v_S v_C c hwfS hwfC hwfc)
```

## 8.10 Family G — memory size and bulk memory

**WASM.** `memory.size` pushes the size of memory 0 in pages (64 KiB each). `memory.fill` (address `i`, value `v`, count `n`) sets `n` bytes from `i` onward to the low byte of `v`. `memory.copy` (destination `j`, source `i`, count `n`) copies `n` bytes within memory 0, `memmove`-style. `memory.init x` (destination `j`, source offset `i`, count `n`) copies `n` bytes from data segment `x` into memory. The bulk operations follow pattern 1 of §8.2, one byte at a time, using `i32.store8` (`STORE I32 (some 8) memarg0`) and `i32.load8_u` (`LOAD I32 (some (8, U)) memarg0`), where `memarg0` is offset 0, alignment 0 ([wasm2.0.lean:2617-2622](../../../../../src/test-lean-claude/wasm2.0.lean#L2617-L2622)).

**Rules** — [wasm2.0.lean:14632-14695](../../../../../src/test-lean-claude/wasm2.0.lean#L14632-L14695):
```lean
  | memory_size (z : state) (v_n : n) :
    ((v_n * 64) * Ki) = (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.MEMORY_SIZE]) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))]
  | memory_fill_trap (z : state) (i : num_) (v_val : val) (v_n : n) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_FILL]) [admininstr.TRAP]
  | memory_fill_zero (z : state) (i : num_) (v_val : val) (v_n : n) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_FILL]) []
  | memory_fill_succ (z : state) (i : num_) (v_val : val) (v_n : n) :
    (proj_num__0 i) ≠ none →
    v_n ≠ 0 →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_FILL]) [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.MEMORY_FILL]
  | memory_copy_trap (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) [admininstr.TRAP]
  | memory_copy_zero (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) []
  | memory_copy_le (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 j) ≠ none →
    (proj_num__0 i) ≠ none →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    (proj_uN_0 (Option.get! (proj_num__0 j))) ≤ (proj_uN_0 (Option.get! (proj_num__0 i))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.LOAD numtype.I32 (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0, admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.MEMORY_COPY]
  | memory_copy_gt (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 j) ≠ none →
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 j))) > (proj_uN_0 (Option.get! (proj_num__0 i))) →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) : Int) - (1 : Int))))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) : Int) - (1 : Int))))), admininstr.LOAD numtype.I32 (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0, admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0, admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.MEMORY_COPY]
  | memory_init_trap (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_data z x).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_INIT x]) [admininstr.TRAP]
  | memory_init_zero (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_data z x).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_INIT x]) []
  | memory_init_succ (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_data z x).BYTES)) →
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_data z x).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_INIT x]) [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (proj_byte_0 (((fun_data z x).BYTES)[proj_uN_0 (Option.get! (proj_num__0 i))]!)))), admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.MEMORY_INIT x]
```

**Reading the rules.** `memory_size`: `[MEMORY_SIZE]` → `[CONST I32 n]` where `n` pages × 64 KiB equals the memory's byte length. The bulk rules mirror family E: `memory_fill_succ` → `[CONST I32 i, v, i32.store8, CONST I32 (i+1), v, CONST I32 (n-1), MEMORY_FILL]`; `memory_copy_le`/`_gt` load one byte with `i32.load8_u` and store it with `i32.store8`, forward or backward; `memory_init_succ` pushes the data segment's byte `i` as an `i32` constant and stores it.

**Proof cases** — [TypePreservation.lean:2332-2418](../../../../../src/test-lean-claude/TypePreservation.lean#L2332-L2418):
```lean
  | memory_size z v_n h0 h1 =>
    exact const_I32_result _ _ _ t1s t2s (wf_const_num (hwf' _ (by simp))) hwfC' hwfS (pt_memory_size _ _ htype)
  | memory_fill_trap z i v_val v_n h0 h1 h2 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | memory_fill_zero z i v_val v_n h0 h1 h2 =>
    exact (ais_empty_typing _ _ t1s t2s).mpr ⟨hwfC', hwfS, instrtype_sub_empty _ _
      (ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_val_arg _ _ _) (inv_const_arg _ _ _ _)
        (fun u1 u2 h => let ⟨_, _, hs⟩ := pt_memory_fill _ _ h; ⟨_, _, _, hs⟩) htype)⟩
  | memory_fill_succ z i v_val v_n h0 h1 h2 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨mt, hm, _⟩ := pt_memory_fill _ _ hop
    obtain ⟨hm0, hget0⟩ := getElem?_eq_some_bang hm
    have hwfmt : wf_memtype mt := by rw [← hget0]; exact wf_context_mem _ _ hm0 hwfC'
    obtain ⟨hvok, isub⟩ := ais_fill_inv _ _ i _ v_val _ valtype.I32 t1s t2s
      (fun u1 u2 h => let ⟨_, _, hs⟩ := pt_memory_fill _ _ h; hs) htype
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_val1 _ _ _ _ hvok hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) [valtype.I32, valtype.I32] [] hwfS (Instr_ok.store_pack _ Inn.I32 8 memarg0 mt hm0 hget0 memarg0_align8 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) (by simp)))))
      (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_val1 _ _ _ _ hvok hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32, valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ instr.MEMORY_FILL _ _ hwfS (Instr_ok.memory_fill _ mt hm0 hget0 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.MEMORY_FILL) (by simp)))))
      (ais_nil_refl _ _ [] hwfC' hwfS))))))))
  | memory_copy_trap z j i v_n h0 h1 h2 h3 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | memory_copy_zero z j i v_n h0 h1 h2 h3 =>
    exact (ais_empty_typing _ _ t1s t2s).mpr ⟨hwfC', hwfS, instrtype_sub_empty _ _
      (ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
        (fun u1 u2 h => let ⟨_, _, hs⟩ := pt_memory_copy _ _ h; ⟨_, _, _, hs⟩) htype)⟩
  | memory_copy_le z j i v_n h0 h1 h2 h3 h4 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨mt, hm, _⟩ := pt_memory_copy _ _ hop
    obtain ⟨hm0, hget0⟩ := getElem?_eq_some_bang hm
    have hwfmt : wf_memtype mt := by rw [← hget0]; exact wf_context_mem _ _ hm0 hwfC'
    have isub := ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
      (fun u1 u2 h => let ⟨_, _, hs⟩ := pt_memory_copy _ _ h; ⟨_, _, _, hs⟩) htype
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [valtype.I32] [valtype.I32] [] (ais_plain1 _ _ (instr.LOAD numtype.I32 (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0) [valtype.I32] [valtype.I32] hwfS (Instr_ok.load_pack _ Inn.I32 8 sx.U memarg0 mt hm0 hget0 memarg0_align8 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.LOAD numtype.I32 (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0) (by simp)))))
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) [valtype.I32, valtype.I32] [] hwfS (Instr_ok.store_pack _ Inn.I32 8 memarg0 mt hm0 hget0 memarg0_align8 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) (by simp)))))
      (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32, valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ instr.MEMORY_COPY _ _ hwfS (Instr_ok.memory_copy _ mt hm0 hget0 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.MEMORY_COPY) (by simp)))))
      (ais_nil_refl _ _ [] hwfC' hwfS)))))))))
  | memory_copy_gt z j i v_n h0 h1 h2 h3 h4 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨mt, hm, _⟩ := pt_memory_copy _ _ hop
    obtain ⟨hm0, hget0⟩ := getElem?_eq_some_bang hm
    have hwfmt : wf_memtype mt := by rw [← hget0]; exact wf_context_mem _ _ hm0 hwfC'
    have isub := ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
      (fun u1 u2 h => let ⟨_, _, hs⟩ := pt_memory_copy _ _ h; ⟨_, _, _, hs⟩) htype
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [valtype.I32] [valtype.I32] [] (ais_plain1 _ _ (instr.LOAD numtype.I32 (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0) [valtype.I32] [valtype.I32] hwfS (Instr_ok.load_pack _ Inn.I32 8 sx.U memarg0 mt hm0 hget0 memarg0_align8 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.LOAD numtype.I32 (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0) (by simp)))))
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) [valtype.I32, valtype.I32] [] hwfS (Instr_ok.store_pack _ Inn.I32 8 memarg0 mt hm0 hget0 memarg0_align8 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) (by simp)))))
      (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32, valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ instr.MEMORY_COPY _ _ hwfS (Instr_ok.memory_copy _ mt hm0 hget0 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.MEMORY_COPY) (by simp)))))
      (ais_nil_refl _ _ [] hwfC' hwfS)))))))))
  | memory_init_trap z j i v_n x h0 h1 h2 h3 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | memory_init_zero z j i v_n x h0 h1 h2 h3 =>
    exact (ais_empty_typing _ _ t1s t2s).mpr ⟨hwfC', hwfS, instrtype_sub_empty _ _
      (ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
        (fun u1 u2 h => let ⟨_, _, _, hs⟩ := pt_memory_init _ _ x h; ⟨_, _, _, hs⟩) htype)⟩
  | memory_init_succ z j i v_n x h0 h1 h2 h3 h4 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨mt, hm, hd, _⟩ := pt_memory_init _ _ x hop
    obtain ⟨hm0, hget0⟩ := getElem?_eq_some_bang hm
    have hwfmt : wf_memtype mt := by rw [← hget0]; exact wf_context_mem _ _ hm0 hwfC'
    have isub := ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
      (fun u1 u2 h => let ⟨_, _, _, hs⟩ := pt_memory_init _ _ x h; ⟨_, _, _, hs⟩) htype
    obtain ⟨hdx, hgetd⟩ := getElem?_eq_some_bang hd
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) [valtype.I32, valtype.I32] [] hwfS (Instr_ok.store_pack _ Inn.I32 8 memarg0 mt hm0 hget0 memarg0_align8 hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0) (by simp)))))
      (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32, valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.MEMORY_INIT x) _ _ hwfS (Instr_ok.memory_init _ x mt hm0 hget0 hdx hgetd hwfC' hwfmt ((wf_admininstr_instr _).mpr (hwf' (admininstr.MEMORY_INIT x) (by simp)))))
      (ais_nil_refl _ _ [] hwfC' hwfS))))))))
```

**Explanation.** `memory_size` is `const_I32_result` with `pt_memory_size`. The `_trap` and `_zero` cases are as before. The `succ` cases are `ais_cons_pre` chains exactly like family E, with three differences: the operator's principal type yields memory 0's type `mt` (`pt_memory_fill`/`_copy`/`_init`) instead of a table type; the byte-level primitives are typed by the static rules `Instr_ok.store_pack` and `Instr_ok.load_pack` for 8-bit access, whose alignment side condition `2^align ≤ 8/8` is discharged by `memarg0_align8`; and `memory_fill_succ` uses `ais_fill_inv` with value type `I32` (the fill value is an `i32`). `memory_init_succ` additionally gets the data segment's existence from `pt_memory_init` (`C'.DATAS[x] = OK`).

## 8.11 The one `sorry` dependency, and the corner case where the theorem is false

`t_read_preservation` depends on exactly one unproved declaration: `Step_read_is_wf` (primer §0.4), stated at [wasm2.0.lean:16028-16039](../../../../../src/test-lean-claude/wasm2.0.lean#L16028-L16039), which supplies `hwf'`. (This was checked mechanically: walking the theorem's transitive dependencies in the compiled environment finds `sorryAx` only inside `Step_read_is_wf`.)

`Step_read_is_wf` is `sorry` in Lean and `Admitted` in Rocq, and — per the doc comment above it, the doc comment of `t_read_preservation`, and the repo's `claude-logging/for-claude/is_wf_theorems.md` — it is **false** in a corner case of three rules: `memory_fill_succ`, `memory_copy_le`, and `memory_init_succ`. Each pushes a constant `CONST I32 (i + 1)` (or `j + 1`) for the next iteration. A memory may have the maximal 2^16 pages, i.e. 2^32 bytes, so with `n = 1` the bounds check `i + n ≤ 2^32` admits `i = 2^32 - 1`, and then `i + 1 = 2^32`, which does not fit in 32 bits: the reduct contains an ill-formed constant. In the proof, those constants are typed by `ais_const1 … (wf_const_num (hwf' _ (by simp))) …`, so in that corner case `hwf'` is asserting something false. Because `Config_ok` includes `wf_config`, the top-level `t_preservation` inherits the same corner case — in Rocq as well as in Lean. The notes record the fix as pending on the specification side. Everything else in `t_read_preservation` is a complete, checked proof.

---
*Next: [09-helper-glossary.md](09-helper-glossary.md) — the recurring helper lemmas used throughout files 01–08.*

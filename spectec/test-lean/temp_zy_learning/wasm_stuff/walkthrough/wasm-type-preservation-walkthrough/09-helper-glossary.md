# 9. Helper glossary

*(Previous: [08-t-read-preservation.md](08-t-read-preservation.md). Back to the [README](README.md).)*

The proofs in files `01`–`08` lean on roughly two hundred helper lemmas. This file collects the ones that recur, grouped by what they are *for*, with a one-line meaning each. Every name links to its definition, and each family ends with a collapsible block giving every lemma's exact statement, quoted from the source (from the declaration line to the start of its proof).

**Reading the names.** The source follows loose conventions that make most helpers guessable once you know them:

| Fragment | Meaning | Example |
|---|---|---|
| `ai_` / `ais_` | about one administrative instruction / a list of them (`List admininstr`) | `ais_composition_typing` |
| `construct_` | *builds* a typing derivation | `construct_ais_compose` |
| `_inv`, `inversion`, `invert` | *reads facts off* a typing or other judgment | `ais_global_set_inv` |
| `pt_` | the **p**rincipal **t**ype of one operator (file `08` §8.3) | `pt_call` |
| `minst_` | about a module instance | `minst_invert_tables` |
| `Extend_store_` | carries a fact across store extension (primer §0.6) | `Extend_store_vals` |
| `wf_` | syntactic well-formedness (primer §0.4) | `wf_config_ais` |
| `_is_wf` | a generated well-formedness lemma | `Step_read_is_wf` |
| `_parts` / `_of_parts` | split a judgment into components / rebuild it | `Store_ok_parts` |
| `_refl` | the reflexive (unchanged) case | `extend_mem_refl` |

## 9.1 Reading a typing derivation (inversion)

A typing derivation `Instrs_ok2 s C ais (t1s → t2s)` can be built in many ways — by sequencing, by subtyping, by adding untouched stack slots underneath — so a proof cannot simply pattern-match on it. These lemmas normalize it: they extract each instruction's *principal* type (the tightest one) plus an `instrtype_sub` fact recording how `t1s → t2s` weakens it (file `08` §8.3 explains both).

| Lemma | Meaning |
|---|---|
| [`ai_principal_typing`](../../../../../src/test-lean-claude/TypingLemmas.lean#L311) | For each administrative instruction, its principal type and side conditions, as one big `match` — e.g. `LOCAL_GET x : [] → [t]` where `C.LOCALS[x] = t`. |
| [`ais_single_typing_inversion`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1344) | A typing of `[ai]` is a weakening of `ai`'s principal type. |
| [`ais_composition_typing`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1254) | A typing of `l1 ++ l2` splits into a typing of `l1` to some middle stack type and of `l2` from it. |
| [`ais_seq_typing_inversion`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1244) | The same split, for `[a] ++ rest`. |
| [`ais_vals_typing_inversion`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1788) | Pushed values typed at `t1s → t2s` have types `vts` (with `Vals_ok`), and `[] → vts` weakens to `t1s → t2s`. |
| [`ais_single_val_typing_inversion`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1386) | The same, for a single pushed value. |
| [`ais_const_typing_inversion`](../../../../../src/test-lean-claude/TypePreservationPure.lean#L1309) | A pushed `CONST nt c` is a weakening of `[] → [nt]`. |
| [`ainstrs_ok_context_store_wf`](../../../../../src/test-lean-claude/TypingLemmas.lean#L261) | Any typing derivation implies its context, store, and instructions are well-formed. |
| [`ais_args1_typing`](../../../../../src/test-lean-claude/TypePreservation.lean#L696), [`ais_args2_typing`](../../../../../src/test-lean-claude/TypePreservation.lean#L709), [`ais_args3_typing`](../../../../../src/test-lean-claude/TypePreservation.lean#L728) | For a redex of one/two/three argument pushes followed by an operator with output `out`, the redex as a whole is a weakening of `[] → out`. They take one fact per piece, supplied by the `inv_*` lemmas below. |
| [`inv_val_arg`](../../../../../src/test-lean-claude/TypePreservation.lean#L753), [`inv_ref_arg`](../../../../../src/test-lean-claude/TypePreservation.lean#L758), [`inv_const_arg`](../../../../../src/test-lean-claude/TypePreservation.lean#L763) | A pushed value / reference / constant is a weakening of `[] → [t]` for some `t`. |
| [`inv_local_set`](../../../../../src/test-lean-claude/TypePreservation.lean#L773), [`inv_global_set`](../../../../../src/test-lean-claude/TypePreservation.lean#L783), [`inv_table_set`](../../../../../src/test-lean-claude/TypePreservation.lean#L793), [`inv_table_grow`](../../../../../src/test-lean-claude/TypePreservation.lean#L803), [`inv_elem_drop`](../../../../../src/test-lean-claude/TypePreservation.lean#L813), [`inv_data_drop`](../../../../../src/test-lean-claude/TypePreservation.lean#L823), [`inv_store_none`](../../../../../src/test-lean-claude/TypePreservation.lean#L833), [`inv_store_pack`](../../../../../src/test-lean-claude/TypePreservation.lean#L843), [`inv_memory_grow`](../../../../../src/test-lean-claude/TypePreservation.lean#L853) | An operator's typing is a weakening of its principal *shape*, e.g. `LOCAL_SET x : [t] → []`, `TABLE_GROW x : [t, t'] → [I32]`, `ELEM_DROP x : [] → []`. |
| [`ais_global_set_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L965), [`ais_table_set_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L981), [`ais_table_grow_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L999) | For the `global.set`/`table.set`/`table.grow` redexes: the global is mutable and the value has its type; the reference has the table's element type. |
| [`ais_elem_drop_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1021), [`ais_data_drop_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1029), [`ais_store_mems_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1037), [`ais_memory_grow_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1052) | For `elem.drop`/`data.drop`/store/`memory.grow` redexes: the segment, or memory 0, exists in the context. |
| [`ais_seq3_last_typing`](../../../../../src/test-lean-claude/TypePreservation.lean#L462), [`ais_seq4_last`](../../../../../src/test-lean-claude/TypePreservation.lean#L1847) | The last operator of a three-/four-instruction sequence has *some* typing (so a `pt_*` lemma can be applied to it). |
| [`ais_fill_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1857) | For `[CONST I32 i, v, CONST I32 n, op]` with `op : [I32, t, I32] → []`: `v` has type `t`, and the redex is a weakening of `[] → []`. |
| `pt_*` (17 lemmas) | One operator's principal-type facts plus its weakening — listed and explained in file `08` §8.3. |
| [`bt_inversion`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L872) | A blocktype's static type (`Blocktype_ok` in the typing context) equals its runtime resolution (`fun_blocktype`). |
| [`funcinst_ok_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L1953) | A well-typed function instance's module instance is `Moduleinst_ok` at some context `C0`, and its code is `Func_ok` there. |
| [`func_ok_body`](../../../../../src/test-lean-claude/TypePreservation.lean#L1961) | A well-typed function's body is typed `[] → t2` in the context whose locals are the parameters plus declared locals and whose label and return type are the results. |
| [`tableinst_ok_invert`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L202) | A well-typed table instance: its type's minimum equals its length, and every reference has the element type. |
| [`meminst_ok_raw`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2159) | A well-typed memory instance: its byte length is its page count × 64 KiB, and its memory type is valid. |
| [`Externaddr_invert_funcs`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L551) | A well-typed function address is in range, and the instance there has a type that is an extern-subtype of the claimed one. |

<details>
<summary>Exact statements (9.1)</summary>

[`ais_single_typing_inversion`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1344)
```lean
theorem ais_single_typing_inversion (v_S : store) (v_C : context) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [v_ai] (mkFunctype t1s t2s) →
    ∃ t1s_sup t2s_sub, ai_principal_typing v_S v_C v_ai (mkFunctype t1s_sup t2s_sub) ∧
      instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) := by
```
[`ais_composition_typing`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1254)
```lean
theorem ais_composition_typing (v_S : store) (v_C : context) (v_ais1 v_ais2 : List admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C (v_ais1 ++ v_ais2) (mkFunctype t1s t2s) →
    ∃ t3s, Instrs_ok2 v_S v_C v_ais1 (mkFunctype t1s t3s) ∧ Instrs_ok2 v_S v_C v_ais2 (mkFunctype t3s t2s) := by
```
[`ais_seq_typing_inversion`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1244)
```lean
theorem ais_seq_typing_inversion (v_S : store) (v_C : context) (v_ais : List admininstr) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C ([v_ai] ++ v_ais) (mkFunctype t1s t2s) →
    ∃ t3s, Instrs_ok2 v_S v_C v_ais (mkFunctype t3s t2s) ∧ Instrs_ok2 v_S v_C [v_ai] (mkFunctype t1s t3s) := by
```
[`ais_vals_typing_inversion`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1788)
```lean
theorem ais_vals_typing_inversion (v_S : store) (v_C : context) (v_vals : List val) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C (v_vals.map admininstr_val) (mkFunctype t1s t2s) →
    ∃ v_ts : List valtype, instrtype_sub (mkFunctype [] v_ts) (mkFunctype t1s t2s) ∧ Vals_ok v_S v_vals v_ts := by
```
[`ais_single_val_typing_inversion`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1386)
```lean
theorem ais_single_val_typing_inversion (v_S : store) (v_C : context) (v_val : val) (ts1 ts2 : List valtype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val] (mkFunctype ts1 ts2) →
    ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype ts1 ts2) ∧ Val_ok v_S v_val t := by
```
[`ais_const_typing_inversion`](../../../../../src/test-lean-claude/TypePreservationPure.lean#L1309)
```lean
theorem ais_const_typing_inversion (v_S : store) (v_C : context) (nt : numtype) (c : num_) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [admininstr.CONST nt c] (mkFunctype t1s t2s) →
    instrtype_sub (mkFunctype [] [valtype_numtype nt]) (mkFunctype t1s t2s) := by
```
[`ainstrs_ok_context_store_wf`](../../../../../src/test-lean-claude/TypingLemmas.lean#L261)
```lean
theorem ainstrs_ok_context_store_wf (v_S : store) (v_C : context) (v_ainstrs : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C v_ainstrs v_ft → wf_context v_C ∧ wf_store v_S ∧ Forall wf_admininstr v_ainstrs := by
```
[`ais_args1_typing`](../../../../../src/test-lean-claude/TypePreservation.lean#L696)
```lean
theorem ais_args1_typing (s : store) (C : context) (a op : admininstr) (out t1s t2s : List valtype)
    (ha : ∀ u1 u2, Instrs_ok2 s C [a] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hop : ∀ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [t] out) (mkFunctype u1 u2)) :
    Instrs_ok2 s C [a, op] (mkFunctype t1s t2s) → instrtype_sub (mkFunctype [] out) (mkFunctype t1s t2s) := by
```
[`ais_args2_typing`](../../../../../src/test-lean-claude/TypePreservation.lean#L709)
```lean
theorem ais_args2_typing (s : store) (C : context) (a b op : admininstr) (out t1s t2s : List valtype)
    (ha : ∀ u1 u2, Instrs_ok2 s C [a] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hb : ∀ u1 u2, Instrs_ok2 s C [b] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hop : ∀ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] out) (mkFunctype u1 u2)) :
    Instrs_ok2 s C [a, b, op] (mkFunctype t1s t2s) → instrtype_sub (mkFunctype [] out) (mkFunctype t1s t2s) := by
```
[`ais_args3_typing`](../../../../../src/test-lean-claude/TypePreservation.lean#L728)
```lean
theorem ais_args3_typing (s : store) (C : context) (a b c op : admininstr) (out t1s t2s : List valtype)
    (ha : ∀ u1 u2, Instrs_ok2 s C [a] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hb : ∀ u1 u2, Instrs_ok2 s C [b] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hc : ∀ u1 u2, Instrs_ok2 s C [c] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hop : ∀ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) →
      ∃ t t' t'', instrtype_sub (mkFunctype [t, t', t''] out) (mkFunctype u1 u2)) :
    Instrs_ok2 s C [a, b, c, op] (mkFunctype t1s t2s) →
      instrtype_sub (mkFunctype [] out) (mkFunctype t1s t2s) := by
```
[`inv_val_arg`](../../../../../src/test-lean-claude/TypePreservation.lean#L753)
```lean
theorem inv_val_arg (s : store) (C : context) (v : val) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr_val v] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) :=
```
[`inv_ref_arg`](../../../../../src/test-lean-claude/TypePreservation.lean#L758)
```lean
theorem inv_ref_arg (s : store) (C : context) (r : ref) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr_ref r] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) :=
```
[`inv_const_arg`](../../../../../src/test-lean-claude/TypePreservation.lean#L763)
```lean
theorem inv_const_arg (s : store) (C : context) (nt : numtype) (c : num_) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.CONST nt c] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) :=
```
[`inv_local_set`](../../../../../src/test-lean-claude/TypePreservation.lean#L773)
```lean
theorem inv_local_set (s : store) (C : context) (x : localidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.LOCAL_SET x] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [t] []) (mkFunctype u1 u2) := by
```
[`inv_global_set`](../../../../../src/test-lean-claude/TypePreservation.lean#L783)
```lean
theorem inv_global_set (s : store) (C : context) (x : globalidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.GLOBAL_SET x] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [t] []) (mkFunctype u1 u2) := by
```
[`inv_table_set`](../../../../../src/test-lean-claude/TypePreservation.lean#L793)
```lean
theorem inv_table_set (s : store) (C : context) (x : tableidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.TABLE_SET x] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] []) (mkFunctype u1 u2) := by
```
[`inv_table_grow`](../../../../../src/test-lean-claude/TypePreservation.lean#L803)
```lean
theorem inv_table_grow (s : store) (C : context) (x : tableidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.TABLE_GROW x] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] [valtype.I32]) (mkFunctype u1 u2) := by
```
[`inv_elem_drop`](../../../../../src/test-lean-claude/TypePreservation.lean#L813)
```lean
theorem inv_elem_drop (s : store) (C : context) (x : elemidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.ELEM_DROP x] (mkFunctype u1 u2) →
      instrtype_sub (mkFunctype [] []) (mkFunctype u1 u2) := by
```
[`inv_data_drop`](../../../../../src/test-lean-claude/TypePreservation.lean#L823)
```lean
theorem inv_data_drop (s : store) (C : context) (x : dataidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.DATA_DROP x] (mkFunctype u1 u2) →
      instrtype_sub (mkFunctype [] []) (mkFunctype u1 u2) := by
```
[`inv_store_none`](../../../../../src/test-lean-claude/TypePreservation.lean#L833)
```lean
theorem inv_store_none (s : store) (C : context) (nt : numtype) (marg : memarg) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.STORE nt none marg] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] []) (mkFunctype u1 u2) := by
```
[`inv_store_pack`](../../../../../src/test-lean-claude/TypePreservation.lean#L843)
```lean
theorem inv_store_pack (s : store) (C : context) (nt : numtype) (k : Nat) (marg : memarg) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.STORE nt (some (sz.mk_sz k)) marg] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] []) (mkFunctype u1 u2) := by
```
[`inv_memory_grow`](../../../../../src/test-lean-claude/TypePreservation.lean#L853)
```lean
theorem inv_memory_grow (s : store) (C : context) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.MEMORY_GROW] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [t] [valtype.I32]) (mkFunctype u1 u2) := by
```
[`ais_global_set_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L965)
```lean
theorem ais_global_set_inv (s : store) (C : context) (v : val) (x : globalidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr_val v, admininstr.GLOBAL_SET x] (mkFunctype t1s t2s) →
    ∃ t, C.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype (some r_MUT.MUT) t) ∧ Val_ok s v t := by
```
[`ais_table_set_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L981)
```lean
theorem ais_table_set_inv (s : store) (C : context) (i : num_) (r : ref) (x : tableidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr.CONST numtype.I32 i, admininstr_ref r, admininstr.TABLE_SET x] (mkFunctype t1s t2s) →
    ∃ rt lim, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) ∧ Ref_ok s r rt := by
```
[`ais_table_grow_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L999)
```lean
theorem ais_table_grow_inv (s : store) (C : context) (r : ref) (k : num_) (x : tableidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr_ref r, admininstr.CONST numtype.I32 k, admininstr.TABLE_GROW x] (mkFunctype t1s t2s) →
    ∃ rt lim, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) ∧ Ref_ok s r rt := by
```
[`ais_elem_drop_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1021)
```lean
theorem ais_elem_drop_inv (s : store) (C : context) (x : elemidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr.ELEM_DROP x] (mkFunctype t1s t2s) → ∃ rt, C.ELEMS[proj_uN_0 x]? = some rt := by
```
[`ais_data_drop_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1029)
```lean
theorem ais_data_drop_inv (s : store) (C : context) (x : dataidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr.DATA_DROP x] (mkFunctype t1s t2s) → C.DATAS[proj_uN_0 x]? = some datatype.OK := by
```
[`ais_store_mems_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1037)
```lean
theorem ais_store_mems_inv (s : store) (C : context) (a b : admininstr) (nt : numtype) (o : Option sz)
    (ao : memarg) (t1s t2s : List valtype) :
    Instrs_ok2 s C [a, b, admininstr.STORE nt o ao] (mkFunctype t1s t2s) → 0 < C.MEMS.length := by
```
[`ais_memory_grow_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1052)
```lean
theorem ais_memory_grow_inv (s : store) (C : context) (a : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 s C [a, admininstr.MEMORY_GROW] (mkFunctype t1s t2s) → 0 < C.MEMS.length := by
```
[`ais_seq3_last_typing`](../../../../../src/test-lean-claude/TypePreservation.lean#L462)
```lean
theorem ais_seq3_last_typing (v_S : store) (v_C : context) (a b op : admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [a, b, op] v_ft → ∃ t1s t2s, Instrs_ok2 v_S v_C [op] (mkFunctype t1s t2s) := by
```
[`ais_seq4_last`](../../../../../src/test-lean-claude/TypePreservation.lean#L1847)
```lean
theorem ais_seq4_last (s : store) (C : context) (a b c op : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 s C [a, b, c, op] (mkFunctype t1s t2s) → ∃ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) := by
```
[`ais_fill_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L1857)
```lean
theorem ais_fill_inv (s : store) (C : context) (i n : num_) (v : val) (op : admininstr) (t : valtype)
    (t1s t2s : List valtype)
    (hop : ∀ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) →
      instrtype_sub (mkFunctype [valtype.I32, t, valtype.I32] []) (mkFunctype u1 u2)) :
    Instrs_ok2 s C [admininstr.CONST numtype.I32 i, admininstr_val v, admininstr.CONST numtype.I32 n, op]
      (mkFunctype t1s t2s) →
    Val_ok s v t ∧ instrtype_sub (mkFunctype [] []) (mkFunctype t1s t2s) := by
```
[`bt_inversion`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L872)
```lean
theorem bt_inversion (v_S : store) (v_C v_C' : context) (r_v_f : frame) (b_lstt : blocktype)
    (ts1 ts2 bt1 bt2 : List valtype) :
    Moduleinst_ok v_S r_v_f.MODULE v_C → Blocktype_ok v_C' b_lstt (mkFunctype ts1 ts2) →
    fun_blocktype (state.mk_state v_S r_v_f) b_lstt = mkFunctype bt1 bt2 → inst_match v_C v_C' →
    ts1 = bt1 ∧ ts2 = bt2 := by
```
[`funcinst_ok_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L1953)
```lean
theorem funcinst_ok_parts (s : store) (ft : functype) (mm : moduleinst) (fn : func) (ft' : functype) :
    Funcinst_ok s ({ TYPE := ft, MODULE := mm, CODE := fn } : funcinst) ft' →
    ∃ C0, Moduleinst_ok s mm C0 ∧ Func_ok C0 fn ft ∧ wf_context C0 := by
```
[`func_ok_body`](../../../../../src/test-lean-claude/TypePreservation.lean#L1961)
```lean
theorem func_ok_body (C : context) (x : idx) (t_lst : List valtype) (instrs : List instr) (t1 t2 : List valtype) :
    Func_ok C (func.FUNC x (Map (fun t => local.LOCAL t) t_lst) instrs)
      (functype.mk_functype (.mk_list t1) (.mk_list t2)) →
    Instrs_ok (({
      TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
      LOCALS := t1 ++ t_lst, LABELS := [.mk_list t2], RETURN := some (.mk_list t2) } : context) ++ C)
      instrs (mkFunctype [] t2) := by
```
[`tableinst_ok_invert`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L202)
```lean
theorem tableinst_ok_invert (s : store) (tb : tableinst) (tbt : tabletype) :
    Tableinst_ok s tb tbt → ∃ (ref_lst : List ref) (v_m : Option Nat) (rt : reftype),
      tb = tableinst.MKtableinst tbt ref_lst ∧
      tbt = tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN ref_lst.length) (v_m.map uN.mk_uN)) rt ∧
      Tabletype_ok tbt ∧ Forall (fun r => Ref_ok s r rt) ref_lst := by
```
[`meminst_ok_raw`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2159)
```lean
theorem meminst_ok_raw (s : store) (mi : meminst) (ty : memtype) :
    Meminst_ok s mi ty → ∃ (v_n : Nat) (m_opt : Option Nat) (bs : List byte),
      mi = meminst.MKmeminst
        (memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN))) bs ∧
      ty = memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN)) ∧
      bs.length = v_n * (64 * Ki) ∧
      Memtype_ok (memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN))) ∧
      wf_store s := by
```
[`Externaddr_invert_funcs`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L551)
```lean
theorem Externaddr_invert_funcs (s : store) (exta : addr) (ext : functype) :
    Externaddr_ok s (externaddr.FUNC exta) (externtype.FUNC ext) →
    ∃ (xt : externtype) (v_funcinst : funcinst),
      exta < s.FUNCS.length ∧ lookup_total s.FUNCS exta = v_funcinst ∧
      xt = externtype.FUNC v_funcinst.TYPE ∧
      wf_externtype (externtype.FUNC v_funcinst.TYPE) ∧
      Externtype_sub xt (externtype.FUNC ext) :=
```

</details>

## 9.2 Building a typing derivation (construction)

The mirror image of 9.1: these assemble a derivation for a reduct.

| Lemma | Meaning |
|---|---|
| [`construct_ais_typing_single`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1499) | Lift a one-instruction typing `Instr_ok2` to the one-element list. |
| [`construct_ais_subtyping`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1509) | Weaken a typing along an `instrtype_sub` fact (move 3 of file `08` §8.3). |
| [`construct_ais_compose`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1532) | Sequence two typings whose middle stack types match. |
| [`construct_ais_vals`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1816) | Type a list of pushed values from `Vals_ok` and a weakening. |
| [`construct_instrs_from_ais`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1575) | Lift a static `Instrs_ok` typing of plain instructions to their administrative versions. |
| [`construct_ais_trap`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1741) | `[TRAP]` has every type. |
| [`ais_empty_typing`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1156) | `[]` has type `t1s → t2s` exactly when the context and store are well-formed and `t1s ≤ t2s`. |
| [`const_I32_result`](../../../../../src/test-lean-claude/TypePreservation.lean#L896) | `[CONST I32 c]` has any type that weakens `[] → [I32]` (given `c` is well-formed). |
| [`construct_inst_prepend_label`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1919) | Pushing a label onto `C'` keeps `inst_match C C'` (labels are not compared). |
| `ais_cons_pre`, `ais_nil_refl`, `ais_const1`, `ais_val1`, `ais_ref1`, `ais_plain1` | The straight-line-program toolkit — file `08` §8.3. |

<details>
<summary>Exact statements (9.2)</summary>

[`construct_ais_typing_single`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1499)
```lean
theorem construct_ais_typing_single (v_S : store) (v_C : context) (v_ai : admininstr) (ts1 ts2 : List valtype) :
    Instr_ok2 v_S v_C v_ai (mkFunctype ts1 ts2) → Instrs_ok2 v_S v_C [v_ai] (mkFunctype ts1 ts2) := by
```
[`construct_ais_subtyping`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1509)
```lean
theorem construct_ais_subtyping (v_S : store) (v_C : context) (v_ais : List admininstr) (ts1 ts2 ts1' ts2' : List valtype) :
    Instrs_ok2 v_S v_C v_ais (mkFunctype ts1 ts2) →
    instrtype_sub (mkFunctype ts1 ts2) (mkFunctype ts1' ts2') →
    Instrs_ok2 v_S v_C v_ais (mkFunctype ts1' ts2') := by
```
[`construct_ais_compose`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1532)
```lean
theorem construct_ais_compose (v_S : store) (v_C : context) (v_ais1 v_ais2 : List admininstr) (t1s t2s t3s : List valtype) :
    Instrs_ok2 v_S v_C v_ais1 (mkFunctype t1s t2s) → Instrs_ok2 v_S v_C v_ais2 (mkFunctype t2s t3s) →
    Instrs_ok2 v_S v_C (v_ais1 ++ v_ais2) (mkFunctype t1s t3s) := by
```
[`construct_ais_vals`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1816)
```lean
theorem construct_ais_vals (v_S : store) (v_C : context) (v_vals : List val) (t1s t2s ts : List valtype) :
    wf_context v_C → wf_store v_S → instrtype_sub (mkFunctype [] ts) (mkFunctype t1s t2s) →
    Vals_ok v_S v_vals ts → Instrs_ok2 v_S v_C (v_vals.map admininstr_val) (mkFunctype t1s t2s) := by
```
[`construct_instrs_from_ais`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1575)
```lean
theorem construct_instrs_from_ais (v_S : store) (v_C : context) (v_instrs : List instr) (ts1 ts2 : List valtype) :
    wf_store v_S → Instrs_ok v_C v_instrs (mkFunctype ts1 ts2) →
    Instrs_ok2 v_S v_C (v_instrs.map admininstr_instr) (mkFunctype ts1 ts2) := by
```
[`construct_ais_trap`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1741)
```lean
theorem construct_ais_trap (v_S : store) (v_C : context) (v_ft : functype) :
    wf_context v_C → wf_store v_S → Instrs_ok2 v_S v_C [admininstr.TRAP] v_ft := by
```
[`ais_empty_typing`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1156)
```lean
theorem ais_empty_typing (v_S : store) (v_C : context) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [] (mkFunctype t1s t2s) ↔ (wf_context v_C ∧ wf_store v_S ∧ ResulttypeSub t1s t2s) := by
```
[`const_I32_result`](../../../../../src/test-lean-claude/TypePreservation.lean#L896)
```lean
theorem const_I32_result (s : store) (C : context) (c : num_) (t1s t2s : List valtype) :
    wf_num_ numtype.I32 c → wf_context C → wf_store s →
    instrtype_sub (mkFunctype [] [valtype.I32]) (mkFunctype t1s t2s) →
    Instrs_ok2 s C [admininstr.CONST numtype.I32 c] (mkFunctype t1s t2s) := fun hn hC hS hsub =>
```
[`construct_inst_prepend_label`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1919)
```lean
theorem construct_inst_prepend_label (C C' : context) (lab : resulttype) :
    inst_match C C' → inst_match C (prepend_label C' lab) := fun h => h
```

</details>

## 9.3 Subtyping

WASM 2.0's value subtyping is tiny: a type is a subtype of itself, and `BOT` is a subtype of everything. `BOT` only arises for unreachable code. Instruction types add the "frame" rule on top (file `08` §8.3).

The base definitions — [wasm2.0.lean:12728-12739](../../../../../src/test-lean-claude/wasm2.0.lean#L12728-L12739) and [Subtyping.lean:31-54](../../../../../src/test-lean-claude/Subtyping.lean#L31-L54):
```lean
/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:71.1-71.69 -/
inductive Valtype_sub : valtype → valtype → Prop where
  | refl (t : valtype) : Valtype_sub t t
  | bot (t : valtype) : Valtype_sub valtype.BOT t


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:72.1-72.76 -/
inductive Resulttype_sub : resulttype → resulttype → Prop where
  | mk_Resulttype_sub (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (List.length t_1_lst) = (List.length t_2_lst) →
    Forall₂ (fun (t_1_elem : valtype) (t_2_elem : valtype) => Valtype_sub t_1_elem t_2_elem) t_1_lst t_2_lst →
    Resulttype_sub (.mk_list t_1_lst) (.mk_list t_2_lst)
```
```lean
/-- Rocq: `Notation "tf1 :-> tf2" := (mk_functype (mk_list _ tf1) (mk_list _ tf2))`. -/
def mkFunctype (t1 t2 : List valtype) : functype := functype.mk_functype (.mk_list t1) (.mk_list t2)

/-- Rocq: `Notation "t1 <tv: t2" := (Valtype_sub t1 t2)`. Kept as a plain alias (not a
    notation) to avoid clashing with `<` on `Nat`-like types when this file is opened
    alongside others; call sites read `Valtype_sub t1 t2` directly, matching the underlying
    backend-generated relation name 1:1. -/
abbrev ValtypeSub := @Valtype_sub

/-- Rocq: `Definition Resulttype_subtype ts1 ts2 := Resulttype_sub (mk_list _ ts1) (mk_list _ ts2)`. -/
def ResulttypeSub (ts1 ts2 : List valtype) : Prop := Resulttype_sub (.mk_list ts1) (.mk_list ts2)

/-- Rocq: `Definition instrtype_sub tf tf' : Prop := match tf, tf' with ts11:->ts12, ts21:->ts22 =>
    exists ts_sub ts ts11_sub ts12_sup, ts21 = ts_sub++ts11_sub /\ ts22 = ts++ts12_sup /\
    (ts_sub<ts:ts) /\ (ts11_sub<ts:ts11) /\ (ts12<ts:ts12_sup) end`. -/
def instrtype_sub (tf tf' : functype) : Prop :=
  match tf, tf' with
  | .mk_functype (.mk_list ts11) (.mk_list ts12), .mk_functype (.mk_list ts21) (.mk_list ts22) =>
    ∃ ts_sub ts ts11_sub ts12_sup,
      ts21 = ts_sub ++ ts11_sub ∧
      ts22 = ts ++ ts12_sup ∧
      ResulttypeSub ts_sub ts ∧
      ResulttypeSub ts11_sub ts11 ∧
      ResulttypeSub ts12 ts12_sup
```

| Lemma | Meaning |
|---|---|
| [`instrtype_sub_compose_eq`](../../../../../src/test-lean-claude/Subtyping.lean#L452) | Combine the weakenings of two adjacent pieces into one for the whole sequence, when the middle stack types have the same length; also returns the subtyping between the two middles. |
| [`instrtype_sub_compose_le`](../../../../../src/test-lean-claude/Subtyping.lean#L396) | A variant where the second piece also consumes extra stack slots (`ts3`) from underneath. |
| [`instrtype_sub_empty`](../../../../../src/test-lean-claude/Subtyping.lean#L536) | If `[] → []` weakens to `t1s → t2s`, then `t1s ≤ t2s`. |
| [`instrtype_sub_iff_resulttype_sub`](../../../../../src/test-lean-claude/Subtyping.lean#L579) | `ts1 ≤ ts2` exactly when `ts3 → ts1` weakens to `ts3 → ts2`. |
| [`resulttype_sub_refl`](../../../../../src/test-lean-claude/Subtyping.lean#L147) | `ts ≤ ts`. |
| [`resulttype_sub_non_bot`](../../../../../src/test-lean-claude/Subtyping.lean#L83) | If `ts` contains no `BOT`, then `ts ≤ ts2` forces `ts = ts2`. |
| [`Val_ok_non_bot`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1779), [`Vals_ok_non_bot`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1934) | A value never has type `BOT` — which is why value types, once known, are pinned exactly. |

<details>
<summary>Exact statements (9.3)</summary>

[`instrtype_sub_compose_eq`](../../../../../src/test-lean-claude/Subtyping.lean#L452)
```lean
theorem instrtype_sub_compose_eq (ts1 ts2 ts2' ts3 txs tys tzs : List valtype) :
    instrtype_sub (mkFunctype ts1 ts2) (mkFunctype txs tys) →
    instrtype_sub (mkFunctype ts2' ts3) (mkFunctype tys tzs) →
    ts2.length = ts2'.length →
    instrtype_sub (mkFunctype ts1 ts3) (mkFunctype txs tzs) ∧ ResulttypeSub ts2 ts2' := by
```
[`instrtype_sub_compose_le`](../../../../../src/test-lean-claude/Subtyping.lean#L396)
```lean
theorem instrtype_sub_compose_le (ts1 ts2' ts2 ts3 ts4 txs tys tzs : List valtype) :
    instrtype_sub (mkFunctype ts1 ts2') (mkFunctype txs tys) →
    instrtype_sub (mkFunctype (ts3 ++ ts2) ts4) (mkFunctype tys tzs) →
    ts2.length = ts2'.length →
    instrtype_sub (mkFunctype (ts3 ++ ts1) ts4) (mkFunctype txs tzs) ∧ ResulttypeSub ts2' ts2 := by
```
[`instrtype_sub_empty`](../../../../../src/test-lean-claude/Subtyping.lean#L536)
```lean
theorem instrtype_sub_empty (txs tys : List valtype) :
    instrtype_sub (mkFunctype [] []) (mkFunctype txs tys) → ResulttypeSub txs tys := by
```
[`instrtype_sub_iff_resulttype_sub`](../../../../../src/test-lean-claude/Subtyping.lean#L579)
```lean
theorem instrtype_sub_iff_resulttype_sub (ts1 ts2 ts3 : List valtype) :
    ResulttypeSub ts1 ts2 ↔ instrtype_sub (mkFunctype ts3 ts1) (mkFunctype ts3 ts2) := by
```
[`resulttype_sub_refl`](../../../../../src/test-lean-claude/Subtyping.lean#L147)
```lean
theorem resulttype_sub_refl (ts : List valtype) : ResulttypeSub ts ts :=
```
[`resulttype_sub_non_bot`](../../../../../src/test-lean-claude/Subtyping.lean#L83)
```lean
theorem resulttype_sub_non_bot (v_ts v_ts2 : List valtype) :
    Forall (fun v_t => v_t ≠ valtype.BOT) v_ts → ResulttypeSub v_ts v_ts2 → v_ts = v_ts2 := by
```
[`Val_ok_non_bot`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1779)
```lean
theorem Val_ok_non_bot (v_S : store) (v_val : val) (t : valtype) :
    Val_ok v_S v_val t → t ≠ valtype.BOT := by
```
[`Vals_ok_non_bot`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1934)
```lean
theorem Vals_ok_non_bot (v_S : store) (v_val : List val) (v_ts : List valtype) :
    Vals_ok v_S v_val v_ts → Forall (fun t => t ≠ valtype.BOT) v_ts := by
```

</details>

## 9.4 Module instance ↔ context

These bridge the runtime view (store addresses held by a module instance) and the static view (types in a context) — primer §0.2–0.3.

| Lemma | Meaning |
|---|---|
| [`inst_match`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1886) | The two contexts agree except on locals, labels, and return (primer §0.3). |
| [`Moduleinst_ok_lengths`](../../../../../src/test-lean-claude/TypePreservation.lean#L408) | A module instance's address lists have the same lengths as its context's type lists. |
| [`minst_invert_globals`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L749), [`minst_invert_tables`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L728), [`minst_invert_mems`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L770), [`minst_invert_elems`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L796), [`minst_invert_datas`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L810) | Per sort: every address the module holds is in range in the store; for globals, tables, and memories the instance there has the context's type up to extern subtyping, and for element segments it has exactly the context's element type with every reference well-typed. (Data segments carry no type.) |
| [`minst_invert_functypes`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L694) | The context's type section equals the module instance's. |
| [`minst_func_externaddr`](../../../../../src/test-lean-claude/TypePreservation.lean#L1911) | The module's function address `k` is a store function of the context's type `C'.FUNCS[k]`. |
| [`lookup_global`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L838) | The store global behind a module's global index holds a value of the declared type. |
| [`table_refs_ok`](../../../../../src/test-lean-claude/TypePreservation.lean#L1881), [`elem_refs_ok`](../../../../../src/test-lean-claude/TypePreservation.lean#L1921) | Every reference in the table / element segment behind a module index has the declared element type. |
| [`inst_t_context_local_empty`](../../../../../src/test-lean-claude/TypePreservation.lean#L103) | A module-level context has no locals. |
| [`inst_match_locals_append`](../../../../../src/test-lean-claude/TypePreservation.lean#L671) | Putting a locals-only context in front of `C` keeps `inst_match`. |
| [`locals_append_eq`](../../../../../src/test-lean-claude/TypePreservation.lean#L679) | The locals of `{LOCALS := tl} ++ C` are exactly `tl`, when `C` has none. |
| [`externtype_global_eq`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L485), [`externtype_func_eq`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L493) | For globals and functions, extern subtyping is equality. |
| [`externtype_table_sub_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L956) | A table's extern-subtype has the same element type (only the limits may differ). |

<details>
<summary>Exact statements (9.4)</summary>

[`inst_match`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1886)
```lean
/-- Rocq `typing_lemmas.v:1833` `inst_match`. Deliberately excludes LOCALS/LABELS/RETURN:
    "same module-instance-derived components, differing local/label/return typing". -/
def inst_match (C C' : context) : Prop :=
  C.TYPES = C'.TYPES ∧ C.FUNCS = C'.FUNCS ∧ C.GLOBALS = C'.GLOBALS ∧ C.TABLES = C'.TABLES ∧
  C.MEMS = C'.MEMS ∧ C.ELEMS = C'.ELEMS ∧ C.DATAS = C'.DATAS
```
[`Moduleinst_ok_lengths`](../../../../../src/test-lean-claude/TypePreservation.lean#L408)
```lean
theorem Moduleinst_ok_lengths (s : store) (minst : moduleinst) (C : context) :
    Moduleinst_ok s minst C →
    minst.GLOBALS.length = C.GLOBALS.length ∧ minst.FUNCS.length = C.FUNCS.length ∧
    minst.MEMS.length = C.MEMS.length ∧ minst.TABLES.length = C.TABLES.length ∧
    minst.DATAS.length = C.DATAS.length ∧ minst.ELEMS.length = C.ELEMS.length := by
```
[`minst_invert_globals`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L749)
```lean
theorem minst_invert_globals (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ga gt => ∃ gt' v_val, ga < v_S.GLOBALS.length ∧
      lookup_total v_S.GLOBALS ga = globalinst.MKglobalinst gt' v_val ∧
      Externtype_sub (externtype.GLOBAL gt') (externtype.GLOBAL gt)) minst.GLOBALS C'.GLOBALS := by
```
[`minst_invert_tables`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L728)
```lean
theorem minst_invert_tables (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun tba tbt => ∃ tbr tbt', tba < v_S.TABLES.length ∧
      lookup_total v_S.TABLES tba = tableinst.MKtableinst tbt' tbr ∧
      Externtype_sub (externtype.TABLE tbt') (externtype.TABLE tbt)) minst.TABLES C'.TABLES := by
```
[`minst_invert_mems`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L770)
```lean
theorem minst_invert_mems (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ma mt => ∃ v_mt b_lst, ma < v_S.MEMS.length ∧
      lookup_total v_S.MEMS ma = meminst.MKmeminst v_mt b_lst ∧
      Externtype_sub (externtype.MEM v_mt) (externtype.MEM mt)) minst.MEMS C'.MEMS := by
```
[`minst_invert_elems`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L796)
```lean
theorem minst_invert_elems (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ea et => ∃ ref_lst, ea < v_S.ELEMS.length ∧ Forall (fun r => Ref_ok v_S r et) ref_lst ∧
      lookup_total v_S.ELEMS ea = eleminst.MKeleminst et ref_lst) minst.ELEMS C'.ELEMS := by
```
[`minst_invert_datas`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L810)
```lean
theorem minst_invert_datas (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    minst.DATAS.length = C'.DATAS.length ∧
      Forall (fun da => ∃ b_lst, da < v_S.DATAS.length ∧ lookup_total v_S.DATAS da = datainst.MKdatainst b_lst)
        minst.DATAS := by
```
[`minst_invert_functypes`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L694)
```lean
theorem minst_invert_functypes (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' → C'.TYPES = minst.TYPES := by
```
[`minst_func_externaddr`](../../../../../src/test-lean-claude/TypePreservation.lean#L1911)
```lean
theorem minst_func_externaddr (s : store) (minst : moduleinst) (C C' : context) (k : Nat) :
    Moduleinst_ok s minst C → inst_match C C' → k < C'.FUNCS.length →
    Externaddr_ok s (externaddr.FUNC (minst.FUNCS[k]!)) (externtype.FUNC (C'.FUNCS[k]!)) := by
```
[`lookup_global`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L838)
```lean
theorem lookup_global (v_a : Nat) (v_C v_C' : context) (v_mut : «mut») (v_vt : valtype) (v_S : store) (minst : moduleinst) :
    v_a < v_C'.GLOBALS.length → lookup_total v_C'.GLOBALS v_a = globaltype.mk_globaltype v_mut v_vt →
    Moduleinst_ok v_S minst v_C → inst_match v_C v_C' → Store_ok v_S →
    Val_ok v_S (lookup_total v_S.GLOBALS (lookup_total minst.GLOBALS v_a)).VALUE v_vt := by
```
[`table_refs_ok`](../../../../../src/test-lean-claude/TypePreservation.lean#L1881)
```lean
theorem table_refs_ok (s : store) (minst : moduleinst) (C C' : context) (x : tableidx) (rt : reftype)
    (lim : limits) :
    Store_ok s → Moduleinst_ok s minst C → inst_match C C' →
    C'.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) →
    Forall (fun r => Ref_ok s r rt) (s.TABLES[minst.TABLES[proj_uN_0 x]!]!).REFS := by
```
[`elem_refs_ok`](../../../../../src/test-lean-claude/TypePreservation.lean#L1921)
```lean
theorem elem_refs_ok (s : store) (minst : moduleinst) (C C' : context) (y : elemidx) (rt : reftype) :
    Moduleinst_ok s minst C → inst_match C C' → C'.ELEMS[proj_uN_0 y]? = some rt →
    Forall (fun r => Ref_ok s r rt) (s.ELEMS[minst.ELEMS[proj_uN_0 y]!]!).REFS := by
```
[`inst_t_context_local_empty`](../../../../../src/test-lean-claude/TypePreservation.lean#L103)
```lean
theorem inst_t_context_local_empty (s : store) (i : moduleinst) (C : context) :
    Moduleinst_ok s i C → C.LOCALS = [] := by
```
[`inst_match_locals_append`](../../../../../src/test-lean-claude/TypePreservation.lean#L671)
```lean
theorem inst_match_locals_append (tl : List valtype) (C : context) :
    inst_match C (({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [],
        ELEMS := [], DATAS := [], LOCALS := tl, LABELS := [], RETURN := none } : context) ++ C) := by
```
[`locals_append_eq`](../../../../../src/test-lean-claude/TypePreservation.lean#L679)
```lean
theorem locals_append_eq (tl : List valtype) (C : context) (h : C.LOCALS = []) :
    ((({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [],
        ELEMS := [], DATAS := [], LOCALS := tl, LABELS := [], RETURN := none } : context)
      ++ C) : context).LOCALS = tl := by
```
[`externtype_global_eq`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L485)
```lean
theorem externtype_global_eq (gt gt' : globaltype) :
    Externtype_sub (externtype.GLOBAL gt) (externtype.GLOBAL gt') → gt = gt' := by
```
[`externtype_func_eq`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L493)
```lean
theorem externtype_func_eq (ft ft' : functype) :
    Externtype_sub (externtype.FUNC ft) (externtype.FUNC ft') → ft = ft' := by
```
[`externtype_table_sub_inv`](../../../../../src/test-lean-claude/TypePreservation.lean#L956)
```lean
theorem externtype_table_sub_inv (tbt : tabletype) (lim : limits) (rt : reftype) :
    Externtype_sub (externtype.TABLE tbt) (externtype.TABLE (tabletype.mk_tabletype lim rt)) →
    ∃ lim', tbt = tabletype.mk_tabletype lim' rt := by
```

</details>

## 9.5 Taking the store apart and putting it back

The five-step recipe of file `02` §2a in lemma form.

| Lemma | Meaning |
|---|---|
| [`Store_ok_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L306), [`Store_ok_of_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L321) | `Store_ok` is equivalent to: each of the six component lists is typed (`Forall₂` against a list of types of the same length), plus well-formedness. |
| [`wf_store_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L359), [`Store_ok_wf_store`](../../../../../src/test-lean-claude/TypePreservation.lean#L1308) | Split `wf_store` into per-component facts; `Store_ok` implies `wf_store`. |
| [`wf_store_with_globals`](../../../../../src/test-lean-claude/TypePreservation.lean#L923), [`wf_store_with_tables`](../../../../../src/test-lean-claude/TypePreservation.lean#L929), [`wf_store_with_mems`](../../../../../src/test-lean-claude/TypePreservation.lean#L935), [`wf_store_with_elems`](../../../../../src/test-lean-claude/TypePreservation.lean#L941), [`wf_store_with_datas`](../../../../../src/test-lean-claude/TypePreservation.lean#L947) | Replacing one component with a well-formed list keeps the store well-formed. |
| [`list_update_func`](../../../../../src/test-lean-claude/HelperLemmas.lean#L40), [`list_update_length_func`](../../../../../src/test-lean-claude/HelperLemmas.lean#L429), [`Forall_list_update_func`](../../../../../src/test-lean-claude/TypePreservation.lean#L286) | Modify one list element (`List.modify`); this keeps the length, and keeps any property the modifier preserves. |
| [`lookup_total`](../../../../../src/test-lean-claude/HelperLemmas.lean#L33), [`Forall2_nth_of_length`](../../../../../src/test-lean-claude/HelperLemmas.lean#L271) | `l[n]!`; and from `Forall₂ R l l'` with equal lengths, `R l[i] l'[i]` — the standard way to read one slot's typing. |
| [`mem_zip_modify_right`](../../../../../src/test-lean-claude/HelperLemmas.lean#L298) | After modifying one slot of the right-hand list, each zipped pair is either an old pair or the modified one (used to update `Vals_ok` after `local.set`). |
| [`holds_upto`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L89), [`Extend_store_of_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L334) | "Holds for every index below `n`"; and build `Extend_store` from per-component facts. |
| [`construct_globalinsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2140), [`construct_tableinsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2067), [`construct_tableinsts_grow`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2087), [`construct_meminsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2177), [`construct_meminsts_grow`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2196), [`construct_eleminsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2261), [`construct_datainsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2250) | Re-type one component list after a single write (set, grow, overwrite bytes, drop). |
| [`datatype_eq_OK`](../../../../../src/test-lean-claude/TypePreservation.lean#L1061), [`datainsts_Forall_of_Forall₂`](../../../../../src/test-lean-claude/TypePreservation.lean#L1065), [`datainsts_Forall₂_of_Forall`](../../../../../src/test-lean-claude/TypePreservation.lean#L1074) | `datatype` has one value, so the two forms of data-segment typing are interchangeable. |
| [`mem_store_extension`](../../../../../src/test-lean-claude/TypePreservation.lean#L422), [`splice_eq_list_slice_update`](../../../../../src/test-lean-claude/HelperLemmas.lean#L467) | The memory-write engine behind `with_mem_store_ok` (file `02`); `splice` is a slice update. |

<details>
<summary>Exact statements (9.5)</summary>

[`Store_ok_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L306)
```lean
theorem Store_ok_parts (s : store) (h : Store_ok s) :
    ∃ (gtl : List globaltype) (mtl : List memtype) (ttl : List tabletype) (ftl : List functype)
      (dtl : List datatype) (etl : List elemtype),
      s.GLOBALS.length = gtl.length ∧ Forall₂ (fun v t => Globalinst_ok s v t) s.GLOBALS gtl ∧
      s.MEMS.length = mtl.length ∧ Forall₂ (fun v t => Meminst_ok s v t) s.MEMS mtl ∧
      s.TABLES.length = ttl.length ∧ Forall₂ (fun v t => Tableinst_ok s v t) s.TABLES ttl ∧
      s.FUNCS.length = ftl.length ∧ Forall₂ (fun v t => Funcinst_ok s v t) s.FUNCS ftl ∧
      s.DATAS.length = dtl.length ∧ Forall₂ (fun v t => Datainst_ok s v t) s.DATAS dtl ∧
      s.ELEMS.length = etl.length ∧ Forall₂ (fun v t => Eleminst_ok s v t) s.ELEMS etl ∧
      wf_store s ∧ Forall wf_memtype mtl ∧ Forall wf_tabletype ttl := by
```
[`Store_ok_of_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L321)
```lean
theorem Store_ok_of_parts (s : store) (gtl : List globaltype) (mtl : List memtype) (ttl : List tabletype)
    (ftl : List functype) (dtl : List datatype) (etl : List elemtype) :
    s.GLOBALS.length = gtl.length → Forall₂ (fun v t => Globalinst_ok s v t) s.GLOBALS gtl →
    s.MEMS.length = mtl.length → Forall₂ (fun v t => Meminst_ok s v t) s.MEMS mtl →
    s.TABLES.length = ttl.length → Forall₂ (fun v t => Tableinst_ok s v t) s.TABLES ttl →
    s.FUNCS.length = ftl.length → Forall₂ (fun v t => Funcinst_ok s v t) s.FUNCS ftl →
    s.DATAS.length = dtl.length → Forall₂ (fun v t => Datainst_ok s v t) s.DATAS dtl →
    s.ELEMS.length = etl.length → Forall₂ (fun v t => Eleminst_ok s v t) s.ELEMS etl →
    wf_store s → Forall wf_memtype mtl → Forall wf_tabletype ttl → Store_ok s := by
```
[`wf_store_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L359)
```lean
theorem wf_store_parts (s : store) (h : wf_store s) :
    Forall wf_funcinst s.FUNCS ∧ Forall wf_globalinst s.GLOBALS ∧ Forall wf_tableinst s.TABLES ∧
      Forall wf_meminst s.MEMS ∧ Forall wf_datainst s.DATAS := by
```
[`Store_ok_wf_store`](../../../../../src/test-lean-claude/TypePreservation.lean#L1308)
```lean
theorem Store_ok_wf_store (s : store) (h : Store_ok s) : wf_store s := by
```
[`wf_store_with_globals`](../../../../../src/test-lean-claude/TypePreservation.lean#L923)
```lean
theorem wf_store_with_globals (s : store) (gs : List globalinst) :
    wf_store s → Forall wf_globalinst gs → wf_store { s with GLOBALS := gs } := by
```
[`wf_store_with_tables`](../../../../../src/test-lean-claude/TypePreservation.lean#L929)
```lean
theorem wf_store_with_tables (s : store) (ts : List tableinst) :
    wf_store s → Forall wf_tableinst ts → wf_store { s with TABLES := ts } := by
```
[`wf_store_with_mems`](../../../../../src/test-lean-claude/TypePreservation.lean#L935)
```lean
theorem wf_store_with_mems (s : store) (ms : List meminst) :
    wf_store s → Forall wf_meminst ms → wf_store { s with MEMS := ms } := by
```
[`wf_store_with_elems`](../../../../../src/test-lean-claude/TypePreservation.lean#L941)
```lean
theorem wf_store_with_elems (s : store) (es : List eleminst) :
    wf_store s → wf_store { s with ELEMS := es } := by
```
[`wf_store_with_datas`](../../../../../src/test-lean-claude/TypePreservation.lean#L947)
```lean
theorem wf_store_with_datas (s : store) (ds : List datainst) :
    wf_store s → Forall wf_datainst ds → wf_store { s with DATAS := ds } := by
```
[`list_update_func`](../../../../../src/test-lean-claude/HelperLemmas.lean#L40)
```lean
abbrev list_update_func {α : Type} (l : List α) (n : Nat) (f : α → α) : List α := l.modify n f
```
[`list_update_length_func`](../../../../../src/test-lean-claude/HelperLemmas.lean#L429)
```lean
theorem list_update_length_func {α : Type} (l : List α) (f : α → α) (i : Nat) :
    (list_update_func l i f).length = l.length := List.length_modify f l i
```
[`Forall_list_update_func`](../../../../../src/test-lean-claude/TypePreservation.lean#L286)
```lean
theorem Forall_list_update_func {A : Type} (P : A → Prop) (l : List A) (n : Nat) (f : A → A) :
    Forall P l → (∀ x, P x → P (f x)) → Forall P (list_update_func l n f) := by
```
[`lookup_total`](../../../../../src/test-lean-claude/HelperLemmas.lean#L33)
```lean
def lookup_total {α : Type} [Inhabited α] (l : List α) (n : Nat) : α := l[n]!
```
[`Forall2_nth_of_length`](../../../../../src/test-lean-claude/HelperLemmas.lean#L271)
```lean
theorem Forall2_nth_of_length {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    (l : List α) (l' : List β) (h : Forall₂ R l l') (hlen : l.length = l'.length)
    (i : Nat) (hi : i < l.length) : R (l[i]!) (l'[i]!) :=
```
[`mem_zip_modify_right`](../../../../../src/test-lean-claude/HelperLemmas.lean#L298)
```lean
theorem mem_zip_modify_right {α β : Type} [Inhabited α] [Inhabited β] (g : β → β)
    (l : List α) :
    ∀ (ts : List β) (idx : Nat) (p : α × β), p ∈ l.zip (ts.modify idx g) →
      p ∈ l.zip ts ∨
        (p.1 = l[idx]! ∧ p.2 = g (ts[idx]!) ∧ (l[idx]!, ts[idx]!) ∈ l.zip ts) := by
```
[`holds_upto`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L89)
```lean
abbrev holds_upto (P : Nat → Prop) (n : Nat) : Prop := Forall P (List.range n)
```
[`Extend_store_of_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L334)
```lean
theorem Extend_store_of_parts (s s' : store) :
    s.GLOBALS.length ≤ s'.GLOBALS.length →
    holds_upto (fun a => Extend_globalinst (s.GLOBALS[a]!) (s'.GLOBALS[a]!)) s.GLOBALS.length →
    s.MEMS.length ≤ s'.MEMS.length →
    holds_upto (fun a => Extend_meminst (s.MEMS[a]!) (s'.MEMS[a]!)) s.MEMS.length →
    s.TABLES.length ≤ s'.TABLES.length →
    holds_upto (fun a => Extend_tableinst (s.TABLES[a]!) (s'.TABLES[a]!)) s.TABLES.length →
    s.FUNCS.length ≤ s'.FUNCS.length →
    holds_upto (fun a => Extend_funcinst (s.FUNCS[a]!) (s'.FUNCS[a]!)) s.FUNCS.length →
    s.DATAS.length ≤ s'.DATAS.length →
    holds_upto (fun a => Extend_datainst (s.DATAS[a]!) (s'.DATAS[a]!)) s.DATAS.length →
    s.ELEMS.length ≤ s'.ELEMS.length →
    holds_upto (fun a => Extend_eleminst (s.ELEMS[a]!) (s'.ELEMS[a]!)) s.ELEMS.length →
    wf_store s → wf_store s' → Extend_store s s' := by
```
[`construct_globalinsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2140)
```lean
theorem construct_globalinsts (s : store) (ts : List globaltype) (ga : Nat) (v : val) (t : valtype) (v_old : val) :
    Forall₂ (fun v0 ty => Globalinst_ok s v0 ty) s.GLOBALS ts →
    lookup_total s.GLOBALS ga = globalinst.MKglobalinst (globaltype.mk_globaltype (some r_MUT.MUT) t) v_old →
    Val_ok s v t →
    Forall₂ (fun v0 ty => Globalinst_ok s v0 ty) (list_update_func s.GLOBALS ga (fun g => { g with VALUE := v })) ts := by
```
[`construct_tableinsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2067)
```lean
theorem construct_tableinsts (s : store) (ts : List tabletype) (t : reftype) (tba : Nat) (lim : limits)
    (tbr : List ref) (i : Nat) (ref_lst : ref) :
    Forall₂ (fun v ty => Tableinst_ok s v ty) s.TABLES ts → Ref_ok s ref_lst t →
    lookup_total s.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype lim t) tbr →
    Forall₂ (fun v ty => Tableinst_ok s v ty)
      (list_update_func s.TABLES tba (fun v1 => { v1 with REFS := list_update_func v1.REFS i (fun _ => ref_lst) })) ts := by
```
[`construct_tableinsts_grow`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2087)
```lean
theorem construct_tableinsts_grow (s : store) (ts : List tabletype) (ref_lst : ref) (t : reftype)
    (tba : Nat) (v_r : List ref) (j_opt : Option uN) (v_n : Nat) (tbinsts : List tableinst) :
    Forall wf_tableinst tbinsts →
    Forall₂ (fun v ty => Tableinst_ok s v ty) s.TABLES ts → Ref_ok s ref_lst t →
    Forall (fun v_j => v_r.length + v_n ≤ (proj_uN_0 v_j)) (Option.toList j_opt) →
    lookup_total s.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_r.length) j_opt) t) v_r →
    tbinsts = list_update_func s.TABLES tba (fun _ => tableinst.MKtableinst
        (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (v_r.length + v_n)) j_opt) t) (v_r ++ List.replicate v_n ref_lst)) →
    Forall₂ (fun v ty => Tableinst_ok s v ty) tbinsts
      (list_update_func ts tba (fun _ => tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (v_r.length + v_n)) j_opt) t)) := by
```
[`construct_meminsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2177)
```lean
theorem construct_meminsts (s : store) (ts : List memtype) (ma : Nat) (v_mt : memtype) (b_lst : List byte)
    (v_i : Nat) (v_nb : List byte) :
    Forall wf_byte v_nb →
    Forall₂ (fun v ty => Meminst_ok s v ty) s.MEMS ts →
    lookup_total s.MEMS ma = meminst.MKmeminst v_mt b_lst →
    Forall₂ (fun v ty => Meminst_ok s v ty)
      (list_update_func s.MEMS ma (fun m => { m with BYTES := list_slice_update m.BYTES v_i v_nb.length v_nb })) ts := by
```
[`construct_meminsts_grow`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2196)
```lean
theorem construct_meminsts_grow (s : store) (ts : List memtype) (ma : Nat) (b_lst : List byte)
    (lim_old v_n : Nat) (v_j_opt : Option uN) (minsts : List meminst) :
    Forall wf_meminst minsts →
    Forall₂ (fun v ty => Meminst_ok s v ty) s.MEMS ts →
    lookup_total s.MEMS ma = meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN lim_old) v_j_opt)) b_lst →
    lim_old = b_lst.length / (64 * Ki) →
    Forall (fun v_j => lim_old + v_n ≤ (proj_uN_0 v_j)) (Option.toList v_j_opt) → lim_old + v_n ≤ 2 ^ 16 →
    minsts = list_update_func s.MEMS ma (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (lim_old + v_n)) v_j_opt))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))) →
    Forall₂ (fun v ty => Meminst_ok s v ty) minsts
      (list_update_func ts ma (fun _ => memtype.PAGE (limits.mk_limits (uN.mk_uN (lim_old + v_n)) v_j_opt))) := by
```
[`construct_eleminsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2261)
```lean
theorem construct_eleminsts (s : store) (ts : List elemtype) (ea : Nat) (t : elemtype) (ref_lst : List ref) :
    Forall₂ (fun v ty => Eleminst_ok s v ty) s.ELEMS ts →
    lookup_total s.ELEMS ea = eleminst.MKeleminst t ref_lst →
    Forall₂ (fun v ty => Eleminst_ok s v ty) (list_update_func s.ELEMS ea (fun e => { e with REFS := [] })) ts := by
```
[`construct_datainsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L2250)
```lean
theorem construct_datainsts (s : store) (da : Nat) (b_lst : List byte) :
    Forall (fun a => Datainst_ok s a datatype.OK) s.DATAS → lookup_total s.DATAS da = datainst.MKdatainst b_lst →
    Forall (fun a => Datainst_ok s a datatype.OK) (list_update_func s.DATAS da (fun _ => datainst.MKdatainst [])) := by
```
[`datatype_eq_OK`](../../../../../src/test-lean-claude/TypePreservation.lean#L1061)
```lean
theorem datatype_eq_OK (t : datatype) : t = datatype.OK := by cases t; rfl
```
[`datainsts_Forall_of_Forall₂`](../../../../../src/test-lean-claude/TypePreservation.lean#L1065)
```lean
theorem datainsts_Forall_of_Forall₂ (s : store) (ds : List datainst) (dts : List datatype) :
    ds.length = dts.length → Forall₂ (fun v t => Datainst_ok s v t) ds dts →
    Forall (fun a => Datainst_ok s a datatype.OK) ds := by
```
[`datainsts_Forall₂_of_Forall`](../../../../../src/test-lean-claude/TypePreservation.lean#L1074)
```lean
theorem datainsts_Forall₂_of_Forall (s : store) (ds : List datainst) (dts : List datatype) :
    Forall (fun a => Datainst_ok s a datatype.OK) ds → Forall₂ (fun v t => Datainst_ok s v t) ds dts := by
```
[`mem_store_extension`](../../../../../src/test-lean-claude/TypePreservation.lean#L422)
```lean
theorem mem_store_extension (s : store) (v_f : frame) (C C' : context) (off : Nat) (b_lst : List byte)
    (len : Nat) :
    Store_ok s → wf_store s → Moduleinst_ok s v_f.MODULE C → inst_match C C' → 0 < C'.MEMS.length →
    Forall wf_byte b_lst → b_lst.length = len →
    Extend_store s { s with
      MEMS := list_update_func s.MEMS (v_f.MODULE.MEMS[0]!)
        (fun m => { m with BYTES := list_slice_update m.BYTES off len b_lst }) } ∧
    Store_ok { s with
      MEMS := list_update_func s.MEMS (v_f.MODULE.MEMS[0]!)
        (fun m => { m with BYTES := list_slice_update m.BYTES off len b_lst }) } := by
```
[`splice_eq_list_slice_update`](../../../../../src/test-lean-claude/HelperLemmas.lean#L467)
```lean
theorem splice_eq_list_slice_update {α : Type} (l b : List α) (i : Nat) :
    splice l b i = list_slice_update l i b.length b := by
```

</details>

## 9.6 Store extension

Everything about `Extend_store` (primer §0.6) beyond the two diagram nodes `Extend_store_refl` (file `02`) and `Extend_store_moduleinst` (file `04`).

| Lemma | Meaning |
|---|---|
| [`extend_global_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1008), [`extend_mem_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L994), [`extend_table_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L949), [`extend_func_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L928), [`extend_data_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1033), [`extend_elem_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1021) | Per component: an unchanged list extends itself (the "other five components" in every store-writing proof). |
| [`extend_globalinst_refl_0`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1001) (and the `_meminst_`, `_tableinst_`, `_funcinst_`, `_datainst_`, `_eleminst_` siblings) | The same for a single instance. |
| [`forall_range_lt`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L98), [`forall_range_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L107) | Index-range plumbing used by `Extend_store_refl`. |
| [`global_set_global_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1200), [`table_set_table_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1299), [`table_grow_table_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1346), [`store_none_mem_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1232), [`memory_grow_mem_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1267), [`elem_drop_elem_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1380), [`data_drop_data_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1399) | One per kind of write: the written component, old versus new, satisfies the component's `Extend_*` relation at every index. |
| [`Extend_store_globalinsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1809), [`Extend_store_tableinsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1823), [`Extend_store_meminsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1836), [`Extend_store_funcinsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1795), [`Extend_store_eleminsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1728), [`Extend_store_datainsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1746), [`Extend_store_datainsts₂`](../../../../../src/test-lean-claude/TypePreservation.lean#L367) | A component's typing relative to the old store carries over to the extended store — needed even for unchanged components, because `*_ok` judgments are indexed by the store (file `02` §2a). |
| [`Extend_store_vals`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1171) | `Vals_ok` carries over (used for the locals, file `05`). |
| [`Extend_store_ais`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1875) | A whole instruction-sequence typing carries over (used in file `07`'s congruence cases). |
| [`Extend_store_exts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1659), [`Extend_store_datainst_ext`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1698), [`Extend_store_eleminst_ext`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1683) | Export instances, and a data/element instance together with its extended version, stay well-typed. |
| [`addrss_store_globals_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1611), [`addrss_store_funcs_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1595), [`addrss_tables_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1603), [`addrss_mems_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1619) | A list of well-typed addresses of one sort stays well-typed in the extended store (the core of `Extend_store_moduleinst`). |
| [`Extend_store_wf_store'`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1127) | The extended store is well-formed. |

<details>
<summary>Exact statements (9.6)</summary>

[`extend_global_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1008)
```lean
theorem extend_global_refl (s : store) (h : Forall wf_globalinst s.GLOBALS) :
    holds_upto (fun n => Extend_globalinst (s.GLOBALS[n]!) (s.GLOBALS[n]!)) s.GLOBALS.length :=
```
[`extend_globalinst_refl_0`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1001)
```lean
theorem extend_globalinst_refl_0 {g : globalinst} (h : wf_globalinst g) : Extend_globalinst g g := by
```
[`forall_range_lt`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L98)
```lean
theorem forall_range_lt {α : Type} (l : List α) :
    Forall (fun a => a < l.length) (List.range l.length) := by
```
[`forall_range_refl`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L107)
```lean
theorem forall_range_refl {α : Type} [Inhabited α] (l : List α) (P : α → Prop)
    (R : α → α → Prop) (hP : Forall P l) (hR : ∀ x, P x → R x x) :
    Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
```
[`global_set_global_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1200)
```lean
theorem global_set_global_extension (v_g v_g' : List globalinst) (v_idx : Nat) (v_valtype : valtype)
    (v_val_0 v_val_1 : val) :
    Forall wf_globalinst v_g → wf_val v_val_1 →
    v_idx < v_g.length → lookup_total v_g v_idx = globalinst.MKglobalinst (globaltype.mk_globaltype (some r_MUT.MUT) v_valtype) v_val_0 →
    v_g' = list_update_func v_g v_idx (fun g => { g with VALUE := v_val_1 }) →
    holds_upto (fun a => Extend_globalinst (v_g[a]!) (v_g'[a]!)) v_g.length := by
```
[`table_set_table_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1299)
```lean
theorem table_set_table_extension (v_tbs v_tbs' : List tableinst) (v_idx : Nat) (tbt : tabletype) (tbr : List ref)
    (v_i : Nat) (v_tbr : ref) :
    Forall wf_tableinst v_tbs →
    v_idx < v_tbs.length → lookup_total v_tbs v_idx = tableinst.MKtableinst tbt tbr →
    v_tbs' = list_update_func v_tbs v_idx (fun tb => { tb with REFS := list_update_func tb.REFS v_i (fun _ => v_tbr) }) →
    holds_upto (fun a => Extend_tableinst (v_tbs[a]!) (v_tbs'[a]!)) v_tbs.length := by
```
[`table_grow_table_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1346)
```lean
theorem table_grow_table_extension (v_tbs v_tbs' : List tableinst) (v_idx : Nat) (j : Option uN) (r : ref)
    (rt : reftype) (nn : Nat) (tbr : List ref) :
    Forall wf_tableinst v_tbs → Forall wf_tableinst v_tbs' →
    v_idx < v_tbs.length →
    lookup_total v_tbs v_idx = tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN tbr.length) j) rt) tbr →
    v_tbs' = list_update_func v_tbs v_idx (fun _ =>
      tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (tbr.length + nn)) j) rt)
        (tbr ++ List.replicate nn r)) →
    holds_upto (fun a => Extend_tableinst (v_tbs[a]!) (v_tbs'[a]!)) v_tbs.length := by
```
[`store_none_mem_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1232)
```lean
theorem store_none_mem_extension (v_ms v_ms' : List meminst) (v_idx : Nat) (v_mt : memtype) (b_lst : List byte)
    (v_l v_n_len : Nat) (v_nb : List byte) :
    Forall wf_byte v_nb → Forall wf_meminst v_ms →
    v_idx < v_ms.length → lookup_total v_ms v_idx = meminst.MKmeminst v_mt b_lst →
    v_ms' = list_update_func v_ms v_idx (fun m => { m with BYTES := list_slice_update m.BYTES v_l v_n_len v_nb }) →
    holds_upto (fun a => Extend_meminst (v_ms[a]!) (v_ms'[a]!)) v_ms.length := by
```
[`memory_grow_mem_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1267)
```lean
theorem memory_grow_mem_extension (v_ms v_ms' : List meminst) (v_idx : Nat) (b_lst : List byte)
    (v_i v_n : Nat) (v_j : Option Nat) :
    Forall wf_meminst v_ms → Forall wf_meminst v_ms' →
    v_idx < v_ms.length →
    lookup_total v_ms v_idx = meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN v_i) (v_j.map uN.mk_uN))) b_lst →
    Forall (fun j => v_i + v_n ≤ j) v_j.toList →
    v_ms' = list_update_func v_ms v_idx (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (v_i + v_n)) (v_j.map uN.mk_uN)))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))) →
    holds_upto (fun a => Extend_meminst (v_ms[a]!) (v_ms'[a]!)) v_ms.length := by
```
[`elem_drop_elem_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1380)
```lean
theorem elem_drop_elem_extension (es es' : List eleminst) (idx : Nat) :
    idx < es.length → es' = list_update_func es idx (fun e => { e with REFS := [] }) →
    holds_upto (fun a => Extend_eleminst (es[a]!) (es'[a]!)) es.length := by
```
[`data_drop_data_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1399)
```lean
theorem data_drop_data_extension (ds ds' : List datainst) (idx : Nat) :
    Forall wf_datainst ds → idx < ds.length → ds' = list_update_func ds idx (fun _ => datainst.MKdatainst []) →
    holds_upto (fun a => Extend_datainst (ds[a]!) (ds'[a]!)) ds.length := by
```
[`Extend_store_globalinsts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1809)
```lean
theorem Extend_store_globalinsts (s s' : store) (vs : List globalinst) (ts : List globaltype) :
    Extend_store s s' → Forall₂ (fun v t => Globalinst_ok s v t) vs ts →
    Forall₂ (fun v t => Globalinst_ok s' v t) vs ts :=
```
[`Extend_store_datainsts₂`](../../../../../src/test-lean-claude/TypePreservation.lean#L367)
```lean
theorem Extend_store_datainsts₂ (s s' : store) (ds : List datainst) (dts : List datatype) :
    Extend_store s s' → Forall₂ (fun v t => Datainst_ok s v t) ds dts →
    Forall₂ (fun v t => Datainst_ok s' v t) ds dts := by
```
[`Extend_store_vals`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1171)
```lean
theorem Extend_store_vals (v_S v_S' : store) (v_t : List valtype) (v_val : List val) :
    Extend_store v_S v_S' → Vals_ok v_S v_val v_t → Vals_ok v_S' v_val v_t := by
```
[`Extend_store_ais`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1875)
```lean
theorem Extend_store_ais (s s' : store) (c : context) (ais : List admininstr) (ft : functype) :
    Extend_store s s' → Store_ok s → Store_ok s' → Instrs_ok2 s c ais ft → Instrs_ok2 s' c ais ft := by
```
[`Extend_store_exts`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1659)
```lean
theorem Extend_store_exts (v_S v_S' : store) (v_exportinst : List exportinst) :
    Extend_store v_S v_S' → Forall (Exportinst_ok v_S) v_exportinst → Forall (Exportinst_ok v_S') v_exportinst := by
```
[`Extend_store_datainst_ext`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1698)
```lean
theorem Extend_store_datainst_ext (v_S v_S' : store) (d d' : datainst) (t : datatype) :
    Extend_store v_S v_S' → Extend_datainst d d' → Datainst_ok v_S d t →
    Datainst_ok v_S' d' t := by
```
[`Extend_store_eleminst_ext`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1683)
```lean
theorem Extend_store_eleminst_ext (v_S v_S' : store) (e e' : eleminst) (t : elemtype) :
    Extend_store v_S v_S' → Extend_eleminst e e' → Eleminst_ok v_S e t → Eleminst_ok v_S' e' t := by
```
[`addrss_store_globals_extension`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1611)
```lean
theorem addrss_store_globals_extension (v_S v_S' : store) (v_addrs : List Nat) (tcs : List globaltype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.GLOBAL a) (externtype.GLOBAL t)) v_addrs tcs →
    holds_upto (fun a => a < v_S'.GLOBALS.length) v_S.GLOBALS.length →
    holds_upto (fun a => Extend_globalinst (v_S.GLOBALS[a]!) (v_S'.GLOBALS[a]!)) v_S.GLOBALS.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.GLOBAL a) (externtype.GLOBAL t)) v_addrs tcs :=
```
[`Extend_store_wf_store'`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1127)
```lean
theorem Extend_store_wf_store' (s s' : store) : Extend_store s s' → wf_store s' := by
```

(The other per-component lemmas have the same shape as the representatives shown.)

</details>

## 9.7 Well-formedness plumbing

Syntactic side conditions (primer §0.4). Almost every typing rule asks for some of these, so they appear everywhere but carry no deep content.

| Lemma | Meaning |
|---|---|
| [`wf_config_ais`](../../../../../src/test-lean-claude/TypePreservation.lean#L863), [`wf_config_wf_frame`](../../../../../src/test-lean-claude/TypePreservation.lean#L874) | A well-formed configuration's instructions, and its frame, are well-formed. |
| [`wf_const_num`](../../../../../src/test-lean-claude/TypePreservation.lean#L878), [`wf_vconst_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L1335), [`wf_num_Inn_proj`](../../../../../src/test-lean-claude/TypePreservation.lean#L1323) | A well-formed `CONST`/`VCONST` carries a well-formed payload of the right width. |
| [`wf_admininstr_instr`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1545), [`Val_ok_wf_val`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1938) | Lifting a plain instruction preserves well-formedness (both directions); a well-typed value is well-formed. |
| [`wf_context_app`](../../../../../src/test-lean-claude/TypePreservation.lean#L72), [`wf_context_tab`](../../../../../src/test-lean-claude/TypePreservation.lean#L87), [`wf_context_mem`](../../../../../src/test-lean-claude/TypePreservation.lean#L95), [`wf_context_label_only`](../../../../../src/test-lean-claude/TypePreservation.lean#L882), [`wf_context_return_only`](../../../../../src/test-lean-claude/TypePreservation.lean#L889) | Context well-formedness: closed under `++`; table and memory types read out of it are well-formed; the small label-only and return-only contexts are well-formed. |
| [`Step_pure_is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L14076), [`Step_read_is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L16034), [`Step_is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L16045) | The reduct of a step is well-formed. `Step_read_is_wf` is `sorry` and false in one corner case (file `08` §8.11). |
| [`nbytes__is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L4210), [`ibytes__is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L4182), [`vbytes__is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L4224), [`wrap___is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L2868) | Numeric/byte-encoding primitives return well-formed results. `sorry`: the primitives are `opaque` (primer §0.4). |

<details>
<summary>Exact statements (9.7)</summary>

[`wf_config_ais`](../../../../../src/test-lean-claude/TypePreservation.lean#L863)
```lean
theorem wf_config_ais {z : state} {ais : List admininstr} (h : wf_config (config.mk_config z ais)) :
    Forall wf_admininstr ais := by
```
[`wf_config_wf_frame`](../../../../../src/test-lean-claude/TypePreservation.lean#L874)
```lean
theorem wf_config_wf_frame {s : store} {f : frame} {ais : List admininstr}
    (h : wf_config (config.mk_config (state.mk_state s f) ais)) : wf_frame f := by
```
[`wf_const_num`](../../../../../src/test-lean-claude/TypePreservation.lean#L878)
```lean
theorem wf_const_num {nt : numtype} {c : num_} (h : wf_admininstr (admininstr.CONST nt c)) : wf_num_ nt c := by
```
[`wf_vconst_parts`](../../../../../src/test-lean-claude/TypePreservation.lean#L1335)
```lean
theorem wf_vconst_parts {vt : vectype} {c : vec_} (h : wf_admininstr (admininstr.VCONST vt c)) :
    size (valtype_vectype vt) ≠ none ∧ wf_uN (Option.get! (size (valtype_vectype vt))) c := by
```
[`wf_num_Inn_proj`](../../../../../src/test-lean-claude/TypePreservation.lean#L1323)
```lean
theorem wf_num_Inn_proj (v_Inn : Inn) (c : num_) :
    wf_num_ (numtype_Inn v_Inn) c → proj_num__0 c ≠ none →
    wf_uN (Option.get! (size (valtype_Inn v_Inn))) (Option.get! (proj_num__0 c)) := by
```
[`wf_admininstr_instr`](../../../../../src/test-lean-claude/TypingLemmas.lean#L1545)
```lean
theorem wf_admininstr_instr (i : instr) : wf_instr i ↔ wf_admininstr (admininstr_instr i) := by
```
[`Val_ok_wf_val`](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1938)
```lean
theorem Val_ok_wf_val (s : store) (v : val) (t : valtype) : Val_ok s v t → wf_val v := by
```
[`wf_context_app`](../../../../../src/test-lean-claude/TypePreservation.lean#L72)
```lean
theorem wf_context_app (C C' : context) : wf_context C → wf_context C' → wf_context (C ++ C') := by
```
[`wf_context_tab`](../../../../../src/test-lean-claude/TypePreservation.lean#L87)
```lean
theorem wf_context_tab (n : Nat) (C : context) :
    n < C.TABLES.length → wf_context C → wf_tabletype (C.TABLES[n]!) := by
```
[`wf_context_mem`](../../../../../src/test-lean-claude/TypePreservation.lean#L95)
```lean
theorem wf_context_mem (n : Nat) (C : context) :
    n < C.MEMS.length → wf_context C → wf_memtype (C.MEMS[n]!) := by
```
[`wf_context_label_only`](../../../../../src/test-lean-claude/TypePreservation.lean#L882)
```lean
theorem wf_context_label_only (t : resulttype) :
    wf_context ({
      TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
      LOCALS := [], LABELS := [t], RETURN := none } : context) :=
```
[`wf_context_return_only`](../../../../../src/test-lean-claude/TypePreservation.lean#L889)
```lean
theorem wf_context_return_only (t : resulttype) :
    wf_context ({
      TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
      LOCALS := [], LABELS := [], RETURN := some t } : context) :=
```
[`Step_pure_is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L14076)
```lean
theorem Step_pure_is_wf (var_0 : List admininstr) (var_1 : List admininstr) :
  Forall (fun (var_0_elem : admininstr) => wf_admininstr var_0_elem) var_0 →
  Step_pure var_0 var_1 →
  Forall (fun (var_1_elem : admininstr) => wf_admininstr var_1_elem) var_1 := by
```
[`Step_read_is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L16034)
```lean
theorem Step_read_is_wf (z : state) (admininstr_lst : List admininstr) (var_1 : List admininstr) :
  wf_config (config.mk_config z admininstr_lst) →
  Store_ok (fun_store z) →
  Step_read (config.mk_config z admininstr_lst) var_1 →
  Forall (fun (var_1_elem : admininstr) => wf_admininstr var_1_elem) var_1 :=
```
[`Step_is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L16045)
```lean
theorem Step_is_wf (z : state) (admininstr_lst : List admininstr) (var_1 : config) :
  wf_config (config.mk_config z admininstr_lst) →
  Store_ok (fun_store z) →
  Step (config.mk_config z admininstr_lst) var_1 →
  wf_config var_1 := by
```
[`nbytes__is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L4210)
```lean
theorem nbytes__is_wf (v_numtype : numtype) (v_num_ : num_) (ret_val_lst : List byte) :
  wf_num_ v_numtype v_num_ →
  ret_val_lst = (nbytes_ v_numtype v_num_) →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
```
[`ibytes__is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L4182)
```lean
theorem ibytes__is_wf (v_N : N) (v_iN : iN) (ret_val_lst : List byte) :
  wf_uN v_N v_iN →
  ret_val_lst = (ibytes_ v_N v_iN) →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
```
[`vbytes__is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L4224)
```lean
theorem vbytes__is_wf (v_vectype : vectype) (v_vec_ : vec_) (ret_val_lst : List byte) :
  (size (valtype_vectype v_vectype)) ≠ none →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
  ret_val_lst = (vbytes_ v_vectype v_vec_) →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
```
[`wrap___is_wf`](../../../../../src/test-lean-claude/wasm2.0.lean#L2868)
```lean
theorem wrap___is_wf (v_M : M) (v_N : N) (v_iN : iN) (ret_val : iN) :
  wf_uN v_M v_iN →
  ret_val = (wrap__ v_M v_N v_iN) →
  wf_uN v_N ret_val :=
```

</details>

---
*Back to the [README](README.md).*

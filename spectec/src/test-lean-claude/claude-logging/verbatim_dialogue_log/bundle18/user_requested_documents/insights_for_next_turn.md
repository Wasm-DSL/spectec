# Insights for the next turn (written end of bundle18)

Written for: the next Claude session working on the Lean port (possibly a different session
or a less capable model). Read this before touching any `.lean` file. It is deliberately
verbose. Everything here was true when written (2026-10-03, end of bundle18); verify names
and line numbers before relying on them.

---

## 0. Standing rules (unchanged, still binding)

- **Never modify anything outside `spectec/src/test-lean-claude`.** Reading outside is fine.
  After every batch of edits, run from the repo root `/home/zhengyew/spectec`:
  `bash spectec/src/test-lean-claude/claude-logging/safety-checks/check.sh`,
  then diff the lines *not* mentioning `test-lean-claude` against the turn's baseline:
  `diff <(grep -v test-lean-claude BASELINE | grep -v '^=== Safety') <(grep -v test-lean-claude NEW | grep -v '^=== Safety')`.
  Bundle18's baseline was `safety-checks/check-20261003T091646Z.txt`.
  `spectec/src/backend-lean/backend.ml` and `lean_builder.ml` show as modified: those are the
  **user's own** changes, present in the baseline. Leave them alone.
- `wasm2.0.lean` is generated. Do not edit it, even though it sits inside the target folder.
- Logging: every exchange gets `claude-logging/verbatim_dialogue_log/bundleN/` with
  `prompt_N.md` (verbatim, mid-turn messages appended), `response_N.md` (verbatim final
  reply), `response_N_modelinfo.md`. Never edit previous bundles. Deliverables go in
  `bundleN/user_requested_documents/`. Also update the living
  `claude-logging/for-claude/NOTES.md`, `for-claude/is_wf_theorems.md` and
  `for-humans/SUMMARY.md`.
- Signatures must match Rocq (intended deviations are documented in doc comments). Proof
  method is free. Write signatures first (body `sorry`), then fill bodies. Imitate the Rocq
  body first. If that fails, understand its intuition and prove it the Lean way.
- If something significant comes up (unprovable statement, false lemma, spec bug), stop and
  report rather than spinning.
- Ignore `TODO FROM USER` markers.
- Run `lake build` (or `lake build TypePreservation`, which imports everything) frequently.
  A full rebuild of `TypePreservation` takes about 2 to 4 minutes.
- Memory note from another session: ask before editing `test-lean-claude`. The explicit task
  prompts of bundles 17 and 18 were treated as the go-ahead.

## 1. State at the end of bundle18

`lake build` is clean (3004 jobs). `sorry` count per file (declarations):

| File | sorries | What they are |
|---|---|---|
| `HelperLemmas.lean` | 15 | Dead cluster (rule 1, "mark for deletion"): `list_update_func_split`, `list_update_func_split_strong`, `Forall2_nth`, `Forall2_lookup`, `lookup_list_update_func`, `Forall2_forall2`, `Forall2_forall2weak{,2,3,4}`, `Forall2_list_update_func{,2}`, `Forall2_list_update{,2}`, `Forall2_list_update_both`. Nothing on the preservation path uses them. They are Rocq lemmas phrased over the inductive `Forall2`, and most are **false** for the zip-based `Forall₂` without a length hypothesis. Recommend deleting them or adding `hlen`. |
| `Subtyping.lean` | 0 | |
| `TypingLemmas.lean` | 0 | |
| `TypePreservationPure.lean` | 0 | |
| `ExtensionLemmas.lean` | 1 | `Val_ok_store` (dead, rule 1; no current Rocq counterpart). |
| `TypePreservation.lean` | 2 | `t_read_preservation` (**the remaining real work**, see §3) and `rat_to_nat_natCast` (**unprovable**, see §2.1). |

Transitive `sorry` dependencies (computed with the meta-program in §6):

- `store_extension_reduce`: `rat_to_nat_natCast`, plus the generated `ibytes__is_wf`,
  `nbytes__is_wf`, `vbytes__is_wf`, `wrap___is_wf`. **It no longer depends on `Step_is_wf`.**
- `t_preservation_type`: `Step_is_wf`, `Step_pure_is_wf`, `t_read_preservation`.
- `t_pure_preservation`: `Step_pure_is_wf` only. That is `Qed` upstream, so this is fully
  proved modulo a generated theorem that is true.
- `t_preservation` (top-level): `Step_is_wf`, `Step_pure_is_wf`, `rat_to_nat_natCast`,
  `t_read_preservation`, and the four byte/`wrap` `_is_wf`.

`#print axioms TLC.t_preservation` lists `[propext, sorryAx, Classical.choice, Quot.sound]`.
No custom `axiom` (like `HelperLemmas.nbytes_len`) is on the preservation path.

## 2. Blocking issues (report-worthy, already reported to the user in bundle18)

### 2.1 `rat_to_nat` is opaque, so the `memory.grow` case is unprovable

`wasm2.0.lean:9` declares `opaque rat_to_nat (r : Rat) : Nat`. Nothing about its values can
be proved. `$growmemory` stores the new page count as
`rat_to_nat (|b*|/64Ki + n)`, so `Extend_meminst` (needs `old ≤ new`) and `Meminst_ok` (needs
`|b*'| = new * 64Ki`) cannot be established.

What bundle18 did: isolated the gap into one lemma,
`TypePreservation.lean` `theorem rat_to_nat_natCast (n : Nat) : rat_to_nat (n : Rat) = n := sorry`,
with a doc comment explaining it. `memory_grow_store_ok` (the memory-grow case of
`store_extension_reduce`) is fully proved from it. The statement is consistent: it holds for
the intended definition `fun r => r.floor.toNat`.

**Fix (user's call, backend side):** generate `rat_to_nat` as a real function, e.g.
`def rat_to_nat (r : Rat) : Nat := r.floor.toNat`. Then `rat_to_nat_natCast` is a one-liner,
roughly `simp [rat_to_nat, Rat.floor_natCast]` (check the exact Mathlib name). The
`store_*`/`load_*` rules also mention `rat_to_nat (size/8)`, but `with_mem` ignores its
length argument (`splice` uses only the payload), so stores don't care. The loads'
`rat_to_nat` sits inside `Step_read` premises, which only matters for progress.

### 2.2 `t_read_preservation` / `t_preservation` are FALSE in one corner case

This is an upstream spec issue that affects Rocq too; it was first noted in bundle17.
`memory_fill_succ`, `memory_copy_le` and `memory_init_succ` push `CONST I32 (i + 1)` (and
`table_*` analogues push `j + 1` / `i + 1`). Take a memory of exactly `2^16` pages
(`2^32` bytes; allowed, since `Memtype_ok` caps at `2^16`), `i = 2^32 - 1` and `n = 1`.
Then `i + n ≤ |mem|` holds, so the `succ` rule fires and pushes `CONST I32 (2^32)`.
`wf_uN 32 (mk_uN 2^32)` is false, so the reduct is not well-formed and not typable
(`Instr_ok.const` needs a well-formed constant). `Config_ok` of the pre-state holds, and of
the post-state fails.

Consequences:
- The generated `Step_read_is_wf` and `Step_is_wf` (both `sorry` in `wasm2.0.lean`) are
  **false**. In Rocq, `Step_read_is_wf` is `Admitted`, with the author noting these exact
  cases.
- `t_read_preservation` (as stated, identical to Rocq) is false in that corner case. **Any
  proof of it must use a false lemma.** The honest choice, and what Rocq does, is to take the
  reduct's well-formedness from `Step_read_is_wf _ _ hwfc hstep`. Do that; do not try to
  derive wf of `CONST I32 (i+1)` yourself.
- The table versions do **not** have this problem in practice: table sizes are bounded by
  `Limits_ok _ (2^32 - 1)`, so `i + n ≤ |tab| ≤ 2^32 - 1` gives `i + 1 ≤ 2^32 - 1`. But
  simply using `Step_read_is_wf` for every case is fine and much shorter.
- Fix options (user's call): add a side condition to the spec's `succ` rules, or make the
  i32 arithmetic wrap. This has been reported. Do not "fix" it in Lean.

### 2.3 Earlier issues, now resolved

- **`with_mem` not length-preserving.** Bundle17's blocker. Resolved by the user's
  regeneration with `splice`. Verified in bundle18: `splice` is clamped and
  length-preserving, and `HelperLemmas.splice_eq_list_slice_update` proves
  `splice l b i = list_slice_update l i b.length b`.
- **`br_table_ge`.** The user removed the extra premise in bundle18. The current statement
  matches Rocq and is proved.

## 3. How to do `t_read_preservation` (the remaining proof)

Signature (`TypePreservation.lean`, around line 915; matches Rocq `type_preservation.v:1661`):

```lean
theorem t_read_preservation (v_s : store) (v_f : frame) (v_ais : List admininstr)
    (v_ais' : List admininstr) (v_C v_C' : context) (t1s t2s : List valtype) :
    wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →
    Step_read (config.mk_config (state.mk_state v_s v_f) v_ais) v_ais' →
    Store_ok v_s → Moduleinst_ok v_s v_f.MODULE v_C →
    Forall₂ (fun v_t v_val => Val_ok v_s v_val v_t) v_C'.LOCALS v_f.LOCALS → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s) → Instrs_ok2 v_s v_C' v_ais' (mkFunctype t1s t2s)
```

Note the locals hypothesis is a bare `Forall₂` with **no length**. The caller,
`t_preservation_type_aux`'s `read` case, passes `hvals.2` from `Vals_ok`. If a case needs
the length (`local_get` does), either change the caller to pass all of `Vals_ok` (a
signature deviation; document it like `funcinst_same`) or get `x < C'.LOCALS.length` from
typing and use `Forall₂` membership via `mem_zip_getElem!`, which needs both lengths. The
second route is awkward. The cleaner fix is to deviate and take `Vals_ok` (that is, add
`hlen`), exactly as was done for `wf_tableinsts_preserves` and friends. Ask or document.

### 3.1 Recommended structure

1. `intro hwfc hstep hsok hmi hlocs him htype`.
2. `have hwf' := Step_read_is_wf _ _ hwfc hstep` gives `Forall wf_admininstr v_ais'` (§2.2).
3. `obtain ⟨hwfC', hwfS, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype`.
4. Case split on `hstep`. `Step_read` is indexed by a config, so either use `cases hstep`
   (the config index `config.mk_config (state.mk_state v_s v_f) v_ais` is a constructor
   application, so `cases` unifies it; the fields `z`, … get substituted), or generalize as
   in `t_preservation_type_aux` / `store_extension_reduce_aux`. `cases` is fine here: no
   induction is needed, since `Step_read` is not recursive.
5. Group the 47 constructors:
   - **15 traps** (`call_indirect_trap`, `table_get_trap`, `table_fill_trap`,
     `table_copy_trap`, `table_init_trap`, `load_num_trap`, `load_pack_trap`, `vload_oob`,
     `vload_shape_oob`, `vload_splat_oob`, `vload_zero_oob`, `vload_lane_oob`,
     `memory_fill_trap`, `memory_copy_trap`, `memory_init_trap`):
     `exact construct_ais_trap _ _ _ hwfC' hwfS`.
   - **6 zeros** (`table_fill_zero`, `table_copy_zero`, `table_init_zero`,
     `memory_fill_zero`, `memory_copy_zero`, `memory_init_zero`): the reduct is `[]`. Use
     `(ais_empty_typing _ _ t1s t2s).mpr ⟨hwfC', hwfS, instrtype_sub_empty _ _ H⟩`, where
     `H : instrtype_sub (mkFunctype [] []) (mkFunctype t1s t2s)` comes from
     `ais_args3_typing _ _ a b c op [] t1s t2s inv_a inv_b inv_c inv_op htype`. The
     operator inversions (`inv_table_fill` etc.) need writing, following the pattern of
     `inv_table_set` in `TypePreservation.lean` (§4 has the template). `ais_args3_typing`
     already exists.
   - **Single-constant results** (`table_size`, `memory_size`, `load_num_val`,
     `load_pack_val`): the result is `[CONST nt c]`. Typing of the original gives
     `instrtype_sub (mkFunctype [] [nt]) (mkFunctype t1s t2s)` (via `ais_args1_typing` /
     `ais_single_typing_inversion`). Wf of `c` comes from `hwf'`
     (`wf_const_num (hwf' _ (by simp))`). Build the result with `const_I32_result`, or for
     general `nt` with
     `construct_ais_subtyping … (construct_ais_typing_single … (Instr_ok2.plain … (Instr_ok.const …)))`.
     Look at `construct_ai_const_I32` (`TypingLemmas.lean:1639`) and generalize it to any
     `nt`.
   - **Vector loads** (`vload_val`, `vload_lane_val`): `Step_read__vload_preserves` and
     `Step_read__vload_lane_preserves` already exist (`TypePreservation.lean`, around line
     606 and 619). Use them with the `VCONST` wf from `hwf'`. `vload_shape_val`,
     `vload_splat_val` and `vload_zero_val` are the same shape: one `CONST I32` operand and a
     `VLOAD` with a different `vloadop_`. `ais_vload_typing_inversion` is stated for a
     generic `vlo : Option vloadop_`, so `Step_read__vload_preserves` should cover all four
     plain-`VLOAD` value cases (check its signature: it takes `vlo` generically).
   - **`ref_func`**: typing `REF_FUNC x` gives `x < C'.FUNCS.length`. The address is
     `f.MODULE.FUNCS[x]!`. `minst_invert_funcs` + `Forall2_nth_of_length` (length from
     `Moduleinst_ok_lengths …|>.2.1` + `him.2.1`) give the `Externaddr_ok`. Build with
     `Instr_ok2.ref` / `Ref_ok.func`.
   - **`local_get`**: the result is `[admininstr_val (fun_local z x)]`, where
     `fun_local (mk_state s f) x = f.LOCALS[x]!`. Typing gives
     `C'.LOCALS[x]? = some t` (principal typing `LOCAL_GET`). You need
     `Val_ok s (f.LOCALS[x]!) t`, from the locals `Forall₂` at index `x`; that needs the
     length (see the note above). Then `construct_ai_val`.
   - **`global_get`**: result `[admininstr_val ((fun_global z x).VALUE)]`. The existing
     `ExtensionLemmas.lookup_global` gives exactly
     `Val_ok v_S (lookup_total v_S.GLOBALS (lookup_total minst.GLOBALS v_a)).VALUE v_vt`.
     Use it with `construct_ai_val`.
   - **`table_get_val`**: result `[admininstr_ref (tab.REFS[i]!)]`. You need
     `Ref_ok s (REFS[i]!) rt`. Get the table from `minst_invert_tables` +
     `externtype_table_sub_inv` (new in bundle18), its `Tableinst_ok` from
     `Store_ok_parts … h6` at the address, then `tableinst_ok_invert` gives
     `Forall (Ref_ok s · rt) refs`, and index with `getElem!_pos` + `List.getElem_mem`.
     Copy the shape of `table_grow_store_ok`, which does all of this.
   - **`call`**: result `[CALL_ADDR (fun_funcaddr z)[x]!]`. Typing `CALL x` gives
     `C'.FUNCS[x]? = some ft`. `minst_invert_funcs` gives the `Externaddr_ok`, and
     `externtype_func_eq` gives equal types. Build with `Instr_ok2.call_addr` (check the
     constructor name in `wasm2.0.lean`, `inductive Instr_ok2`).
   - **`call_indirect_call`**: as `call`, plus the `CONST I32 i` operand
     (`ais_args1_typing`-style composition). The function type check uses
     `fun_type z y = funcinst.TYPE`, and `minst_invert_functypes` gives
     `C'.TYPES = minst.TYPES`.
   - **`block`, `loop`**: `vals ++ [BLOCK bt instrs]` becomes
     `[LABEL_ n [] (vals ++ instrs)]` (loop: the label continuation is `[LOOP bt instrs]`).
     Use `ais_composition_typing` to split, `ais_vals_typing_inversion`,
     `ais_single_typing_inversion` + principal typing of `BLOCK`
     (`Blocktype_ok` + `Instrs_ok` of the body), `bt_inversion` (exists,
     `ExtensionLemmas.lean:838`) to identify `t_1_lst`/`t_2_lst`, then build `Instr_ok2.label`
     with the body typed by `construct_ais_compose (construct_ais_vals …)
     (construct_instrs_from_ais …)`. `construct_instrs_from_ais` was added in bundle17
     (`TypingLemmas.lean`). The context in the label is
     `{C' with LABELS := (list.mk_list t2) :: C'.LABELS}` (block) or `… t1 …` (loop).
     Compare the `ctxt_label` case of `t_preservation_type_aux`, which deconstructs
     `Instr_ok2.label` the other way.
   - **`call_addr`** (the hardest, about 120 Rocq lines, 1838-1958): the result is
     `[FRAME_ n f [LABEL_ n [] instrs]]` with `f = {LOCALS := vals ++ defaults, MODULE := mm}`.
     You must build `Frame_ok` (needs `Moduleinst_ok s mm C0` for the callee's module, from
     `Store_ok` → `Funcinst_ok` → `Func_ok`/`Moduleinst_ok`; see `funcinst_same` /
     `funcinst_ok_invert` in `ExtensionLemmas.lean`) and `Expr_ok2` of the label body in
     context `prepend_return (prepend_local C0 (t1 ++ t_lst)) t2`. `prepend_local` and
     `prepend_return` were added in bundle17 (`HelperLemmas.lean`, literal-`++` forms that
     match `Frame_ok`'s conclusion). Default values: `Val_ok s (Option.get! (default_ t)) t`
     for each local type with `default_ t ≠ none` needs a small lemma (Rocq inlines it at
     1897-1915). Do this case last.
   - **Sequence cases** (`table_fill_succ`, `table_copy_le`, `table_copy_gt`,
     `table_init_succ`, `memory_fill_succ`, `memory_copy_le`, `memory_copy_gt`,
     `memory_init_succ`): the original `[c1, c2, c3, OP]` has type
     `t1s → t2s` with `instrtype_sub (mkFunctype [] []) (mkFunctype t1s t2s)` (via
     `ais_args3_typing`). Type the reduct at `[] → []` by composing small pieces with
     `construct_ais_compose`, then `construct_ais_subtyping`. Pieces:
     `CONST I32 k : [] → [I32]` (`construct_ai_const_I32`, wf from `hwf'`),
     `val v : [] → [t]` (`construct_ai_val`, `Val_ok` from inverting the original typing via
     `ais_single_val_typing_inversion`), and `TABLE_SET x : [I32, ref rt] → []` /
     `STORE I32 (some 8) memarg0 : [I32, I32] → []` / `LOAD … : [I32] → [I32]` /
     `TABLE_GET y : [I32] → [ref rt]` via `Instr_ok2.plain (Instr_ok.… )` (or the `instr`
     typing constructors; check `inductive Instr_ok` in `wasm2.0.lean`). To grow the stack
     under a prefix you need a frame or weakening lemma ("typing at `ts → ts'` gives typing
     at `pre ++ ts → pre ++ ts'`"). Look for `instr_subtyping_weaken2` /
     `instrtype_sub_add_same` in `Subtyping.lean`, and `Instr_ok2`'s own frame-style
     constructor, if any. **Simplest trick:** type each piece at a principal type
     `[] → [t]` or `[ts] → []`, then use `construct_ais_subtyping` with an `instrtype_sub`
     that adds a common prefix. `instrtype_sub (mkFunctype a b) (mkFunctype (p ++ a) (p ++ b))`
     holds by definition (`instrtype_sub` is "exists ts_sub ts …", so pick `ts_sub = ts = p`).
     Write that lemma once (`instrtype_sub_prefix`) and the sequence cases become mechanical.
     For `memory_*` you need `0 < C'.MEMS.length` (`ais_store_mems_inv`, or the
     `MEMORY_FILL` principal typing, which has `C.MEMS[0]? = some mt`). For `TABLE_SET x` in
     `table_fill_succ` you need the table type of `x`, from `TABLE_FILL x`'s principal
     typing.

### 3.2 Expected size

About 600 to 1000 Lean lines if done with good helper lemmas (Rocq: about 1460 lines).
Recommended order: traps and zeros first (cheap, 21 cases), then constants and `*_get`, then
loads, then sequences (write `instrtype_sub_prefix` first), then block/loop, then call /
call_indirect, then call_addr. Leave a `sorry` per unfinished case. Lean's `cases` lets you
close finished ones and `all_goals sorry` the rest, so progress is incremental and the
build stays green.

## 4. Lean techniques that worked in bundle18 (copy these patterns)

- **Auto-promoted parameters.** Lean 4 turns an inductive's leading indices into parameters
  when every constructor uses them uniformly (same variable, same position). Those take
  **no name slot** in `cases h with | ctor a b c`. Seen for:
  - `Moduleinst_ok`'s `s`: 14 names, then the premises.
  - `fun_growtable`'s first 3 indices: `| fun_growtable_case_0 ti' i j_opt rt r'_lst i' hold hi' hj hti' hwfold hwfnew`, and `| fun_growtable_case_1 hnot`.
  - `fun_growmemory`'s first 2: `| fun_growmemory_case_0 mi' i j_opt b_lst i' hold hi' hj h216 hmi' hwfold hwfnew`.
  - `wf_num_`'s numtype: `| num__case_0 v_Inn x hsz hwf heq`, `| num__case_1 v_Fnn x hwf heq`.

  If you get "Too many variable names provided", this is why: drop the leading names.
- **Moduleinst_ok premise order** (after the 14 list params): 1 `Forall Functype_ok`,
  2 globals-len, 3 globals-`Forall₂`, 4 funcs-len, 5 funcs-`Forall₂`, 6 mems-len,
  7 mems-`Forall₂`, 8 tables-len, 9 tables-`Forall₂`, 10 exports, 11 datas-len,
  12 datas-`<`, 13 datas-`Forall₂`, 14 elems-len, 15 elems-`<`, 16 elems-`Forall₂`, …
  The new `Moduleinst_ok_lengths` (`TypePreservation.lean`) packages all six length facts:
  `.1` GLOBALS, `.2.1` FUNCS, `.2.2.1` MEMS, `.2.2.2.1` TABLES, `.2.2.2.2.1` DATAS,
  `.2.2.2.2.2` ELEMS.
- **`inst_match C C'` components:** `.1` TYPES, `.2.1` FUNCS, `.2.2.1` GLOBALS,
  `.2.2.2.1` TABLES, `.2.2.2.2.1` MEMS, `.2.2.2.2.2.1` ELEMS, `.2.2.2.2.2.2` DATAS.
  "Context length = instance length" is
  `rw [← him.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.1` (tables).
- **Store lookups at an instance address:**
  `obtain ⟨tbr, tbt', hta, hlk, hsub⟩ := Forall2_nth_of_length f.MODULE.TABLES C'.TABLES (minst_invert_tables s f.MODULE C C' hmi him) hlenT (proj_uN_0 x) (by omega)`.
  The `getElem?` fact from principal typing becomes `k < len ∧ l[k]! = a` with
  `getElem?_eq_some_bang` (new).
- **Generated state accessors are defeq to lookups:** `fun_table (mk_state s f) x` ≡
  `lookup_total s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!)`, so `hold.trans hlk` typechecks
  directly (used in `table_grow_store_ok`).
- **`with_*` post-states:** after `injection h2 with hz2 _`, do
  `simp only [with_global] at hz2; injection hz2 with hs _; subst hs`. For `with_mem`, add
  `splice_eq_list_slice_update` to the simp set (see `with_mem_store_ok`).
- **Store_ok plumbing (new in bundle18):** `Store_ok_parts` / `Store_ok_of_parts` take
  `Store_ok` apart and put it back over the store's own fields. `Extend_store_of_parts`
  reduces `Extend_store` to "no shorter" plus pointwise facts per component.
  `wf_store_parts`, `wf_store_with_{globals,tables,mems,elems,datas}`,
  `Extend_store_datainsts₂`, `datainsts_Forall{,₂}_of_Forall{₂,}` and `Store_ok_wf_store`
  round this out. Every store case of `store_extension_reduce` is about 30 lines with these;
  copy `elem_drop_store_ok` as the simplest template.
- **Multi-line structure-update syntax is indentation sensitive.** Write
  `{ s with` (newline) `  FIELD := …` (newline, deeper) `    …continuation }`. Writing
  `{ s with FIELD := long` and continuing on the next line at a shallower column is a parse
  error ("unexpected token '('; expected '}'").
- **`simp_all` can hit max recursion** in contexts with large hypotheses (store lemmas).
  Use targeted `simp only [Option.toList_some, List.mem_singleton] at h` plus `subst`.
- **`set x := big_term with hx`** keeps long store-update terms manageable and gives the
  equation that `*_extension` / `construct_*` lemmas want as their last premise.
- **Rat arithmetic:** Mathlib is available (imported via `HelperLemmas`'s
  `import Mathlib.Tactic`). `rw [hi', hblen]; unfold Ki; push_cast; ring` proved
  `(vn0 * (64*Ki) : Rat) / (64 * Ki) + v_n = ((vn0 + v_n : Nat) : Rat)`, and
  `exact_mod_cast` converts `Rat` inequalities on casts back to `Nat`.
- **Proving well-formedness without `Step_is_wf`:** `fun_growtable` and `fun_growmemory`
  carry `wf_tableinst` / `wf_meminst` of both the old and the new instance as premises. Use
  those rather than `Step_is_wf`, which is false (§2.2).

## 5. Things to clean up (low priority)

**Update at the end of bundle18:** the stale doc comments listed below **were fixed** at the
very end of bundle18: the headers of `TypePreservation.lean` and `TypePreservationPure.lean`,
plus the doc comments of `t_read_preservation`, `step_moduleinst`, `t_preservation`,
`Step_pure__return_frame_preserves` and `t_pure_preservation`. The rebuild was clean. Only
the dead-sorry deletion remains.


- **Stale doc comments in `TypePreservation.lean`.**
  - The file header (lines 1 to 40) still says "3 lemmas are `Admitted`" and similar.
  - `t_read_preservation`'s doc says "`Admitted` in Rocq … SIMD gap". In current upstream it
    is `Qed`, relying on the `Admitted` `Step_read_is_wf`.
  - `step_moduleinst`'s doc says "inherits `store_extension_reduce`'s SIMD gap", which is no
    longer true.
  - `t_preservation`'s doc says "modulo the 3 transitively-Admitted lemmas".

  Rewrite these to match §1.
- **`TypePreservationPure.lean` header / `return_frame` doc** may still mention `Admitted`;
  check.
- **Delete or fix the 15 dead `HelperLemmas` sorries and `Val_ok_store`** (rule 1). Ask the
  user before deleting.
- **`construct_meminsts_grow` doc comment** was rewritten in bundle18 (it is proved). Its
  signature now takes `v_j_opt : Option uN`, as in Rocq.

## 6. Tool: transitive `sorry` dependencies (save as a scratch `.lean` file, run with `lake env lean FILE`)

```lean
import TypePreservation
open Lean Meta Elab Command

partial def sorryDeps (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut out : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let tyConsts := ci.type.getUsedConstants
      let valConsts := match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants
        | none => #[]
      if valConsts.contains ``sorryAx || tyConsts.contains ``sorryAx then
        out := out.push n
      for c in tyConsts ++ valConsts do
        if !visited.contains c then stack := stack.push c
  return out

elab "#sorry_deps " id:ident : command => do
  let deps := sorryDeps (← getEnv) id.getId
  logInfo m!"{id.getId} uses sorry via {deps.size} declarations: {deps.qsort (·.toString < ·.toString)}"

#sorry_deps TLC.t_preservation
```

Put the file in the session scratchpad, **not** in the repo. Run it from
`spectec/src/test-lean-claude` with `timeout 600 lake env lean /path/to/file.lean`.

## 7. After preservation

Progress (`type_progress.v`) is next. Bundle16's `proof_prioritization_v6.md` lists the 12
progress-only axioms. Nothing on progress was touched in bundles 17 and 18.

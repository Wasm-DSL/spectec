# Proof prioritization — update v6 (bundle16)

Written for: a future Claude session (primary audience) and the user.
Supersedes `bundle15/user_requested_documents/proof_prioritization_v5.md`
(kept untouched). v5's 8-item plan is now **items 1-6 complete**; this document
replaces it with the much shorter remaining list.

## Direct answer to "what's left?"

**5 genuine proofs, all in `TypePreservationPure.lean`.** Everything else is
either a deliberate gap mirroring a Rocq `Admitted`, a signature defect on a
lemma upstream has dropped, or the dead `HelperLemmas` cluster.

27 `sorry`s project-wide = 5 genuine + 5 deliberate gaps + 2 bad signatures +
15 dead. (Was 83 at bundle16's start.)

## Recommended order

### 1. `Step_pure__br_table_ge_preserves` — do this one FIRST

Easiest of the five, and it is the template for the next one. Route:

- `ai_principal_typing` for `BR_TABLE ls l'` (TypingLemmas ~line 342) gives
  `∃ t1s ts t2s, ft = mkFunctype (t1s ++ ts ++ [I32]) t2s ∧ (∀ l ∈ ls, …) ∧
  (∃ r', C.LABELS[l']? = some r' ∧ Resulttype_sub (.mk_list ts) r')`.
- `ai_principal_typing` for `BR l` gives
  `∃ t1s ts t2s, ft = mkFunctype (t1s ++ ts) t2s ∧ C.LABELS[l]? = some (.mk_list ts)`.
- Copy the *shape* of the already-proved `Step_pure__br_if_preserves`
  (TypePreservationPure ~line 390): split `[CONST I32 i] ++ [BR_TABLE ls l']`
  with `ais_seq_typing_inversion`, invert `CONST`'s principal typing to pin
  `[] -> [I32]`, invert `BR_TABLE`'s, compose with `instrtype_sub_compose1`.
- Then rebuild `BR l'` via `construct_ai_maybe` + `Instr_ok.br` (note `r'` is a
  `resulttype`, so write it as `.mk_list (proj_list_0 valtype r')` using the
  already-proved `proj_identity` helper), and widen with
  `construct_ais_subtyping`.
- The `Resulttype_sub (.mk_list ts) r'` fact is what lets the `BR l'`
  derivation at `r'`'s payload type subsume the required `ts`; chain it with
  `resulttype_sub_trans`/`resulttype_sub_app` exactly as `br_if` does.
- The `v_l.length ≤ …` premise is *not needed* for the proof (it only picks
  which reduction fired); ignore it.

### 2. `Step_pure__br_table_lt_preserves`

Identical to #1 except the label comes from `∀ l ∈ ls, …` instantiated at
`ls[i]!` where `i = proj_uN_0 (Option.get! (proj_num__0 v_i))`. The `i < ls.length`
premise *is* needed here, to turn `∀ l ∈ ls` into a fact about `ls[i]!`: use
`HelperLemmas.Forall_nth'` (proved) or `getElem!_pos` + `List.getElem_mem`.
Rocq calls this one of its longest lemmas, but with #1 in hand the delta is
small.

### 3. `Step_pure__br_zero_preserves`

```lean
Instrs_ok2 v_S v_C [LABEL_ n instr' ((vals' ++ vals ++ [BR 0]) ++ ais)] ft →
vals.length = n → Instrs_ok2 v_S v_C (vals.map admininstr_val ++ instr'.map admininstr_instr) ft
```
Route: invert `LABEL_`'s principal typing (`ais_single_typing_inversion` +
`ai_principal_typing`, exactly as the already-proved
`Step_pure__label_vals_preserves` does, ~line 291) to get both
`Instrs_ok2 v_S v_C (instr'.map admininstr_instr) (mkFunctype t's ts)` and
`Instrs_ok2 v_S (prepend_label v_C (.mk_list t's)) body (mkFunctype [] ts)`.
Then `ais_composition_typing` the body three ways to isolate the
`vals.map admininstr_val` segment and the `BR 0`; `BR 0`'s principal typing plus
`HelperLemmas.lookup_label_0` (proved) pins its label payload to `t's`. Rebuild
with `construct_ais_vals'`/`construct_ais_compose`/`construct_ais_subtyping`.

### 4. `Step_pure__br_succ_preserves`

Same shape as #3 with `BR (l+1)` and `HelperLemmas.lookup_label_1` (proved)
instead of `lookup_label_0`; the outer label is *dropped* rather than entered.

### 5. `Step_pure__return_label_preserves`

Same family again; `RETURN`'s principal typing reads `C.RETURN` rather than
`C.LABELS`, and the `prepend_label` wrapper leaves `RETURN` untouched, which is
exactly why this one goes through while its `_frame_` sibling is Rocq-`Admitted`.

### Not targets (do not spend time on these)

- `t_pure_preservation`, `store_extension_reduce`, `t_read_preservation`,
  `t_preservation_type`, `Step_pure__return_frame_preserves` — all mirror Rocq
  `Admitted`s. Leave as `sorry`; the in-file doc comments explain each.
- `ExtensionLemmas.Val_ok_store`, `ExtensionLemmas.funcinst_same` — unprovable
  as stated and dropped upstream. See `extension_lemmas_triage_v2.md` for the
  exact defect in each and what the corrected statement would be. Only touch
  these if the user asks for a signature change.
- `HelperLemmas.lean`'s 15 — dead `nat→N`-refactor cluster, several unprovable
  as stated. Their usable replacements already exist
  (`Forall2_nth_of_length`, `mem_zip_modify*`, `extend_funcinst_eq`).

## After the five

The natural next project is `type_progress.v`, which is **not started** and was
previously gated on `ExtensionLemmas.lean`. That gate is now gone. It needs
`TypingLemmas` + `ExtensionLemmas` + `Subtyping` + `Axioms` and **not**
Preservation, so it is independently approachable.

# 2. `store_extension_reduce` and its engine, `store_extension_reduce_aux`

*(Previous: [01-t-preservation.md](01-t-preservation.md). Next: [03-reduce-inst-unchanged.md](03-reduce-inst-unchanged.md).)*

**Plain-English summary.** One step of execution turns the store into a *growth* of itself (§0.6 of the primer) and the new store is still well-typed. This is the half of preservation about the store component specifically, independent of whatever instructions are left to execute.

**Code (`store_extension_reduce`)** — [TypePreservation.lean:1611-1622](../../../../../src/test-lean-claude/TypePreservation.lean#L1611-L1622):
```lean
/-- Rocq `type_preservation.v:437` `store_extension_reduce`: one reduction step extends the
    store and keeps it `Store_ok`. `Qed` in Rocq. Proved here by `store_extension_reduce_aux`.
    Unlike Rocq, this does not use `Step_is_wf`. -/
theorem store_extension_reduce (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (tf : functype) :
    wf_config (config.mk_config (state.mk_state s f) ais) →
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Moduleinst_ok s f.MODULE C → Instrs_ok2 s C' ais tf → inst_match C C' → Store_ok s →
    Extend_store s s' ∧ Store_ok s' := by
  intro hwfc hstep hmi htype him hsok
  obtain ⟨⟨t1s⟩, ⟨t2s⟩⟩ := tf
  exact store_extension_reduce_aux _ _ hstep s f ais s' f' ais' C C' t1s t2s rfl rfl hwfc hmi htype him hsok
```

**Signature.** Takes a well-formed pre-config, a `Step` between the two full configs, the usual `Moduleinst_ok`/`Instrs_ok2`/`inst_match` typing package for the *pre*-state, and `Store_ok s`. Concludes `Extend_store s s' ∧ Store_ok s'` — both halves of the store invariant, for the *post*-store, in one shot. This is a thin wrapper: it just unwraps the `functype tf` into its two bare `List valtype` components (the primer's §0.3 `list` quirk) and hands everything to the `_aux` induction (primer's §0.8 pattern).

**Code (`store_extension_reduce_aux`, the actual induction)** — [TypePreservation.lean:1437-1609](../../../../../src/test-lean-claude/TypePreservation.lean#L1437-L1609):
```lean
/-- Generalized form of `store_extension_reduce` (same `remember`/`generalize dependent`
    encoding as `reduce_inst_unchanged_aux`). The context rules recurse (the congruence rules
    carry the inner configuration's `wf_config` as a premise), the store-writing rules go to the
    per-rule lemmas above, and every other rule leaves the store unchanged. -/
private theorem store_extension_reduce_aux (c1 c2 : config) (hstep : Step c1 c2) :
    ∀ (s : store) (f : frame) (ais : List admininstr) (s' : store) (f' : frame)
      (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype),
      c1 = config.mk_config (state.mk_state s f) ais →
      c2 = config.mk_config (state.mk_state s' f') ais' →
      wf_config c1 → Moduleinst_ok s f.MODULE C → Instrs_ok2 s C' ais (mkFunctype t1s t2s) →
      inst_match C C' → Store_ok s → Extend_store s s' ∧ Store_ok s' := by
  induction hstep
  case pure z ais ais' _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ hsok
    injection h1 with hz1 _
    injection h2 with hz2 _
    rw [hz1] at hz2
    injection hz2 with hs _
    subst hs
    exact ⟨Extend_store_refl (Store_ok_wf_store _ hsok), hsok⟩
  case read z ais ais' _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ hsok
    injection h1 with hz1 _
    injection h2 with hz2 _
    rw [hz1] at hz2
    injection hz2 with hs _
    subst hs
    exact ⟨Extend_store_refl (Store_ok_wf_store _ hsok), hsok⟩
  case ctxt_label z n instrs0 ais z' ais' _ hwf1 _ ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 hais2
    subst hz1 hz2 hais1 hais2
    obtain ⟨_, _, hpt, _⟩ := ais_single_typing_inversion _ _ _ t1s t2s htype
    unfold ai_principal_typing at hpt
    obtain ⟨ts, t's, _, _, _, hbody⟩ := hpt
    exact ih s f ais s' f' ais' C { C' with LABELS := (list.mk_list t's) :: C'.LABELS } [] ts rfl rfl
      hwf1 hmi hbody (construct_inst_prepend_label C C' _ him) hsok
  case ctxt_frame s0 f0 n fi ais s0' fi' ais' _ hwf1 _ ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ htype _ hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 hais2
    injection hz1 with hs1 hf1
    injection hz2 with hs2 hf2
    subst hs1 hf1 hs2 hf2 hais1 hais2
    obtain ⟨_, _, hpt, _⟩ := ais_single_typing_inversion _ _ _ t1s t2s htype
    unfold ai_principal_typing at hpt
    obtain ⟨ts, _, _, hframe, hexpr, _⟩ := hpt
    cases hframe with
    | mk_Frame_ok vals minst tl C0 hminst _ _ _ _ _ _ =>
      cases hexpr with
      | mk_Expr_ok2 _ _ _ hbody _ _ _ =>
        have him_in : inst_match C0 ({ (({
            TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
            LOCALS := tl, LABELS := [], RETURN := none } : context) ++ C0) with
              RETURN := some (list.mk_list ts) } : context) :=
          inst_match_locals_append tl C0
        exact ih s0 _ ais s0' fi' ais' C0 _ [] ts rfl rfl hwf1 hminst hbody him_in hsok
  case ctxt_instrs z vals ais ais1 z' ais' _ _ hwf1 _ ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 hais2
    subst hz1 hz2 hais1 hais2
    obtain ⟨x1, _, hrest⟩ := ais_composition_typing _ _ _ _ t1s t2s htype
    obtain ⟨x2, hA, _⟩ := ais_composition_typing _ _ ais ais1 x1 t2s hrest
    exact ih s f ais s' f' ais' C C' x1 x2 rfl rfl hwf1 hmi hA him hsok
  case local_set z v x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ hsok
    injection h1 with hz1 _
    injection h2 with hz2 _
    subst hz1
    simp only [with_local] at hz2
    injection hz2 with hs _
    subst hs
    exact ⟨Extend_store_refl (Store_ok_wf_store _ hsok), hsok⟩
  case global_set z v x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    simp only [with_global] at hz2
    injection hz2 with hs _
    subst hs
    exact global_set_store_ok s f C C' v x t1s t2s hsok hmi him htype
  case table_set_val z i r x _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    simp only [with_table] at hz2
    injection hz2 with hs _
    subst hs
    exact table_set_store_ok s f C C' i r x _ t1s t2s hsok hmi him htype
  case table_grow_succeed z r k x ti var_0 hgrow hne hget =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    simp only [with_tableinst] at hz2
    injection hz2 with hs _
    subst hs
    exact table_grow_store_ok s f C C' r k _ x ti var_0 t1s t2s hsok hmi him htype hgrow hne hget
  case elem_drop z x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    simp only [with_elem] at hz2
    injection hz2 with hs _
    subst hs
    exact elem_drop_store_ok s f C C' x t1s t2s hsok hmi him htype
  case store_num_val z i nt c ao b_lst _ _ hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    have hwfn : wf_num_ nt c := wf_const_num (wf_config_ais hwfc _ (by simp))
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hz2 hsok hmi him
      (ais_store_mems_inv _ _ _ _ _ _ _ t1s t2s htype) (nbytes__is_wf nt c b_lst hwfn hb)
  case store_pack_val z i v_Inn c k ao b_lst _ _ hc hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    have hwfn : wf_num_ (numtype_Inn v_Inn) c := wf_const_num (wf_config_ais hwfc _ (by simp))
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hz2 hsok hmi him
      (ais_store_mems_inv _ _ _ _ _ _ _ t1s t2s htype)
      (ibytes__is_wf k _ b_lst (wrap___is_wf _ k _ _ (wf_num_Inn_proj v_Inn c hwfn hc) rfl) hb)
  case vstore_val z i c ao b_lst _ _ hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    obtain ⟨u1, u2, hop⟩ := ais_seq3_last_typing _ _ _ _ _ _ htype
    have hwfv : wf_admininstr (admininstr.VCONST vectype.V128 c) := wf_config_ais hwfc _ (by simp)
    obtain ⟨hsz, hwfu⟩ := wf_vconst_parts hwfv
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hz2 hsok hmi him
      (ais_vstore_mems_inversion _ _ ao u1 u2 hop) (vbytes__is_wf vectype.V128 c b_lst hsz hwfu hb)
  case vstore_lane_val z i c v_N ao j b_lst v_Jnn v_M _ _ _ _ _ hb hwfl =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    obtain ⟨u1, u2, hop⟩ := ais_seq3_last_typing _ _ _ _ _ _ htype
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hz2 hsok hmi him
      (ais_vstore_lane_mems_inversion _ _ v_N ao j u1 u2 hop) (ibytes__is_wf v_N _ b_lst hwfl hb)
  case memory_grow_succeed z v_n mi var_0 hgrow hne hget _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    simp only [with_meminst] at hz2
    injection hz2 with hs _
    subst hs
    exact memory_grow_store_ok s f C C' _ v_n mi var_0 t1s t2s hsok hmi him htype hgrow hne hget
  case data_drop z x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1
    simp only [with_data] at hz2
    injection hz2 with hs _
    subst hs
    exact data_drop_store_ok s f C C' x t1s t2s hsok hmi him htype
  -- the remaining rules (traps and failed grows) leave the state unchanged
  all_goals
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ hsok
    injection h1 with hz1 _
    injection h2 with hz2 _
    rw [hz1] at hz2
    injection hz2 with hs _
    subst hs
    exact ⟨Extend_store_refl (Store_ok_wf_store _ hsok), hsok⟩
```

**Signature** (of the `_aux`). Same shape as `store_extension_reduce`, but phrased over fully general `c1 c2 : config` plus the two equality premises (`c1 = ...`, `c2 = ...`) that let `induction hstep` work — see primer §0.8.

**Proof sketch.** Induct on the 23 `Step` constructors. `pure`/`read` and every "trap"/"failed grow" rule change nothing about the store (`all_goals` catches these), so they're `Extend_store_refl` — reflexive, trivially a (degenerate) growth of itself. The three congruence rules (`ctxt_label`/`ctxt_frame`/`ctxt_instrs`) peel off one layer of typing structure (via `ais_single_typing_inversion`/`ais_composition_typing`, which read off the *principal type* of the wrapped sub-instruction) and recurse via the induction hypothesis `ih`. Every genuinely store-writing rule (`global_set`, `table_set_val`, `table_grow_succeed`, `elem_drop`, the four memory-write rules, `memory_grow_succeed`, `data_drop`) is dispatched to exactly one of the per-rule lemmas below, after `simp only [with_global, ...]` unfolds the operational `with_*` state-update function enough to match that lemma's conclusion.

## 2a. The seven store-writing lemmas

Each of these proves one `Step` rule's write respects `Extend_store` (primer §0.6) and keeps `Store_ok`. They all follow one recipe:

1. **Invert the typing** of the redex (an `ais_*_inv` lemma) to learn what the type checker guaranteed — e.g. "the global is mutable and `v` has its type," "the reference has the table's element type."
2. **Locate the store slot**: the instruction names a *module-local* index `x`; `Moduleinst_ok_lengths` + `inst_match` + an `minst_invert_*` lemma turn that into a concrete, in-range store address plus the store's actual instance there (primer §0.2's two-level lookup).
3. **Split** `Store_ok s` into its six typed components (`Store_ok_parts`) and `wf_store s` into its parts (`wf_store_parts`).
4. **Build `Extend_store s s'`** component by component (`Extend_store_of_parts`): the one written component via a dedicated `*_extension` lemma, the other five via reflexivity (`extend_global_refl`, `extend_mem_refl`, …).
5. **Rebuild `Store_ok s'`** (`Store_ok_of_parts`): the written component is re-typed by a `construct_*` lemma, and *every* component's typing — changed or not — is then transported from `s` to `s'` with an `Extend_store_*insts hext` lemma.

That last transport, applied even to untouched components, is easy to miss and worth understanding: the `*_ok` judgments are **indexed by the store**. A table full of function references is well-typed *relative to the store those references point into* (`Ref_ok s r rt` checks the address `r` in `s`), so a typing fact about `s` is not automatically a fact about `s'`; it has to be carried across, and `Extend_store` is exactly what makes that carrying possible.

### `global_set_store_ok`

**Plain-English summary.** `global.set x` overwrites one global variable's value. This lemma shows that write is a legal store growth and leaves the store well-typed — which works because the type checker only accepts `global.set` on a global declared mutable, and only with a value of the global's declared type.

**Code** — [TypePreservation.lean:1081-1120](../../../../../src/test-lean-claude/TypePreservation.lean#L1081-L1120):
```lean
/-- Rocq `store_extension_reduce`, "Global Set" case. -/
theorem global_set_store_ok (s : store) (f : frame) (C C' : context) (v : val) (x : globalidx)
    (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr_val v, admininstr.GLOBAL_SET x] (mkFunctype t1s t2s) →
    Extend_store s { s with
      GLOBALS := list_update_func s.GLOBALS (f.MODULE.GLOBALS[proj_uN_0 x]!)
        (fun g => { g with VALUE := v }) } ∧
    Store_ok { s with
      GLOBALS := list_update_func s.GLOBALS (f.MODULE.GLOBALS[proj_uN_0 x]!)
        (fun g => { g with VALUE := v }) } := by
  intro hsok hmi him htype
  set gs' := list_update_func s.GLOBALS (f.MODULE.GLOBALS[proj_uN_0 x]!) (fun g => { g with VALUE := v })
    with hgs'
  obtain ⟨t, hlkC, hvok⟩ := ais_global_set_inv s C' v x t1s t2s htype
  obtain ⟨hx, hgt⟩ := getElem?_eq_some_bang hlkC
  have hlenG : f.MODULE.GLOBALS.length = C'.GLOBALS.length := by
    rw [← him.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).1
  obtain ⟨gt', v_old, hga, hlk, hsub⟩ := Forall2_nth_of_length f.MODULE.GLOBALS C'.GLOBALS
    (minst_invert_globals s f.MODULE C C' hmi him) hlenG (proj_uN_0 x) (by omega)
  rw [hgt] at hsub
  rw [externtype_global_eq _ _ hsub] at hlk
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt⟩ :=
    Store_ok_parts s hsok
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfv := Val_ok_wf_val s v t hvok
  have hwfgs' : Forall wf_globalinst gs' := Forall_list_update_func _ s.GLOBALS _ _ hwfG
    (fun g hg => by cases hg with | globalinst_case_ gt0 _ _ => exact wf_globalinst.globalinst_case_ gt0 v hwfv)
  have hwfS' : wf_store { s with GLOBALS := gs' } := wf_store_with_globals s gs' hwfS hwfgs'
  have hext : Extend_store s { s with GLOBALS := gs' } := Extend_store_of_parts _ _
    (Nat.le_of_eq (list_update_length_func _ _ _).symm)
    (global_set_global_extension s.GLOBALS gs' _ t v_old v hwfG hwfv hga hlk hgs')
    (Nat.le_refl _) (extend_mem_refl s hwfM) (Nat.le_refl _) (extend_table_refl s hwfT)
    (Nat.le_refl _) (extend_func_refl s hwfF) (Nat.le_refl _) (extend_data_refl s hwfD)
    (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
  refine ⟨hext, Store_ok_of_parts _ gtl mtl ttl ftl dtl etl ((list_update_length_func _ _ _).trans h1)
    (Extend_store_globalinsts _ _ _ _ hext (construct_globalinsts s gtl _ v t v_old h2 hlk hvok))
    h3 (Extend_store_meminsts _ _ _ _ hext h4) h5 (Extend_store_tableinsts _ _ _ _ hext h6)
    h7 (Extend_store_funcinsts _ _ _ _ hext h8) h9 (Extend_store_datainsts₂ _ _ _ _ hext h10)
    h11 (Extend_store_eleminsts _ _ _ _ hext h12) hwfS' hmt htt⟩
```

**Signature.** Inputs: `Store_ok s`; `Moduleinst_ok s f.MODULE C` and `inst_match C C'` (the running module's addresses resolve correctly, and the typing context `C'` agrees with `C` on module-level components); and a typing of exactly the two-instruction redex `[v, GLOBAL_SET x]` at some `t1s → t2s`. Output: for the new store — `s` with its `GLOBALS` list modified at the single address `f.MODULE.GLOBALS[x]` to hold value `v` — both `Extend_store s s'` and `Store_ok s'`. That new-store expression is literally what the operational `with_global` computes, which is why `store_extension_reduce_aux` can pass this lemma's conclusion straight through after `simp only [with_global]`.

**Proof sketch.** Following the recipe: `ais_global_set_inv` (step 1) yields `C'.GLOBALS[x] = some (globaltype.mk_globaltype (some MUT) t)` — the global is declared **mutable** — and `Val_ok s v t`. `minst_invert_globals` (step 2) gives the store address `ga`, in range, holding some `globalinst` whose type is an externtype-subtype of the context's; `externtype_global_eq` collapses that subtyping to equality for globals, so the store's global really is `(MUT, t)` with some old value `v_old`. The new global list is still well-formed (`Forall_list_update_func`, with `Val_ok_wf_val` for `v`). `global_set_global_extension` proves `Extend_globalinst` at every address — the one changed slot is the mutable-global branch of `Extend_globalinst`'s disjunction (primer §0.6). `construct_globalinsts` re-types the updated global list (it needs exactly `Val_ok s v t`), and `Store_ok_of_parts` reassembles, with every component transported by `Extend_store_*insts hext`.

### `table_set_store_ok`

**Plain-English summary.** `table.set x` writes one reference into one slot of table `x`. Same story as `global.set`: the type checker guarantees the new reference has the table's element type, so the table stays well-typed.

**Code** — [TypePreservation.lean:1122-1161](../../../../../src/test-lean-claude/TypePreservation.lean#L1122-L1161):
```lean
/-- Rocq `store_extension_reduce`, "Table Set" case. -/
theorem table_set_store_ok (s : store) (f : frame) (C C' : context) (i : num_) (r : ref) (x : tableidx)
    (k : Nat) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr.CONST numtype.I32 i, admininstr_ref r, admininstr.TABLE_SET x] (mkFunctype t1s t2s) →
    Extend_store s { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!)
        (fun tb => { tb with REFS := list_update_func tb.REFS k (fun _ => r) }) } ∧
    Store_ok { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!)
        (fun tb => { tb with REFS := list_update_func tb.REFS k (fun _ => r) }) } := by
  intro hsok hmi him htype
  set ts' := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!)
    (fun tb => { tb with REFS := list_update_func tb.REFS k (fun _ => r) }) with hts'
  obtain ⟨rt, lim, hlkC, hrok⟩ := ais_table_set_inv s C' i r x t1s t2s htype
  obtain ⟨hx, htt⟩ := getElem?_eq_some_bang hlkC
  have hlenT : f.MODULE.TABLES.length = C'.TABLES.length := by
    rw [← him.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.1
  obtain ⟨tbr, tbt', hta, hlk, hsub⟩ := Forall2_nth_of_length f.MODULE.TABLES C'.TABLES
    (minst_invert_tables s f.MODULE C C' hmi him) hlenT (proj_uN_0 x) (by omega)
  rw [htt] at hsub
  obtain ⟨lim', hlim'⟩ := externtype_table_sub_inv _ _ _ hsub
  rw [hlim'] at hlk
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt'⟩ :=
    Store_ok_parts s hsok
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfts' : Forall wf_tableinst ts' := Forall_list_update_func _ s.TABLES _ _ hwfT
    (fun tb htb => by cases htb with | tableinst_case_ tt0 _ h => exact wf_tableinst.tableinst_case_ tt0 _ h)
  have hwfS' : wf_store { s with TABLES := ts' } := wf_store_with_tables s ts' hwfS hwfts'
  have hext : Extend_store s { s with TABLES := ts' } := Extend_store_of_parts _ _
    (Nat.le_refl _) (extend_global_refl s hwfG) (Nat.le_refl _) (extend_mem_refl s hwfM)
    (Nat.le_of_eq (list_update_length_func _ _ _).symm)
    (table_set_table_extension s.TABLES ts' _ _ tbr k r hwfT hta hlk hts')
    (Nat.le_refl _) (extend_func_refl s hwfF) (Nat.le_refl _) (extend_data_refl s hwfD)
    (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
  refine ⟨hext, Store_ok_of_parts _ gtl mtl ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
    h3 (Extend_store_meminsts _ _ _ _ hext h4) ((list_update_length_func _ _ _).trans h5)
    (Extend_store_tableinsts _ _ _ _ hext (construct_tableinsts s ttl rt _ lim' tbr k r h6 hrok hlk))
    h7 (Extend_store_funcinsts _ _ _ _ hext h8) h9 (Extend_store_datainsts₂ _ _ _ _ hext h10)
    h11 (Extend_store_eleminsts _ _ _ _ hext h12) hwfS' hmt htt'⟩
```

**Signature.** Inputs as before, with the redex `[CONST I32 i, ref r, TABLE_SET x]`. Output: `Extend_store` and `Store_ok` for `s` with the table at address `f.MODULE.TABLES[x]` having its `REFS` list updated at slot `k` to `r`. Note `k` is a free parameter, not tied to `i`: the lemma holds for *any* slot index (updating a list out of range is a no-op), and the caller (`store_extension_reduce_aux`'s `table_set_val` case) lets Lean unify `k` with the index the step actually computed from `i`.

**Proof sketch.** `ais_table_set_inv` yields the context's table type `(lim, rt)` and `Ref_ok s r rt` — the reference has the table's element type. `minst_invert_tables` gives the store address and the store's actual `tableinst` there, whose type is an externtype-subtype of `(lim, rt)`; `externtype_table_sub_inv` says that subtype has the *same* element type `rt` (only the limits may differ — e.g. the store's real table may be larger than an importing module declared). `table_set_table_extension` gives `Extend_tableinst` everywhere: the table's size is unchanged, and `Extend_tableinst` constrains only sizes and the type, not contents. `construct_tableinsts` re-types the updated table (needs `Ref_ok s r rt`), and `Store_ok_of_parts` reassembles.

### `table_grow_store_ok`

**Plain-English summary.** `table.grow x` appends `n` copies of an initial reference `r` to table `x` — when the operational helper `$growtable` succeeds. (It fails if the new size would exceed the table's declared maximum; that's the separate `table_grow_fail` rule, which leaves the store alone and pushes `-1`.)

**Code** — [TypePreservation.lean:1163-1232](../../../../../src/test-lean-claude/TypePreservation.lean#L1163-L1232):
```lean
/-- Rocq `store_extension_reduce`, "Table Grow" case. -/
theorem table_grow_store_ok (s : store) (f : frame) (C C' : context) (r : ref) (v_n : Nat) (k : num_)
    (x : tableidx) (ti : tableinst) (var_0 : Option tableinst) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr_ref r, admininstr.CONST numtype.I32 k, admininstr.TABLE_GROW x] (mkFunctype t1s t2s) →
    fun_growtable (fun_table (state.mk_state s f) x) v_n r var_0 → var_0 ≠ none → Option.get! var_0 = ti →
    Extend_store s { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ => ti) } ∧
    Store_ok { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ => ti) } := by
  intro hsok hmi him htype hgrow hne hget
  cases hgrow with
  | fun_growtable_case_1 _ => exact absurd rfl hne
  | fun_growtable_case_0 ti' i j_opt rt r'_lst i' hold hi' hj hti' _ hwfnew =>
    have hteq : ti' = ti := hget
    subst hteq hti' hi'
    -- the table operand's type, and the table address the module instance maps `x` to
    obtain ⟨rt0, lim0, hlkC, hrok⟩ := ais_table_grow_inv s C' r k x t1s t2s htype
    obtain ⟨hx, htt⟩ := getElem?_eq_some_bang hlkC
    have hlenT : f.MODULE.TABLES.length = C'.TABLES.length := by
      rw [← him.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.1
    obtain ⟨tbr, tbt', hta, hlk, hsub⟩ := Forall2_nth_of_length f.MODULE.TABLES C'.TABLES
      (minst_invert_tables s f.MODULE C C' hmi him) hlenT (proj_uN_0 x) (by omega)
    rw [htt] at hsub
    obtain ⟨lim', hlim'⟩ := externtype_table_sub_inv _ _ _ hsub
    rw [hlim'] at hlk
    -- `$growtable`'s view of the old table is the store's table at that address
    have hold' := hold.trans hlk
    injection hold' with hT hR
    injection hT with hL hrt
    subst hL hrt hR
    obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt'⟩ :=
      Store_ok_parts s hsok
    obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
    -- its `Tableinst_ok` pins the old minimum to the current length
    have htok := Forall2_nth_of_length s.TABLES ttl h6 h5 _ hta
    rw [show (s.TABLES[f.MODULE.TABLES[proj_uN_0 x]!]! : tableinst) = lookup_total s.TABLES _ from rfl,
      hlk] at htok
    obtain ⟨rl0, v_m, rt'', he1, he2, _, _⟩ := tableinst_ok_invert s _ _ htok
    injection he1 with hA hB
    rw [← hA] at he2
    injection he2 with hC _
    injection hC with hD _
    subst hB
    subst hD
    have hwfnewtt : wf_tabletype (tabletype.mk_tabletype
        (limits.mk_limits (uN.mk_uN (r'_lst.length + v_n)) j_opt) rt) := by
      cases hwfnew with | tableinst_case_ _ _ h => exact h
    set ts' := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ =>
      tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (r'_lst.length + v_n)) j_opt) rt)
        (r'_lst ++ List.replicate v_n r)) with hts'
    have hwfts' : Forall wf_tableinst ts' := Forall_list_update_func _ s.TABLES _ _ hwfT (fun _ _ => hwfnew)
    have hwfS' : wf_store { s with TABLES := ts' } := wf_store_with_tables s ts' hwfS hwfts'
    have hext : Extend_store s { s with TABLES := ts' } := Extend_store_of_parts _ _
      (Nat.le_refl _) (extend_global_refl s hwfG) (Nat.le_refl _) (extend_mem_refl s hwfM)
      (Nat.le_of_eq (list_update_length_func _ _ _).symm)
      (table_grow_table_extension s.TABLES ts' _ j_opt r rt v_n r'_lst hwfT hwfts' hta hlk hts')
      (Nat.le_refl _) (extend_func_refl s hwfF) (Nat.le_refl _) (extend_data_refl s hwfD)
      (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
    refine ⟨hext, Store_ok_of_parts _ gtl mtl
      (list_update_func ttl (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ =>
        tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (r'_lst.length + v_n)) j_opt) rt))
      ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
      h3 (Extend_store_meminsts _ _ _ _ hext h4)
      ((list_update_length_func _ _ _).trans (h5.trans (list_update_length_func _ _ _).symm))
      (Extend_store_tableinsts _ _ _ _ hext
        (construct_tableinsts_grow s ttl r rt _ r'_lst j_opt v_n ts' hwfts' h6 hrok hj hlk hts'))
      h7 (Extend_store_funcinsts _ _ _ _ hext h8) h9 (Extend_store_datainsts₂ _ _ _ _ hext h10)
      h11 (Extend_store_eleminsts _ _ _ _ hext h12) hwfS' hmt
      (Forall_list_update_func _ ttl _ _ htt' (fun _ _ => hwfnewtt))⟩
```

**Signature.** Beyond the usual inputs and the redex typing `[ref r, CONST I32 k, TABLE_GROW x]`, it threads the operational facts the `Step.table_grow_succeed` rule carries: `fun_growtable (fun_table (state.mk_state s f) x) v_n r var_0` (running `$growtable` on the current table produced `var_0`), `var_0 ≠ none` (it succeeded), and `Option.get! var_0 = ti` (the result is `ti`). Output: `Extend_store`/`Store_ok` for `s` with the table at `f.MODULE.TABLES[x]` replaced wholesale by `ti`.

**Proof sketch.** Case on `fun_growtable`'s two constructors: `fun_growtable_case_1` is the "returns `none`" case, contradicting `var_0 ≠ none` (`absurd`). In `fun_growtable_case_0` we learn the old table `ti'`, the shape of the new table (old refs `r'_lst` plus `replicate v_n r`, minimum bumped to `|r'_lst| + v_n`), that the new size respects the maximum (`hj`), and that the new table is well-formed. The code's own comments mark the next moves: identify `$growtable`'s view of the old table with the store's actual table at that address (`hold.trans hlk`), then use that table's `Tableinst_ok` (`tableinst_ok_invert`) to pin the old minimum to the current length. With the new store built, `table_grow_table_extension` gives `Extend_tableinst` (size grows, old refs kept as a prefix) and `construct_tableinsts_grow` re-types the grown table at its *new* type (needs `Ref_ok s r rt` for the fill value and the maximum bound). Because the grown table's type changed (bigger minimum), the table-type list handed to `Store_ok_of_parts` is itself updated (`list_update_func ttl …`), as is its well-formedness (`Forall_list_update_func … hwfnewtt`).

### `elem_drop_store_ok`

**Plain-English summary.** `elem.drop x` empties a passive element segment (a list of references that `table.init` copies from). Dropping exists so an engine can free a segment once it's no longer needed; afterwards the segment behaves as if it were empty.

**Code** — [TypePreservation.lean:1234-1267](../../../../../src/test-lean-claude/TypePreservation.lean#L1234-L1267):
```lean
/-- Rocq `store_extension_reduce`, "Elem Drop" case. -/
theorem elem_drop_store_ok (s : store) (f : frame) (C C' : context) (x : elemidx) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr.ELEM_DROP x] (mkFunctype t1s t2s) →
    Extend_store s { s with
      ELEMS := list_update_func s.ELEMS (f.MODULE.ELEMS[proj_uN_0 x]!)
        (fun e => { e with REFS := [] }) } ∧
    Store_ok { s with
      ELEMS := list_update_func s.ELEMS (f.MODULE.ELEMS[proj_uN_0 x]!)
        (fun e => { e with REFS := [] }) } := by
  intro hsok hmi him htype
  set es' := list_update_func s.ELEMS (f.MODULE.ELEMS[proj_uN_0 x]!) (fun e => { e with REFS := [] })
    with hes'
  obtain ⟨rt, hlkC⟩ := ais_elem_drop_inv s C' x t1s t2s htype
  obtain ⟨hx, _⟩ := getElem?_eq_some_bang hlkC
  have hlenE : f.MODULE.ELEMS.length = C'.ELEMS.length := by
    rw [← him.2.2.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.2.2
  obtain ⟨ref_lst, hea, _, hlk⟩ := Forall2_nth_of_length f.MODULE.ELEMS C'.ELEMS
    (minst_invert_elems s f.MODULE C C' hmi him) hlenE (proj_uN_0 x) (by omega)
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt⟩ :=
    Store_ok_parts s hsok
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfS' : wf_store { s with ELEMS := es' } := wf_store_with_elems s es' hwfS
  have hext : Extend_store s { s with ELEMS := es' } := Extend_store_of_parts _ _
    (Nat.le_refl _) (extend_global_refl s hwfG) (Nat.le_refl _) (extend_mem_refl s hwfM)
    (Nat.le_refl _) (extend_table_refl s hwfT) (Nat.le_refl _) (extend_func_refl s hwfF)
    (Nat.le_refl _) (extend_data_refl s hwfD)
    (Nat.le_of_eq (list_update_length_func _ _ _).symm)
    (elem_drop_elem_extension s.ELEMS es' _ hea hes') hwfS hwfS'
  refine ⟨hext, Store_ok_of_parts _ gtl mtl ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
    h3 (Extend_store_meminsts _ _ _ _ hext h4) h5 (Extend_store_tableinsts _ _ _ _ hext h6)
    h7 (Extend_store_funcinsts _ _ _ _ hext h8) h9 (Extend_store_datainsts₂ _ _ _ _ hext h10)
    ((list_update_length_func _ _ _).trans h11)
    (Extend_store_eleminsts _ _ _ _ hext (construct_eleminsts s etl _ _ ref_lst h12 hlk)) hwfS' hmt htt⟩
```

**Signature.** Inputs as usual with the one-instruction redex `[ELEM_DROP x]`. Output: `Extend_store`/`Store_ok` for `s` with the element instance at `f.MODULE.ELEMS[x]` having `REFS := []`.

**Proof sketch.** The simplest of the seven — no operational side-relation to case on. `ais_elem_drop_inv` yields `C'.ELEMS[x] = some rt`, so `x` is in range; `minst_invert_elems` gives the store address and its element instance `{TYPE := rt, REFS := ref_lst}`. Well-formedness of the new store is immediate: `wf_store` places no constraint on element instances, which is why `wf_store_with_elems` takes no extra premise. `elem_drop_elem_extension` proves `Extend_eleminst` everywhere — the emptied segment is the `ref'_lst = []` disjunct (primer §0.6). `construct_eleminsts` re-types it (an empty reference list is trivially well-typed at the segment's type), and `Store_ok_of_parts` reassembles.

### `data_drop_store_ok`

**Plain-English summary.** `data.drop x` is `elem.drop`'s mirror image for passive *data* segments (byte blobs that `memory.init` copies from).

**Code** — [TypePreservation.lean:1269-1306](../../../../../src/test-lean-claude/TypePreservation.lean#L1269-L1306):
```lean
/-- Rocq `store_extension_reduce`, "Data Drop" case. -/
theorem data_drop_store_ok (s : store) (f : frame) (C C' : context) (x : dataidx) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr.DATA_DROP x] (mkFunctype t1s t2s) →
    Extend_store s { s with
      DATAS := list_update_func s.DATAS (f.MODULE.DATAS[proj_uN_0 x]!)
        (fun _ => datainst.MKdatainst []) } ∧
    Store_ok { s with
      DATAS := list_update_func s.DATAS (f.MODULE.DATAS[proj_uN_0 x]!)
        (fun _ => datainst.MKdatainst []) } := by
  intro hsok hmi him htype
  set ds' := list_update_func s.DATAS (f.MODULE.DATAS[proj_uN_0 x]!) (fun _ => datainst.MKdatainst [])
    with hds'
  have hlkC := ais_data_drop_inv s C' x t1s t2s htype
  obtain ⟨hx, _⟩ := getElem?_eq_some_bang hlkC
  obtain ⟨hlenD, hdas⟩ := minst_invert_datas s f.MODULE C C' hmi him
  have hxm : proj_uN_0 x < f.MODULE.DATAS.length := by omega
  have hmem : f.MODULE.DATAS[proj_uN_0 x]! ∈ f.MODULE.DATAS := by
    rw [getElem!_pos f.MODULE.DATAS _ hxm]; exact List.getElem_mem hxm
  obtain ⟨b_lst, hda, hlk⟩ := hdas _ hmem
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt⟩ :=
    Store_ok_parts s hsok
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfds' : Forall wf_datainst ds' := Forall_list_update_func _ s.DATAS _ _ hwfD
    (fun _ _ => wf_datainst.datainst_case_ [] (by intro _ h; simp at h))
  have hwfS' : wf_store { s with DATAS := ds' } := wf_store_with_datas s ds' hwfS hwfds'
  have hext : Extend_store s { s with DATAS := ds' } := Extend_store_of_parts _ _
    (Nat.le_refl _) (extend_global_refl s hwfG) (Nat.le_refl _) (extend_mem_refl s hwfM)
    (Nat.le_refl _) (extend_table_refl s hwfT) (Nat.le_refl _) (extend_func_refl s hwfF)
    (Nat.le_of_eq (list_update_length_func _ _ _).symm)
    (data_drop_data_extension s.DATAS ds' _ hwfD hda hds')
    (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
  refine ⟨hext, Store_ok_of_parts _ gtl mtl ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
    h3 (Extend_store_meminsts _ _ _ _ hext h4) h5 (Extend_store_tableinsts _ _ _ _ hext h6)
    h7 (Extend_store_funcinsts _ _ _ _ hext h8) ((list_update_length_func _ _ _).trans h9)
    (datainsts_Forall₂_of_Forall _ _ dtl (Extend_store_datainsts _ _ _ hext
      (construct_datainsts s _ b_lst (datainsts_Forall_of_Forall₂ s s.DATAS dtl h9 h10) hlk)))
    h11 (Extend_store_eleminsts _ _ _ _ hext h12) hwfS' hmt htt⟩
```

**Signature.** Redex `[DATA_DROP x]`; output: `Extend_store`/`Store_ok` for `s` with the data instance at `f.MODULE.DATAS[x]` replaced by `{BYTES := []}`.

**Proof sketch.** `ais_data_drop_inv` yields `C'.DATAS[x] = some datatype.OK`; `minst_invert_datas` gives the module's data-address list has the context's length and that every data address is in range with some bytes, from which the proof picks the one at `x` (`hmem`, `hdas`). The empty data instance is well-formed, `data_drop_data_extension` gives `Extend_datainst` (the `b'_lst = []` disjunct), and `construct_datainsts` re-types it. One wrinkle: `datatype` has exactly one value, `OK` (`datatype_eq_OK`), so data-segment typing carries no information, and the two small lemmas `datainsts_Forall_of_Forall₂`/`datainsts_Forall₂_of_Forall` convert between `Store_ok`'s "`Forall₂` against a list of types" form and the simpler "every segment is `Datainst_ok … OK`" form that `construct_datainsts` and `Extend_store_datainsts` use.

### `with_mem_store_ok`

**Plain-English summary.** All four memory-*write* rules — scalar `store` (`i32.store`, `f64.store`, …), narrow `store` (`i32.store8`, …), `v128.store`, and `v128.storeN_lane` — end in the same operational update, `with_mem`, which overwrites a run of bytes in memory 0. So one lemma covers all four; the rules differ only in how they compute the bytes.

**Code** — [TypePreservation.lean:1339-1354](../../../../../src/test-lean-claude/TypePreservation.lean#L1339-L1354):
```lean
/-- Rocq `store_extension_reduce`, the four memory-store cases (`store_num_val`,
    `store_pack_val`, `vstore_val`, `vstore_lane_val`). `with_mem` writes `b*` with `splice`,
    which is `list_slice_update` with length `|b*|` (`splice_eq_list_slice_update`), so each case
    is `mem_store_extension` (as in Rocq, which calls it for the two SIMD cases and inlines it
    for the two scalar ones). The length argument `with_mem` receives is unused by `splice`. -/
theorem with_mem_store_ok (s : store) (f : frame) (s' : store) (f' : frame) (C C' : context)
    (off len : Nat) (b_lst : List byte) :
    with_mem (state.mk_state s f) (uN.mk_uN 0) off len b_lst = state.mk_state s' f' →
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' → 0 < C'.MEMS.length →
    Forall wf_byte b_lst → Extend_store s s' ∧ Store_ok s' := by
  intro heq hsok hmi him hmem hwfb
  simp only [with_mem, splice_eq_list_slice_update] at heq
  injection heq with hs _
  subst hs
  exact mem_store_extension s f C C' off b_lst b_lst.length hsok (Store_ok_wf_store s hsok) hmi him hmem
    hwfb rfl
```

**Signature.** Phrased operationally rather than per instruction: if `with_mem` (write `b_lst` at byte offset `off` of memory 0) takes state `(s, f)` to `(s', f')`, the usual typing package holds, `0 < C'.MEMS.length` (the module has a memory 0), and the bytes are well-formed (`Forall wf_byte b_lst`), then `Extend_store s s' ∧ Store_ok s'`. That genericity is what lets `store_extension_reduce_aux` reuse it for four different rules. As its doc comment notes, the `len` argument `with_mem` receives is unused (`splice` uses `b_lst.length`).

**Proof sketch.** Unfold `with_mem`, rewrite its `splice` into `list_slice_update` (`splice_eq_list_slice_update`), and `injection` the resulting state equation to identify `s'` exactly. Then hand off to `mem_store_extension` ([TypePreservation.lean:422-459](../../../../../src/test-lean-claude/TypePreservation.lean#L422-L459)), which runs the five-step recipe for memory 0. The key fact underneath is that `list_slice_update` overwrites in place and never changes the list's length (it is defined by structural recursion that stops at the end of the original list), so the memory keeps its size: its byte count still matches its page count (`construct_meminsts` needs no length premise), and `Extend_meminst`, which only constrains sizes, holds (`store_none_mem_extension`).

### `memory_grow_store_ok`

**Plain-English summary.** `memory.grow` appends `n` pages (64 KiB each) of zero bytes to memory 0, when the operational helper `$growmemory` succeeds — the structural twin of `table_grow_store_ok`. (Failure, e.g. exceeding the declared maximum, is the separate `memory_grow_fail` rule, which leaves the store alone and pushes `-1`.)

**Code** — [TypePreservation.lean:1356-1435](../../../../../src/test-lean-claude/TypePreservation.lean#L1356-L1435):
```lean
/-- Rocq `store_extension_reduce`, "Memory Grow" case. Uses `rat_to_nat_natCast` above for the
    new page count. -/
theorem memory_grow_store_ok (s : store) (f : frame) (C C' : context) (a : admininstr) (v_n : Nat)
    (mi : meminst) (var_0 : Option meminst) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [a, admininstr.MEMORY_GROW] (mkFunctype t1s t2s) →
    fun_growmemory (fun_mem (state.mk_state s f) (uN.mk_uN 0)) v_n var_0 → var_0 ≠ none →
    Option.get! var_0 = mi →
    Extend_store s { s with
      MEMS := list_update_func s.MEMS (f.MODULE.MEMS[0]!) (fun _ => mi) } ∧
    Store_ok { s with
      MEMS := list_update_func s.MEMS (f.MODULE.MEMS[0]!) (fun _ => mi) } := by
  intro hsok hmi him htype hgrow hne hget
  cases hgrow with
  | fun_growmemory_case_1 _ => exact absurd rfl hne
  | fun_growmemory_case_0 mi' i j_opt b_lst i' hold hi' hj h216 hmi' _ hwfnew =>
    have hmeq : mi' = mi := hget
    subst hmeq hmi'
    -- the grown memory is memory 0 of the module instance, a valid store address
    have hmems := ais_memory_grow_inv s C' a t1s t2s htype
    have hlenM : f.MODULE.MEMS.length = C'.MEMS.length := by
      rw [← him.2.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.1
    obtain ⟨_, _, hma, _, _⟩ := Forall2_nth_of_length f.MODULE.MEMS C'.MEMS
      (minst_invert_mems s f.MODULE C C' hmi him) hlenM 0 (by omega)
    obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt⟩ :=
      Store_ok_parts s hsok
    obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
    -- its `Meminst_ok` pins the old shape: `|b*| = lim_old * 64Ki`
    have hmok := Forall2_nth_of_length s.MEMS mtl h4 h3 _ hma
    obtain ⟨vn0, m_opt, bs0, he1, _, hblen, _, _⟩ := meminst_ok_raw s _ _ hmok
    have hold' : meminst.MKmeminst (memtype.PAGE (limits.mk_limits i j_opt)) b_lst =
        meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN vn0) (m_opt.map uN.mk_uN))) bs0 :=
      hold.trans he1
    injection hold' with hA hB
    injection hA with hA'
    injection hA' with hC hjo
    subst hC hjo hB
    -- so the new page count `i'` is the natural number `lim_old + n`
    have hi'' : i' = ((vn0 + v_n : Nat) : Rat) := by
      rw [hi', hblen]; unfold Ki; push_cast; ring
    subst hi''
    rw [rat_to_nat_natCast] at hwfnew ⊢
    have h216' : vn0 + v_n ≤ 2 ^ 16 := by exact_mod_cast h216
    have hjn : Forall (fun v_j => vn0 + v_n ≤ proj_uN_0 v_j) (Option.toList (m_opt.map uN.mk_uN)) := by
      intro v_j hv
      have := hj v_j hv
      exact_mod_cast this
    have hjn' : Forall (fun j => vn0 + v_n ≤ j) m_opt.toList := by
      intro j hjm
      have hmem : uN.mk_uN j ∈ Option.toList (m_opt.map uN.mk_uN) := by
        rcases m_opt with _ | m0
        · simp at hjm
        · simp only [Option.toList_some, List.mem_singleton] at hjm
          subst hjm; simp
      exact hjn _ hmem
    have hlim : vn0 = b_lst.length / (64 * Ki) := by
      rw [hblen, Nat.mul_div_cancel _ (by unfold Ki; norm_num)]
    have hwfmt : wf_memtype (memtype.PAGE (limits.mk_limits (uN.mk_uN (vn0 + v_n)) (m_opt.map uN.mk_uN))) := by
      cases hwfnew with | meminst_case_ _ _ h _ => exact h
    set ms' := list_update_func s.MEMS (f.MODULE.MEMS[0]!) (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (vn0 + v_n)) (m_opt.map uN.mk_uN)))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))) with hms'
    have hwfms' : Forall wf_meminst ms' := Forall_list_update_func _ s.MEMS _ _ hwfM (fun _ _ => hwfnew)
    have hwfS' : wf_store { s with MEMS := ms' } := wf_store_with_mems s ms' hwfS hwfms'
    have hext : Extend_store s { s with MEMS := ms' } := Extend_store_of_parts _ _
      (Nat.le_refl _) (extend_global_refl s hwfG)
      (Nat.le_of_eq (list_update_length_func _ _ _).symm)
      (memory_grow_mem_extension s.MEMS ms' _ b_lst vn0 v_n m_opt hwfM hwfms' hma he1 hjn' hms')
      (Nat.le_refl _) (extend_table_refl s hwfT) (Nat.le_refl _) (extend_func_refl s hwfF)
      (Nat.le_refl _) (extend_data_refl s hwfD) (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
    refine ⟨hext, Store_ok_of_parts _ gtl
      (list_update_func mtl (f.MODULE.MEMS[0]!) (fun _ =>
        memtype.PAGE (limits.mk_limits (uN.mk_uN (vn0 + v_n)) (m_opt.map uN.mk_uN))))
      ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
      ((list_update_length_func _ _ _).trans (h3.trans (list_update_length_func _ _ _).symm))
      (Extend_store_meminsts _ _ _ _ hext
        (construct_meminsts_grow s mtl _ b_lst vn0 v_n _ ms' hwfms' h4 he1 hlim hjn h216' hms'))
      h5 (Extend_store_tableinsts _ _ _ _ hext h6) h7 (Extend_store_funcinsts _ _ _ _ hext h8)
      h9 (Extend_store_datainsts₂ _ _ _ _ hext h10) h11 (Extend_store_eleminsts _ _ _ _ hext h12)
      hwfS' (Forall_list_update_func _ mtl _ _ hmt (fun _ _ => hwfmt)) htt⟩
```

**Signature.** Redex typing `[a, MEMORY_GROW]` (where `a` is the page-count operand; the lemma only needs the sequence to typecheck, to learn memory 0 exists), plus the operational facts from `Step.memory_grow_succeed`: `fun_growmemory (fun_mem (state.mk_state s f) (uN.mk_uN 0)) v_n var_0`, `var_0 ≠ none`, `Option.get! var_0 = mi`. Output: `Extend_store`/`Store_ok` for `s` with the memory at `f.MODULE.MEMS[0]` replaced by `mi`.

**Proof sketch.** Case on `fun_growmemory` (the `_case_1` failure case contradicts `var_0 ≠ none`). The success case provides the old memory `{PAGE (limits i j_opt), b_lst}`, the new page count `i'` — computed by the spec as the rational `|b_lst| / 64Ki + v_n` — and the bounds `i' ≤ 2^16` (`h216`) and `i' ≤` the declared maximum (`hj`). The comments in the code mark the steps: memory 0 of the module instance is a valid store address (`ais_memory_grow_inv`, `minst_invert_mems`); its `Meminst_ok` pins the old shape `|b*| = lim_old * 64Ki` (`meminst_ok_raw`); so the new page count `i'` is the natural number `lim_old + n` (`push_cast; ring`). That last fact is where `rat_to_nat_natCast` ([TypePreservation.lean:1312-1319](../../../../../src/test-lean-claude/TypePreservation.lean#L1312-L1319), `rat_to_nat (n : Rat) = n`) earns its place: it collapses the spec's rational arithmetic back to plain `Nat`, after which the bounds transfer by `exact_mod_cast`. Then the recipe: `memory_grow_mem_extension` (size grows, old bytes kept as a prefix), `construct_meminsts_grow` (the grown memory is well-typed at its new page count), and — since the grown memory's type changed — an updated memory-type list passed to `Store_ok_of_parts`.

## 2b. `Extend_store_refl`

**Plain-English summary.** Reflexivity: a store trivially "extends" itself (every component is unchanged, which satisfies every `Extend_*` relation's "stayed the same or only grew" clause). Used by every `Step` case that doesn't touch the store at all (`pure`, `read`, `local_set`, and every trap/failed-grow rule).

**Code** — [ExtensionLemmas.lean:1037-1074](../../../../../src/test-lean-claude/ExtensionLemmas.lean#L1037-L1074):
```lean
/-- Rocq `Extend_store_refl` (was `store_extension_refl`; RENAMED only —
    the underlying `Extend_store` constructor lives in `wasm2.0.lean`,
    which was **not** touched by the 2026-09-24 resync, so this lemma's
    actual shape and proof are unaffected; only its Rocq-side name changed).
    **No explicit `Extend_store_trans` (transitivity) lemma exists anywhere
    in the current Rocq file either** — downstream preservation proofs
    re-derive extension facts per reduction step rather than composing two
    `Extend_store` proofs. Not ported here either, matching the Rocq gap.
    Proof reused from a prior Lean session's `Extension.lean`
    (`extend_store_refl`); note it calls the single-instance `_refl0` lemmas
    and `forall_range_refl` directly rather than routing through the
    store-specific `extend_func_refl`-family lemmas above — a legitimate
    proof-method divergence (Lean has proof irrelevance), not a
    signature divergence. -/
theorem Extend_store_refl {s : store} (h : wf_store s) : Extend_store s s := by
  cases h with
  | store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas =>
    have hwf : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas
    exact Extend_store.mk_Extend_store _ _
      (forall_range_lt globals) (forall_range_lt globals)
      (forall_range_refl globals wf_globalinst Extend_globalinst hglobals
        (fun x hx => extend_globalinst_refl_0 hx))
      (forall_range_lt mems) (forall_range_lt mems)
      (forall_range_refl mems wf_meminst Extend_meminst hmems
        (fun x hx => extend_meminst_refl_0 hx))
      (forall_range_lt tables) (forall_range_lt tables)
      (forall_range_refl tables wf_tableinst Extend_tableinst htables
        (fun x hx => extend_tableinst_refl_0 hx))
      (forall_range_lt funcs) (forall_range_lt funcs)
      (forall_range_refl funcs wf_funcinst Extend_funcinst hfuncs
        (fun x hx => extend_funcinst_refl_0 hx))
      (forall_range_lt datas) (forall_range_lt datas)
      (forall_range_refl datas wf_datainst Extend_datainst hdatas
        (fun x hx => extend_datainst_refl_0 hx))
      (forall_range_lt elems) (forall_range_lt elems)
      (forall_range_refl_noWf elems Extend_eleminst extend_eleminst_refl_0)
      hwf hwf
```

**Signature.** Just `wf_store s → Extend_store s s` — note it needs `wf_store`, not `Store_ok`; reflexivity of "growth" only needs syntactic sanity, not typing.

**Proof sketch.** Destructure `wf_store`'s one constructor to get each component's well-formedness, then build `Extend_store.mk_Extend_store` field by field: "every address below the length is in range" (`forall_range_lt`) is trivially true against itself, and "each old/new pair at that address satisfies `Extend_<thing>inst`" reduces, when old = new, to each `Extend_<thing>inst`'s own dedicated reflexivity fact (`extend_globalinst_refl_0`, etc. — one tiny lemma per component, applying the "or equal" side of each disjunction from primer §0.6). The doc comment also records a fact worth knowing: there is no `Extend_store_trans` (transitivity) lemma, in Lean or in Rocq — every proof re-derives extension facts per step instead of chaining them.

## Bonus: `step_moduleinst` — the pre-packaged composition

Not separately named in the diagram, but worth flagging since it exists in the source and *is* exactly "`store_extension_reduce` + `reduce_inst_unchanged` + `Extend_store_moduleinst`, composed" — [TypePreservation.lean:1624-1636](../../../../../src/test-lean-claude/TypePreservation.lean#L1624-L1636):
```lean
/-- Rocq `type_preservation.v:3120` `step_moduleinst`. Composition:
    `reduce_inst_unchanged` + `Extend_store_moduleinst` + `store_extension_reduce`. -/
theorem step_moduleinst (v_s : store) (v_f : frame) (v_ais : List admininstr) (v_s' : store)
    (v_f' : frame) (v_ais' : List admininstr) (v_C v_C' : context) (v_tf : functype) :
    wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →
    Step (config.mk_config (state.mk_state v_s v_f) v_ais) (config.mk_config (state.mk_state v_s' v_f') v_ais') →
    Store_ok v_s → Moduleinst_ok v_s v_f.MODULE v_C → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais v_tf → Moduleinst_ok v_s' v_f'.MODULE v_C := by
  intro hwfc hstep hsok hmi him htype
  rw [← reduce_inst_unchanged v_s v_f v_ais v_s' v_f' v_ais' hstep]
  exact Extend_store_moduleinst v_s v_s' v_f.MODULE v_C
    (store_extension_reduce v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' v_tf hwfc hstep hmi htype him hsok).1
    hmi
```
Interesting detail from reading `t_preservation`'s actual proof term (file `01`): it does *not* call `step_moduleinst`. It inlines the same three-lemma composition directly instead (you can see `reduce_inst_unchanged`, `Extend_store_moduleinst`, and `.1` of `store_extension_reduce`'s pair, called separately). `step_moduleinst` is available — ported 1:1 from the Rocq lemma of the same name — but this particular caller just didn't route through it.

---
*Next: [03-reduce-inst-unchanged.md](03-reduce-inst-unchanged.md).*

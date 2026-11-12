# 7. `t_preservation_type_aux` — the 23-case engine

*(Previous: [06-t-preservation-type.md](06-t-preservation-type.md). Next: [08-t-read-preservation.md](08-t-read-preservation.md), the `Step.read` branch — the diagram's §7b.)*

**Plain-English summary.** This is where the instruction-sequence-typing half of preservation is actually proved, case by case over every way a step can happen: hand off to `t_pure_preservation`/`t_read_preservation` for the two lifted sub-relations, recurse through the three congruence rules, and directly re-derive a typing for each store-writing rule's very simple reduct (`[]`, or one `CONST` value).

**Code — the full 23-case proof** — [TypePreservation.lean:2420-2673](../../../../../src/test-lean-claude/TypePreservation.lean#L2420-L2673):
```lean
/-- Generalized form of `t_preservation_type` (same `remember`/`generalize dependent`
    encoding as `reduce_inst_unchanged_aux`), additionally taking `wf_config` of the
    post-configuration: the congruence rules carry the inner configurations' `wf_config`
    as premises, so the induction never needs `Step_is_wf` itself; only the top-level
    wrapper below does (exactly where Rocq uses it). -/
private theorem t_preservation_type_aux (c1 c2 : config) (hstep : Step c1 c2) :
    ∀ (v_s : store) (v_f : frame) (v_ais : List admininstr) (v_s' : store) (v_f' : frame)
      (v_ais' : List admininstr) (v_C v_C' : context) (t1s t2s : List valtype),
      c1 = config.mk_config (state.mk_state v_s v_f) v_ais →
      c2 = config.mk_config (state.mk_state v_s' v_f') v_ais' →
      wf_config c1 → wf_config c2 →
      Store_ok v_s → Store_ok v_s' → Extend_store v_s v_s' →
      Moduleinst_ok v_s v_f.MODULE v_C → Moduleinst_ok v_s' v_f.MODULE v_C →
      Vals_ok v_s v_f.LOCALS v_C'.LOCALS → inst_match v_C v_C' →
      Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s) → Instrs_ok2 v_s' v_C' v_ais' (mkFunctype t1s t2s) := by
  induction hstep
  case pure z ais ais' hp =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ _ _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with hz2 hais2
    rw [hz1] at hz2
    injection hz2 with hs _
    subst hs hais1 hais2
    exact t_pure_preservation _ _ _ _ _ htype hp
  case read z ais ais' hr =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc1 _ hsok _ _ hmi _ hvals him htype
    injection h1 with hz1 hais1
    injection h2 with hz2 hais2
    rw [hz1] at hz2
    injection hz2 with hs _
    subst hz1 hs hais1 hais2
    exact t_read_preservation _ f _ _ C C' t1s t2s hwfc1 hr hsok hmi hvals him htype
  case ctxt_label z n instrs0 ais z' ais' _ hwf1 hwf2 ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 hsok hsok' hext hmi hmi' hvals him htype
    injection h1 with hz1 hais1
    injection h2 with hz2 hais2
    subst hz1 hz2 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    obtain ⟨_, _, hpt, hsub⟩ := ais_single_typing_inversion _ _ _ t1s t2s htype
    unfold ai_principal_typing at hpt
    obtain ⟨ts, t's, heq, hn, hinstrs, hbody⟩ := hpt
    rw [heq] at hsub
    have hbody' := ih s f ais s' f' ais' C { C' with LABELS := (list.mk_list t's) :: C'.LABELS } [] ts rfl rfl
      hwf1 hwf2 hsok hsok' hext hmi hmi' hvals (construct_inst_prepend_label C C' _ him) hbody
    have hinstrs' := Extend_store_ais _ _ _ _ _ hext hsok hsok' hinstrs
    have hwfL : wf_admininstr (admininstr.LABEL_ n instrs0 ais') := wf_config_ais hwfc2 _ (by simp)
    exact construct_ais_subtyping _ _ _ [] ts t1s t2s
      (construct_ais_typing_single _ _ _ [] ts
        (Instr_ok2.label _ C' n instrs0 ais' ts t's hinstrs' hbody' (Extend_store_wf_store' _ _ hext) hwfC'
          hwfL (wf_context_label_only _) hn.symm)) hsub
  case ctxt_frame s0 f0 n fi ais s0' fi' ais' hinner hwf1 hwf2 ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 hsok hsok' hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with hz2 hais2
    injection hz1 with hs1 hf1
    injection hz2 with hs2 hf2
    subst hs1 hf1 hs2 hf2 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    have hwfS' := Extend_store_wf_store' _ _ hext
    obtain ⟨_, _, hpt, hsub⟩ := ais_single_typing_inversion _ _ _ t1s t2s htype
    unfold ai_principal_typing at hpt
    obtain ⟨ts, c', heq, hframe, hexpr, hlen⟩ := hpt
    rw [heq] at hsub
    cases hframe with
    | mk_Frame_ok vals minst tl C0 hminst hlenv hvalsf _ hwfC0 _ hwfloc =>
      cases hexpr with
      | mk_Expr_ok2 _ _ _ hbody _ hwfc'' _ =>
        have hC0loc : C0.LOCALS = [] := inst_t_context_local_empty _ minst C0 hminst
        have hvals_in : Vals_ok s0 vals tl := ⟨hlenv, hvalsf⟩
        -- the frame body's context: locals-only context ++ module context, with RETURN set
        have hvals_in' : Vals_ok s0 vals ({ (({
            TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
            LOCALS := tl, LABELS := [], RETURN := none } : context) ++ C0) with
              RETURN := some (list.mk_list ts) } : context).LOCALS := by
          show Vals_ok s0 vals ((({
            TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
            LOCALS := tl, LABELS := [], RETURN := none } : context) ++ C0).LOCALS)
          rw [locals_append_eq tl C0 hC0loc]; exact hvals_in
        have him_in : inst_match C0 ({ (({
            TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
            LOCALS := tl, LABELS := [], RETURN := none } : context) ++ C0) with
              RETURN := some (list.mk_list ts) } : context) :=
          inst_match_locals_append tl C0
        have hminst' := Extend_store_moduleinst _ _ _ _ hext hminst
        have hbody' := ih s0 _ ais s0' fi' ais' C0 _ [] ts rfl rfl hwf1 hwf2 hsok hsok' hext hminst hminst'
          hvals_in' him_in hbody
        -- the inner step leaves the frame's module alone and keeps its locals well-typed
        have hmod := reduce_inst_unchanged _ _ ais s0' fi' ais' hinner
        have hloc := t_preservation_vs_type _ _ ais s0' fi' ais' C0 _ [] ts hinner hsok hext hminst
          hvals_in' him_in hbody
        have hloc' : Vals_ok s0' fi'.LOCALS tl := by
          rw [← locals_append_eq tl C0 hC0loc]; exact hloc
        obtain ⟨hlen', hvals'⟩ := hloc'
        have hmi'' : Moduleinst_ok s0' fi'.MODULE C0 := by rw [← hmod]; exact hminst'
        have hframe' : Frame_ok s0' fi' (({
            TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
            LOCALS := tl, LABELS := [], RETURN := none } : context) ++ C0) :=
          Frame_ok.mk_Frame_ok s0' fi'.LOCALS fi'.MODULE tl C0 hmi'' hlen' hvals' hwfS' hwfC0
            (wf_config_wf_frame hwf2) hwfloc
        have hexpr' := Expr_ok2.mk_Expr_ok2 s0' _ ais' ts hbody' hwfS' hwfc'' (wf_config_ais hwf2)
        have hwfF : wf_admininstr (admininstr.FRAME_ n fi' ais') := wf_config_ais hwfc2 _ (by simp)
        exact construct_ais_subtyping _ _ _ [] ts t1s t2s
          (construct_ais_typing_single _ _ _ [] ts
            (Instr_ok2.Instr_ok2_frame s0' C' n fi' ais' ts _ hframe' hexpr' hwfS' hwfC'
              (wf_context_app _ _ hwfloc hwfC0) hwfF (wf_context_return_only _) hlen.symm)) hsub
  case ctxt_instrs z vals ais ais1 z' ais' _ _ hwf1 hwf2 ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ hsok hsok' hext hmi hmi' hvals him htype
    injection h1 with hz1 hais1
    injection h2 with hz2 hais2
    subst hz1 hz2 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    have hwfS' := Extend_store_wf_store' _ _ hext
    obtain ⟨x1, hV, hrest⟩ := ais_composition_typing _ _ _ _ t1s t2s htype
    obtain ⟨x2, hA, hA1⟩ := ais_composition_typing _ _ ais ais1 x1 t2s hrest
    have hA' := ih s f ais s' f' ais' C C' x1 x2 rfl rfl hwf1 hwf2 hsok hsok' hext hmi hmi' hvals him hA
    obtain ⟨vts, hsubV, hvok⟩ := ais_vals_typing_inversion _ _ vals t1s x1 hV
    have hV' := construct_ais_vals _ C' vals t1s x1 vts hwfC' hwfS' hsubV (Extend_store_vals _ _ vts vals hext hvok)
    have hA1' := Extend_store_ais _ _ _ _ _ hext hsok hsok' hA1
    exact construct_ais_compose _ _ _ _ t1s x1 t2s hV' (construct_ais_compose _ _ _ _ x1 x2 t2s hA' hA1')
  case local_set z v x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (ais_args1_typing _ _ _ _ [] t1s t2s (inv_val_arg _ _ v) (inv_local_set _ _ x) htype)⟩
  case global_set z v x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (ais_args1_typing _ _ _ _ [] t1s t2s (inv_val_arg _ _ v) (inv_global_set _ _ x) htype)⟩
  case table_set_trap =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact construct_ais_trap _ C' _ hwfC' (Extend_store_wf_store' _ _ hext)
  case table_set_val z i r x _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (ais_args2_typing _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ numtype.I32 i) (inv_ref_arg _ _ r) (inv_table_set _ _ x) htype)⟩
  case table_grow_succeed z r k x _ _ _ _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact const_I32_result _ C' _ t1s t2s (wf_const_num (wf_config_ais hwfc2 _ (by simp))) hwfC'
      (Extend_store_wf_store' _ _ hext) (ais_args2_typing _ _ _ _ _ [valtype.I32] t1s t2s (inv_ref_arg _ _ r) (inv_const_arg _ _ numtype.I32 _) (inv_table_grow _ _ x) htype)
  case table_grow_fail z r k x _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact const_I32_result _ C' _ t1s t2s (wf_const_num (wf_config_ais hwfc2 _ (by simp))) hwfC'
      (Extend_store_wf_store' _ _ hext) (ais_args2_typing _ _ _ _ _ [valtype.I32] t1s t2s (inv_ref_arg _ _ r) (inv_const_arg _ _ numtype.I32 _) (inv_table_grow _ _ x) htype)
  case elem_drop z x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (inv_elem_drop _ _ x t1s t2s htype)⟩
  case store_num_trap =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact construct_ais_trap _ C' _ hwfC' (Extend_store_wf_store' _ _ hext)
  case store_num_val z i nt c ao _ _ _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (ais_args2_typing _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ numtype.I32 i) (inv_const_arg _ _ nt c) (inv_store_none _ _ nt ao) htype)⟩
  case store_pack_trap =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact construct_ais_trap _ C' _ hwfC' (Extend_store_wf_store' _ _ hext)
  case store_pack_val z i v_Inn c k ao _ _ _ _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (ais_args2_typing _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ numtype.I32 i) (inv_const_arg _ _ _ c) (inv_store_pack _ _ _ k ao) htype)⟩
  case vstore_oob =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact construct_ais_trap _ C' _ hwfC' (Extend_store_wf_store' _ _ hext)
  case vstore_val =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    exact Step__vstore_preserves _ _ C' _ _ _ _ htype (Extend_store_wf_store' _ _ hext)
  case vstore_lane_oob =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact construct_ais_trap _ C' _ hwfC' (Extend_store_wf_store' _ _ hext)
  case vstore_lane_val =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    exact Step__vstore_lane_preserves _ _ C' _ _ _ _ _ _ htype (Extend_store_wf_store' _ _ hext)
  case memory_grow_succeed =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact const_I32_result _ C' _ t1s t2s (wf_const_num (wf_config_ais hwfc2 _ (by simp))) hwfC'
      (Extend_store_wf_store' _ _ hext) (ais_args1_typing _ _ _ _ [valtype.I32] t1s t2s (inv_const_arg _ _ numtype.I32 _) (inv_memory_grow _ _) htype)
  case memory_grow_fail =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact const_I32_result _ C' _ t1s t2s (wf_const_num (wf_config_ais hwfc2 _ (by simp))) hwfC'
      (Extend_store_wf_store' _ _ hext) (ais_args1_typing _ _ _ _ [valtype.I32] t1s t2s (inv_const_arg _ _ numtype.I32 _) (inv_memory_grow _ _) htype)
  case data_drop z x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (inv_data_drop _ _ x t1s t2s htype)⟩
```

**Signature.** Same `_aux` shape as every other node in the primer's §0.8: fully general `c1 c2 : config` plus equality premises. What's new here versus the smaller `_aux`s is the sheer number of hypotheses the goal carries — `wf_config` of *both* sides, `Store_ok` of *both* sides, `Extend_store` between them, `Moduleinst_ok` of *both* stores against the *same* unchanging context, `Vals_ok` for the locals, `inst_match`, and the pre-typing — because by this point in the proof (recall file `01`'s `t_preservation`), every other piece of the puzzle has already been established by the other children, and this is the one case-split that actually needs all of them simultaneously.

**Proof sketch.** Three groups, matching `Step`'s 23 constructors one-to-one:
1. **`pure`/`read`** dispatch straight to `t_pure_preservation` (§7a below) and `t_read_preservation` (file `08`) after peeling the config equalities — all the real casework for these two lives there, not here.
2. **`ctxt_label`/`ctxt_frame`/`ctxt_instrs`** recurse through the induction hypothesis `ih`, exactly as in files `02` and `05`'s `_aux`s: invert the wrapping instruction's principal type, recurse on the shorter inner sequence, then re-wrap the result in a fresh `Instr_ok2.label`/`Instr_ok2_frame`/sequencing derivation. `ctxt_frame` is the most involved of the three because it's where `t_preservation_vs_type` (file `05`) and `reduce_inst_unchanged` (file `03`) get invoked *again*, locally, to re-derive `Frame_ok` for the frame sitting inside the stepped `FRAME_` marker.
3. **Every store-writing rule** (`local_set` through `data_drop`) retypes its reduct directly and cheaply, because every store-writing rule's reduct is either `[]` (typed via `ais_empty_typing`, after inverting the premise's typing with the matching `inv_*`/`ais_args*_typing` helper to get a subtyping fact) or one `CONST I32 _` value (typed via `const_I32_result`) — **this is exactly "the reduct is `[]` or a constant, typed directly"** from the diagram. The two SIMD-store cases (`vstore_val`, `vstore_lane_val`) are the only two that don't inline this and instead call the dedicated `Step__vstore_preserves`/`Step__vstore_lane_preserves` helper lemmas (defined earlier in the file, around [TypePreservation.lean:637-670](../../../../../src/test-lean-claude/TypePreservation.lean#L637-L670)) — purely because their typing-inversion step is more involved (three-instruction sequences, not two), not because the underlying logic differs.

## 7a. `t_pure_preservation`

**Plain-English summary.** Type preservation for the 54 store-independent, frame-independent rules — arithmetic, control-flow bookkeeping, `select`/`if`/`local.tee`, trap propagation, the full SIMD pure-op family. Each rule gets its own tiny dedicated lemma (`Step_pure__<rule>_preserves`), proved earlier in the file; this theorem is purely the dispatch table.

**Code — the complete 54-case theorem** — [TypePreservationPure.lean:1854-1974](../../../../../src/test-lean-claude/TypePreservationPure.lean#L1854-L1974):
```lean
/-- Rocq `type_preservation_pure.v` `t_pure_preservation` — the master theorem for this
    file. `Qed` upstream, SIMD cases included; proved here (bundle18) by dispatching every
    `Step_pure` case to the per-rule lemmas above, with the reduct's well-formedness from the
    generated `Step_pure_is_wf` (as in Rocq). -/
theorem t_pure_preservation (v_s : store) (v_ais v_ais' : List admininstr) (v_C : context) (tf : functype) :
    Instrs_ok2 v_s v_C v_ais tf → Step_pure v_ais v_ais' → Instrs_ok2 v_s v_C v_ais' tf := by
  intro h hstep
  obtain ⟨hwfC, hwfS, hwfais⟩ := ainstrs_ok_context_store_wf v_s v_C v_ais tf h
  -- well-formedness of the reduct, from the generated `Step_pure_is_wf` (as in Rocq)
  have hwf' := Step_pure_is_wf v_ais v_ais' hwfais hstep
  have hs := hstep
  cases hstep
  case unreachable =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case nop =>
    exact Step_pure__nop_preserves v_s v_C tf h hs
  case drop =>
    exact Step_pure__drop_preserves v_s v_C _ tf h hs
  case select_true =>
    exact Step_pure__select_true_preserves v_s v_C _ _ _ _ tf h hs
  case select_false =>
    exact Step_pure__select_false_preserves v_s v_C _ _ _ _ tf h hs
  case if_true =>
    exact Step_pure__if_true_preserves v_s v_C _ _ _ _ tf h hs
  case if_false =>
    exact Step_pure__if_false_preserves v_s v_C _ _ _ _ tf h hs
  case label_vals =>
    exact Step_pure__label_vals_preserves v_s v_C _ _ _ tf h hs
  case br_zero _ _ _ _ _ hn =>
    exact Step_pure__br_zero_preserves v_s v_C _ _ _ _ _ tf h hn.symm
  case br_succ =>
    exact Step_pure__br_succ_preserves v_s v_C _ _ _ _ _ tf h hs
  case br_if_true =>
    exact Step_pure__br_if_true_preserves v_s v_C _ _ tf h hs
  case br_if_false =>
    exact Step_pure__br_if_false_preserves v_s v_C _ _ tf h hs
  case br_table_lt _ _ _ hlt _ =>
    exact Step_pure__br_table_lt_preserves v_s v_C _ _ _ tf h hs hlt
  case br_table_ge =>
    exact Step_pure__br_table_ge_preserves v_s v_C _ _ _ tf h hs
  case frame_vals =>
    exact Step_pure__frame_vals_preserves v_s v_C _ _ _ tf h hs
  case return_frame _ _ _ _ _ hn =>
    exact Step_pure__return_frame_preserves v_s v_C _ _ _ _ _ tf h hs hn.symm
  case return_label =>
    exact Step_pure__return_label_preserves v_s v_C _ _ _ _ tf h hs
  case trap_vals =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case trap_label =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case trap_frame =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case unop_val =>
    exact Step_pure__unop_val_preserves v_s v_C _ _ _ _ tf h hs (hwf' _ (by simp))
  case unop_trap =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case binop_val =>
    exact Step_pure__binop_val_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case binop_trap =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case testop =>
    exact Step_pure__testop_preserves v_s v_C _ _ _ _ tf h hs (hwf' _ (by simp))
  case relop =>
    exact Step_pure__relop_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case cvtop_val =>
    exact Step_pure__cvtop_val_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case cvtop_trap =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case ref_is_null_true _ rt heq =>
    subst heq
    exact Step_pure__ref_is_null_true_preserves v_s v_C rt tf h hs
  case ref_is_null_false =>
    exact Step_pure__ref_is_null_false_preserves v_s v_C _ tf h hs
  case vvunop =>
    exact Step_pure__vvunop_preserves v_s v_C _ _ _ tf h hs (hwf' _ (by simp))
  case vvbinop =>
    exact Step_pure__vvbinop_preserves v_s v_C _ _ _ _ tf h hs (hwf' _ (by simp))
  case vvternop =>
    exact Step_pure__vvternop_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vvtestop =>
    exact Step_pure__vvtestop_preserves v_s v_C _ _ _ tf h hs (hwf' _ (by simp))
  case vunop =>
    exact Step_pure__vunop_preserves v_s v_C _ _ _ _ tf h hs (hwf' _ (by simp))
  case vunop_trap =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case vbinop_val =>
    exact Step_pure__vbinop_val_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vbinop_trap =>
    exact construct_ais_trap v_s v_C tf hwfC hwfS
  case vtestop_true =>
    exact Step_pure__vtestop_preserves v_s v_C _ _ _ _ tf h hs (hwf' _ (by simp))
  case vtestop_false =>
    exact Step_pure__vtestop_preserves v_s v_C _ _ _ _ tf h hs (hwf' _ (by simp))
  case vrelop =>
    exact Step_pure__vrelop_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vshiftop =>
    exact Step_pure__vshiftop_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vbitmask =>
    exact Step_pure__vbitmask_preserves v_s v_C _ _ _ tf h hs (hwf' _ (by simp))
  case vswizzle =>
    exact Step_pure__vswizzle_preserves v_s v_C _ _ _ _ tf h hs (hwf' _ (by simp))
  case vshuffle =>
    exact Step_pure__vshuffle_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vsplat =>
    exact Step_pure__vsplat_preserves v_s v_C _ _ _ _ tf h hs (hwf' _ (by simp))
  case vextract_lane_num =>
    exact Step_pure__vextract_lane_num_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vextract_lane_pack =>
    exact Step_pure__vextract_lane_pack_preserves v_s v_C _ _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vreplace_lane =>
    exact Step_pure__vreplace_lane_preserves v_s v_C _ _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vextunop =>
    exact Step_pure__vextunop_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vextbinop =>
    exact Step_pure__vextbinop_preserves v_s v_C _ _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vnarrow =>
    exact Step_pure__vnarrow_preserves v_s v_C _ _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case vcvtop =>
    exact Step_pure__vcvtop_preserves v_s v_C _ _ _ _ _ tf h hs (hwf' _ (by simp))
  case local_tee =>
    exact Step_pure__local_tee_preserves v_s v_C _ _ tf h hs
```

**Signature.** `Instrs_ok2 v_s v_C v_ais tf → Step_pure v_ais v_ais' → Instrs_ok2 v_s v_C v_ais' tf` — note there's no store or frame anywhere in sight, matching `Step_pure`'s own signature (primer §0.7): pure reduction never touches either, so neither the hypothesis nor the conclusion needs to mention them.

**Proof sketch.** `cases hstep` splits into all 54 `Step_pure` constructors. Every genuine "trap" constructor (`unreachable`, `trap_vals`, `trap_label`, `trap_frame`, `unop_trap`, `binop_trap`, `cvtop_trap`, `vunop_trap`, `vbinop_trap`) is dismissed identically by `construct_ais_trap`, since `TRAP` types at *any* signature (primer §0.5's `Instr_ok2.trap`). Every other case calls exactly one dedicated `Step_pure__<name>_preserves` lemma, passing through the original typing `h`, the `Step_pure` fact `hs`, and — for anything whose result is a fresh numeric/vector constant rather than a syntactic copy — a well-formedness fact for that constant pulled from `Step_pure_is_wf` (`hwf'`). A representative one of those 54 per-rule lemmas, in full — [TypePreservationPure.lean:28-50](../../../../../src/test-lean-claude/TypePreservationPure.lean#L28-L50):
```lean
/-- Rocq `type_preservation_pure.v:41` `Step_pure__nop_preserves`. Rocq's proof is a
    5-tactic-macro pipeline (`resolve_wfness`/`invert_ais_typing`/`resolve_all_pt`/
    `resolve_subtyping`/`construct_ais_typing`, all pure Ltac automation from
    `helper_tactics.v`, not ported per project convention); the underlying content is:
    `[NOP]`'s only principal type is `[]->[]` (`ai_principal_typing`'s `NOP` case), so the
    typing hypothesis reduces to `instrtype_sub([]->[])v_ft`, and `[]` types at any such
    `v_ft` via `ais_empty_typing` + `instrtype_sub_empty`. -/
theorem Step_pure__nop_preserves (v_S : store) (v_C : context) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.NOP] v_ft → Step_pure [admininstr.NOP] [] →
    Instrs_ok2 v_S v_C [] v_ft := by
  intro h _
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  obtain ⟨t1s_sup, t2s_sub, hprincipal, hsub⟩ := ais_single_typing_inversion v_S v_C admininstr.NOP t1s t2s h
  unfold ai_principal_typing at hprincipal
  unfold mkFunctype at hprincipal
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hprincipal
  obtain ⟨e1, e2⟩ := hprincipal
  subst e1; subst e2
  have hrsub : ResulttypeSub t1s t2s := instrtype_sub_empty t1s t2s hsub
  obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C [admininstr.NOP] (mkFunctype t1s t2s) h
  exact (ais_empty_typing v_S v_C t1s t2s).mpr ⟨hwfC, hwfS, hrsub⟩
```
`[NOP]`'s only possible principal type is `[] → []` (read off by `ais_single_typing_inversion`/`ai_principal_typing`), so the typing hypothesis collapses to "`t1s` subtypes into `t2s` via the empty instruction sequence" — which is exactly what `[]` itself satisfies, by `ais_empty_typing`. Every other `_preserves` lemma is this same move, specialized to its own rule's principal type (e.g. `Step_pure__drop_preserves`, one instruction longer, inverts `[v, DROP]`'s sequencing first to separate the value's `[]→[t]` typing from `DROP`'s own `[t']→[]]`, then composes the two subtyping facts).

---

*Next: [08-t-read-preservation.md](08-t-read-preservation.md) — `t_read_preservation`, the 47-case `Step_read` dispatcher (§7b in the diagram).*

# 6. `t_preservation_type`

*(Previous: [05-t-preservation-vs-type.md](05-t-preservation-vs-type.md). Next: [07-t-preservation-type-aux.md](07-t-preservation-type-aux.md).)*

**Plain-English summary. The central preservation lemma for the whole `Step` relation**, per its own doc comment — the instruction sequence itself stays well-typed at the *same* `t1s → t2s` arrow type across one step (and, unlike `t_preservation_vs_type`, this one already needs the store-extension and well-formedness facts as explicit hypotheses rather than deriving them internally). It's the thinnest possible wrapper around `t_preservation_type_aux` (next file), existing only to supply that `_aux`'s one extra hypothesis — well-formedness of the post-config — from the generated `Step_is_wf`.

**Code** — [TypePreservation.lean:2675-2693](../../../../../src/test-lean-claude/TypePreservation.lean#L2675-L2693):
```lean
/-- Rocq `type_preservation.v:3137` `t_preservation_type`. **The central preservation
    lemma for the whole `Step` relation** (subsumes `t_read_preservation`). `Qed` in Rocq,
    SIMD cases included (the "`Admitted`, SIMD gap" note this file used to carry described
    the pre-`a8b585cdb` Rocq and was corrected in bundle18). Dispatches `Step_pure` to
    `t_pure_preservation` and `Step_read` to `t_read_preservation`; the case analysis is in
    `t_preservation_type_aux`. Like Rocq, it takes the reduct's well-formedness from the
    generated `Step_is_wf`. -/
theorem t_preservation_type (v_s : store) (v_f : frame) (v_ais : List admininstr) (v_s' : store)
    (v_f' : frame) (v_ais' : List admininstr) (v_C v_C' : context) (t1s t2s : List valtype) :
    wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →
    Step (config.mk_config (state.mk_state v_s v_f) v_ais) (config.mk_config (state.mk_state v_s' v_f') v_ais') →
    Store_ok v_s → Store_ok v_s' → Extend_store v_s v_s' →
    Moduleinst_ok v_s v_f.MODULE v_C → Moduleinst_ok v_s' v_f.MODULE v_C →
    Vals_ok v_s v_f.LOCALS v_C'.LOCALS → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s) → Instrs_ok2 v_s' v_C' v_ais' (mkFunctype t1s t2s) := by
  intro hwf hstep hsok hsok' hext hmi hmi' hvals him htype
  -- well-formedness of the reduct, from the generated `Step_is_wf` (as in Rocq)
  exact t_preservation_type_aux _ _ hstep v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' t1s t2s rfl rfl
    hwf (Step_is_wf _ _ _ hwf hsok hstep) hsok hsok' hext hmi hmi' hvals him htype
```

**Signature.** Notice it already requires *both* `Store_ok v_s` and `Store_ok v_s'` plus `Extend_store v_s v_s'` as hypotheses (unlike `t_preservation_vs_type`, which only needed `Extend_store` and derived everything else) — this lemma is meant to be called *after* `store_extension_reduce` has already run, not instead of it. Likewise `Moduleinst_ok` is required for *both* `v_s` (against `v_f.MODULE`) and `v_s'` (against the *same* `v_f.MODULE`, since file `03` already told us the module instance itself doesn't change).

**Proof sketch.** Literally one step: derive `wf_config` of the post-config from `Step_is_wf` (primer §0.4), then hand everything to `t_preservation_type_aux`, filling in its two config-equality obligations with `rfl` (primer §0.8's pattern, one more time).

---
*Next: [07-t-preservation-type-aux.md](07-t-preservation-type-aux.md).*

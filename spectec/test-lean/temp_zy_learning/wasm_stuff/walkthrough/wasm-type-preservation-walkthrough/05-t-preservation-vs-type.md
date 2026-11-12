# 5. `t_preservation_vs_type` (and its two layers underneath)

*(Previous: [04-extend-store-moduleinst.md](04-extend-store-moduleinst.md). Next: [06-t-preservation-type.md](06-t-preservation-type.md).)*

**Plain-English summary.** The frame's **locals** stay well-typed across one step. (`vs_type` = "value-stack type," inherited naming from Rocq, even though what's actually tracked here is locals, not the operand stack — the operand stack's typing is handled by `t_preservation_type` in the next file instead.) This is built in three layers, exactly the primer's §0.8 `_aux` pattern: a fully-general induction (`'_aux`), a thin store-fixed wrapper (`'`), and the final version that also transports across store growth.

**Code, layer 1 (`t_preservation_vs_type'_aux`)** — [TypePreservation.lean:112-212](../../../../../src/test-lean-claude/TypePreservation.lean#L112-L212):
```lean
/-- Generalized form of `t_preservation_vs_type'` below (same `remember`/
    `generalize dependent` encoding as `reduce_inst_unchanged_aux`). Of `Step`'s
    23 rules, 20 leave the frame alone outright — only `local_set` touches
    `LOCALS`, and only the two congruence rules (`ctxt_label`, `ctxt_instrs`)
    need the induction hypothesis; `ctxt_frame` changes only the *inner* frame.
    Rocq compresses the same case split into one `induction ...; try (...)`
    script backed by its `invert_ais_typing`/`resolve_all_pt` tactics. -/
private theorem t_preservation_vs_type'_aux (c1 c2 : config) (h : Step c1 c2) :
    ∀ (s : store) (f : frame) (ais : List admininstr) (s' : store) (f' : frame)
      (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype),
      c1 = config.mk_config (state.mk_state s f) ais →
      c2 = config.mk_config (state.mk_state s' f') ais' →
      Store_ok s → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS → inst_match C C' →
      Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s f'.LOCALS C'.LOCALS := by
  induction h
  case ctxt_label z vn i0 al z' al' _ _ _ ih =>
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 hsok hmi hvals him htype
    injection h1 with hz1 hais
    injection h2 with hz2 _
    subst hz1
    rw [← hais] at htype
    obtain ⟨_, _, hpt, _⟩ :=
      ais_single_typing_inversion s C' (admininstr.LABEL_ vn i0 al) t1s t2s htype
    unfold ai_principal_typing at hpt
    obtain ⟨ts, ts', _, _, _, hbody⟩ := hpt
    exact ih s f al s' f' al' C (prepend_label C' (list.mk_list ts')) [] ts rfl (by rw [hz2])
      hsok hmi hvals (construct_inst_prepend_label C C' (list.mk_list ts') him) hbody
  case ctxt_instrs z vl al al1 z' al' _ _ _ _ ih =>
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 hsok hmi hvals him htype
    injection h1 with hz1 hais
    injection h2 with hz2 _
    subst hz1
    rw [← hais] at htype
    obtain ⟨tm, _, hrest⟩ := ais_composition_typing s C' _ (al ++ al1) t1s t2s htype
    obtain ⟨tm2, hal, _⟩ := ais_composition_typing s C' al al1 tm t2s hrest
    exact ih s f al s' f' al' C C' tm tm2 rfl (by rw [hz2]) hsok hmi hvals him hal
  case ctxt_frame =>
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 _ _ hvals _ _
    injection h1 with hz1 _
    injection h2 with hz2 _
    injection hz1 with _ e1
    injection hz2 with _ e2
    subst e1
    subst e2
    exact hvals
  case local_set z v x =>
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 _ _ hvals _ htype
    injection h1 with hz1 hais
    injection h2 with hz2 _
    subst hz1
    simp only [with_local] at hz2
    injection hz2 with _ hf
    subst hf
    rw [← hais] at htype
    -- the value being written has exactly the local's declared type
    have heqs : [admininstr_val v, admininstr.LOCAL_SET x]
        = [admininstr_val v] ++ [admininstr.LOCAL_SET x] := rfl
    rw [heqs] at htype
    obtain ⟨t3s, h_ls, h_v⟩ :=
      ais_seq_typing_inversion s C' _ (admininstr_val v) t1s t2s htype
    obtain ⟨tv, hsub_v, hvok⟩ := ais_single_val_typing_inversion s C' v t1s t3s h_v
    obtain ⟨_, _, hls_pt, hsub_ls⟩ :=
      ais_single_typing_inversion s C' (admininstr.LOCAL_SET x) t3s t2s h_ls
    unfold ai_principal_typing at hls_pt
    obtain ⟨t, hls_eq, hlookup⟩ := hls_pt
    unfold mkFunctype at hls_eq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hls_eq
    obtain ⟨el1, el2⟩ := hls_eq
    subst el1; subst el2
    obtain ⟨_, hrsub⟩ := instrtype_sub_compose_eq [] [tv] [t] [] t1s t3s t2s hsub_v hsub_ls rfl
    have hnb : Forall (fun u => u ≠ valtype.BOT) [tv] := by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rw [hu]
      exact Val_ok_non_bot s v tv hvok
    have heqt := resulttype_sub_non_bot [tv] [t] hnb hrsub
    injection heqt with et _
    have hget : C'.LOCALS[proj_uN_0 x]! = t := by
      rw [List.getElem!_eq_getElem?_getD, hlookup]; rfl
    -- now transport the locals typing across the single-slot update
    obtain ⟨hlen, hall⟩ := hvals
    refine ⟨?_, ?_⟩
    · show C'.LOCALS.length = (f.LOCALS.modify (proj_uN_0 x) (fun _ => v)).length
      rw [List.length_modify]
      exact hlen
    · intro p hp
      rcases mem_zip_modify_right _ C'.LOCALS f.LOCALS (proj_uN_0 x) p hp with hp' | ⟨h1', h2', _⟩
      · exact hall p hp'
      · show Val_ok s p.2 p.1
        rw [h1', h2', hget, ← et]
        exact hvok
  all_goals (
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 _ _ hvals _ _
    injection h1 with hz1 _
    injection h2 with hz2 _
    subst hz1
    try simp only [with_global, with_table, with_tableinst, with_elem, with_mem,
      with_meminst, with_data] at hz2
    injection hz2 with _ hf
    subst hf
    exact hvals)
```

**Code, layer 2 (`t_preservation_vs_type'`)** — [TypePreservation.lean:214-222](../../../../../src/test-lean-claude/TypePreservation.lean#L214-L222):
```lean
/-- Rocq `type_preservation.v:53` `t_preservation_vs_type'`. Locals stay well-typed under
    one `Step` (store held fixed / pre-store-extension). -/
theorem t_preservation_vs_type' (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Store_ok s → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS → inst_match C C' →
    Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s f'.LOCALS C'.LOCALS :=
  fun hstep hsok hmi hvals him htype =>
    t_preservation_vs_type'_aux _ _ hstep s f ais s' f' ais' C C' t1s t2s rfl rfl hsok hmi hvals him htype
```

**Code, layer 3 — the actual diagram node (`t_preservation_vs_type`)** — [TypePreservation.lean:224-234](../../../../../src/test-lean-claude/TypePreservation.lean#L224-L234):
```lean
/-- Rocq `type_preservation.v:107` `t_preservation_vs_type`. Composition:
    `t_preservation_vs_type'` then `store_extension_vals` to transport across store
    extension. -/
theorem t_preservation_vs_type (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Store_ok s → Extend_store s s' → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS →
    inst_match C C' → Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s' f'.LOCALS C'.LOCALS := by
  intro hstep hsok hext hmi hvals him htype
  exact Extend_store_vals s s' C'.LOCALS f'.LOCALS hext
    (t_preservation_vs_type' s f ais s' f' ais' C C' t1s t2s hstep hsok hmi hvals him htype)
```

**Signature.** The final version adds exactly one thing beyond layer 2: `Extend_store s s'`, and its conclusion is `Vals_ok s' f'.LOCALS C'.LOCALS` — typed against the **new** store `s'`, not the old one `s`. That upgrade (old-store typing → new-store typing, given the store only grew) is the whole reason this layer exists on top of `'`.

**Proof sketch.** Layer 3 is one line: call layer 2 to get the locals typed against the *old* store `s`, then push that through `Extend_store_vals` (a one-off lemma, not itself in the diagram, that lifts `Val_ok`/`Vals_ok` across store growth — unsurprising, since growth never invalidates an existing value's type). All the real content is in layer 1's induction over `Step`'s 23 constructors: congruence rules recurse after peeling one level of typing (same `ais_single_typing_inversion`/`ais_composition_typing` moves you saw in file `02`'s `_aux`); `ctxt_frame` is immediate, because it changes only the frame *nested inside* the stepped `FRAME_`, not the ambient `f`; every store-writing rule except `local_set` is dismissed by the `all_goals` block, since none of them touch `LOCALS` (confirmed by unfolding every `with_*` updater and finding the frame untouched); and `local_set` is the one substantive case — it inverts the typing of `[v, LOCAL_SET x]` to learn the written value's type exactly matches local `x`'s declared type (routing through `Val_ok_non_bot`/`resulttype_sub_non_bot` to rule out the value having degenerated to `BOT`), then transports the old `Vals_ok` fact across the single-slot `List.modify` via `mem_zip_modify_right` (the untouched slots keep their old `Val_ok` proof; the touched slot gets the freshly-derived one).

---
*Next: [06-t-preservation-type.md](06-t-preservation-type.md).*

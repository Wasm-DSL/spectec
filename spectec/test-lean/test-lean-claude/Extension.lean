import «wasm2.0»

/-!
# Store/instance extension: reflexivity

This file is part of `test-lean-claude/`, an attempt to translate the
partially-completed Rocq and Isabelle Wasm 2.0 type-safety proofs into Lean,
against the SpecTec-generated `wasm2.0.lean` model (one directory up).
See `test-lean-claude/PROGRESS.md` for the overall status and source-branch
provenance of every lemma in this development.

Source material for this file:
* Rocq (branch `rocq-backend-proof`, `spectec/test-rocq/theories/extension_lemmas.v`):
  `extend_globalinst_refl_0`, `extend_meminst_refl_0`, `extend_tableinst_refl_0`,
  `extend_eleminst_refl_0`, `extend_datainst_refl_0`, `extend_funcinst_refl_0`
  (single-instance versions, lines ~926-1006), and the store-wide versions
  `extend_global_refl` .. `Extend_store_refl` (lines ~1538-1627), which lift the
  single-instance lemmas across a `holds_upto`-bounded list index.
* Isabelle (branch `isabelle-mech-backend`,
  `spectec/isabelle_type_safety_proof/Properties.thy`, read in full — 165 lines):
  `func_extension_refl`, `global_extension_refl`, `mem_extension_refl`,
  `tab_extension_refl`, `elem_extension_refl`, `data_extension_refl`,
  `store_extension_refl` (lines 6-81).

Both source developments prove that the `Extend_*` "grows monotonically" order
on stores/instances is reflexive on well-formed values. Neither source
development proves *transitivity* of `Extend_*` anywhere in the fetched
files, so none is attempted here either.

The Lean backend represents the store-wide relation `Extend_store` with plain
`Forall _ (List.range n)` index bounds (see `wasm2.0.lean:12460-12482`) rather
than Rocq/Isabelle's custom `holds_upto` predicate, so the per-field lifting
lemmas below (`forall_range_lt`, `forall_range_refl`,
`forall_range_refl_noWf`) are new plumbing with no direct Rocq/Isabelle
counterpart, needed only to bridge that representational difference.
-/

namespace TestLeanClaude

/-- Rocq: `extend_globalinst_refl_0` (extension_lemmas.v:926).
    Isabelle: `global_extension_refl` (Properties.thy:11). -/
theorem extend_globalinst_refl {g : globalinst} (h : wf_globalinst g) :
    Extend_globalinst g g := by
  obtain ⟨ty, v⟩ := g
  obtain ⟨v_mut, t⟩ := ty
  exact Extend_globalinst.mk_Extend_globalinst v_mut t v v (Or.inr rfl) h h

/-- Rocq: `extend_funcinst_refl_0` (extension_lemmas.v:997).
    Isabelle: `func_extension_refl` (Properties.thy:6). -/
theorem extend_funcinst_refl {f : funcinst} (h : wf_funcinst f) :
    Extend_funcinst f f := by
  obtain ⟨ft, mm, fc⟩ := f
  exact Extend_funcinst.mk_Extend_funcinst ft mm fc h

/-- Rocq: `extend_datainst_refl_0` (extension_lemmas.v:986).
    Isabelle: `data_extension_refl` (Properties.thy:69). -/
theorem extend_datainst_refl {d : datainst} (h : wf_datainst d) :
    Extend_datainst d d := by
  obtain ⟨bs⟩ := d
  exact Extend_datainst.mk_Extend_datainst bs bs (Or.inl rfl) h h

/-- Rocq: `extend_eleminst_refl_0` (extension_lemmas.v:976) — takes no
    well-formedness hypothesis, matching the fact that no `wf_eleminst`
    predicate exists (neither here nor in Rocq/Isabelle's `Extend_eleminst`).
    Isabelle: `elem_extension_refl` (Properties.thy:65). -/
theorem extend_eleminst_refl (el : eleminst) : Extend_eleminst el el := by
  obtain ⟨rt, refs⟩ := el
  exact Extend_eleminst.mk_Extend_eleminst rt refs refs (Or.inl rfl)

/-- Rocq: `extend_tableinst_refl_0` (extension_lemmas.v:957).
    Isabelle: `tab_extension_refl` (Properties.thy:41). -/
theorem extend_tableinst_refl {tb : tableinst} (h : wf_tableinst tb) :
    Extend_tableinst tb tb := by
  obtain ⟨ty, refs⟩ := tb
  obtain ⟨lim, rt⟩ := ty
  obtain ⟨v_u32, u32_opt⟩ := lim
  obtain ⟨v_n⟩ := v_u32
  rcases u32_opt with _ | u32opt
  · exact Extend_tableinst.mk_Extend_tableinst v_n none rt refs v_n refs
      (Nat.le_refl v_n) (Nat.le_refl refs.length) h h
  · obtain ⟨n'⟩ := u32opt
    exact Extend_tableinst.mk_Extend_tableinst v_n (some n') rt refs v_n refs
      (Nat.le_refl v_n) (Nat.le_refl refs.length) h h

/-- Rocq: `extend_meminst_refl_0` (extension_lemmas.v:938).
    Isabelle: `mem_extension_refl` (Properties.thy:17). -/
theorem extend_meminst_refl {mi : meminst} (h : wf_meminst mi) :
    Extend_meminst mi mi := by
  obtain ⟨ty, bs⟩ := mi
  obtain ⟨lim⟩ := ty
  obtain ⟨v_u32, u32_opt⟩ := lim
  obtain ⟨v_n⟩ := v_u32
  rcases u32_opt with _ | u32opt
  · exact Extend_meminst.mk_Extend_meminst v_n none bs v_n bs
      (Nat.le_refl v_n) (Nat.le_refl bs.length) h h
  · obtain ⟨n'⟩ := u32opt
    exact Extend_meminst.mk_Extend_meminst v_n (some n') bs v_n bs
      (Nat.le_refl v_n) (Nat.le_refl bs.length) h h

/-- Bounds side-condition needed by `Extend_store`'s constructor: every index
    into `List.range l.length` is `< l.length`. No Rocq/Isabelle counterpart
    (see module doc comment). -/
theorem forall_range_lt {α : Type} (l : List α) :
    Forall (fun a => a < l.length) (List.range l.length) := by
  intro a ha
  exact List.mem_range.mp ha

/-- Lifts a single-instance reflexivity fact, plus a well-formedness `Forall`
    over a list, to the index-`Forall`-over-`List.range` shape `Extend_store`
    is stated with. No direct Rocq/Isabelle counterpart (see module doc
    comment); the closest analogues are Rocq's `holds_upto_all_strong'` +
    `extend_*_refl` and Isabelle's `list_all_length` step in
    `store_extension_refl`. -/
theorem forall_range_refl {α : Type} [Inhabited α] (l : List α) (P : α → Prop)
    (R : α → α → Prop) (hP : Forall P l) (hR : ∀ x, P x → R x x) :
    Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a ha
  have ha' : a < l.length := List.mem_range.mp ha
  have hmem : l[a]! ∈ l := by
    rw [getElem!_pos l a ha']
    exact List.getElem_mem ha'
  exact hR _ (hP _ hmem)

/-- As `forall_range_refl`, but for `Extend_eleminst`, which has no
    well-formedness side condition. -/
theorem forall_range_refl_noWf {α : Type} [Inhabited α] (l : List α)
    (R : α → α → Prop) (hR : ∀ x, R x x) :
    Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a _
  exact hR _

/-- Rocq: `Extend_store_refl` (extension_lemmas.v:1603), built from
    `extend_global_refl` .. `extend_data_refl` (lines 1538-1601).
    Isabelle: `store_extension_refl` (Properties.thy:73-81). -/
theorem extend_store_refl {s : store} (h : wf_store s) : Extend_store s s := by
  cases h with
  | store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas =>
    have hwf : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas
    exact Extend_store.mk_Extend_store _ _
      (forall_range_lt globals) (forall_range_lt globals)
      (forall_range_refl globals wf_globalinst Extend_globalinst hglobals
        (fun x hx => extend_globalinst_refl hx))
      (forall_range_lt mems) (forall_range_lt mems)
      (forall_range_refl mems wf_meminst Extend_meminst hmems
        (fun x hx => extend_meminst_refl hx))
      (forall_range_lt tables) (forall_range_lt tables)
      (forall_range_refl tables wf_tableinst Extend_tableinst htables
        (fun x hx => extend_tableinst_refl hx))
      (forall_range_lt funcs) (forall_range_lt funcs)
      (forall_range_refl funcs wf_funcinst Extend_funcinst hfuncs
        (fun x hx => extend_funcinst_refl hx))
      (forall_range_lt datas) (forall_range_lt datas)
      (forall_range_refl datas wf_datainst Extend_datainst hdatas
        (fun x hx => extend_datainst_refl hx))
      (forall_range_lt elems) (forall_range_lt elems)
      (forall_range_refl_noWf elems Extend_eleminst extend_eleminst_refl)
      hwf hwf

end TestLeanClaude

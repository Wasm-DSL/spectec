import «wasm2.0»

/-!
# Store extension under reduction (`store_extension_reduce`)

Source material:
* Rocq (branch `rocq-backend-proof`, `spectec/test-rocq/theories/type_preservation.v`,
  `store_extension_reduce`, lines ~224-1235) — the mature version: almost every
  case is proved (a handful of internal `admit.`s), driving Preservation.
* Isabelle (branch `isabelle-mech-backend`,
  `spectec/isabelle_type_safety_proof/Properties.thy:84-164`,
  `reduce_store_extension`) — an *induction on `Step`* with 23 cases, of which
  only `pure` is proved; all 22 others are bare `sorry`.

This file reproduces Isabelle's proof shape (induction on `Step`, one case per
constructor) against the Lean backend's `Step` relation
(`wasm2.0.lean:11106-11205`, 23 constructors — exact 1-1 correspondence with
Isabelle's case list, confirmed by name). Two cases are proved for real here
(`pure`, and — going one step further than either source development —
`read`, since a `Step_read` premise likewise leaves the `state` argument `z`
of `Step` completely unchanged on both sides, exactly as `pure` does; nothing
about the `read` case is actually harder than `pure`, it looks like Isabelle's
author simply didn't get to it). The three "congruence" cases
(`ctxt_label`/`ctxt_frame`/`ctxt_instrs`) reduce to their own induction
hypothesis with no extra work, since they too leave the running store
untouched outside of the nested sub-step. The remaining 18 cases are the ones
that actually mutate the store (`with_table`/`with_mem`/`with_meminst`/etc.)
and need real per-case semantic reasoning that has not been ported yet — they
are left `sorry`, same as in Isabelle, and are the natural next-step target
(Rocq's version has these mostly done and would be the reference to port from).

NOTE ON FILE STRUCTURE: this file duplicates `extend_store_refl` and its
dependencies from `Extension.lean` verbatim (down to `forall_range_lt` etc.)
rather than importing that file. `test-lean/lakefile.lean` (outside this
folder, so not editable per the task's safety constraints) only registers
`wasm2.0`/`custom_notation`/`typing_lemmas`/`ExtendedDeriveDecEq`/`sandbox_5`/
`sandbox_10` as buildable modules, so no `.olean` exists yet for anything
under `test-lean-claude/`, and `lake env lean <file>` cannot resolve an
`import` of a sibling file with no prebuilt `.olean` — confirmed empirically
(`unknown module prefix 'test-lean-claude'`). Every file in this folder is
therefore kept independently self-contained (only importing `wasm2.0.lean`
directly), accepting some duplication, rather than risk writing build
artifacts outside `test-lean-claude/`. See `logs/DECISIONS.md` for the full
account of this constraint.
-/

namespace TestLeanClaude

/-- Rocq: `extend_globalinst_refl_0` (extension_lemmas.v:926).
    Isabelle: `global_extension_refl` (Properties.thy:11).
    (Duplicated from `Extension.lean` — see file-header note.) -/
theorem extend_globalinst_refl {g : globalinst} (h : wf_globalinst g) :
    Extend_globalinst g g := by
  obtain ⟨ty, v⟩ := g
  obtain ⟨v_mut, t⟩ := ty
  exact Extend_globalinst.mk_Extend_globalinst v_mut t v v (Or.inr rfl) h h

theorem extend_funcinst_refl {f : funcinst} (h : wf_funcinst f) :
    Extend_funcinst f f := by
  obtain ⟨ft, mm, fc⟩ := f
  exact Extend_funcinst.mk_Extend_funcinst ft mm fc h

theorem extend_datainst_refl {d : datainst} (h : wf_datainst d) :
    Extend_datainst d d := by
  obtain ⟨bs⟩ := d
  exact Extend_datainst.mk_Extend_datainst bs bs (Or.inl rfl) h h

theorem extend_eleminst_refl (el : eleminst) : Extend_eleminst el el := by
  obtain ⟨rt, refs⟩ := el
  exact Extend_eleminst.mk_Extend_eleminst rt refs refs (Or.inl rfl)

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

theorem forall_range_lt {α : Type} (l : List α) :
    Forall (fun a => a < l.length) (List.range l.length) := by
  intro a ha
  exact List.mem_range.mp ha

theorem forall_range_refl {α : Type} [Inhabited α] (l : List α) (P : α → Prop)
    (R : α → α → Prop) (hP : Forall P l) (hR : ∀ x, P x → R x x) :
    Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a ha
  have ha' : a < l.length := List.mem_range.mp ha
  have hmem : l[a]! ∈ l := by
    rw [getElem!_pos l a ha']
    exact List.getElem_mem ha'
  exact hR _ (hP _ hmem)

theorem forall_range_refl_noWf {α : Type} [Inhabited α] (l : List α)
    (R : α → α → Prop) (hR : ∀ x, R x x) :
    Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a _
  exact hR _

/-- Rocq: `Extend_store_refl` (extension_lemmas.v:1603).
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

/-- Projects the running store out of a `config`. Not present in
    `wasm2.0.lean` itself (that file has no field-accessor sugar for the
    plain, non-`structure` `config`/`state` types) — new plumbing local to
    this file. -/
def configStore : config → store
  | config.mk_config (state.mk_state s _) _ => s

/-- Rocq: the `pure`-transition fragment of `store_extension_reduce`
    (`type_preservation.v`, inside the induction driving `store_extension_reduce`).
    Isabelle: `Properties.thy`, `case (pure admininstr_lst admininstr'_lst)` —
    the one case Isabelle's development actually completes. -/
theorem store_extension_pure {z : state} {ais ais' : List admininstr}
    (_hpure : Step_pure ais ais')
    (hcfg : wf_config (config.mk_config z ais)) :
    Extend_store (configStore (config.mk_config z ais)) (configStore (config.mk_config z ais)) := by
  obtain ⟨s, f⟩ := z
  have hstate : wf_state (state.mk_state s f) := by
    cases hcfg with
    | config_case_0 _ _ hst _ => exact hst
  have hs : wf_store s := by
    cases hstate with
    | state_case_0 _ _ hs _ => exact hs
  exact extend_store_refl hs

/-- Isabelle marks this case `sorry` (`case (read admininstr_lst admininstr'_lst)
    then show ?case sorry`), but it is exactly as trivial as the `pure` case:
    `Step.read`'s own conclusion (`wasm2.0.lean:11110-11112`) uses the same
    state `z` on both sides, so the store cannot have changed. -/
theorem store_extension_read {z : state} {ais ais' : List admininstr}
    (_hread : Step_read (config.mk_config z ais) ais')
    (hcfg : wf_config (config.mk_config z ais)) :
    Extend_store (configStore (config.mk_config z ais)) (configStore (config.mk_config z ais)) := by
  obtain ⟨s, f⟩ := z
  have hstate : wf_state (state.mk_state s f) := by
    cases hcfg with
    | config_case_0 _ _ hst _ => exact hst
  have hs : wf_store s := by
    cases hstate with
    | state_case_0 _ _ hs _ => exact hs
  exact extend_store_refl hs

/-- Generic version of the `store_extension_pure`/`store_extension_read`
    pattern: whenever a `Step` case's own conclusion keeps `z` completely
    unchanged (only the admininstr list on the right may differ), the store
    extension obligation is pure reflexivity regardless of which
    admininstr list `ais'` is. Several leaf cases turn out to have this
    shape once checked directly against their actual constructor
    (trap/failure variants in particular — see the induction below for the
    full list) rather than assumed to need typing infrastructure by
    analogy with `global_set`. -/
theorem store_extension_same_state {z : state} {ais ais' : List admininstr}
    (hcfg : wf_config (config.mk_config z ais)) :
    Extend_store (configStore (config.mk_config z ais)) (configStore (config.mk_config z ais')) := by
  obtain ⟨s, f⟩ := z
  have hstate : wf_state (state.mk_state s f) := by
    cases hcfg with
    | config_case_0 _ _ hst _ => exact hst
  have hs : wf_store s := by
    cases hstate with
    | state_case_0 _ _ hs _ => exact hs
  exact extend_store_refl hs

/-- `local_set` only ever touches the *frame*'s `LOCALS` (`with_local`,
    `wasm2.0.lean:9043-9048`: `state.mk_state s {f with LOCALS := ...}` —
    note `s` is passed through completely unchanged), so — like `pure`/`read`
    above — the store extension obligation is pure reflexivity, no typing
    needed. (`global_set`'s analogous case *does* need typing — mutability —
    since `with_global` genuinely rewrites a `store` component; don't
    conflate the two, as an earlier pass in this file did before this was
    checked directly — see `logs/DECISIONS.md`.) -/
theorem store_extension_local_set {z : state} {v_val : val} {x : idx}
    (hcfg : wf_config (config.mk_config z [admininstr_val v_val, admininstr.LOCAL_SET x])) :
    Extend_store (configStore (config.mk_config z [admininstr_val v_val, admininstr.LOCAL_SET x]))
      (configStore (config.mk_config (with_local z x v_val) [])) := by
  obtain ⟨s, f⟩ := z
  have hstate : wf_state (state.mk_state s f) := by
    cases hcfg with
    | config_case_0 _ _ hst _ => exact hst
  have hs : wf_store s := by
    cases hstate with
    | state_case_0 _ _ hs _ => exact hs
  show Extend_store s (configStore (config.mk_config (with_local (state.mk_state s f) x v_val) []))
  simp only [with_local, configStore]

  exact extend_store_refl hs

/-- Rocq's/Isabelle's counterpart cases for `elem_drop`/`data_drop` are among
    the 18 store-mutating leaf cases both sources also leave nontrivial (Rocq
    proves them, Isabelle `sorry`s them). Unlike most of the other 16
    (`table_set`/`store_*`/`memory_grow`/etc.), these two are provable from
    *structural* facts alone (`wf_config`), with no typing/mutability
    hypothesis needed: `Extend_eleminst`/`Extend_datainst`'s own constructors
    (`wasm2.0.lean:12430-12456`) allow the new value to be `[]`/empty
    unconditionally, which is exactly what `ELEM_DROP`/`DATA_DROP` produce.
    This proves `elem_drop`; `data_drop` is the same shape (not yet ported,
    the only difference is needing `wf_datainst {BYTES := []}`, which holds
    trivially since `Forall wf_byte []`). -/
theorem store_extension_elem_drop {s : store} {f : frame} {x : idx}
    (hcfg : wf_config (config.mk_config (state.mk_state s f) [admininstr.ELEM_DROP x])) :
    Extend_store s (configStore (config.mk_config (with_elem (state.mk_state s f) x []) [])) := by
  have hstate : wf_state (state.mk_state s f) := by
    cases hcfg with
    | config_case_0 _ _ hst _ => exact hst
  have hs : wf_store s := by
    cases hstate with
    | state_case_0 _ _ hs _ => exact hs
  cases hs with
  | store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas =>
    show Extend_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas }
      { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := List.modify elems (f.MODULE.ELEMS)[proj_uN_0 x]! (fun e => { e with REFS := [] }), DATAS := datas }
    have hwf1 : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas
    have hwf2 : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := List.modify elems (f.MODULE.ELEMS)[proj_uN_0 x]! (fun e => { e with REFS := [] }), DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems (List.modify elems (f.MODULE.ELEMS)[proj_uN_0 x]! (fun e => { e with REFS := [] })) datas
        hfuncs hglobals htables hmems hdatas
    refine Extend_store.mk_Extend_store _ _
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
      (forall_range_lt elems) ?_ ?_
      hwf1 hwf2
    · rw [List.length_modify]; exact forall_range_lt elems
    · intro a ha
      have ha' : a < elems.length := List.mem_range.mp ha
      have hlen : a < (List.modify elems (f.MODULE.ELEMS)[proj_uN_0 x]! (fun e => { e with REFS := [] })).length := by
        rw [List.length_modify]; exact ha'
      rw [getElem!_pos elems a ha', getElem!_pos _ a hlen, List.getElem_modify]
      split
      · obtain ⟨rt, refs⟩ := elems[a]
        exact Extend_eleminst.mk_Extend_eleminst rt refs [] (Or.inr rfl)
      · exact extend_eleminst_refl _

/-- `data_drop`'s counterpart to `store_extension_elem_drop` above. Unlike
    `Extend_eleminst`, `Extend_datainst`'s constructor (`wasm2.0.lean:
    12430-12443`) *does* require `wf_datainst` of both the old and the new
    (here: empty) value, but the new one's is trivial (`Forall wf_byte []`)
    and the old one's comes straight out of `hdatas` at the modified index,
    exactly as in the `Extend_datainst` slot of `extend_store_refl`. -/
theorem store_extension_data_drop {s : store} {f : frame} {x : idx}
    (hcfg : wf_config (config.mk_config (state.mk_state s f) [admininstr.DATA_DROP x])) :
    Extend_store s (configStore (config.mk_config (with_data (state.mk_state s f) x []) [])) := by
  have hstate : wf_state (state.mk_state s f) := by
    cases hcfg with
    | config_case_0 _ _ hst _ => exact hst
  have hs : wf_store s := by
    cases hstate with
    | state_case_0 _ _ hs _ => exact hs
  cases hs with
  | store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas =>
    show Extend_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas }
      { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := List.modify datas (f.MODULE.DATAS)[proj_uN_0 x]! (fun e => { e with BYTES := [] }) }
    have hwf1 : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas
    have hdatas' : Forall (fun e => wf_datainst e) (List.modify datas (f.MODULE.DATAS)[proj_uN_0 x]! (fun e => { e with BYTES := [] })) := by
      intro e he
      have hlen : (List.modify datas (f.MODULE.DATAS)[proj_uN_0 x]! (fun e => { e with BYTES := [] })).length = datas.length :=
        List.length_modify _ _ _
      have : e ∈ (List.modify datas (f.MODULE.DATAS)[proj_uN_0 x]! (fun e => { e with BYTES := [] })) := he
      obtain ⟨a, ha_lt, ha_eq⟩ := List.mem_iff_getElem.mp this
      rw [List.getElem_modify] at ha_eq
      split at ha_eq
      · rw [← ha_eq]; exact wf_datainst.datainst_case_ [] (by intro y hy; simp at hy)
      · rw [← ha_eq]
        exact hdatas _ (List.getElem_mem (by omega : a < datas.length))
    have hwf2 : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := List.modify datas (f.MODULE.DATAS)[proj_uN_0 x]! (fun e => { e with BYTES := [] }) } :=
      wf_store.store_case_ funcs globals tables mems elems (List.modify datas (f.MODULE.DATAS)[proj_uN_0 x]! (fun e => { e with BYTES := [] }))
        hfuncs hglobals htables hmems hdatas'
    refine Extend_store.mk_Extend_store _ _
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
      (forall_range_lt datas) ?_ ?_
      (forall_range_lt elems) (forall_range_lt elems)
      (forall_range_refl_noWf elems Extend_eleminst extend_eleminst_refl)
      hwf1 hwf2
    · rw [List.length_modify]; exact forall_range_lt datas
    · intro a ha
      have ha' : a < datas.length := List.mem_range.mp ha
      have hlen : a < (List.modify datas (f.MODULE.DATAS)[proj_uN_0 x]! (fun e => { e with BYTES := [] })).length := by
        rw [List.length_modify]; exact ha'
      rw [getElem!_pos datas a ha', getElem!_pos _ a hlen, List.getElem_modify]
      split
      · refine Extend_datainst.mk_Extend_datainst (datas[a]).BYTES [] (Or.inr rfl) ?_ ?_
        · exact hdatas _ (List.getElem_mem ha')
        · exact wf_datainst.datainst_case_ [] (by intro y hy; simp at hy)
      · exact extend_datainst_refl (hdatas _ (List.getElem_mem ha'))

/-- `table_set_val` (`wasm2.0.lean:11135-11138`) writes a *single* table
    slot via a doubly-nested `List.modify` (`with_table`,
    `wasm2.0.lean:9080-9088`: outer modify picks the table by address, inner
    modify overwrites one `REFS` entry). Both `List.modify`s preserve
    length, and `wf_tableinst` (`wasm2.0.lean:8262-8268`) only constrains
    `TYPE`, not `REFS` at all — so, like `elem_drop`/`data_drop`, this is
    provable purely structurally: no mutability/typing hypothesis needed
    (tables, unlike globals, have no immutability distinction in Wasm to
    begin with). -/
theorem store_extension_table_set_val {s : store} {f : frame} {ais : List admininstr}
    {x : idx} {natIdx : Nat} {v_ref : ref}
    (hcfg : wf_config (config.mk_config (state.mk_state s f) ais)) :
    Extend_store s (configStore (config.mk_config (with_table (state.mk_state s f) x natIdx v_ref) [])) := by
  have hstate : wf_state (state.mk_state s f) := by
    cases hcfg with
    | config_case_0 _ _ hst _ => exact hst
  have hs : wf_store s := by
    cases hstate with
    | state_case_0 _ _ hs _ => exact hs
  cases hs with
  | store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas =>
    show Extend_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas }
      { FUNCS := funcs, GLOBALS := globals, TABLES := List.modify tables (f.MODULE.TABLES)[proj_uN_0 x]! (fun ti => { ti with REFS := List.modify ti.REFS natIdx (fun _ => v_ref) }), MEMS := mems, ELEMS := elems, DATAS := datas }
    have hwf1 : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas
    have htables' : Forall (fun ti => wf_tableinst ti) (List.modify tables (f.MODULE.TABLES)[proj_uN_0 x]! (fun ti => { ti with REFS := List.modify ti.REFS natIdx (fun _ => v_ref) })) := by
      intro e he
      have hmem : e ∈ (List.modify tables (f.MODULE.TABLES)[proj_uN_0 x]! (fun ti => { ti with REFS := List.modify ti.REFS natIdx (fun _ => v_ref) })) := he
      obtain ⟨a, ha_lt, ha_eq⟩ := List.mem_iff_getElem.mp hmem
      have hlen_eq : (List.modify tables (f.MODULE.TABLES)[proj_uN_0 x]! (fun ti => { ti with REFS := List.modify ti.REFS natIdx (fun _ => v_ref) })).length = tables.length :=
        List.length_modify _ _ _
      have ha2 : a < tables.length := by omega
      have hwf_old2 : wf_tableinst tables[a] := htables _ (List.getElem_mem ha2)
      rw [List.getElem_modify] at ha_eq
      split at ha_eq
      · rw [← ha_eq]
        generalize hti2 : tables[a] = ti2 at hwf_old2 ⊢
        cases hwf_old2 with
        | tableinst_case_ v_0 v_1 hlim =>
          exact wf_tableinst.tableinst_case_ v_0 (List.modify v_1 natIdx (fun _ => v_ref)) hlim
      · rw [← ha_eq]; exact htables _ (List.getElem_mem ha2)
    have hwf2 : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := List.modify tables (f.MODULE.TABLES)[proj_uN_0 x]! (fun ti => { ti with REFS := List.modify ti.REFS natIdx (fun _ => v_ref) }), MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals (List.modify tables (f.MODULE.TABLES)[proj_uN_0 x]! (fun ti => { ti with REFS := List.modify ti.REFS natIdx (fun _ => v_ref) })) mems elems datas
        hfuncs hglobals htables' hmems hdatas
    refine Extend_store.mk_Extend_store _ _
      (forall_range_lt globals) (forall_range_lt globals)
      (forall_range_refl globals wf_globalinst Extend_globalinst hglobals
        (fun x hx => extend_globalinst_refl hx))
      (forall_range_lt mems) (forall_range_lt mems)
      (forall_range_refl mems wf_meminst Extend_meminst hmems
        (fun x hx => extend_meminst_refl hx))
      (forall_range_lt tables) ?_ ?_
      (forall_range_lt funcs) (forall_range_lt funcs)
      (forall_range_refl funcs wf_funcinst Extend_funcinst hfuncs
        (fun x hx => extend_funcinst_refl hx))
      (forall_range_lt datas) (forall_range_lt datas)
      (forall_range_refl datas wf_datainst Extend_datainst hdatas
        (fun x hx => extend_datainst_refl hx))
      (forall_range_lt elems) (forall_range_lt elems)
      (forall_range_refl_noWf elems Extend_eleminst extend_eleminst_refl)
      hwf1 hwf2
    · rw [List.length_modify]; exact forall_range_lt tables
    · intro a ha
      have ha' : a < tables.length := List.mem_range.mp ha
      have hlen : a < (List.modify tables (f.MODULE.TABLES)[proj_uN_0 x]! (fun ti => { ti with REFS := List.modify ti.REFS natIdx (fun _ => v_ref) })).length := by
        rw [List.length_modify]; exact ha'
      have hwf_old : wf_tableinst tables[a] := htables _ (List.getElem_mem ha')
      rw [getElem!_pos tables a ha', getElem!_pos _ a hlen, List.getElem_modify]
      generalize hti : tables[a] = ti at hwf_old ⊢
      split
      · obtain ⟨ty, refs⟩ := ti
        obtain ⟨lim, rt⟩ := ty
        obtain ⟨v_u32, u32_opt⟩ := lim
        obtain ⟨v_n⟩ := v_u32
        have hlen_refs : (List.modify refs natIdx (fun _ => v_ref)).length = refs.length :=
          List.length_modify _ _ _
        have hwf_new_type : wf_tabletype (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_n) u32_opt) rt) := by
          cases hwf_old with
          | tableinst_case_ _ _ hlim => exact hlim
        rcases u32_opt with _ | u32opt
        · exact Extend_tableinst.mk_Extend_tableinst v_n none rt refs v_n (List.modify refs natIdx (fun _ => v_ref))
            (Nat.le_refl v_n) (hlen_refs ▸ Nat.le_refl refs.length) hwf_old
            (wf_tableinst.tableinst_case_ _ _ hwf_new_type)
        · obtain ⟨n'⟩ := u32opt
          exact Extend_tableinst.mk_Extend_tableinst v_n (some n') rt refs v_n (List.modify refs natIdx (fun _ => v_ref))
            (Nat.le_refl v_n) (hlen_refs ▸ Nat.le_refl refs.length) hwf_old
            (wf_tableinst.tableinst_case_ _ _ hwf_new_type)
      · exact extend_tableinst_refl hwf_old

/-- Full case skeleton, matching `Step`'s 23 constructors (`wasm2.0.lean:
    11106-11205`) one-for-one, proved by induction on `Step` so the three
    congruence cases (`ctxt_label`/`ctxt_frame`/`ctxt_instrs`) get their
    inductive hypothesis for free.

    **16/23 real, only 7 `sorry`** — far more than initially expected, because
    checking each case's *actual* constructor directly (rather than assuming
    "mutates the store ⇒ needs typing" by analogy with `global_set`) turned up
    many more structural wins than the first pass found:
    - `pure`/`read`: same state `z` on both sides (Isabelle proves `pure`,
      leaves `read` `sorry` despite it being no harder).
    - `local_set`: `with_local` only ever touches the *frame*, never the store.
    - `elem_drop`/`data_drop`: the dropped-to value being empty always
      satisfies `Extend_eleminst`/`Extend_datainst` unconditionally.
    - `table_set_trap`/`table_grow_fail`/`store_num_trap`/`store_pack_trap`/
      `vstore_oob`/`vstore_lane_oob`/`memory_grow_fail`: every one of these
      is a trap/failure variant whose `Step` conclusion *also* keeps `z`
      unchanged (checked directly against each constructor, not assumed) —
      `store_extension_same_state` covers all seven in one line each.
    - `table_set_val`: single-slot table write; length-preserving
      (`List.modify` never changes length) and `wf_tableinst` doesn't
      constrain `REFS` at all, so no typing needed here either.

    The 7 still `sorry` (`global_set`, `table_grow_succeed`,
    `store_num_val`/`store_pack_val`/`vstore_val`/`vstore_lane_val`,
    `memory_grow_succeed`) are qualitatively different: `global_set` needs
    real mutability typing; the memory-write cases need a length-preservation
    fact about `nbytes_`/`ibytes_`/`vbytes_`'s output (not yet checked in
    detail); the `_grow_succeed` cases need `fun_growtable`/`fun_growmemory`'s
    postcondition. Isabelle proves 1/23 (`pure`); this file's 16/23 is the
    most complete `store_extension_reduce`-equivalent of the three
    developments after Rocq's own (which has the true target — full
    `Instrs_ok2`-based preconditions — mostly proved, not replicated here). -/
theorem store_extension_reduce {cfg cfg' : config} (hstep : Step cfg cfg')
    (hcfg : wf_config cfg) :
    Extend_store (configStore cfg) (configStore cfg') := by
  induction hstep with
  | pure z ais ais' hpure => exact store_extension_pure hpure hcfg
  | read z ais ais' hread => exact store_extension_read hread hcfg
  | ctxt_label z v_n instr_0_lst ais z' ais' _hstep hwf1 _hwf2 ih =>
    exact ih hwf1
  | ctxt_frame s f v_n f' ais s' f'' ais' _hstep hwf1 _hwf2 ih =>
    exact ih hwf1
  | ctxt_instrs z val_lst ais ais_1 z' ais' _hstep _hne hwf1 _hwf2 ih =>
    exact ih hwf1
  | elem_drop z x =>
    obtain ⟨s, f⟩ := z
    exact store_extension_elem_drop hcfg
  | data_drop z x =>
    obtain ⟨s, f⟩ := z
    exact store_extension_data_drop hcfg
  | local_set z v_val x =>
    exact store_extension_local_set hcfg
  | table_set_trap _ _ _ _ _ _ => exact store_extension_same_state hcfg
  | table_grow_fail _ _ _ _ _ _ => exact store_extension_same_state hcfg
  | store_num_trap _ _ _ _ _ _ _ _ _ => exact store_extension_same_state hcfg
  | store_pack_trap _ _ _ _ _ _ _ _ _ => exact store_extension_same_state hcfg
  | vstore_oob _ _ _ _ _ _ _ _ => exact store_extension_same_state hcfg
  | vstore_lane_oob _ _ _ _ _ _ _ _ _ => exact store_extension_same_state hcfg
  | memory_grow_fail _ _ _ _ => exact store_extension_same_state hcfg
  | table_set_val z i v_ref x _ _ =>
    obtain ⟨s, f⟩ := z
    exact store_extension_table_set_val hcfg
  | _ => sorry

end TestLeanClaude

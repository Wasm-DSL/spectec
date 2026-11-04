import «wasm2.0»
import HelperLemmas
import Subtyping
import TypingLemmas
import TypePreservationPure
import ExtensionLemmas

/-!
# TypePreservation

Lean port of `spectec/test-rocq/theories/type_preservation.v` — the
capstone file containing the main preservation theorem. Full digest:
`claude-logging/for-claude/digest_type_preservation.md`.

Status: upstream `type_preservation.v` has **no** `Admitted` lemmas: everything is `Qed`. Since
upstream `6582b3a39` that includes the
generated `Step_read_is_wf` in `wasm.v`, which used to be `Admitted` (and false in a
memory.fill/copy/init `2^32` corner case, fixed by spec commit `4cf9f29c5`, which makes those
rules push `$iadd_(32, i, 1)`). `t_preservation` depends on no `sorry`: besides Lean's standard
axioms, `#print axioms` lists only the model's `*_is_wf` axioms for the functions that are
`opaque` in `wasm2.0.lean` (`Axiom`s in Rocq too, where these theorems are `Admitted`).
`num_default_is_well_formed` is proved (its Rocq statement is commented out upstream).

Since the model was regenerated with `sideconditions_on_defs` (user commit `12b021fc9`), the state
lookups and updates (`fun_table`, `fun_with_mem`, …) are relations whose premises carry the index
bounds. The proofs here invert them, mostly through the inversion lemmas at the end of
`HelperLemmas.lean`.

Line numbers refer to `spectec/test-rocq/theories` at upstream `rocq-backend-proof` `6582b3a39`.
-/

namespace TLC

/-- Rocq `type_preservation.v:13` `zero_is_well_formed`. -/
theorem zero_is_well_formed : wf_num_ numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)) := by
  refine wf_num_.num__case_0 numtype.I32 Inn.I32 (uN.mk_uN 0) ?_ ?_ rfl
  · simp [size, valtype_Inn]
  · simp only [size, valtype_Inn]
    exact wf_uN.uN_case_0 32 0 (by decide)

/-- Rocq `type_preservation.v:19` `num_default`. Default/zero value per numtype (`fzero` is the
    HelperLemmas function view of `fun_fzero`). Only `num_default_is_well_formed` uses it; the
    default locals of `t_read_preservation`'s `call_addr` case come from `default_`
    (`default_vals_ok`). -/
def num_default (nt : numtype) : num_ :=
  match nt with
  | .I32 => .mk_num__0 Inn.I32 (uN.mk_uN 0)
  | .I64 => .mk_num__0 Inn.I64 (uN.mk_uN 0)
  | .F32 => .mk_num__1 Fnn.F32 (fzero 32)
  | .F64 => .mk_num__1 Fnn.F64 (fzero 64)

/-- Rocq `type_preservation.v:75` `num_default_is_well_formed` (commented out in Rocq; proved
    here). -/
theorem num_default_is_well_formed (nt : numtype) : wf_num_ nt (num_default nt) := by
  cases nt with
  | I32 =>
    refine wf_num_.num__case_0 numtype.I32 Inn.I32 (uN.mk_uN 0) ?_ ?_ rfl
    · simp [size, valtype_Inn]
    · simp only [size, valtype_Inn]
      exact wf_uN.uN_case_0 32 0 (by decide)
  | I64 =>
    refine wf_num_.num__case_0 numtype.I64 Inn.I64 (uN.mk_uN 0) ?_ ?_ rfl
    · simp [size, valtype_Inn]
    · simp only [size, valtype_Inn]
      exact wf_uN.uN_case_0 64 0 (by decide)
  | F32 =>
    exact wf_num_.num__case_1 numtype.F32 Fnn.F32 (fzero 32) 32 (fun_sizenn_sizenn _) wf_fzero_32 rfl
  | F64 =>
    exact wf_num_.num__case_1 numtype.F64 Fnn.F64 (fzero 64) 64 (fun_sizenn_sizenn _) wf_fzero_64 rfl

/-- Rocq `type_preservation.v:41` `wf_context_app`. -/
theorem wf_context_app (C C' : context) : wf_context C → wf_context C' → wf_context (C ++ C') := by
  intro h1 h2
  cases h1 with
  | context_case_ _ _ _ _ _ _ _ _ _ _ hT hM =>
    cases h2 with
    | context_case_ _ _ _ _ _ _ _ _ _ _ hT' hM' =>
      refine wf_context.context_case_ _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        exacts [hT x hx, hT' x hx]
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        exacts [hM x hx, hM' x hx]

/-- Rocq `type_preservation.v:53` `wf_context_tab`. -/
theorem wf_context_tab (n : Nat) (C : context) :
    n < C.TABLES.length → wf_context C → wf_tabletype (C.TABLES[n]!) := by
  intro hn hC
  have hmem : C.TABLES[n]! ∈ C.TABLES := by rw [getElem!_pos C.TABLES n hn]; exact List.getElem_mem hn
  cases hC with
  | context_case_ _ _ _ _ _ _ _ _ _ _ hT _ => exact hT _ hmem

/-- Rocq `type_preservation.v:63` `wf_context_mem`. -/
theorem wf_context_mem (n : Nat) (C : context) :
    n < C.MEMS.length → wf_context C → wf_memtype (C.MEMS[n]!) := by
  intro hn hC
  have hmem : C.MEMS[n]! ∈ C.MEMS := by rw [getElem!_pos C.MEMS n hn]; exact List.getElem_mem hn
  cases hC with
  | context_case_ _ _ _ _ _ _ _ _ _ _ _ hM => exact hM _ hmem

/-- Rocq `type_preservation.v:86` `inst_t_context_local_empty`. -/
theorem inst_t_context_local_empty (s : store) (i : moduleinst) (C : context) :
    Moduleinst_ok s i C → C.LOCALS = [] := by
  intro h; cases h; rfl

/-- Rocq `type_preservation.v:93` `inst_t_context_labels_empty`. -/
theorem inst_t_context_labels_empty (s : store) (i : moduleinst) (C : context) :
    Moduleinst_ok s i C → C.LABELS = [] := by
  intro h; cases h; rfl

/-- Generalized form of `t_preservation_vs_type'` below (same `remember`/
    `generalize dependent` encoding as `reduce_inst_unchanged_aux`). Of `Step`'s
    23 rules, 20 leave the frame alone outright — only `local_set` touches
    `LOCALS`, and only the two congruence rules (`ctxt_label`, `ctxt_instrs`)
    need the induction hypothesis; `ctxt_frame` changes only the *inner* frame.
    The store-writing rules produce their state through a `fun_with_*`
    premise, which is inverted to expose the unchanged frame.
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
    try casesm fun_with_global _ _ _ _, fun_with_table _ _ _ _ _, fun_with_tableinst _ _ _ _,
      fun_with_elem _ _ _ _, fun_with_mem _ _ _ _ _ _, fun_with_meminst _ _ _ _,
      fun_with_data _ _ _ _
    injection hz2 with _ hf
    subst hf
    exact hvals)

/-- Rocq `type_preservation.v:100` `t_preservation_vs_type'`. Locals stay well-typed under
    one `Step` (store held fixed / pre-store-extension). -/
theorem t_preservation_vs_type' (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Store_ok s → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS → inst_match C C' →
    Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s f'.LOCALS C'.LOCALS :=
  fun hstep hsok hmi hvals him htype =>
    t_preservation_vs_type'_aux _ _ hstep s f ais s' f' ais' C C' t1s t2s rfl rfl hsok hmi hvals him htype

/-- Rocq `type_preservation.v:154` `t_preservation_vs_type`. Composition:
    `t_preservation_vs_type'` then `Extend_store_vals` to transport across store
    extension. -/
theorem t_preservation_vs_type (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Store_ok s → Extend_store s s' → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS →
    inst_match C C' → Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s' f'.LOCALS C'.LOCALS := by
  intro hstep hsok hext hmi hvals him htype
  exact Extend_store_vals s s' C'.LOCALS f'.LOCALS hext
    (t_preservation_vs_type' s f ais s' f' ais' C C' t1s t2s hstep hsok hmi hvals him htype)

/-- Rocq `type_preservation.v:170` `wf_tableinsts_preserves`.
    **Intended deviation**: takes `hlen`, the same move as `funcinst_same`/`Vals_ok` — Rocq's
    inductive `Forall2` implies equal lengths, this file's zip-based `Forall₂` does not, and
    without `hlen` the statement is false when `tbts` is longer than `tbinsts`. -/
theorem wf_tableinsts_preserves (s : store) (tbinsts : List tableinst) (tbts : List tabletype)
    (hlen : tbinsts.length = tbts.length) :
    Forall₂ (fun v t => Tableinst_ok s v t) tbinsts tbts → Forall wf_tableinst tbinsts →
    Forall wf_tabletype tbts := by
  intro h _ t ht
  -- `Tableinst_ok` carries `wf_tabletype` of its type directly; invert it over bare variables
  have aux : ∀ tb tbt, Tableinst_ok s tb tbt → wf_tabletype tbt := by
    intro tb tbt hok; cases hok; assumption
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have hok := Forall2_nth_of_length tbinsts tbts h hlen i (by omega)
  rw [getElem!_pos tbts i hi] at hok
  exact aux _ _ hok

/-- Rocq `type_preservation.v:185` `wf_memoryinsts_preserves`. Takes `hlen`,
    for the same reason as `wf_tableinsts_preserves`. -/
theorem wf_memoryinsts_preserves (s : store) (meminsts : List meminst) (mts : List memtype)
    (hlen : meminsts.length = mts.length) :
    Forall₂ (fun v t => Meminst_ok s v t) meminsts mts → Forall wf_meminst meminsts →
    Forall wf_memtype mts := by
  intro h _ t ht
  have aux : ∀ mi mt, Meminst_ok s mi mt → wf_memtype mt := by
    intro mi mt hok; cases hok; assumption
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have hok := Forall2_nth_of_length meminsts mts h hlen i (by omega)
  rw [getElem!_pos mts i hi] at hok
  exact aux _ _ hok

/-- Rocq `type_preservation.v:201` `list_update_func_preserves_prop`. -/
theorem list_update_func_preserves_prop {A : Type} [Inhabited A] (l : List A) (f : A → A) (P : A → Prop)
    (x : Nat) : Forall P l → P (f (l[x]!)) → Forall P (list_update_func l x f) := by
  intro hl hf y hy
  rcases mem_modify f l x y hy with h | ⟨h1, _⟩
  · exact hl y h
  · rw [h1]; exact hf

/-- Rocq `type_preservation.v:216` `list_update_func_forall_inv`. -/
theorem list_update_func_forall_inv {A : Type} [Inhabited A] (l : List A) (f : A → A) (P : A → Prop)
    (x : Nat) : x < l.length → Forall P (list_update_func l x f) → P (f (l[x]!)) := by
  intro hx h
  have hx' : x < (l.modify x f).length := by simpa using hx
  have hmem : (l.modify x f)[x]! ∈ l.modify x f := by
    rw [getElem!_pos (l.modify x f) x hx']; exact List.getElem_mem hx'
  have := h _ hmem
  rwa [getElem!_modify_eq_or_ne l x x f hx, if_pos rfl] at this

/-- Rocq `type_preservation.v:242` `Forall_list_update_func`. -/
theorem Forall_list_update_func {A : Type} (P : A → Prop) (l : List A) (n : Nat) (f : A → A) :
    Forall P l → (∀ x, P x → P (f x)) → Forall P (list_update_func l n f) := by
  intro hl hf
  cases l with
  | nil => intro y hy; simp [list_update_func] at hy
  | cons a t =>
    haveI : Inhabited A := ⟨a⟩
    intro y hy
    rcases mem_modify f (a :: t) n y hy with h | ⟨h1, h2⟩
    · exact hl y h
    · rw [h1]; exact hf _ (hl _ h2)

/-! ### Store-update plumbing for `store_extension_reduce` (Lean-only)

    Rocq rebuilds `Extend_store`/`Store_ok` in every store-writing case with
    `mk_Extend_store … ; eauto` and `mk_Store_ok with (…) ; first [eapply Extend_store_*s …]`.
    `Store_ok_parts`/`Store_ok_of_parts` take `Store_ok` apart and back together over a store's
    own fields, and `Extend_store_of_parts` replaces the 18 index-range premises of
    `Extend_store` by one "no shorter" + one pointwise fact per component. -/

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
  cases h with
  | mk_Store_ok _ gtl _ mtl _ ttl _ ftl _ dtl _ etl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hs hwf hmt htt _ =>
    subst hs
    exact ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwf, hmt, htt⟩

theorem Store_ok_of_parts (s : store) (gtl : List globaltype) (mtl : List memtype) (ttl : List tabletype)
    (ftl : List functype) (dtl : List datatype) (etl : List elemtype) :
    s.GLOBALS.length = gtl.length → Forall₂ (fun v t => Globalinst_ok s v t) s.GLOBALS gtl →
    s.MEMS.length = mtl.length → Forall₂ (fun v t => Meminst_ok s v t) s.MEMS mtl →
    s.TABLES.length = ttl.length → Forall₂ (fun v t => Tableinst_ok s v t) s.TABLES ttl →
    s.FUNCS.length = ftl.length → Forall₂ (fun v t => Funcinst_ok s v t) s.FUNCS ftl →
    s.DATAS.length = dtl.length → Forall₂ (fun v t => Datainst_ok s v t) s.DATAS dtl →
    s.ELEMS.length = etl.length → Forall₂ (fun v t => Eleminst_ok s v t) s.ELEMS etl →
    wf_store s → Forall wf_memtype mtl → Forall wf_tabletype ttl → Store_ok s := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hwf hmt htt
  exact Store_ok.mk_Store_ok s s.GLOBALS gtl s.MEMS mtl s.TABLES ttl s.FUNCS ftl s.DATAS dtl s.ELEMS etl
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 rfl hwf hmt htt hwf

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
  intro hg1 hg2 hm1 hm2 ht1 ht2 hf1 hf2 hd1 hd2 he1 he2 hwf hwf'
  exact Extend_store.mk_Extend_store s s'
    (forall_range_lt _) (fun a ha => Nat.lt_of_lt_of_le (List.mem_range.mp ha) hg1) hg2
    (forall_range_lt _) (fun a ha => Nat.lt_of_lt_of_le (List.mem_range.mp ha) hm1) hm2
    (forall_range_lt _) (fun a ha => Nat.lt_of_lt_of_le (List.mem_range.mp ha) ht1) ht2
    (forall_range_lt _) (fun a ha => Nat.lt_of_lt_of_le (List.mem_range.mp ha) hf1) hf2
    (forall_range_lt _) (fun a ha => Nat.lt_of_lt_of_le (List.mem_range.mp ha) hd1) hd2
    (forall_range_lt _) (fun a ha => Nat.lt_of_lt_of_le (List.mem_range.mp ha) he1) he2
    hwf hwf'

/-- `wf_store s` gives each component list's `wf_*` facts. -/
theorem wf_store_parts (s : store) (h : wf_store s) :
    Forall wf_funcinst s.FUNCS ∧ Forall wf_globalinst s.GLOBALS ∧ Forall wf_tableinst s.TABLES ∧
      Forall wf_meminst s.MEMS ∧ Forall wf_datainst s.DATAS := by
  cases h with
  | store_case_ _ _ _ _ _ _ hf hg ht hm hd => exact ⟨hf, hg, ht, hm, hd⟩

/-- `Datainst_ok` facts move across a store extension in `Forall₂` form too (`datatype` has the
    single inhabitant `OK`, so this is `Extend_store_datainsts` with the type list re-attached). -/
theorem Extend_store_datainsts₂ (s s' : store) (ds : List datainst) (dts : List datatype) :
    Extend_store s s' → Forall₂ (fun v t => Datainst_ok s v t) ds dts →
    Forall₂ (fun v t => Datainst_ok s' v t) ds dts := by
  intro hext h p hp
  have hwfS' := Extend_store_wf_store' s s' hext
  have aux : ∀ d t, Datainst_ok s d t → Datainst_ok s' d t := by
    intro d t hd
    cases hd with
    | mk_Datainst_ok b_lst hlen _ hwf => exact Datainst_ok.mk_Datainst_ok s' b_lst hlen hwfS' hwf
  exact aux _ _ (h p hp)

/-- Rocq `type_preservation.v:253` `wf_store_mem_update`. Stated, as in Rocq,
    with `list_slice_update`; the model's `$with_mem` (the relation `fun_with_mem`, which writes
    with `splice`) is bridged to it by
    `HelperLemmas.splice_eq_list_slice_update`. -/
theorem wf_store_mem_update (s : store) (idx off len : Nat) (b_lst : List byte) :
    wf_store s → Forall wf_byte b_lst →
    wf_store { s with
      MEMS := list_update_func s.MEMS idx
        (fun m => { m with BYTES := list_slice_update m.BYTES off len b_lst }) } := by
  intro hS hb
  cases hS with
  | store_case_ _ _ _ ms _ _ hf hg ht hm hd =>
    refine wf_store.store_case_ _ _ _ _ _ _ hf hg ht ?_ hd
    refine Forall_list_update_func _ ms idx _ hm (fun m hm' => ?_)
    cases hm' with
    | meminst_case_ mt bs hmt hbs =>
      exact wf_meminst.meminst_case_ mt _ hmt (list_slice_update_forall bs b_lst off len hbs hb)

/-- Rocq `type_preservation.v:270` `wf_store_mem_update'`. -/
theorem wf_store_mem_update' (fs : List funcinst) (gs : List globalinst) (ts : List tableinst)
    (ms : List meminst) (es : List eleminst) (ds : List datainst) (idx off len : Nat) (b_lst : List byte) :
    wf_store (store.MKstore fs gs ts ms es ds) → Forall wf_byte b_lst →
    wf_store (store.MKstore fs gs ts (list_update_func ms idx
      (fun m => { m with BYTES := list_slice_update m.BYTES off len b_lst })) es ds) := by
  intro h hb
  exact wf_store_mem_update (store.MKstore fs gs ts ms es ds) idx off len b_lst h hb

/-- The address lists of a module instance have the lengths of its context's type lists:
    `Moduleinst_ok`'s own length premises, collected once (Lean-only). Rocq gets these
    from `Forall2_length` on the corresponding `Forall2` premises; the zip-based `Forall₂` here
    cannot, so they are read off the separate length premises instead. -/
theorem Moduleinst_ok_lengths (s : store) (minst : moduleinst) (C : context) :
    Moduleinst_ok s minst C →
    minst.GLOBALS.length = C.GLOBALS.length ∧ minst.FUNCS.length = C.FUNCS.length ∧
    minst.MEMS.length = C.MEMS.length ∧ minst.TABLES.length = C.TABLES.length ∧
    minst.DATAS.length = C.DATAS.length ∧ minst.ELEMS.length = C.ELEMS.length := by
  intro h
  cases h with
  | mk_Moduleinst_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg _ hf _ hm _ ht _ _ hd _ _ he =>
    exact ⟨hg, hf, hm, ht, hd, he⟩

/-- Rocq `type_preservation.v:287` `mem_store_extension`: storing a
    well-formed byte sequence into memory 0 extends the store and keeps it `Store_ok`. The
    byte-list-agnostic core of `store_extension_reduce`'s store cases. Rocq's `len : Q` is a
    `Nat` here, matching the Lean model's byte lengths. -/
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
  intro hsok hwfS hmi him hmem hwfb hlen
  subst hlen
  -- memory 0 of the module instance is a store address pointing at some memory instance
  have hlenM : v_f.MODULE.MEMS.length = C'.MEMS.length := by
    rw [← him.2.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.1
  obtain ⟨v_mt, b0, hb, hlk, _⟩ := Forall2_nth_of_length v_f.MODULE.MEMS C'.MEMS
    (minst_invert_mems s v_f.MODULE C C' hmi him) hlenM 0 (by omega)
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfS' := wf_store_mem_update s (v_f.MODULE.MEMS[0]!) off b_lst.length b_lst hwfS hwfb
  -- every component but MEMS is unchanged; MEMS grows pointwise (`store_none_mem_extension`)
  have hext : Extend_store s { s with
      MEMS := list_update_func s.MEMS (v_f.MODULE.MEMS[0]!)
        (fun m => { m with BYTES := list_slice_update m.BYTES off b_lst.length b_lst }) } := by
    refine Extend_store_of_parts _ _ (Nat.le_refl _) (extend_global_refl s hwfG) ?_ ?_
      (Nat.le_refl _) (extend_table_refl s hwfT) (Nat.le_refl _) (extend_func_refl s hwfF)
      (Nat.le_refl _) (extend_data_refl s hwfD) (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
    · exact Nat.le_of_eq (list_update_length_func _ _ _).symm
    · exact store_none_mem_extension s.MEMS _ _ v_mt b0 off b_lst.length b_lst hwfb hwfM hb hlk rfl
  refine ⟨hext, ?_⟩
  -- `Store_ok`: the old typings carry over by `Extend_store_*s`, the new memory by `construct_meminsts`
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _, hmt, htt⟩ :=
    Store_ok_parts s hsok
  refine Store_ok_of_parts _ gtl mtl ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2) ?_ ?_
    h5 (Extend_store_tableinsts _ _ _ _ hext h6) h7 (Extend_store_funcinsts _ _ _ _ hext h8)
    h9 (Extend_store_datainsts₂ _ _ _ _ hext h10) h11 (Extend_store_eleminsts _ _ _ _ hext h12)
    hwfS' hmt htt
  · exact (list_update_length_func _ _ _).trans h3
  · exact Extend_store_meminsts _ _ _ _ hext (construct_meminsts s mtl _ v_mt b0 off b_lst hwfb h4 hlk)

/-- Rocq `type_preservation.v:402` `ais_seq3_last_typing`. -/
theorem ais_seq3_last_typing (v_S : store) (v_C : context) (a b op : admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [a, b, op] v_ft → ∃ t1s t2s, Instrs_ok2 v_S v_C [op] (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  obtain ⟨t3s, hrest, _⟩ := ais_seq_typing_inversion v_S v_C [b, op] a t1s t2s h
  obtain ⟨t4s, hop, _⟩ := ais_seq_typing_inversion v_S v_C [op] b t3s t2s hrest
  exact ⟨t4s, t2s, hop⟩

/-- Rocq `type_preservation.v:414` `ais_vstore_mems_inversion`. -/
theorem ais_vstore_mems_inversion (v_S : store) (v_C : context) (ao : memarg) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [admininstr.VSTORE vectype.V128 ao] (mkFunctype t1s t2s) → 0 < v_C.MEMS.length := by
  intro h
  obtain ⟨_, _, hok, _⟩ := ais_single_plain_typing_inversion v_S v_C (instr.VSTORE vectype.V128 ao) t1s t2s h
  simp only [mkFunctype] at hok
  cases hok
  assumption

/-- Rocq `type_preservation.v:424` `ais_vstore_lane_mems_inversion`. -/
theorem ais_vstore_lane_mems_inversion (v_S : store) (v_C : context) (v_n : n) (ao : memarg)
    (v_laneidx : laneidx) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_n) ao v_laneidx] (mkFunctype t1s t2s) →
    0 < v_C.MEMS.length := by
  intro h
  obtain ⟨_, _, hok, _⟩ := ais_single_plain_typing_inversion v_S v_C (instr.VSTORE_LANE vectype.V128 (sz.mk_sz v_n) ao v_laneidx) t1s t2s h
  simp only [mkFunctype] at hok
  cases hok
  assumption

/-- Generalized form of `reduce_inst_unchanged` below. Rocq does the same
    thing with `remember ... as c1`/`remember ... as c2` plus `generalize
    dependent` before `induction HReduce`; Lean's `induction` needs the
    indices to be variables, so the two `config`s are generalized and the
    shapes recovered from equational premises instead. Every `Step`
    constructor either leaves the state alone, rewrites it with `with_local`
    (which touches only `LOCALS`) or through one of the `fun_with_*` relations
    (inverted here; they touch only the store), or is one of the two
    congruence rules that need the induction hypothesis; `ctxt_frame` needs no
    induction hypothesis either, since it changes only the store and the *inner* frame. -/
private theorem reduce_inst_unchanged_aux (c1 c2 : config) (h : Step c1 c2) :
    ∀ (s : store) (f : frame) (ais : List admininstr) (s' : store) (f' : frame)
      (ais' : List admininstr),
      c1 = config.mk_config (state.mk_state s f) ais →
      c2 = config.mk_config (state.mk_state s' f') ais' → f.MODULE = f'.MODULE := by
  induction h
  case ctxt_label z v_n i0 L z' L' _ _ _ ih =>
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    injection h2 with hz' _
    exact ih s f L s' f' L' (by rw [hz]) (by rw [hz'])
  case ctxt_instrs z vl L L1 z' L' _ _ _ _ ih =>
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    injection h2 with hz' _
    exact ih s f L s' f' L' (by rw [hz]) (by rw [hz'])
  case local_set z v_val x =>
    -- the only rule that touches the frame at all: `with_local` rewrites
    -- `LOCALS` and leaves `MODULE` alone.
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    subst hz
    injection h2 with hz' _
    simp only [with_local] at hz'
    injection hz' with _ hf
    subst hf
    rfl
  all_goals (
    intro s f ais s' f' ais' h1 h2
    try casesm fun_with_global _ _ _ _, fun_with_table _ _ _ _ _, fun_with_tableinst _ _ _ _,
      fun_with_elem _ _ _ _, fun_with_mem _ _ _ _ _ _, fun_with_meminst _ _ _ _,
      fun_with_data _ _ _ _
    simp_all)

/-- Rocq `type_preservation.v:1504` `reduce_inst_unchanged`. The module-instance component
    of the frame is invariant under `Step`. -/
theorem reduce_inst_unchanged (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    f.MODULE = f'.MODULE :=
  fun h => reduce_inst_unchanged_aux _ _ h s f ais s' f' ais' rfl rfl

/-! ### SIMD loads and stores (`type_preservation.v:1518-1660`) -/

/-- Rocq `type_preservation.v:1522` `ais_vload_typing_inversion`. -/
theorem ais_vload_typing_inversion (v_S : store) (v_C : context) (vlo : Option vloadop_) (ao : memarg)
    (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [admininstr.VLOAD vectype.V128 vlo ao] (mkFunctype t1s t2s) →
    instrtype_sub (mkFunctype [valtype.I32] [valtype.V128]) (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t1, t2, hok, hsub⟩ := ais_single_plain_typing_inversion v_S v_C (instr.VLOAD vectype.V128 vlo ao) t1s t2s h
  simp only [mkFunctype] at hok
  cases hok <;> exact hsub

/-- Rocq `type_preservation.v:1533` `ais_vload_lane_typing_inversion`. -/
theorem ais_vload_lane_typing_inversion (v_S : store) (v_C : context) (v_sz : sz) (ao : memarg)
    (l : laneidx) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [admininstr.VLOAD_LANE vectype.V128 v_sz ao l] (mkFunctype t1s t2s) →
    instrtype_sub (mkFunctype [valtype.I32, valtype.V128] [valtype.V128]) (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t1, t2, hok, hsub⟩ := ais_single_plain_typing_inversion v_S v_C (instr.VLOAD_LANE vectype.V128 v_sz ao l) t1s t2s h
  simp only [mkFunctype] at hok
  cases hok <;> exact hsub

/-- Rocq `type_preservation.v:1544` `ais_vstore_typing_inversion`. -/
theorem ais_vstore_typing_inversion (v_S : store) (v_C : context) (ao : memarg) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [admininstr.VSTORE vectype.V128 ao] (mkFunctype t1s t2s) →
    instrtype_sub (mkFunctype [valtype.I32, valtype.V128] []) (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t1, t2, hok, hsub⟩ := ais_single_plain_typing_inversion v_S v_C (instr.VSTORE vectype.V128 ao) t1s t2s h
  simp only [mkFunctype] at hok
  cases hok <;> exact hsub

/-- Rocq `type_preservation.v:1554` `ais_vstore_lane_typing_inversion`. -/
theorem ais_vstore_lane_typing_inversion (v_S : store) (v_C : context) (v_sz : sz) (ao : memarg)
    (l : laneidx) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [admininstr.VSTORE_LANE vectype.V128 v_sz ao l] (mkFunctype t1s t2s) →
    instrtype_sub (mkFunctype [valtype.I32, valtype.V128] []) (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t1, t2, hok, hsub⟩ := ais_single_plain_typing_inversion v_S v_C (instr.VSTORE_LANE vectype.V128 v_sz ao l) t1s t2s h
  simp only [mkFunctype] at hok
  cases hok <;> exact hsub

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

/-- Rocq `type_preservation.v:1607` `vec_store_preserves_2`: a store consumes its two operands
    and leaves nothing, so the result is typed by `Instrs_ok2.empty` over the *updated* store. -/
theorem vec_store_preserves_2 (v_S v_S' : store) (v_C : context) (a b op : admininstr) (t_a t_b : valtype)
    (v_ft : functype) :
    Instrs_ok2 v_S v_C [a, b, op] v_ft →
    (∀ t1s t2s, Instrs_ok2 v_S v_C [a] (mkFunctype t1s t2s) →
      instrtype_sub (mkFunctype [] [t_a]) (mkFunctype t1s t2s)) →
    (∀ t1s t2s, Instrs_ok2 v_S v_C [b] (mkFunctype t1s t2s) →
      instrtype_sub (mkFunctype [] [t_b]) (mkFunctype t1s t2s)) →
    (∀ t1s t2s, Instrs_ok2 v_S v_C [op] (mkFunctype t1s t2s) →
      instrtype_sub (mkFunctype [t_a, t_b] []) (mkFunctype t1s t2s)) →
    wf_store v_S' →
    Instrs_ok2 v_S' v_C [] v_ft := by
  intro h hinva hinvb hinvop hS'
  obtain ⟨hwfC, _, _⟩ := ainstrs_ok_context_store_wf v_S v_C _ v_ft h
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  obtain ⟨t3s, hrest, ha⟩ := ais_seq_typing_inversion v_S v_C [b, op] a t1s t2s h
  obtain ⟨t4s, hop, hb⟩ := ais_seq_typing_inversion v_S v_C [op] b t3s t2s hrest
  have h23 := instrtype_sub_compose1 [] [t_b] [t_a] [] t3s t4s t2s (hinvb t3s t4s hb) (hinvop t4s t2s hop)
  simp only [List.append_nil] at h23
  exact construct_ais_subtyping v_S' v_C [] [] [] t1s t2s (Instrs_ok2.empty v_S' v_C hS' hwfC)
    (instrtype_sub_compose [] [t_a] [] t1s t3s t2s (hinva t1s t3s ha) h23)

/-- Rocq `type_preservation.v:1631` `Step__vstore_preserves`. -/
theorem Step__vstore_preserves (v_S v_S' : store) (v_C : context) (i : num_) (c : vec_) (ao : memarg)
    (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c,
      admininstr.VSTORE vectype.V128 ao] v_ft →
    wf_store v_S' → Instrs_ok2 v_S' v_C [] v_ft := by
  intro h hS'
  exact vec_store_preserves_2 v_S v_S' v_C _ _ _ (valtype_numtype numtype.I32) valtype.V128 v_ft h
    (ais_const_typing_inversion v_S v_C numtype.I32 i)
    (ais_vconst_typing_inversion v_S v_C c)
    (ais_vstore_typing_inversion v_S v_C ao) hS'

/-- Rocq `type_preservation.v:1646` `Step__vstore_lane_preserves`. -/
theorem Step__vstore_lane_preserves (v_S v_S' : store) (v_C : context) (i : num_) (c : vec_) (v_sz : sz)
    (ao : memarg) (l : laneidx) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c,
      admininstr.VSTORE_LANE vectype.V128 v_sz ao l] v_ft →
    wf_store v_S' → Instrs_ok2 v_S' v_C [] v_ft := by
  intro h hS'
  exact vec_store_preserves_2 v_S v_S' v_C _ _ _ (valtype_numtype numtype.I32) valtype.V128 v_ft h
    (ais_const_typing_inversion v_S v_C numtype.I32 i)
    (ais_vconst_typing_inversion v_S v_C c)
    (ais_vstore_lane_typing_inversion v_S v_C v_sz ao l) hS'

/-! ### Plumbing for `t_preservation`

    `Frame_ok`'s conclusion types a frame at `<locals-only context> ++ C`
    (`wasm2.0.lean`), and `Config_ok`/`State_ok` carry that same appended
    context. These two small lemmas isolate the only two facts the top-level
    proof needs about that shape, so the (long) context literal appears in
    exactly one place. Rocq gets both for free from `resolve_inst_match` and
    its `_append`/`cats0` rewriting. -/

/-- Prefixing a context with a locals-only context leaves every component
    `inst_match` looks at untouched. -/
theorem inst_match_locals_append (tl : List valtype) (C : context) :
    inst_match C (({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [],
        ELEMS := [], DATAS := [], LOCALS := tl, LABELS := [], RETURN := none } : context) ++ C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- …and its `LOCALS` are exactly the prefix, since `Moduleinst_ok` forces the
    module context's own `LOCALS` to be empty (`inst_t_context_local_empty`). -/
theorem locals_append_eq (tl : List valtype) (C : context) (h : C.LOCALS = []) :
    ((({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [],
        ELEMS := [], DATAS := [], LOCALS := tl, LABELS := [], RETURN := none } : context)
      ++ C) : context).LOCALS = tl := by
  show tl ++ C.LOCALS = tl
  rw [h, List.append_nil]

/-! ### Shared helpers for the `Step`/`Step_read` case analyses (Lean-only)

    Rocq discharges most cases of `t_read_preservation`/`t_preservation_type` with its
    `invert_ais_typing; resolve_all_pt; join_subtyping_*; construct_ais_typing` automation
    (Ltac in `typing_lemmas.v`, not ported). These package the recurring shapes once: "k operands,
    then an operator whose principal type consumes them", plus the per-operator principal
    type inversions and a few well-formedness projections. -/

/-- One operand, then an operator `[t] -> out`: the pair has principal type `[] -> out`. -/
theorem ais_args1_typing (s : store) (C : context) (a op : admininstr) (out t1s t2s : List valtype)
    (ha : ∀ u1 u2, Instrs_ok2 s C [a] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hop : ∀ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [t] out) (mkFunctype u1 u2)) :
    Instrs_ok2 s C [a, op] (mkFunctype t1s t2s) → instrtype_sub (mkFunctype [] out) (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t3s, hop', ha'⟩ := ais_seq_typing_inversion s C [op] a t1s t2s h
  obtain ⟨ta, hsa⟩ := ha t1s t3s ha'
  obtain ⟨tout, hso⟩ := hop t3s t2s hop'
  exact (instrtype_sub_compose_eq [] [ta] [tout] out t1s t3s t2s hsa hso rfl).1

/-- Two operands, then an operator `[t, t'] -> out`. -/
theorem ais_args2_typing (s : store) (C : context) (a b op : admininstr) (out t1s t2s : List valtype)
    (ha : ∀ u1 u2, Instrs_ok2 s C [a] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hb : ∀ u1 u2, Instrs_ok2 s C [b] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2))
    (hop : ∀ u1 u2, Instrs_ok2 s C [op] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] out) (mkFunctype u1 u2)) :
    Instrs_ok2 s C [a, b, op] (mkFunctype t1s t2s) → instrtype_sub (mkFunctype [] out) (mkFunctype t1s t2s) := by
  intro h
  obtain ⟨t3s, hrest, ha'⟩ := ais_seq_typing_inversion s C [b, op] a t1s t2s h
  obtain ⟨t4s, hop', hb'⟩ := ais_seq_typing_inversion s C [op] b t3s t2s hrest
  obtain ⟨ta, hsa⟩ := ha t1s t3s ha'
  obtain ⟨tb, hsb⟩ := hb t3s t4s hb'
  obtain ⟨x, y, hso⟩ := hop t4s t2s hop'
  have h1 := (instrtype_sub_compose_le [] [tb] [y] [x] out t3s t4s t2s hsb hso rfl).1
  simp only [List.append_nil] at h1
  exact (instrtype_sub_compose_eq [] [ta] [x] out t1s t3s t2s hsa h1 rfl).1

/-- Three operands, then an operator `[t, t', t''] -> out`. -/
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
  intro h
  obtain ⟨t3s, hr1, ha'⟩ := ais_seq_typing_inversion s C [b, c, op] a t1s t2s h
  obtain ⟨t4s, hr2, hb'⟩ := ais_seq_typing_inversion s C [c, op] b t3s t2s hr1
  obtain ⟨t5s, hop', hc'⟩ := ais_seq_typing_inversion s C [op] c t4s t2s hr2
  obtain ⟨ta, hsa⟩ := ha _ _ ha'
  obtain ⟨tb, hsb⟩ := hb _ _ hb'
  obtain ⟨tc, hsc⟩ := hc _ _ hc'
  obtain ⟨x, y, z, hso⟩ := hop _ _ hop'
  have h1 := (instrtype_sub_compose_le [] [tc] [z] [x, y] out t4s t5s t2s hsc hso rfl).1
  simp only [List.append_nil] at h1
  have h2 := (instrtype_sub_compose_le [] [tb] [y] [x] out t3s t4s t2s hsb h1 rfl).1
  simp only [List.append_nil] at h2
  exact (instrtype_sub_compose_eq [] [ta] [x] out t1s t3s t2s hsa h2 rfl).1

theorem inv_val_arg (s : store) (C : context) (v : val) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr_val v] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) :=
  fun u1 u2 h => let ⟨t, hs, _⟩ := ais_single_val_typing_inversion s C v u1 u2 h; ⟨t, hs⟩

theorem inv_ref_arg (s : store) (C : context) (r : ref) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr_ref r] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) :=
  fun u1 u2 h => let ⟨_, hs, _⟩ := ais_single_ref_typing_inversion s C r u1 u2 h; ⟨_, hs⟩

theorem inv_const_arg (s : store) (C : context) (nt : numtype) (c : num_) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.CONST nt c] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) :=
  fun u1 u2 h => ⟨_, ais_const_typing_inversion s C nt c u1 u2 h⟩

theorem inv_vconst_arg (s : store) (C : context) (c : vec_) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.VCONST vectype.V128 c] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype u1 u2) :=
  fun u1 u2 h => ⟨_, ais_vconst_typing_inversion s C c u1 u2 h⟩

theorem inv_local_set (s : store) (C : context) (x : localidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.LOCAL_SET x] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [t] []) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, heq, _⟩ := hpt
  rw [heq] at hs
  exact ⟨_, hs⟩

theorem inv_global_set (s : store) (C : context) (x : globalidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.GLOBAL_SET x] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [t] []) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, heq, _⟩ := hpt
  rw [heq] at hs
  exact ⟨_, hs⟩

theorem inv_table_set (s : store) (C : context) (x : tableidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.TABLE_SET x] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] []) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, _, heq, _⟩ := hpt
  rw [heq] at hs
  exact ⟨_, _, hs⟩

theorem inv_table_grow (s : store) (C : context) (x : tableidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.TABLE_GROW x] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] [valtype.I32]) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, _, heq, _⟩ := hpt
  rw [heq] at hs
  exact ⟨_, _, hs⟩

theorem inv_elem_drop (s : store) (C : context) (x : elemidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.ELEM_DROP x] (mkFunctype u1 u2) →
      instrtype_sub (mkFunctype [] []) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, heq, _⟩ := hpt
  rw [heq] at hs
  exact hs

theorem inv_data_drop (s : store) (C : context) (x : dataidx) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.DATA_DROP x] (mkFunctype u1 u2) →
      instrtype_sub (mkFunctype [] []) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨heq, _⟩ := hpt
  rw [heq] at hs
  exact hs

theorem inv_store_none (s : store) (C : context) (nt : numtype) (marg : memarg) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.STORE nt none marg] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] []) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, _, heq, _⟩ := hpt
  rw [heq] at hs
  exact ⟨_, _, hs⟩

theorem inv_store_pack (s : store) (C : context) (nt : numtype) (k : Nat) (marg : memarg) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.STORE nt (some (sz.mk_sz k)) marg] (mkFunctype u1 u2) →
      ∃ t t', instrtype_sub (mkFunctype [t, t'] []) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, _, _, heq, _⟩ := hpt
  rw [heq] at hs
  exact ⟨_, _, hs⟩

theorem inv_memory_grow (s : store) (C : context) :
    ∀ u1 u2, Instrs_ok2 s C [admininstr.MEMORY_GROW] (mkFunctype u1 u2) →
      ∃ t, instrtype_sub (mkFunctype [t] [valtype.I32]) (mkFunctype u1 u2) := by
  intro u1 u2 h
  obtain ⟨_, _, hpt, hs⟩ := ais_single_typing_inversion s C _ u1 u2 h
  unfold ai_principal_typing at hpt
  obtain ⟨_, heq, _⟩ := hpt
  rw [heq] at hs
  exact ⟨_, hs⟩

theorem wf_config_ais {z : state} {ais : List admininstr} (h : wf_config (config.mk_config z ais)) :
    Forall wf_admininstr ais := by
  cases h with | config_case_0 _ _ _ h => exact h

theorem wf_config_store {s : store} {f : frame} {ais : List admininstr}
    (h : wf_config (config.mk_config (state.mk_state s f) ais)) : wf_store s := by
  cases h with | config_case_0 _ _ hst _ => cases hst with | state_case_0 _ _ h _ => exact h

/-- Lean-only helper: the frame of a well-formed configuration is well-formed. Renamed
    from `wf_config_frame` to free that name for the Rocq progress lemma
    `type_progress.v:870` `wf_config_frame` (a different statement), ported in TypeProgress.lean. -/
theorem wf_config_wf_frame {s : store} {f : frame} {ais : List admininstr}
    (h : wf_config (config.mk_config (state.mk_state s f) ais)) : wf_frame f := by
  cases h with | config_case_0 _ _ hst _ => cases hst with | state_case_0 _ _ _ h => exact h

theorem wf_const_num {nt : numtype} {c : num_} (h : wf_admininstr (admininstr.CONST nt c)) : wf_num_ nt c := by
  cases h with | admininstr_case_13 _ _ hn => exact hn

/-- The single-label context `Instr_ok2.label` pushes is well-formed (no tables/memories). -/
theorem wf_context_label_only (t : resulttype) :
    wf_context ({
      TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
      LOCALS := [], LABELS := [t], RETURN := none } : context) :=
  wf_context.context_case_ _ _ _ [] [] _ _ _ _ _ (by intro x hx; simp at hx) (by intro x hx; simp at hx)

/-- The return-only context `Instr_ok2_frame` pushes is well-formed. -/
theorem wf_context_return_only (t : resulttype) :
    wf_context ({
      TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
      LOCALS := [], LABELS := [], RETURN := some t } : context) :=
  wf_context.context_case_ _ _ _ [] [] _ _ _ _ _ (by intro x hx; simp at hx) (by intro x hx; simp at hx)

/-- Typing a freshly produced `CONST I32 c` at whatever type `[] -> [I32]` sits under. -/
theorem const_I32_result (s : store) (C : context) (c : num_) (t1s t2s : List valtype) :
    wf_num_ numtype.I32 c → wf_context C → wf_store s →
    instrtype_sub (mkFunctype [] [valtype.I32]) (mkFunctype t1s t2s) →
    Instrs_ok2 s C [admininstr.CONST numtype.I32 c] (mkFunctype t1s t2s) := fun hn hC hS hsub =>
  construct_ais_subtyping s C _ [] [valtype.I32] t1s t2s
    (construct_ais_typing_single s C _ [] [valtype.I32] (construct_ai_const_I32 s C c hn hC hS)) hsub

/-! ### `store_extension_reduce`: per-rule store cases

    Rocq proves `store_extension_reduce` by one induction on `Step`
    (`type_preservation.v:437-1502`): every rule that leaves the store alone is closed by
    `Extend_store_refl`, and each of the store-writing rules rebuilds `Extend_store` and
    `Store_ok` by hand from the `extend_*_refl`, `*_extension` and `construct_*` lemmas. The
    per-rule work is split out below (one lemma per store-writing rule), and
    `store_extension_reduce_aux` is the induction.

    **Deviation (intended, an improvement):** Rocq takes the post-store's well-formedness from
    `Step_is_wf`. Here every new store component's well-formedness comes from the reducing
    instruction sequence, the old store, or the `$growtable`/`$growmemory` relations' own
    premises, so this lemma does not depend on `Step_is_wf` (which was false in a corner case
    until spec commit `4cf9f29c5`; it is proved now, so this is only a difference
    of proof route). -/

theorem getElem?_eq_some_bang {α : Type} [Inhabited α] {l : List α} {k : Nat} {a : α}
    (h : l[k]? = some a) : k < l.length ∧ l[k]! = a := by
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp h
  exact ⟨hk, by rw [getElem!_pos l k hk]; exact he⟩

theorem wf_store_with_globals (s : store) (gs : List globalinst) :
    wf_store s → Forall wf_globalinst gs → wf_store { s with GLOBALS := gs } := by
  intro h hx
  cases h with
  | store_case_ _ _ _ _ _ _ hf _ ht hm hd => exact wf_store.store_case_ _ _ _ _ _ _ hf hx ht hm hd

theorem wf_store_with_tables (s : store) (ts : List tableinst) :
    wf_store s → Forall wf_tableinst ts → wf_store { s with TABLES := ts } := by
  intro h hx
  cases h with
  | store_case_ _ _ _ _ _ _ hf hg _ hm hd => exact wf_store.store_case_ _ _ _ _ _ _ hf hg hx hm hd

theorem wf_store_with_mems (s : store) (ms : List meminst) :
    wf_store s → Forall wf_meminst ms → wf_store { s with MEMS := ms } := by
  intro h hx
  cases h with
  | store_case_ _ _ _ _ _ _ hf hg ht _ hd => exact wf_store.store_case_ _ _ _ _ _ _ hf hg ht hx hd

theorem wf_store_with_elems (s : store) (es : List eleminst) :
    wf_store s → wf_store { s with ELEMS := es } := by
  intro h
  cases h with
  | store_case_ _ _ _ _ _ _ hf hg ht hm hd => exact wf_store.store_case_ _ _ _ _ _ _ hf hg ht hm hd

theorem wf_store_with_datas (s : store) (ds : List datainst) :
    wf_store s → Forall wf_datainst ds → wf_store { s with DATAS := ds } := by
  intro h hx
  cases h with
  | store_case_ _ _ _ _ _ _ hf hg ht hm _ => exact wf_store.store_case_ _ _ _ _ _ _ hf hg ht hm hx

theorem valtype_reftype_inj (rt rt' : reftype) : valtype_reftype rt = valtype_reftype rt' → rt = rt' := by
  cases rt <;> cases rt' <;> simp [valtype_reftype]

theorem externtype_table_sub_inv (tbt : tabletype) (lim : limits) (rt : reftype) :
    Externtype_sub (externtype.TABLE tbt) (externtype.TABLE (tabletype.mk_tabletype lim rt)) →
    ∃ lim', tbt = tabletype.mk_tabletype lim' rt := by
  intro h
  cases h with
  | table _ _ hsub _ _ => cases hsub; exact ⟨_, rfl⟩

/-- `global.set`'s operand has the declared type of a mutable global (Rocq: `invert_ais_typing;
    resolve_all_pt; join_subtyping_eq; Val_ok_non_bot; valtype_sub_non_bot`). -/
theorem ais_global_set_inv (s : store) (C : context) (v : val) (x : globalidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr_val v, admininstr.GLOBAL_SET x] (mkFunctype t1s t2s) →
    ∃ t, C.GLOBALS[proj_uN_0 x]? = some (globaltype.mk_globaltype (some r_MUT.MUT) t) ∧ Val_ok s v t := by
  intro h
  obtain ⟨t3s, hop, hv⟩ := ais_seq_typing_inversion s C [admininstr.GLOBAL_SET x] _ t1s t2s h
  obtain ⟨tv, hsv, hvok⟩ := ais_single_val_typing_inversion s C v t1s t3s hv
  obtain ⟨_, _, hpt, hso⟩ := ais_single_typing_inversion s C _ t3s t2s hop
  unfold ai_principal_typing at hpt
  obtain ⟨t, heq, hlk⟩ := hpt
  rw [heq] at hso
  have hrs := (instrtype_sub_compose_eq [] [tv] [t] [] t1s t3s t2s hsv hso rfl).2
  have hteq := valtype_sub_non_bot t tv (resulttype_sub_cons tv t [] [] hrs).1 (Val_ok_non_bot s v tv hvok)
  refine ⟨tv, ?_, hvok⟩
  rw [← hteq]; exact hlk

/-- `table.set`'s reference operand has the table's element type. -/
theorem ais_table_set_inv (s : store) (C : context) (i : num_) (r : ref) (x : tableidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr.CONST numtype.I32 i, admininstr_ref r, admininstr.TABLE_SET x] (mkFunctype t1s t2s) →
    ∃ rt lim, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) ∧ Ref_ok s r rt := by
  intro h
  obtain ⟨t3s, hr1, _⟩ := ais_seq_typing_inversion s C [admininstr_ref r, admininstr.TABLE_SET x] _ t1s t2s h
  obtain ⟨t4s, hop, hb⟩ := ais_seq_typing_inversion s C [admininstr.TABLE_SET x] _ t3s t2s hr1
  obtain ⟨rtr, hsb, hrok⟩ := ais_single_ref_typing_inversion s C r t3s t4s hb
  obtain ⟨_, _, hpt, hso⟩ := ais_single_typing_inversion s C _ t4s t2s hop
  unfold ai_principal_typing at hpt
  obtain ⟨rt, lim, heq, hlk⟩ := hpt
  rw [heq] at hso
  have hrs := (instrtype_sub_compose_le [] [valtype_reftype rtr] [valtype_reftype rt] [valtype.I32] []
    t3s t4s t2s hsb hso rfl).2
  have hteq := valtype_sub_non_bot _ _ (resulttype_sub_cons _ _ [] [] hrs).1 (Ref_ok_non_bot s r rtr hrok)
  refine ⟨rtr, lim, ?_, hrok⟩
  rw [← valtype_reftype_inj _ _ hteq]; exact hlk

/-- `table.grow`'s reference operand has the table's element type. -/
theorem ais_table_grow_inv (s : store) (C : context) (r : ref) (k : num_) (x : tableidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr_ref r, admininstr.CONST numtype.I32 k, admininstr.TABLE_GROW x] (mkFunctype t1s t2s) →
    ∃ rt lim, C.TABLES[proj_uN_0 x]? = some (tabletype.mk_tabletype lim rt) ∧ Ref_ok s r rt := by
  intro h
  obtain ⟨t3s, hr1, ha⟩ :=
    ais_seq_typing_inversion s C [admininstr.CONST numtype.I32 k, admininstr.TABLE_GROW x] _ t1s t2s h
  obtain ⟨t4s, hop, hb⟩ := ais_seq_typing_inversion s C [admininstr.TABLE_GROW x] _ t3s t2s hr1
  obtain ⟨rtr, hsa, hrok⟩ := ais_single_ref_typing_inversion s C r t1s t3s ha
  have hsb := ais_const_typing_inversion s C numtype.I32 k t3s t4s hb
  obtain ⟨_, _, hpt, hso⟩ := ais_single_typing_inversion s C _ t4s t2s hop
  unfold ai_principal_typing at hpt
  obtain ⟨rt, lim, heq, hlk⟩ := hpt
  rw [heq] at hso
  have h1 := (instrtype_sub_compose_le [] [valtype_numtype numtype.I32] [valtype.I32] [valtype_reftype rt]
    [valtype.I32] t3s t4s t2s hsb hso rfl).1
  simp only [List.append_nil] at h1
  have hrs := (instrtype_sub_compose_eq [] [valtype_reftype rtr] [valtype_reftype rt] [valtype.I32]
    t1s t3s t2s hsa h1 rfl).2
  have hteq := valtype_sub_non_bot _ _ (resulttype_sub_cons _ _ [] [] hrs).1 (Ref_ok_non_bot s r rtr hrok)
  refine ⟨rtr, lim, ?_, hrok⟩
  rw [← valtype_reftype_inj _ _ hteq]; exact hlk

theorem ais_elem_drop_inv (s : store) (C : context) (x : elemidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr.ELEM_DROP x] (mkFunctype t1s t2s) → ∃ rt, C.ELEMS[proj_uN_0 x]? = some rt := by
  intro h
  obtain ⟨_, _, hpt, _⟩ := ais_single_typing_inversion s C _ t1s t2s h
  unfold ai_principal_typing at hpt
  obtain ⟨rt, _, hlk⟩ := hpt
  exact ⟨rt, hlk⟩

theorem ais_data_drop_inv (s : store) (C : context) (x : dataidx) (t1s t2s : List valtype) :
    Instrs_ok2 s C [admininstr.DATA_DROP x] (mkFunctype t1s t2s) → C.DATAS[proj_uN_0 x]? = some datatype.OK := by
  intro h
  obtain ⟨_, _, hpt, _⟩ := ais_single_typing_inversion s C _ t1s t2s h
  unfold ai_principal_typing at hpt
  exact hpt.2

/-- A scalar `store` needs a memory in the context. -/
theorem ais_store_mems_inv (s : store) (C : context) (a b : admininstr) (nt : numtype) (o : Option sz)
    (ao : memarg) (t1s t2s : List valtype) :
    Instrs_ok2 s C [a, b, admininstr.STORE nt o ao] (mkFunctype t1s t2s) → 0 < C.MEMS.length := by
  intro h
  obtain ⟨u1, u2, hop⟩ := ais_seq3_last_typing s C a b _ _ h
  obtain ⟨_, _, hpt, _⟩ := ais_single_typing_inversion s C _ u1 u2 hop
  rcases o with _ | ⟨k⟩
  · unfold ai_principal_typing at hpt
    obtain ⟨mt, _, _, hmem, _⟩ := hpt
    exact (List.getElem?_eq_some_iff.mp hmem).fst
  · unfold ai_principal_typing at hpt
    obtain ⟨mt, _, _, _, hmem, _⟩ := hpt
    exact (List.getElem?_eq_some_iff.mp hmem).fst

/-- `memory.grow` needs a memory in the context. -/
theorem ais_memory_grow_inv (s : store) (C : context) (a : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 s C [a, admininstr.MEMORY_GROW] (mkFunctype t1s t2s) → 0 < C.MEMS.length := by
  intro h
  obtain ⟨t3s, hop, _⟩ := ais_seq_typing_inversion s C [admininstr.MEMORY_GROW] a t1s t2s h
  obtain ⟨_, _, hpt, _⟩ := ais_single_typing_inversion s C _ t3s t2s hop
  unfold ai_principal_typing at hpt
  obtain ⟨mt, _, hmem⟩ := hpt
  exact (List.getElem?_eq_some_iff.mp hmem).fst

theorem datatype_eq_OK (t : datatype) : t = datatype.OK := by cases t; rfl

/-- `datatype` has the single inhabitant `OK`, so the `Forall₂` and `Forall` forms of a list of
    `Datainst_ok` facts carry the same information (given the lengths `Store_ok` provides). -/
theorem datainsts_Forall_of_Forall₂ (s : store) (ds : List datainst) (dts : List datatype) :
    ds.length = dts.length → Forall₂ (fun v t => Datainst_ok s v t) ds dts →
    Forall (fun a => Datainst_ok s a datatype.OK) ds := by
  intro hlen h d hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  have hok := Forall2_nth_of_length ds dts h hlen i hi
  rw [getElem!_pos ds i hi, datatype_eq_OK (dts[i]!)] at hok
  exact hok

theorem datainsts_Forall₂_of_Forall (s : store) (ds : List datainst) (dts : List datatype) :
    Forall (fun a => Datainst_ok s a datatype.OK) ds → Forall₂ (fun v t => Datainst_ok s v t) ds dts := by
  intro h p hp
  obtain ⟨d, t⟩ := p
  rw [datatype_eq_OK t]
  exact h d (List.of_mem_zip hp).1

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

/-- Rocq `store_extension_reduce`, "Table Grow" case. Takes the rule's `fun_table` premise for the
    grown table (the relational `$table`; the old statement applied it as a function). -/
theorem table_grow_store_ok (s : store) (f : frame) (C C' : context) (r : ref) (v_n : Nat) (k : num_)
    (x : tableidx) (ti : tableinst) (var_2 : Option tableinst) (var_1 : tableinst) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr_ref r, admininstr.CONST numtype.I32 k, admininstr.TABLE_GROW x] (mkFunctype t1s t2s) →
    fun_growtable var_1 v_n r var_2 → fun_table (state.mk_state s f) x var_1 → var_2 ≠ none →
    Option.get! var_2 = ti →
    Extend_store s { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ => ti) } ∧
    Store_ok { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ => ti) } := by
  intro hsok hmi him htype hgrow htab hne hget
  obtain ⟨_, _, htab⟩ := fun_table_inv htab
  subst htab
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

theorem Store_ok_wf_store (s : store) (h : Store_ok s) : wf_store s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwf, _, _⟩ := Store_ok_parts s h
  exact hwf

/-- `rat_to_nat` is a left inverse of the `Nat → Rat` cast: the one property of it that the
    `memory.grow` case of `store_extension_reduce` needs (`$growmemory` stores the new page count
    as `rat_to_nat (|b*| / 64Ki + n)`, which in every `Store_ok` store is the natural number
    `lim_old + n`). Lean-only, no Rocq counterpart (its rational-to-`N` conversion is concrete).
    Follows from the definition of `rat_to_nat` (`wasm2.0.lean:9`), which used to be `opaque`. -/
theorem rat_to_nat_natCast (n : Nat) : rat_to_nat (n : Rat) = n := by
  simp [rat_to_nat]

/-- A well-formed `CONST (Inn) c` carries a `wf_uN` integer of the right width (used for the
    byte sequence `store_pack_val` writes). -/
theorem wf_num_Inn_proj (v_Inn : Inn) (c : num_) :
    wf_num_ (numtype_Inn v_Inn) c → proj_num__0 c ≠ none →
    wf_uN (Option.get! (size (valtype_Inn v_Inn))) (Option.get! (proj_num__0 c)) := by
  intro h hne
  cases h with
  | num__case_0 v_Inn' x _ hwf heq =>
    have : v_Inn = v_Inn' := by
      cases v_Inn <;> cases v_Inn' <;> first | rfl | (simp [numtype_Inn] at heq)
    subst this
    exact hwf
  | num__case_1 _ _ _ _ => exact absurd rfl hne

theorem wf_vconst_parts {vt : vectype} {c : vec_} (h : wf_admininstr (admininstr.VCONST vt c)) :
    size (valtype_vectype vt) ≠ none ∧ wf_uN (Option.get! (size (valtype_vectype vt))) c := by
  cases h with | admininstr_case_20 _ _ h1 h2 => exact ⟨h1, h2⟩

/-- Rocq `store_extension_reduce`, the four memory-store cases (`store_num_val`,
    `store_pack_val`, `vstore_val`, `vstore_lane_val`), stated over the rules' `fun_with_mem`
    premise (the relational `$with_mem`). It writes `b*` with `splice`, which is
    `list_slice_update` with length `|b*|` (`splice_eq_list_slice_update`), so each case is
    `mem_store_extension` (as in Rocq, which calls it for the two SIMD cases and inlines it for
    the two scalar ones). The length argument `fun_with_mem` receives is unused by `splice`. -/
theorem with_mem_store_ok (s : store) (f : frame) (s' : store) (f' : frame) (C C' : context)
    (off len : Nat) (b_lst : List byte) :
    fun_with_mem (state.mk_state s f) (uN.mk_uN 0) off len b_lst (state.mk_state s' f') →
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' → 0 < C'.MEMS.length →
    Forall wf_byte b_lst → Extend_store s s' ∧ Store_ok s' := by
  intro hw hsok hmi him hmem hwfb
  cases hw
  simp only [splice_eq_list_slice_update]
  exact mem_store_extension s f C C' off b_lst b_lst.length hsok (Store_ok_wf_store s hsok) hmi him hmem
    hwfb rfl

/-- Rocq `store_extension_reduce`, "Memory Grow" case. Takes the rule's `fun_mem` premise for
    the grown memory (the relational `$mem`; the old statement applied it as a function). Uses
    `rat_to_nat_natCast` above for the new page count. -/
theorem memory_grow_store_ok (s : store) (f : frame) (C C' : context) (a : admininstr) (v_n : Nat)
    (mi : meminst) (var_2 : Option meminst) (var_1 : meminst) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [a, admininstr.MEMORY_GROW] (mkFunctype t1s t2s) →
    fun_growmemory var_1 v_n var_2 → fun_mem (state.mk_state s f) (uN.mk_uN 0) var_1 → var_2 ≠ none →
    Option.get! var_2 = mi →
    Extend_store s { s with
      MEMS := list_update_func s.MEMS (f.MODULE.MEMS[0]!) (fun _ => mi) } ∧
    Store_ok { s with
      MEMS := list_update_func s.MEMS (f.MODULE.MEMS[0]!) (fun _ => mi) } := by
  intro hsok hmi him htype hgrow hmem hne hget
  obtain ⟨_, _, hmem⟩ := fun_mem_inv hmem
  subst hmem
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

/-- Generalized form of `store_extension_reduce` (same `remember`/`generalize dependent`
    encoding as `reduce_inst_unchanged_aux`). The context rules recurse (the congruence rules
    carry the inner configuration's `wf_config` as a premise), the store-writing rules invert
    their `fun_with_*` premise (the four memory stores hand `fun_with_mem` to `with_mem_store_ok`,
    which inverts it) and go to the per-rule lemmas above, and every other rule leaves the store
    unchanged. -/
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
  case global_set z v x var_0 hw =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    cases hw
    exact global_set_store_ok s f C C' v x t1s t2s hsok hmi him htype
  case table_set_val z i r x var_1 var_0 _ _ hw _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    cases hw
    exact table_set_store_ok s f C C' i r x _ t1s t2s hsok hmi him htype
  case table_grow_succeed z r k x ti var_2 var_1 var_0 hgrow htab hw hne hget =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    cases hw
    exact table_grow_store_ok s f C C' r k _ x ti var_2 var_1 t1s t2s hsok hmi him htype hgrow htab hne
      hget
  case elem_drop z x var_0 hw =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    cases hw
    exact elem_drop_store_ok s f C C' x t1s t2s hsok hmi him htype
  case store_num_val z i nt c ao b_lst var_0 _ _ hw hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    have hwfn : wf_num_ nt c := wf_const_num (wf_config_ais hwfc _ (by simp))
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hw hsok hmi him
      (ais_store_mems_inv _ _ _ _ _ _ _ t1s t2s htype) (nbytes__is_wf nt c b_lst hwfn hb)
  case store_pack_val z i v_Inn c k ao b_lst var_0 _ hw _ hc hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    have hwfn : wf_num_ (numtype_Inn v_Inn) c := wf_const_num (wf_config_ais hwfc _ (by simp))
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hw hsok hmi him
      (ais_store_mems_inv _ _ _ _ _ _ _ t1s t2s htype)
      (ibytes__is_wf k _ b_lst (wrap___is_wf _ k _ _ (wf_num_Inn_proj v_Inn c hwfn hc) rfl) hb)
  case vstore_val z i c ao b_lst var_0 _ _ hw hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    obtain ⟨u1, u2, hop⟩ := ais_seq3_last_typing _ _ _ _ _ _ htype
    have hwfv : wf_admininstr (admininstr.VCONST vectype.V128 c) := wf_config_ais hwfc _ (by simp)
    obtain ⟨hsz, hwfu⟩ := wf_vconst_parts hwfv
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hw hsok hmi him
      (ais_vstore_mems_inversion _ _ ao u1 u2 hop) (vbytes__is_wf vectype.V128 c b_lst hsz hwfu hb)
  case vstore_lane_val z i c v_N ao j b_lst v_Jnn v_M var_1 var_0 _ _ hw _ _ _ _ hb hwfl =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    obtain ⟨u1, u2, hop⟩ := ais_seq3_last_typing _ _ _ _ _ _ htype
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hw hsok hmi him
      (ais_vstore_lane_mems_inversion _ _ v_N ao j u1 u2 hop) (ibytes__is_wf v_N _ b_lst hwfl hb)
  case memory_grow_succeed z v_n mi var_2 var_1 var_0 hgrow hmem hw hne hget _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    cases hw
    exact memory_grow_store_ok s f C C' _ v_n mi var_2 var_1 t1s t2s hsok hmi him htype hgrow hmem hne
      hget
  case data_drop z x var_0 hw =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1
    injection h2 with hz2 _
    subst hz1 hais1 hz2
    cases hw
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

/-! ### Helpers for `t_read_preservation` (Lean-only)

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
  have hwf := default__is_wf t _ _ (fun_default_default t) hd rfl
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

/-- Rocq `type_preservation.v:1661` `t_read_preservation`: preservation under the read-only
    reduction relation (no store mutation). `Qed` in Rocq; proved here for all 47
    `Step_read` rules. As in Rocq, the reduct's well-formedness comes from the generated
    `Step_read_is_wf`, which is proved (in `wasm2.0.lean`; it was `Admitted` in Rocq and `sorry`
    here until the spec fixed the memory.fill/copy/init `CONST I32 2^32` corner case in commit
    `4cf9f29c5`).

    **Signature deviation (intended):** the locals hypothesis is
    `Vals_ok v_s v_f.LOCALS v_C'.LOCALS`, i.e. Rocq's
    `Forall2 (fun v_t v_val => Val_ok v_s v_val v_t) (context_LOCALS v_C') (LOCALS v_f)` plus
    the length equation. Rocq's inductive `Forall2` implies equal lengths; Lean's generated
    `Forall₂` is zip-based and does not, and the `local.get` case uses the length (with
    `Forall2_nth_of_length`) to index the locals (the same kind of deviation as `funcinst_same`'s
    `hlen`; since `sideconditions_on_defs` the rule's `fun_local` premise also bounds the index by
    `F.LOCALS`, so there the length is convenient rather than necessary). The only caller,
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
  | block z k val_lst bt instr_lst v_n t_1_lst t_2_lst ft h0 h1 h2 h3 h4 =>
    subst h1
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
          hwfS hwfC' (hwf' _ (List.mem_singleton_self _)) (wf_context_label_only _) h4)) hsub
  | loop z k val_lst bt instr_lst t_1_lst v_n t_2_lst ft h0 h1 h2 h3 h4 =>
    subst h1
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
          hwfS hwfC' (hwf' _ (List.mem_singleton_self _)) (wf_context_label_only _) h3)) hsub
  | call z x h0 =>
    obtain ⟨u1, u2, hlk, hs⟩ := pt_call _ _ x htype
    obtain ⟨hx, hget⟩ := getElem?_eq_some_bang hlk
    have hea := minst_func_externaddr _ _ _ _ _ hmi him hx
    rw [hget] at hea
    exact construct_ais_subtyping _ _ _ u1 u2 t1s t2s
      (construct_ais_typing_single _ _ _ u1 u2 (Instr_ok2.call_addr _ _ _ u1 u2 hea hwfS hwfC'
        (hwf' _ (List.mem_singleton_self _)) (wf_externtype.externtype_case_0 _))) hs
  | call_indirect_call z i x y a ft ti h0 h1 h2 h3 h4 h5 h6 =>
    obtain ⟨t3, hop, hc⟩ := ais_seq_typing_inversion _ _ [admininstr.CALL_INDIRECT x y] _ t1s t2s htype
    obtain ⟨u1, u2, lim, _, hty, hs⟩ := pt_call_indirect _ _ x y hop
    have s1 := ais_const_typing_inversion _ _ numtype.I32 i t1s t3 hc
    have isub := (instrtype_sub_compose_le [] [valtype_numtype numtype.I32] [valtype.I32] u1 u2 t1s t3 t2s s1 hs rfl).1
    simp only [List.append_nil] at isub
    obtain ⟨hy, hgety⟩ := getElem?_eq_some_bang hty
    have htypes := minst_invert_functypes _ _ _ _ hmi him
    have h4' : v_f.MODULE.TYPES[proj_uN_0 y]! = (v_s.FUNCS[a]!).TYPE := (fun_type_inv h0).2.symm.trans h6
    have hfty : (v_s.FUNCS[a]!).TYPE = mkFunctype u1 u2 := by
      rw [← h4', ← htypes]; exact hgety
    have hea0 := Externaddr_ok.func v_s a (v_s.FUNCS[a]!) h5 rfl hwfS
      (by rw [hfty]; exact wf_externtype.externtype_case_0 _)
    rw [hfty] at hea0
    exact construct_ais_subtyping _ _ _ u1 u2 t1s t2s
      (construct_ais_typing_single _ _ _ u1 u2 (Instr_ok2.call_addr _ _ _ u1 u2 hea0 hwfS hwfC'
        (hwf' _ (by simp)) (wf_externtype.externtype_case_0 _))) isub
  | call_indirect_trap z i x y h0 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | call_addr z k val_lst a v_n f instr_lst t_1_lst t_2_lst mm v_func x t_lst o_lst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
    obtain ⟨t3s, hV, hC⟩ := ais_composition_typing _ _ _ _ t1s t2s htype
    obtain ⟨vts, hsubV, hvok⟩ := ais_vals_typing_inversion _ _ val_lst t1s t3s hV
    obtain ⟨ts1, ts2, hext, hsubC⟩ := pt_call_addr _ _ a hC
    obtain ⟨xt, fi, ha, hfi, hxt, _, hxsub⟩ := Externaddr_invert_funcs _ _ _ hext
    subst hxt
    have hft := externtype_func_eq _ _ hxsub
    have h1' : v_s.FUNCS[a]! = ({
        TYPE := functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst), MODULE := mm, CODE := v_func } : funcinst) := h3
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
    rw [h4] at hfo
    have hIok := func_ok_body _ _ _ _ _ _ hfo
    have ho : o_lst = Map default_ t_lst := by
      have key : ∀ (l1 : List (Option val)) (l2 : List valtype),
          List.Forall₂ (fun o t => fun_default_ t o) l1 l2 → l1 = Map default_ l2 := by
        intro l1 l2 hl
        induction hl with
        | nil => rfl
        | cons hab _ ih => simp only [Map, List.map_cons] at ih ⊢; rw [fun_default_eq hab, ih]
      exact key _ _ (to_mathlib_forall₂ h0 h1)
    have hd : Forall (fun t => default_ t ≠ none) t_lst := fun t ht =>
      h5 _ (by rw [ho]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
    have hloc : Map (fun o => Option.get! o) o_lst = Map (fun t => Option.get! (default_ t)) t_lst := by
      rw [ho]; simp [Map]
    rw [hloc] at h6 h9
    subst h6
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
        (Forall2_app_intro (by omega) hvok.2 (default_vals_ok _ _ hwfS hd)) hwfS hwfC0 h9 hwfCL
    refine construct_ais_subtyping _ _ _ [] t_2_lst t1s t2s
      (construct_ais_typing_single _ _ _ [] t_2_lst
        (Instr_ok2.Instr_ok2_frame _ v_C' v_n _ _ t_2_lst _ hframe ?_ hwfS hwfC' hwfC1 hwfF
          (wf_context_return_only _) h12)) hsub
    refine Expr_ok2.mk_Expr_ok2 _ _ _ t_2_lst ?_ hwfS hwfCR
      (fun e he => by rw [List.mem_singleton] at he; subst he; exact hwfL)
    exact construct_ais_typing_single _ _ _ [] t_2_lst
      (Instr_ok2.label _ _ v_n [] _ t_2_lst t_2_lst
        ((ais_empty_typing _ _ t_2_lst t_2_lst).mpr ⟨hwfCR, hwfS, resulttype_sub_refl _⟩)
        (construct_instrs_from_ais _ _ instr_lst [] t_2_lst hwfS hIok)
        hwfS hwfCR hwfL (wf_context_label_only _) h12)
  | ref_func z x h0 =>
    obtain ⟨ft, hlk, hs⟩ := pt_ref_func _ _ x htype
    obtain ⟨hx, _⟩ := getElem?_eq_some_bang hlk
    have hea := minst_func_externaddr _ _ _ _ _ hmi him hx
    have hr : Ref_ok v_s (ref.REF_FUNC_ADDR (v_f.MODULE.FUNCS[proj_uN_0 x]!)) reftype.FUNCREF :=
      Ref_ok.func _ _ _ hea hwfS (wf_externtype.externtype_case_0 _)
    exact construct_ais_subtyping _ _ _ [] _ t1s t2s (ais_ref1 _ _ _ _ hr hwfC' hwfS) hs
  | local_get z x v h0 =>
    obtain ⟨_, rfl⟩ := fun_local_inv h0
    obtain ⟨t, hlk, hs⟩ := pt_local_get _ _ x htype
    obtain ⟨hx, hget⟩ := getElem?_eq_some_bang hlk
    have hv : Val_ok v_s (v_f.LOCALS[proj_uN_0 x]!) t := by
      have h := Forall2_nth_of_length v_C'.LOCALS v_f.LOCALS hvals.2 hvals.1 (proj_uN_0 x) hx
      rw [hget] at h; exact h
    exact construct_ais_subtyping _ _ _ [] [t] t1s t2s (ais_val1 _ _ _ t hv hwfC' hwfS) hs
  | global_get z x gi h0 =>
    obtain ⟨_, _, rfl⟩ := fun_global_inv h0
    obtain ⟨t, m, hlk, hs⟩ := pt_global_get _ _ x htype
    obtain ⟨hx, hget⟩ := getElem?_eq_some_bang hlk
    have hv := lookup_global (proj_uN_0 x) v_C v_C' m t v_s v_f.MODULE hx hget hmi him hsok
    exact construct_ais_subtyping _ _ _ [] [t] t1s t2s (ais_val1 _ _ _ t hv hwfC' hwfS) hs
  | table_get_trap z i x h0 h1 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | table_get_val z i x ti h0 h1 h2 =>
    obtain ⟨t3, hop, hc⟩ := ais_seq_typing_inversion _ _ [admininstr.TABLE_GET x] _ t1s t2s htype
    obtain ⟨rt, lim, hlk, hs⟩ := pt_table_get _ _ x hop
    have s1 := ais_const_typing_inversion _ _ numtype.I32 i t1s t3 hc
    have isub := (instrtype_sub_compose_eq [] [valtype_numtype numtype.I32] [valtype.I32] [valtype_reftype rt]
      t1s t3 t2s s1 hs rfl).1
    have hrefs := table_refs_ok _ _ _ _ x rt lim hsok hmi him hlk
    rw [← (fun_table_inv h2).2.2] at hrefs
    have hr := hrefs (ti.REFS[proj_uN_0 (Option.get! (proj_num__0 i))]!)
      (by rw [getElem!_pos ti.REFS _ h0]; exact List.getElem_mem h0)
    exact construct_ais_subtyping _ _ _ [] _ t1s t2s (ais_ref1 _ _ _ rt hr hwfC' hwfS) isub
  | table_size z x v_n h0 =>
    exact const_I32_result _ _ _ t1s t2s (wf_const_num (hwf' _ (by simp))) hwfC' hwfS (pt_table_size _ _ x htype)
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
  | table_init_succ z j i v_n x y ti ei h0 h1 h2 h3 h4 h5 h6 =>
    obtain ⟨_, _, hop⟩ := ais_seq4_last _ _ _ _ _ _ t1s t2s htype
    obtain ⟨rt, lim, hlx, hly, _⟩ := pt_table_init _ _ x y hop
    have isub := ais_args3_typing _ _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _) (inv_const_arg _ _ _ _)
      (fun u1 u2 h => let ⟨_, _, _, _, hs⟩ := pt_table_init _ _ x y h; ⟨_, _, _, hs⟩) htype
    obtain ⟨hx, hgetx⟩ := getElem?_eq_some_bang hlx
    obtain ⟨hy, hgety⟩ := getElem?_eq_some_bang hly
    have hwftt : wf_tabletype (tabletype.mk_tabletype lim rt) := by rw [← hgetx]; exact wf_context_tab _ _ hx hwfC'
    have hrefs := elem_refs_ok _ _ _ _ y rt hmi him hly
    rw [← (fun_elem_inv h4).2.2] at hrefs
    have hr := hrefs (ei.REFS[proj_uN_0 (Option.get! (proj_num__0 i))]!)
      (by rw [getElem!_pos ei.REFS _ h0]; exact List.getElem_mem h0)
    refine construct_ais_subtyping _ _ _ [] [] t1s t2s ?_ isub
    exact (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype_reftype rt] [] (ais_ref1 _ _ _ rt hr hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype_reftype rt] [] [] (ais_plain1 _ _ (instr.TABLE_SET x) _ _ hwfS (Instr_ok.table_set _ x rt lim hx hgetx hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_SET x) (by simp))) hwftt))
      (ais_cons_pre _ _ _ _ [] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [valtype.I32, valtype.I32] [] [valtype.I32] [] (ais_const1 _ _ numtype.I32 _ (wf_const_num (hwf' _ (by simp))) hwfC' hwfS)
      (ais_cons_pre _ _ _ _ [] [valtype.I32, valtype.I32, valtype.I32] [] [] (ais_plain1 _ _ (instr.TABLE_INIT x y) _ _ hwfS (Instr_ok.table_init _ x y lim rt hx hgetx hy hgety hwfC' ((wf_admininstr_instr _).mpr (hwf' (admininstr.TABLE_INIT x y) (by simp))) hwftt))
      (ais_nil_refl _ _ [] hwfC' hwfS))))))))
  | load_num_trap z i nt ao h0 h1 h2 h3 =>
    exact construct_ais_trap _ _ _ hwfC' hwfS
  | load_num_val z i nt ao c mi h0 h1 h2 h3 h4 h5 =>
    have isub := ais_args1_typing _ _ _ _ [valtype_numtype nt] t1s t2s (inv_const_arg _ _ _ i)
      (fun u1 u2 h => ⟨_, pt_load_none _ _ nt ao h⟩) htype
    exact construct_ais_subtyping _ _ _ [] _ t1s t2s (ais_const1 _ _ nt c h4 hwfC' hwfS) isub
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
  case global_set z v x _ _ =>
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
  case table_set_val z i r x _ _ _ _ _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (ais_args2_typing _ _ _ _ _ [] t1s t2s (inv_const_arg _ _ numtype.I32 i) (inv_ref_arg _ _ r) (inv_table_set _ _ x) htype)⟩
  case table_grow_succeed z r k x _ _ _ _ _ _ _ _ _ =>
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
  case elem_drop z x _ _ =>
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
  case store_num_val z i nt c ao _ _ _ _ _ _ =>
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
  case store_pack_val z i v_Inn c k ao _ _ _ _ _ _ _ =>
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
  case data_drop z x _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hwfc2 _ _ hext _ _ _ _ htype
    injection h1 with hz1 hais1
    injection h2 with _ hais2
    subst hz1 hais1 hais2
    obtain ⟨hwfC', _, _⟩ := ainstrs_ok_context_store_wf _ _ _ _ htype
    exact (ais_empty_typing _ C' t1s t2s).mpr ⟨hwfC', Extend_store_wf_store' _ _ hext,
      instrtype_sub_empty t1s t2s (inv_data_drop _ _ x t1s t2s htype)⟩

/-- Rocq `type_preservation.v:3137` `t_preservation_type`. **The central preservation
    lemma for the whole `Step` relation** (subsumes `t_read_preservation`). `Qed` in Rocq,
    SIMD cases included. Dispatches `Step_pure` to
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

/-- Rocq `type_preservation.v:3412` `t_preservation`. **THE top-level theorem** — Rocq
    source comment: `(* Ultimate goal of project *)`. Whole-program preservation: reduction
    (`Step`) on a full `config` preserves well-typedness at the same fixed result type.
    `Qed` in Rocq; proved here by the same composition (`store_extension_reduce`,
    `t_preservation_vs_type`, `t_preservation_type`, `reduce_inst_unchanged`,
    `Extend_store_moduleinst`). -/
theorem t_preservation (config1 : config) (rt : resulttype) (config2 : config) :
    Step config1 config2 → Config_ok config1 rt → Config_ok config2 rt := by
  intro step_configs config1_ok
  obtain ⟨⟨store1, frame1⟩, ais1⟩ := config1
  obtain ⟨⟨store2, frame2⟩, ais2⟩ := config2
  cases config1_ok with
  | mk_Config_ok _ _ _ rt' C state1_ok expr1_ok context_ok config1_ok' _ =>
    cases state1_ok with
    | mk_State_ok _ _ _ store1_ok frame1_ok _ _ =>
      generalize frame1_def : frame1 = f at frame1_ok
      cases frame1_ok with
      | mk_Frame_ok
        frame1locals
        frame1minst
        localstypes
        frame1minstcontext
        frame1minst_ok_store1
        frame1locals_length_match_types
        frame1locals_ok_forall
        _
        minstcontext_wf
        _
        frame1localsonlycontext_wf
        =>
        obtain rfl : frame1minst = frame1.MODULE := by rw [frame1_def]
        obtain rfl : frame1locals = frame1.LOCALS := by rw [frame1_def]
        clear frame1_def
        cases expr1_ok with
        | mk_Expr_ok2 _ _ _ ais1_ok _ _ _ =>

          -- for readability, restore variables from earlier
          set config1 : config := config.mk_config (state.mk_state store1 frame1) ais1
          set config2 : config := config.mk_config (state.mk_state store2 frame2) ais2
          set rt : resulttype := list.mk_list rt'
          set C := (
            {
                TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
                LOCALS := localstypes, LABELS := [], RETURN := none
            }
            ++ frame1minstcontext
          )
          set state2 := state.mk_state store2 frame2

          -- well-formedness of the post-state, from the generated `Step_is_wf`
          have config2_wf : wf_config config2 :=
            Step_is_wf _ ais1 _ config1_ok' store1_ok step_configs
          have ais2_wf : Forall wf_admininstr ais2 := by
            change wf_config (config.mk_config (state.mk_state store2 frame2) ais2) at config2_wf
            cases config2_wf with | config_case_0 _ _ _ h => exact h
          have state2_wf : wf_state state2 := by
            change wf_config (config.mk_config (state.mk_state store2 frame2) ais2) at config2_wf
            cases config2_wf with | config_case_0 _ _ h _ => exact h
          have store2_wf : wf_store store2 := by
            change wf_state (state.mk_state store2 frame2) at state2_wf
            cases state2_wf with | state_case_0 _ _ h _ => exact h
          have frame2_wf : wf_frame frame2 := by
            change wf_state (state.mk_state store2 frame2) at state2_wf
            cases state2_wf with | state_case_0 _ _ _ h => exact h

          -- the module context's own LOCALS are empty, so the appended context's
          -- LOCALS are exactly the frame's local types
          have frame1minstcontext_has_no_locals : frame1minstcontext.LOCALS = [] :=
            inst_t_context_local_empty
              store1
              frame1.MODULE
              frame1minstcontext
              frame1minst_ok_store1
          have frame1minstcontext_matches_C :
            inst_match
              frame1minstcontext
              C
            :=
              inst_match_locals_append localstypes frame1minstcontext

          -- store extension + store typedness across the step
          obtain ⟨extend_stores, store2_ok⟩ :=
            store_extension_reduce
              store1 _ ais1 store2 frame2 ais2 frame1minstcontext _ _
              config1_ok' step_configs frame1minst_ok_store1 ais1_ok
              frame1minstcontext_matches_C store1_ok

          have frame1minst_is_frame2minst : frame1.MODULE = frame2.MODULE :=
            reduce_inst_unchanged
              store1
              _
              ais1
              store2
              frame2
              ais2
              step_configs

          have frame1minst_ok_store2 : Moduleinst_ok store2 frame1.MODULE frame1minstcontext :=
            Extend_store_moduleinst
              store1
              store2
              frame1.MODULE
              frame1minstcontext
              extend_stores
              frame1minst_ok_store1

          have frame2locals_ok : Vals_ok store2 frame2.LOCALS localstypes := by

            -- locals stay well-typed
            have frame2locals_ok'
              :
              Vals_ok
                store2
                frame2.LOCALS
                C.LOCALS
              :=
              t_preservation_vs_type
                store1 _ ais1 store2 frame2 ais2 frame1minstcontext
                _ [] rt' step_configs store1_ok extend_stores
                frame1minst_ok_store1
                (by rw [locals_append_eq localstypes frame1minstcontext frame1minstcontext_has_no_locals]; exact ⟨frame1locals_length_match_types, frame1locals_ok_forall⟩)
                frame1minstcontext_matches_C ais1_ok

            -- resolves that frame2locals_ok is actually just also referencing localstypes
            rw [locals_append_eq localstypes frame1minstcontext frame1minstcontext_has_no_locals] at frame2locals_ok'

            exact frame2locals_ok'

          obtain ⟨frame2locals_length_match_types, frame2locals_ok_forall⟩ := frame2locals_ok

          -- and so does the instruction sequence
          have ais2_ok
            :
            Instrs_ok2 store2
              C
              ais2 (mkFunctype [] rt')
            :=
            t_preservation_type
              store1 _ ais1 store2 frame2 ais2 frame1minstcontext _ [] rt' config1_ok' step_configs
              store1_ok store2_ok extend_stores frame1minst_ok_store1 frame1minst_ok_store2
              (by rw [locals_append_eq localstypes frame1minstcontext frame1minstcontext_has_no_locals]; exact ⟨frame1locals_length_match_types, frame1locals_ok_forall⟩) frame1minstcontext_matches_C ais1_ok

          have frame2minst_ok : Moduleinst_ok store2 frame2.MODULE frame1minstcontext := by
            rw [← frame1minst_is_frame2minst]
            exact frame1minst_ok_store2

          -- reassemble
          exact
            Config_ok.mk_Config_ok
              store2
              frame2
              ais2
              rt'
              _
              (
                State_ok.mk_State_ok
                  store2
                  frame2
                  _
                  store2_ok
                  (
                    Frame_ok.mk_Frame_ok
                      store2
                      frame2.LOCALS
                      frame2.MODULE
                      localstypes
                      frame1minstcontext
                      frame2minst_ok
                      frame2locals_length_match_types
                      frame2locals_ok_forall
                      store2_wf
                      minstcontext_wf
                      frame2_wf
                      frame1localsonlycontext_wf
                  )
                  context_ok
                  state2_wf
              )
              (
                Expr_ok2.mk_Expr_ok2
                  store2
                  _
                  ais2
                  rt'
                  ais2_ok
                  store2_wf
                  context_ok
                  ais2_wf
              )
              context_ok
              config2_wf
              state2_wf

end TLC

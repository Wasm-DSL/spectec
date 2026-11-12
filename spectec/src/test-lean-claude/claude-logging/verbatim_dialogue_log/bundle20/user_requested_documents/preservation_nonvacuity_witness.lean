import TypePreservation

/-!
Non-vacuity witness for `TLC.t_preservation` (bundle20 audit, subagent audit-nonvacuity).
Scratch file outside the repository; NOT part of the project.

Witness: a store with exactly one (mutable, i32) global, a module instance whose only entry is
that global address, a frame with no locals, `ts = []`, and the configuration `[NOP]` stepping to
`[]` (`Step.pure` + `Step_pure.nop`). A second witness uses `[CONST I32 0, DROP]` stepping to `[]`
(`Step.pure` + `Step_pure.drop`).

Why not an all-empty module instance: the generated `Moduleinst_ok` (and Rocq's) has the premise
`List.length (GLOBAL globaladdr* ++ MEM memaddr* ++ TABLE tableaddr* ++ FUNC funcaddr*) > 0`.
Why a mutable global: the generated `Globaltype_ok` (and Rocq's) only has the constructor
`Globaltype_ok (globaltype.mk_globaltype (some r_MUT.MUT) t)`.
-/

namespace NonVacuity

/-- `CONST I32 0` as a `num_` payload. -/
abbrev n0 : num_ := num_.mk_num__0 Inn.I32 (uN.mk_uN 0)

/-- `CONST I32 0` as a value. -/
abbrev v0 : val := val.CONST numtype.I32 n0

/-- A mutable i32 global type. -/
abbrev gt0 : globaltype := globaltype.mk_globaltype (some r_MUT.MUT) valtype.I32

abbrev gi0 : globalinst := { TYPE := gt0, VALUE := v0 }

/-- Store with exactly one global and nothing else. -/
abbrev s0 : store :=
  { FUNCS := [], GLOBALS := [gi0], TABLES := [], MEMS := [], ELEMS := [], DATAS := [] }

/-- Module instance whose only entry is global address 0. -/
abbrev mi0 : moduleinst :=
  { TYPES := [], FUNCS := [], GLOBALS := [0], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    EXPORTS := [] }

abbrev f0 : frame := { LOCALS := [], MODULE := mi0 }

/-- The module context produced by `Moduleinst_ok`. -/
abbrev Cmod : context :=
  { TYPES := [], FUNCS := [], GLOBALS := [gt0], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := [], LABELS := [], RETURN := none }

/-- The locals-only context that `Frame_ok` prepends (no locals). -/
abbrev Cloc : context :=
  { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := [], LABELS := [], RETURN := none }

/-- The frame context, exactly as `Frame_ok` produces it. -/
abbrev C0 : context := Cloc ++ Cmod

abbrev z0 : state := state.mk_state s0 f0

abbrev c1 : config := config.mk_config z0 [admininstr.NOP]
abbrev c2 : config := config.mk_config z0 []
abbrev ts : resulttype := .mk_list []

/-! ### Generic vacuity helpers (`Forall`/`Forall₂` over `[]`) -/

theorem forall_nil {α : Type} (P : α → Prop) : Forall P [] := by
  intro x hx; cases hx

theorem forall2_nil {α β : Type} (P : α → β → Prop) : Forall₂ P [] [] := by
  intro t ht; simp at ht

/-! ### Well-formedness facts -/

theorem wf_n0 : wf_num_ numtype.I32 n0 :=
  wf_num_.num__case_0 numtype.I32 Inn.I32 (uN.mk_uN 0) (by decide)
    (wf_uN.uN_case_0 _ 0 ⟨Nat.zero_le _, Nat.zero_le _⟩) rfl

theorem wf_v0 : wf_val v0 := wf_val.val_case_0 _ _ wf_n0

theorem wf_gi0 : wf_globalinst gi0 := wf_globalinst.globalinst_case_ _ _ wf_v0

theorem wf_s0 : wf_store s0 :=
  wf_store.store_case_ [] [gi0] [] [] [] []
    (forall_nil _)
    (by intro x hx; simp at hx; subst hx; exact wf_gi0)
    (forall_nil _) (forall_nil _) (forall_nil _)

theorem wf_mi0 : wf_moduleinst mi0 :=
  wf_moduleinst.moduleinst_case_ [] [] [0] [] [] [] [] [] (forall_nil _)

theorem wf_f0 : wf_frame f0 := wf_frame.frame_case_ [] mi0 (forall_nil _) wf_mi0

theorem wf_z0 : wf_state z0 := wf_state.state_case_0 s0 f0 wf_s0 wf_f0

theorem wf_Cmod : wf_context Cmod :=
  wf_context.context_case_ [] [] [gt0] [] [] [] [] [] [] none (forall_nil _) (forall_nil _)

theorem wf_Cloc : wf_context Cloc :=
  wf_context.context_case_ [] [] [] [] [] [] [] [] [] none (forall_nil _) (forall_nil _)

theorem wf_C0 : wf_context C0 :=
  wf_context.context_case_ [] [] [gt0] [] [] [] [] [] [] none (forall_nil _) (forall_nil _)

/-! ### Store, module instance, frame, state -/

theorem gi0_ok : Globalinst_ok s0 gi0 gt0 :=
  Globalinst_ok.mk_Globalinst_ok s0 (some r_MUT.MUT) valtype.I32 v0
    (Globaltype_ok.mk_Globaltype_ok valtype.I32)
    (Val_ok.numtype s0 numtype.I32 _ wf_s0 wf_v0)
    wf_s0 wf_gi0

theorem s0_ok : Store_ok s0 :=
  Store_ok.mk_Store_ok s0 [gi0] [gt0] [] [] [] [] [] [] [] [] [] []
    rfl
    (by intro t ht; simp at ht; subst ht; exact gi0_ok)
    rfl (forall2_nil _) rfl (forall2_nil _) rfl (forall2_nil _) rfl (forall2_nil _)
    rfl (forall2_nil _)
    rfl wf_s0 (forall_nil _) (forall_nil _) wf_s0

theorem glob0_ok : Externaddr_ok s0 (externaddr.GLOBAL 0) (externtype.GLOBAL gt0) :=
  Externaddr_ok.global s0 0 gi0 (by decide) rfl wf_s0 (wf_externtype.externtype_case_1 _)

theorem mi0_ok : Moduleinst_ok s0 mi0 Cmod :=
  Moduleinst_ok.mk_Moduleinst_ok s0 [] [] [0] [] [] [] [] [] [] [gt0] [] [] [] []
    (forall_nil _)
    rfl (by intro t ht; simp at ht; subst ht; exact glob0_ok)
    rfl (forall2_nil _)
    rfl (forall2_nil _)
    rfl (forall2_nil _)
    (forall_nil _)
    rfl (forall_nil _) (forall2_nil _)
    rfl (forall_nil _) (forall2_nil _)
    rfl
    (by decide)
    (forall_nil _)
    wf_s0 wf_mi0 wf_Cmod
    (by intro x hx; simp at hx; subst hx; exact wf_externtype.externtype_case_1 _)
    (forall_nil _) (forall_nil _) (forall_nil _)

theorem f0_ok : Frame_ok s0 f0 C0 :=
  Frame_ok.mk_Frame_ok s0 [] mi0 [] Cmod mi0_ok rfl (forall2_nil _) wf_s0 wf_Cmod wf_f0 wf_Cloc

theorem z0_ok : State_ok z0 C0 := State_ok.mk_State_ok s0 f0 C0 s0_ok f0_ok wf_C0 wf_z0

/-! ### Witness 1: `[NOP] ~> []` -/

theorem nop_ok : Expr_ok2 s0 C0 [admininstr.NOP] (.mk_list []) :=
  Expr_ok2.mk_Expr_ok2 s0 C0 [admininstr.NOP] []
    (Instrs_ok2.instr s0 C0 admininstr.NOP [] []
      (Instr_ok2.plain s0 C0 instr.NOP [] [] (Instr_ok.nop C0 wf_C0 wf_instr.instr_case_0)
        wf_s0 wf_C0 wf_instr.instr_case_0)
      wf_s0 wf_C0 wf_admininstr.admininstr_case_0)
    wf_s0 wf_C0
    (by intro x hx; simp at hx; subst hx; exact wf_admininstr.admininstr_case_0)

theorem wf_c1 : wf_config c1 :=
  wf_config.config_case_0 z0 [admininstr.NOP] wf_z0
    (by intro x hx; simp at hx; subst hx; exact wf_admininstr.admininstr_case_0)

/-- Hypothesis 2 of `t_preservation` holds for the witness. -/
theorem c1_ok : Config_ok c1 ts :=
  Config_ok.mk_Config_ok s0 f0 [admininstr.NOP] [] C0 z0_ok nop_ok wf_C0 wf_c1 wf_z0

/-- Hypothesis 1 of `t_preservation` holds for the witness. -/
theorem c1_step : Step c1 c2 :=
  Step.pure z0 [admininstr.NOP] [] Step_pure.nop

/-- Both hypotheses at once (the joint-satisfiability statement). -/
theorem hyps_satisfiable : ∃ (c1 c2 : config) (ts : resulttype), Step c1 c2 ∧ Config_ok c1 ts :=
  ⟨c1, c2, ts, c1_step, c1_ok⟩

/-- Applying the theorem to the witness. -/
theorem c2_ok : Config_ok c2 ts := TLC.t_preservation c1 ts c2 c1_step c1_ok

/-! ### Witness 2: `[CONST I32 0, DROP] ~> []` -/

abbrev d1 : config := config.mk_config z0 [admininstr.CONST numtype.I32 n0, admininstr.DROP]

theorem constdrop_ok :
    Expr_ok2 s0 C0 [admininstr.CONST numtype.I32 n0, admininstr.DROP] (.mk_list []) :=
  Expr_ok2.mk_Expr_ok2 s0 C0 _ []
    (Instrs_ok2.seq s0 C0 [admininstr.CONST numtype.I32 n0] [admininstr.DROP] [] [] [valtype.I32]
      (Instrs_ok2.instr s0 C0 (admininstr.CONST numtype.I32 n0) [] [valtype.I32]
        (Instr_ok2.plain s0 C0 (instr.CONST numtype.I32 n0) [] [valtype.I32]
          (Instr_ok.const C0 numtype.I32 n0 wf_C0 (wf_instr.instr_case_13 _ _ wf_n0))
          wf_s0 wf_C0 (wf_instr.instr_case_13 _ _ wf_n0))
        wf_s0 wf_C0 (wf_admininstr.admininstr_case_13 _ _ wf_n0))
      (Instrs_ok2.instr s0 C0 admininstr.DROP [valtype.I32] []
        (Instr_ok2.plain s0 C0 instr.DROP [valtype.I32] []
          (Instr_ok.drop C0 valtype.I32 wf_C0 wf_instr.instr_case_2)
          wf_s0 wf_C0 wf_instr.instr_case_2)
        wf_s0 wf_C0 wf_admininstr.admininstr_case_2)
      wf_s0 wf_C0
      (by intro x hx; simp at hx; subst hx; exact wf_admininstr.admininstr_case_13 _ _ wf_n0)
      (by intro x hx; simp at hx; subst hx; exact wf_admininstr.admininstr_case_2))
    wf_s0 wf_C0
    (by
      intro x hx; simp at hx
      rcases hx with hx | hx <;> subst hx
      · exact wf_admininstr.admininstr_case_13 _ _ wf_n0
      · exact wf_admininstr.admininstr_case_2)

theorem wf_d1 : wf_config d1 :=
  wf_config.config_case_0 z0 _ wf_z0
    (by
      intro x hx; simp at hx
      rcases hx with hx | hx <;> subst hx
      · exact wf_admininstr.admininstr_case_13 _ _ wf_n0
      · exact wf_admininstr.admininstr_case_2)

theorem d1_ok : Config_ok d1 ts :=
  Config_ok.mk_Config_ok s0 f0 _ [] C0 z0_ok constdrop_ok wf_C0 wf_d1 wf_z0

theorem d1_step : Step d1 c2 :=
  Step.pure z0 _ [] (Step_pure.drop v0)

theorem d2_ok : Config_ok c2 ts := TLC.t_preservation d1 ts c2 d1_step d1_ok

/-! ### Machine-checked evidence for the two satisfiability findings -/

/-- The empty module instance (exactly the one `fun_invoke` puts in its frame). -/
abbrev emptyMI : moduleinst :=
  { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    EXPORTS := [] }

/-- Finding 1: in no store and no context is the empty module instance `Moduleinst_ok`. -/
theorem emptyMI_not_ok (s : store) (C : context) : ¬ Moduleinst_ok s emptyMI C := by
  intro h
  cases h
  simp_all [Map]

/-- Finding 1, consequence: no configuration produced by `$invoke` is `Config_ok`, so
`t_preservation` never applies to an invocation's initial configuration. -/
theorem invoke_config_not_ok (s : store) (fa : funcaddr) (vals : List val) (c : config)
    (hinv : fun_invoke s fa vals c) (ts : resulttype) : ¬ Config_ok c ts := by
  intro hc
  cases hinv with
  | fun_invoke_case_0 _ _ f _ _ hf =>
    subst hf
    cases hc with
    | mk_Config_ok _ _ _ _ _ hstate =>
      cases hstate with
      | mk_State_ok _ _ _ _ hframe =>
        cases hframe with
        | mk_Frame_ok _ _ _ _ hmod => exact emptyMI_not_ok _ _ hmod

/-- Finding 2: an immutable global type is never `Globaltype_ok`. -/
theorem immutable_globaltype_not_ok (t : valtype) :
    ¬ Globaltype_ok (globaltype.mk_globaltype none t) := by
  intro h; cases h

/-- The witness store with its one global made immutable. -/
abbrev gi_imm : globalinst := { TYPE := globaltype.mk_globaltype none valtype.I32, VALUE := v0 }

abbrev s_imm : store :=
  { FUNCS := [], GLOBALS := [gi_imm], TABLES := [], MEMS := [], ELEMS := [], DATAS := [] }

/-- Finding 2, consequence: a store holding one immutable i32 global is not `Store_ok`. -/
theorem s_imm_not_ok : ¬ Store_ok s_imm := by
  intro hs
  cases hs with
  | mk_Store_ok gl gts _ _ _ _ _ _ _ _ _ _ hlen hgl _ _ _ _ _ _ _ _ _ _ heq =>
    have hgl' : gl = [gi_imm] := (congrArg store.GLOBALS heq).symm
    subst hgl'
    rcases gts with _ | ⟨g, _ | ⟨g', gts'⟩⟩
    · simp at hlen
    · have h := hgl (gi_imm, g) (by simp)
      cases h with
      | mk_Globalinst_ok _ _ _ hgt => cases hgt
    · simp at hlen

end NonVacuity

#check @TLC.t_preservation
#print axioms NonVacuity.c1_ok
#print axioms NonVacuity.c1_step
#print axioms NonVacuity.hyps_satisfiable
#print axioms NonVacuity.d1_ok
#print axioms NonVacuity.d1_step
#print axioms NonVacuity.c2_ok
#print axioms NonVacuity.d2_ok
#print axioms NonVacuity.emptyMI_not_ok
#print axioms NonVacuity.invoke_config_not_ok
#print axioms NonVacuity.immutable_globaltype_not_ok
#print axioms NonVacuity.s_imm_not_ok

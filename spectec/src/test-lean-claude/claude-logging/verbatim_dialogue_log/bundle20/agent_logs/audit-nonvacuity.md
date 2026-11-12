# audit-nonvacuity — non-vacuity witness for `TLC.t_preservation` (bundle20)

## Task

Subagent "audit-nonvacuity" of the bundle20 preservation audit. Goal: build a machine-checked
witness that the hypotheses of `TLC.t_preservation`
(`Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts`) are jointly satisfiable, i.e. the theorem is
not vacuous. Concretely: pick `c1`, `c2`, `ts`, prove `Step c1 c2` and `Config_ok c1 ts`, then apply
`TLC.t_preservation`. Report anything surprising about satisfiability as findings. Lean is allowed
for this task only via `timeout 900 lake env lean <abs path>` on ONE scratch file `Witness.lean`
in the scratch dir (never `lake build`, never two Lean processes at once).

Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/audit-nonvacuity/`

## Safety check (START)

```
safety check [audit-nonvacuity] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Progress (written incrementally)

- Read shared brief `scratchpad/briefs/audit_brief.md` (lines 1-146, complete) and task file
  `scratchpad/briefs/task_nonvacuity.md` (lines 1-33, complete).

## Resumed (v2 relaunch)

The first wave was killed by the usage limit after reading the brief; no `Witness.lean` existed
in the scratch dir (directory empty). Work restarted from scratch.

- Read shared brief v2 `scratchpad/briefs/audit_brief_v2.md` (lines 1-169, complete), task file
  `scratchpad/briefs/task2_nonvacuity.md` (lines 1-9) and original task `task_nonvacuity.md`
  (complete).

### Safety check (START, v2)

```
safety check [audit-nonvacuity] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T110027.780706365Z-audit-nonvacuity-1407704.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

### What I read (v2, targeted ranges)

- `TypePreservation.lean` l.2695-2710 (`t_preservation` statement; `namespace TLC` l.29-2751).
- `wasm2.0.lean`: `Forall`/`Forall₂` l.17-21; `disjoint_` l.121-124; `uN`/`wf_uN` l.166-180;
  `numtype`/`valtype` l.520-560; `Inn` l.579-595; `limits`..`externtype`/`wf_externtype`
  l.700-770; `num_`/`wf_num_` l.896-925; `wf_instr` l.1980-2018; `externaddr`..`wf_val`
  l.11272-11340; `exportinst`..`globalinst` l.11356-11440; `store`..`wf_state` l.11498-11562;
  `admininstr`/`wf_admininstr` (heads) l.11562-11570, 11730-11768; `admininstr_instr` l.11642-11657;
  `config`/`wf_config` l.11957-11975; `context`/`append_context`/`wf_context`/`Functype_ok`/
  `Globaltype_ok` l.12623-12695; `Instr_ok` nop/drop/const l.12825-12992; `Step_pure` nop/drop
  l.13746-13747; `Step` l.14699-14712; `Externaddr_ok` l.15547-15580; `Val_ok` l.15597-15610;
  `Exportinst_ok` l.15655-15665; `Moduleinst_ok` l.15671-15740; `Frame_ok` l.15743-15780;
  `Instr_ok2` (plain) l.15785-15792; `Instrs_ok2`/`Expr_ok2` l.15874-15916; `Globalinst_ok`
  l.15921-15935; `Store_ok` l.15992-16025; `State_ok`/`Config_ok` l.16315-16333.
- Rocq `wasm.v` l.17155-17183 (`Moduleinst_ok`, `Frame_ok`), l.14685-14686 (`Globaltype_ok`).
- Spec `specification/wasm-2.0/B-soundness.spectec` l.196-226 (`Moduleinst_ok` rule),
  `6-typing.spectec` l.21-22, 35-36 (`Globaltype_ok`).

### Two satisfiability surprises found while reading (details in Findings)

1. `Moduleinst_ok` (Lean l.15688 and Rocq `wasm.v` l.17174) requires
   `|GLOBAL globaladdr* ++ MEM memaddr* ++ TABLE tableaddr* ++ FUNC funcaddr*| > 0`, so an
   all-empty module instance is NOT `Moduleinst_ok`; the suggested all-empty witness is
   impossible. The spec rule only says `(if exportinst.ADDR <- (GLOBAL globaladdr)* ...)*`.
2. `Globaltype_ok` (Lean l.12688-12689, Rocq l.14685-14686) only admits `some MUT`, although the
   spec rule is `|- MUT? t : OK`. So every global of a `Store_ok` store must be mutable.

Witness design consequently: store with one mutable i32 global (`CONST I32 0`), module instance
`GLOBALS := [0]` (everything else empty), frame without locals, `ts = []`; witness 1 `[NOP] ~> []`
via `Step.pure` + `Step_pure.nop`; witness 2 `[CONST I32 0, DROP] ~> []` via `Step_pure.drop`.

### Lean runs (6 total; always `cd .../test-lean-claude && timeout 900 lake env lean <scratch>/Witness.lean`, one at a time)

| run | result | note |
|---|---|---|
| 1 | exit 0, no errors/warnings | first draft (witness 1 `[NOP]` + witness 2 `[CONST I32 0, DROP]`) compiled as written; ~2 s wall, max RSS 3.6 GB |
| 2 | exit 0 | temporary read-only `#eval` (removed afterwards) recomputed Lake's source hashes: `wasm2.0.lean` = `711b692ecbe2b7e3`, `TypePreservation.lean` = `4868dd4c31f381cf`, identical to the `inputs` recorded in `.lake/build/lib/lean/{wasm2.0,TypePreservation}.trace` |
| 3 | exit 1 | added finding lemmas; 3 positional `cases ... with` pattern errors |
| 4 | exit 1 | fixed 3; one left (same cause) |
| 5 | exit 0, 1 linter warning | redundant `<;> omega` |
| 6 | exit 0, no errors/warnings | final |

Why runs 3-4 failed: Lean 4 promotes leading indices that every constructor uses as the same bare variable
into inductive *parameters*, so `Store_ok`, `Frame_ok`, `Moduleinst_ok`, `Globalinst_ok` (the store `s`)
and `fun_invoke` (`s`, `fa`) have fewer constructor fields than the generated binder lists suggest;
positional `cases ... with | ctor _ _ ...` patterns must omit them. `Config_ok`/`State_ok` (first index
is a constructor application) are unaffected.

Olean freshness: `wasm2.0.lean` has mtime 14:54 local, newer than `wasm2.0.olean` (11:55) and the
downstream oleans (13:22). It is content-identical, though: `git status` reports no change against
HEAD `0a7507f41` (committed 00:21), and run 2 reproduced Lake's recorded source hash exactly. So the
witness was checked against the current sources.

Side note: the IDE (VS Code Lean extension) briefly opened the scratch file after an `Edit` and
reported a spurious `unknown module prefix 'TypePreservation'` with its default toolchain
(v4.30.0-rc2, since the file is outside the lake project). To avoid triggering editor Lean
processes, all later scratch edits were done with `sed`.

### Final `Witness.lean` (verbatim; 282 lines, sha256 prefix bf19d3956a35e023)

```lean
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
```

### Final Lean output (run 6, verbatim)

```
TLC.t_preservation : ∀ (c1 : config) (ts : resulttype) (c2 : config), Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts
'NonVacuity.c1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonVacuity.c1_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonVacuity.hyps_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonVacuity.d1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonVacuity.d1_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonVacuity.c2_ok' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NonVacuity.d2_ok' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'NonVacuity.emptyMI_not_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonVacuity.invoke_config_not_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonVacuity.immutable_globaltype_not_ok' does not depend on any axioms
'NonVacuity.s_imm_not_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Findings

**F0 [info, result] Non-vacuity established (machine-checked).**
`NonVacuity.hyps_satisfiable : ∃ c1 c2 ts, Step c1 c2 ∧ Config_ok c1 ts` and both
`Config_ok` witnesses (`c1_ok` for `[NOP]`, `d1_ok` for `[CONST I32 0, DROP]`) and both steps
depend only on `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Applying
`TLC.t_preservation` (`c2_ok`, `d2_ok`) adds `sorryAx`, as expected from the 33 known generated
`sorry`s. Store: one mutable i32 global; module instance `GLOBALS := [0]`, all else empty; frame
without locals; `ts = []`. The suggested all-empty witness is impossible (F1).

**F1 [major, new; independently corroborates audit-isabelle F1] `Moduleinst_ok` carries a hoisted
nonemptiness premise that the spec does not state, so an all-empty module instance (the one
`$invoke` uses) is never typable.**
- Lean `wasm2.0.lean:15690`: `(List.length ((Map (fun v => externaddr.GLOBAL v) globaladdr_lst) ++ (... MEM ... ++ (... TABLE ... ++ ... FUNC ...)))) > 0 →`
- Rocq `wasm.v:17174` `(... >? 0%N)%BN`; Isabelle generated reference `isabelle_reference_output_wasm2.thy:13634` `... > 0)`.
- Spec `B-soundness.spectec:230` only: `-- (if exportinst.ADDR <- (GLOBAL globaladdr)* (MEM memaddr)* (TABLE tableaddr)* (FUNC funcaddr)*)*` (per-export membership, vacuous with no exports).
- Root cause (shared middle-end, read-only check): `spectec/src/middlend/sideconditions.ml:62-63` adds `|xs| > 0` for every `x <- xs` (`MemE`); the `iterPr` smart constructor (l.21-28) then drops the now-dead iteration variable `exportinst` and, because `iter <= List1 && vars' = []`, returns the bare premise. That hoisting is unsound for a `*` iteration with zero elements.
- Machine-checked consequences: `NonVacuity.emptyMI_not_ok : ∀ s C, ¬ Moduleinst_ok s emptyMI C` and `NonVacuity.invoke_config_not_ok : fun_invoke s fa vals c → ∀ ts, ¬ Config_ok c ts` (standard axioms only). `fun_invoke` (`wasm2.0.lean:15452-15484`) builds its frame with `MODULE := { TYPES := [], FUNCS := [], GLOBALS := [], ... EXPORTS := [] }` (l.15456ff).
- Effect: `t_preservation` is still true and non-vacuous, but never applies to the configuration `$invoke` produces, or to any frame whose module has no global/mem/table/func. Not a Lean-port deviation (identical in all three backends).
- The other 13 `> 0` premises in `wasm2.0.lean` were glanced at: l.2082/11832 are trivially true constant lists; l.9556-9637 and 13798-13874 accompany real memberships into result sets, where nonemptiness is already implied. They were not audited in depth.

**F2 [major, known-undocumented] `Globaltype_ok` admits only mutable globals, so every `Store_ok`
store (and every valid module) has only mutable globals.**
- Lean `wasm2.0.lean:12688-12689`: `| mk_Globaltype_ok (t : valtype) : Globaltype_ok (globaltype.mk_globaltype (some r_MUT.MUT) t)`; Rocq `wasm.v:14685-14686` `Globaltype_ok (mk_globaltype (Some MUT) t)`; Isabelle reference l.11392-11394 same.
- Spec `6-typing.spectec:35-36`: `rule Globaltype_ok: |- MUT? t : OK` (any mutability). `Global_ok` (spec l.591-595; Lean l.13469-13476) clearly intends both: `Globaltype_ok gt → gt = mk_globaltype v_mut t → ...` with `v_mut` free.
- Chain: `Store_ok` → `Forall₂ Globalinst_ok` → `Globalinst_ok.mk_Globalinst_ok` premise `Globaltype_ok (mk_globaltype v_mut t)` (l.15921-15923).
- Machine-checked: `NonVacuity.immutable_globaltype_not_ok : ¬ Globaltype_ok (mk_globaltype none t)` (no axioms); `NonVacuity.s_imm_not_ok : ¬ Store_ok s_imm` for the witness store with its global made immutable (standard axioms).
- Prior mention: `claude-logging/for-claude/digest_wasm_v.md:260-268` flagged it only as "possibly unusual ... worth double-checking", never confirmed. Shared by all three backends, so it is not a Lean porting deviation; the root cause (rendering of an option iteration `MUT?` with no iteration variable as the constant `Some MUT`) was not traced. The 6 hand-written proof files never mention `Globaltype_ok` (0 occurrences each).
- Effect: preservation is still true and non-vacuous, but covers only stores whose globals are all mutable.

**F3 [info] Build freshness.** `wasm2.0.lean`'s mtime is newer than all oleans, but the content
is unchanged (git status clean against HEAD; Lake source hash `711b692ecbe2b7e3` reproduced). There is
no staleness, and the main thread's "lake build clean" stands.

## Unsure / notes
- F1's root-cause attribution to `sideconditions.ml` comes from reading the code (l.21-28, 62-63, 113-120), not from running the pipeline.
- F2's root cause is not traced. Only the spec text vs. the generated output across three backends is established.
- A non-vacuity witness says nothing about the *strength* of the conclusion: `Config_ok c2 ts` for the empty instruction list is also directly provable. As a spot check, `Resulttype_sub` (l.12735-12739) carries an explicit length premise, so `Instrs_ok2.sub` cannot retype `[]` as `[] -> [t]` through the zip-based `Forall₂`.

## Safety check (END, v2)

```
safety check [audit-nonvacuity] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T111428.916898417Z-audit-nonvacuity-1414080.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Scratch files (outside the repo): `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/audit-nonvacuity/` (Witness.lean, run1-6.txt). No repository file other than this log was created or modified by this agent. The safety-check script itself writes its own uniquely named check log into `claude-logging/safety-checks/`, as the brief requires.

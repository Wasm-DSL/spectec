# prove-C09 log (bundle20 progress port, batch C09)

Targets (TypeProgress.lean): t_progress_be_vswizzle (:1898), t_progress_be_vshuffle (:1907), t_progress_be_vsplat (:1918);
Rocq source: type_progress.v:3963-4068 (bullets of t_progress_be). Only this log file was written inside the repo;
all scratch work is in /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C09/. TypeProgress.lean was NOT edited. No state-changing git; no agents spawned.

## Safety check (START)
```
safety check [prove-C09] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T132430.475032623Z-prove-C09-1497547.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- Work.lean = `import TypeProgress` + each target header copied verbatim by script (build.py; renamed `<name>_proof`) +
  `example : type_of% @<name>_proof = type_of% @<name> := rfl` guard. Checked with `timeout 900 lake env lean Work.lean`
  (one Lean process at a time). All three compiled on the first attempt; guards passed.
- Extra check Work_ax.lean (build_ax.py): the 7 still-`sorry` earlier lemmas used were replaced by local axioms with
  identical statements => `#print axioms` shows no sorryAx, i.e. sorryAx in Work.lean comes only from those lemmas.
- Porting: follows the Rocq bullets step by step (invert typeof of the operand values, wf_instr inversion fixing the
  shape to I8x16 (and |i_lst| = 16 for vshuffle), lanes_Jnn_form for both operands, the padded/concatenated lane list
  cs with its well-formedness and length (Hcsw/Hcsl), then apply Step_pure.vswizzle/vshuffle/vsplat with Pnn = I8,
  M = 16, k = 0). Rocq holds_upto_intro steps are done inline (intro k hk; List.mem_range), Rocq wf_uN_lt' is replaced
  by a direct inversion of wf_uN 8 (Hx256), and getElem!_pos + List.getElem_mem replace Forall_size.

## t_progress_be_vswizzle — status: proved
- still-sorry earlier lemmas used: invert_typeof_V128 (:241), lanes_Jnn_form (:942), jlane_some (:953), jlane_proj_wf (:1205). Project axiom: lanes_len (HelperLemmas).
- notes: also uses def jlane (:933); Lean core getElem!_pos, List.getElem_mem, List.eq_of_mem_replicate.

Proof body (tactic block after `:= by`, exactly as compiled):
```lean
  intro C sh HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP2
    have Hsh : sh = ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim 16)) := by
      cases HWfinstr; assumption
    subst Hsh
    have Hwsh : wf_shape (shape.X lanetype.I8 (dim.mk_dim 16)) :=
      wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (Or.inr rfl)) rfl
    have HL1 : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1) :=
      lanes_Jnn_form Jnn.I8 16 c1 Hwsh Hwf1
    have HL2 : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) :=
      lanes_Jnn_form Jnn.I8 16 c2 Hwsh Hwf2
    obtain ⟨cs, Hcs⟩ : ∃ cs : List iN, cs = List.map (fun l => Option.get! (proj_lane__0 l))
        (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1) ++
        List.replicate (Int.toNat ((256 : Int) - ((16 : Nat) : Int))) (uN.mk_uN 0) := ⟨_, rfl⟩
    have Hcsw : Forall (fun x => wf_uN 8 x) cs := by
      intro x hx
      rw [Hcs, List.mem_append] at hx
      rcases hx with hx | hx
      · exact jlane_proj_wf Jnn.I8 _ HL1 x hx
      · rw [List.eq_of_mem_replicate hx]
        exact wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩
    have Hcsl : cs.length = 256 := by
      rw [Hcs, List.length_append, List.length_map, lanes_len, List.length_replicate]
      all_goals decide
    have Hidx : ∀ k, k < 16 → ∃ x, (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2)[k]! =
        lane_.mk_lane__0 Jnn.I8 x ∧ wf_uN 8 x := by
      intro k hk
      have hk' : k < (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2).length := by
        rw [lanes_len]; exact hk
      rw [getElem!_pos _ k hk']
      exact HL2 _ (List.getElem_mem hk')
    have Hx256 : ∀ x : uN, wf_uN 8 x → proj_uN_0 x < 256 := by
      intro x hx
      cases hx with
      | uN_case_0 i h =>
        have h2 : i ≤ 255 := h.2
        simp only [proj_uN_0]; omega
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
    refine ⟨s, f, _, Step.pure _ _ _ (Step_pure.vswizzle c1 c2 packtype.I8 16 _
      (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) cs 0 rfl ?_ ?_ ?_ ?_ ?_ rfl Hwsh ?_ ?_)⟩
    · exact jlane_some Jnn.I8 _ HL1
    · exact Hcs
    · intro k hk
      rw [List.mem_range] at hk
      obtain ⟨x, Hx, Hwx⟩ := Hidx k hk
      rw [Hx, Hcsl]
      exact Hx256 x Hwx
    · intro k hk
      rw [List.mem_range] at hk
      obtain ⟨x, Hx, _⟩ := Hidx k hk
      rw [Hx]; simp [proj_lane__0]
    · intro k hk
      rw [List.mem_range] at hk
      rw [lanes_len]; exact hk
    · exact wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩
    · intro k hk
      rw [List.mem_range] at hk
      obtain ⟨x, Hx, Hwx⟩ := Hidx k hk
      rw [Hx]
      have hj : proj_uN_0 x < cs.length := by rw [Hcsl]; exact Hx256 x Hwx
      refine wf_lane_.lane__case_0 _ _ _ ?_ ?_
      · show wf_uN 8 (cs[proj_uN_0 x]!)
        rw [getElem!_pos cs _ hj]
        exact Hcsw _ (List.getElem_mem hj)
      · rfl
  · simp at Hts
```

## t_progress_be_vshuffle — status: proved
- still-sorry earlier lemmas used: invert_typeof_V128 (:241), lanes_Jnn_form (:942), jlane_proj_wf (:1205), jlane_map_proj (:1212). Project axiom: lanes_len (HelperLemmas).
- notes: also uses def jlane (:933); Lean core getElem!_pos, List.getElem_mem.

Proof body (tactic block after `:= by`, exactly as compiled):
```lean
  intro C sh i_lst Hilt HWfC HWfdim HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP1
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP2
    have Hshlen : sh = ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim 16)) ∧ i_lst.length = 16 := by
      cases HWfinstr; assumption
    obtain ⟨Hsh, Hlen⟩ := Hshlen
    subst Hsh
    have Hwsh : wf_shape (shape.X lanetype.I8 (dim.mk_dim 16)) :=
      wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (Or.inr rfl)) rfl
    have HL1 : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1) :=
      lanes_Jnn_form Jnn.I8 16 c1 Hwsh Hwf1
    have HL2 : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) :=
      lanes_Jnn_form Jnn.I8 16 c2 Hwsh Hwf2
    have HL : Forall (jlane Jnn.I8) (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1 ++
        lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact HL1 l hl
      · exact HL2 l hl
    obtain ⟨cs, Hcs⟩ : ∃ cs : List iN, cs = List.map (fun l => Option.get! (proj_lane__0 l))
        (lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c1 ++
         lanes_ (shape.X lanetype.I8 (dim.mk_dim 16)) c2) := ⟨_, rfl⟩
    have Hcsw : Forall (fun x => wf_uN 8 x) cs := by
      rw [Hcs]; exact jlane_proj_wf Jnn.I8 _ HL
    have Hcsl : cs.length = 32 := by
      rw [Hcs, List.length_map, List.length_append, lanes_len, lanes_len]
    have Hi32 : ∀ k, k < 16 → proj_uN_0 (i_lst[k]!) < 32 := by
      intro k hk
      have hk' : k < i_lst.length := by rw [Hlen]; exact hk
      rw [getElem!_pos i_lst k hk']
      exact Hilt _ (List.getElem_mem hk')
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
    refine ⟨s, f, _, Step.pure _ _ _ (Step_pure.vshuffle c1 c2 packtype.I8 16 i_lst _ cs 0
      ?_ ?_ ?_ rfl ?_ Hwsh ?_)⟩
    · rw [Hcs]; exact jlane_map_proj Jnn.I8 _ HL
    · intro k hk
      rw [List.mem_range] at hk
      rw [Hcsl]; exact Hi32 k hk
    · intro k hk
      rw [List.mem_range] at hk
      rw [Hlen]; exact hk
    · intro x hx
      refine wf_lane_.lane__case_0 _ _ _ ?_ ?_
      · exact Hcsw x hx
      · rfl
    · intro k hk
      rw [List.mem_range] at hk
      have hj : proj_uN_0 (i_lst[k]!) < cs.length := by rw [Hcsl]; exact Hi32 k hk
      refine wf_lane_.lane__case_0 _ _ _ ?_ ?_
      · show wf_uN 8 (cs[proj_uN_0 (i_lst[k]!)]!)
        rw [getElem!_pos cs _ hj]
        exact Hcsw _ (List.getElem_mem hj)
      · rfl
  · simp at Hts
```

## t_progress_be_vsplat — status: proved
- still-sorry earlier lemmas used: invert_typeof_numtype_wf (:232), packnum_not_none (:1122). No project axioms.
- notes: sh destructured to shape.X Lnn (dim.mk_dim Ndim) as in Rocq.

Proof body (tactic block after `:= by`, exactly as compiled):
```lean
  intro C sh HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, _⟩ := Hts
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨Lnn, ⟨Ndim⟩⟩ := sh
    have Hwfsh : wf_shape (shape.X Lnn (dim.mk_dim Ndim)) := by cases HWfinstr; assumption
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_numtype_wf v1 (unpack Lnn) Ht1 HP1
    have Hpk := packnum_not_none Lnn c1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    exact ⟨s, f, [admininstr.VCONST vectype.V128
      (inv_lanes_ (shape.X Lnn (dim.mk_dim Ndim)) (List.replicate Ndim (Option.get! (packnum_ Lnn c1))))],
      Step.pure _ _ _ (Step_pure.vsplat Lnn c1 Ndim _ Hpk rfl Hwfsh)⟩
  · simp at Hts
```

## Final Lean check output (Work.lean, exit 0, no errors/warnings)
```
'TLC.t_progress_be_vswizzle_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, lanes_len]
'TLC.t_progress_be_vshuffle_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, lanes_len]
'TLC.t_progress_be_vsplat_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Axiom-substituted check output (Work_ax.lean, exit 0)
```
'TLC.t_progress_be_vswizzle_ax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ax_invert_typeof_V128,
 ax_jlane_proj_wf,
 ax_jlane_some,
 ax_lanes_Jnn_form,
 lanes_len]
'TLC.t_progress_be_vshuffle_ax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ax_invert_typeof_V128,
 ax_jlane_map_proj,
 ax_jlane_proj_wf,
 ax_lanes_Jnn_form,
 lanes_len]
'TLC.t_progress_be_vsplat_ax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ax_invert_typeof_numtype_wf,
 ax_packnum_not_none]
```

## Safety check (END)
```
safety check [prove-C09] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T133304.026686736Z-prove-C09-1502219.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Safety check (post-log confirmation, after writing this log)
```
safety check [prove-C09] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T133326.804334906Z-prove-C09-1502482.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

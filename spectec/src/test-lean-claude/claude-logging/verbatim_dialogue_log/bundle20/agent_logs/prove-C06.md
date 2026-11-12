# prove-C06 log (bundle20 progress port, proof batch C06)

Agent: prove-C06 (subagent). Wrote only this log file inside the target dir; scratch work in
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C06/` (Work.lean, Work_ax.lean, Work_sorry.lean, out*.txt, body_*.txt). No repo file edited; no git; no agents spawned.

## Safety check at START
```
safety check [prove-C06] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T131941.765679882Z-prove-C06-1494440.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- Scratch `Work.lean`: `import TypeProgress`, each target header copied verbatim (renamed `<name>_proof`) + guard `example : type_of% @<name>_proof = type_of% @<name> := rfl`.
- Checked with `cd spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/Work.lean` (one Lean process at a time). TypeProgress.olean (20:18:19) postdates TypeProgress.lean (20:18:16), so the guards compare against the current statements.
- `#print axioms` variant (Work_ax.lean) plus a small meta command (Work_sorry.lean) that lists which reachable constants use `sorryAx` directly.

## Results (all 5 proved)

### t_progress_be_ref_is_null — proved
- Location: TypeProgress.lean:1783; Rocq type_progress.v:3672-3716
- Still-sorry earlier lemmas used: invert_typeof_reftype (TypeProgress.lean:250)
- Notes: Follows the Rocq bullet: split vcs by the result-type equation (inline replacement for Ltac invert_typeof_vcs), invert_typeof_reftype on the single value; REF_NULL -> Step_pure.ref_is_null_true; REF_FUNC_ADDR / REF_HOST_ADDR -> Step_pure.ref_is_null_false, refuting the negated before-premise by `generalize` on its index list then `cases` (avoids dependent-elimination failure on admininstr_ref v_ref), then `subst` + `simp [admininstr_ref]`.
- Body (goes after `:= by`):
```lean
  intro C rt HWfC HWfinstr
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
    rcases invert_typeof_reftype v1 rt Ht1 with Hnull | ⟨x, Hf | Hh⟩
    · refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Hnull]
      exact Step.pure _ _ _ (Step_pure.ref_is_null_true (ref.REF_NULL rt) rt rfl)
    · refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Hf]
      refine Step.pure _ _ _ (Step_pure.ref_is_null_false (ref.REF_FUNC_ADDR x) ?_)
      intro HContra
      generalize hl : [admininstr_ref (ref.REF_FUNC_ADDR x), admininstr.REF_IS_NULL] = l at HContra
      cases HContra with
      | ref_is_null_true_0 v_ref rt' h =>
        subst h
        simp [admininstr_ref] at hl
    · refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Hh]
      refine Step.pure _ _ _ (Step_pure.ref_is_null_false (ref.REF_HOST_ADDR x) ?_)
      intro HContra
      generalize hl : [admininstr_ref (ref.REF_HOST_ADDR x), admininstr.REF_IS_NULL] = l at HContra
      cases HContra with
      | ref_is_null_true_0 v_ref rt' h =>
        subst h
        simp [admininstr_ref] at hl
  · simp at Hts
```

### t_progress_be_vconst — proved
- Location: TypeProgress.lean:1792; Rocq type_progress.v:3716-3721
- Still-sorry earlier lemmas used: none
- Notes: Rocq `by left`: const_list [VCONST V128 c] = true holds by `rfl`. No sorry dependencies.
- Body (goes after `:= by`):
```lean
  intro C c HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  left
  rfl
```

### t_progress_be_vvunop — proved
- Location: TypeProgress.lean:1800; Rocq type_progress.v:3721-3733
- Still-sorry earlier lemmas used: invert_typeof_V128 (TypeProgress.lean:241)
- Notes: Follows Rocq: split vcs to [v1], wf_val v1 from HWfVals, invert_typeof_V128 gives VCONST V128 c1, rewrite, Step.pure with Step_pure.vvunop c1 op _ rfl.
- Body (goes after `:= by`):
```lean
  intro C v_vvunop HWfC HWfinstr
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
    have HP : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨c1, Heqv1, _⟩ := invert_typeof_V128 v1 Ht1 HP
    refine ⟨s, f, [admininstr.VCONST vectype.V128 (vvunop_ vectype.V128 v_vvunop c1)], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1]
    exact Step.pure _ _ _ (Step_pure.vvunop c1 v_vvunop _ rfl)
  · simp at Hts
```

### t_progress_be_vvbinop — proved
- Location: TypeProgress.lean:1810; Rocq type_progress.v:3733-3746
- Still-sorry earlier lemmas used: invert_typeof_V128 (TypeProgress.lean:241)
- Notes: As vvunop with two values; Step_pure.vvbinop c1 c2 op _ rfl.
- Body (goes after `:= by`):
```lean
  intro C v_vvbinop HWfC HWfinstr
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
    have HP : wf_val v1 := HWfVals v1 (by simp)
    have HP0 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨c1, Heqv1, _⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, _⟩ := invert_typeof_V128 v2 Ht2 HP0
    refine ⟨s, f, [admininstr.VCONST vectype.V128 (vvbinop_ vectype.V128 v_vvbinop c1 c2)], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    exact Step.pure _ _ _ (Step_pure.vvbinop c1 c2 v_vvbinop _ rfl)
  · simp at Hts
```

### t_progress_be_vvternop — proved
- Location: TypeProgress.lean:1820; Rocq type_progress.v:3746-3760
- Still-sorry earlier lemmas used: invert_typeof_V128 (TypeProgress.lean:241)
- Notes: As vvunop with three values; Step_pure.vvternop c1 c2 c3 op _ rfl.
- Body (goes after `:= by`):
```lean
  intro C v_vvternop HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, Ht3, _⟩ := Hts
    have HP : wf_val v1 := HWfVals v1 (by simp)
    have HP0 : wf_val v2 := HWfVals v2 (by simp)
    have HP1 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨c1, Heqv1, _⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, _⟩ := invert_typeof_V128 v2 Ht2 HP0
    obtain ⟨c3, Heqv3, _⟩ := invert_typeof_V128 v3 Ht3 HP1
    refine ⟨s, f, [admininstr.VCONST vectype.V128 (vvternop_ vectype.V128 v_vvternop c1 c2 c3)], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2, Heqv3]
    exact Step.pure _ _ _ (Step_pure.vvternop c1 c2 c3 v_vvternop _ rfl)
  · simp at Hts
```

## Final Lean check output
`lake env lean Work.lean`: exit=0, no output (no errors, no warnings; all 5 rfl guards pass).

`lake env lean Work_ax.lean` (same + `#print axioms`): exit=0
```
'TLC.t_progress_be_ref_is_null_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_vconst_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_be_vvunop_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_vvbinop_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_vvternop_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Direct sorry users (Work_sorry.lean): ref_is_null -> [TLC.invert_typeof_reftype]; vconst -> []; vvunop/vvbinop/vvternop -> [TLC.invert_typeof_V128].
No new axioms, no sorry/admit/native_decide; only Lean core axioms propext, Classical.choice, Quot.sound (+ sorryAx inherited from the two still-sorry canonical-form lemmas).

## Safety check at END
```
safety check [prove-C06] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T132317.513776918Z-prove-C06-1496679.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Safety check after writing this log (final)
```
safety check [prove-C06] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T132348.633407433Z-prove-C06-1497071.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

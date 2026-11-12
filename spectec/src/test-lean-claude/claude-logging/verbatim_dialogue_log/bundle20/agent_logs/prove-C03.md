# prove-C03 (bundle20 progress port, batch C03)

Targets (in order): `t_progress_be_br_if` (TypeProgress.lean:1651), `t_progress_be_br_table` (TypeProgress.lean:1661).
Rocq source: `spectec/test-rocq/theories/type_progress.v` 3344-3393 (br_if), 3393-3449 (br_table).
No repo file edited; scratch work in `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C03/` (Work.lean, Check.lean).

## Safety check (START)

```
safety check [prove-C03] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T131242.494241501Z-prove-C03-1489946.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Results

### t_progress_be_br_if: proved

Uses still-`sorry` earlier lemmas: `typeof_append` (TypeProgress.lean:188), `invert_typeof_I32` (TypeProgress.lean:209).

Notes: follows the Rocq bullet. `right`; peel `Htf` to `t_lst ++ [I32] = ts1`; `typeof_append` splits `vcs = vs ++ [v1]`;
`invert_typeof_I32` makes `v1` an `i32.const n`; then a case split on `n` (zero: `br_if_false`, succ: `br_if_true`).
Rocq's `destruct ts` (pure vs `ctxt_instrs`) is factored into a local helper `Hctxt` that does `cases vs`.
Reduct well-formedness is built directly (`[]` or `[BR l]`, with `wf_uN 32 l` taken from `a_3 : wf_instr (BR_IF l)`).
It deliberately avoids the generated `Step_pure_is_wf`/`Step_is_wf`, which carry a transitive `sorry`.
No new axioms. `#print axioms` gives [propext, sorryAx, Classical.choice, Quot.sound]. A variant with `typeof_append`/`invert_typeof_I32`
taken as hypotheses (Check.lean) gives [propext, Classical.choice, Quot.sound], so those two are the only sources of `sorryAx`.

```lean
  intro C l t_lst a a_1 a_2 a_3
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, -⟩ := Htf
  rw [← Htf1] at Hts
  obtain ⟨v1, Hvcs, Hts', Ht1⟩ := typeof_append _ _ _ Hts
  have Hwfv1 : wf_val v1 :=
    HWfVals v1 (by rw [Hvcs]; exact List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨n, Heqv⟩ := invert_typeof_I32 v1 Ht1 Hwfv1
  generalize List.take t_lst.length vcs = vs at Hvcs Hts'
  subst Hvcs
  have Hcfg : List.map admininstr_val (vs ++ [v1]) ++ List.map admininstr_instr [_root_.instr.BR_IF l]
      = List.map admininstr_val vs ++
          ([admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n)), admininstr.BR_IF l] ++ []) := by
    simp [Heqv, admininstr_instr]
  rw [Hcfg] at HWfConfig ⊢
  -- Rocq's `ctxt_instrs` step under the value prefix `vs` (plain `pure` when `vs = []`, Rocq's `destruct ts`)
  have Hctxt : ∀ (es es' : List admininstr), Step_pure es es' →
      Forall (fun e => wf_admininstr e) es' →
      wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vs ++ (es ++ []))) →
      ∃ (s' : store) (f' : frame) (es'' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vs ++ (es ++ [])))
          (config.mk_config (state.mk_state s' f') es'') := by
    intro es es' Hpure Hes' Hwf
    obtain ⟨Hst, Hais⟩ : wf_state (state.mk_state s f) ∧
        Forall (fun e => wf_admininstr e) (List.map admininstr_val vs ++ (es ++ [])) := by
      cases Hwf with | config_case_0 _ _ h1 h2 => exact ⟨h1, h2⟩
    have Hes : Forall (fun e => wf_admininstr e) es :=
      fun e he => Hais e (List.mem_append_right _ (List.mem_append_left _ he))
    cases vs with
    | nil =>
      refine ⟨s, f, es', ?_⟩
      simp only [List.map_nil, List.nil_append, List.append_nil]
      exact Step.pure _ _ _ Hpure
    | cons v vs' =>
      exact ⟨s, f, List.map admininstr_val (v :: vs') ++ (es' ++ []),
        Step.ctxt_instrs _ (v :: vs') es [] _ es' (Step.pure _ _ _ Hpure) (Or.inl (List.cons_ne_nil _ _))
          (wf_config.config_case_0 _ _ Hst Hes) (wf_config.config_case_0 _ _ Hst Hes')⟩
  have Hl : wf_uN 32 l := by
    cases a_3 with | instr_case_8 _ h => exact h
  cases n with
  | zero =>
    exact Hctxt _ [] (Step_pure.br_if_false _ _ (by simp [proj_num__0])
      (by simp [proj_num__0, proj_uN_0])) (iswf_Forall_nil _) HWfConfig
  | succ n' =>
    exact Hctxt _ [admininstr.BR l] (Step_pure.br_if_true _ _ (by simp [proj_num__0])
      (by simp [proj_num__0, proj_uN_0]))
      (iswf_Forall_cons (wf_admininstr.admininstr_case_7 _ Hl) (iswf_Forall_nil _)) HWfConfig
```

### t_progress_be_br_table: proved

Uses still-`sorry` earlier lemmas: `typeof_append` (TypeProgress.lean:188), `invert_typeof_I32` (TypeProgress.lean:209).

Notes: follows the Rocq bullet. `right`; peel `Htf`, reassociate `t_1_lst ++ (t_lst ++ [I32])` (Rocq `catA`); `typeof_append`; `invert_typeof_I32`.
Case split `n < l_lst.length` (Rocq `n <? |ls|`): `br_table_lt` or `br_table_ge`. The same `Hctxt` helper replaces Rocq's `destruct (ts1 ++ ts)` plus `ctxt_instrs`.
Rocq gets the reduct's wf from `Step_is_wf` (which depends on the Admitted `Step_read_is_wf`). Here it is built directly from `a_5 : wf_instr (BR_TABLE l_lst l')`
(`iswf_Forall_getElem!` for `l_lst[n]!`). No new axioms; the axiom check is the same as for br_if.

```lean
  intro C l_lst l' t_1_lst t_lst t_2_lst a a_1 a_2 a_3 a_4 a_5
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, -⟩ := Htf
  rw [← Htf1, ← List.append_assoc] at Hts
  obtain ⟨v1, Hvcs, Hts', Ht1⟩ := typeof_append _ _ _ Hts
  have Hwfv1 : wf_val v1 :=
    HWfVals v1 (by rw [Hvcs]; exact List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨n, Heqv⟩ := invert_typeof_I32 v1 Ht1 Hwfv1
  generalize List.take (t_1_lst ++ t_lst).length vcs = vs at Hvcs Hts'
  subst Hvcs
  have Hcfg : List.map admininstr_val (vs ++ [v1]) ++ List.map admininstr_instr [_root_.instr.BR_TABLE l_lst l']
      = List.map admininstr_val vs ++
          ([admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN n)), admininstr.BR_TABLE l_lst l'] ++ []) := by
    simp [Heqv, admininstr_instr]
  rw [Hcfg] at HWfConfig ⊢
  -- Rocq's `ctxt_instrs` step under the value prefix `vs` (plain `pure` when `vs = []`, Rocq's `destruct (ts1 ++ ts)`)
  have Hctxt : ∀ (es es' : List admininstr), Step_pure es es' →
      Forall (fun e => wf_admininstr e) es' →
      wf_config (config.mk_config (state.mk_state s f) (List.map admininstr_val vs ++ (es ++ []))) →
      ∃ (s' : store) (f' : frame) (es'' : List admininstr),
        Step (config.mk_config (state.mk_state s f) (List.map admininstr_val vs ++ (es ++ [])))
          (config.mk_config (state.mk_state s' f') es'') := by
    intro es es' Hpure Hes' Hwf
    obtain ⟨Hst, Hais⟩ : wf_state (state.mk_state s f) ∧
        Forall (fun e => wf_admininstr e) (List.map admininstr_val vs ++ (es ++ [])) := by
      cases Hwf with | config_case_0 _ _ h1 h2 => exact ⟨h1, h2⟩
    have Hes : Forall (fun e => wf_admininstr e) es :=
      fun e he => Hais e (List.mem_append_right _ (List.mem_append_left _ he))
    cases vs with
    | nil =>
      refine ⟨s, f, es', ?_⟩
      simp only [List.map_nil, List.nil_append, List.append_nil]
      exact Step.pure _ _ _ Hpure
    | cons v vs' =>
      exact ⟨s, f, List.map admininstr_val (v :: vs') ++ (es' ++ []),
        Step.ctxt_instrs _ (v :: vs') es [] _ es' (Step.pure _ _ _ Hpure) (Or.inl (List.cons_ne_nil _ _))
          (wf_config.config_case_0 _ _ Hst Hes) (wf_config.config_case_0 _ _ Hst Hes')⟩
  obtain ⟨Hls, Hl'⟩ : Forall (fun l => wf_uN 32 l) l_lst ∧ wf_uN 32 l' := by
    cases a_5 with | instr_case_9 _ _ h1 h2 => exact ⟨h1, h2⟩
  by_cases Hv1 : n < l_lst.length
  · exact Hctxt _ _ (Step_pure.br_table_lt _ _ _ (by simpa [proj_num__0, proj_uN_0] using Hv1)
      (by simp [proj_num__0]))
      (iswf_Forall_cons (wf_admininstr.admininstr_case_7 _ (iswf_Forall_getElem! _ Hls (iswf_uN_zero _)))
        (iswf_Forall_nil _)) HWfConfig
  · exact Hctxt _ [admininstr.BR l'] (Step_pure.br_table_ge _ _ _ (by simp [proj_num__0])
      (by simp [proj_num__0, proj_uN_0]; omega))
      (iswf_Forall_cons (wf_admininstr.admininstr_case_7 _ Hl') (iswf_Forall_nil _)) HWfConfig
```

## Final Lean check (`lake env lean /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C03/Work.lean`)

Work.lean = headers copied verbatim (renamed `*_proof`) + bodies above + `example : type_of% @X_proof = type_of% @X := rfl` guards for both + `#print axioms`.
Full output (no errors, no warnings; both rfl guards pass):

```
'TLC.t_progress_be_br_if_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_br_table_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Sorry-source check (`lake env lean /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C03/Check.lean`):

```
'TLC.chk_br_if' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.chk_br_table' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Safety check (END)

```
safety check [prove-C03] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T131855.549516827Z-prove-C03-1493978.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

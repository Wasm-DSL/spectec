# prove-C19 log (bundle20 progress port, batch C19)

Agent label: prove-C19. Scratch dir: /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C19/ (Work.lean, build.py, body_*.txt, hdr_*.txt).
No repo file edited; only this log written. TypeProgress.lean untouched (main thread merges).

## Safety check (START)
```
safety check [prove-C19] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T135059.809290715Z-prove-C19-1512292.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- Headers copied verbatim from TypeProgress.lean by build.py (theorem renamed `<name>_proof`), each followed by `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all 4 guards pass).
- Context check: TypeProgress.lean has only `namespace TLC` before the targets (no open/set_option/simp attributes/instances anywhere), so the scratch context equals the insertion context.
- Ordering rule: every TypeProgress declaration used (invert_typeof_I32:209, invert_typeof_I64:217, invert_typeof_numtype:225, list_slice_size:270, Forall_list_slice:1088, wf_config_mem_bytes:1101, t_progress_be_P:1486) precedes the targets (2193+). Sorry roots computed exactly with a CoreM dependency walk (stops at constants whose body uses sorryAx).
- Template credit: the shape of the stack inversion follows prove-C18's draft for the sibling `t_progress_be_load_val` (read-only look at its scratch dir).

## t_progress_be_load_pack (TypeProgress.lean:2193; Rocq type_progress.v:5034-5061) -- status: proved

Still-sorry earlier lemmas relied on: invert_typeof_I32, list_slice_size, Forall_list_slice, wf_config_mem_bytes (TypeProgress, all earlier); inv_ibytes__is_wf (generated wasm2.0.lean, sorry-bodied)

Notes: Direct port of the Rocq bullet: invert the 1-value stack via typeof, invert_typeof_I32, case on the bounds check; trap branch = Step.read + Step_read.load_pack_trap; in-bounds branch = Step_read.load_pack_val with c := inv_ibytes_ M (slice), closed by ibytes_inv + list_slice_size (bound via omega from the negated check) and inv_ibytes__is_wf + Forall_list_slice + wf_config_mem_bytes. `size (valtype_Inn v_Inn) ≠ none` by `cases v_Inn` (Rocq `by destruct v_Inn`). Axioms: ibytes_inv (HelperLemmas, mirrors Rocq axioms.v).

Proof body (tactic block after `:= by`, exactly as compiled):
```lean
  intro C v_Inn v_M v_sx memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + M/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat ((v_M : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply load_pack_trap; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.load_pack_trap _ _ _ _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: in bounds, read the value back out of the byte slice (`load_pack_val` with
      -- `c := inv_ibytes_ M bs`; `ibytes_inv` + `list_slice_size`; `inv_ibytes__is_wf` +
      -- `Forall_list_slice` + `wf_config_mem_bytes`).
      refine ⟨s, f, [admininstr.CONST (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn
          (extend__ v_M (Option.get! (size (valtype_Inn v_Inn))) v_sx
            (inv_ibytes_ v_M (List.take (rat_to_nat ((v_M : Rat) / (8 : Rat)))
              (List.drop (n1 + proj_uN_0 memarg.OFFSET)
                ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))))))],
        Step.read _ _ _ (Step_read.load_pack_val _ _ _ _ _ _ _ ?_ (by simp [proj_num__0]) ?_ ?_
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
      · -- Rocq: `1: by destruct v_Inn.`
        cases v_Inn <;> simp [valtype_Inn, size]
      · -- Rocq: `apply/eqP; apply: ibytes_inv. apply: list_slice_size. ... by apply: Hs.`
        simp only [proj_num__0, Option.get!_some, proj_uN_0]
        apply ibytes_inv
        exact list_slice_size _ _ _ (by simp only [proj_uN_0] at Hs ⊢; omega)
      · -- Rocq: `eapply inv_ibytes__is_wf; last by apply: eqxx. apply: Forall_list_slice.
        --        by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).`
        exact inv_ibytes__is_wf _ _ _
          (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl
  · simp at Hts
```

## t_progress_be_store_val (TypeProgress.lean:2210; Rocq type_progress.v:5061-5081) -- status: proved

Still-sorry earlier lemmas relied on: invert_typeof_I32, invert_typeof_numtype (TypeProgress, earlier)

Notes: Direct port: invert the 2-value stack, invert_typeof_I32 / invert_typeof_numtype; trap branch Step.store_num_trap; in-bounds branch Step.store_num_val (state.mk_state s f) with b_lst := nbytes_ (rfl); the existential's s'/f' are solved by unification since with_mem (state.mk_state s f) .. reduces to state.mk_state .. f. No project axioms.

Proof body (tactic block after `:= by`, exactly as compiled):
```lean
  intro C nt memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs3⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto.
    --        rewrite Heqv1. eapply invert_typeof_numtype in Ht2 as [n2 Heqv2]; eauto. rewrite Heqv2.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    obtain ⟨n2, Heqv2⟩ := invert_typeof_numtype v2 nt Ht2
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + size/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET
        + rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. by eapply store_num_trap; eauto.`
      exact ⟨s, f, [admininstr.TRAP],
        Step.store_num_trap _ _ _ _ _ (by simp [proj_num__0]) Hfunsize
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩)⟩
    · -- Rocq: `do 3 eexists. eapply (store_num_val (mk_state s f)); eauto.`
      exact ⟨_, _, _, Step.store_num_val (state.mk_state s f) _ _ _ _ _
        (by simp [proj_num__0]) Hfunsize rfl⟩
  · simp at Hts
```

## t_progress_be_store_pack (TypeProgress.lean:2222; Rocq type_progress.v:5081-5132) -- status: proved

Still-sorry earlier lemmas relied on: invert_typeof_I32, invert_typeof_I64 (TypeProgress, earlier)

Notes: Direct port incl. Rocq's structure (case on bounds first, then destruct Inn in each branch, invert_typeof_I32/I64 on the stored value). Rocq's `rewrite H in Heqv2` (I32 = numtype_Inn Inn_I32) is unnecessary in Lean: Inn is passed explicitly to Step.store_pack_trap / Step.store_pack_val and numtype_Inn Inn.I32 ≡ numtype.I32 by defeq. No project axioms.

Proof body (tactic block after `:= by`, exactly as compiled):
```lean
  intro C v_Inn v_M memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vcs3⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    have Hwf2 : wf_val v2 := HWfVals v2 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + M/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat ((v_M : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. destruct Inn.` then per `Inn`:
      -- `eapply invert_typeof_I32/I64 in Ht2 as [n2 Heqv2]; eauto. rewrite H in Heqv2.
      --  rewrite Heqv2. eapply store_pack_trap; eauto. econstructor; eauto.`
      refine ⟨s, f, [admininstr.TRAP], ?_⟩
      cases v_Inn
      · obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 Hwf2
        rw [Heqv2]
        exact Step.store_pack_trap _ _ Inn.I32 _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩)
      · obtain ⟨n2, Heqv2⟩ := invert_typeof_I64 v2 Ht2 Hwf2
        rw [Heqv2]
        exact Step.store_pack_trap _ _ Inn.I64 _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩)
    -- Rocq: `destruct Inn.` then per `Inn`: invert `Ht2`, `do 3 eexists.
    -- eapply (store_pack_val (mk_state s f)); eauto.`
    cases v_Inn
    · obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 Hwf2
      rw [Heqv2]
      exact ⟨_, _, _, Step.store_pack_val (state.mk_state s f) _ Inn.I32 _ _ _ _
        (by simp [proj_num__0]) (by simp [valtype_Inn, size]) (by simp [proj_num__0]) rfl⟩
    · obtain ⟨n2, Heqv2⟩ := invert_typeof_I64 v2 Ht2 Hwf2
      rw [Heqv2]
      exact ⟨_, _, _, Step.store_pack_val (state.mk_state s f) _ Inn.I64 _ _ _ _
        (by simp [proj_num__0]) (by simp [valtype_Inn, size]) (by simp [proj_num__0]) rfl⟩
  · simp at Hts
```

## t_progress_be_vload_val (TypeProgress.lean:2233; Rocq type_progress.v:5132-5161) -- status: proved

Still-sorry earlier lemmas relied on: invert_typeof_I32, list_slice_size, Forall_list_slice, wf_config_mem_bytes (TypeProgress, all earlier); inv_vbytes__is_wf (generated wasm2.0.lean, sorry-bodied)

Notes: Direct port as load_val: Step_read.vload_oob / Step_read.vload_val with c := inv_vbytes_ V128 (slice); vbytes_inv's Rat-valued length premise reduces (after list_slice_size) to the closed fact ((rat_to_nat (128/8) : Nat) : Rat) = 128/8, closed by `decide +kernel` (kernel-checked, no extra axioms; NOT native_decide). Axioms: vbytes_inv (HelperLemmas, mirrors Rocq axioms.v).

Proof body (tactic block after `:= by`, exactly as compiled):
```lean
  intro C memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + size V128/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET
        + rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply vload_oob; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.vload_oob _ _ _ (by simp [proj_num__0]) Hfunsize
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: in bounds, read the value back out of the byte slice (`Step_read__vload_val` with
      -- `c := inv_vbytes_ V128 bs`; `vbytes_inv` + `list_slice_size`; `inv_vbytes__is_wf` +
      -- `Forall_list_slice` + `wf_config_mem_bytes`).
      refine ⟨s, f, [admininstr.VCONST vectype.V128 (inv_vbytes_ vectype.V128
          (List.take (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))
            (List.drop (n1 + proj_uN_0 memarg.OFFSET)
              ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))))],
        Step.read _ _ _ (Step_read.vload_val _ _ _ _ (by simp [proj_num__0]) Hfunsize ?_ ?_
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
      · -- Rocq: `apply/eqP; apply: vbytes_inv. apply: list_slice_size. ... by apply: Hs.`
        simp only [proj_num__0, Option.get!_some, proj_uN_0]
        apply vbytes_inv
        rw [list_slice_size _ _ _ (by simp only [proj_uN_0] at Hs ⊢; omega)]
        decide +kernel
      · -- Rocq: `eapply (inv_vbytes__is_wf V128); [ | by apply: eqxx | by [] ].
        --        apply: Forall_list_slice. by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).`
        exact inv_vbytes__is_wf vectype.V128 _ _
          (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl Hfunsize
  · simp at Hts
```

## Final Lean check
`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/prove-C19/Work.lean` -> exit=0, empty output (no errors, no warnings; 4 rfl guards pass).

`#print axioms` (WorkAx.lean, same proofs):
```
'TLC.t_progress_be_load_pack_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, ibytes_inv]
'TLC.t_progress_be_store_val_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_store_pack_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_vload_val_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, vbytes_inv]
```

Exact sorry roots (WorkDeps.lean):
```
TLC.t_progress_be_load_pack_proof sorry roots: [TLC.invert_typeof_I32, TLC.list_slice_size, inv_ibytes__is_wf, TLC.Forall_list_slice, TLC.wf_config_mem_bytes]
TLC.t_progress_be_store_val_proof sorry roots: [TLC.invert_typeof_I32, TLC.invert_typeof_numtype]
TLC.t_progress_be_store_pack_proof sorry roots: [TLC.invert_typeof_I32, TLC.invert_typeof_I64]
TLC.t_progress_be_vload_val_proof sorry roots: [TLC.invert_typeof_I32, TLC.list_slice_size, inv_vbytes__is_wf, TLC.Forall_list_slice, TLC.wf_config_mem_bytes]
```

## Safety check (END)
```
safety check [prove-C19] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T135659.882810669Z-prove-C19-1515864.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

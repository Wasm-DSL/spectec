# prove-C21 log (bundle20 progress port, proof batch C21)

Agent label: prove-C21. Brief: scratchpad/briefs/progress_prove_brief.md; task: scratchpad/briefs/task_prove-C21.md.
Scratch files (not in repo): /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C21/{Work.lean,Work2.lean,Final.lean,Deps.lean}. No repo file was edited except this log.

## Safety check (START)

```
safety check [prove-C21] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T135402.757383349Z-prove-C21-1514120.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Results

| target | status | still-sorry earlier lemmas used |
|---|---|---|
| `t_progress_be_vload_zero` | proved | `invert_typeof_I32`, `list_slice_size`, `Forall_list_slice`, `wf_config_mem_bytes` |
| `t_progress_be_vload_lane` | proved | `invert_typeof_I32`, `invert_typeof_V128`, `list_slice_size`, `Forall_list_slice`, `wf_config_mem_bytes` |
| `t_progress_be_vstore` | proved | `invert_typeof_I32`, `invert_typeof_V128` |
| `t_progress_be_vstore_lane` | proved | `invert_typeof_I32`, `invert_typeof_V128`, `vstore_lane_progress` |
| `t_progress_be_empty` | proved | none |

Each proof checked as `theorem <name>_proof <header copied verbatim> := by <body>` + guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all 5 guards pass). Ordering rule: every TypeProgress lemma used is earlier than its target (invert_typeof_I32:209, invert_typeof_V128:241, list_slice_size:270, Forall_list_slice:1088, wf_config_mem_bytes:1101, vstore_lane_progress:1140, t_progress_be_P/P0:1486/1505; targets start at 2268). The still-sorry list was computed exactly by a meta traversal of each proof term (Deps.lean). `inv_ibytes__is_wf` (from the imported generated `wasm2.0.lean`, a `:= sorry` well-formedness stub) is also reached by vload_zero and vload_lane.

### `t_progress_be_vload_zero` — proved

Notes: Follows the Rocq bullet (type_progress.v:5277) step for step: invert Htf, invert vcs to [v1] with typeof I32, invert_typeof_I32, split on the out-of-bounds test. OOB: Step.read + Step_read.vload_zero_oob. In bounds: Step.read + Step_read.vload_zero_val with j := inv_ibytes_ v_n (slice); the bytes premise is ibytes_inv (HelperLemmas axiom) + list_slice_size; wf_uN v_n j is inv_ibytes__is_wf + Forall_list_slice + wf_config_mem_bytes. Also uses the generated wasm2.0.lean theorem inv_ibytes__is_wf, which is a `:= sorry` stub in the imported generated file (Rocq uses the same generated lemma). Axioms: ibytes_inv.

```lean
  intro C v_n v_memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨rfl, rfl⟩ := Htf
  obtain ⟨v1, rfl, Ht1⟩ := List.map_eq_singleton_iff.mp Hts
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
  have Hwf0 : wf_uN 32 (uN.mk_uN 0) := wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
  by_cases Hs : n1 + proj_uN_0 v_memarg.OFFSET + rat_to_nat ((v_n : Rat) / 8)
      > ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length
  · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
      (Step_read.vload_zero_oob _ _ _ _ (by simp [proj_num__0]) Hs Hwf0)⟩
  · have Hbnd : n1 + proj_uN_0 v_memarg.OFFSET + rat_to_nat ((v_n : Rat) / 8)
        ≤ ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length := Nat.le_of_not_lt Hs
    exact ⟨s, f, _, Step.read _ _ _
      (Step_read.vload_zero_val _ _ _ _ _ _ (by simp [proj_num__0])
        (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl
        (inv_ibytes__is_wf _ _ _
          (Forall_list_slice _ _ _ _ (wf_config_mem_bytes s f _ (uN.mk_uN 0) HWfConfig)) rfl)
        Hwf0)⟩
```

### `t_progress_be_vload_lane` — proved

Notes: Follows the Rocq bullet (type_progress.v:5304): canonical forms for I32 and V128, OOB split (Step_read.vload_lane_oob), then wf_sz from wf_instr gives v_n in {8,16,32,64}, and each case applies Step_read.vload_lane_val with (Jnn, M) = (I8,16), (I16,8), (I32,4), (I64,2), as Rocq does. Rocq's `mk_uN_eta` rewrite is a local `Heta : uN.mk_uN (proj_uN_0 x) = x` (cases x; rfl). omega cannot see the `n`-typed disjunction from wf_sz (abbrev n := Nat literals), so the case split is done with explicit Or injections. Also uses the generated stub inv_ibytes__is_wf (wasm2.0.lean, `:= sorry`). Axioms: ibytes_inv.

```lean
  intro C v_n v_memarg v_laneidx mt Hlen Hlookup HLim Hidx HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨rfl, rfl⟩ := Htf
  obtain ⟨v1, l1, rfl, Ht1, Hts'⟩ := List.map_eq_cons_iff.mp Hts
  obtain ⟨v2, rfl, Ht2⟩ := List.map_eq_singleton_iff.mp Hts'
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  obtain ⟨c1, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 (HWfVals v2 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
  have Hwf0 : wf_uN 32 (uN.mk_uN 0) := wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
  by_cases Hs : n1 + proj_uN_0 v_memarg.OFFSET + rat_to_nat ((v_n : Rat) / 8)
      > ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length
  · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
      (Step_read.vload_lane_oob _ _ _ _ _ _ (by simp [proj_num__0]) Hs Hwf0)⟩
  · have Hbnd : n1 + proj_uN_0 v_memarg.OFFSET + rat_to_nat ((v_n : Rat) / 8)
        ≤ ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length := Nat.le_of_not_lt Hs
    have Hwfk : wf_uN v_n (inv_ibytes_ v_n (List.take (rat_to_nat ((v_n : Rat) / 8))
        (List.drop (n1 + proj_uN_0 v_memarg.OFFSET)
          ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES)))) :=
      inv_ibytes__is_wf _ _ _
        (Forall_list_slice _ _ _ _ (wf_config_mem_bytes s f _ (uN.mk_uN 0) HWfConfig)) rfl
    have Heta : ∀ x : uN, uN.mk_uN (proj_uN_0 x) = x := fun x => by cases x; rfl
    have Hsz : wf_sz (sz.mk_sz v_n) := by cases HWfinstr; assumption
    have Hcases : v_n = 8 ∨ v_n = 16 ∨ v_n = 32 ∨ v_n = 64 := by
      cases Hsz with
      | sz_case_0 _ h =>
        rcases h with ((h | h) | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    rcases Hcases with E | E | E | E <;> subst E
    · exact ⟨s, f, _, Step.read _ _ _
        (Step_read.vload_lane_val _ _ _ _ _ _ _ _ Jnn.I8 16 (by simp [proj_num__0])
          (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl (by norm_num) rfl Hwf0
          (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
          (wf_lane_.lane__case_0 _ _ _ (by rw [Heta]; exact Hwfk) rfl))⟩
    · exact ⟨s, f, _, Step.read _ _ _
        (Step_read.vload_lane_val _ _ _ _ _ _ _ _ Jnn.I16 8 (by simp [proj_num__0])
          (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl (by norm_num) rfl Hwf0
          (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
          (wf_lane_.lane__case_0 _ _ _ (by rw [Heta]; exact Hwfk) rfl))⟩
    · exact ⟨s, f, _, Step.read _ _ _
        (Step_read.vload_lane_val _ _ _ _ _ _ _ _ Jnn.I32 4 (by simp [proj_num__0])
          (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl (by norm_num) rfl Hwf0
          (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
          (wf_lane_.lane__case_0 _ _ _ (by rw [Heta]; exact Hwfk) rfl))⟩
    · exact ⟨s, f, _, Step.read _ _ _
        (Step_read.vload_lane_val _ _ _ _ _ _ _ _ Jnn.I64 2 (by simp [proj_num__0])
          (ibytes_inv _ _ (list_slice_size _ _ _ Hbnd)) rfl (by norm_num) rfl Hwf0
          (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
          (wf_lane_.lane__case_0 _ _ _ (by rw [Heta]; exact Hwfk) rfl))⟩
```

### `t_progress_be_vstore` — proved

Notes: Follows the Rocq bullet (type_progress.v:5348): canonical forms for I32/V128, then Step.vstore_val directly (this rule has no bounds premise), with the `size V128 ≠ none` premise taken from the case's own hypothesis. No axioms beyond the core ones.

```lean
  intro C v_memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨rfl, rfl⟩ := Htf
  obtain ⟨v1, l1, rfl, Ht1, Hts'⟩ := List.map_eq_cons_iff.mp Hts
  obtain ⟨v2, rfl, Ht2⟩ := List.map_eq_singleton_iff.mp Hts'
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 (HWfVals v2 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
  exact ⟨_, _, _, Step.vstore_val _ _ _ _ _ (by simp [proj_num__0]) Hfunsize rfl⟩
```

### `t_progress_be_vstore_lane` — proved

Notes: Follows the Rocq bullet (type_progress.v:5363): canonical forms, OOB split (Step.vstore_lane_oob), else v_n in {8,16,32,64} from wf_sz, then vstore_lane_progress with (J, M) = (I8,16), (I16,8), (I32,4), (I64,2). The lane-index bound proj_uN_0 laneidx < M comes from the Rat premise via norm_num (then exact_mod_cast, or omega for I64, where norm_num yields `≤ 1`). M = 128 / jsize J is a `show ... by norm_num` checked by defeq. wf_uN 128 c1 comes by defeq from invert_typeof_V128's `wf_uN (Option.get! (size ..)) c1`. No axioms beyond the core ones.

```lean
  intro C v_n v_memarg v_laneidx mt Hlen Hlookup HLim Hidx HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨rfl, rfl⟩ := Htf
  obtain ⟨v1, l1, rfl, Ht1, Hts'⟩ := List.map_eq_cons_iff.mp Hts
  obtain ⟨v2, rfl, Ht2⟩ := List.map_eq_singleton_iff.mp Hts'
  obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 (HWfVals v1 (by simp))
  obtain ⟨c1, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 (HWfVals v2 (by simp))
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2]
  have Hwf0 : wf_uN 32 (uN.mk_uN 0) := wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
  by_cases Hs : n1 + proj_uN_0 v_memarg.OFFSET + v_n
      > ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES).length
  · exact ⟨s, f, [admininstr.TRAP],
      Step.vstore_lane_oob _ _ _ _ _ _ (by simp [proj_num__0]) Hs Hwf0⟩
  · have Hsz : wf_sz (sz.mk_sz v_n) := by cases HWfinstr; assumption
    have Hcases : v_n = 8 ∨ v_n = 16 ∨ v_n = 32 ∨ v_n = 64 := by
      cases Hsz with
      | sz_case_0 _ h =>
        rcases h with ((h | h) | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    have Hwf128 : wf_uN 128 c1 := Hwf2
    rcases Hcases with E | E | E | E <;> subst E
    · exact vstore_lane_progress s f n1 v_memarg v_laneidx c1 Jnn.I8 16 Hwf128
        (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
        (by have h := Hidx; norm_num at h; exact_mod_cast h) (show ((16 : ℕ) : Rat) = 128 / ((8 : ℕ) : Rat) by norm_num)
    · exact vstore_lane_progress s f n1 v_memarg v_laneidx c1 Jnn.I16 8 Hwf128
        (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
        (by have h := Hidx; norm_num at h; exact_mod_cast h) (show ((8 : ℕ) : Rat) = 128 / ((16 : ℕ) : Rat) by norm_num)
    · exact vstore_lane_progress s f n1 v_memarg v_laneidx c1 Jnn.I32 4 Hwf128
        (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
        (by have h := Hidx; norm_num at h; exact_mod_cast h) (show ((4 : ℕ) : Rat) = 128 / ((32 : ℕ) : Rat) by norm_num)
    · exact vstore_lane_progress s f n1 v_memarg v_laneidx c1 Jnn.I64 2 Hwf128
        (wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) rfl)
        (by have h := Hidx; norm_num at h; omega) (show ((2 : ℕ) : Rat) = 128 / ((64 : ℕ) : Rat) by norm_num)
```

### `t_progress_be_empty` — proved

Notes: Rocq bullet (type_progress.v:5394) is `by left`: here `left; rfl` (const_list [] reduces to true). No sorry dependencies; axioms are only propext, Classical.choice and Quot.sound.

```lean
  intro C a
  unfold t_progress_be_P0
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  left
  rfl
```

## Final Lean check

Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C21/Final.lean` (exit 0, no errors or warnings):

```
'TLC.t_progress_be_vload_zero_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, ibytes_inv]
'TLC.t_progress_be_vload_lane_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, ibytes_inv]
'TLC.t_progress_be_vstore_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_vstore_lane_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_empty_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Safety check (END)

```
safety check [prove-C21] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T140204.423471909Z-prove-C21-1518804.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

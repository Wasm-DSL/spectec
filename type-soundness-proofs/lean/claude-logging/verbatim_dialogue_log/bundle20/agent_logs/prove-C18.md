# prove-C18 (bundle20 progress port, proof batch C18)

Targets (in order): `t_progress_be_memory_init` (TypeProgress.lean:2161), `t_progress_be_data_drop`
(TypeProgress.lean:2172), `t_progress_be_load_val` (TypeProgress.lean:2181). All three are PROVED.
No repo file was edited. The only writes were this log and files in
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C18/`
(`Work.lean`, `Hsz.lean`, `Ax.lean`, `Head.lean`, `hdr_*.txt`, `body_*.txt`).

## Safety check at START

```
safety check [prove-C18] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134830.481094447Z-prove-C18-1510543.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method

- `Work.lean` does `import TypeProgress` and `namespace TLC`. Each target's header was copied by `sed`
  verbatim from TypeProgress.lean, with only the name changed to `<name>_proof`. Each is followed by
  `example : type_of% @<name>_proof = type_of% @<name> := rfl`. All three guards pass.
- Checked with `timeout 900 lake env lean <file>`, one Lean process at a time. I never ran `lake build`.
- Ordering rule. The TypeProgress declarations used are `t_progress_be_P` (1486), `invert_typeof_I32` (209),
  `list_slice_size` (270), `Forall_list_slice` (1088) and `wf_config_mem_bytes` (1101). All come before 2161.
  TypeProgress.lean has no `@[simp]`/`attribute` lines and no `open`/`set_option`, so `simp` and name
  resolution in Work.lean match the merge point.
- Merge simulation (`Head.lean`): a copy of TypeProgress.lean up to and including `t_progress_be_load_val`,
  with the three bodies spliced in and `end TLC` added. It compiles with exit 0; the only warnings are
  "declaration uses `sorry`" from other lemmas.
- No `sorry`, `admit`, `native_decide` or new axioms. The one project axiom used is `nbytes_inv`
  (HelperLemmas.lean:794, which mirrors Rocq `axioms.v` `nbytes_inv`), and only in `load_val`. One Lean-only
  tactic, `decide +kernel`, is used for a closed numeric fact. It is kernel reduction and adds no axiom
  (no `Lean.ofReduceBool` in `#print axioms`).

## Results

### `t_progress_be_memory_init` : proved

Still-`sorry` earlier lemmas relied on: `invert_typeof_I32` (TypeProgress.lean:209). `#print axioms`:
`[propext, sorryAx, Classical.choice, Quot.sound]`. `Ax.lean` shows the `sorryAx` comes only from
`invert_typeof_I32`, since `fun_data`, `fun_mem` and `Step_read.memory_init_*` use only `propext`.

Notes: a close port of the Rocq bullet at `type_progress.v:4917-4994`, following C15's `table_init` template.
- `invert_typeof_vcs` is done inline: `rcases vcs` into `[v1, v2, v3]`, with the other lengths closed by
  `simp at Hts`.
- `inv_Forall` becomes `HWfVals vi (by simp)`, then three `invert_typeof_I32` calls as in Rocq.
- The Rocq boolean split `case Hs: ((n2+n3 >? |data.BYTES|) || (n1+n3 >? |mem.BYTES|))` becomes
  `by_cases Hs` on the same two Nat comparisons. Operand order follows the Lean rule
  `[CONST j; CONST i; CONST n; MEMORY_INIT x]` with j=n1, i=n2, n=n3.
- `destruct n3 using N.peano_ind` becomes `rcases n3 with _ | n3`.
- The steps are `Step.read` with `Step_read.memory_init_trap` / `_zero` / `_succ`. Numeric side conditions use
  `simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega`. The trap rule's `wf_uN 32 (uN.mk_uN 0)` is
  `wf_uN.uN_case_0 32 0 ⟨_, _⟩` (Rocq's `econstructor; eauto`).
- In the succ case the result list is left as `_`, so it is taken from the rule. That makes Rocq's
  `assert (n3 = N.succ n3 - 1)` rewrite unnecessary.

```lean
  intro C x mt Hlen Hlookup HRange HData HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  -- Rocq: `invert_typeof_vcs Hts HWfConfig HWfVals.` (vcs = [v1; v2; v3])
  rcases vcs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, vcs4⟩⟩⟩⟩
  · simp at Hts
  · simp at Hts
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, Ht2, Ht3, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    have Hwf2 : wf_val v2 := HWfVals v2 (by simp)
    have Hwf3 : wf_val v3 := HWfVals v3 (by simp)
    -- Rocq: `eapply invert_typeof_I32 in Ht1/Ht2/Ht3 as [n_i Heqv_i]; eauto. rewrite Heqv_i.`
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 Hwf2
    obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 Hwf3
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2, Heqv3,
      admininstr_instr]
    -- Rocq: `case Hs: ((n2 + n3 >? |data.BYTES|) || (n1 + n3 >? |mem.BYTES|)).`
    by_cases Hs : (n2 + n3 > (fun_data (state.mk_state s f) x).BYTES.length) ∨
        (n1 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length)
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply memory_init_trap; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.memory_init_trap _ _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: `destruct n3 using N.peano_ind.`
      rcases n3 with _ | n3
      · -- Rocq: `exists s, f, []. eapply read. eapply memory_init_zero; eauto. ...`
        exact ⟨s, f, [], Step.read _ _ _
          (Step_read.memory_init_zero _ _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega) rfl)⟩
      · -- Rocq: `exists s, f, [...]. eapply read. eapply memory_init_succ; eauto. ...`
        exact ⟨s, f, _, Step.read _ _ _
          (Step_read.memory_init_succ _ _ _ _ _
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega)
            (by simp [proj_num__0]) (by simp [proj_num__0]) (Nat.succ_ne_zero _)
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega))⟩
  · simp at Hts
```

### `t_progress_be_data_drop` : proved

Still-`sorry` earlier lemmas relied on: none. `#print axioms`: `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`.

Notes: a direct port of the Rocq bullet at `type_progress.v:4995-5004`, the same pattern as C15's `elem_drop`.
- `vcs = []` is done inline; the non-empty case is closed by `simp at Hts`.
- Rocq's `case Estate: (with_data (mk_state s f) x []) => [s' f']` becomes
  `cases Estate : ... with | mk_state s' f'`.
- `rewrite -Estate` becomes `rw [← Estate]`, and `by eapply Step__data_drop` becomes
  `exact Step.data_drop _ x`.

```lean
  intro C x HRange Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs1⟩
  · -- Rocq: `case Estate: (with_data (mk_state s f) x []) => [s' f']. exists s', f', [].
    --        rewrite -Estate. by eapply Step__data_drop.`
    cases Estate : with_data (state.mk_state s f) x [] with
    | mk_state s' f' =>
      refine ⟨s', f', [], ?_⟩
      rw [← Estate]
      exact Step.data_drop _ x
  · simp at Hts
```

### `t_progress_be_load_val` : proved

Still-`sorry` earlier lemmas relied on:
- `invert_typeof_I32` (TypeProgress.lean:209)
- `list_slice_size` (270)
- `Forall_list_slice` (1088)
- `wf_config_mem_bytes` (1101)
- generated `inv_nbytes__is_wf` (wasm2.0.lean ~4296, a generated well-formedness theorem whose body is
  `sorry`; Rocq uses the same lemma)

Project axiom used: `nbytes_inv` (HelperLemmas.lean:794). `#print axioms`:
`[propext, sorryAx, Classical.choice, Quot.sound, nbytes_inv]`.

Notes: a close port of the Rocq bullet at `type_progress.v:5005-5033`.
- vcs = [v1] is inverted inline, then `invert_typeof_I32` gives `n1`.
- The Rocq split `case Hs: ((n1 + OFFSET + size/8) >? |mem.BYTES|)` becomes `by_cases Hs` on
  `n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (size/8) > |BYTES|`. This is written exactly as the
  `load_num_trap`/`load_num_val` premises are.
- Trap branch: `Step.read` + `Step_read.load_num_trap`.
- In-bounds branch: `Step.read` + `Step_read.load_num_val`, with the explicit witness
  `c := inv_nbytes_ nt (List.take (rat_to_nat (size/8)) (List.drop (n1+OFFSET) BYTES))`. This replaces
  Rocq's `do 3 eexists` plus the `Unshelve`.
- Byte equation, as in Rocq: `apply nbytes_inv`, then `rw [list_slice_size ...]`, using `¬Hs` via `omega`.
- One Lean-specific step: Lean's `nbytes_inv` premise is the exact rational
  `(bs.length : Rat) = size/8`. After `list_slice_size` this needs `(rat_to_nat (size/8) : Rat) = size/8`,
  which holds because every numtype size (32/64) is a multiple of 8. It is proved by
  `cases nt <;> decide +kernel`.
  - Plain `decide` gets stuck on `Rat` arithmetic.
  - `norm_num [size, valtype_numtype, rat_to_nat]` leaves `↑(Int.toNat 4) = 4`.
  - Note: `((Option.get! (size ..)) : Rat)` elaborates as `(do let a ← size ..; pure ↑a).get!`. The same
    text is used, so the `Hsz` statement matches the rule premise syntactically.
- Well-formedness, as in Rocq: `inv_nbytes__is_wf nt _ _ (Forall_list_slice _ _ _ _
  (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl`.

```lean
  intro C nt memarg mt Hlen Hlookup Hfunsize HLim HWfC HWfMemType HWfinstr
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
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + size/8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET
        + rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply load_num_trap; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.load_num_trap _ _ _ _ (by simp [proj_num__0]) Hfunsize
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: in bounds, read the value back out of the byte slice (`load_num_val` with
      -- `c := inv_nbytes_ nt bs`; `nbytes_inv` + `list_slice_size`; `inv_nbytes__is_wf` +
      -- `Forall_list_slice` + `wf_config_mem_bytes`).
      have Hsz : ((rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)) : Nat) : Rat)
          = ((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat) := by
        cases nt <;> decide +kernel
      refine ⟨s, f, [admininstr.CONST nt (inv_nbytes_ nt
          (List.take (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))
            (List.drop (n1 + proj_uN_0 memarg.OFFSET)
              ((fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))))],
        Step.read _ _ _ (Step_read.load_num_val _ _ _ _ _ (by simp [proj_num__0]) Hfunsize ?_ ?_
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
      · -- Rocq: `apply/eqP; apply: nbytes_inv. apply: list_slice_size. ... by apply: Hs.`
        simp only [proj_num__0, Option.get!_some, proj_uN_0]
        apply nbytes_inv
        rw [list_slice_size _ _ _ (by simp only [proj_uN_0] at Hs ⊢; omega)]
        exact Hsz
      · -- Rocq: `eapply inv_nbytes__is_wf; last by apply: eqxx. apply: Forall_list_slice.
        --        by apply: (wf_config_mem_bytes _ _ _ _ HWfConfig).`
        exact inv_nbytes__is_wf nt _ _
          (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl
  · simp at Hts
```

## Final Lean check output

Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean
/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C18/Work.lean`.
Exit 0, with no errors and no warnings. All three `rfl` guards are accepted.

```
'TLC.t_progress_be_memory_init_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_data_drop_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_be_load_val_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, nbytes_inv]
EXIT=0
```

Merge simulation `Head.lean` (TypeProgress.lean prefix through line 2188, with the bodies spliced in).
Output with the "declaration uses `sorry`" warnings filtered:

```
'TLC.t_progress_be_memory_init' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_data_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_be_load_val' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, nbytes_inv]
EXIT=0
```

Axiom-source check `Ax.lean`:

```
'TLC.invert_typeof_I32' depends on axioms: [propext, sorryAx]
'TLC.list_slice_size' depends on axioms: [sorryAx]
'TLC.Forall_list_slice' depends on axioms: [sorryAx]
'TLC.wf_config_mem_bytes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'inv_nbytes__is_wf' depends on axioms: [propext, sorryAx]
'fun_data' depends on axioms: [propext]
'fun_mem' depends on axioms: [propext]
'with_data' depends on axioms: [propext]
'Step_read.memory_init_trap' depends on axioms: [propext]
'Step_read.memory_init_zero' depends on axioms: [propext]
'Step_read.memory_init_succ' depends on axioms: [propext]
'Step_read.load_num_trap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Step_read.load_num_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'Step.data_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

## Safety check at END

```
safety check [prove-C18] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T135315.111462127Z-prove-C18-1513771.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

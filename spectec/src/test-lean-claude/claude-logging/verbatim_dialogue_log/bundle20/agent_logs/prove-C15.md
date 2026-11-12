# prove-C15 (bundle20 progress port, proof batch C15)

Targets (in order): `t_progress_be_table_init` (TypeProgress.lean:2102), `t_progress_be_elem_drop`
(TypeProgress.lean:2114). Both PROVED. No repo file was edited. The only writes were this log and files in
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C15/`.

## Safety check at START

```
safety check [prove-C15] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134235.811949698Z-prove-C15-1507182.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method

- Scratch file `.../agents/prove-C15/Work.lean` does `import TypeProgress`. Each target's header is copied
  verbatim with the name changed to `<name>_proof`, followed by the guard
  `example : type_of% @<name>_proof = type_of% @<name> := rfl`. Both guards pass.
- Checked with `timeout 900 lake env lean <Work.lean>`, one Lean process at a time.
- Ordering rule: the only TypeProgress declarations used are `invert_typeof_I32` (line 209, still `sorry`)
  and `t_progress_be_P` (line 1486). Both come before 2102. `mkFunctype` comes from the imported
  `Subtyping.lean`. Everything else is from wasm2.0 (`Step.read`, `Step_read.table_init_{trap,zero,succ}`,
  `Step.elem_drop`, `with_elem`, `fun_elem`, `fun_table`, `proj_num__0`, `proj_uN_0`, `admininstr_instr`).
- No `sorry`, `admit`, `native_decide` or new axioms. No project axioms are used.

## Results

### `t_progress_be_table_init` : proved

Still-`sorry` earlier lemmas relied on: `invert_typeof_I32` (TypeProgress.lean:209).
`#print axioms` gives `[propext, sorryAx, Classical.choice, Quot.sound]`. A separate `#print axioms` run
shows the `sorryAx` comes only from `invert_typeof_I32`: `fun_elem`/`fun_table`/`Step_read.table_init_*`
have none.

Notes: a close port of the Rocq bullet at `type_progress.v:4605-4682`.
- Rocq's `invert_typeof_vcs` is done inline: `rcases vcs` into `[v1, v2, v3]`, and the other lengths are
  closed by `simp at Hts`.
- `inv_Forall HWfVals` becomes `HWfVals vi (by simp)`.
- The three `invert_typeof_I32` calls work as in Rocq.
- Rocq's `case Hs: (... || ...)` boolean split becomes `by_cases Hs` on the same two Nat comparisons.
  This uses the Lean rule's operand order `[CONST j; CONST i; CONST n; TABLE_INIT x y]` with j=n1, i=n2,
  n=n3.
- Rocq's `destruct n3 using N.peano_ind` becomes `rcases n3 with _ | n3`.
- Each branch gives the step `Step.read` + `Step_read.table_init_trap` / `table_init_zero` /
  `table_init_succ`, with numeric side conditions done by `simp only [proj_num__0, Option.get!_some,
  proj_uN_0]; omega`.
- In the succ case the result list is left as `_`, so it is taken from the rule. The Rocq `assert (n3 =
  (N.succ n3) - 1)` rewrite is therefore unnecessary.
- Pitfall found: the premise `v_n ≠ 0` has type `n` (`abbrev n := Nat`). `omega` does not recognise it,
  even though the goal displays as `n3 + 1 ≠ 0`, so the proof uses `Nat.succ_ne_zero _`.

```lean
  intro C x1 x2 lim1 rt Hlenx1 Hlookupx1 Hlenx2 Hlookupx2 HWfC HWfinstr HWfTabType
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
    -- Rocq: `case Hs: ((n2 + n3 >? |elem.REFS|) || (n1 + n3 >? |table.REFS|)).`
    by_cases Hs : (n2 + n3 > (fun_elem (state.mk_state s f) x2).REFS.length) ∨
        (n1 + n3 > (fun_table (state.mk_state s f) x1).REFS.length)
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply table_init_trap; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.table_init_trap _ _ _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs))⟩
    · -- Rocq: `destruct n3 using N.peano_ind.`
      rcases n3 with _ | n3
      · -- Rocq: `exists s, f, []. eapply read. eapply table_init_zero; eauto. ...`
        exact ⟨s, f, [], Step.read _ _ _
          (Step_read.table_init_zero _ _ _ _ _ _ (by simp [proj_num__0]) (by simp [proj_num__0])
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega) rfl)⟩
      · -- Rocq: `exists s, f, [...]. eapply read. eapply table_init_succ; eauto. ...`
        exact ⟨s, f, _, Step.read _ _ _
          (Step_read.table_init_succ _ _ _ _ _ _
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega)
            (by simp [proj_num__0]) (by simp [proj_num__0]) (Nat.succ_ne_zero _)
            (by simp only [proj_num__0, Option.get!_some, proj_uN_0]; omega))⟩
  · simp at Hts
```

### `t_progress_be_elem_drop` : proved

Still-`sorry` earlier lemmas relied on: none. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx`.

Notes: a direct port of the Rocq bullet at `type_progress.v:4683-4692`.
- `vcs = []` is done inline: the non-empty case is closed by `simp at Hts`.
- Rocq's `case Estate: (with_elem (mk_state s f) x []) => [s' f']` becomes
  `cases Estate : ... with | mk_state s' f'`.
- `rewrite -Estate` becomes `rw [← Estate]`, and `apply: Step__elem_drop` becomes
  `exact Step.elem_drop _ x`.
- This is the same pattern as C12's `local_set`/`global_set`.

```lean
  intro C x rt Hlen Hlookup HWfC HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs1⟩
  · -- Rocq: `case Estate: (with_elem (mk_state s f) x []) => [s' f']. exists s', f', [].
    --        rewrite -Estate. by apply: Step__elem_drop.`
    cases Estate : with_elem (state.mk_state s f) x [] with
    | mk_state s' f' =>
      refine ⟨s', f', [], ?_⟩
      rw [← Estate]
      exact Step.elem_drop _ x
  · simp at Hts
```

## Final Lean check output

Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean
/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C15/Work.lean`
(exit 0, no errors and no warnings, both `rfl` guards accepted):

```
'TLC.t_progress_be_table_init_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_elem_drop_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

Axiom-source check (`.../prove-C15/Ax.lean`):

```
'TLC.invert_typeof_I32' depends on axioms: [propext, sorryAx]
'fun_elem' depends on axioms: [propext]
'fun_table' depends on axioms: [propext]
'Step_read.table_init_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Step_read.table_init_zero' depends on axioms: [propext]
'Step_read.table_init_trap' depends on axioms: [propext]
```

## Safety check at END

```
safety check [prove-C15] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134729.949676019Z-prove-C15-1509919.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

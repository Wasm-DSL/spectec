# prove-C14 log (bundle20 progress port, proof batch C14)

Target: `t_progress_be_table_copy` (TypeProgress.lean:2089; Rocq type_progress.v:4511-4605, bullet
`Instr_ok__table_copy` of `t_progress_be`).

## Safety check at START
```
safety check [prove-C14] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134127.833560989Z-prove-C14-1506528.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- Scratch `build.py` pulls the target header verbatim from TypeProgress.lean (from `theorem` to `:= sorry`), renames
  it `t_progress_be_table_copy_proof`, appends the proof and the guard
  `example : type_of% @t_progress_be_table_copy_proof = type_of% @t_progress_be_table_copy := rfl`, inside
  `import TypeProgress` / `namespace TLC`. `lake env lean Work.lean`: exit 0, no output (proof and guard pass).
- Negative control `Work_ctl.lean` (same file plus `#print axioms` and `example : (1:Nat) = 2 := rfl`): the bogus
  example fails with a type mismatch (exit 1), so the check is live.
- TypeProgress.olean (20:18:19.90) is newer than TypeProgress.lean (20:18:16.73), so the guard compares against the
  current statement.
- Merge simulation `Head.lean` (scratch, from `head.py`): the real TypeProgress.lean lines 1..2097 with my proof in
  place of `:= sorry` for the target, plus `#print axioms t_progress_be_table_copy` and `end TLC`. `lake env lean`:
  exit 0, 0 errors; the last `declaration uses sorry` warning is at line 2078 (`t_progress_be_table_fill`, not mine),
  so the target (Head.lean 2089) does not warn. This also confirms the ordering rule.
- One Lean process at a time, `lake env lean` only (never `lake build`). No repo file edited.
- Porting: follows the Rocq bullet: `right`; take `ts1 = [I32; I32; I32]` from `Htf`; Rocq's Ltac
  `invert_typeof_vcs` done inline (`rcases` on `vcs` + `simp at Hts`); `invert_typeof_I32` on the three values;
  case on the trap condition `n2+n3 > |tab x2| \/ n1+n3 > |tab x1|` (Rocq's `case Hs`) -> `Step_read.table_copy_trap`;
  otherwise `n3 = 0` (Rocq's `N.peano_ind` base) -> `Step_read.table_copy_zero`; otherwise case `n1 <= n2`
  (Rocq's `case Hle`) -> `Step_read.table_copy_le`, else `Step_read.table_copy_gt`.
  The Lean step rules take `v_n` directly and output `Int.toNat (v_n - 1)` etc., and `es'` is an existential, so
  Rocq's `n3 = N.succ n3 - 1` / `add_sub_parens` rewrites are unnecessary (witness `es'` left as `_`).
  The Lean `table_copy_le`/`_gt` rules have no `Step_read_before_*` negative premise, so none is needed.
- Axioms (`#print axioms`): `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`; `sorryAx` is inherited only from
  the still-sorry earlier lemma `invert_typeof_I32` (TypeProgress.lean:209). No HelperLemmas project axiom used.
  No `sorry`, `admit`, `native_decide`, or new axioms.

## Results
### `t_progress_be_table_copy` : proved
Still-`sorry` earlier lemmas relied on: `invert_typeof_I32` (line 209). Other earlier/imported decls used:
`t_progress_be_P` (line 1486, def), `mkFunctype` (Subtyping.lean:32), generated `Step.read`,
`Step_read.table_copy_{trap,zero,le,gt}`, `fun_table`, `proj_num__0`, `proj_uN_0`.
```lean
  intro C x1 x2 lim1 rt lim2 Hlenx1 Hlookupx1 Hlenx2 Hlookupx2 HWfC HWfinstr HWfTabType1 HWfTabType2
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
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    have HP2 : wf_val v2 := HWfVals v2 (by simp)
    have HP3 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 HP1
    obtain ⟨n2, Heqv2⟩ := invert_typeof_I32 v2 Ht2 HP2
    obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 HP3
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv2, Heqv3]
    by_cases Hs : n2 + n3 > (fun_table (state.mk_state s f) x2).REFS.length ∨
        n1 + n3 > (fun_table (state.mk_state s f) x1).REFS.length
    · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.table_copy_trap (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
          (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)) n3 x1 x2 (by simp [proj_num__0]) (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs))⟩
    · have Hb : n2 + n3 ≤ (fun_table (state.mk_state s f) x2).REFS.length ∧
          n1 + n3 ≤ (fun_table (state.mk_state s f) x1).REFS.length := by omega
      by_cases Hz : n3 = 0
      · subst Hz
        exact ⟨s, f, [], Step.read _ _ _
          (Step_read.table_copy_zero (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
            (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)) 0 x1 x2 (by simp [proj_num__0]) (by simp [proj_num__0])
            (by simpa [proj_num__0, proj_uN_0] using Hb) rfl)⟩
      · by_cases Hle : n1 ≤ n2
        · exact ⟨s, f, _, Step.read _ _ _
            (Step_read.table_copy_le (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
              (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)) n3 x1 x2 (by simp [proj_num__0]) (by simp [proj_num__0])
              Hz (by simpa [proj_num__0, proj_uN_0] using Hb) (by simpa [proj_num__0, proj_uN_0] using Hle))⟩
        · exact ⟨s, f, _, Step.read _ _ _
            (Step_read.table_copy_gt (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1))
              (num_.mk_num__0 Inn.I32 (uN.mk_uN n2)) n3 x1 x2 (by simp [proj_num__0]) (by simp [proj_num__0])
              (by simp only [proj_num__0, proj_uN_0, Option.get!_some]; omega) Hz
              (by simpa [proj_num__0, proj_uN_0] using Hb))⟩
  · simp at Hts
```

## Final Lean check output
`lake env lean Work.lean` (proof + rfl guard): exit 0, no output.

`lake env lean Head.lean` (merge simulation), non-warning lines and last two sorry warnings:
```
'TLC.t_progress_be_table_copy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Head.lean:2067:8: warning: declaration uses `sorry`
Head.lean:2078:8: warning: declaration uses `sorry`
(exit 0; 237 'declaration uses sorry' warnings, all from other still-sorry declarations at lines <= 2078)
```

Negative control `Work_ctl.lean`:
```
'TLC.t_progress_be_table_copy_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Work_ctl.lean:62:25: error: Type mismatch  rfl  has type ?m.7 = ?m.7 but is expected to have type 1 = 2
(exit 1, as intended)
```

## Safety check at END
```
safety check [prove-C14] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134441.506947336Z-prove-C14-1508228.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

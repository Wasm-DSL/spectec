# prove-H15 (bundle20 progress port, proof batch H15)

Targets (in order): `vcvtop_trunc_sat_i16_wf_instr` (TypeProgress.lean:2676, Rocq type_progress.v:6124-6130) and
`vcvtop_trunc_sat_i16_stuck` (TypeProgress.lean:2684, Rocq type_progress.v:6132-6159).
Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H15/`
(`Work.lean` = final file with both proofs and the `type_of%` rfl guards; `GuardTest.lean` = sanity check that
the guard really fails on an altered statement; `final_check_output.txt` = the last Lean run).
No repo file was edited (in particular not `TypeProgress.lean`); only this log was written inside the target dir.

## Safety check, START (run from /home/zhengyew/spectec)

```
safety check [prove-H15] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T130603.900092417Z-prove-H15-1479555.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Safety check, END (run from /home/zhengyew/spectec)

```
safety check [prove-H15] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T131156.939596070Z-prove-H15-1489446.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Result 1: `vcvtop_trunc_sat_i16_wf_instr` -- PROVED

Rocq proof: `constructor; try (by constructor; [constructor | vm_compute]). by econstructor; [constructor; vm_compute | | ].`
Lean port: the same three subgoals of `wf_instr.instr_case_39` (two `wf_shape`, one `wf_vcvtop__`), each built with
the explicit constructors; the numeric side conditions (`vm_compute` in Rocq) are closed by `decide` / `rfl`.

```lean
  refine wf_instr.instr_case_39 _ _ _ ?_ ?_ ?_
  · exact wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)
  · exact wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)
  · exact wf_vcvtop__.vcvtop___case_2 _ _ _ _ _ _ _
      (wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2.vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 _ _ _ _ _ _
        (Or.inr ⟨by decide, rfl⟩)) rfl rfl
```

Axioms (`#print axioms`): `propext, Classical.choice, Quot.sound` only. Still-`sorry` lemmas used: none.
Note: the `Or.inr` branch of the `TRUNC_SAT` side condition is `sizenn1 F32 = 2 * lsizenn2 I16` (`32 = 2 * 16`)
and `zero_opt = some ZERO`, exactly the "second disjunct" Rocq's comment describes.

## Result 2: `vcvtop_trunc_sat_i16_stuck` -- PROVED

Rocq proof: `inversion H; subst; try discriminate` leaves two `Step_pure` rules (`trap_vals`, `vcvtop`); `trap_vals` is
killed by a length/shape argument on `val_lst`; for `vcvtop`, inversion of `fun_vcvtop__` gives full / half / zero /
fallthrough: full has `4 = 8`, half has no `half` for `TRUNC_SAT`, zero would need a lane-wise `fun_lcvtop__` result
for `F32 -> I16`, but `lanes_len` makes the lane list non-empty and `fun_lcvtop__` is only `none` there; fallthrough
yields `none`, contradicting `var_0 <> none`.
Lean port (same case structure). Lean-specific points: `cases` on `Step_pure [..] es` fails on the rule `trap_vals`
(left side `Map f vs ++ (TRAP :: rest)` is not constructor-headed), so the concrete left side is first `generalize`d to
a variable `l` with `hl : [..] = l`; then `cases H` and `simp at hl` discharge all rules but `trap_vals` and `vcvtop`.
The `fun_vcvtop__` alternatives are named with `cases hf with | fun_vcvtop___case_k ...` (24 slots for case_1/case_2).

```lean
  intro H
  -- generalize the left side so that `cases` can handle the rule `trap_vals` (a non-constructor lhs)
  generalize hl : [admininstr.VCONST vectype.V128 c,
        admininstr.VCVTOP (shape.X lanetype.I16 (dim.mk_dim 8)) (shape.X lanetype.F32 (dim.mk_dim 4))
          (vcvtop__.mk_vcvtop___2 Fnn.F32 4 Jnn.I16 8
            (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT sx (some zero.ZERO)))] = l at H
  cases H
  all_goals (try (simp at hl; done))
  · -- `trap_vals`: the left side `[VCONST, VCVTOP]` has no `TRAP`
    rename_i vl al _
    rcases vl with _ | ⟨v, _ | ⟨v', vl⟩⟩ <;> simp [Map] at hl
  · -- `vcvtop`
    cases hl
    rename_i hne _ hf
    cases hf with
    | fun_vcvtop___case_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hMM _ =>
      -- full: the lane counts differ (`4 = 8`)
      omega
    | fun_vcvtop___case_1 _ _ _ _ _ _ _ v_half c_1_lst c_lst_lst var_1_lst var_0 hlen hF2 hh hvne hvget hc hF1 _ _ _ _ _ =>
      -- half: `TRUNC_SAT` has no `half`
      cases hh <;> first | exact absurd rfl hvne | (simp at hvget)
    | fun_vcvtop___case_2 _ _ _ _ _ _ v128 c_1_lst c_lst_lst var_1_lst var_0 hlen hF2 hz hvne hvget hc hF1 _ _ _ _ _ _ =>
      -- zero: no lane-wise `TRUNC_SAT` to `I16`
      have hlcvtop : ∀ (ci : lane_) (v : Option (List lane_)),
          fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim 4)) (shape.X lanetype.I16 (dim.mk_dim 8))
            (vcvtop__.mk_vcvtop___2 Fnn.F32 4 Jnn.I16 8
              (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT sx (some zero.ZERO))) ci v → v = none := by
        intro ci v hv
        cases hv
        rfl
      have h4 : c_1_lst.length = 4 := by rw [hc]; exact lanes_len lanetype.F32 4 c
      rcases var_1_lst with _ | ⟨v, vl⟩
      · have h0 : c_1_lst.length = 0 := hlen.symm
        omega
      · rcases c_1_lst with _ | ⟨ci, cl⟩
        · simp at hlen
        · exact hF1 v (List.mem_cons_self ..) (hlcvtop ci v (hF2 (v, ci) (List.mem_cons_self ..)))
    | fun_vcvtop___case_3 _ _ _ _ hnb =>
      -- fallthrough: the result is `none`
      exact hne rfl
```

Axioms (`#print axioms`): `propext, Classical.choice, Quot.sound, lanes_len` (`lanes_len` is the HelperLemmas axiom
mirroring Rocq's `axioms.v` `lanes_len`, which the Rocq proof also uses). Still-`sorry` earlier lemmas used: none.
No Lean-only helper lemma is needed (the one helper fact `hlcvtop` is a `have` inside the proof).

## Final Lean check (`cd .../test-lean-claude && lake env lean <scratch>/Work.lean`), full output

```
'TLC.vcvtop_trunc_sat_i16_wf_instr_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.vcvtop_trunc_sat_i16_stuck_proof' depends on axioms: [propext, Classical.choice, Quot.sound, lanes_len]
```
No errors, no warnings (no `sorry`); both `type_of%` rfl guards pass (guard effectiveness confirmed with an altered
statement in `GuardTest.lean`, which fails with "Type mismatch" as expected). Wall time about 2.5 s per run.
Context check: `TypeProgress.lean` has no `open`, `set_option`, `attribute`, `@[...]` or `local` lines, so the
proofs see the same environment inside the real file (`namespace TLC` only) as in `Work.lean`.

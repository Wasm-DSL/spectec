# prove-C11 log (bundle20 progress port, proof batch C11)

Result: **both targets proved** (`t_progress_be_vextbinop`, `t_progress_be_vnarrow`). No repo file edited
(only this log); scratch files only in
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C11/`
(Work.lean = final combined check file; WorkB.lean, WorkA_vnarrow.lean, Axioms*.lean, Deps.lean = intermediate/diagnostic copies).

## Safety check at START

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C11
safety check [prove-C11] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T133131.096466910Z-prove-C11-1501194.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method

Work.lean = `import TypeProgress` + `namespace TLC` + each target's header copied verbatim from TypeProgress.lean
(renamed `<name>_proof`) + `example : type_of% @<name>_proof = type_of% @<name> := rfl` guard. Proofs follow the
Rocq bullets (type_progress.v:4180-4264 and 4264-4301): intro, `unfold t_progress_be_P`, Rocq's
`move => s f C' vcs ...` names, inline `invert_typeof_vcs` as in prove-C06/C08 (`simp only [mkFunctype, ...] at Htf`,
`rcases vcs`), canonical forms via `invert_typeof_V128`, then `Step.pure` with the generated `Step_pure` rule.
One Lean process at a time (`timeout 900 lake env lean <abs path>`; never `lake build`).

Ordering rule: every TypeProgress declaration used is before line 1958 (largest: `t_progress_be_P` at 1486; lane
lemmas 241-1298). Checked with `grep -n`. A meta check (`getConstInfo` + `Expr.getUsedConstants`) confirmed that
neither proof term references `sorryAx` directly (`direct sorryAx = false` for both); `#print axioms` shows
`[propext, sorryAx, Classical.choice, Quot.sound]`, with `sorryAx` inherited only from the still-sorry lemmas listed
below. No `sorry`/`admit`/`native_decide`/new axioms in the proof text (grep count 0). No HelperLemmas axioms used.

## Results

### t_progress_be_vextbinop — proved

- Location: TypeProgress.lean:1958; Rocq type_progress.v:4180-4264
- Still-sorry earlier TypeProgress lemmas used: invert_typeof_V128 (241), lanes_Jnn_form (942), jlane_some (953),
  lanes_size_eq (963), Forall_list_slice (1088), evens_odds_concat (1236), evens_odds_size (1242), Forall_evens (1247),
  Forall_odds (1252), Forall2_of_Forall (1259), list_slice_size_eq (1266), zip_lane_wf2 (1274), zip_wf (1286),
  size_zipWith_eq (1292), shape_lanes_even (1298). (Non-sorry defs used: jlane 933, evens 1218, odds 1223,
  t_progress_be_P 1486.)
- Imported facts used: generated well-formedness theorems `extend___is_wf`, `imul__is_wf`, `iadd__is_wf`
  (todaywasm2.0.lean; bodies `sorry` there).
- Notes:
  - Same skeleton as Rocq: `wf_ishape sh_1`, `wf_ishape sh_2`, `wf_vextbinop__ sh_2 sh_1 op` from `cases HWfinstr`;
    invert `wf_vextbinop__` (`obtain ⟨J1, M1, J2, M2, o, Ho, E1, E2⟩`; its two ishape indices are auto-promoted
    parameters, so they take no slot) and `subst`; Hs1/Hs2 from `cases Hw2`/`cases Hw1`; H128 from `cases Hs1`;
    HL1/HL2 := lanes_Jnn_form; HLs := lanes_size_eq; Hext (Rocq's `Hext`, with `ext` inlined); then split
    `Ho` into EXTMUL (`hf`, `v_sx`, `Hsz`) / DOTS (`Hsz`).
  - EXTMUL: HS1/HS2 := Forall_list_slice, HSs := list_slice_size_eq, HW := zip_lane_wf2 with
    imul__is_wf/extend___is_wf, HSo1/HSo2 := jlane_some -- exactly Rocq's facts. DOT: P (Rocq `pose P`, here
    `obtain ⟨P, HPdef⟩ : ∃ P, P = List.zipWith ...`), HPw via zip_wf, HPe via size_zipWith_eq + shape_lanes_even,
    HPs/HPc := evens_odds_size/evens_odds_concat, HW2 via Forall2_of_Forall + Forall_evens/odds + iadd__is_wf.
  - Rocq's `destruct J1, J2; try (by move: Hsz); econstructor` is `cases J1 <;> cases J2 <;> (try exact absurd Hsz
    (by decide))`: `decide` refutes the size constraint (`2*lsize J1 = lsize J2 ∧ lsize J2 ≥ 16` for EXTMUL,
    `... ∧ lsize J2 = 32` for DOTS) in the impossible combinations, leaving (I16,I32), (I32,I64), (I8,I16) for EXTMUL
    (generated `fun_vextbinop___case_3/4/14`, picked with `first`) and (I16,I32) for DOTS (`fun_vextbinop___case_19`).
    The generated `fun_vextbinop__` has one constructor per (J1,J2) pair (16 per op) plus a catch-all `none` case.
  - Deviation (Lean-way, same content): Rocq passes the result vector explicitly to `Step_pure__vextbinop`; here the
    `fun_vextbinop__ ... (some c)` fact is proved first as `Hfun : ∃ c, ...` (the witness is fixed by the
    constructor's `c = inv_lanes_ ...` premise, closed by `rfl`), then `Step.pure` + `Step_pure.vextbinop c1 c2 _ _ _
    c (some c) Hc (Option.some_ne_none c) rfl`. This avoids writing the long result expression twice.
  - The DOT `concat_` premise is stated with `Map₂` in Lean (`Map₂ f l1 l2 = List.zipWith (·  ·) (l1.map f) l2`);
    a local `hMap2 : Map₂ g l1 l2 = List.zipWith g l1 l2` (`simp [Map₂, List.ap, List.zipWith_map_left]`, as in
    prove-C07) turns it into `HPc.trans HPdef`.
  - Lean's DOT rule fixes the extension signedness to `sx.S` (Rocq `res_S`), as in Rocq.
- Body (goes after `:= by`):

```lean
  intro C sh_1 sh_2 op HWfC HWfinstr
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
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP0
    have Hw1 : wf_ishape sh_1 := by cases HWfinstr; assumption
    have Hw2 : wf_ishape sh_2 := by cases HWfinstr; assumption
    have Hop : wf_vextbinop__ sh_2 sh_1 op := by cases HWfinstr; assumption
    obtain ⟨J1, M1, J2, M2, o, Ho, E1, E2⟩ := Hop
    subst E1 E2
    have Hs1 : wf_shape (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) := by cases Hw2; assumption
    have Hs2 : wf_shape (shape.X (lanetype_Jnn J2) (dim.mk_dim M2)) := by cases Hw1; assumption
    have H128 : lsize (lanetype_Jnn J1) * M1 = 128 := by
      cases Hs1 with
      | shape_case_0 _ _ _ h => exact h
    have HL1 := lanes_Jnn_form J1 M1 c1 Hs1 Hwf1
    have HL2 := lanes_Jnn_form J1 M1 c2 Hs1 Hwf2
    have HLs := lanes_size_eq (lanetype_Jnn J1) M1 c1 c2
    -- Lean's `Map₂` is `zipWith` (Rocq's `list_zipWith`)
    have hMap2 : ∀ {A B D : Type} (g : A → B → D) (l1 : List A) (l2 : List B),
        Map₂ g l1 l2 = List.zipWith g l1 l2 := by
      intro A B D g l1 l2
      simp [Map₂, List.ap, List.zipWith_map_left]
    have Hext : ∀ (v_sx : sx) (l : lane_), jlane J1 l →
        wf_uN (lsize (lanetype_Jnn J2)) (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) v_sx
          (Option.get! (proj_lane__0 l))) := by
      intro v_sx l ⟨x, hx, Hx⟩
      subst hx
      exact extend___is_wf _ _ v_sx x _ Hx rfl
    have Hfun : ∃ c, fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)))
        (ishape.mk_ishape (shape.X (lanetype_Jnn J2) (dim.mk_dim M2)))
        (vextbinop__.mk_vextbinop___0 J1 M1 J2 M2 o) c1 c2 (some c) := by
      rcases Ho with ⟨hf, v_sx, Hsz⟩ | ⟨Hsz⟩
      · -- EXTMUL: the extended lanes of one half of each operand are multiplied.
        have HS1 := Forall_list_slice _ _ (fun_half hf 0 M2) M2 HL1
        have HS2 := Forall_list_slice _ _ (fun_half hf 0 M2) M2 HL2
        have HSs := list_slice_size_eq _ _ _ _ (fun_half hf 0 M2) M2 HLs
        have HW := zip_lane_wf2 J1 J2 (lanetype_Jnn J2)
          (fun a b => imul_ (lsizenn2 (lanetype_Jnn J2))
            (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) v_sx a)
            (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) v_sx b)) _ _ rfl
          (fun a b Ha Hb => imul__is_wf _ _ _ _ (extend___is_wf _ _ _ _ _ Ha rfl)
            (extend___is_wf _ _ _ _ _ Hb rfl) rfl) HS1 HS2 HSs
        have HSo1 := jlane_some _ _ HS1
        have HSo2 := jlane_some _ _ HS2
        cases J1 <;> cases J2 <;> (try exact absurd Hsz (by decide)) <;>
        first
          | exact ⟨_, fun_vextbinop__.fun_vextbinop___case_3 M1 M2 hf v_sx c1 c2 M1 M2 _ _ _ rfl rfl
              HSo1 HSo2 rfl Hs1 Hs2 HSs HSo1 HSo2 HW rfl rfl⟩
          | exact ⟨_, fun_vextbinop__.fun_vextbinop___case_4 M1 M2 hf v_sx c1 c2 M1 M2 _ _ _ rfl rfl
              HSo1 HSo2 rfl Hs1 Hs2 HSs HSo1 HSo2 HW rfl rfl⟩
          | exact ⟨_, fun_vextbinop__.fun_vextbinop___case_14 M1 M2 hf v_sx c1 c2 M1 M2 _ _ _ rfl rfl
              HSo1 HSo2 rfl Hs1 Hs2 HSs HSo1 HSo2 HW rfl rfl⟩
      · -- DOT: the products of the extended lanes are added pairwise.
        obtain ⟨P, HPdef⟩ : ∃ P : List iN, P = List.zipWith (fun a b => imul_ (lsizenn2 (lanetype_Jnn J2))
            (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx.S (Option.get! (proj_lane__0 a)))
            (extend__ (lsizenn1 (lanetype_Jnn J1)) (lsizenn2 (lanetype_Jnn J2)) sx.S (Option.get! (proj_lane__0 b))))
            (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) c1)
            (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim M1)) c2) := ⟨_, rfl⟩
        have HPw : Forall (fun x => wf_uN (lsize (lanetype_Jnn J2)) x) P := by
          rw [HPdef]
          exact zip_wf J1 _ _ _ _ (fun a b Ha Hb => imul__is_wf _ _ _ _ (Hext _ _ Ha) (Hext _ _ Hb) rfl) HL1 HL2
        have HPe : ¬ Odd P.length := by
          rw [HPdef, size_zipWith_eq _ _ _ _ _ _ HLs]
          exact shape_lanes_even J1 M1 c1 H128
        have HPs := evens_odds_size _ _ HPe
        have HPc := evens_odds_concat _ _ HPe
        have HW2 : Forall₂ (fun a b => wf_lane_ (lanetype_Jnn J2)
            (lane_.mk_lane__0 J2 (iadd_ (lsizenn2 (lanetype_Jnn J2)) a b))) (evens P) (odds P) :=
          Forall2_of_Forall _ _ _ _ _
            (fun a b Ha Hb => wf_lane_.lane__case_0 _ J2 _ (iadd__is_wf _ _ _ _ Ha Hb rfl) rfl)
            (Forall_evens _ _ _ HPw) (Forall_odds _ _ _ HPw) HPs
        have HSo1 := jlane_some _ _ HL1
        have HSo2 := jlane_some _ _ HL2
        cases J1 <;> cases J2 <;> (try exact absurd Hsz (by decide))
        exact ⟨_, fun_vextbinop__.fun_vextbinop___case_19 M1 M2 c1 c2 (evens P) (odds P) M1 M2 _ _ _ rfl rfl
          HSo1 HSo2 (by simp only [hMap2]; exact HPc.trans HPdef) rfl Hs1 Hs2 HPs HW2 rfl rfl⟩
    obtain ⟨c, Hc⟩ := Hfun
    refine ⟨s, f, [admininstr.VCONST vectype.V128 c], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    exact Step.pure _ _ _ (Step_pure.vextbinop c1 c2 _ _ _ c (some c) Hc (Option.some_ne_none c) rfl)
  · simp at Hts
```

### t_progress_be_vnarrow — proved

- Location: TypeProgress.lean:1968; Rocq type_progress.v:4264-4301
- Still-sorry earlier TypeProgress lemmas used: invert_typeof_V128 (241), lanes_Jnn_form (942), jlane_some (953),
  Forall_map_P (1063), wf_ishape_inv (1190). (Non-sorry defs used: jlane 933, t_progress_be_P 1486.)
- Imported facts used: generated well-formedness theorems `narrow___is_wf`, `lanes__is_wf` (todaywasm2.0.lean;
  bodies `sorry` there).
- Notes: Direct port of the Rocq bullet: `wf_ishape_inv` on `Hw1`/`Hw2` with `rfl` patterns (Rocq `->`) giving
  sh_1 = J2/N2 (output) and sh_2 = J1/N1 (input); HL1/HL2 := lanes_Jnn_form; `Hnar` as in Rocq (Forall_map_P +
  `wf_lane_.lane__case_0` + narrow___is_wf); result vector given explicitly with the generated rule's `Map` forms;
  `Step_pure.vnarrow c1 c2 J2 N2 J1 N1 v_sx _ (lanes c1) (lanes c2) _ _` with premises rfl, rfl, jlane_some HL1, rfl,
  jlane_some HL2, rfl, rfl, lanes__is_wf (x2), Hs1, Hs2, Hnar HL1, Hnar HL2 (the `cj_*` lists and the result `c` are
  fixed by the `rfl` premises). One fix on the way: `Forall_map_P _ _ _ _ _ _ _ HL` (Rocq argument count) put `HL`
  in the pointwise-hypothesis slot ("introN failed"); Lean needs `refine Forall_map_P _ _ _ _ _ _ ?_ HL`.
- Body (goes after `:= by`):

```lean
  intro C sh_1 sh_2 v_sx HWfC HWfinstr
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
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP
    obtain ⟨c2, Heqv2, Hwf2⟩ := invert_typeof_V128 v2 Ht2 HP0
    have Hw1 : wf_ishape sh_1 := by cases HWfinstr; assumption
    have Hw2 : wf_ishape sh_2 := by cases HWfinstr; assumption
    obtain ⟨J2, N2, rfl, Hs2, _⟩ := wf_ishape_inv _ Hw1
    obtain ⟨J1, N1, rfl, Hs1, _⟩ := wf_ishape_inv _ Hw2
    have HL1 := lanes_Jnn_form J1 N1 c1 Hs1 Hwf1
    have HL2 := lanes_Jnn_form J1 N1 c2 Hs1 Hwf2
    have Hnar : ∀ L, Forall (jlane J1) L →
        Forall (fun cj => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn J2) (dim.mk_dim N2))) (lane_.mk_lane__0 J2 cj))
          (List.map (fun l => narrow__ (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2)) v_sx
            (Option.get! (proj_lane__0 l))) L) := by
      intro L HL
      refine Forall_map_P _ _ _ _ _ _ ?_ HL
      intro l ⟨x, hx, Hx⟩
      subst hx
      exact wf_lane_.lane__case_0 _ J2 _ (narrow___is_wf _ _ v_sx x _ Hx rfl) rfl
    refine ⟨s, f, [admininstr.VCONST vectype.V128 (inv_lanes_ (shape.X (lanetype_Jnn J2) (dim.mk_dim N2))
      (Map (fun cj => lane_.mk_lane__0 J2 cj) (Map (fun l => narrow__ (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2)) v_sx
          (Option.get! (proj_lane__0 l))) (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim N1)) c1)) ++
       Map (fun cj => lane_.mk_lane__0 J2 cj) (Map (fun l => narrow__ (lsize (lanetype_Jnn J1)) (lsize (lanetype_Jnn J2)) v_sx
          (Option.get! (proj_lane__0 l))) (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim N1)) c2))))], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    exact Step.pure _ _ _ (Step_pure.vnarrow c1 c2 J2 N2 J1 N1 v_sx _
      (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim N1)) c1) (lanes_ (shape.X (lanetype_Jnn J1) (dim.mk_dim N1)) c2)
      _ _ rfl rfl (jlane_some _ _ HL1) rfl (jlane_some _ _ HL2) rfl rfl
      (lanes__is_wf _ _ _ Hs1 Hwf1 rfl) (lanes__is_wf _ _ _ Hs1 Hwf2 rfl) Hs1 Hs2 (Hnar _ HL1) (Hnar _ HL2))
  · simp at Hts
```

## Final Lean check output

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C11/Work.lean`
-> exit=0, output empty (0 bytes: no errors, no warnings; both `type_of%` rfl guards pass).

Diagnostics (copies of Work.lean with extra commands):
```
'TLC.t_progress_be_vextbinop_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_vnarrow_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
TLC.t_progress_be_vextbinop_proof: direct sorryAx = false
TLC.t_progress_be_vnarrow_proof: direct sorryAx = false
```

## Safety check at END

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-C11
safety check [prove-C11] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134039.944016442Z-prove-C11-1506162.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Safety check after writing this log (final)

```
safety check [prove-C11] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134128.550181250Z-prove-C11-1506619.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

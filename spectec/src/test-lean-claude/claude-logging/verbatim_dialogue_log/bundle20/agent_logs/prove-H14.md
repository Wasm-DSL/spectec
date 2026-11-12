# prove-H14 (bundle20 progress port, proof batch H14)

Targets (14): `setproduct1_Forall`, `setproduct_Forall`, `setproduct_nonempty`, `setproduct_pick` (TypeProgress.lean:1360-1377), `halfop_total`, `zeroop_total`, `zero_lane_wf`, `vcvtop_step_full`, `vcvtop_step_half`, `vcvtop_step_zero`, `vcvtop_zero_numtype`, `vcvtop_full_lsize` (1407-1478), `vload_shape64_wf`, `vload_shape64_stuck` (2662-2668).

**Result: all 14 proved; no statement changed; no repo file edited.** Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H14/` (`Work1..8.lean` = per-target files with header copy + `type_of%` guard; `proofs/<name>.txt` = the exact tactic blocks below; `TypeProgressH14.lean` = merge simulation; `merged_check.out`; `NegControl.lean`). Only my own log file was written inside the target dir (plus the safety-check output files the check script itself creates).

## Safety check at START
```
safety check [prove-H14] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T125905.870699348Z-prove-H14-1474195.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- Per target: scratch file with the header copied verbatim from TypeProgress.lean (theorem renamed `<name>_proof`) and the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all 14 guards pass). Negative control (`NegControl.lean`: a copy of `setproduct1_Forall`'s statement guarded against `setproduct_Forall`'s) correctly FAILS with "Type mismatch", the identical-statement control passes, so the guard is live.
- Merge simulation `TypeProgressH14.lean`: the REAL, current TypeProgress.lean (2690 lines) with the 14 `sorry` bodies replaced (by script) by the blocks below, compiled whole with `lake env lean` against the same imports (`import TypePreservation` etc.). Result: 0 errors; no `declaration uses sorry` warning at any of the 14 targets; so the blocks drop into the real file unchanged and respect the ordering rule (they only use declarations before the target in TypeProgress.lean plus imports).
- One Lean process at a time (`lake env lean <scratch file>` only; never `lake build`; nothing written under `.lake/`). Each run took ~2-3 s.
- Axioms: only the standard ones (`propext`; `Classical.choice`/`Quot.sound` enter through Mathlib `norm_num` and through opaque constants in statements such as `inv_lanes_`). No HelperLemmas project axiom used. No `sorry`, `admit`, `native_decide`, new axioms.
- Pitfalls hit (all solved, see notes): leading `shape_1 shape_2` constructor args take no `cases ... with` slot; `first | exact absurd _ (by tac)` does not backtrack when `tac` leaves a goal (use `(tac; done)`); `simpa using Hin` cannot unfold `Map`; `cases H` on `Step_read` needs `generalize` first; hypothesis order after `obtain ⟨rfl,..⟩` changes (`rename_i`).

## Results

### `setproduct1_Forall` : proved

Still-`sorry` earlier lemmas relied on: `setproduct2_Forall` (TypeProgress:1354, still `sorry`; Rocq uses it too).

```lean
  intro Hl HS
  induction l with
  | nil => intro x hx; simp [setproduct1_] at hx
  | cons w l' ih =>
    have Hw : P w := Hl w (List.mem_cons_self ..)
    have Hl' : Forall P l' := fun x hx => Hl x (List.mem_cons_of_mem _ hx)
    have h2 := setproduct2_Forall X P w S Hw HS
    have h1 := ih Hl'
    intro x hx
    simp only [setproduct1_, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h2 x hx
    · exact h1 x hx
```

Notes: Induction on `l` (Rocq `elim: Hl`; Lean generalizes `Hl` automatically). `setproduct1_ X (w :: l') S = setproduct2_ X w S ++ setproduct1_ X l' S`, so membership in the append splits into the `setproduct2_Forall` part and the IH. Axioms: propext (+ sorryAx only through `setproduct2_Forall`).

### `setproduct_Forall` : proved

Still-`sorry` earlier lemmas relied on: `setproduct1_Forall` (target of this batch, 1360; transitively `setproduct2_Forall`).

```lean
  intro H
  induction ls with
  | nil =>
    intro x hx
    simp only [setproduct_, List.mem_singleton] at hx
    subst hx
    intro y hy
    simp at hy
  | cons l ls' ih =>
    have Hl : Forall P l := H l (List.mem_cons_self ..)
    have Hls' : Forall (Forall P) ls' := fun x hx => H x (List.mem_cons_of_mem _ hx)
    exact setproduct1_Forall X P l (setproduct_ X ls') Hl (ih Hls')
```

Notes: Induction on `ls`; nil case: `setproduct_ X [] = [[]]` and `[]` satisfies `Forall P` vacuously; cons case is exactly `setproduct1_Forall` as in Rocq.

### `setproduct_nonempty` : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro H
  induction ls with
  | nil => simp [setproduct_]
  | cons l ls' ih =>
    have Hl : l ≠ [] := H l (List.mem_cons_self ..)
    have Hls' : Forall (fun l => l ≠ []) ls' := fun x hx => H x (List.mem_cons_of_mem _ hx)
    have IH := ih Hls'
    simp only [setproduct_]
    cases l with
    | nil => exact absurd rfl Hl
    | cons w l' =>
      cases hS : setproduct_ X ls' with
      | nil => exact absurd hS IH
      | cons s S => simp [setproduct1_, setproduct2_]
```

Notes: Induction on `ls`; case on the head list (non-empty by hypothesis) and on `setproduct_ X ls'` (non-empty by IH), then `simp [setproduct1_, setproduct2_]`. Axioms: propext only.

### `setproduct_pick` : proved

Still-`sorry` earlier lemmas relied on: `setproduct_nonempty`, `setproduct_Forall` (both targets of this batch; transitively `setproduct2_Forall`, still `sorry`).

```lean
  intro Hne Hw
  have Hsp := setproduct_nonempty lane_ lss Hne
  have Hsw := setproduct_Forall lane_ (wf_lane_ lt) lss Hw
  revert Hsp Hsw
  cases hS : setproduct_ lane_ lss with
  | nil => intro Hsp; exact absurd rfl Hsp
  | cons cj S =>
    intro _ Hsw
    refine ⟨inv_lanes_ (shape.X lt (dim.mk_dim M)) cj, ?_, ?_, Hsw⟩
    · simp
    · simp
```

Notes: As in Rocq: revert the two facts, `cases` on `setproduct_ lane_ lss` (nil contradicts non-emptiness), witness `inv_lanes_ (shape.X lt (dim.mk_dim M)) cj`. Rocq's `N.ltb_spec0`/`lia` and `mem_head` become `simp` (`List.length_map`, `List.mem_cons_self`).

### `halfop_total` : proved

Still-`sorry` earlier lemmas relied on: none (only the definitions `halfop_of`, `vcvtop_trunc_sat_i16`).

```lean
  intro Hop Hts
  cases Hop with
  | vcvtop___case_0 J1 M1 J2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases J1 <;> cases J2 <;> constructor <;> rfl
  | vcvtop___case_1 J1 M1 F2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases J1 <;> cases F2 <;> constructor <;> rfl
  | vcvtop___case_2 F1 M1 J2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases F1 <;> cases J2 <;> constructor <;> rfl
  | vcvtop___case_3 F1 M1 F2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx <;> (cases F1 <;> cases F2 <;> constructor <;> rfl)
```

Notes: Invert `wf_vcvtop__` (4 constructors; the equations `sh_i = shape.X ..` are `subst`ed since `sh_i` are variables), invert the inner `wf_vcvtop__*`, split the `Jnn`/`Fnn` variables, then `constructor <;> rfl` picks the matching generated constructor `fun_halfop_case_k` (`M_1 = M_1_0` closed by `rfl`; `halfop_of op` reduces by iota). Lean's generated `fun_halfop` has a constructor for EVERY (source lane, destination lane) pair of each `vcvtop__` constructor, so neither the wf size side-conditions nor the hypothesis `vcvtop_trunc_sat_i16 op = false` is needed (`Hts` is unused; Rocq needed it in `vcvtop_cases`). Binder-slot note: for `cases Hop with | vcvtop___case_0 ..` the two leading `shape_1 shape_2` args take no slot (they are unified with the indices), inner `cases Hx` needs no names. Axioms: propext only.

### `zeroop_total` : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro Hop Hts
  cases Hop with
  | vcvtop___case_0 J1 M1 J2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases J1 <;> cases J2 <;> constructor <;> rfl
  | vcvtop___case_1 J1 M1 F2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases J1 <;> cases F2 <;> constructor <;> rfl
  | vcvtop___case_2 F1 M1 J2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx
    cases F1 <;> cases J2 <;> constructor <;> rfl
  | vcvtop___case_3 F1 M1 F2 M2 x Hx E1 E2 =>
    subst E1 E2
    cases Hx <;> (cases F1 <;> cases F2 <;> constructor <;> rfl)
```

Notes: Identical to `halfop_total` (generated `fun_zeroop` also has all 40 combos). `Hts` unused. Axioms: propext only.

### `zero_lane_wf` : proved

Still-`sorry` earlier lemmas relied on: `packnum_not_none` (TypeProgress:1122, still `sorry`; Rocq uses it too). Also uses the wasm2.0 generated lemmas `zero_is_wf` / `packnum__is_wf` (imported).

```lean
  have Hz : wf_num_ (unpack (lanetype_numtype nt)) (fun_zero nt) := by
    cases nt <;> exact zero_is_wf _ _ rfl
  have Hp := packnum_not_none _ _ Hz
  exact ⟨Hp, packnum__is_wf _ _ _ Hz Hp rfl⟩
```

Notes: As in Rocq: `zero_is_wf` per numtype (`cases nt`), `packnum_not_none`, `packnum__is_wf`; `!(x)` is `Option.get!`.

### `vcvtop_step_full` : proved

Still-`sorry` earlier lemmas relied on: `vcvtop_lanes_total` (TypeProgress:1339, still `sorry`); batch-internal: `setproduct_pick`, `halfop_total`, `zeroop_total`. Imported wasm2.0 generated `lanes__is_wf` is itself `sorry` in wasm2.0.lean.

```lean
  intro Hc Hs1 Hs2 Hop Hts Hh Hz
  have Hl := lanes__is_wf _ _ _ Hs1 Hc rfl
  obtain ⟨vs, H2, Hn, Hne0, Hne, Hw⟩ := vcvtop_lanes_total _ _ _ _ Hs1 Hs2 Hop Hts Hl
  obtain ⟨c, Hgt, Hin, Hsw⟩ := setproduct_pick L2 M _ Hne Hw
  have Hhalf := halfop_total _ _ _ Hop Hts
  have Hzero := zeroop_total _ _ _ Hop Hts
  rw [Hh] at Hhalf
  rw [Hz] at Hzero
  refine ⟨c, Step_pure.vcvtop c1 _ _ op c (some c) ?_ (by simp) rfl⟩
  exact fun_vcvtop__.fun_vcvtop___case_0 L1 M L2 op c1 c M _ _ vs (some none) (some none)
    Hn H2 Hzero Hhalf (by simp) (by simp) ⟨rfl, rfl⟩ rfl Hne0 rfl Hgt (List.elem_eq_true_of_mem Hin) Hs1 Hs2 rfl
```

Notes: Same structure as Rocq. `Step_pure.vcvtop c1 _ _ op c (some c)` then `fun_vcvtop__.fun_vcvtop___case_0 L1 M L2 op c1 c M _ _ vs (some none) (some none) ..` with the premises in generated order: length (`Hn`, this is the extra conjunct of the Lean `vcvtop_lanes_total`), `Forall₂` (`H2`), `fun_zeroop`/`fun_halfop` (`Hzero`/`Hhalf` after `rw [Hz/Hh]`), the two `≠ none` (`by simp`), `⟨rfl, rfl⟩`, `c_1_lst = lanes_ ..` (`rfl`), `Hne0`, `c_lst_lst = setproduct_ ..` (`rfl`), `Hgt`, `List.contains` (`List.elem_eq_true_of_mem Hin`), `Hs1 Hs2`, `M = M` (`rfl`). (`simpa using Hin` does NOT work for `List.contains (Map ..)`: `Map` is not unfolded by simp.)

### `vcvtop_step_half` : proved

Still-`sorry` earlier lemmas relied on: `Forall_list_slice` (TypeProgress:1088, still `sorry`), `vcvtop_lanes_total` (1339, still `sorry`); batch-internal: `setproduct_pick`, `halfop_total`.

```lean
  intro Hc Hs1 Hs2 Hop Hts Hh
  have Hl := Forall_list_slice _ _ (fun_half h 0 M2) M2 (lanes__is_wf _ _ _ Hs1 Hc rfl)
  obtain ⟨vs, H2, Hn, Hne0, Hne, Hw⟩ := vcvtop_lanes_total _ _ _ _ Hs1 Hs2 Hop Hts Hl
  obtain ⟨c, Hgt, Hin, Hsw⟩ := setproduct_pick L2 M2 _ Hne Hw
  have Hhalf := halfop_total _ _ _ Hop Hts
  rw [Hh] at Hhalf
  refine ⟨c, Step_pure.vcvtop c1 _ _ op c (some c) ?_ (by simp) rfl⟩
  exact fun_vcvtop__.fun_vcvtop___case_1 L1 M1 L2 M2 op c1 c h _ _ vs (some (some h))
    Hn H2 Hhalf (by simp) rfl rfl Hne0 rfl Hgt (List.elem_eq_true_of_mem Hin) Hs1 Hs2
```

Notes: As in Rocq with `fun_vcvtop__.fun_vcvtop___case_1 L1 M1 L2 M2 op c1 c h _ _ vs (some (some h)) ..`; `Hl := Forall_list_slice _ _ (fun_half h 0 M2) M2 (lanes__is_wf ..)` matches the generated `List.take M_2 (List.drop (fun_half v_half 0 M_2) (lanes_ ..))`.

### `vcvtop_step_zero` : proved

Still-`sorry` earlier lemmas relied on: `vcvtop_lanes_total` (1339, still `sorry`), `packnum_not_none` via `zero_lane_wf`; batch-internal: `zero_lane_wf`, `setproduct_pick`, `zeroop_total`.

```lean
  intro Hc Hs1 Hs2 Hop Hts Hz
  have Hl := lanes__is_wf _ _ _ Hs1 Hc rfl
  obtain ⟨vs, H2, Hn, Hne0, Hne, Hw⟩ := vcvtop_lanes_total _ _ _ _ Hs1 Hs2 Hop Hts Hl
  obtain ⟨Hpz, Hwz⟩ := zero_lane_wf nt2
  have Hu : ∀ nt : numtype, unpack (lanetype_numtype nt) = nt := by
    intro nt; cases nt <;> rfl
  have Hpz' : packnum_ (lanetype_numtype nt2) (fun_zero (unpack (lanetype_numtype nt2))) ≠ none := by
    rw [Hu nt2]; exact Hpz
  have Hwz' : wf_lane_ (lanetype_numtype nt2)
      (Option.get! (packnum_ (lanetype_numtype nt2) (fun_zero (unpack (lanetype_numtype nt2))))) := by
    rw [Hu nt2]; exact Hwz
  have Hne' : Forall (fun l => l ≠ [])
      (List.map (fun v => Option.get! v) vs ++
        List.replicate M1 [Option.get! (packnum_ (lanetype_numtype nt2) (fun_zero (unpack (lanetype_numtype nt2))))]) := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact Hne l hl
    · rw [List.eq_of_mem_replicate hl]
      exact List.cons_ne_nil _ _
  have Hw' : Forall (Forall (wf_lane_ (lanetype_numtype nt2)))
      (List.map (fun v => Option.get! v) vs ++
        List.replicate M1 [Option.get! (packnum_ (lanetype_numtype nt2) (fun_zero (unpack (lanetype_numtype nt2))))]) := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact Hw l hl
    · rw [List.eq_of_mem_replicate hl]
      intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact Hwz'
  obtain ⟨c, Hgt, Hin, Hsw⟩ := setproduct_pick (lanetype_numtype nt2) M2 _ Hne' Hw'
  have Hzero := zeroop_total _ _ _ Hop Hts
  rw [Hz] at Hzero
  refine ⟨c, Step_pure.vcvtop c1 _ _ op c (some c) ?_ (by simp) rfl⟩
  exact fun_vcvtop__.fun_vcvtop___case_2 (lanetype_numtype nt1) M1 (lanetype_numtype nt2) M2 op c1 c _ _ vs
    (some (some zero.ZERO)) Hn H2 Hzero (by simp) rfl rfl Hne0 Hpz' rfl Hgt (List.elem_eq_true_of_mem Hin) Hs1 Hs2
```

Notes: Same as Rocq with `fun_vcvtop___case_2`. Lean-specific: the generated constructor has `packnum_ Lnn_2 (fun_zero (unpack Lnn_2))` while `zero_lane_wf nt2` is stated with `fun_zero nt2`; bridged with `Hu : unpack (lanetype_numtype nt) = nt` (`cases nt <;> rfl`) and `rw [Hu nt2]` on the GOAL (`Hpz'`, `Hwz'`). The padding rows `List.replicate M1 [zero lane]` are handled with core `List.eq_of_mem_replicate` (so NO use of the sorry'd `Forall_list_repeat`).

### `vcvtop_zero_numtype` : proved

Still-`sorry` earlier lemmas relied on: none (only defs `zeroop_of`, `vcvtop_trunc_sat_i16`).

```lean
  intro Hop Hts Hz
  cases Hop with
  | vcvtop___case_0 J1 M1' J2 M2' x Hx E1 E2 =>
    exact absurd Hz (by simp [zeroop_of])
  | vcvtop___case_1 J1 M1' F2 M2' x Hx E1 E2 =>
    exact absurd Hz (by simp [zeroop_of])
  | vcvtop___case_2 F1 M1' J2 M2' x Hx E1 E2 =>
    simp only [shape.X.injEq, dim.mk_dim.injEq] at E1 E2
    obtain ⟨rfl, rfl⟩ := E1
    obtain ⟨rfl, rfl⟩ := E2
    cases Hx with
    | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 sx zo hcond =>
      simp only [zeroop_of] at Hz
      subst Hz
      cases z
      cases F1 <;> cases J2 <;> first
        | (simp [vcvtop_trunc_sat_i16] at Hts; done)
        | (exfalso; revert hcond; decide)
        | exact ⟨numtype.F64, numtype.I32, rfl, rfl⟩
  | vcvtop___case_3 F1 M1' F2 M2' x Hx E1 E2 =>
    simp only [shape.X.injEq, dim.mk_dim.injEq] at E1 E2
    obtain ⟨rfl, rfl⟩ := E1
    obtain ⟨rfl, rfl⟩ := E2
    cases Hx with
    | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 z' hcond =>
      cases F1 <;> cases F2 <;> first
        | (exfalso; revert hcond; decide)
        | exact ⟨numtype.F64, numtype.F32, rfl, rfl⟩
    | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 hcond =>
      exact absurd Hz (by simp [zeroop_of])
```

Notes: Rocq `vcvtop_cases_full`. Lean: invert `wf_vcvtop__`; for constructors 0/1 `zeroop_of = none` contradicts `Hz`; for 2/3 `injection` of the shape equations (`simp only [shape.X.injEq, dim.mk_dim.injEq]`), invert the inner wf (3-slot / 1-slot / 2-slot binders), `subst` the `zeroop_of` equation, `cases z`, split `Fnn`/`Jnn`, then per combination: `Hts` false (F32 -> I16 TRUNC_SAT), or the generated size side-condition `hcond` is decidably false (`exfalso; revert hcond; decide`), or the goal is the witness `⟨F64, I32⟩` / `⟨F64, F32⟩`. IMPORTANT: inside `first | .. | ..` use `(simp [..] at Hts; done)` and `(exfalso; revert hcond; decide)`; a nested `exact absurd _ (by simp ..)` that leaves a goal only LOGS an error (no backtracking). Axioms: propext only.

### `vcvtop_full_lsize` : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro Hop Hts Hh Hz
  cases Hop with
  | vcvtop___case_0 J1 M1' J2 M2' x Hx E1 E2 =>
    exact absurd Hh (by simp [halfop_of])
  | vcvtop___case_1 J1 M1' F2 M2' x Hx E1 E2 =>
    simp only [shape.X.injEq, dim.mk_dim.injEq] at E1 E2
    obtain ⟨rfl, rfl⟩ := E1
    obtain ⟨rfl, rfl⟩ := E2
    cases Hx with
    | vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 ho sx hcond =>
      simp only [halfop_of] at Hh
      subst Hh
      cases J1 <;> cases F2 <;> first
        | rfl
        | exact absurd hcond (by decide)
  | vcvtop___case_2 F1 M1' J2 M2' x Hx E1 E2 =>
    simp only [shape.X.injEq, dim.mk_dim.injEq] at E1 E2
    obtain ⟨rfl, rfl⟩ := E1
    obtain ⟨rfl, rfl⟩ := E2
    cases Hx with
    | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 sx zo hcond =>
      simp only [zeroop_of] at Hz
      subst Hz
      cases F1 <;> cases J2 <;> first
        | rfl
        | exact absurd hcond (by decide)
  | vcvtop___case_3 F1 M1' F2 M2' x Hx E1 E2 =>
    cases Hx with
    | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 z' hcond =>
      exact absurd Hz (by simp [zeroop_of])
    | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 hcond =>
      exact absurd Hh (by simp [halfop_of])
```

Notes: Same scheme: constructor 0 contradicts `halfop_of op = none`; 1 (CONVERT, `ho = none` after subst) and 2 (TRUNC_SAT, `zo = none`) split the lane pair and close by `rfl` (equal sizes) or by deciding `hcond` false; 3 (DEMOTE/PROMOTELOW) contradicts `Hz`/`Hh`. Axioms: propext only.

### `vload_shape64_wf` : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  refine wf_vloadop_.vloadop__case_0 _ _ _ _ (wf_sz.sz_case_0 64 (by decide)) ?_
  norm_num [proj_sz_0, vsize]
```

Notes: `wf_vloadop_.vloadop__case_0` with `wf_sz.sz_case_0 64 (by decide)` and the `Rat` equation `64 * 1 = 128 / 2` by `norm_num [proj_sz_0, vsize]`. Axioms: propext, Classical.choice, Quot.sound (Mathlib `norm_num`).

### `vload_shape64_stuck` : proved

Still-`sorry` earlier lemmas relied on: none (uses TypePreservation's proved `rat_to_nat_natCast`, imported).

```lean
  intro Hb H
  have key : ∀ (vs : List val) (a b x : admininstr), [a, b] = Map admininstr_val vs ++ [x] → b = x := by
    intro vs a b x h
    rcases vs with _ | ⟨v, _ | ⟨v', vs'⟩⟩
    · simp [Map] at h
    · simp [Map] at h
      exact h.2
    · simp [Map] at h
  generalize hc : config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 i),
        admininstr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz 64) 1 sx)) ao] = c at H
  cases H
  all_goals try (simp at hc; done)
  all_goals try (injection hc with h1 h2; exact absurd (key _ _ _ _ h2) (by simp))
  case vload_shape_oob =>
    simp only [config.mk_config.injEq, List.cons.injEq, admininstr.CONST.injEq, admininstr.VLOAD.injEq,
      Option.some.injEq, vloadop_.SHAPEX_.injEq, sz.mk_sz.injEq, true_and, and_true] at hc
    obtain ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    rename_i _ _ Hgt
    have h8 : rat_to_nat (((64 : Nat) : Rat) * ((1 : Nat) : Rat) / (8 : Rat)) = 8 := by
      have : (((64 : Nat) : Rat) * ((1 : Nat) : Rat) / (8 : Rat)) = ((8 : Nat) : Rat) := by norm_num
      rw [this, rat_to_nat_natCast]
    rw [h8] at Hgt
    simp only [proj_num__0, Option.get!_some] at Hgt
    omega
  case vload_shape_val =>
    simp only [config.mk_config.injEq, List.cons.injEq, admininstr.CONST.injEq, admininstr.VLOAD.injEq,
      Option.some.injEq, vloadop_.SHAPEX_.injEq, sz.mk_sz.injEq, true_and, and_true] at hc
    obtain ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hc
    rename_i _ _ J _ h1 _ _ _ _ _ _
    cases J <;> exact absurd h1 (by decide)
```

Notes: Rocq `inversion H`. Lean: a direct `cases H` would fail ("dependent elimination") on the rules whose left side is `Map admininstr_val vs ++ [..]` (block/loop/call_addr), so first `generalize hc : config.mk_config z [..] = c at H`, then `cases H` and per rule: `simp at hc` closes all rules with a different head instruction / list length; block/loop/call_addr closed by the local lemma `key` (`[a, b] = Map admininstr_val vs ++ [x] -> b = x`, via `rcases vs`); `vload_shape_oob`: `simp only [..injEq..]` + `obtain ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩`, `rat_to_nat (64 * 1 / 8) = 8` by `norm_num` + `rat_to_nat_natCast`, then `omega` against `Hb`; `vload_shape_val`: `jsize J = 64 * 2` false for each `Jnn` by `decide`. NOTE: after the `obtain`s the order of the remaining inaccessible hypotheses is not the constructor's order (premises independent of the substituted variables come first), hence `rename_i _ _ Hgt` / `rename_i _ _ J _ h1 _ _ _ _ _ _`. Axioms: propext, Classical.choice, Quot.sound.

## Final Lean check (merge simulation of the whole TypeProgress.lean)
Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/TypeProgressH14.lean` -> 0 errors. `#print axioms` lines (appended to the scratch copy):
```
'TLC.setproduct1_Forall' depends on axioms: [propext, sorryAx]
'TLC.setproduct_Forall' depends on axioms: [propext, sorryAx]
'TLC.setproduct_nonempty' depends on axioms: [propext]
'TLC.setproduct_pick' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.halfop_total' depends on axioms: [propext]
'TLC.zeroop_total' depends on axioms: [propext]
'TLC.zero_lane_wf' depends on axioms: [propext, sorryAx]
'TLC.vcvtop_step_full' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.vcvtop_step_half' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.vcvtop_step_zero' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.vcvtop_zero_numtype' depends on axioms: [propext]
'TLC.vcvtop_full_lsize' depends on axioms: [propext]
'TLC.vload_shape64_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.vload_shape64_stuck' depends on axioms: [propext, Classical.choice, Quot.sound]
real	0m3.005s
user	0m3.819s
sys	0m1.406s
```

`sorryAx` in the list above is inherited only from earlier still-`sorry` lemmas (`setproduct2_Forall`, `packnum_not_none`, `vcvtop_lanes_total`, `Forall_list_slice`, and wasm2.0's own `lanes__is_wf`), never from the 14 bodies themselves.

## Safety check at END
Run after all Lean work and after this log was written (the first END run, check-20261005T131310.938149528Z, also printed `VERIFIED`):
```
safety check [prove-H14] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T131419.195725904Z-prove-H14-1491033.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

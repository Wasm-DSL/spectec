# prove-C08 log (bundle20 progress port, proof batch C08)

Agent: prove-C08. Scratch: /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C08/Work.lean

Wrote only: this log + scratch dir. No repo file edited (TypeProgress.lean untouched), no git state changes, no agents spawned, no `lake build`; one Lean process (`lake env lean Work.lean`) at a time.

## Safety check at START

```
safety check [prove-C08] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T132247.096771055Z-prove-C08-1496363.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method

Work.lean = `import TypeProgress` + `namespace TLC` + each target's header copied verbatim (renamed `<name>_proof`) + `example : type_of% @<name>_proof = type_of% @<name> := rfl` guard. Proofs imitate the Rocq bullets of `t_progress_be` (intro, `unfold t_progress_be_P`, Rocq's `move => s f C' vcs ...` names, inline `invert_typeof_vcs` as in prove-C06: `simp only [mkFunctype, ...] at Htf`, `rcases vcs`, canonical forms, then `Step.pure` with the generated `Step_pure` rule). Ordering rule checked: every TypeProgress lemma used is at a line < 1870.

## Results (all 3 proved)

### t_progress_be_vrelop — proved

- Location: TypeProgress.lean:1870; Rocq type_progress.v:3852-3867
- Still-sorry earlier lemmas / imported facts used: invert_typeof_V128 (TypeProgress.lean:241), vrelop_some (TypeProgress.lean:1075)
- Axioms: no new axioms; no sorry/admit/native_decide in the proof text.
- Notes: Direct port of the Rocq bullet: canonical forms for the two V128 operands (invert_typeof_V128), wf_shape / wf_vrelop_ from `cases HWfinstr`, `vrelop_some` gives `r` with `fun_vrelop_ sh op c1 c2 (some r)`, then `Step.pure` + `Step_pure.vrelop c1 c2 sh vrelop r (some r) Hr (Option.some_ne_none r) rfl`. No axioms beyond those of the used lemmas.
- Body (goes after `:= by`):

```lean
  intro C sh vrelop HWfC HWfinstr
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
    have Hwfsh : wf_shape sh := by cases HWfinstr; assumption
    have Hwfop : wf_vrelop_ sh vrelop := by cases HWfinstr; assumption
    obtain ⟨r, Hr⟩ := vrelop_some sh vrelop c1 c2 Hwfsh Hwfop Hwf1 Hwf2
    refine ⟨s, f, [admininstr.VCONST vectype.V128 r], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1, Heqv2]
    exact Step.pure _ _ _ (Step_pure.vrelop c1 c2 sh vrelop r (some r) Hr (Option.some_ne_none r) rfl)
  · simp at Hts
```

### t_progress_be_vshiftop — proved

- Location: TypeProgress.lean:1880; Rocq type_progress.v:3867-3917
- Still-sorry earlier lemmas / imported facts used: invert_typeof_V128 (241), invert_typeof_I32_wf (1163), wf_lane_Jnn_inv (814), wf_lane_Jnn_some (820), Forall2_map_l (1157); imported: lanes__is_wf (wasm2.0.lean:4651, generated well-formedness theorem, body sorry in wasm2.0.lean)
- Axioms: no new axioms; no sorry/admit/native_decide in the proof text.
- Notes: Follows Rocq: invert wf_vshiftop_ (`obtain ⟨J, M, o, Hsh⟩` -- v_ishape is an auto-promoted parameter so it takes no slot) and `subst`; `Hwsh` from `cases Hwish` (instead of Rocq's wf_ishape_inv + J'=J/M'=M injectivity step; same content, avoids subst-direction ambiguity); `Hl := lanes__is_wf`; `Hlx` via wf_lane_Jnn_inv/wf_lane_Jnn_some; `cases o` (SHL / SHR sx) and apply `Step_pure.vshiftop` with Rocq's explicit lane lists (`List.map (fun l => some (mk_lane__0 J (ishl_/ishr_ ...)))`). Side goals: length by `simp`; Forall2 via `Forall2_map_l` then `cases J` + explicit `fun_vshiftop__case_0..3` (SHL) / `_case_4..7` (SHR) with `rfl`; `≠ none` by `Option.some_ne_none`; inv_lanes_ equation by `simp only [Map, List.map_map]; rfl`.
- Body (goes after `:= by`):

```lean
  intro C sh op HWfC HWfinstr
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
    obtain ⟨k, Heqv2, Hwfk⟩ := invert_typeof_I32_wf v2 Ht2 HP0
    have Hwish : wf_ishape sh := by cases HWfinstr; assumption
    have Hwop : wf_vshiftop_ sh op := by cases HWfinstr; assumption
    obtain ⟨J, M, o, Hsh⟩ := Hwop
    subst Hsh
    have Hwsh : wf_shape (shape.X (lanetype_Jnn J) (dim.mk_dim M)) := by cases Hwish; assumption
    have Hl := lanes__is_wf _ _ _ Hwsh Hwf1 rfl
    have Hlx : Forall (fun l => ∃ x, l = lane_.mk_lane__0 J x ∧ wf_uN (lsize (lanetype_Jnn J)) x)
        (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1) := by
      intro l hl
      exact wf_lane_Jnn_inv J l (Hl l hl) (wf_lane_Jnn_some J l (Hl l hl))
    cases o with
    | SHL =>
      refine ⟨s, f, [admininstr.VCONST vectype.V128 (inv_lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M))
        (List.map (fun l => lane_.mk_lane__0 J (ishl_ (lsizenn (lanetype_Jnn J)) (Option.get! (proj_lane__0 l)) (uN.mk_uN k)))
          (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Heqv1, Heqv2]
      refine Step.pure _ _ _ (Step_pure.vshiftop c1 k J M _ _ (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)
        (List.map (fun l => some (lane_.mk_lane__0 J (ishl_ (lsizenn (lanetype_Jnn J)) (Option.get! (proj_lane__0 l)) (uN.mk_uN k))))
          (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)) ?_ ?_ rfl ?_ ?_ Hl Hwsh Hwish Hwfk)
      · simp
      · apply Forall2_map_l
        intro l hl
        obtain ⟨x, rfl, _⟩ := Hlx l hl
        cases J
        · exact fun_vshiftop_.fun_vshiftop__case_0 M x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_1 M x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_2 M x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_3 M x k M rfl
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨l, _, rfl⟩ := ho
        exact Option.some_ne_none _
      · simp only [Map, List.map_map]
        rfl
    | SHR v_sx =>
      refine ⟨s, f, [admininstr.VCONST vectype.V128 (inv_lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M))
        (List.map (fun l => lane_.mk_lane__0 J (ishr_ (lsizenn (lanetype_Jnn J)) v_sx (Option.get! (proj_lane__0 l)) (uN.mk_uN k)))
          (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)))], ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [Heqv1, Heqv2]
      refine Step.pure _ _ _ (Step_pure.vshiftop c1 k J M _ _ (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)
        (List.map (fun l => some (lane_.mk_lane__0 J (ishr_ (lsizenn (lanetype_Jnn J)) v_sx (Option.get! (proj_lane__0 l)) (uN.mk_uN k))))
          (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)) ?_ ?_ rfl ?_ ?_ Hl Hwsh Hwish Hwfk)
      · simp
      · apply Forall2_map_l
        intro l hl
        obtain ⟨x, rfl, _⟩ := Hlx l hl
        cases J
        · exact fun_vshiftop_.fun_vshiftop__case_4 M v_sx x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_5 M v_sx x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_6 M v_sx x k M rfl
        · exact fun_vshiftop_.fun_vshiftop__case_7 M v_sx x k M rfl
      · intro o ho
        simp only [List.mem_map] at ho
        obtain ⟨l, _, rfl⟩ := ho
        exact Option.some_ne_none _
      · simp only [Map, List.map_map]
        rfl
  · simp at Hts
```

### t_progress_be_vbitmask — proved

- Location: TypeProgress.lean:1890; Rocq type_progress.v:3917-3963
- Still-sorry earlier lemmas / imported facts used: invert_typeof_V128 (241), wf_ishape_inv (1190), lanes_Jnn_form (942), Forall_exists_Forall2 (800), icmp_total_bit (1039), bit_of_wf1 (1181), jlane_some (953); imported: lanes_len (HelperLemmas.lean:785, axiom = Rocq axioms.v lanes_len), ibits_inv (HelperLemmas.lean:821, axiom = Rocq axioms.v:64), inv_ibits__is_wf (wasm2.0.lean:4239, generated well-formedness theorem, body sorry in wasm2.0.lean)
- Axioms: no new axioms; no sorry/admit/native_decide in the proof text.
- Notes: Follows Rocq: wf_ishape_inv + `subst`; HL := lanes_Jnn_form; Hz0 directly by `wf_uN.uN_case_0 _ 0 ⟨Nat.zero_le _, Nat.zero_le _⟩` (Lean Nat makes Rocq's two_pow_pos/Zsub1_toN step unnecessary); vs from Forall_exists_Forall2 + icmp_total_bit(.1) + bit_of_wf1 -- its length conjunct replaces Rocq's (not ported) Forall2_size_eq; `bits` introduced as `obtain ⟨bits, Hbits⟩ : ∃ bits, bits = Map ... ++ List.replicate (Int.toNat (32 - M)) (bit.mk_bit 0)` (Rocq `pose bits`); Hbw/Hbl as in Rocq (Hbl uses lanes_len and HM : M ≤ 16). Pitfall hit: omega ignores `HM : @LE.le N instLENat M 16` (type argument is the abbrev `N`, not `Nat`), so it is restated as `have HM' : @LE.le Nat instLENat M 16 := HM` before `omega`. Then `Step_pure.vbitmask c1 J M (inv_ibits_ 32 bits) (lanes_ ...) vs` with premises Hsvs, jlane_some, H2, rfl, `(ibits_inv 32 bits Hbl Hbw).trans Hbits`, `inv_ibits__is_wf 32 bits _ Hbw rfl`, Hwsh, Hb, `wf_bit.bit_case_0 0 (Or.inl rfl)`.
- Body (goes after `:= by`):

```lean
  intro C sh HWfC HWfinstr
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
    obtain ⟨c1, Heqv1, Hwf1⟩ := invert_typeof_V128 v1 Ht1 HP
    have Hwish : wf_ishape sh := by cases HWfinstr; assumption
    obtain ⟨J, M, Hsh, Hwsh, HM⟩ := wf_ishape_inv _ Hwish
    subst Hsh
    have HL := lanes_Jnn_form J M c1 Hwsh Hwf1
    have Hz0 : wf_uN (lsize (lanetype_Jnn J)) (uN.mk_uN 0) :=
      wf_uN.uN_case_0 _ 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
    obtain ⟨vs, ⟨H2, Hsvs⟩, Hb⟩ := Forall_exists_Forall2 uN lane_
      (fun v l => fun_ilt_ (lsize (lanetype_Jnn J)) sx.S (Option.get! (proj_lane__0 l)) (uN.mk_uN 0) v)
      (fun v => wf_bit (bit.mk_bit (proj_uN_0 v)))
      (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1)
      (by
        intro l hl
        obtain ⟨x, rfl, Hx⟩ := HL l hl
        obtain ⟨r, Hr, Hrb⟩ := (icmp_total_bit _ sx.S x (uN.mk_uN 0) Hx Hz0).1
        exact ⟨r, Hr, bit_of_wf1 _ Hrb⟩)
    have HlenM : (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1).length = M := lanes_len _ _ _
    obtain ⟨bits, Hbits⟩ : ∃ bits : List bit, bits =
        Map (fun (v : uN) => bit.mk_bit (proj_uN_0 v)) vs ++
          List.replicate (Int.toNat ((32 : Int) - (M : Int))) (bit.mk_bit 0) := ⟨_, rfl⟩
    have Hbw : Forall (fun b => wf_bit b) bits := by
      intro b hb
      rw [Hbits] at hb
      rcases List.mem_append.1 hb with hb | hb
      · simp only [Map, List.mem_map] at hb
        obtain ⟨v, hv, rfl⟩ := hb
        exact Hb v hv
      · rw [List.eq_of_mem_replicate hb]
        exact wf_bit.bit_case_0 0 (Or.inl rfl)
    have Hbl : bits.length = 32 := by
      rw [Hbits]
      simp only [Map, List.length_append, List.length_map, List.length_replicate]
      have HM' : @LE.le Nat instLENat M 16 := HM
      have Hsvs' : vs.length = (M : Nat) := Hsvs.trans HlenM
      rw [Hsvs']
      omega
    refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (irev_ 32 (inv_ibits_ 32 bits)))], ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [Heqv1]
    exact Step.pure _ _ _ (Step_pure.vbitmask c1 J M (inv_ibits_ 32 bits)
      (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) c1) vs
      Hsvs (jlane_some J _ HL) H2 rfl ((ibits_inv 32 bits Hbl Hbw).trans Hbits)
      (inv_ibits__is_wf 32 bits _ Hbw rfl) Hwsh Hb (wf_bit.bit_case_0 0 (Or.inl rfl)))
  · simp at Hts
```

## Final Lean check output

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/Work.lean`: exit=0, output empty (0 bytes: no errors, no warnings; all 3 rfl guards pass).

Intermediate errors fixed on the way: (1) `obtain ⟨_, J, M, o, Hsh⟩ := Hwop` -> `Unknown identifier Hsh` (wf_vshiftop_'s v_ishape is an auto-promoted parameter, no slot) -> `⟨J, M, o, Hsh⟩`; (2) `omega` failed on `M + (32 - ↑M).toNat = 32` because `HM : M ≤ 16` is stated at type `N` (abbrev) which omega does not pick up -> restated at `Nat`.

## Safety check at END

```
safety check [prove-C08] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T133026.972314375Z-prove-C08-1500795.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

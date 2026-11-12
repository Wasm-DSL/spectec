# prove-H05 log (bundle20 progress port, proof batch H05)

Agent: prove-H05. Target file: spectec/src/test-lean-claude/TypeProgress.lean (NOT edited; the main thread merges). Work scratch: /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H05/ (Work.lean, Work2.lean, SpliceCheck.lean, bodies.json).

## Safety checks

Start (run from /home/zhengyew/spectec, `bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-H05`):

```
safety check [prove-H05] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T122446.300605905Z-prove-H05-1450525.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

End (same command, after all Lean runs):

```
safety check [prove-H05] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T123159.539373813Z-prove-H05-1455479.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written by this agent: only this log and files in its scratch dir. No repo file edited, no git state change, no `lake build`, no agents spawned; one Lean process at a time.

## Results (7 targets, all `proved`)

Verification: every `_proof` theorem copies the real header verbatim and carries the guard `example : type_of% @X_proof = type_of% @X := rfl` (all pass). Additionally a full spliced copy of TypeProgress.lean (the 7 `:= sorry` bodies replaced by the proofs below, in place) compiles (exit 0, no errors, none of the 7 theorems reported as `declaration uses sorry`). Axioms (`#print axioms`): propext, Classical.choice, Quot.sound, plus `sorryAx` only through the earlier still-sorry TypeProgress lemmas listed per target (checked with a transitive-closure script over project constants: no other project constant reached contains sorry). `size_eq1_cat` depends only on `propext`.

### `s_typing_lf_br`

Status: proved. Still-sorry earlier lemmas relied on: frame_t_context_label_empty (TypeProgress.lean:398, still sorry).

Proof body (tactic block after `:= by`, exactly as compiled):

```lean
  intro Hframe
  induction es generalizing t1s t2s with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons a es ih =>
    intro Hadmin e he
    obtain ⟨t3s, HType1, HType2⟩ := ais_seq_typing_inversion s _ es a t1s t2s Hadmin
    rcases List.mem_cons.mp he with rfl | he'
    · intro Hbr
      subst Hbr
      have h1 := revert_to_instr_from_ai s _ (instr.BR l) t1s t3s HType2
      obtain ⟨t1s_sup, t2s_sub, HType2', HSub⟩ := instrs_single_typing_inversion _ (instr.BR l) t1s t3s h1
      have Hlab := frame_t_context_label_empty s f C Hframe
      cases HType2'
      rename_i _ _ _ _ hlt _
      have : (prepend_return C rt).LABELS = [] := by
        show ([] : List resulttype) ++ C.LABELS = []
        rw [Hlab]; rfl
      rw [this] at hlt
      simp at hlt
    · exact ih t3s t2s HType1 e he'
```

Notes: Rocq proof ported 1:1: induction on es; head: ais_seq_typing_inversion, revert_to_instr_from_ai, instrs_single_typing_inversion, invert Instr_ok.br; (prepend_return C rt).LABELS = [] ++ C.LABELS = [] via frame_t_context_label_empty (a `show` of the definitional unfolding of `++` on contexts), so `l < 0`. `cases` on `Instr_ok` works directly (no dependent-elimination problem); constructor hypotheses are anonymous so `rename_i _ _ _ _ hlt _` names the `proj_uN_0 l < labels.length` premise.

### `s_typing_lf_return`

Status: proved. Still-sorry earlier lemmas relied on: frame_t_context_return_empty (TypeProgress.lean:432, still sorry).

Proof body (tactic block after `:= by`, exactly as compiled):

```lean
  intro Hframe
  induction es generalizing t1s t2s with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons a es ih =>
    intro Hadmin e he
    obtain ⟨t3s, HType1, HType2⟩ := ais_seq_typing_inversion s _ es a t1s t2s Hadmin
    rcases List.mem_cons.mp he with rfl | he'
    · intro Hret
      subst Hret
      have h1 := revert_to_instr_from_ai s _ instr.RETURN t1s t3s HType2
      obtain ⟨t1s_sup, t2s_sub, HType2', HSub⟩ := instrs_single_typing_inversion _ instr.RETURN t1s t3s h1
      have Hr := frame_t_context_return_empty s f C Hframe
      cases HType2'
      rename_i _ _ _ hret _
      rw [Hr] at hret
      cases hret
    · exact ih t3s t2s HType1 e he'
```

Notes: Same shape as lf_br; Instr_ok.return gives C.RETURN = some _, contradicting frame_t_context_return_empty (C.RETURN = none). `rename_i _ _ _ hret _` names that premise (constructor hypotheses come out in the order t_1, t_lst, wf_instr, RETURN-premise, wf_context).

### `s_typing_not_lf_br'`

Status: proved. Still-sorry earlier lemmas relied on: s_typing_lf_br' (TypeProgress.lean:~467, still sorry; not in this batch).

Proof body (tactic block after `:= by`, exactly as compiled):

```lean
  intro Hframe Hadmin vcs l es' Hcontra
  have Hes := s_typing_lf_br' s f C es t1s t2s l Hframe Hadmin
  clear Hframe Hadmin
  induction vcs generalizing es with
  | nil =>
    simp only [List.map_nil, List.nil_append] at Hcontra
    subst Hcontra
    exact Hes (admininstr.BR l) (List.mem_cons_self) rfl
  | cons v vcs ih =>
    cases es with
    | nil => simp at Hcontra
    | cons e es0 =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at Hcontra
      exact ih es0 Hcontra.2 (fun x hx => Hes x (List.mem_cons_of_mem _ hx))
```

Notes: Rocq proof ported: from Forall (e <> BR l) es get a contradiction with es = map admininstr_val vcs ++ ([BR l] ++ es') by induction on vcs generalizing es. NOTE for the induction: `Hes` and `Hcontra` both depend on `es` so `ih` takes (Hcontra-type) then (Hes-type) in that order.

### `s_typing_not_lf_br`

Status: proved. Still-sorry earlier lemmas relied on: s_typing_lf_br (TypeProgress.lean:474; proved in this batch, #1).

Proof body (tactic block after `:= by`, exactly as compiled):

```lean
  intro Hframe Hadmin vcs l es' Hcontra
  have Hes := s_typing_lf_br s f C rt es t1s t2s l Hframe Hadmin
  clear Hframe Hadmin
  induction vcs generalizing es with
  | nil =>
    simp only [List.map_nil, List.nil_append] at Hcontra
    subst Hcontra
    exact Hes (admininstr.BR l) (List.mem_cons_self) rfl
  | cons v vcs ih =>
    cases es with
    | nil => simp at Hcontra
    | cons e es0 =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at Hcontra
      exact ih es0 Hcontra.2 (fun x hx => Hes x (List.mem_cons_of_mem _ hx))
```

Notes: Identical to s_typing_not_lf_br' but using s_typing_lf_br (with the prepended-return context).

### `s_typing_not_lf_return`

Status: proved. Still-sorry earlier lemmas relied on: s_typing_lf_return (TypeProgress.lean:482; proved in this batch, #2).

Proof body (tactic block after `:= by`, exactly as compiled):

```lean
  intro Hframe Hadmin vcs es' Hcontra
  have Hes := s_typing_lf_return s f C es t1s t2s Hframe Hadmin
  clear Hframe Hadmin
  induction vcs generalizing es with
  | nil =>
    simp only [List.map_nil, List.nil_append] at Hcontra
    subst Hcontra
    exact Hes admininstr.RETURN (List.mem_cons_self) rfl
  | cons v vcs ih =>
    cases es with
    | nil => simp at Hcontra
    | cons e es0 =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at Hcontra
      exact ih es0 Hcontra.2 (fun x hx => Hes x (List.mem_cons_of_mem _ hx))
```

Notes: Identical shape for RETURN: es = map admininstr_val vcs ++ ([RETURN] ++ es').

### `size_eq1_cat`

Status: proved. Still-sorry earlier lemmas relied on: none.

Proof body (tactic block after `:= by`, exactly as compiled):

```lean
  intro Hsize Hcat
  exact List.append_inj Hcat Hsize
```

Notes: One line: core `List.append_inj` (s1 ++ t1 = s2 ++ t2 -> |s1| = |s2| -> s1 = s2 /\ t1 = t2). Only axiom: propext. Rocq's take/drop argument is not needed.

### `br_reduce_extract_vs`

Status: proved. Still-sorry earlier lemmas relied on: Admin_instrs_ok_cat (TypeProgress.lean:~459, still sorry; not in this batch); size_eq1_cat (TypeProgress.lean:515; proved in this batch, #6).

Proof body (tactic block after `:= by`, exactly as compiled):

```lean
  intro Hbr Hadmin Hlookup
  obtain ⟨vcs, es', Hbr⟩ := Hbr
  have Hadmin' := Hadmin
  rw [Hbr, ← List.append_assoc] at Hadmin'
  obtain ⟨ta, tb, tc, ts3, Ets1, Ets2, Hadmin1, Hadmin2⟩ :=
    Admin_instrs_ok_cat s C _ es' [] ts2 Hadmin'
  obtain ⟨Ets', Ets1'⟩ := List.append_eq_nil_iff.mp Ets1.symm
  subst Ets' Ets1'
  obtain ⟨td, te, tf, ts3', Ets1, Ets2', Hadmin1, Hadmin1'⟩ :=
    Admin_instrs_ok_cat s C _ [admininstr.BR (uN.mk_uN 0)] [] ts3 Hadmin1
  obtain ⟨Ets'', Ets1''⟩ := List.append_eq_nil_iff.mp Ets1.symm
  subst Ets'' Ets1''
  obtain ⟨t, Hsub, HValsok⟩ := ais_vals_typing_inversion s C vcs [] ts3' Hadmin1
  obtain ⟨t1', t2', Hai, Hsub0⟩ :=
    ais_single_typing_inversion s C (admininstr.BR (uN.mk_uN 0)) ts3' tf Hadmin1'
  unfold ai_principal_typing at Hai
  obtain ⟨t1s_, lab, t2s_, Hft, Hlab⟩ := Hai
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Hft
  obtain ⟨rfl, rfl⟩ := Hft
  have Hlab' : C.LABELS[0]? = some (list.mk_list lab) := Hlab
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp Hlab'
  have Hlab'' : C.LABELS[0]! = list.mk_list lab := by rw [getElem!_pos C.LABELS 0 hk]; exact he
  rw [Hlab''] at Hlookup
  subst Hlookup
  have Hsubr : ResulttypeSub t ts3' := (instrtype_sub_iff_resulttype_sub t ts3' []).mpr Hsub
  have Hnonbot := Vals_ok_non_bot s vcs t HValsok
  have Ht : t = ts3' := resulttype_sub_non_bot t ts3' Hnonbot Hsubr
  subst Ht
  obtain ⟨tsa, tsb, ts11_sub, ts12_sup, E1, E2, Hs1, Hs2, Hs3⟩ := Hsub0
  subst E1
  have Hs12 := resulttype_sub_app tsa ts11_sub tsb (t1s_ ++ lab) Hs1 Hs2
  have Heq := resulttype_sub_non_bot _ _ Hnonbot Hs12
  have Hlen : tsa.length = tsb.length := by
    cases Hs1 with
    | mk_Resulttype_sub _ _ hlen _ => exact hlen
  obtain ⟨Hts, H2⟩ := size_eq1_cat valtype ts11_sub (t1s_ ++ lab) tsa tsb Hlen Heq
  subst Hts H2
  have Hlenv := HValsok.1
  refine ⟨vcs.take (tsa ++ t1s_).length, vcs.drop (tsa ++ t1s_).length, es', ?_, ?_⟩
  · rw [Hbr]
    simp only [← List.append_assoc, ← List.map_append, List.take_append_drop]
  · show (vcs.drop (tsa ++ t1s_).length).length = lab.length
    simp only [List.length_drop, List.length_append] at Hlenv ⊢
    omega
```

Notes: Ported following the Rocq proof: rewrite es, Admin_instrs_ok_cat twice (cat_nil replaced by core `List.append_eq_nil_iff` so no extra sorry'd dependency), ais_vals_typing_inversion on the values (= Rocq invert_ais_vals_typing), ais_single_typing_inversion + `unfold ai_principal_typing` on BR 0 (= Rocq invert_ais_single_typing + resolve_all_pt; Lean's BR case is `exists t1s ts t2s, ft = mkFunctype (t1s ++ ts) t2s /\ C.LABELS[l]? = some (mk_list ts)`), instrtype_sub_iff_resulttype_sub, Vals_ok_non_bot, resulttype_sub_non_bot, resulttype_sub_app, size_eq1_cat, then split vcs at (tsa ++ t1s_).length with take/drop and finish by omega on lengths (Vals_ok carries the length). The `getElem?`-to-`getElem!` step uses core `List.getElem?_eq_some_iff` + `getElem!_pos` (the content of TypePreservation's `getElem?_eq_some_bang`, restated inline so the proof does not depend on TypePreservation).

## Final Lean check output

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/Work.lean`: no output, exit 0 (all 7 theorems and 7 guards elaborate).

`... lake env lean <scratch>/SpliceCheck.lean` (full TypeProgress.lean with the 7 bodies spliced in): exit 0; only `declaration uses sorry` warnings for the other (not yet proved) lemmas, none for the 7 targets (lines 474-640 of the spliced file are warning-free).

`... lake env lean <scratch>/Work2.lean` (Work.lean + dependency/axiom report), relevant output:

```
s_typing_lf_br_proof: sorry-containing project constants reached: [TLC.frame_t_context_label_empty]
s_typing_lf_return_proof: sorry-containing project constants reached: [TLC.frame_t_context_return_empty]
s_typing_not_lf_br'_proof: sorry-containing project constants reached: [TLC.s_typing_lf_br']
s_typing_not_lf_br_proof: sorry-containing project constants reached: [TLC.s_typing_lf_br]
s_typing_not_lf_return_proof: sorry-containing project constants reached: [TLC.s_typing_lf_return]
size_eq1_cat_proof: sorry-containing project constants reached: []
br_reduce_extract_vs_proof: sorry-containing project constants reached: [TLC.Admin_instrs_ok_cat, TLC.size_eq1_cat]
'TLC.size_eq1_cat_proof' depends on axioms: [propext]
(others: [propext, sorryAx, Classical.choice, Quot.sound], sorryAx only via the lemmas above)
```

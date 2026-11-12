# prove-H06 (bundle20 progress port, proof batch H06)

Targets (14, TypeProgress.lean:540-738 in the unmodified file): `return_reduce_extract_vs`, `lookup_types`, `funcs_size`, `admininstr_CONST_eq_arg`, `typeof_non_bot`, `typeof_vals_non_bot`, `unop_not_none`, `two_pow_pos`, `Zsub1_toN`, `wf_uN_lt`, `two_pow_succ`, `signed_total`, `invsigned_total`, `Zquot_abs_le`. ALL 14 PROVED.

No repo file was edited (TypeProgress.lean mtime 20:18:16, before this session started). Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H06/` (`Work.lean` = final proofs + guards; `t/TypeProgressMerged.lean` = merge simulation; `t/Neg.lean` = negative control). Only my own log file was written inside the target dir (plus the safety-check output files the check script itself creates).

## Safety check at START
```
safety check [prove-H06] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T123020.722176558Z-prove-H06-1454291.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- `Work.lean` (scratch): the header of every target copied verbatim from TypeProgress.lean, theorem renamed `<name>_proof`, plus the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl`. Negative control (`t/Neg.lean`: a changed statement against the same guard) correctly FAILS with `Type mismatch rfl`, so the guard is live.
- Merge simulation (`t/TypeProgressMerged.lean`): a copy of the real TypeProgress.lean (2690 lines) in which the 14 `:= sorry` are replaced by `:= by` + the exact tactic blocks below, compiled standalone with `lake env lean` against the same imports: exit 0, ZERO errors, 266 remaining `declaration uses sorry` warnings (the other lemmas), none located at the 14 target lines (lines 540, 584, 600, 610, 617, 628, 639, 663, 670, 674, 685, 694, 720, 738 OF THE MERGED COPY, whose line numbers shift once the earlier blocks are inserted; the headings below use the line numbers of the unmodified TypeProgress.lean). So the blocks drop into the real file unchanged and respect the ordering rule.
- Ordering rule: TypeProgress lemmas used are only `typeof_non_bot` (by `typeof_vals_non_bot`) and `two_pow_succ` (by `signed_total`), both earlier in the file and proved in this very batch. Everything else comes from imports (TypingLemmas `ais_composition_typing`, `ais_seq_typing_inversion`, `ais_vals_typing_inversion`, `ais_single_typing_inversion`; Subtyping `resulttype_sub_size_eq`, `instrtype_sub_iff_resulttype_sub`; TypePreservation `Moduleinst_ok_lengths`; Lean core/Mathlib). The file has no `open`/`set_option`/`variable`, so the elaboration context of the real file equals that of `Work.lean`.
- One Lean process at a time, `lake env lean` only (never `lake build`, nothing written to `.lake/`).
- Axioms: no project `axiom` (HelperLemmas' two) used; no `sorry`, `admit`, `native_decide`, new axiom. Only `propext`, `Classical.choice`, `Quot.sound` appear (see the `#print axioms` lines below). `sorryAx` appears only for `typeof_vals_non_bot` and `signed_total`, through the earlier lemmas `typeof_non_bot` / `two_pow_succ` while those are still sorry in the imported TypeProgress olean; with them replaced by my proofs (`t/Work2.lean`) neither depends on sorryAx.

## Results

### `return_reduce_extract_vs` (TypeProgress.lean:540) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hret hadmin hlookup
  obtain ⟨vcs, es', hes⟩ := hret
  subst hes
  obtain ⟨x3, hV, hrest⟩ := ais_composition_typing s C (List.map admininstr_val vcs)
    ([admininstr.RETURN] ++ es') [] ts2 hadmin
  obtain ⟨x4, _, hRET⟩ := ais_seq_typing_inversion s C es' admininstr.RETURN x3 ts2 hrest
  obtain ⟨vts, hsubV, hvok⟩ := ais_vals_typing_inversion s C vcs [] x3 hV
  obtain ⟨u1, u2, hpt, hsubR⟩ := ais_single_typing_inversion s C admininstr.RETURN x3 x4 hRET
  unfold ai_principal_typing at hpt
  obtain ⟨t1s, tsr, t2s, heq, hr, _⟩ := hpt
  unfold mkFunctype at heq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at heq
  obtain ⟨e1, e2⟩ := heq
  rw [e1, e2] at hsubR
  rw [hlookup] at hr
  have ht : t = list.mk_list tsr := Option.some.inj hr
  subst ht
  simp only [proj_list_0]
  obtain ⟨hl1, _⟩ := hvok
  have hl2 := resulttype_sub_size_eq _ _ ((instrtype_sub_iff_resulttype_sub vts x3 []).mpr hsubV)
  obtain ⟨tp1', tp1, ts1', ts2'', h1e1, h1e2, h1s1, h1s2, h1s3⟩ := hsubR
  have hl3 := resulttype_sub_size_eq _ _ h1s2
  have hx3 : x3.length = tp1'.length + ts1'.length := by rw [h1e1]; simp
  simp only [List.length_append] at hl3
  have hlen : tsr.length ≤ vcs.length := by omega
  refine ⟨vcs.take (vcs.length - tsr.length), vcs.drop (vcs.length - tsr.length), es', ?_, ?_⟩
  · rw [← List.append_assoc (List.map admininstr_val (List.take _ vcs)), ← List.map_append,
      List.take_append_drop]
  · simp only [List.length_drop]
    omega
```

Notes: Lean-way proof (not a line-by-line port). Rocq (and `br_reduce_extract_vs`) peels `vals ++ [RETURN] ++ es'` with `Admin_instrs_ok_cat`, then uses non-BOT reasoning (`Vals_ok_non_bot`, `resulttype_sub_non_bot`, `size_eq1_cat`) to identify the split `take/drop (size (ts ++ extr)) vcs`. The statement only needs `|vcs2| = |t|`, and every ingredient (`Vals_ok`, `ResulttypeSub`) carries a length equality, so the Lean proof counts lengths and splits at `|vcs| - |t|`; no BOT reasoning is needed. Steps: `ais_composition_typing` (vals | `[RETURN] ++ es'`), `ais_seq_typing_inversion` (isolate `[RETURN]`), `ais_vals_typing_inversion` (vals typed by `vts` with `Vals_ok`), `ais_single_typing_inversion` + `unfold ai_principal_typing` (RETURN gives `C.RETURN = some (list.mk_list tsr)` and `instrtype_sub (t1s ++ tsr :-> t2s) (x3 :-> x4)`), then lengths via `resulttype_sub_size_eq` / `instrtype_sub_iff_resulttype_sub`. Axioms: propext, Classical.choice, Quot.sound only (no project axiom, no sorryAx).

### `lookup_types` (TypeProgress.lean:554) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro h
  have hT : C.TYPES = f.MODULE.TYPES := by
    generalize f.MODULE = m at h ⊢
    cases h
    rfl
  show C.TYPES[idx]! = f.MODULE.TYPES[idx]!
  rw [hT]
```

Notes: Port of Rocq `inversion HMinst; by rewrite /=`: `generalize f.MODULE = m at h ⊢; cases h; rfl` gives `C.TYPES = f.MODULE.TYPES` (the generated `Moduleinst_ok` constructor builds both the moduleinst and the context from the same `functype_lst`); `upd_local_label_return` only changes LOCALS/LABELS/RETURN so its TYPES is `C.TYPES` definitionally (`show` then `rw`). No sorryAx.

### `funcs_size` (TypeProgress.lean:563) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro h
  show C.FUNCS.length = f.MODULE.FUNCS.length
  exact ((Moduleinst_ok_lengths s f.MODULE C h).2.1).symm
```

Notes: Uses the Lean-only helper `Moduleinst_ok_lengths` (TypePreservation.lean:408, imported by TypeProgress.lean precisely for such helpers); its `.2.1` is `minst.FUNCS.length = C.FUNCS.length`, read off `Moduleinst_ok`'s own `funcaddr_lst.length = functype_F_lst.length` premise. `upd_local_label_return` leaves FUNCS unchanged (definitional `show`). No sorryAx.

### `admininstr_CONST_eq_arg` (TypeProgress.lean:570) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro h
  injection h
```

Notes: `injection` (Rocq `inversion`). Axiom-free.

### `typeof_non_bot` (TypeProgress.lean:575) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  cases v with
  | CONST t _ => cases t <;> simp [typeof, valtype_numtype]
  | VCONST t _ => cases t; simp [typeof, valtype_vectype]
  | REF_NULL t => cases t <;> simp [typeof, valtype_reftype]
  | REF_FUNC_ADDR _ => simp [typeof]
  | REF_HOST_ADDR _ => simp [typeof]
```

Notes: Case analysis on the value and its inner numtype/vectype/reftype, then `simp [typeof, valtype_numtype/vectype/reftype]` (Rocq: `destruct v; rewrite /typeof; discriminate`). `cases t; simp` is used for the single-constructor `vectype` (a `<;>` would trip the unnecessarySeqFocus linter).

### `typeof_vals_non_bot` (TypeProgress.lean:580) : proved

Still-`sorry` earlier lemmas relied on: `typeof_non_bot` (proved in this batch).

```lean
  intro h
  subst h
  intro t ht
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
  exact typeof_non_bot v
```

Notes: Rocq inducts on `vs`; here `subst`, `List.mem_map` and the earlier lemma `typeof_non_bot` (TypeProgress:575, proved in this same batch, so no sorry remains after merge: checked in the merged copy, `#print axioms` has no sorryAx once `typeof_non_bot` is the proved version).

### `unop_not_none` (TypeProgress.lean:586) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hn hu hneq
  cases hn with
  | num__case_0 vI vx h1 h2 h3 =>
    cases hu with
    | unop__case_0 vI0 vx0 h4 =>
      subst h3
      cases vI <;> cases vI0 <;> cases vx0 <;> simp [numtype_Inn, fun_unop_] at h4 hneq
    | unop__case_1 vF vx0 h4 =>
      subst h3
      cases vI <;> cases vF <;> simp [numtype_Inn, numtype_Fnn] at h4
  | num__case_1 vF vx h1 h3 =>
    cases hu with
    | unop__case_0 vI0 vx0 h4 =>
      subst h3
      cases vF <;> cases vI0 <;> simp [numtype_Inn, numtype_Fnn] at h4
    | unop__case_1 vF0 vx0 h4 =>
      subst h3
      cases vF <;> cases vF0 <;> cases vx0 <;> simp [numtype_Fnn, fun_unop_] at h4 hneq
```

Notes: Port of Rocq: invert `wf_num_` and `wf_unop_` (4 combinations), `subst` the numtype, split on `Inn`/`Fnn`/unop constructors, and close with `simp [numtype_Inn, numtype_Fnn, fun_unop_]` (mismatching Inn/Fnn cases die on the equation `numtype_Inn _ = numtype_Fnn _` / `I32 = I64`; matching cases reduce `fun_unop_` to `some _ = none`). Binder-slot pitfall hit: the leading `v_numtype` of `num__case_*`/`unop__case_*` takes no slot (`num__case_0 vI vx h1 h2 h3`, `unop__case_0 vI0 vx0 h4`).

### `two_pow_pos` (TypeProgress.lean:592) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  exact Nat.two_pow_pos v_N
```

Notes: Core `Nat.two_pow_pos`.

### `Zsub1_toN` (TypeProgress.lean:598) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  omega
```

Notes: `omega` (it understands `Int.toNat`).

### `wf_uN_lt` (TypeProgress.lean:601) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro h
  cases h with
  | uN_case_0 _ hb =>
    obtain ⟨_, hle⟩ := hb
    have hp : 0 < 2 ^ v_N := Nat.two_pow_pos v_N
    have hc : ((2 ^ v_N : Nat) : Int) = (2 : Int) ^ v_N := by push_cast; rfl
    omega
```

Notes: Port of Rocq (`inversion`, take the upper bound, `Zsub1_toN`, `two_pow_pos`, `lia`). Here: `cases h with | uN_case_0 _ hb` (the `v_N` index takes no slot), then `omega`. Pitfall: the generated bound is `Int.toNat ((2:Int) ^ v_N - 1)` whereas omega's cast-pushing turns the Nat power `2 ^ v_N` into `(↑(2:Nat)) ^ v_N`, a DIFFERENT atom, so the bridge `hc : ((2 ^ v_N : Nat) : Int) = (2 : Int) ^ v_N := by push_cast; rfl` is supplied. Does not depend on TypeProgress's `two_pow_pos`/`Zsub1_toN` (uses `Nat.two_pow_pos` directly).

### `two_pow_succ` (TypeProgress.lean:605) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.pow_succ, Nat.add_sub_cancel]
  omega
```

Notes: Write `m = k + 1`, `Nat.pow_succ`, `omega` (Rocq: `N.pow_succ_r'` + `f_equal; lia`).

### `signed_total` (TypeProgress.lean:610) : proved

Still-`sorry` earlier lemmas relied on: `two_pow_succ` (proved in this batch).

```lean
  intro hlt
  have hp : 0 < 2 ^ v_N := Nat.two_pow_pos v_N
  have hp1 : 0 < 2 ^ (v_N - 1) := Nat.two_pow_pos (v_N - 1)
  have e1 : Int.toNat ((v_N : Int) - (1 : Int)) = v_N - 1 := by omega
  have hc1 : ((2 ^ v_N : Nat) : Int) = (2 : Int) ^ v_N := by push_cast; rfl
  have hc2 : ((2 ^ (v_N - 1) : Nat) : Int) = (2 : Int) ^ (v_N - 1) := by push_cast; rfl
  by_cases E : i < 2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))
  · refine ⟨(i : Int), fun_signed_.fun_signed__case_0 v_N i E, ?_, ?_⟩
    · rw [e1] at E; omega
    · rw [e1] at E; omega
  · rw [e1] at E
    have hge : 2 ^ (v_N - 1) ≤ i := by omega
    have hN0 : v_N ≠ 0 := by
      intro h0; subst h0; simp at hlt hge; omega
    have hd := two_pow_succ v_N hN0
    refine ⟨(i : Int) - (2 : Int) ^ v_N, fun_signed_.fun_signed__case_1 v_N i ⟨by rw [e1]; exact hge, hlt⟩, ?_, ?_⟩
    · omega
    · omega
```

Notes: Same case split as Rocq (`i < 2^(v_N - 1)` or not); the generated constructors are `fun_signed_.fun_signed__case_0/1`. The generated bounds mention `Int.toNat ((v_N : Int) - 1)`, rewritten with `e1 : Int.toNat ((v_N : Int) - (1 : Int)) = v_N - 1 := by omega` (this is `Zsub1_toN`, inlined), and the Nat/Int power atoms are bridged with `hc1`/`hc2` (see `wf_uN_lt`). Uses the earlier lemma `two_pow_succ` (TypeProgress:605, proved in this batch) for `2^v_N = 2 * 2^(v_N-1)`; replacing it by my proved version removes sorryAx (checked).

### `invsigned_total` (TypeProgress.lean:618) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hlo hhi
  have e1 : Int.toNat ((v_N : Int) - (1 : Int)) = v_N - 1 := by omega
  have hc1 : ((2 ^ v_N : Nat) : Int) = (2 : Int) ^ v_N := by push_cast; rfl
  have hc2 : ((2 ^ (v_N - 1) : Nat) : Int) = (2 : Int) ^ (v_N - 1) := by push_cast; rfl
  by_cases Ez : 0 ≤ z
  · refine ⟨Int.toNat z, fun_inv_signed_.fun_inv_signed__case_0 v_N z ⟨Ez, ?_⟩⟩
    rw [e1]; omega
  · refine ⟨Int.toNat (z + (2 : Int) ^ v_N), fun_inv_signed_.fun_inv_signed__case_1 v_N z ⟨?_, ?_⟩⟩
    · rw [e1]; omega
    · omega
```

Notes: Same case split as Rocq (`0 ≤ z`); witnesses `Int.toNat z` and `Int.toNat (z + 2 ^ v_N)` with the generated constructors `fun_inv_signed__case_0/1`; same `e1`/`hc1`/`hc2` bridges. No sorryAx.

### `Zquot_abs_le` (TypeProgress.lean:626) : proved

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hb hp ha
  have h1 := Int.natAbs_tdiv_le_natAbs a b
  rw [Int.abs_eq_natAbs] at ha ⊢
  omega
```

Notes: Lean-way proof. Rocq uses `Z.quot_abs` + `Z.quot_le_compat_l`; Lean core has `Int.natAbs_tdiv_le_natAbs (a b : Int) : natAbs (a.tdiv b) ≤ natAbs a`, so: `rw [Int.abs_eq_natAbs] at ha ⊢; omega`. (The hypothesis `b ≠ 0` is not needed: `a / 0 = 0`.)

## Final Lean check output (`lake env lean Work.lean`, all 14 guards `rfl` accepted)
```
'TLC.return_reduce_extract_vs_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.lookup_types_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.funcs_size_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.admininstr_CONST_eq_arg_proof' does not depend on any axioms
'TLC.typeof_non_bot_proof' depends on axioms: [propext]
'TLC.typeof_vals_non_bot_proof' depends on axioms: [propext, sorryAx, Quot.sound]
'TLC.unop_not_none_proof' depends on axioms: [propext]
'TLC.two_pow_pos_proof' depends on axioms: [propext]
'TLC.Zsub1_toN_proof' depends on axioms: [propext, Quot.sound]
'TLC.wf_uN_lt_proof' depends on axioms: [propext, Quot.sound]
'TLC.two_pow_succ_proof' depends on axioms: [propext, Quot.sound]
'TLC.signed_total_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.invsigned_total_proof' depends on axioms: [propext, Quot.sound]
'TLC.Zquot_abs_le_proof' depends on axioms: [propext, Quot.sound]
exit: 0
```

Merge simulation (`lake env lean t/TypeProgressMerged.lean`): exit 0, 0 errors, 266 `declaration uses sorry` warnings, 0 at the 14 target lines.


## Safety check at END
```
safety check [prove-H06] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T124020.984045220Z-prove-H06-1462154.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Hand-off notes for the main thread
- Merge order: paste each block after `:= by` of the matching theorem in TypeProgress.lean (replacing `:= sorry`); the blocks were verified in a merged copy of the real file (see Method). `typeof_vals_non_bot` needs `typeof_non_bot` and `signed_total` needs `two_pow_succ` merged too (all in this batch).
- The same proof shape as `return_reduce_extract_vs` should work for `br_reduce_extract_vs` (TypeProgress.lean:525): replace `RETURN` by `BR (uN.mk_uN 0)`, `C.RETURN = some t` by `C.LABELS[0]! = ts`, and read the label type from `ai_principal_typing` of `BR` (`v_C.LABELS[proj_uN_0 l]? = some (list.mk_list ts)`, see the pattern in `Step_pure__br_zero_preserves`, TypePreservationPure.lean:350).
- Pitfall list hit and solved: omega treats `((2:Nat)^n : Int)` cast-pushed and `(2:Int)^n` as different atoms (bridge with `((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl`); `cases h with | ctor ..` slots skip the leading index/parameter `v_N` / `v_numtype`.

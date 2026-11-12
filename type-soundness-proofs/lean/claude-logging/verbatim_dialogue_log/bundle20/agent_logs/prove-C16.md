# prove-C16 log (bundle20 progress port, proof batch C16)

Targets (in order): `t_progress_be_memory_size` (TypeProgress.lean:2123; Rocq type_progress.v:4693-4745),
`t_progress_be_memory_grow` (TypeProgress.lean:2132; Rocq 4745-4769), `t_progress_be_memory_fill`
(TypeProgress.lean:2141; Rocq 4769-4820). All bullets of `t_progress_be`.

## Safety check at START
```
safety check [prove-C16] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T134510.967426726Z-prove-C16-1508517.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- Scratch `build.py` copies each target header verbatim from TypeProgress.lean (from `theorem` to `:= sorry`), renames it
  `<name>_proof`, appends the proof body (scratch `proofs/<name>.lean`) and the guard
  `example : type_of% @<name>_proof = type_of% @<name> := rfl`, inside `import TypeProgress` / `namespace TLC`.
  `lake env lean Work.lean`: exit 0, no output (all 3 proofs and all 3 guards pass).
- Negative control `Work_ctl.lean` (same file + `#print axioms` + `example : (1:Nat) = 2 := rfl`): the bogus example
  fails (exit 1), so the check is live.
- TypeProgress.olean (20:18:19.90) is newer than TypeProgress.lean (20:18:16.73), so the guard compares against the
  current statements. TypeProgress.lean has no file-level `open`/`set_option`/`attribute` (only `namespace TLC`) and
  no `@[simp]` lemmas, so the merged proofs elaborate in the same context as in Work.lean.
- Merge simulation `Head.lean` (scratch, from `head.py`): the real TypeProgress.lean prefix through
  `t_progress_be_memory_fill`, my three proofs in place of `:= sorry`, plus `#print axioms` for the three, and `end TLC`.
  `lake env lean`: exit 0, 0 errors. The last `declaration uses sorry` warning is at Head.lean:2114
  (`t_progress_be_elem_drop`, not mine), so none of the targets (Head.lean 2123/2160/2187) warns. This also confirms
  the ordering rule.
- One Lean process of mine at a time, `lake env lean` only (never `lake build`). No repo file edited (only this log).
- Ordering: TypeProgress declarations used: `invert_typeof_I32` (line 209, sorry), `invsigned_total_32m1` (line 1082,
  sorry), `t_progress_be_P` (line 1486, def), all before 2123. Imported: `Moduleinst_ok_lengths`, `Store_ok_parts`
  (TypePreservation.lean, Lean-only inversion helpers; TypeProgress.lean imports TypePreservation for exactly such
  helpers, see its module doc), `minst_invert_mems`, `meminst_ok_raw` (ExtensionLemmas), `mem_zip_getElem!`
  (HelperLemmas), `mkFunctype` (Subtyping), generated `Step.read`, `Step.memory_grow_fail`,
  `Step_read.memory_size`, `Step_read.memory_fill_{trap,zero,succ}`, `wf_uN.uN_case_0`, `fun_mem`, `proj_num__0`,
  `proj_uN_0`.
- Axioms (`#print axioms`): memory_size: `propext, Classical.choice, Quot.sound` (sorry-free). memory_grow / memory_fill:
  additionally `sorryAx`, inherited only from the still-sorry earlier lemmas listed per target. No HelperLemmas
  project axiom used. No `sorry`, `admit`, `native_decide`, or new axioms.

## Porting notes
- Common prefix (as in C14): `intro`s, `unfold t_progress_be_P`, Rocq's
  `move => s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret`, `right`,
  `case: Htf => Htf1 _` / `rewrite -Htf1 in Hts`; Rocq's Ltac `invert_typeof_vcs` done inline (`rcases` on `vcs` +
  `simp at Hts` on the wrong-length branches); `inv_Forall HWfVals` = `HWfVals v (by simp)`; `invert_typeof_I32`.
- memory_size: Rocq's `addr := lookup_total (MEMS (frame_MODULE f)) 0` and `Haddr : addr < |meminst_lst|` (via
  `invert_moduleinstok` + `Externaddr_invert_mems`) = `Moduleinst_ok_lengths` (for `0 < |f.MODULE.MEMS|`, using
  `C.MEMS = C'.MEMS` since `upd_local_label_return` leaves MEMS alone) + `minst_invert_mems` with
  `inst_match C' C'` + `mem_zip_getElem!`. Rocq's `invert_storeok Hstore` / `Hmem : Meminst_ok s (lookup_total
  meminst_lst addr) ...` = `Store_ok_parts` + `mem_zip_getElem!` (zip-based `Forall₂`; lengths from Store_ok's
  explicit length premise). Rocq's `inversion Hmem` = `meminst_ok_raw` (gives `|bs| = n * (64 * Ki)` exactly;
  `s_invert_mems` only has `n = |bs| / (64*Ki)`). Then `Step_read.memory_size` with the `N.mul_assoc` rewrite
  (`Nat.mul_assoc` here); the extra `wf_uN 32 (mk_uN 0)` premise of the Lean rule is `wf_uN.uN_case_0 32 0`.
- memory_grow: Rocq builds `meminst1`/`meminst2`/`Estate` but never uses them (its NOTE says it relies on
  `memory_grow_fail`); only the essential steps are ported: `invsigned_total_32m1` (`(0:Int) - 1` vs the rule's
  `-(1:Int)` closed by `simpa`) then `Step.memory_grow_fail` (a `Step`, not `Step_read`, rule in Lean too).
- memory_fill: case on Rocq's `Hs : n1 + n3 > |BYTES (fun_mem s 0)|` -> `Step_read.memory_fill_trap`; otherwise
  `n3 = 0` (Rocq's `N.peano_ind` base) -> `memory_fill_zero`; otherwise `memory_fill_succ` (Lean's rule takes `v_n`
  and outputs `Int.toNat (v_n - 1)`, and `es'` is existential, so Rocq's `n3 = N.succ n3 - 1` rewrite is
  unnecessary; witness `es'` left as `_`). `v2` stays as `admininstr_val v2` as in the rule, so (as in Rocq, which
  never uses `Heqv2`) it is not inverted.

## Results
### `t_progress_be_memory_size` : proved
Still-`sorry` earlier lemmas relied on: none (sorry-free).
```lean
  intro C mt Hlen Hlookup HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, vcs⟩
  · -- Rocq: `addr := lookup_total (MEMS (frame_MODULE f)) 0` and `Haddr : addr < |meminst_lst|`
    have HeqC : C.MEMS = C'.MEMS := by subst Hcontext; rfl
    obtain ⟨_, _, Hmlen, _, _, _⟩ := Moduleinst_ok_lengths s f.MODULE C' Hmod
    have Hlen' : 0 < f.MODULE.MEMS.length := by rw [Hmlen, ← HeqC]; exact Hlen
    have Hinv := minst_invert_mems s f.MODULE C' C' Hmod ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨_, _, Haddr, _, _⟩ :=
      Hinv _ (mem_zip_getElem! f.MODULE.MEMS C'.MEMS 0 Hlen' (by rw [← Hmlen]; exact Hlen'))
    have Haddr' : f.MODULE.MEMS[0]! < s.MEMS.length := Haddr
    -- Rocq: `invert_storeok Hstore` and `Hmem : Meminst_ok s (lookup_total meminst_lst addr) ...`
    obtain ⟨_, mtl, _, _, _, _, _, _, Hml, HMem, _⟩ := Store_ok_parts s Hstore
    have Hmem : Meminst_ok s s.MEMS[f.MODULE.MEMS[0]!]! mtl[f.MODULE.MEMS[0]!]! :=
      HMem _ (mem_zip_getElem! s.MEMS mtl _ Haddr' (by rw [← Hml]; exact Haddr'))
    -- Rocq: `inversion Hmem`
    obtain ⟨v_n, _, bs, Hmi, _, Hbs, _, _⟩ := meminst_ok_raw s _ _ Hmem
    refine ⟨s, f, [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))],
      Step.read _ _ _ (Step_read.memory_size (state.mk_state s f) v_n ?_ ?_)⟩
    · simp only [fun_mem, proj_uN_0]
      rw [Hmi, Hbs, Nat.mul_assoc]
    · exact wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩
  · simp at Hts
```

### `t_progress_be_memory_grow` : proved
Still-`sorry` earlier lemmas relied on: `invert_typeof_I32` (line 209), `invsigned_total_32m1` (line 1082).
```lean
  intro C mt Hlen Hlookup HWfC HWMemType HWfinstr
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
    have HP1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 HP1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1]
    -- Rocq: `pose proof invsigned_total_32m1 as [r Hunsigned]` then `memory_grow_fail`
    obtain ⟨r, Hunsigned⟩ := invsigned_total_32m1
    exact ⟨s, f, _, Step.memory_grow_fail (state.mk_state s f) n1 r (by simpa using Hunsigned)⟩
  · simp at Hts
```

### `t_progress_be_memory_fill` : proved
Still-`sorry` earlier lemmas relied on: `invert_typeof_I32` (line 209).
```lean
  intro C mt Hlen Hlookup HWfC HWfMemType HWfinstr
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
    have HP3 : wf_val v3 := HWfVals v3 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 HP1
    obtain ⟨n3, Heqv3⟩ := invert_typeof_I32 v3 Ht3 HP3
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1, Heqv3]
    by_cases Hs : n1 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.memory_fill_trap (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)) v2 n3
          (by simp [proj_num__0]) (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · by_cases Hz : n3 = 0
      · subst Hz
        exact ⟨s, f, [], Step.read _ _ _
          (Step_read.memory_fill_zero (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)) v2 0
            (by simp [proj_num__0]) (by simp only [proj_num__0, proj_uN_0, Option.get!_some]; omega) rfl)⟩
      · exact ⟨s, f, _, Step.read _ _ _
          (Step_read.memory_fill_succ (state.mk_state s f) (num_.mk_num__0 Inn.I32 (uN.mk_uN n1)) v2 n3
            (by simp [proj_num__0]) Hz (by simp only [proj_num__0, proj_uN_0, Option.get!_some]; omega))⟩
  · simp at Hts
```

## Final Lean check output
`lake env lean Work.lean` (3 proofs + 3 rfl guards): exit 0, no output.

Negative control `Work_ctl.lean`:
```
'TLC.t_progress_be_memory_size_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_be_memory_grow_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_memory_fill_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Work_ctl.lean:110:25: error: Type mismatch  rfl  has type ?m.7 = ?m.7 but is expected to have type 1 = 2
(exit 1, as intended)
```

`lake env lean Head.lean` (merge simulation), non-warning lines and last two sorry warnings:
```
'TLC.t_progress_be_memory_size' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.t_progress_be_memory_grow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.t_progress_be_memory_fill' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
exit=0
Head.lean:2102:8: warning: declaration uses `sorry`
Head.lean:2114:8: warning: declaration uses `sorry`
(exit 0; 0 errors; 240 'declaration uses sorry' warnings, all from other still-sorry declarations at lines <= 2114)
```

## Safety check at END
```
safety check [prove-C16] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T135008.426855077Z-prove-C16-1511808.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

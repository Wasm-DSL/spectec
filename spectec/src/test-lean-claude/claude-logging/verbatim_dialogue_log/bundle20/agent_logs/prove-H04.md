# prove-H04 (bundle20 progress port, proof batch H04)

Targets (14): `not_lf_return_right`, `not_lf_return_left`, `Forall2_Val_ok_is_same_as_map`, `frame_t_context_local_types`, `frame_t_context_label_empty`, `wf_forall_admin_val`, `wf_forall_admin`, `wf_config_label`, `wf_config_frame`, `frame_t_context_return_empty`, `Admin_instrs_ok_cons`, `Admin_instrs_ok_cat`, `Admin_instrs_ok_all`, `s_typing_lf_br'` (TypeProgress.lean:366-466).

**Result: all 14 proved.** No repo file was edited. Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H04/`. Only my own log file was written inside the target dir (plus the safety-check output files the check script itself creates).

## Safety check at START
```
safety check [prove-H04] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T122405.410131932Z-prove-H04-1449895.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- `Work.lean` (scratch): the header of each target copied verbatim from TypeProgress.lean, theorem renamed `<name>_proof`, plus the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all 14 guards pass, so the tactic blocks below drop into the real file unchanged).
- `Merged.lean` (scratch): same proofs with the in-batch dependencies redirected to the `_proof` versions; `#print axioms` shows the only remaining `sorryAx` is `not_lf_return_left` (through `const_es_exists`, batch H01). Everything else uses only `propext`, `Classical.choice`, `Quot.sound`.
- `Head.lean` (scratch): merge simulation = the first part of the real TypeProgress.lean (everything before `s_typing_lf_br`, 636 lines after substitution) with the 14 `sorry` bodies replaced by the proofs below, compiled with `lake env lean` against the real imports. It compiles with no errors; no `sorry` warning is attached to any of the 14 targets (the remaining warnings are the other batches' targets, all at earlier lines); ordering rule satisfied (only earlier declarations / imports are used).
- One Lean process at a time, `lake env lean` only (never `lake build`, nothing written under `.lake/`). A run takes about 2 s (oleans are memory-mapped).
- Axioms: only the standard ones (`propext`, `Classical.choice`, `Quot.sound`). No project `axiom` from HelperLemmas was used. No `sorry`, `admit`, `native_decide`, new axioms.
- Imported helper lemmas used (all proved): `to_mathlib_forall₂` (HelperLemmas), `inst_t_context_local_empty`, `inst_t_context_labels_empty` (TypePreservation), `wf_admininstr_instr`, `ainstrs_ok_context_store_wf`, `ais_seq_typing_inversion`, `ais_single_typing_inversion'`, `revert_to_instr_from_ai`, `instrs_single_typing_inversion` (TypingLemmas).
- Binder-slot facts learned (useful for other batches): `Frame_ok` and `Val_ok` both have their leading `s : store` auto-promoted to an inductive parameter, so `cases hframe with | mk_Frame_ok val_lst v_minst t_lst0 C0 hminst hlen hvals _ _ _ _` has 11 slots and `Val_ok`'s `numtype`/`vectype`/`reftype` have 4 slots each. After `cases` on `Instr_ok C (BR l) _` the hypotheses are NOT in declaration order (fetch by type with `assumption`).

## Results

### `not_lf_return_right` : proved

Location: TypeProgress.lean:366; Rocq type_progress.v:772-781.

Still-`sorry` earlier lemmas relied on: none.

```lean
  unfold not_lf_return
  intro hnotret vcs es' hcontra
  apply hnotret vcs (es' ++ es2)
  rw [hcontra]
  simp
```

Notes: Faithful port: Rocq `rewrite /not_lf_return; move/(_ vcs (es' ++ es2))`, `rewrite Hcontra -2!catA` becomes `unfold not_lf_return`, `apply hnotret vcs (es' ++ es2)`, `rw [hcontra]`, `simp` (list-append associativity).

### `not_lf_return_left` : proved

Location: TypeProgress.lean:372; Rocq type_progress.v:783-793.

Still-`sorry` earlier lemmas relied on: const_es_exists (TypeProgress.lean:~124, batch H01, still `sorry` when this was checked).

```lean
  unfold not_lf_return
  intro hconst hnotret vcs es' hcontra
  obtain ⟨vs1, hvs1⟩ := const_es_exists es1 hconst
  apply hnotret (vs1 ++ vcs) es'
  rw [hvs1, hcontra]
  simp
```

Notes: Faithful port: `const_es_exists` gives `vs1` with `es1 = map admininstr_val vs1`; the witness for the hypothesis is `vs1 ++ vcs` (Rocq's `-v_to_e_cat -catA` is `simp` with `List.map_append`/`List.append_assoc`).

### `Forall2_Val_ok_is_same_as_map` : proved

Location: TypeProgress.lean:384; Rocq type_progress.v:795-806.

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hforall hlen
  have h := to_mathlib_forall₂ hlen hforall
  clear hforall hlen
  induction h with
  | nil => rfl
  | @cons a b l1 l2 hab _ ih =>
    have hab' : Val_ok v_S b a := hab
    have hty : typeof b = a := by
      cases hab' with
      | numtype _ _ _ _ => rfl
      | vectype _ _ _ _ => rfl
      | reftype _ _ href _ => cases href <;> rfl
    rw [List.map_cons, hty, ih]
```

Notes: Same induction as Rocq, but not on the zip-based `Forall₂` directly: with the length premise (the statement's documented deviation) `to_mathlib_forall₂` (HelperLemmas) turns it into Mathlib's inductive `List.Forall₂`, on which `induction` works as Rocq's `Forall2` induction. `Val_ok v_S b a -> typeof b = a` by `cases`: numtype/vectype are `rfl`; reftype needs `cases href <;> rfl` (Ref_ok null/func/extern fix `val_ref r` and the reftype). Binder gotcha: `Val_ok`'s leading `s : store` is auto-promoted to an inductive parameter, so its constructors take 4 binder slots (not 5).

### `frame_t_context_local_types` : proved

Location: TypeProgress.lean:392; Rocq type_progress.v:808-817.

Still-`sorry` earlier lemmas relied on: Forall2_Val_ok_is_same_as_map (TypeProgress.lean:384; proved in this same batch).

```lean
  intro hframe
  cases hframe with
  | mk_Frame_ok val_lst v_minst t_lst0 C0 hminst hlen hvals _ _ _ _ =>
    have hloc := inst_t_context_local_empty s v_minst C0 hminst
    show t_lst0 ++ C0.LOCALS = List.map typeof val_lst
    rw [hloc, List.append_nil]
    exact (Forall2_Val_ok_is_same_as_map s t_lst0 val_lst hvals hlen).symm
```

Notes: Faithful port. `cases hframe with | mk_Frame_ok ...` (11 slots; `s` is a promoted parameter), `C = {LOCALS := t_lst0, ...} ++ C0`, so `C.LOCALS` is `t_lst0 ++ C0.LOCALS` (`show`), `C0.LOCALS = []` by `inst_t_context_local_empty` (TypePreservation.lean:103, proved), then `Forall2_Val_ok_is_same_as_map` with Frame_ok's own length premise.

### `frame_t_context_label_empty` : proved

Location: TypeProgress.lean:398; Rocq type_progress.v:819-826.

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hframe
  cases hframe with
  | mk_Frame_ok _ v_minst _ C0 hminst _ _ _ _ _ _ =>
    have hlab := inst_t_context_labels_empty s v_minst C0 hminst
    show [] ++ C0.LABELS = []
    simp [hlab]
```

Notes: Faithful port. `C.LABELS = [] ++ C0.LABELS`, `C0.LABELS = []` by `inst_t_context_labels_empty` (TypePreservation.lean:108, proved).

### `wf_forall_admin_val` : proved

Location: TypeProgress.lean:404; Rocq type_progress.v:829-844.

Still-`sorry` earlier lemmas relied on: none.

```lean
  constructor
  · intro h a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    have hwf := h v hv
    cases hwf with
    | val_case_0 nt c hn => exact wf_admininstr.admininstr_case_13 nt c hn
    | val_case_1 vt c hsz hwfc => exact wf_admininstr.admininstr_case_20 vt c hsz hwfc
    | val_case_2 rt => exact wf_admininstr.admininstr_case_40 rt
    | val_case_3 a => exact wf_admininstr.admininstr_case_68 a
    | val_case_4 a => exact wf_admininstr.admininstr_case_69 a
  · intro h v hv
    have hwf := h (admininstr_val v) (List.mem_map.mpr ⟨v, hv, rfl⟩)
    cases v with
    | CONST nt c =>
      have hwf' : wf_admininstr (admininstr.CONST nt c) := hwf
      cases hwf' with
      | admininstr_case_13 _ _ hn => exact wf_val.val_case_0 nt c hn
    | VCONST vt c =>
      have hwf' : wf_admininstr (admininstr.VCONST vt c) := hwf
      cases hwf' with
      | admininstr_case_20 _ _ hsz hwfc => exact wf_val.val_case_1 vt c hsz hwfc
    | REF_NULL rt => exact wf_val.val_case_2 rt
    | REF_FUNC_ADDR a => exact wf_val.val_case_3 a
    | REF_HOST_ADDR a => exact wf_val.val_case_4 a
```

Notes: Rocq inducts on `List.Forall`; Lean's `Forall` is the membership-form `def`, so it is proved pointwise via `List.mem_map`. Forward: `cases` on `wf_val` and the matching `wf_admininstr.admininstr_case_{13,20,40,68,69}`. Backward: `cases v`, restate `hwf` at the constructor form (`admininstr_val` iota-reduces) and `cases` it (case_13 / case_20), refs are the constant cases.

### `wf_forall_admin` : proved

Location: TypeProgress.lean:410; Rocq type_progress.v:846-854.

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro h a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  exact (wf_admininstr_instr i).mp (h i hi)
```

Notes: Pointwise via `List.mem_map`; each element uses `wf_admininstr_instr` (TypingLemmas.lean:1545, proved), as Rocq's `apply wf_admininstr_instr`.

### `wf_config_label` : proved

Location: TypeProgress.lean:417; Rocq type_progress.v:857-868.

Still-`sorry` earlier lemmas relied on: wf_forall_admin (TypeProgress.lean:410; proved in this same batch).

```lean
  intro h
  cases h with
  | config_case_0 _ _ hst hall =>
    have hlab : wf_admininstr (admininstr.LABEL_ n bes es) := hall _ (List.mem_singleton_self _)
    cases hlab with
    | admininstr_case_71 _ _ _ hbes hes =>
      exact ⟨wf_config.config_case_0 s es hst hes,
             wf_config.config_case_0 s _ hst (wf_forall_admin bes hbes)⟩
```

Notes: Faithful port of `inversion HWf; inv_Forall; inversion HP; apply wf_forall_admin; config_case_0`: `cases` on `wf_config`, the singleton membership gives `wf_admininstr (LABEL_ n bes es)`, `cases` it (`admininstr_case_71`), rebuild both configs with `wf_config.config_case_0` and the same `wf_state`.

### `wf_config_frame` : proved

Location: TypeProgress.lean:425; Rocq type_progress.v:870-883.

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro h
  cases h with
  | config_case_0 _ _ hst hall =>
    have hfr : wf_admininstr (admininstr.FRAME_ n f es) := hall _ (List.mem_singleton_self _)
    cases hfr with
    | admininstr_case_72 _ _ _ hwff hes =>
      cases hst with
      | state_case_0 _ _ hwfs hwff' =>
        exact ⟨wf_config.config_case_0 _ es (wf_state.state_case_0 s f' hwfs hwff') hes,
               wf_config.config_case_0 _ es (wf_state.state_case_0 s f hwfs hwff) hes⟩
```

Notes: Faithful port: `cases` the config, the singleton gives `wf_admininstr (FRAME_ n f es)` (`admininstr_case_72`: `wf_frame f` and the body), `cases` the outer `wf_state` (`state_case_0`: `wf_store s`, `wf_frame f'`), and rebuild `wf_state.state_case_0 s f' ..` / `s f ..`.

### `frame_t_context_return_empty` : proved

Location: TypeProgress.lean:432; Rocq type_progress.v:885-892.

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hframe
  cases hframe with
  | mk_Frame_ok _ _ _ C0 hminst _ _ _ _ _ _ =>
    cases hminst
    rfl
```

Notes: Faithful port. `cases hminst` substitutes `C0` by the module context literal (`RETURN := none`), after which `Option.orElse none (fun _ => none) = none` is `rfl`.

### `Admin_instrs_ok_cons` : proved

Location: TypeProgress.lean:438; Rocq type_progress.v:895-909.

Still-`sorry` earlier lemmas relied on: none.

```lean
  intro hadmin
  obtain ⟨t3s, h1, h2⟩ := ais_seq_typing_inversion s C es e ts1 ts2 hadmin
  exact ⟨[], ts1, ts2, t3s, rfl, rfl, h2, h1⟩
```

Notes: Faithful port: `ais_seq_typing_inversion` (TypingLemmas.lean:1244, proved) and the empty common prefix `ts = []` (`[] ++ ts1 = ts1` is `rfl`).

### `Admin_instrs_ok_cat` : proved

Location: TypeProgress.lean:449; Rocq type_progress.v:912-947.

Still-`sorry` earlier lemmas relied on: Admin_instrs_ok_cons (TypeProgress.lean:438; proved in this same batch).

```lean
  induction es1 generalizing ts1 ts2 with
  | nil =>
    intro hadmin
    obtain ⟨hWfC, hWfS, _⟩ := ainstrs_ok_context_store_wf s C _ _ hadmin
    refine ⟨[], ts1, ts2, ts1, rfl, rfl, ?_, by simpa using hadmin⟩
    have hf := Instrs_ok2.Instrs_ok2_frame s C [] ts1 [] [] (Instrs_ok2.empty s C hWfS hWfC) hWfS hWfC
      (by intro x hx; simp at hx)
    simpa [mkFunctype] using hf
  | cons e1 es1' ih =>
    intro hadmin
    obtain ⟨hWfC, hWfS, _⟩ := ainstrs_ok_context_store_wf s C _ _ hadmin
    have hadmin' : Instrs_ok2 s C ([e1] ++ (es1' ++ es2)) (mkFunctype ts1 ts2) := hadmin
    obtain ⟨ts, ts1', ts2', ts3, Ets1, Ets2, Hadmin1, Hadmin2⟩ :=
      Admin_instrs_ok_cons s C (es1' ++ es2) e1 ts1 ts2 hadmin'
    obtain ⟨ts', ts1'', ts2'', ts3', Ets1', Ets2', Hadmin1', Hadmin2'⟩ := ih ts3 ts2' Hadmin2
    have hwf1 := (ainstrs_ok_context_store_wf s C [e1] _ Hadmin1).2.2
    have hwf_es1' := (ainstrs_ok_context_store_wf s C es1' _ Hadmin1').2.2
    have hwf_es2 := (ainstrs_ok_context_store_wf s C es2 _ Hadmin2').2.2
    have hf1 : Instrs_ok2 s C es1' (mkFunctype (ts' ++ ts1'') (ts' ++ ts3')) :=
      Instrs_ok2.Instrs_ok2_frame s C es1' ts' ts1'' ts3' Hadmin1' hWfS hWfC hwf_es1'
    have hf2 : Instrs_ok2 s C es2 (mkFunctype (ts' ++ ts3') (ts' ++ ts2'')) :=
      Instrs_ok2.Instrs_ok2_frame s C es2 ts' ts3' ts2'' Hadmin2' hWfS hWfC hwf_es2
    rw [← Ets1'] at hf1
    rw [← Ets2'] at hf2
    exact ⟨ts, ts1', ts2', ts' ++ ts3', Ets1, Ets2,
      Instrs_ok2.seq s C [e1] es1' ts1' (ts' ++ ts3') ts3 Hadmin1 hf1 hWfS hWfC hwf1 hwf_es1', hf2⟩
```

Notes: Faithful port: induction on `es1` (generalizing the types) with the same lemma applications as Rocq: `Admin_instrs_ok_cons` for the head, the IH on the tail, `Instrs_ok2.Instrs_ok2_frame` on both pieces, `rw` with `Ets1'`/`Ets2'` (Rocq's `-Ets1'`), then `Instrs_ok2.seq`. Nil case: `Instrs_ok2_frame` of `Instrs_ok2.empty` with prefix `ts1`, `simpa` for `ts1 ++ [] = ts1`. Deviation: the `Forall wf_admininstr` side conditions (Rocq's `inv_Forall` output `Hrest`/`HP2`) are read off the sub-derivations with `ainstrs_ok_context_store_wf` (`.2.2`) instead of inverting the whole list's `Forall`. (`ais_composition_typing` of TypingLemmas would also give this lemma directly with `ts = []`; Rocq's own TODO notes the duplication.)

### `Admin_instrs_ok_all` : proved

Location: TypeProgress.lean:460; Rocq type_progress.v:949-970.

Still-`sorry` earlier lemmas relied on: Admin_instrs_ok_cons (TypeProgress.lean:438; proved in this same batch).

```lean
  induction es generalizing ts1 ts2 with
  | nil =>
    intro _ e he
    simp at he
  | cons e' es' ih =>
    intro hadmin e he
    have hadmin' : Instrs_ok2 s C ([e'] ++ es') (mkFunctype ts1 ts2) := hadmin
    obtain ⟨ts, ts1', ts2', ts3, Ets1, Ets2, Hadmin1, Hadmin2⟩ :=
      Admin_instrs_ok_cons s C es' e' ts1 ts2 hadmin'
    rcases List.mem_cons.mp he with rfl | hin
    · obtain ⟨t1s_sup, t2s_sub, hty, _⟩ := ais_single_typing_inversion' s C e ts1' ts3 Hadmin1
      exact ⟨t1s_sup, t2s_sub, hty⟩
    · exact ih ts3 ts2' Hadmin2 e hin
```

Notes: Faithful port: induction on `es` generalizing the types; head case via `Admin_instrs_ok_cons` then `ais_single_typing_inversion'` (TypingLemmas.lean:1333, proved); tail case via the IH on the second component.

### `s_typing_lf_br'` : proved

Location: TypeProgress.lean:466; Rocq type_progress.v:972-1006.

Still-`sorry` earlier lemmas relied on: frame_t_context_label_empty (TypeProgress.lean:398; proved in this same batch).

```lean
  intro hframe
  induction es generalizing t1s t2s with
  | nil =>
    intro _ e he
    simp at he
  | cons a es ih =>
    intro hadmin e he
    have hadmin' : Instrs_ok2 s C ([a] ++ es) (mkFunctype t1s t2s) := hadmin
    obtain ⟨t3s, HType2, HType1⟩ := ais_seq_typing_inversion s C es a t1s t2s hadmin'
    rcases List.mem_cons.mp he with rfl | hin
    · intro H
      subst H
      have hbr : Instrs_ok2 s C [admininstr_instr (instr.BR l)] (mkFunctype t1s t3s) := HType1
      have hbr' := revert_to_instr_from_ai s C (instr.BR l) t1s t3s hbr
      obtain ⟨t1s_sup, t2s_sub, hty, _⟩ := instrs_single_typing_inversion C (instr.BR l) t1s t3s hbr'
      cases hty
      have hlt : proj_uN_0 l < C.LABELS.length := by assumption
      rw [frame_t_context_label_empty s f C hframe] at hlt
      simp at hlt
    · exact ih t3s t2s HType2 e hin
```

Notes: Faithful port: induction on `es` (generalizing the types); for the head `BR l`: `ais_seq_typing_inversion`, `revert_to_instr_from_ai`, `instrs_single_typing_inversion`, `cases` on `Instr_ok C (BR l) _` leaves only the `br` rule, whose bound `proj_uN_0 l < C.LABELS.length` contradicts `C.LABELS = []` (`frame_t_context_label_empty`). Gotcha: after `cases hty` the hypotheses come out in a non-declaration order, so the label-bound hypothesis is fetched by type with `assumption` rather than by position (`rename_i` mislabels it). The tail case is the IH.

## Final Lean check output
`lake env lean .../prove-H04/Work.lean` (final version): exit 0, empty output (no errors, no warnings).

`lake env lean .../prove-H04/Head.lean` (merge simulation) ends with:
```
'TLC.not_lf_return_right' depends on axioms: [propext]
'TLC.not_lf_return_left' depends on axioms: [propext, sorryAx]
'TLC.Forall2_Val_ok_is_same_as_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.frame_t_context_local_types' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.frame_t_context_label_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.wf_forall_admin_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.wf_forall_admin' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.wf_config_label' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.wf_config_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.frame_t_context_return_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.Admin_instrs_ok_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.Admin_instrs_ok_cat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.Admin_instrs_ok_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.s_typing_lf_br'' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(`not_lf_return_left` is the only one with `sorryAx`, solely through the earlier `const_es_exists` of batch H01.)

## Safety check at END
```
safety check [prove-H04] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T123034.046246269Z-prove-H04-1454559.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

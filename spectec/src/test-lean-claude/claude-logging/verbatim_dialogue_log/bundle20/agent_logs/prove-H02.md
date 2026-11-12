# prove-H02 log (bundle20 progress port, proof batch H02, 14 targets)

Agent label: prove-H02. Scope: only this log file and the scratch dir `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H02/` were written; `TypeProgress.lean` and every other repo file were NOT touched. One Lean process at a time; no `lake build`; no git state changes; no agents spawned.

## Safety check at START (run from /home/zhengyew/spectec)

```
safety check [prove-H02] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T121955.709970672Z-prove-H02-1446684.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method

Scratch `Work.lean` (`import TypeProgress`, `namespace TLC`): each target's header copied verbatim and renamed `<name>_proof`, followed by the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all 14 guards pass, so the statements are identical and the bodies drop in unchanged). `Work2.lean` = same with same-batch references redirected to the `_proof` versions plus `#print axioms`. `Merged.lean` = the first 246 lines of the real `TypeProgress.lean` (through `invert_typeof_V128`) with the 14 `:= sorry` replaced by `:= by <body>` below, compiled standalone: no errors; the only `declaration uses sorry` warnings are the 13 pre-existing sorry'd lemmas outside this batch (`cat_nil`, `LOCAL_injective`, `default_not_none`, `wf_config_app`, `v_to_e_const`, `const_list_cat`, `const_list_concat`, `const_list_split`, `const_es_exists`, `map_eq_nil`, `map_neq_nil`, `reduce_trap_left`, `v_e_trap`).

Ordering rule: every reference is to an earlier declaration (`concat_cancel_last` 138 < `extract_list1` 143; `cat_split` 165 < `typeof_append` 188 < `typeof_cat` 197; `const_list_split` ~106 < `terminal_form_v_e` 172).

Axioms: only `propext` (and none for `cat_split`, `invert_typeof_numtype`). No `sorry`/`admit`/`native_decide`/new axioms of my own. `terminal_form_v_e` is transitively `sorryAx`-dependent solely through the earlier still-sorry `const_list_split` (Rocq's own proof uses `const_list_split` as well).

Pitfall hit while porting (both fixed): `cases ... with | num__case_0 ...` binder slots - `wf_num_`'s first index (`numtype`) is auto-promoted to an inductive parameter, so `num__case_0` takes 5 names (vInn, x, size-premise, wf_uN-premise, numtype-eq) and `num__case_1` 4; `val_case_1` takes 4 (vectype, payload, size-premise, wf_uN-premise).

## Results (all 14 proved)

### `concat_cancel_last` (TypeProgress.lean:138; Rocq type_progress.v:186-194) - PROVED

Earlier lemmas relied on: none. Imitates Rocq (reverse both sides, `rev_cat`, `revK`) via `List.reverse_append` + `List.reverse_inj`.

```lean
  intro H
  have H0 : (l1 ++ [e1]).reverse = (l2 ++ [e2]).reverse := by rw [H]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.cons.injEq] at H0
  obtain ⟨h1, h2⟩ := H0
  exact ⟨List.reverse_inj.mp h2, h1⟩
```

### `extract_list1` (TypeProgress.lean:143; Rocq type_progress.v:197-204) - PROVED

Earlier lemmas relied on: concat_cancel_last (same batch, proved here). As Rocq: `apply concat_cancel_last` with `[e2]` unified with `[] ++ [e2]` (defeq).

```lean
  intro H
  exact concat_cancel_last es [] e1 e2 H
```

### `v_to_e_cat` (TypeProgress.lean:148; Rocq type_progress.v:206-212) - PROVED

Earlier lemmas relied on: none. Induction on vs1, as Rocq.

```lean
  induction vs1 with
  | nil => rfl
  | cons a l IH => simp only [List.map_cons, List.cons_append, IH]
```

### `be_to_e_cat` (TypeProgress.lean:153; Rocq type_progress.v:214-220) - PROVED

Earlier lemmas relied on: none. Induction on bes1, as Rocq.

```lean
  induction bes1 with
  | nil => rfl
  | cons a l IH => simp only [List.map_cons, List.cons_append, IH]
```

### `to_e_list_cat` (TypeProgress.lean:159; Rocq type_progress.v:222-228) - PROVED

Earlier lemmas relied on: none. Induction on bes1, as Rocq.

```lean
  induction bes1 with
  | nil => rfl
  | cons a l IH => simp only [List.map_cons, List.cons_append, IH]
```

### `cat_split` (TypeProgress.lean:165; Rocq type_progress.v:231-244) - PROVED

Earlier lemmas relied on: none. `subst` then `List.take_left` / `List.drop_left` (Rocq inducts on l1; Lean closes it by the library lemmas).

```lean
  intro HCat
  subst HCat
  exact ⟨(List.take_left).symm, (List.drop_left).symm⟩
```

### `terminal_form_v_e` (TypeProgress.lean:172; Rocq type_progress.v:246-260) - PROVED

Earlier lemmas relied on: const_list_split (earlier, still sorry, outside this batch). As Rocq: `const_list_split` for the const_list branch; TRAP branch by cases on vs, the cons case contradicts `const_list` (TRAP is not const).

```lean
  intro HConst HTerm
  unfold terminal_form at HTerm ⊢
  rcases HTerm with H | H
  · left
    exact (const_list_split vs es H).2
  · cases vs with
    | nil =>
      right
      simpa using H
    | cons a vs' =>
      exfalso
      simp only [List.cons_append, List.cons.injEq] at H
      obtain ⟨rfl, _⟩ := H
      simp [const_list, is_const] at HConst
```

### `typeof_append` (TypeProgress.lean:188; Rocq type_progress.v:271-293) - PROVED

Earlier lemmas relied on: cat_split (same batch, proved here). As Rocq: `cat_split`, `map_take`/`map_drop` (Lean `List.map_take`/`List.map_drop` rewritten right-to-left), case on `drop`, `cat_take_drop` = `List.take_append_drop`.

```lean
  intro HMapType
  obtain ⟨H, H0⟩ := cat_split _ _ _ HMapType
  rw [← List.map_take] at H
  rw [← List.map_drop] at H0
  generalize hD : List.drop ts.length vs = D at H0
  cases D with
  | nil => simp at H0
  | cons v l =>
    cases l with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at H0
      refine ⟨v, ?_, H.symm, H0.symm⟩
      rw [← hD]
      exact (List.take_append_drop _ _).symm
    | cons v' l' => simp at H0
```

### `typeof_cat` (TypeProgress.lean:197; Rocq type_progress.v:295-317) - PROVED

Earlier lemmas relied on: typeof_append (same batch, proved here). As Rocq: induction on ts2 from the right (`List.reverseRecOn` = `last_ind`), uses `typeof_append`, then the IH.

```lean
  induction ts2 using List.reverseRecOn generalizing ts1 vs with
  | nil =>
    intro H
    refine ⟨vs, [], by simp, ?_, rfl⟩
    simpa using H
  | append_singleton ts2' t IH =>
    intro H
    rw [← List.append_assoc] at H
    obtain ⟨v, Hvs, H1, H2⟩ := typeof_append (ts1 ++ ts2') t vs H
    obtain ⟨vs1, vs2, Hvs', IH1, IH2⟩ := IH ts1 (List.take (ts1 ++ ts2').length vs) H1
    refine ⟨vs1, vs2 ++ [v], ?_, IH1, ?_⟩
    · rw [← List.append_assoc, ← Hvs']
      exact Hvs
    · rw [List.map_append, IH2]
      show ts2' ++ [typeof v] = ts2' ++ [t]
      rw [H2]
```

### `invert_typeof_I32` (TypeProgress.lean:209; Rocq type_progress.v:416-432) - PROVED

Earlier lemmas relied on: none. Case split on `v` / numtype / `Hwf` (wf_num_ inversion) as Rocq; binder-slot note: `wf_num_`'s first index is promoted to an inductive parameter so `num__case_0` has 5 slots, `num__case_1` 4.

```lean
  intro Ht Hwf
  cases v with
  | CONST nt n =>
    cases nt with
    | I32 =>
      cases Hwf with
      | val_case_0 _ _ Hn =>
        cases Hn with
        | num__case_0 vInn x _ _ hnt =>
          cases vInn with
          | I32 =>
            cases x with
            | mk_uN i => exact ⟨i, rfl⟩
          | I64 => cases hnt
        | num__case_1 vFnn x _ hnt =>
          cases vFnn <;> cases hnt
    | I64 => cases Ht
    | F32 => cases Ht
    | F64 => cases Ht
  | VCONST vt c => cases vt; cases Ht
  | REF_NULL rt => cases rt <;> cases Ht
  | REF_FUNC_ADDR _ => cases Ht
  | REF_HOST_ADDR _ => cases Ht
```

### `invert_typeof_I64` (TypeProgress.lean:217; Rocq type_progress.v:434-450) - PROVED

Earlier lemmas relied on: none. Same as I32.

```lean
  intro Ht Hwf
  cases v with
  | CONST nt n =>
    cases nt with
    | I64 =>
      cases Hwf with
      | val_case_0 _ _ Hn =>
        cases Hn with
        | num__case_0 vInn x _ _ hnt =>
          cases vInn with
          | I32 => cases hnt
          | I64 =>
            cases x with
            | mk_uN i => exact ⟨i, rfl⟩
        | num__case_1 vFnn x _ hnt =>
          cases vFnn <;> cases hnt
    | I32 => cases Ht
    | F32 => cases Ht
    | F64 => cases Ht
  | VCONST vt c => cases vt; cases Ht
  | REF_NULL rt => cases rt <;> cases Ht
  | REF_FUNC_ADDR _ => cases Ht
  | REF_HOST_ADDR _ => cases Ht
```

### `invert_typeof_numtype` (TypeProgress.lean:225; Rocq type_progress.v:452-465) - PROVED

Earlier lemmas relied on: none. Case split on v, nt, t; mismatches closed by `cases Ht`.

```lean
  intro Ht
  cases v with
  | CONST nt n =>
    cases nt <;> cases t <;> first | exact ⟨n, rfl⟩ | cases Ht
  | VCONST vt c => cases vt; cases t <;> cases Ht
  | REF_NULL rt => cases rt <;> cases t <;> cases Ht
  | REF_FUNC_ADDR _ => cases t <;> cases Ht
  | REF_HOST_ADDR _ => cases t <;> cases Ht
```

### `invert_typeof_numtype_wf` (TypeProgress.lean:232; Rocq type_progress.v:467-479) - PROVED

Earlier lemmas relied on: none. Same, plus `cases Hwf` (`val_case_0`) to extract `wf_num_`.

```lean
  intro Ht Hwf
  cases v with
  | CONST nt n =>
    cases nt <;> cases t <;>
      first
      | (cases Hwf with
         | val_case_0 _ _ Hn => exact ⟨n, rfl, Hn⟩)
      | cases Ht
  | VCONST vt c => cases vt; cases t <;> cases Ht
  | REF_NULL rt => cases rt <;> cases t <;> cases Ht
  | REF_FUNC_ADDR _ => cases t <;> cases Ht
  | REF_HOST_ADDR _ => cases t <;> cases Ht
```

### `invert_typeof_V128` (TypeProgress.lean:241; Rocq type_progress.v:482-496) - PROVED

Earlier lemmas relied on: none. Case split on v; VCONST case uses `val_case_1 _ _ _ h2` (4 slots: vectype, payload, size premise, wf_uN premise).

```lean
  intro Ht Hwf
  cases v with
  | CONST nt n => cases nt <;> cases Ht
  | VCONST vt c =>
    cases vt
    cases Hwf with
    | val_case_1 _ _ _ h2 => exact ⟨c, rfl, h2⟩
  | REF_NULL rt => cases rt <;> cases Ht
  | REF_FUNC_ADDR _ => cases Ht
  | REF_HOST_ADDR _ => cases Ht
```

## Final Lean check output (last lines)

`lake env lean Work.lean`: no output, exit 0 (all 14 proofs + 14 statement guards elaborate).

`lake env lean Merged.lean`: 0 lines other than the 13 pre-existing `declaration uses sorry` warnings (none for my 14 theorems).

`lake env lean Work2.lean` (`#print axioms`):

```
'TLC.concat_cancel_last_proof' depends on axioms: [propext]
'TLC.extract_list1_proof' depends on axioms: [propext]
'TLC.v_to_e_cat_proof' depends on axioms: [propext]
'TLC.be_to_e_cat_proof' depends on axioms: [propext]
'TLC.to_e_list_cat_proof' depends on axioms: [propext]
'TLC.cat_split_proof' does not depend on any axioms
'TLC.terminal_form_v_e_proof' depends on axioms: [propext, sorryAx]
'TLC.typeof_append_proof' depends on axioms: [propext]
'TLC.typeof_cat_proof' depends on axioms: [propext]
'TLC.invert_typeof_I32_proof' depends on axioms: [propext]
'TLC.invert_typeof_I64_proof' depends on axioms: [propext]
'TLC.invert_typeof_numtype_proof' does not depend on any axioms
'TLC.invert_typeof_numtype_wf_proof' depends on axioms: [propext]
'TLC.invert_typeof_V128_proof' depends on axioms: [propext]
```

(`sorryAx` in `terminal_form_v_e_proof` comes only from the earlier lemma `const_list_split`, still `sorry` in TypeProgress.lean.)

## Safety check at END (run from /home/zhengyew/spectec)

```
safety check [prove-H02] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T122348.279849962Z-prove-H02-1449626.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

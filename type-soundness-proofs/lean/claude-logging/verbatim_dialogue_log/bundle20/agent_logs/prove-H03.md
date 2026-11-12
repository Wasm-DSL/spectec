# prove-H03 log (bundle20 progress port, proof batch H03)

Agent label: `prove-H03`. Task: fill in the `sorry` bodies of 13 declarations of `TypeProgress.lean` (lines 250-359), porting `spectec/test-rocq/theories/type_progress.v:498-770`. Nothing in the repo was edited by this agent; the proofs below are for the main thread to merge.

Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H03/` (`Work.lean`: per-target `_proof` copies with the header-copy + `rfl` statement guard; `Work2.lean`: same plus concrete I/O checks; `Merged.lean`: excerpt of the real `TypeProgress.lean` (lines 1 to the end of `not_lf_br_left`) with the 13 proof bodies spliced in; `proofs/*.txt`: the final bodies).

## Safety check at START (run from /home/zhengyew/spectec)

```
bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-H03
safety check [prove-H03] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T122400.513756392Z-prove-H03-1449768.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Results (13 targets, all proved)

Method: for every target the header was copied verbatim into `Work.lean` as `<name>_proof`, with the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl` (all 13 guards pass, so the tactic blocks drop into the real file unchanged). Then all 13 bodies were spliced into an excerpt of the real `TypeProgress.lean` (`Merged.lean`) and compiled in place: exit 0, no errors, and no remaining `sorry` among the 13 targets.

### `invert_typeof_reftype` (theorem, TypeProgress.lean:250; Rocq type_progress.v:498-528) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  intro Ht
  cases v with
  | CONST nt n =>
    cases nt <;> cases t <;> simp [typeof, valtype_numtype, valtype_reftype] at Ht
  | VCONST vt c =>
    cases vt; cases t <;> simp [typeof, valtype_vectype, valtype_reftype] at Ht
  | REF_NULL rt =>
    left
    cases rt <;> cases t <;> simp [typeof, valtype_reftype, admininstr_val] at Ht ⊢
  | REF_FUNC_ADDR x => exact Or.inr ⟨x, Or.inl rfl⟩
  | REF_HOST_ADDR x => exact Or.inr ⟨x, Or.inr rfl⟩
```

Case split on `v` as in Rocq (`destruct v`, then `destruct v_numtype/v_vectype, t; try discriminate`). The `CONST`/`VCONST` cases are contradictions (`valtype_numtype nt = valtype_reftype t` / `valtype_vectype vt = valtype_reftype t` are different constructors); `REF_NULL rt` goes left (only the matching `rt = t` pairs survive `simp ... at Ht ⊢`); `REF_FUNC_ADDR x`/`REF_HOST_ADDR x` go right with witness `x`. Axioms: propext.

### `invert_typeof_reftype'` (theorem, TypeProgress.lean:259; Rocq type_progress.v:530-554) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  intro Ht
  cases v with
  | CONST nt n =>
    cases nt <;> cases t <;> simp [typeof, valtype_numtype, valtype_reftype] at Ht
  | VCONST vt c =>
    cases vt; cases t <;> simp [typeof, valtype_vectype, valtype_reftype] at Ht
  | REF_NULL rt => exact ⟨ref.REF_NULL rt, rfl⟩
  | REF_FUNC_ADDR x => exact ⟨ref.REF_FUNC_ADDR x, rfl⟩
  | REF_HOST_ADDR x => exact ⟨ref.REF_HOST_ADDR x, rfl⟩
```

Same case split. Rocq's `REF_NULL` case picks `ref_REF_NULL FUNCREF`/`EXTERNREF` by `t`; Lean takes `ref.REF_NULL rt` directly (`admininstr_val (val.REF_NULL rt) = admininstr_ref (ref.REF_NULL rt)` is `rfl`), so the typing hypothesis is only needed for the `CONST`/`VCONST` contradictions. Axioms: propext.

### `list_slice_size` (theorem, TypeProgress.lean:270; Rocq type_progress.v:560-584) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  intro H
  rw [List.length_take, List.length_drop]
  omega
```

Lean way instead of Rocq's `N.peano_ind` double induction: `List.length_take`, `List.length_drop` give `min j (bs.length - i) = j`, which `omega` discharges from `i + j <= bs.length`. Axioms: propext, Quot.sound.

### `split_vals_inverse` (theorem, TypeProgress.lean:309; Rocq type_progress.v:629-650) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  induction es generalizing vs es' with
  | nil =>
    intro H
    simp only [split_vals, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    rfl
  | cons e es ih =>
    intro H
    cases e <;> simp only [split_vals, Prod.mk.injEq] at H <;>
      (try (obtain ⟨rfl, rfl⟩ := H; rfl)) <;>
      (obtain ⟨rfl, rfl⟩ := H
       simp only [List.map_cons, admininstr_val, List.cons_append, List.cons.injEq, true_and]
       exact ih _ _ rfl)
```

Induction on `es` generalizing `vs es'`, as in Rocq. `nil`: `H` gives `vs = []`, `es' = []`. `cons`: `cases e`; for the non-value constructors the catch-all equation of `split_vals` gives `vs = []`, `es' = e :: es` and the goal is `rfl`; for the five value constructors `H` gives `vs = v :: (split_vals es).1`, `es' = (split_vals es).2` and the IH applies (`ih _ _ rfl`). Axioms: propext.

### `split_vals_prefix` (theorem, TypeProgress.lean:316; Rocq type_progress.v:652-664) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  intro H
  induction vs with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    cases e <;> simp_all [is_const, split_vals]
  | cons v vs ih =>
    show split_vals (admininstr_val v :: (List.map admininstr_val vs ++ ([e] ++ es))) = (v :: vs, [e] ++ es)
    cases v <;> simp only [admininstr_val, split_vals, ih]
```

Induction on `vs`, as in Rocq (`elim: vs`). `nil`: `cases e`; value constructors contradict `H : not (is_const e = true)`, the others are the catch-all case of `split_vals`. `cons`: `show` exposes `admininstr_val v :: (map ... ++ ([e] ++ es))` (a plain `simp only [List.cons_append]` would also rewrite `[e] ++ es` and break the match with the IH), then `cases v` and `simp only [admininstr_val, split_vals, ih]`. Axioms: propext.

### `br_reduce_decidable` (def, TypeProgress.lean:325; Rocq type_progress.v:666-690) -- proved

Earlier still-`sorry` lemmas used: `split_vals_prefix`, `split_vals_inverse`

```lean
  unfold br_reduce
  rcases Ees : split_vals es with ⟨vs, es'⟩
  rcases Ees' : es' with _ | ⟨e, es''⟩
  · refine isFalse ?_
    rintro ⟨vcs, l, es''', Hcontra⟩
    rw [Hcontra, split_vals_prefix vcs (admininstr.BR l) es''' (by simp [is_const])] at Ees
    have h2 := (Prod.mk.inj Ees).2
    rw [Ees'] at h2
    simp at h2
  · cases e with
    | BR l =>
      refine isTrue ⟨vs, l, es'', ?_⟩
      have h := split_vals_inverse vs es es' Ees
      rw [h, Ees']
      rfl
    | _ =>
      refine isFalse ?_
      rintro ⟨vcs, li, es''', Hcontra⟩
      rw [Hcontra, split_vals_prefix vcs (admininstr.BR li) es''' (by simp [is_const])] at Ees
      have h2 := (Prod.mk.inj Ees).2
      rw [Ees'] at h2
      simp at h2
```

CONSTRUCTIVE (computable): no `noncomputable` keyword needed (it compiled as a plain `def`, and `#eval` runs it, see the concrete I/O section). Mirrors Rocq: `rcases Ees : split_vals es with ⟨vs, es'⟩`, `rcases Ees' : es' with _ | ⟨e, es''⟩`. `es' = []`: `isFalse` (a witness `es = map vcs ++ ([BR l] ++ es''')` would make `split_vals es = (vcs, [BR l] ++ es''')` by `split_vals_prefix`, contradicting `es' = []`). `es' = e :: es''`: `cases e with | BR l => isTrue ... | _ => isFalse ...` (Lean's wildcard alternative replaces Rocq's `destruct e; try (...); all: left`). The two earlier lemmas it uses are PROVED in this batch (`split_vals_inverse` at 309, `split_vals_prefix` at 316), so once merged the def depends on axioms [propext] only (checked in Merged.lean). Not an `instance`.

### `return_reduce_decidable` (def, TypeProgress.lean:330; Rocq type_progress.v:692-715) -- proved

Earlier still-`sorry` lemmas used: `split_vals_prefix`, `split_vals_inverse`

```lean
  unfold return_reduce
  rcases Ees : split_vals es with ⟨vs, es'⟩
  rcases Ees' : es' with _ | ⟨e, es''⟩
  · refine isFalse ?_
    rintro ⟨vcs, es''', Hcontra⟩
    rw [Hcontra, split_vals_prefix vcs admininstr.RETURN es''' (by simp [is_const])] at Ees
    have h2 := (Prod.mk.inj Ees).2
    rw [Ees'] at h2
    simp at h2
  · cases e with
    | RETURN =>
      refine isTrue ⟨vs, es'', ?_⟩
      have h := split_vals_inverse vs es es' Ees
      rw [h, Ees']
      rfl
    | _ =>
      refine isFalse ?_
      rintro ⟨vcs, es''', Hcontra⟩
      rw [Hcontra, split_vals_prefix vcs admininstr.RETURN es''' (by simp [is_const])] at Ees
      have h2 := (Prod.mk.inj Ees).2
      rw [Ees'] at h2
      simp at h2
```

Identical to `br_reduce_decidable` with `RETURN` (no label argument) in place of `BR l`. Constructive/computable, no `noncomputable` needed. Same earlier lemmas (both proved in this batch). Axioms: propext.

### `not_br_reduce_not_lf_br` (theorem, TypeProgress.lean:334; Rocq type_progress.v:717-723) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  unfold br_reduce not_lf_br
  intro H1 vcs l es' H2
  exact H1 ⟨vcs, l, es', H2⟩
```

`unfold br_reduce not_lf_br`, then the witness `(vcs, l, es')` refutes the premise. Axiom-free.

### `not_return_reduce_not_lf_return` (theorem, TypeProgress.lean:339; Rocq type_progress.v:725-731) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  unfold return_reduce not_lf_return
  intro H1 vcs es' H2
  exact H1 ⟨vcs, es', H2⟩
```

As above with `return_reduce`/`not_lf_return`. Axiom-free.

### `not_lf_br_singleton` (theorem, TypeProgress.lean:344; Rocq type_progress.v:733-739) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  intro H Hcontra
  subst Hcontra
  exact H [] l [] (by simp)
```

`subst` the equation `e = BR l`, instantiate `not_lf_br [BR l]` at `([], l, [])`; the side goal `[BR l] = map _ [] ++ ([BR l] ++ [])` is `by simp`. Axioms: propext.

### `not_lf_return_singleton` (theorem, TypeProgress.lean:349; Rocq type_progress.v:741-747) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  intro H Hcontra
  subst Hcontra
  exact H [] [] (by simp)
```

Same with `RETURN`. Axioms: propext.

### `not_lf_br_right` (theorem, TypeProgress.lean:353; Rocq type_progress.v:749-758) -- proved

Earlier still-`sorry` lemmas used: none

```lean
  unfold not_lf_br
  intro Hnotbr vcs l es' Hcontra
  apply Hnotbr vcs l (es' ++ es2)
  rw [Hcontra]
  simp only [List.append_assoc]
```

As in Rocq: instantiate the hypothesis at `(vcs, l, es' ++ es2)`, rewrite with `Hcontra` and reassociate (`List.append_assoc`; Rocq's `-2!catA`). Axioms: propext.

### `not_lf_br_left` (theorem, TypeProgress.lean:359; Rocq type_progress.v:760-770) -- proved

Earlier still-`sorry` lemmas used: `const_es_exists`

```lean
  unfold not_lf_br
  intro Hconst Hnotbr vcs l es' Hcontra
  obtain ⟨vs1, Hvs1⟩ := const_es_exists es1 Hconst
  apply Hnotbr (vs1 ++ vcs) l es'
  rw [Hvs1, Hcontra]
  simp only [List.map_append, List.append_assoc]
```

As in Rocq: `const_es_exists` turns `const_list es1 = true` into `es1 = map admininstr_val vs1`; instantiate the hypothesis at `(vs1 ++ vcs, l, es')`, rewrite with `Hvs1`, `Hcontra` and reassociate (`List.map_append`, `List.append_assoc`; Rocq's `-v_to_e_cat -catA`). Uses the EARLIER, still-`sorry` lemma `const_es_exists` (TypeProgress.lean:110; its statement is fixed, it is proved in another batch), hence `sorryAx` in `#print axioms` until that one lands.

## Concrete I/O of the two decision procedures (Work2.lean, `#eval`, verified output)

`z := uN.mk_uN 0 : labelidx`, `c := admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 7))`; the match returns "true" on `isTrue _` and "false" on `isFalse _`.

```
br_reduce_decidable      []                       -> false
br_reduce_decidable      [BR z]                   -> true
br_reduce_decidable      [c, c, BR z, NOP]        -> true    (vcs = [c, c], es' = [NOP])
br_reduce_decidable      [c, NOP, BR z]           -> false   (BR is behind a non-value)
br_reduce_decidable      [c, c]                   -> false
return_reduce_decidable  []                       -> false
return_reduce_decidable  [RETURN]                 -> true
return_reduce_decidable  [c, RETURN, c]           -> true
return_reduce_decidable  [BR z]                   -> false
return_reduce_decidable  [c, TRAP, RETURN]        -> false
```

## Final Lean check output (last lines)

Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean /tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H03/Merged.lean` (excerpt of the real file with the 13 bodies in place; `#print axioms` for the 13 targets appended). Output, with the 27 `declaration uses 'sorry'` warnings of the other batches' declarations in the excerpt filtered out, followed by the exit status:

```
'TLC.invert_typeof_reftype' depends on axioms: [propext]
'TLC.invert_typeof_reftype'' depends on axioms: [propext]
'TLC.list_slice_size' depends on axioms: [propext, Quot.sound]
'TLC.split_vals_inverse' depends on axioms: [propext]
'TLC.split_vals_prefix' depends on axioms: [propext]
'TLC.br_reduce_decidable' depends on axioms: [propext]
'TLC.return_reduce_decidable' depends on axioms: [propext]
'TLC.not_br_reduce_not_lf_br' does not depend on any axioms
'TLC.not_return_reduce_not_lf_return' does not depend on any axioms
'TLC.not_lf_br_singleton' depends on axioms: [propext]
'TLC.not_lf_return_singleton' depends on axioms: [propext]
'TLC.not_lf_br_right' depends on axioms: [propext]
'TLC.not_lf_br_left' depends on axioms: [propext, sorryAx]
exit=0
```

`Work.lean` (guards + `#print axioms` of the `_proof` copies): exit=0, no errors, no warnings. The `_proof` copies of `br_reduce_decidable`/`return_reduce_decidable`/`not_lf_br_left` show `sorryAx` there only because they reference the real, still-`sorry` `split_vals_prefix`/`split_vals_inverse`/`const_es_exists` of the imported `TypeProgress`; in `Merged.lean` (where the first two are proved) only `not_lf_br_left` retains it, via `const_es_exists`.

## Ordering rule

Every declaration a body uses comes before its target in `TypeProgress.lean`: `typeof` (178), `is_const` (70), `const_es_exists` (110), `br_reduce`/`return_reduce`/`not_lf_br`/`not_lf_return`/`split_vals` (279-299), `split_vals_inverse` (309), `split_vals_prefix` (316). There are no `@[simp]` attributes, `open`s or `set_option`s in `TypeProgress.lean`, so the `simp` calls behave the same in the real file as in the scratch files.

## Notes for the main thread

- Bodies are indented by 2 spaces (as they appear after `:= by` on the next line). No header changes. No `noncomputable` needed anywhere (both `Decidable` defs are computable). No new axioms, no `native_decide`/`sorry`/`admit`; axioms used: `propext` (and `Quot.sound` for `list_slice_size`), both standard Lean core axioms; no HelperLemmas axioms.
- Only earlier-`sorry` dependency: `not_lf_br_left` -> `const_es_exists`.

## Safety check at END (run from /home/zhengyew/spectec)

```
bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" prove-H03
safety check [prove-H03] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T122943.500187024Z-prove-H03-1453812.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

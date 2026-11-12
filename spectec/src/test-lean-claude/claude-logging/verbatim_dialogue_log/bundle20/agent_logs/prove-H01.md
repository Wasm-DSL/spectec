# prove-H01 (bundle20 progress port, proof batch H01)

Targets: `cat_nil`, `LOCAL_injective`, `default_not_none`, `wf_config_app`, `v_to_e_const`, `const_list_cat`, `const_list_concat`, `const_list_split`, `const_es_exists`, `map_eq_nil`, `map_neq_nil`, `reduce_trap_left`, `v_e_trap` (TypeProgress.lean:49-131).
No repo file was edited. Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H01/`. Only my own log file was written inside the target dir (plus the safety-check output files the check script itself creates).

## Safety check at START
```
safety check [prove-H01] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T121953.844455783Z-prove-H01-1446504.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- `Work.lean` (scratch): header of each target copied verbatim from TypeProgress.lean, theorem renamed `<name>_proof`, plus guard `example : type_of% @<name>_proof = type_of% @<name> := rfl`. Negative control (`Neg.lean`, guard against a different statement) correctly FAILS, so the guard mechanism is live.
- `Head.lean` (scratch): merge simulation = the first 134 lines of the real TypeProgress.lean with all 13 proofs substituted for `sorry`, compiled with `lake env lean` against the same imports. It compiles with NO `sorryAx` anywhere, so the tactic blocks are valid in the real file (ordering rule satisfied: only earlier declarations are used).
- One Lean process at a time, `lake env lean` only (never `lake build`).
- Axioms: only the standard ones (`propext`, and `Classical.choice`/`Quot.sound` which enter only through the constants `wf_config`/`Step_pure` in the statements). No project `axiom` from HelperLemmas was used. No `sorry`, `admit`, `native_decide`, new axioms.

## Results
### `cat_nil` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  constructor
  · intro h
    cases s1 with
    | nil => exact ⟨rfl, h⟩
    | cons a l => cases h
  · rintro ⟨rfl, rfl⟩
    rfl
```

### `LOCAL_injective` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  intro x y H
  injection H
```

### `default_not_none` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  intro HForall t ht
  have h := HForall t ht
  cases t with
  | BOT => exact absurd rfl h
  | _ => simp [default_]
```

### `wf_config_app` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  constructor
  · intro H
    cases H with
    | config_case_0 _ _ hs hf =>
      refine ⟨wf_config.config_case_0 _ _ hs ?_, wf_config.config_case_0 _ _ hs ?_⟩
      · intro x hx; exact hf x (List.mem_append_left _ hx)
      · intro x hx; exact hf x (List.mem_append_right _ hx)
  · rintro ⟨H1, H2⟩
    cases H1 with
    | config_case_0 _ _ hs hf1 =>
      cases H2 with
      | config_case_0 _ _ _ hf2 =>
        refine wf_config.config_case_0 _ _ hs ?_
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hf1 x h
        · exact hf2 x h
```

### `v_to_e_const` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, const_list, List.all_cons, Bool.and_eq_true] at ih ⊢
    refine ⟨?_, ih⟩
    cases v <;> rfl
```

### `const_list_cat` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  unfold const_list
  exact List.all_append
```

### `const_list_concat` : proved
Still-`sorry` earlier lemmas relied on: `const_list_cat`.
```lean
  intro Hconst1 Hconst2
  rw [const_list_cat, Hconst1, Hconst2]
  rfl
```

### `const_list_split` : proved
Still-`sorry` earlier lemmas relied on: `const_list_cat`.
```lean
  intro Hconst
  rw [const_list_cat] at Hconst
  exact Bool.and_eq_true_iff.mp Hconst
```

### `const_es_exists` : proved
Still-`sorry` earlier lemmas relied on: const_list_split (and through it const_list_cat).
```lean
  induction es with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a es ih =>
    intro HConst
    obtain ⟨ha, hes⟩ := const_list_split [a] es HConst
    obtain ⟨vs, rfl⟩ := ih hes
    have ha' : is_const a = true := by simpa [const_list] using ha
    cases a with
    | CONST t n => exact ⟨val.CONST t n :: vs, rfl⟩
    | VCONST t v => exact ⟨val.VCONST t v :: vs, rfl⟩
    | REF_NULL t => exact ⟨val.REF_NULL t :: vs, rfl⟩
    | REF_FUNC_ADDR a => exact ⟨val.REF_FUNC_ADDR a :: vs, rfl⟩
    | REF_HOST_ADDR a => exact ⟨val.REF_HOST_ADDR a :: vs, rfl⟩
    | _ => simp [is_const] at ha'
```

### `map_eq_nil` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  intro h
  cases l with
  | nil => rfl
  | cons a l => cases h
```

### `map_neq_nil` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  intro h hl
  subst hl
  exact h rfl
```

### `reduce_trap_left` : proved
Still-`sorry` earlier lemmas relied on: `const_es_exists`, `map_neq_nil`.
```lean
  intro HConst H
  obtain ⟨vcs, rfl⟩ := const_es_exists vs HConst
  exact Step_pure.trap_vals vcs [] (Or.inl (map_neq_nil admininstr_val vcs H))
```

### `v_e_trap` : proved
Still-`sorry` earlier lemmas relied on: none.
```lean
  intro HConst H
  cases vs with
  | nil => exact ⟨rfl, H⟩
  | cons v vs =>
    cases vs with
    | nil =>
      have hv : is_const v = true := by simpa [const_list] using HConst
      have hv' : v = admininstr.TRAP := (List.cons.inj H).1
      subst hv'
      simp [is_const] at hv
    | cons v' vs' => simp at H
```

Notes:
- `Map` (wasm2.0) is a plain def `xs.map f`, so `Step_pure.trap_vals vcs []` (stated with `Map (fun v => admininstr_val v) vcs ++ ([TRAP] ++ [])`) is accepted by `exact` for the goal `List.map admininstr_val vcs ++ [TRAP]` by defeq.
- `const_es_exists` is the `∃` (Prop) version as stated in the Lean file; the Rocq `sig` deviation is already documented in the docstring.
- `default_not_none`: `Forall` here is the `∀ x ∈ l` def (not an inductive), so the Rocq `induction HForall` is replaced by a pointwise argument; BOT case contradicts the hypothesis, all other valtypes have `default_ = some _`.

## Final Lean check output (Work.lean with rfl guards + `#print axioms`, `lake env lean`, exit 0, no errors/warnings, ~2 s)
```
'TLC.cat_nil_proof' does not depend on any axioms
'TLC.LOCAL_injective_proof' does not depend on any axioms
'TLC.default_not_none_proof' depends on axioms: [propext]
'TLC.wf_config_app_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.v_to_e_const_proof' depends on axioms: [propext]
'TLC.const_list_cat_proof' depends on axioms: [propext]
'TLC.const_list_concat_proof' depends on axioms: [propext, sorryAx]   -- sorryAx only via still-sorry const_list_cat
'TLC.const_list_split_proof' depends on axioms: [propext, sorryAx]    -- via const_list_cat
'TLC.const_es_exists_proof' depends on axioms: [propext, sorryAx]     -- via const_list_split
'TLC.map_eq_nil_proof' does not depend on any axioms
'TLC.map_neq_nil_proof' does not depend on any axioms
'TLC.reduce_trap_left_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]   -- via const_es_exists, map_neq_nil
'TLC.v_e_trap_proof' depends on axioms: [propext]
```
Merge simulation (Head.lean, first 134 lines of real file with all proofs substituted), exit 0, no errors; `#print axioms` shows no `sorryAx` for any of the 13:
```
'TLC.cat_nil' does not depend on any axioms
'TLC.LOCAL_injective' does not depend on any axioms
'TLC.default_not_none' depends on axioms: [propext]
'TLC.wf_config_app' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.v_to_e_const' depends on axioms: [propext]
'TLC.const_list_cat' depends on axioms: [propext]
'TLC.const_list_concat' depends on axioms: [propext]
'TLC.const_list_split' depends on axioms: [propext]
'TLC.const_es_exists' depends on axioms: [propext]
'TLC.map_eq_nil' does not depend on any axioms
'TLC.map_neq_nil' does not depend on any axioms
'TLC.reduce_trap_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'TLC.v_e_trap' depends on axioms: [propext]
```

## Safety check at END (re-run after the last Lean command and after writing this log)
```
safety check [prove-H01] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T122337.220238575Z-prove-H01-1449314.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

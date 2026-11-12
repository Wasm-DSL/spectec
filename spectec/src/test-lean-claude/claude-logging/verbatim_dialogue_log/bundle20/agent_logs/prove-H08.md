# prove-H08 (bundle20 progress port, proof batch H08, 14 targets)

Agent label: prove-H08. Scope: fill the `sorry` bodies of the 14 listed declarations of `TypeProgress.lean` (lines 702-800), porting `spectec/test-rocq/theories/type_progress.v:1629-1872`. Nothing outside `spectec/src/test-lean-claude` was touched; the only repo-side writes are this log file and the safety-check files the verification script itself creates under `claude-logging/safety-checks/`. Scratch: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H08/` (`Work.lean` = header-copy + `rfl` guard form, `Merged.lean` = copy of TypeProgress.lean with the 14 proofs inlined, bodies in `bodies/*.txt`).

## Result: 14/14 proved (0 blocked, 0 skipped)

## Safety check (start)
```
safety check [prove-H08] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T123311.328509011Z-prove-H08-1456364.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method / verification

- Header-copy + guard workflow of the brief: `Work.lean` contains, for each target, the header copied verbatim from TypeProgress.lean (renamed `<name>_proof`), the proof, and `example : type_of% @<name>_proof = type_of% @<name> := rfl`. Compiles with exit 0 and no errors (the Mathlib name linter is disabled in the scratch file only, because of the `_proof` suffix).
- Stronger in-situ check: `Merged.lean` is a copy of the real `TypeProgress.lean` in which exactly the 14 `:= sorry` of the targets were replaced by `:= by <body>` (`diff` shows only those 14 lines removed). `lake env lean Merged.lean` exits without errors, the number of `declaration uses sorry` warnings drops by exactly 14 relative to the unmodified file's `:= sorry` count (244 -> 230 `:= sorry` occurrences), and none of the 14 target lines carries a sorry warning. This confirms the ordering rule (no forward references) and that the bodies drop in unchanged.
- No `sorry`/`admit`/`native_decide`/new axioms in any body (grep-checked). Only `decide` (kernel-checked) is used.
- One Lean process at a time; each run takes ~2-3 s (`import TypeProgress`).

## Shared structure of the numeric proofs

Rocq's Ltac `num_shapes` (inversion of `wf_binop_`/`wf_num_`/... and destruct of every `Inn`/`Fnn`, then `try discriminate`) is rendered with `rcases` on the generated `wf_*` inductives plus three local helper facts proved at the start of each proof (`numI`: `numtype_Inn` injective, `numF`: `numtype_Fnn` injective, `numIF`: `numtype_Inn I ≠ numtype_Fnn F`), because after `rcases` the numtype equations are `numtype_Inn I = numtype_Inn I1` with an opaque `Inn` variable (a plain `cases`/`subst` would fail on them). Slot note: for `rcases`/`cases` on `wf_binop_`/`wf_num_`/`wf_cvtop__` the leading index parameter (`v_numtype`) takes no slot, so patterns are `⟨I, bI, hI⟩` / `⟨I1, x1, hsz, hw1, h1⟩`. Rocq's `eexists; econstructor` is `apply Exists.intro; constructor` (the existential witness mvar is assigned by the constructor whose indices match; `refine ⟨_, ?_⟩` is NOT usable because `refine` rejects the unassigned `_`).

## wf_opt_num_

- status: **proved** (TypeProgress.lean:702; Rocq type_progress.v:1629-1638)
- earlier still-`sorry` TypeProgress lemmas relied on: none
- notes: Rocq: `[x|] Ho /=; last by split; Forall_nil` then `inversion Ho`, `num__case_0`. Lean: `cases o`; the `some` case needs `wf_num_.num__case_0` whose `wf_uN` size is `(size (valtype_Inn I)).get!` while the hypothesis has `sizenn (numtype_Inn I)`; these agree only after `cases I`, so `cases I <;> exact ...`. `OMap f o` unfolds to `Option.map f o` (defeq). Axioms: propext only.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Ho
  cases o with
  | none => exact ⟨fun x hx => by simp at hx, fun x hx => by simp [list_] at hx⟩
  | some x =>
    have Hx : wf_num_ (numtype_Inn I) (num_.mk_num__0 I x) := by
      cases I <;> exact wf_num_.num__case_0 _ _ _ (by decide) (Ho x (by simp)) rfl
    constructor
    · intro y hy
      simp at hy
      subst hy
      exact Hx
    · intro y hy
      simp [list_] at hy
      subst hy
      exact Hx
```

## binop_total

- status: **proved** (TypeProgress.lean:712; Rocq type_progress.v:1663-1689)
- earlier still-`sorry` TypeProgress lemmas relied on: idiv_total, irem_total, idiv_wf, wf_fN_num_, wf_opt_num_ (proved in this batch)
- notes: Port of Rocq: `num_shapes` (inversion of the three wf hypotheses + destruct Inn/Fnn) is done with `rcases` + three local injectivity helpers `numI`/`numF`/`numIF` (`numtype_Inn`/`numtype_Fnn` injective / disjoint); DIV/REM cases supply `idiv_total`/`irem_total` + `idiv_wf`/`irem__is_wf` + `wf_opt_num_` and the explicit constructors `fun_binop__case_6..9` (Rocq's `match goal`); the other cases are Rocq's `eexists; econstructor; binop_wf` = `apply Exists.intro; constructor` followed by `first` over the operator `*_is_wf` lemmas (`wf_fN_num_` for floats). SHL/SHR use the project axioms `ishl_wf`/`ishr_wf` for BOTH I32 and I64 (Rocq used `ishl__is_wf`+`wf_uN_mk_proj` for I32 and the axioms only for I64; the axioms apply for any shift amount so `wf_uN_mk_proj` is not needed). Imported baseline-`sorry` generated lemmas used (wasm2.0.lean): iand__is_wf, ior__is_wf, ixor__is_wf, irotl__is_wf, irotr__is_wf, fadd__is_wf, fsub__is_wf, fmul__is_wf, fdiv__is_wf, fmin__is_wf, fmax__is_wf, fcopysign__is_wf (same lemmas Rocq's `binop_wf` uses). Other imported lemmas: iadd__is_wf, isub__is_wf, imul__is_wf, irem__is_wf (proved). Axioms: propext, Classical.choice, Quot.sound, sorryAx (from the sorry lemmas above), TLC.ishl_wf, TLC.ishr_wf (HelperLemmas axioms = Rocq axioms.v:83,85).

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 hn2 hb
  rcases hb with ⟨I, bI, hI⟩ | ⟨F, bF, hF⟩
  · subst hI
    rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    rcases hn2 with ⟨I2, x2, _, hw2, h2⟩ | ⟨F2, x2, _, h2⟩
    swap
    · exact (numIF _ _ h2).elim
    obtain rfl := numI _ _ h2
    cases bI with
    | DIV sx =>
      cases I
      · obtain ⟨r, Hr⟩ := idiv_total _ sx x1 x2 hw1 hw2
        have Hw := idiv_wf _ _ _ _ _ Hr
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I32 r Hw
        exact ⟨_, fun_binop_.fun_binop__case_6 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1⟩
      · obtain ⟨r, Hr⟩ := idiv_total _ sx x1 x2 hw1 hw2
        have Hw := idiv_wf _ _ _ _ _ Hr
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I64 r Hw
        exact ⟨_, fun_binop_.fun_binop__case_7 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1⟩
    | REM sx =>
      cases I
      · obtain ⟨r, Hr⟩ := irem_total _ sx x1 x2 hw1 hw2
        have Hw := irem__is_wf _ _ _ _ _ _ Hr hw1 hw2 rfl
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I32 r Hw
        exact ⟨_, fun_binop_.fun_binop__case_8 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1⟩
      · obtain ⟨r, Hr⟩ := irem_total _ sx x1 x2 hw1 hw2
        have Hw := irem__is_wf _ _ _ _ _ _ Hr hw1 hw2 rfl
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I64 r Hw
        exact ⟨_, fun_binop_.fun_binop__case_9 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1⟩
    | _ =>
      cases I <;> apply Exists.intro <;> constructor <;>
        refine wf_num_.num__case_0 _ _ _ (by decide) ?_ rfl <;>
        first
          | exact iadd__is_wf _ _ _ _ hw1 hw2 rfl
          | exact isub__is_wf _ _ _ _ hw1 hw2 rfl
          | exact imul__is_wf _ _ _ _ hw1 hw2 rfl
          | exact iand__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ior__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ixor__is_wf _ _ _ _ hw1 hw2 rfl
          | exact irotl__is_wf _ _ _ _ hw1 hw2 rfl
          | exact irotr__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ishl_wf _ _ _ hw1
          | exact ishr_wf _ _ _ _ hw1
  · subst hF
    rcases hn1 with ⟨I1, x1, _, _, h1⟩ | ⟨F1, x1, hw1, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    rcases hn2 with ⟨I2, x2, _, _, h2⟩ | ⟨F2, x2, hw2, h2⟩
    · exact (numIF _ _ h2.symm).elim
    obtain rfl := numF _ _ h2
    cases F <;> cases bF <;> apply Exists.intro <;> constructor <;> (try apply wf_fN_num_) <;>
      first
        | exact fadd__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fsub__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmul__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fdiv__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmin__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmax__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fcopysign__is_wf _ _ _ _ hw1 hw2 rfl
```

## relop_total

- status: **proved** (TypeProgress.lean:718; Rocq type_progress.v:1691-1713)
- earlier still-`sorry` TypeProgress lemmas relied on: ilt_total, igt_total, ile_total, ige_total
- notes: Same shape-inversion prelude as binop_total. LT/GT/LE/GE: obtain `c` from `ilt_total`/`igt_total`/`ile_total`/`ige_total`, then explicit constructors `fun_relop__case_4..11`; EQ/NE and all float cases: `apply Exists.intro; constructor` (Rocq's `eexists; econstructor`). Axioms: propext, sorryAx (from ilt_total etc.).

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 hn2 hr
  rcases hr with ⟨I, rI, hI⟩ | ⟨F, rF, hF⟩
  · subst hI
    rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    rcases hn2 with ⟨I2, x2, _, hw2, h2⟩ | ⟨F2, x2, _, h2⟩
    swap
    · exact (numIF _ _ h2).elim
    obtain rfl := numI _ _ h2
    cases rI with
    | LT sx =>
      cases I
      · obtain ⟨c, Hc⟩ := ilt_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_4 sx x1 x2 c Hc⟩
      · obtain ⟨c, Hc⟩ := ilt_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_5 sx x1 x2 c Hc⟩
    | GT sx =>
      cases I
      · obtain ⟨c, Hc⟩ := igt_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_6 sx x1 x2 c Hc⟩
      · obtain ⟨c, Hc⟩ := igt_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_7 sx x1 x2 c Hc⟩
    | LE sx =>
      cases I
      · obtain ⟨c, Hc⟩ := ile_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_8 sx x1 x2 c Hc⟩
      · obtain ⟨c, Hc⟩ := ile_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_9 sx x1 x2 c Hc⟩
    | GE sx =>
      cases I
      · obtain ⟨c, Hc⟩ := ige_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_10 sx x1 x2 c Hc⟩
      · obtain ⟨c, Hc⟩ := ige_total _ sx x1 x2 hw1 hw2
        exact ⟨_, fun_relop_.fun_relop__case_11 sx x1 x2 c Hc⟩
    | _ => cases I <;> apply Exists.intro <;> constructor
  · subst hF
    rcases hn1 with ⟨I1, x1, _, _, h1⟩ | ⟨F1, x1, hw1, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    rcases hn2 with ⟨I2, x2, _, _, h2⟩ | ⟨F2, x2, hw2, h2⟩
    · exact (numIF _ _ h2.symm).elim
    obtain rfl := numF _ _ h2
    cases F <;> cases rF <;> apply Exists.intro <;> constructor
```

## cvtop_total

- status: **proved** (TypeProgress.lean:724; Rocq type_progress.v:1715-1733)
- earlier still-`sorry` TypeProgress lemmas relied on: none
- notes: Rocq: `inversion Hcvt; inversion Hc1; ... destruct Inn/Fnn; try discriminate; eexists; econstructor`. Lean: `rcases` on the 4 `wf_cvtop__` constructors, `subst` the numtype equations, invert `wf_num_` with the helper injectivity lemmas, `cases` on the conversion operator and on Inn/Fnn, then `apply Exists.intro; constructor`. For the two REINTERPRET families the size equation `hsz` from `wf_cvtop__*_case_1/2` kills the mismatched (Inn,Fnn) combinations (`exfalso; revert hsz; decide`, Rocq's `try discriminate`) and `decide` discharges the constructor's side premises (`size .. ≠ none`, `get! = get!`) for the matching ones. Axioms: propext only (no sorry).

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hc1 hcvt
  rcases hcvt with ⟨I1, I2, x, hx, e1, e2⟩ | ⟨I1, F2, x, hx, e1, e2⟩ |
      ⟨F1, I2, x, hx, e1, e2⟩ | ⟨F1, F2, x, hx, e1, e2⟩
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, hw, h1⟩ | ⟨F1', y, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    cases x <;> cases I1 <;> cases I2 <;> apply Exists.intro <;> constructor
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, hw, h1⟩ | ⟨F1', y, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    cases x with
    | CONVERT sx => cases I1 <;> cases F2 <;> apply Exists.intro <;> constructor
    | REINTERPRET =>
      cases hx with
      | cvtop__Inn_1_Fnn_2_case_1 hsz =>
        cases I1 <;> cases F2 <;>
          first
            | (exfalso; revert hsz; decide)
            | (apply Exists.intro; constructor <;> decide)
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, _, h1⟩ | ⟨F1', y, hw, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    cases x with
    | TRUNC sx => cases F1 <;> cases I2 <;> apply Exists.intro <;> constructor
    | TRUNC_SAT sx => cases F1 <;> cases I2 <;> apply Exists.intro <;> constructor
    | REINTERPRET =>
      cases hx with
      | cvtop__Fnn_1_Inn_2_case_2 hsz =>
        cases F1 <;> cases I2 <;>
          first
            | (exfalso; revert hsz; decide)
            | (apply Exists.intro; constructor <;> decide)
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, _, h1⟩ | ⟨F1', y, hw, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    cases x <;> cases F1 <;> cases F2 <;> apply Exists.intro <;> constructor
```

## binop_before

- status: **proved** (TypeProgress.lean:731; Rocq type_progress.v:1735-1759)
- earlier still-`sorry` TypeProgress lemmas relied on: idiv_total, irem_total, idiv_wf, wf_fN_num_, wf_opt_num_ (proved in this batch)
- notes: Same proof as binop_total but the goal is the inductive `fun_binop__before_fun_binop__case_38` itself (no existential): `constructor`, and the explicit constructors `fun_binop__before_fun_binop__case_38.fun_binop__case_6..9` for DIV/REM. Same imported baseline-sorry lemmas and axioms as binop_total.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 hn2 hb
  rcases hb with ⟨I, bI, hI⟩ | ⟨F, bF, hF⟩
  · subst hI
    rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    rcases hn2 with ⟨I2, x2, _, hw2, h2⟩ | ⟨F2, x2, _, h2⟩
    swap
    · exact (numIF _ _ h2).elim
    obtain rfl := numI _ _ h2
    cases bI with
    | DIV sx =>
      cases I
      · obtain ⟨r, Hr⟩ := idiv_total _ sx x1 x2 hw1 hw2
        have Hw := idiv_wf _ _ _ _ _ Hr
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I32 r Hw
        exact fun_binop__before_fun_binop__case_38.fun_binop__case_6 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1
      · obtain ⟨r, Hr⟩ := idiv_total _ sx x1 x2 hw1 hw2
        have Hw := idiv_wf _ _ _ _ _ Hr
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I64 r Hw
        exact fun_binop__before_fun_binop__case_38.fun_binop__case_7 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1
    | REM sx =>
      cases I
      · obtain ⟨r, Hr⟩ := irem_total _ sx x1 x2 hw1 hw2
        have Hw := irem__is_wf _ _ _ _ _ _ Hr hw1 hw2 rfl
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I32 r Hw
        exact fun_binop__before_fun_binop__case_38.fun_binop__case_8 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1
      · obtain ⟨r, Hr⟩ := irem_total _ sx x1 x2 hw1 hw2
        have Hw := irem__is_wf _ _ _ _ _ _ Hr hw1 hw2 rfl
        obtain ⟨Ho1, Ho2⟩ := wf_opt_num_ Inn.I64 r Hw
        exact fun_binop__before_fun_binop__case_38.fun_binop__case_9 sx x1 x2 r Hr Ho2 (by decide) Hw Ho1
    | _ =>
      cases I <;> constructor <;>
        refine wf_num_.num__case_0 _ _ _ (by decide) ?_ rfl <;>
        first
          | exact iadd__is_wf _ _ _ _ hw1 hw2 rfl
          | exact isub__is_wf _ _ _ _ hw1 hw2 rfl
          | exact imul__is_wf _ _ _ _ hw1 hw2 rfl
          | exact iand__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ior__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ixor__is_wf _ _ _ _ hw1 hw2 rfl
          | exact irotl__is_wf _ _ _ _ hw1 hw2 rfl
          | exact irotr__is_wf _ _ _ _ hw1 hw2 rfl
          | exact ishl_wf _ _ _ hw1
          | exact ishr_wf _ _ _ _ hw1
  · subst hF
    rcases hn1 with ⟨I1, x1, _, _, h1⟩ | ⟨F1, x1, hw1, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    rcases hn2 with ⟨I2, x2, _, _, h2⟩ | ⟨F2, x2, hw2, h2⟩
    · exact (numIF _ _ h2.symm).elim
    obtain rfl := numF _ _ h2
    cases F <;> cases bF <;> constructor <;> (try apply wf_fN_num_) <;>
      first
        | exact fadd__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fsub__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmul__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fdiv__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmin__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fmax__is_wf _ _ _ _ hw1 hw2 rfl
        | exact fcopysign__is_wf _ _ _ _ hw1 hw2 rfl
```

## binop_not_none

- status: **proved** (TypeProgress.lean:737; Rocq type_progress.v:1761-1772)
- earlier still-`sorry` TypeProgress lemmas relied on: binop_before (proved in this batch)
- notes: Rocq: `inversion Hf; subst; try discriminate; exfalso; apply H; apply binop_before`. Lean: `intro ... hnone; subst hnone; cases hf` (the 38 `some` constructors are eliminated by `cases` since `some _ = none` is a constructor clash; only the catch-all `fun_binop__case_38` remains) then `exact hnb (binop_before ...)`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro hn1 hn2 hb hf hnone
  subst hnone
  cases hf with
  | fun_binop__case_38 _ _ _ _ hnb => exact hnb (binop_before _ _ _ _ hn1 hn2 hb)
```

## relop_before

- status: **proved** (TypeProgress.lean:746; Rocq type_progress.v:1774-1785)
- earlier still-`sorry` TypeProgress lemmas relied on: none
- notes: Same prelude as relop_total; `cases rI <;> cases I <;> constructor <;> exact uN.mk_uN 0` (the signed comparisons' constructors carry an unused `var_0 : uN` argument; Rocq's `try exact: (mk_uN 0%num)`). Float cases: `constructor`. Axioms: propext only (no sorry).

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 hn2 hr
  rcases hr with ⟨I, rI, hI⟩ | ⟨F, rF, hF⟩
  · subst hI
    rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    rcases hn2 with ⟨I2, x2, _, hw2, h2⟩ | ⟨F2, x2, _, h2⟩
    swap
    · exact (numIF _ _ h2).elim
    obtain rfl := numI _ _ h2
    cases rI <;> cases I <;> constructor <;> exact uN.mk_uN 0
  · subst hF
    rcases hn1 with ⟨I1, x1, _, _, h1⟩ | ⟨F1, x1, hw1, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    rcases hn2 with ⟨I2, x2, _, _, h2⟩ | ⟨F2, x2, hw2, h2⟩
    · exact (numIF _ _ h2.symm).elim
    obtain rfl := numF _ _ h2
    cases F <;> cases rF <;> constructor
```

## relop_not_none

- status: **proved** (TypeProgress.lean:752; Rocq type_progress.v:1787-1798)
- earlier still-`sorry` TypeProgress lemmas relied on: relop_before (proved in this batch)
- notes: Same pattern as binop_not_none with `fun_relop__case_24` and `relop_before`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro hn1 hn2 hr hf hnone
  subst hnone
  cases hf with
  | fun_relop__case_24 _ _ _ _ hnb => exact hnb (relop_before _ _ _ _ hn1 hn2 hr)
```

## cvtop_before

- status: **proved** (TypeProgress.lean:762; Rocq type_progress.v:1800-1822)
- earlier still-`sorry` TypeProgress lemmas relied on: none
- notes: Same as cvtop_total but the goal is `fun_cvtop___before_fun_cvtop___case_36` (`constructor` instead of `apply Exists.intro; constructor`). Axioms: propext only (no sorry).

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numF : ∀ F F' : Fnn, numtype_Fnn F = numtype_Fnn F' → F = F' := by
    intro F F' h; cases F <;> cases F' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hc1 hcvt
  rcases hcvt with ⟨I1, I2, x, hx, e1, e2⟩ | ⟨I1, F2, x, hx, e1, e2⟩ |
      ⟨F1, I2, x, hx, e1, e2⟩ | ⟨F1, F2, x, hx, e1, e2⟩
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, hw, h1⟩ | ⟨F1', y, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    cases x <;> cases I1 <;> cases I2 <;> constructor
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, hw, h1⟩ | ⟨F1', y, _, h1⟩
    swap
    · exact (numIF _ _ h1).elim
    obtain rfl := numI _ _ h1
    cases x with
    | CONVERT sx => cases I1 <;> cases F2 <;> constructor
    | REINTERPRET =>
      cases hx with
      | cvtop__Inn_1_Fnn_2_case_1 hsz =>
        cases I1 <;> cases F2 <;>
          first
            | (exfalso; revert hsz; decide)
            | (constructor <;> decide)
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, _, h1⟩ | ⟨F1', y, hw, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    cases x with
    | TRUNC sx => cases F1 <;> cases I2 <;> constructor
    | TRUNC_SAT sx => cases F1 <;> cases I2 <;> constructor
    | REINTERPRET =>
      cases hx with
      | cvtop__Fnn_1_Inn_2_case_2 hsz =>
        cases F1 <;> cases I2 <;>
          first
            | (exfalso; revert hsz; decide)
            | (constructor <;> decide)
  · subst e1 e2
    rcases hc1 with ⟨I1', y, _, _, h1⟩ | ⟨F1', y, hw, h1⟩
    · exact (numIF _ _ h1.symm).elim
    obtain rfl := numF _ _ h1
    cases x <;> cases F1 <;> cases F2 <;> constructor
```

## cvtop_not_none

- status: **proved** (TypeProgress.lean:768; Rocq type_progress.v:1824-1834)
- earlier still-`sorry` TypeProgress lemmas relied on: cvtop_before (proved in this batch)
- notes: Same pattern as binop_not_none with `fun_cvtop___case_36` and `cvtop_before`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro hc1 hcvt hf hnone
  subst hnone
  cases hf with
  | fun_cvtop___case_36 _ _ _ _ hnb => exact hnb (cvtop_before _ _ _ _ hc1 hcvt)
```

## testop_not_none

- status: **proved** (TypeProgress.lean:776; Rocq type_progress.v:1836-1850)
- earlier still-`sorry` TypeProgress lemmas relied on: none
- notes: Invert `wf_testop_` and `wf_num_` (only the Inn constructor survives via `numIF`), `cases tI` (only EQZ), `cases I <;> simp [fun_testop_, numtype_Inn]` (the match in `fun_testop_` reduces to `some _`). Axioms: propext only (no sorry).

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  have numI : ∀ I I' : Inn, numtype_Inn I = numtype_Inn I' → I = I' := by
    intro I I' h; cases I <;> cases I' <;> first | rfl | (exfalso; revert h; decide)
  have numIF : ∀ (I : Inn) (F : Fnn), numtype_Inn I = numtype_Fnn F → False := by
    intro I F h; cases I <;> cases F <;> (revert h; decide)
  intro hn1 ht
  rcases ht with ⟨I, tI, hI⟩
  subst hI
  rcases hn1 with ⟨I1, x1, _, hw1, h1⟩ | ⟨F1, x1, _, h1⟩
  swap
  · exact (numIF _ _ h1).elim
  obtain rfl := numI _ _ h1
  cases tI
  cases I <;> simp [fun_testop_, numtype_Inn]
```

## Forall_all

- status: **proved** (TypeProgress.lean:784; Rocq type_progress.v:1854-1857)
- earlier still-`sorry` TypeProgress lemmas relied on: none
- notes: `Forall P l` unfolds to `∀ x ∈ l, P x`, which is exactly `List.all_eq_true.mpr`. Axioms: propext, Quot.sound.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro h
  exact List.all_eq_true.mpr h
```

## all_Forall

- status: **proved** (TypeProgress.lean:789; Rocq type_progress.v:1858-1863)
- earlier still-`sorry` TypeProgress lemmas relied on: none
- notes: `List.all_eq_true.mp`. Axioms: propext, Quot.sound.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro h
  exact List.all_eq_true.mp h
```

## Forall_exists_Forall2

- status: **proved** (TypeProgress.lean:800; Rocq type_progress.v:1865-1872)
- earlier still-`sorry` TypeProgress lemmas relied on: none
- notes: Induction on `l`; the cons case builds `a :: la` and uses `List.zip_cons_cons` for the zip-based `Forall₂` (membership in `(a::la).zip (b::l)` = head pair or tail membership); length conjunct from the induction hypothesis (`simp [hlen]`). Statement is the Lean-adapted one with the length conjunct (see the docstring in TypeProgress.lean). Axioms: propext only.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  induction l with
  | nil =>
    intro _
    exact ⟨[], ⟨fun t ht => by simp at ht, rfl⟩, fun x hx => by simp at hx⟩
  | cons b l ih =>
    intro h
    obtain ⟨a, hr, hp⟩ := h b (by simp)
    obtain ⟨la, ⟨h2, hlen⟩, hp'⟩ := ih (fun x hx => h x (by simp [hx]))
    refine ⟨a :: la, ⟨?_, by simp [hlen]⟩, ?_⟩
    · intro t ht
      rw [List.zip_cons_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hr
      · exact h2 t ht
    · intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp
      · exact hp' x hx
```

## Final Lean check output (`lake env lean Work.lean`, includes `#print axioms` of every proof)

```
'TLC.wf_opt_num__proof' depends on axioms: [propext]
'TLC.binop_total_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, TLC.ishl_wf, TLC.ishr_wf]
'TLC.relop_total_proof' depends on axioms: [propext, sorryAx]
'TLC.cvtop_total_proof' depends on axioms: [propext]
'TLC.binop_before_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, TLC.ishl_wf, TLC.ishr_wf]
'TLC.binop_not_none_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.relop_before_proof' depends on axioms: [propext]
'TLC.relop_not_none_proof' depends on axioms: [propext, sorryAx]
'TLC.cvtop_before_proof' depends on axioms: [propext]
'TLC.cvtop_not_none_proof' depends on axioms: [propext, sorryAx]
'TLC.testop_not_none_proof' depends on axioms: [propext]
'TLC.Forall_all_proof' depends on axioms: [propext, Quot.sound]
'TLC.all_Forall_proof' depends on axioms: [propext, Quot.sound]
'TLC.Forall_exists_Forall2_proof' depends on axioms: [propext]
exit=0
```

## Merged-file check

```
Orig.lean  (verbatim copy of TypeProgress.lean):  lake env lean -> 0 errors, 280 "declaration uses sorry" warnings
Merged.lean (same file, the 14 targets' `:= sorry` replaced by `:= by <body>`; diff = exactly those 14 lines):
                                                  lake env lean -> 0 errors, 266 "declaration uses sorry" warnings (280 - 14)
Target lines in Merged.lean (702 wf_opt_num_, 727 binop_total, 801 relop_total, 858 cvtop_total, 913 binop_before,
987 binop_not_none, 1000 relop_before, 1032 relop_not_none, 1046 cvtop_before, 1100 cvtop_not_none, 1112 testop_not_none,
1133 Forall_all, 1140 all_Forall, 1153 Forall_exists_Forall2): 0 sorry warnings on each.
```

## Safety check (end)
```
safety check [prove-H08] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T124537.707307803Z-prove-H08-1465088.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Intermediate safety check (before the final one), also clean:
```
safety check [prove-H08] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T124515.214807172Z-prove-H08-1464640.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

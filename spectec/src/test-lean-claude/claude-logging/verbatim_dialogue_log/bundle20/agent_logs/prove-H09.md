# prove-H09 (bundle20 progress port, proof batch H09, 13 targets)

Agent label: prove-H09. Scope: fill the `sorry` bodies of the 13 listed declarations of `TypeProgress.lean` (lines 814-914), porting `spectec/test-rocq/theories/type_progress.v:1884-2117`. Nothing outside `spectec/src/test-lean-claude` was touched; the only files written are this log and scratch files under `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H09/` (`TypeProgress.lean` itself was NOT edited; the main thread merges the bodies below).

## Result: 13/13 proved (0 blocked, 0 skipped)

## Safety check (start)
```
safety check [prove-H09] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T124023.611334297Z-prove-H09-1462268.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method / verification

- Header-copy + guard workflow of the brief: scratch `Work.lean` (`import TypeProgress`, `namespace TLC`) contains, for each target, the header copied verbatim from `TypeProgress.lean` (theorem renamed `<name>_proof`), the proof, and `example : type_of% @<name>_proof = type_of% @<name> := rfl`. All 13 guards pass.
- Stronger in-situ check: scratch `TPMerged.lean` is a copy of the real `TypeProgress.lean` in which exactly the 13 target `sorry`s were replaced by `:= by <body>` (`diff` against the real file shows only those 13 `sorry` lines removed; the declarations stay at the same lines 814, 820, 825, ... in the real file). It compiles with exit 0, 0 errors, and no `declaration uses sorry` warning at any of the 13 targets (all remaining warnings are the other, still-`sorry` declarations). This also confirms the ordering rule (no later TypeProgress lemma is used).
- No `sorry`/`admit`/`native_decide`/new axioms in any body (grep-checked). Axioms of the proofs: only core `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` appears only transitively through the still-`sorry` earlier lemmas / imported generated `*_is_wf` theorems listed per target.
- One Lean process at a time (each run ~3 s with `import TypeProgress`); no `lake build`, nothing written to `.lake/`.

## Cross-cutting notes

- `wf_lane_` has the `lanetype` argument promoted to an inductive parameter: `cases Hw with | lane__case_0 J' c Hc Heq | lane__case_1 F c Hc Heq` (no slot for `v_lanetype`); `Heq : lanetype_Jnn J = lanetype_Jnn J'` / `lanetype_Jnn J = lanetype_Fnn F` is closed by `cases`-ing the `Jnn`/`Fnn` variables and `simp [lanetype_Jnn, lanetype_Fnn]`.
- `wf_vunop_` has `v_shape` promoted to a parameter: `cases Hop with | vunop__case_0 J M o Ho Hs | vunop__case_1 F M o Hs`, then `subst Hs`.
- `constructor` (Lean) plays the role of Rocq's `econstructor` on `fun_vunop_` / `fun_vunop__before_fun_vunop__case_26`: it tries the constructors in order and the first whose conclusion unifies wins (the `fun_vunop__case_26` catch-all has conclusion `.. none`, so it never matches `some _`). The existential witness is introduced with `apply Exists.intro` (a natural metavariable that unification fills in), because `refine ⟨?w, _⟩` would create a synthetic-opaque goal that unification cannot assign.
- Lean's `Forall P l := forall x in l, P x` makes the Rocq list inductions pointwise; the list-length conjuncts of the (deviating) `Forall_iabs_total` come from `Forall_exists_Forall2`.


## wf_lane_Jnn_inv

- status: **proved** (TypeProgress.lean:814; Rocq type_progress.v:1884-1893)
- earlier still-`sorry` / imported-sorry lemmas relied on: none
- notes: Rocq: `inversion Hw` then `destruct J, J'`. Lean: `cases Hw with | lane__case_0 J' c Hc Heq | lane__case_1 F c Hc Heq` (the `lanetype` index of `wf_lane_` is a promoted parameter, so the binder slots are `J' c Hc Heq`); `J' = J` from `Heq : lanetype_Jnn J = lanetype_Jnn J'` by `cases J <;> cases J'` + `simp [lanetype_Jnn]`; the float case is refuted by `simp [lanetype_Jnn, lanetype_Fnn] at Heq`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hw _
  cases Hw with
  | lane__case_0 J' c Hc Heq =>
    have HJ : J' = J := by
      cases J <;> cases J' <;> first | rfl | (exfalso; simp [lanetype_Jnn] at Heq)
    subst HJ
    exact ⟨c, rfl, Hc⟩
  | lane__case_1 F c Hc Heq =>
    exfalso
    cases F <;> cases J <;> simp [lanetype_Jnn, lanetype_Fnn] at Heq
```

## wf_lane_Jnn_some

- status: **proved** (TypeProgress.lean:820; Rocq type_progress.v:1897-1902)
- earlier still-`sorry` / imported-sorry lemmas relied on: none
- notes: Rocq: `inversion Hw`. Lean: `cases Hw`; integer case is `simp [proj_lane__0]`, float case is refuted as in `wf_lane_Jnn_inv`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hw
  cases Hw with
  | lane__case_0 J' c Hc Heq => simp [proj_lane__0]
  | lane__case_1 F c Hc Heq =>
    exfalso
    cases F <;> cases J <;> simp [lanetype_Jnn, lanetype_Fnn] at Heq
```

## wf_lane_Fnn_inv

- status: **proved** (TypeProgress.lean:825; Rocq type_progress.v:1905-1914)
- earlier still-`sorry` / imported-sorry lemmas relied on: none
- notes: Mirror image of `wf_lane_Jnn_inv` (integer case refuted, float case gives `F' = F` then the witness).

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hw
  cases Hw with
  | lane__case_0 J c Hc Heq =>
    exfalso
    cases F <;> cases J <;> simp [lanetype_Jnn, lanetype_Fnn] at Heq
  | lane__case_1 F' c Hc Heq =>
    have HF : F' = F := by
      cases F <;> cases F' <;> first | rfl | (exfalso; simp [lanetype_Fnn] at Heq)
    subst HF
    exact ⟨c, rfl, Hc⟩
```

## Forall_lane_Jnn

- status: **proved** (TypeProgress.lean:830; Rocq type_progress.v:1916-1924)
- earlier still-`sorry` / imported-sorry lemmas relied on: wf_lane_Jnn_inv (earlier target of this batch)
- notes: Rocq: induction on the `Forall`. Lean `Forall P l := forall x in l, P x`, so it is pointwise: `intro Hw Hs l hl; exact wf_lane_Jnn_inv J l (Hw l hl) (Hs l hl)`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hw Hs l hl
  exact wf_lane_Jnn_inv J l (Hw l hl) (Hs l hl)
```

## Forall_lane_map_wf

- status: **proved** (TypeProgress.lean:837; Rocq type_progress.v:1927-1935)
- earlier still-`sorry` / imported-sorry lemmas relied on: none
- notes: Pointwise: `obtain` the witness `x` from the hypothesis, `subst`, then `wf_lane_.lane__case_0 _ _ _ (Hf x hwx) rfl` (`Option.get! (proj_lane__0 (mk_lane__0 J x))` reduces to `x` by `rfl`).

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hf H l hl
  obtain ⟨x, hx, hwx⟩ := H l hl
  subst hx
  exact wf_lane_.lane__case_0 _ _ _ (Hf x hwx) rfl
```

## Forall_lane_fop_wf

- status: **proved** (TypeProgress.lean:846; Rocq type_progress.v:1938-1951)
- earlier still-`sorry` / imported-sorry lemmas relied on: wf_lane_Fnn_inv (earlier target of this batch)
- notes: Pointwise: `wf_lane_Fnn_inv` gives the float witness, then `wf_lane_.lane__case_1 _ _ _ (Hf x hwx r hr) rfl`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hf H l hl
  obtain ⟨x, hx, hwx⟩ := wf_lane_Fnn_inv F l (H l hl)
  subst hx
  intro r hr
  exact wf_lane_.lane__case_1 _ _ _ (Hf x hwx r hr) rfl
```

## iabs_lane_total

- status: **proved** (TypeProgress.lean:856; Rocq type_progress.v:1953-1966)
- earlier still-`sorry` / imported-sorry lemmas relied on: signed_total (TypeProgress.lean:610, still sorry)
- notes: Rocq steps in the same order: `signed_total` gives `z`, `fun_iabs__case_0` builds the `fun_iabs_` witness (`if z >= 0 then x else ineg_ ..`), `iabs__is_wf` + `wf_lane_.lane__case_0` give the lane wf. `wf_uN_lt'` is replaced by the proved `iswf_uN_proj_lt` (wasm2.0.lean), so there is no dependency on the still-sorry `wf_uN_lt'`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hx
  obtain ⟨z, Hz, _⟩ := signed_total (lsize (lanetype_Jnn J)) (proj_uN_0 x) (iswf_uN_proj_lt Hx)
  have Ha : fun_iabs_ (lsizenn (lanetype_Jnn J)) x
      (if z ≥ (0 : Int) then x else ineg_ (lsizenn (lanetype_Jnn J)) x) :=
    fun_iabs_.fun_iabs__case_0 _ _ _ Hz
  exact ⟨_, Ha, wf_lane_.lane__case_0 _ _ _ (iabs__is_wf _ _ _ _ Ha Hx rfl) rfl⟩
```

## Forall_iabs_total

- status: **proved** (TypeProgress.lean:866; Rocq type_progress.v:1968-1976)
- earlier still-`sorry` / imported-sorry lemmas relied on: Forall_exists_Forall2 (TypeProgress.lean:~797, still sorry); iabs_lane_total (earlier target of this batch)
- notes: Rocq: `apply: Forall_exists_Forall2` then `Forall_impl ... iabs_lane_total`. Lean: `apply Forall_exists_Forall2; intro l hl; obtain ⟨x, hx, Hx⟩ := H l hl; subst hx; exact iabs_lane_total J x Hx`. The length conjunct of the (deviating) statement comes for free from `Forall_exists_Forall2`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro H
  apply Forall_exists_Forall2
  intro l hl
  obtain ⟨x, hx, Hx⟩ := H l hl
  subst hx
  exact iabs_lane_total J x Hx
```

## vunop_real

- status: **proved** (TypeProgress.lean:879; Rocq type_progress.v:2004-2028)
- earlier still-`sorry` / imported-sorry lemmas relied on: all_Forall (TypeProgress.lean:~788, still sorry); Forall_lane_Jnn, Forall_iabs_total, Forall_lane_map_wf, Forall_lane_fop_wf (earlier targets of this batch; Forall_iabs_total in turn uses the still-sorry Forall_exists_Forall2 and signed_total); imported generated wf theorems that are `sorry` in wasm2.0.lean: lanes__is_wf, ipopcnt__is_wf, fabs__is_wf, fneg__is_wf, fsqrt__is_wf, fceil__is_wf, ffloor__is_wf, ftrunc__is_wf, fnearest__is_wf (ineg__is_wf is proved)
- notes: Faithful port of the Rocq proof. `cases Hop` (slots `J M o Ho Hs` / `F M o Hs`; `sh` is a promoted parameter) + `subst Hs`; integer branch: `Hsome` from `Hall` via `all_Forall` (`bne_iff_ne` by `simpa`), `Hlx := Forall_lane_Jnn`, `Forall_iabs_total`, plus the NEG/POPCNT lane-wf facts via `Forall_lane_map_wf` (`ineg__is_wf`, `ipopcnt__is_wf`); `cases J <;> cases o` and `try (cases Ho; contradiction)` discards POPCNT at `J <> I8` (Rocq `destruct J, o; inversion Ho`). Rocq's `split; [eexists | ]; econstructor; vunop_case ...` becomes: `refine ⟨?_, ?_⟩`, `apply Exists.intro; constructor` (resp. `constructor`) which selects the matching `fun_vunop_` (resp. `before`) constructor by unification, then `all_goals first | exact H2b | exact H2a | exact Hsome | exact Hsh | exact Hvw | exact Hneg | exact Hpop | rfl` (`rfl` last so it only fills metavariables such as `lane_1_lst`, `v128`). Float branch identical with one `Forall_lane_fop_wf` fact per float op. No 27-way inversion needed.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hop Hv Hsh Hall
  have Hl := lanes__is_wf _ _ _ Hsh Hv rfl
  cases Hop with
  | vunop__case_0 J M o Ho Hs =>
    -- integer shape: lane facts (Rocq `Hsome`, `Hlx`, `Forall_iabs_total`) feed every real case
    subst Hs
    have Hl' : Forall (fun l => wf_lane_ (lanetype_Jnn J) l)
        (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) val) := Hl
    have Hsome : Forall (fun l => proj_lane__0 l ≠ none)
        (lanes_ (shape.X (lanetype_Jnn J) (dim.mk_dim M)) val) := by
      intro l hl
      have h := all_Forall _ _ _ (Hall J M rfl) l hl
      simpa using h
    have Hlx := Forall_lane_Jnn J _ Hl' Hsome
    obtain ⟨vs, ⟨H2a, H2b⟩, Hvw⟩ := Forall_iabs_total J _ Hlx
    have Hneg := Forall_lane_map_wf J (fun x => ineg_ (lsizenn (lanetype_Jnn J)) x) _
      (fun x hx => ineg__is_wf _ x _ hx rfl) Hlx
    have Hpop := Forall_lane_map_wf J (fun x => ipopcnt_ (lsizenn (lanetype_Jnn J)) x) _
      (fun x hx => ipopcnt__is_wf _ x _ hx rfl) Hlx
    -- Rocq `destruct J, o; inversion Ho`: only `POPCNT` at `J = I8` is well formed
    cases J <;> cases o <;> (try (cases Ho; contradiction))
    -- Rocq `split; [eexists | ]; econstructor; vunop_case ...`: `constructor` picks the matching
    -- case of `fun_vunop_` (resp. its `before` predicate); each premise is then closed from the
    -- lane facts, with `rfl` last so that it only fills the remaining metavariables.
    all_goals
      refine ⟨?_, ?_⟩
      · apply Exists.intro
        constructor
        all_goals first | exact H2b | exact H2a | exact Hsome | exact Hsh | exact Hvw | exact Hneg | exact Hpop | rfl
      · constructor
        all_goals first | exact H2b | exact H2a | exact Hsome | exact Hsh | exact Hvw | exact Hneg | exact Hpop | rfl
  | vunop__case_1 F M o Hs =>
    -- float shape: one `Forall_lane_fop_wf` fact per operation (Rocq `vunop_case`, float branch)
    subst Hs
    have Hl' : Forall (fun l => wf_lane_ (lanetype_Fnn F) l)
        (lanes_ (shape.X (lanetype_Fnn F) (dim.mk_dim M)) val) := Hl
    have Habs := Forall_lane_fop_wf F fabs_ _ (fun x hx => fabs__is_wf _ x _ hx rfl) Hl'
    have Hneg := Forall_lane_fop_wf F fneg_ _ (fun x hx => fneg__is_wf _ x _ hx rfl) Hl'
    have Hsqrt := Forall_lane_fop_wf F fsqrt_ _ (fun x hx => fsqrt__is_wf _ x _ hx rfl) Hl'
    have Hceil := Forall_lane_fop_wf F fceil_ _ (fun x hx => fceil__is_wf _ x _ hx rfl) Hl'
    have Hfloor := Forall_lane_fop_wf F ffloor_ _ (fun x hx => ffloor__is_wf _ x _ hx rfl) Hl'
    have Htrunc := Forall_lane_fop_wf F ftrunc_ _ (fun x hx => ftrunc__is_wf _ x _ hx rfl) Hl'
    have Hnearest := Forall_lane_fop_wf F fnearest_ _ (fun x hx => fnearest__is_wf _ x _ hx rfl) Hl'
    cases F <;> cases o
    all_goals
      refine ⟨?_, ?_⟩
      · apply Exists.intro
        constructor
        all_goals first | exact Hsh | exact Habs | exact Hneg | exact Hsqrt | exact Hceil | exact Hfloor | exact Htrunc | exact Hnearest | rfl
      · constructor
        all_goals first | exact Hsh | exact Habs | exact Hneg | exact Hsqrt | exact Hceil | exact Hfloor | exact Htrunc | exact Hnearest | rfl
```

## vunop_total

- status: **proved** (TypeProgress.lean:890; Rocq type_progress.v:2032-2057)
- earlier still-`sorry` / imported-sorry lemmas relied on: Forall_all (TypeProgress.lean:~783, still sorry); vunop_real, wf_lane_Jnn_some (earlier targets of this batch); imported: lanes__is_wf (sorry in wasm2.0.lean)
- notes: DEVIATION in method (statement unchanged): Rocq case-splits on `E : all (proj_lane__0 l != None) ...` and refutes the negative branch by a 27-way inversion of the `before` predicate. Here `Hall` (the side premise of `vunop_real`) always holds by `wf_lane_Jnn_some` (`lanes__is_wf` gives well-formed lanes, `Forall_all` turns the pointwise facts into the boolean `all`), for integer and (vacuously) float shapes alike, so `vunop_real ...` is applied directly and the negative branch is never needed.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hop Hv Hsh
  -- By `wf_lane_Jnn_some` every lane projects as an integer lane, so `vunop_real`'s side premise
  -- always holds (Rocq splits on it, and refutes the negative branch by 27-way inversion of the
  -- `before` predicate; that branch is impossible, so here it is never needed).
  have Hall : ∀ (J : Jnn) (M : N), sh = shape.X (lanetype_Jnn J) (dim.mk_dim M) →
      (lanes_ sh val).all (fun l : lane_ => proj_lane__0 l != none) = true := by
    intro J M hsh
    have Hl := lanes__is_wf _ _ _ Hsh Hv rfl
    subst hsh
    apply Forall_all
    intro l hl
    have h := wf_lane_Jnn_some J l (Hl l hl)
    simpa using h
  obtain ⟨⟨vs, Hvs⟩, _⟩ := vunop_real sh vunop val Hop Hv Hsh Hall
  exact ⟨some vs, Hvs⟩
```

## vunop_not_none

- status: **proved** (TypeProgress.lean:898; Rocq type_progress.v:2059-2088)
- earlier still-`sorry` / imported-sorry lemmas relied on: Forall_all (TypeProgress.lean:~783, still sorry); vunop_real, wf_lane_Jnn_some (earlier targets of this batch); imported: lanes__is_wf (sorry in wasm2.0.lean)
- notes: Rocq's `inversion Hf as [ ... x0 x1 x2 Hnb ]` (only the catch-all case 26 can return `none`) is done once as a local helper `inv : forall s op v, fun_vunop_ s op v none -> ¬ fun_vunop__before_fun_vunop__case_26 s op v` by `cases H with | fun_vunop__case_26 _ _ _ Hnb => exact Hnb` over bare variables (avoids a `cases` on the opaque index `lanetype_Jnn J`). `Hall` is derived as in `vunop_total` (no int/float split), then `.2` of `vunop_real` (the `before` fact) contradicts `inv`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro Hop Hv Hsh Hf Hn
  subst Hn
  -- Rocq's 27-way `inversion Hf`, done once over bare variables (only the catch-all case 26
  -- can return `none`).
  have inv : ∀ (s : shape) (op : vunop_) (v : vec_), fun_vunop_ s op v none →
      ¬ fun_vunop__before_fun_vunop__case_26 s op v := by
    intro s op v H
    cases H with
    | fun_vunop__case_26 _ _ _ Hnb => exact Hnb
  have Hall : ∀ (J : Jnn) (M : N), sh = shape.X (lanetype_Jnn J) (dim.mk_dim M) →
      (lanes_ sh val).all (fun l : lane_ => proj_lane__0 l != none) = true := by
    intro J M hsh
    have Hl := lanes__is_wf _ _ _ Hsh Hv rfl
    subst hsh
    apply Forall_all
    intro l hl
    have h := wf_lane_Jnn_some J l (Hl l hl)
    simpa using h
  -- the real case supplied by `vunop_real` contradicts the catch-all
  exact inv _ _ _ Hf (vunop_real sh vunop val Hop Hv Hsh Hall).2
```

## sat_s_range

- status: **proved** (TypeProgress.lean:908; Rocq type_progress.v:2092-2101)
- earlier still-`sorry` / imported-sorry lemmas relied on: none
- notes: Rocq: `rewrite /sat_s_ Zsub1_toN`, `two_pow_pos`, `Z.ltb_spec` case splits, `lia`. Lean: `unfold sat_s_`, rewrite `Int.toNat (↑v_N - 1) = v_N - 1` (inline `omega`, i.e. Zsub1_toN) and `(2:Int)^k = ((2^k : Nat) : Int)` (`iswf_two_pow_cast`, wasm2.0.lean), `Nat.two_pow_pos` for positivity (two_pow_pos), then `split_ifs <;> omega`. Self-contained: does not use the still-sorry `Zsub1_toN`/`two_pow_pos`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  unfold sat_s_
  -- Rocq `Zsub1_toN` / `two_pow_pos`, done inline (`omega` / `Nat.two_pow_pos`)
  rw [show Int.toNat ((v_N : Int) - (1 : Int)) = v_N - 1 by omega, iswf_two_pow_cast]
  have Hp : 0 < 2 ^ (v_N - 1) := Nat.two_pow_pos _
  split_ifs <;> omega
```

## imin_total_wf

- status: **proved** (TypeProgress.lean:914; Rocq type_progress.v:2103-2117)
- earlier still-`sorry` / imported-sorry lemmas relied on: signed_total (TypeProgress.lean:610, still sorry)
- notes: Rocq steps in the same order: `cases v_sx` (U: `by_cases proj_uN_0 i1 <= proj_uN_0 i2` -> `fun_imin__case_0` / `fun_imin__case_1` with `omega`; S: `signed_total` for both operands -> `fun_imin__case_2 v_N i1 i2 z2 z1 Hs2 Hs1`), then `imin__is_wf` for the range. `wf_uN_lt'` replaced by the proved `iswf_uN_proj_lt`.

Proof body (the tactic block after `:= by`, exactly as compiled):

```lean
  intro H1 H2
  have hr : ∃ r, fun_imin_ v_N v_sx i1 i2 r := by
    cases v_sx with
    | U =>
      by_cases E : proj_uN_0 i1 ≤ proj_uN_0 i2
      · exact ⟨i1, fun_imin_.fun_imin__case_0 _ _ _ E⟩
      · exact ⟨i2, fun_imin_.fun_imin__case_1 _ _ _ (by omega)⟩
    | S =>
      obtain ⟨z1, Hs1, _⟩ := signed_total v_N (proj_uN_0 i1) (iswf_uN_proj_lt H1)
      obtain ⟨z2, Hs2, _⟩ := signed_total v_N (proj_uN_0 i2) (iswf_uN_proj_lt H2)
      exact ⟨_, fun_imin_.fun_imin__case_2 v_N i1 i2 z2 z1 Hs2 Hs1⟩
  obtain ⟨r, Hr⟩ := hr
  exact ⟨r, Hr, imin__is_wf _ _ _ _ _ _ Hr H1 H2 rfl⟩
```

## Final Lean check output

Last `lake env lean .../Work.lean` run (13 proofs + 13 `type_of%` guards + dependency report; `exit=0`; last lines):

```
   axioms = #[propext, sorryAx, Classical.choice, Quot.sound]
TLC.vunop_not_none_proof: TLC deps = #[TLC.Forall_all, TLC.wf_lane_Jnn_some, TLC.vunop_real]; generated wf deps = #[lanes_, lanes__is_wf]
   axioms = #[propext, sorryAx, Classical.choice, Quot.sound]
TLC.sat_s_range_proof: TLC deps = #[TLC.sat_s_range_proof._proof_1_1, TLC.sat_s_range_proof._proof_1_2, TLC.sat_s_range_proof._proof_1_3, TLC.sat_s_range_proof._proof_1_4]; generated wf deps = #[]
   axioms = #[propext, Classical.choice, Quot.sound]
TLC.imin_total_wf_proof: TLC deps = #[TLC.imin_total_wf_proof._proof_1_1, TLC.signed_total]; generated wf deps = #[imin__is_wf]
   axioms = #[propext, sorryAx, Quot.sound]
exit=0
```

Merged-copy run (`lake env lean .../TPMerged.lean`, the real file with the 13 bodies inserted): `exit=0`, `errors: 0`, `warnings: 267` (all `declaration uses sorry` of OTHER declarations; none at the 13 target lines 814, 820, 825, 830, 837, 846, 856, 866, 879, 890, 898, 908, 914 of the real file).

## Safety check (end)
```
safety check [prove-H09] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T125218.077898091Z-prove-H09-1470709.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

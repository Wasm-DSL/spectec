# prove-C20 log (bundle20 progress port, proof batch C20)

Targets (in order): `t_progress_be_vload_pack` (TypeProgress.lean:2245; Rocq type_progress.v:5161-5228) and
`t_progress_be_vload_splat` (TypeProgress.lean:2257; Rocq type_progress.v:5228-5277). Both are bullets of `t_progress_be`.

Result: **both proved**. `t_progress_be_vload_pack` has one documented `sorry`, in the known-false subcase
`SHAPE 64 X 1` (Rocq `admit` at type_progress.v:5208). `t_progress_be_vload_splat` has no `sorry` of its own.
No repo file was edited; this log is the only file I wrote inside the target dir. Scratch files are only in
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C20/`.

## Safety check at START (run from /home/zhengyew/spectec)
```
safety check [prove-C20] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T135216.453972528Z-prove-C20-1513181.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Method
- Scratch `build.py` copies each target header verbatim from TypeProgress.lean (from `theorem` up to `:= sorry`) and
  renames it `<name>_proof`. It then appends the body from scratch `proofs/<name>.lean` and the guard
  `example : type_of% @<name>_proof = type_of% @<name> := rfl`, inside `import TypeProgress` / `namespace TLC`.
- I ran one Lean process at a time, always `lake env lean <file>`, never `lake build`.
- Negative control `Work_ctl.lean` is Work.lean plus `#print axioms` for the dependencies plus
  `example : (1 : Nat) = 2 := rfl`. The bogus example fails (exit 1), so the check is live.
- Merge simulation `Head.lean` (built by scratch `head.py`): the real TypeProgress.lean prefix through
  `t_progress_be_vload_splat`, with both bodies in place of `:= sorry`, plus `#print axioms` and `end TLC`.
  Result: exit 0. The last `declaration uses sorry` warning is at Head.lean:2245 (`vload_pack`, the documented
  sorry). Head.lean:2377 (`vload_splat`) does not warn. This mechanically confirms the ordering rule.
- TypeProgress.lean has no `@[simp]`, `attribute`, `set_option`, `open`, `section` or `variable` commands
  (checked with grep). So the bodies elaborate in the same context in Work.lean and in the merged file.
- Ordering: the TypeProgress declarations used are `invert_typeof_I32` (209), `list_slice_size` (270),
  `Forall_list_slice` (1088), `wf_config_mem_bytes` (1101) and `t_progress_be_P` (1486, def). All come before 2245.
- Imported declarations used:
  - `rat_to_nat_natCast` (TypePreservation.lean:1318, proved; TypeProgress imports TypePreservation for such helpers;
    also used by prove-H14).
  - `ibytes_inv` (HelperLemmas axiom, mirrors Rocq `axioms.v`).
  - Generated wasm2.0 items: `inv_ibytes__is_wf`, `extend___is_wf` (bodies are `sorry`; Rocq uses the same lemmas),
    `Step.read`, `Step_read.vload_shape_oob`, `Step_read.vload_shape_val`, `Step_read.vload_splat_oob`,
    `Step_read.vload_splat_val`, and the constructors `wf_uN.uN_case_0`, `wf_lane_.lane__case_0`,
    `wf_shape.shape_case_0`, `wf_dim.dim_case_0`.
- Axioms (`#print axioms`): both proofs give `[propext, sorryAx, Classical.choice, Quot.sound, ibytes_inv]`.
  - `ibytes_inv` is the only project axiom used.
  - In `vload_splat`, `sorryAx` comes only from the still-sorry dependencies. Their own axiom lists:
    `invert_typeof_I32: [propext, sorryAx]`, `list_slice_size: [sorryAx]`, `Forall_list_slice: [sorryAx]`,
    `wf_config_mem_bytes: [propext, sorryAx, Classical.choice, Quot.sound]`, `inv_ibytes__is_wf: [sorryAx]`,
    `extend___is_wf: [sorryAx]`; `rat_to_nat_natCast` is sorry-free.
  - In `vload_pack`, `sorryAx` additionally comes from the one documented `sorry`.
  - No `admit`, `native_decide` or new axioms were used.

## Porting notes (pitfalls hit)
- `M`, `N` and `n` are `abbrev ... : Type := Nat`. **omega ignores hypotheses and goals typed `@Eq M`/`@Eq N`**
  ("No usable constraints found"). Fixes:
  - state the fact as `@Eq Nat (v_M * v_N) 64`;
  - write `obtain rfl : @Eq Nat v_N 8 := by omega`;
  - close `Hcases` with `simpa [or_assoc] using H`, since `wf_sz`'s premise is already `@Eq Nat`.
  - omega also treats `v_M * v_N` as a nonlinear atom, so `subst` `v_M` before deriving `v_N`.
- `simp only [proj_uN_0]` also rewrote `proj_uN_0 memarg.OFFSET` into the raw projection `memarg.2.1`. omega
  then saw a different atom than the one in `Hbnd`. Fix: rewrite only `proj_uN_0 (uN.mk_uN n1) = n1`, by `rfl`.
- A lambda `fun k => ... ((k * v_M) : Rat) ...` without a binder type elaborates `k : Rat`. `List.range` then gets
  coerced through a monadic lift. Fix: `fun (k : Nat) => ...`.
- `Hv _ (by simp)` (instantiating `Forall` over `Option.toList`) needs an expected type, or the `_` stays a
  metavariable.

## Results

### `t_progress_be_vload_pack` : proved (one documented sorry in the known-false subcase)
Still-`sorry` earlier lemmas relied on: `invert_typeof_I32` (209), `list_slice_size` (270), `Forall_list_slice` (1088),
`wf_config_mem_bytes` (1101). Also the generated `inv_ibytes__is_wf` and `extend___is_wf` (wasm2.0, bodies `sorry`).

Notes: a port of the Rocq bullet at type_progress.v:5161-5228.
- Rocq's `case Hs` becomes `by_cases Hs` on the exact `vload_shape_oob` premise. The OOB branch uses
  `Step_read.vload_shape_oob`.
- `Hwv` comes from `cases HWfinstr`. `cases Hwv` gives `Hsz` and `HMN`. `HMN'` (`v_M * v_N = 64`) comes from the
  `Rat` equation by `exact_mod_cast`. `Hcases` comes from `cases Hsz`.
- Rocq's 4-way `case: Hcases` becomes one `obtain E | ⟨q, Jn, ...⟩` with
  `v_M = 64 ∨ ∃ q Jn, v_M = 8*q ∧ jsize Jn = v_M*2 ∧ wf_shape ...`.
  - (8, 16, 32) give `v_N` = 8/4/2 (omega after subst), q = 1/2/4 and `Jnn` = I16/I32/I64.
  - The 4th case (`v_M = 64`) is the FALSE subcase. It is closed with a single `sorry` on the real step goal
    (in-bounds, `Hbnd` in context), exactly where Rocq has its `admit`.
- The three good cases share one `Step_read.vload_shape_val` application. Its `j_lst` is
  `(List.range v_N).map J`, with Rocq's `J`; this replaces Rocq's per-case `mkseqN J n`.
  - Byte equations: zip-based `Forall₂` via a local `zip_map_self`, then `ibytes_inv` and `list_slice_size`.
  - Bound: `rat_to_nat (k*v_M/8) = k*q`, `rat_to_nat (v_M/8) = q`, `rat_to_nat (v_M*v_N/8) = v_N*q` (all via
    `v_M = 8*q`, `push_cast; ring`, `rat_to_nat_natCast`), then `(k+1)*q ≤ v_N*q` and omega. This is Rocq's
    `Hsl` + `Hbnd`.
  - Lane well-formedness: `lane__case_0` + `extend___is_wf` + `HJ`, as in Rocq.
```lean
  intro C v_M v_N v_sx memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + (v_M * v_N) / 8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (((v_M * v_N) : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply vload_shape_oob; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.vload_shape_oob _ _ _ _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: `have Hbnd : n1 + OFFSET + (v_M * v_N) / 8 <= |mem.BYTES|`.
      have Hbnd : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (((v_M * v_N) : Rat) / (8 : Rat))
          ≤ (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length := Nat.le_of_not_gt Hs
      -- Rocq: `have Hwv : wf_vloadop_ V128 (SHAPEX_ (mk_sz v_M) v_N v_sx)` (inversion HWfinstr).
      have Hwv : wf_vloadop_ vectype.V128 (vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx) := by
        cases HWfinstr
        rename_i Hv _
        exact Hv _ (by simp)
      -- Rocq: `inversion Hwv as [? ? ? ? Hsz HMN | | ]; subst.` and `HMN' : v_M * v_N = 64`.
      cases Hwv
      rename_i Hsz HMN
      have HMN' : @Eq Nat (v_M * v_N) 64 := by
        simp only [proj_sz_0, vsize] at HMN
        have h : (v_M : Rat) * (v_N : Rat) = ((64 : Nat) : Rat) := by rw [HMN]; norm_num
        exact_mod_cast h
      -- Rocq: `have Hcases : v_M = 8 \/ v_M = 16 \/ v_M = 32 \/ v_M = 64` (inversion Hsz).
      have Hcases : v_M = 8 ∨ v_M = 16 ∨ v_M = 32 ∨ v_M = 64 := by
        cases Hsz
        rename_i H
        simpa [or_assoc] using H
      -- Rocq: `pose J := fun k => inv_ibytes_ v_M (list_slice BYTES (n1 + OFFSET + k * v_M / 8)
      -- (v_M / 8))` and `HJ : forall k, wf_uN v_M (J k)`.
      have HJ : ∀ k : Nat, wf_uN v_M (inv_ibytes_ v_M (List.take (rat_to_nat ((v_M : Rat) / (8 : Rat)))
          (List.drop (n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (((k * v_M) : Rat) / (8 : Rat)))
            (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))) := fun k =>
        inv_ibytes__is_wf _ _ _ (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl
      -- Rocq: `case: Hcases => [E | [E | [E | E]]]; subst v_M. 4: { admit }.` In the three good
      -- cases (`v_M` = 8/16/32, so `v_N` = 8/4/2) the lanes widen to `Jnn` = I16/I32/I64; they
      -- share the `vload_shape_val` step below, parametrised by `q = v_M / 8` and that `Jnn`.
      obtain E | ⟨q, Jn, Hq, HJn, Hshape⟩ : v_M = 64 ∨ ∃ (q : Nat) (Jn : Jnn), v_M = 8 * q ∧
          jsize Jn = v_M * 2 ∧ wf_shape (shape.X (lanetype_Jnn Jn) (dim.mk_dim v_N)) := by
        rcases Hcases with E | E | E | E
        · subst E
          obtain rfl : @Eq Nat v_N 8 := by omega
          exact Or.inr ⟨1, Jnn.I16, rfl, rfl,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · subst E
          obtain rfl : @Eq Nat v_N 4 := by omega
          exact Or.inr ⟨2, Jnn.I32, rfl, rfl,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · subst E
          obtain rfl : @Eq Nat v_N 2 := by omega
          exact Or.inr ⟨4, Jnn.I64, rfl, rfl,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · exact Or.inl E
      · -- FALSE subcase as the spec stands (Rocq: admit at type_progress.v:5208); see vload_shape64_stuck.
        sorry
      · -- Rocq: `eapply (vload_shape_val (mk_state s f) _ _ _ _ _ _ (mkseqN J N) Jnn)`.
        -- the byte offsets/sizes are whole numbers, since `v_M = 8 * q`
        have HkM : ∀ k : Nat, rat_to_nat (((k * v_M) : Rat) / (8 : Rat)) = k * q := by
          intro k
          rw [show ((k : Rat) * (v_M : Rat)) / (8 : Rat) = ((k * q : Nat) : Rat) by
            rw [Hq]; push_cast; ring]
          exact rat_to_nat_natCast _
        have HM : rat_to_nat ((v_M : Rat) / (8 : Rat)) = q := by
          rw [show (v_M : Rat) / (8 : Rat) = ((q : Nat) : Rat) by rw [Hq]; push_cast; ring]
          exact rat_to_nat_natCast _
        have HMN8 : rat_to_nat (((v_M * v_N) : Rat) / (8 : Rat)) = v_N * q := by
          rw [show ((v_M : Rat) * (v_N : Rat)) / (8 : Rat) = ((v_N * q : Nat) : Rat) by
            rw [Hq]; push_cast; ring]
          exact rat_to_nat_natCast _
        have zip_map_self : ∀ {β : Type} (g : Nat → β) (l : List Nat),
            List.zip l (List.map g l) = List.map (fun k => (k, g k)) l := by
          intro β g l
          induction l with
          | nil => rfl
          | cons a l ih => simp [ih]
        refine ⟨s, f, _, Step.read _ _ _ (Step_read.vload_shape_val _ _ _ _ _ _ _
          ((List.range v_N).map (fun (k : Nat) => inv_ibytes_ v_M (List.take (rat_to_nat ((v_M : Rat) / (8 : Rat)))
            (List.drop (n1 + proj_uN_0 memarg.OFFSET + rat_to_nat (((k * v_M) : Rat) / (8 : Rat)))
              (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))))
          Jn ?_ ?_ HJn rfl (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩) Hshape ?_ (by simp))⟩
        · -- the address is an `i32` (one premise per lane)
          intro k _
          simp [proj_num__0]
        · -- Rocq: `apply/eqP; apply: ibytes_inv; apply: list_slice_size; apply: (Hsl ... Hbnd)`.
          intro p hp
          rw [zip_map_self] at hp
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
          rw [List.mem_range] at hk
          simp only [proj_num__0, Option.get!_some]
          rw [show proj_uN_0 (uN.mk_uN n1) = n1 from rfl]
          apply ibytes_inv
          apply list_slice_size
          rw [HkM, HM]
          rw [HMN8] at Hbnd
          have h1 : (k + 1) * q ≤ v_N * q := Nat.mul_le_mul_right q hk
          rw [Nat.add_mul, Nat.one_mul] at h1
          omega
        · -- Rocq: `eapply lane__case_0; [ (eapply extend___is_wf; last by apply: eqxx); apply: HJ | by [] ]`.
          intro x hx
          obtain ⟨k, _, rfl⟩ := List.mem_map.1 hx
          exact wf_lane_.lane__case_0 _ _ _ (extend___is_wf _ _ _ _ _ (HJ k) rfl) rfl
  · simp at Hts
```

### `t_progress_be_vload_splat` : proved
Still-`sorry` earlier lemmas relied on: `invert_typeof_I32` (209), `list_slice_size` (270), `Forall_list_slice` (1088),
`wf_config_mem_bytes` (1101). Also the generated `inv_ibytes__is_wf` (wasm2.0, body `sorry`).

Notes: a close port of the Rocq bullet at type_progress.v:5228-5277.
- Rocq's `case Hs` becomes `by_cases Hs`. The OOB branch uses `Step_read.vload_splat_oob`.
- `Hbnd`, `Hwfk` (`inv_ibytes__is_wf` + `Forall_list_slice` + `wf_config_mem_bytes`), `Hsz` (from `cases HWfinstr`,
  then `cases` on `wf_vloadop_`) and `Hcases` (from `cases Hsz`) follow Rocq.
- Rocq's 4-way split with `(Jnn, M)` = (I8, 16) / (I16, 8) / (I32, 4) / (I64, 2) becomes one `obtain ⟨Jn, vM, ...⟩`.
  Each case is closed by `rfl`, `norm_num` and `decide`. Then `subst HJn` (`v_n := jsize Jn`) and one
  `Step_read.vload_splat_val` application with Rocq's explicit `j`.
- Byte equation: `ibytes_inv` + `list_slice_size _ _ _ Hbnd`.
- Lane: Rocq's `mk_uN_eta` (local Lean helper, `cases u; rfl`) + `lane__case_0` + `Hwfk`.
- No `sorry` in this body.
```lean
  intro C v_n memarg mt Hlen Hlookup HLim HWfC HWfMemType HWfinstr
  unfold t_progress_be_P
  intro s f C' vcs ts1 ts2 lab ret HWfConfig HWfVals Htf Hcontext Hmod Hts Hstore Hnotbr Hnotret
  right
  -- Rocq: `case: Htf => Htf1 _. rewrite -Htf1 in Hts. invert_typeof_vcs Hts HWfConfig HWfVals.`
  simp only [mkFunctype, functype.mk_functype.injEq, list.mk_list.injEq] at Htf
  obtain ⟨Htf1, _⟩ := Htf
  rw [← Htf1] at Hts
  rcases vcs with _ | ⟨v1, _ | ⟨v2, vcs2⟩⟩
  · simp at Hts
  · simp only [List.map_cons, List.map_nil, List.cons.injEq] at Hts
    obtain ⟨Ht1, -⟩ := Hts
    -- Rocq: `inv_Forall HWfVals. eapply invert_typeof_I32 in Ht1 as [n1 Heqv1]; eauto. rewrite Heqv1.`
    have Hwf1 : wf_val v1 := HWfVals v1 (by simp)
    obtain ⟨n1, Heqv1⟩ := invert_typeof_I32 v1 Ht1 Hwf1
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Heqv1,
      admininstr_instr]
    -- Rocq: `case Hs: ((n1 + OFFSET memarg + v_n / 8) >? |mem.BYTES|).`
    by_cases Hs : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat ((v_n : Rat) / (8 : Rat))
        > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length
    · -- Rocq: `exists s, f, [admininstr_TRAP]. eapply read. eapply vload_splat_oob; eauto.
      --        econstructor; eauto.`
      exact ⟨s, f, [admininstr.TRAP], Step.read _ _ _
        (Step_read.vload_splat_oob _ _ _ _ (by simp [proj_num__0])
          (by simpa [proj_num__0, proj_uN_0] using Hs)
          (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩))⟩
    · -- Rocq: `have Hbnd : n1 + OFFSET + v_n / 8 <= |mem.BYTES|`.
      have Hbnd : n1 + proj_uN_0 memarg.OFFSET + rat_to_nat ((v_n : Rat) / (8 : Rat))
          ≤ (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length := Nat.le_of_not_gt Hs
      -- Rocq: `have Hwfk : wf_uN v_n (inv_ibytes_ v_n (list_slice BYTES (n1 + OFFSET) (v_n / 8)))`.
      have Hwfk : wf_uN v_n (inv_ibytes_ v_n (List.take (rat_to_nat ((v_n : Rat) / (8 : Rat)))
          (List.drop (n1 + proj_uN_0 memarg.OFFSET) (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES))) :=
        inv_ibytes__is_wf _ _ _ (Forall_list_slice _ _ _ _ (wf_config_mem_bytes _ _ _ _ HWfConfig)) rfl
      -- Rocq: `have Hsz : wf_sz (mk_sz v_n)` (inversion HWfinstr, then of `wf_vloadop_`).
      have Hsz : wf_sz (sz.mk_sz v_n) := by
        cases HWfinstr
        rename_i Hv _
        have Hv' : wf_vloadop_ vectype.V128 (vloadop_.SPLAT (sz.mk_sz v_n)) := Hv _ (by simp)
        cases Hv'
        assumption
      -- Rocq: `have Hcases : v_n = 8 \/ v_n = 16 \/ v_n = 32 \/ v_n = 64` (inversion Hsz).
      have Hcases : v_n = 8 ∨ v_n = 16 ∨ v_n = 32 ∨ v_n = 64 := by
        cases Hsz
        rename_i H
        simpa [or_assoc] using H
      -- Rocq: `case: Hcases => [E | [E | [E | E]]]; subst v_n; ... eapply (vload_splat_val ... Jnn M)`
      -- with (`Jnn`, `M`) = (I8, 16) / (I16, 8) / (I32, 4) / (I64, 2); the four cases share the step.
      obtain ⟨Jn, vM, HJn, HvM, Hshape⟩ : ∃ (Jn : Jnn) (vM : Nat), v_n = jsize Jn ∧
          (vM : Rat) = (128 : Rat) / (v_n : Rat) ∧ wf_shape (shape.X (lanetype_Jnn Jn) (dim.mk_dim vM)) := by
        rcases Hcases with E | E | E | E <;> subst E
        · exact ⟨Jnn.I8, 16, rfl, by norm_num,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · exact ⟨Jnn.I16, 8, rfl, by norm_num,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · exact ⟨Jnn.I32, 4, rfl, by norm_num,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
        · exact ⟨Jnn.I64, 2, rfl, by norm_num,
            wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 _ (by decide)) (by decide)⟩
      subst HJn
      refine ⟨s, f, _, Step.read _ _ _ (Step_read.vload_splat_val _ _ _ _ _
        (inv_ibytes_ (jsize Jn) (List.take (rat_to_nat (((jsize Jn) : Rat) / (8 : Rat)))
          (List.drop (n1 + proj_uN_0 memarg.OFFSET) (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES)))
        Jn vM (by simp [proj_num__0]) ?_ rfl HvM rfl (wf_uN.uN_case_0 32 0 ⟨Nat.zero_le _, Nat.zero_le _⟩)
        Hshape ?_)⟩
      · -- Rocq: `apply/eqP; apply: ibytes_inv; apply: list_slice_size; by apply: Hbnd`.
        simp only [proj_num__0, Option.get!_some]
        rw [show proj_uN_0 (uN.mk_uN n1) = n1 from rfl]
        apply ibytes_inv
        exact list_slice_size _ _ _ Hbnd
      · -- Rocq: `eapply lane__case_0; [ by rewrite mk_uN_eta; apply: Hwfk | by [] ]`.
        have mk_uN_eta : ∀ u : uN, uN.mk_uN (proj_uN_0 u) = u := fun u => by cases u; rfl
        rw [mk_uN_eta]
        exact wf_lane_.lane__case_0 _ _ _ Hwfk rfl
  · simp at Hts
```

## Final Lean check output
Command: `cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean
/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-C20/Work.lean`
(2 proofs, 2 `rfl` guards, `#print axioms`):
```
Work.lean:4:8: warning: declaration uses `sorry`
'TLC.t_progress_be_vload_pack_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, ibytes_inv]
'TLC.t_progress_be_vload_splat_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, ibytes_inv]
EXIT=0
```
The single `sorry` warning (Work.lean:4) is `t_progress_be_vload_pack_proof`, from the documented FALSE subcase.

Negative control `Work_ctl.lean` (tail):
```
'TLC.invert_typeof_I32' depends on axioms: [propext, sorryAx]
'TLC.list_slice_size' depends on axioms: [sorryAx]
'TLC.Forall_list_slice' depends on axioms: [sorryAx]
'TLC.wf_config_mem_bytes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'inv_ibytes__is_wf' depends on axioms: [sorryAx]
'extend___is_wf' depends on axioms: [sorryAx]
'TLC.rat_to_nat_natCast' depends on axioms: [propext, Quot.sound]
Work_ctl.lean:228:27: error: Type mismatch  rfl  has type ?m.7 = ?m.7 but is expected to have type 1 = 2
EXIT=1 (as intended)
```

Merge simulation `Head.lean` (real TypeProgress.lean prefix through `t_progress_be_vload_splat`, bodies spliced in):
```
'TLC.t_progress_be_vload_pack' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, ibytes_inv]
'TLC.t_progress_be_vload_splat' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound, ibytes_inv]
Head.lean:2222:8: warning: declaration uses `sorry`
Head.lean:2233:8: warning: declaration uses `sorry`
Head.lean:2245:8: warning: declaration uses `sorry`
EXIT=0 (0 errors; 252 'declaration uses sorry' warnings, all from other still-sorry declarations except 2245 =
vload_pack's documented sorry; vload_splat at Head.lean:2377 does not warn)
```

## Safety check at END (run from /home/zhengyew/spectec)
```
safety check [prove-C20] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T140509.232702611Z-prove-C20-1520470.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

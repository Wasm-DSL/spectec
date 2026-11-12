# prove-H11 log (bundle20, progress port, proof batch H11, 14 targets)

Task: fill the `sorry` bodies of `ieq_bit`, `ine_bit`, `icmp_total_bit`, `Forall_zipWith`, `Forall2_all`, `Forall_map_P`, `vrelop_some`, `invsigned_total_32m1`, `Forall_list_slice`, `mem_bytes_wf`, `wf_config_mem_bytes`, `all_and_Forall`, `Forall_and_all`, `packnum_not_none` of `TypeProgress.lean` (no repo file edited; only this log and the scratch dir `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/prove-H11/` were written).

## Safety check at START
```
safety check [prove-H11] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T124721.010550415Z-prove-H11-1465787.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Result summary
All 14 targets: **proved**. No statement changed (each `*_proof` copy in `Work_final.lean` is guarded by `example : type_of% @X_proof = type_of% @X := rfl`). No `sorry`/`admit`/`native_decide`/new axiom. Proof bodies are given exactly as compiled (2-space indented, to be placed after `:= by`).

Validation: (1) `Work_final.lean` (14 `_proof` theorems + rfl guards + `#print axioms`) compiles with exit 0 and no errors; (2) a scratch copy `TypeProgressMerged.lean` of the whole `TypeProgress.lean` with these 14 proofs substituted for the `sorry`s (ordering rule check) compiles with 0 errors (4.98 s, 3.9 GB peak); none of the 14 declarations produces a `declaration uses sorry` warning; (3) `TypeProgressMerged2.lean` (same, with the earlier sorry lemmas turned into axioms in the scratch copy) shows that no hidden `sorry` is in the 14 proofs: the only `sorryAx` left in `vrelop_some` is `extend___is_wf` (wasm2.0.lean:2714, `sorry` in the generated file).

## `ieq_bit`  (TypeProgress.lean:1030; Rocq type_progress.v:2335-2337)

- status: proved
- earlier lemmas that are still `sorry` and are used: res_bool_bit (1025, still sorry)
- notes: Rocq: `move => *. exact: res_bool_bit.` `ieq_ v_N a b` unfolds to `uN.mk_uN (nat_of_bool (a == b))` and `proj_uN_0 (mk_uN n)` reduces to `n`, so `res_bool_bit _` unifies by defeq.

Proof body (after `:= by`):
```lean
  exact res_bool_bit _
```

## `ine_bit`  (TypeProgress.lean:1034; Rocq type_progress.v:2338-2340)

- status: proved
- earlier lemmas that are still `sorry` and are used: res_bool_bit (1025, still sorry)
- notes: Same as `ieq_bit`.

Proof body (after `:= by`):
```lean
  exact res_bool_bit _
```

## `icmp_total_bit`  (TypeProgress.lean:1039; Rocq type_progress.v:2341-2358)

- status: proved
- earlier lemmas that are still `sorry` and are used: ilt_total (665), igt_total (669), ile_total (673), ige_total (677), res_bool_bit (1025)  [all still sorry]
- notes: Rocq structure kept: get the four results from the `*_total` lemmas, `exists r_i`, then bit-ness by `case Hr_i` + `res_bool_bit` (`cases Hr` exposes `r = uN.mk_uN (nat_of_bool _)`; both constructors of each relation).

Proof body (after `:= by`):
```lean
  intro H1 H2
  obtain ⟨r1, Hr1⟩ := ilt_total v_N v_sx i1 i2 H1 H2
  obtain ⟨r2, Hr2⟩ := igt_total v_N v_sx i1 i2 H1 H2
  obtain ⟨r3, Hr3⟩ := ile_total v_N v_sx i1 i2 H1 H2
  obtain ⟨r4, Hr4⟩ := ige_total v_N v_sx i1 i2 H1 H2
  refine ⟨⟨r1, Hr1, ?_⟩, ⟨r2, Hr2, ?_⟩, ⟨r3, Hr3, ?_⟩, ⟨r4, Hr4, ?_⟩⟩
  · cases Hr1 <;> exact res_bool_bit _
  · cases Hr2 <;> exact res_bool_bit _
  · cases Hr3 <;> exact res_bool_bit _
  · cases Hr4 <;> exact res_bool_bit _
```

## `Forall_zipWith`  (TypeProgress.lean:1050; Rocq type_progress.v:2360-2365)

- status: proved
- earlier lemmas that are still `sorry` and are used: none
- notes: Induction on `l1` generalizing `l2` (Rocq: `elim: l1 l2`), nil cases by `simp [List.zipWith]`.

Proof body (after `:= by`):
```lean
  intro H
  induction l1 generalizing l2 with
  | nil => intro x hx; simp [List.zipWith] at hx
  | cons a l1 IH =>
    cases l2 with
    | nil => intro x hx; simp [List.zipWith] at hx
    | cons b l2 =>
      intro x hx
      simp only [List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact H a b
      · exact IH l2 x hx
```

## `Forall2_all`  (TypeProgress.lean:1057; Rocq type_progress.v:2367-2373)

- status: proved
- earlier lemmas that are still `sorry` and are used: none
- notes: Lean `Forall₂` is zip-based so the conclusion is just `H t.1 t.2`; the length hypothesis is unused (kept in the statement as in the file).

Proof body (after `:= by`):
```lean
  intro H _ t _
  exact H t.1 t.2
```

## `Forall_map_P`  (TypeProgress.lean:1063; Rocq type_progress.v:2375-2379)

- status: proved
- earlier lemmas that are still `sorry` and are used: none
- notes: Membership in `map f l` gives a preimage `a ∈ l`; `H a (Hl a ha)`.

Proof body (after `:= by`):
```lean
  intro H Hl x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact H a (Hl a ha)
```

## `vrelop_some`  (TypeProgress.lean:1075; Rocq type_progress.v:2400-2440)

- status: proved
- earlier lemmas that are still `sorry` and are used: lanes_Jnn_form (942), lanes_Fnn_form (948), jlane_some (953), flane_some (957), lanes_size_eq (963), zip_lane_rel (999)  [all still sorry], ieq_bit, ine_bit, icmp_total_bit, Forall_zipWith, Forall2_all, Forall_map_P  [this batch; proved], imported: `extend___is_wf` (wasm2.0.lean:2714, `sorry` in the generated file), axioms feq_bit/fne_bit/flt_bit/fgt_bit/fle_bit/fge_bit (HelperLemmas, mirror of Rocq axioms.v)
- notes: Follows the Rocq proof: invert `wf_vrelop_` (integer vs float lane shapes), derive lane facts `HL/HS/Hsz`, split the operator, for LT/GT/LE/GE get `vs` from `zip_lane_rel` with `icmp_total_bit`, then `eexists; econstructor` (here `apply Exists.intro; constructor`) and close the premises uniformly with `first` combinators (Rocq `vrelop_close`/`bit_close`, which are NOT ported as Ltac; they are inlined as the `first | ...` blocks). Differences: (a) Lean has no `eexists`, so `apply Exists.intro; constructor`; the equation premises are discharged by type-directed `rfl` (`List lane_`/`List iN`/`vec_` equalities) BEFORE the other closers so that metavariables for the lane lists are assigned in the right order (a blanket `rfl` would unify `length ?a = length ?b` goals wrongly); (b) `Map₂ f l1 l2 = List.zipWith f l1 l2` is proved locally (`hMap2`) to use `Forall_zipWith`; (c) the I64-unsigned `||` premise handling of Rocq is unnecessary: all 36 `fun_vrelop_` constructors (incl. I64 with `sx.U`) are generic in `sx`, so `Ho` is not used; (d) the float `v_Inn` is chosen by `exact (rfl : isize Inn.I32 = _)` / `Inn.I64` as Rocq does with `eqxx`; (e) `mk_uN_eta` is not needed: `uN.mk_uN (proj_uN_0 u) = u` holds by `rfl` in Lean (structure eta), so `feq_bit` etc. fit `wf_uN 1 (mk_uN (proj_uN_0 (feq_ ..)))` directly. All 36 (J/F, op) cases close; sorryAx in `#print axioms` comes only from the earlier sorry lemmas and `extend___is_wf`.

Proof body (after `:= by`):
```lean
  intro Hsh Hop H1 H2
  -- Lean's `Map₂` is `zipWith` (Rocq's `list_zipWith`)
  have hMap2 : ∀ (α β γ : Type) (f : α → β → γ) (l1 : List α) (l2 : List β),
      Map₂ f l1 l2 = List.zipWith f l1 l2 := by
    intro α β γ f l1 l2
    simp [Map₂, List.ap, List.zipWith_map_left]
  cases Hop with
  | vrelop__case_0 J M o Ho Hs =>
    -- integer lane shapes
    subst Hs
    have HL1 := lanes_Jnn_form J M c1 Hsh H1
    have HL2 := lanes_Jnn_form J M c2 Hsh H2
    have HS1 := jlane_some _ _ HL1
    have HS2 := jlane_some _ _ HL2
    have Hsz := lanes_size_eq (lanetype_Jnn J) M c1 c2
    rcases o with _ | _ | sx | sx | sx | sx
    case' LT =>
      obtain ⟨vs, H3, Hw, Hvs⟩ := zip_lane_rel J (fun a b r => fun_ilt_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN 1 (uN.mk_uN (proj_uN_0 r))) _ _
        (fun a b Ha Hb => (icmp_total_bit _ sx a b Ha Hb).1) HL1 HL2 Hsz
    case' GT =>
      obtain ⟨vs, H3, Hw, Hvs⟩ := zip_lane_rel J (fun a b r => fun_igt_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN 1 (uN.mk_uN (proj_uN_0 r))) _ _
        (fun a b Ha Hb => (icmp_total_bit _ sx a b Ha Hb).2.1) HL1 HL2 Hsz
    case' LE =>
      obtain ⟨vs, H3, Hw, Hvs⟩ := zip_lane_rel J (fun a b r => fun_ile_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN 1 (uN.mk_uN (proj_uN_0 r))) _ _
        (fun a b Ha Hb => (icmp_total_bit _ sx a b Ha Hb).2.2.1) HL1 HL2 Hsz
    case' GE =>
      obtain ⟨vs, H3, Hw, Hvs⟩ := zip_lane_rel J (fun a b r => fun_ige_ (lsizenn (lanetype_Jnn J)) sx a b r)
        (fun r => wf_uN 1 (uN.mk_uN (proj_uN_0 r))) _ _
        (fun a b Ha Hb => (icmp_total_bit _ sx a b Ha Hb).2.2.2) HL1 HL2 Hsz
    all_goals cases J
    -- Rocq: `eexists; econstructor`
    all_goals (apply Exists.intro; constructor)
    -- the equations defining the lane lists / result (Rocq: `apply: eqxx`)
    all_goals try (first
      | exact (rfl : (_ : List lane_) = _)
      | exact (rfl : (_ : List iN) = _)
      | exact (rfl : (_ : vec_) = _))
    all_goals try exact H3
    -- Rocq's `vrelop_close`
    all_goals try (first
      | exact HS1 | exact HS2 | exact Hsz | exact Hsh | exact Hvs | exact Hvs.trans Hsz | exact Hw
      | exact rfl
      | exact Forall2_all _ _ _ _ _ (fun _ _ => ieq_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => ine_bit _ _ _) Hsz
      | (rw [hMap2]; apply Forall_zipWith; intro a b
         exact wf_lane_.lane__case_0 _ _ _ (extend___is_wf _ _ _ _ _ (by first | exact ieq_bit _ _ _ | exact ine_bit _ _ _) rfl) rfl)
      | (refine Forall_map_P _ _ _ _ _ _ ?_ Hw
         intro a ha
         exact wf_lane_.lane__case_0 _ _ _ (extend___is_wf _ _ _ _ _ ha rfl) rfl))
  | vrelop__case_1 F M o Hs =>
    -- float lane shapes
    subst Hs
    have HL1 := lanes_Fnn_form F M c1 Hsh H1
    have HL2 := lanes_Fnn_form F M c2 Hsh H2
    have HS1 := flane_some _ _ HL1
    have HS2 := flane_some _ _ HL2
    have Hsz := lanes_size_eq (lanetype_Fnn F) M c1 c2
    cases F
    all_goals cases o
    all_goals (apply Exists.intro; constructor)
    -- choose `v_Inn` with `isize v_Inn = size F` (Rocq: `exact: (eqxx (isize Inn_I32))`)
    all_goals try (first | exact (rfl : isize Inn.I32 = _) | exact (rfl : isize Inn.I64 = _))
    all_goals try (first
      | exact (rfl : (_ : List lane_) = _)
      | exact (rfl : (_ : List iN) = _)
      | exact (rfl : (_ : vec_) = _))
    all_goals try (first
      | exact HS1 | exact HS2 | exact Hsz | exact Hsh
      | (cases Hsh with | shape_case_0 _ _ hd hm => exact wf_shape.shape_case_0 _ _ hd hm)
      | exact rfl | decide
      | exact Forall2_all _ _ _ _ _ (fun _ _ => feq_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => fne_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => flt_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => fgt_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => fle_bit _ _ _) Hsz
      | exact Forall2_all _ _ _ _ _ (fun _ _ => fge_bit _ _ _) Hsz
      | (rw [hMap2]; apply Forall_zipWith; intro a b
         exact wf_lane_.lane__case_0 _ _ _ (extend___is_wf _ _ _ _ _ (by first | exact feq_bit _ _ _ | exact fne_bit _ _ _ | exact flt_bit _ _ _ | exact fgt_bit _ _ _ | exact fle_bit _ _ _ | exact fge_bit _ _ _) rfl) rfl))
```

## `invsigned_total_32m1`  (TypeProgress.lean:1082; Rocq type_progress.v:2442-2445)

- status: proved
- earlier lemmas that are still `sorry` and are used: invsigned_total (618, still sorry)
- notes: Rocq: `apply: invsigned_total; by vm_compute.` Here `exact invsigned_total 32 _ (by decide) (by decide)`.

Proof body (after `:= by`):
```lean
  exact invsigned_total 32 _ (by decide) (by decide)
```

## `Forall_list_slice`  (TypeProgress.lean:1088; Rocq type_progress.v:2447-2456)

- status: proved
- earlier lemmas that are still `sorry` and are used: none
- notes: Not by induction as in Rocq: `Forall` is membership-based, `x ∈ take j (drop i l) → x ∈ l` by `List.mem_of_mem_take`/`List.mem_of_mem_drop`.

Proof body (after `:= by`):
```lean
  intro H x hx
  exact H x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
```

## `mem_bytes_wf`  (TypeProgress.lean:1095; Rocq type_progress.v:2458-2469)

- status: proved
- earlier lemmas that are still `sorry` and are used: none
- notes: Rocq structure kept: case `k < |ms|` (then `ms[k]! = ms[k]` by `getElem!_pos`, `wf_meminst` inverted after `generalize` to avoid dependent-elimination failure on the opaque index `ms[k]!`) vs out of range (`getElem!_neg`: `ms[k]! = default`, `(default : meminst).BYTES = []` by `rfl`). `getElem!_pos/_neg` are core Lean lemmas (not the TypePreservation helpers).

Proof body (after `:= by`):
```lean
  intro Hall
  by_cases E : k < ms.length
  · have H : wf_meminst (ms[k]!) := by
      rw [getElem!_pos ms k E]
      exact Hall _ (List.getElem_mem E)
    generalize ms[k]! = m at H ⊢
    cases H with
    | meminst_case_ _ _ _ h => exact h
  · rw [getElem!_neg ms k E]
    have hd : (default : meminst).BYTES = [] := rfl
    rw [hd]
    intro b hb
    simp at hb
```

## `wf_config_mem_bytes`  (TypeProgress.lean:1101; Rocq type_progress.v:2471-2480)

- status: proved
- earlier lemmas that are still `sorry` and are used: mem_bytes_wf (1095; proved in this batch)
- notes: Rocq: three `inversion`s (wf_config, wf_state, wf_store) then `mem_bytes_wf`; here the same via `cases` with explicit constructor patterns (`config_case_0`, `state_case_0`, `store_case_`; the 10th slot of `store_case_` is the `MEMS` Forall). `fun_mem (mk_state s f) x` unfolds by defeq to `s.MEMS[f.MODULE.MEMS[x]!]!`. #print axioms shows Classical.choice/Quot.sound/propext (standard axioms, from `cases` on the generated inductives), no project axioms.

Proof body (after `:= by`):
```lean
  intro H
  cases H with
  | config_case_0 _ _ hs _ =>
    cases hs with
    | state_case_0 _ _ hst _ =>
      cases hst with
      | store_case_ _ _ _ _ _ _ _ _ _ h _ =>
        exact mem_bytes_wf _ _ h
```

## `all_and_Forall`  (TypeProgress.lean:1109; Rocq type_progress.v:2486-2492)

- status: proved
- earlier lemmas that are still `sorry` and are used: none
- notes: `List.all_eq_true` + `Bool.and_eq_true`.

Proof body (after `:= by`):
```lean
  intro h
  rw [List.all_eq_true] at h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have := h x hx
    rw [Bool.and_eq_true] at this
    exact this.1
  · have := h x hx
    rw [Bool.and_eq_true] at this
    exact this.2
```

## `Forall_and_all`  (TypeProgress.lean:1115; Rocq type_progress.v:2494-2501)

- status: proved
- earlier lemmas that are still `sorry` and are used: none
- notes: Converse of `all_and_Forall`, same lemmas.

Proof body (after `:= by`):
```lean
  intro HP HQ
  rw [List.all_eq_true]
  intro x hx
  rw [Bool.and_eq_true]
  exact ⟨HP x hx, HQ x hx⟩
```

## `packnum_not_none`  (TypeProgress.lean:1122; Rocq type_progress.v:2503-2511)

- status: proved
- earlier lemmas that are still `sorry` and are used: none
- notes: Rocq: `destruct lt; simpl; try by []; inversion Hwf ...; destruct v_Inn/v_Fnn`. Lean: split the number (`mk_num__0`/`mk_num__1`), the lane type, and the `Inn`/`Fnn` tag (24 cases); the 4 matching scalar cases and the I8/I16 (`OMap`) cases are closed by `simp [packnum_ ...]` and the 16 mismatched ones by inverting `Hwf` (its type equation `unpack lt = numtype_Inn I` is false by `simp_all`).

Proof body (after `:= by`):
```lean
  intro Hwf
  rcases c with ⟨I, x⟩ | ⟨F, x⟩ <;> cases lt <;> (try cases I) <;> (try cases F)
  all_goals first
    | (simp [packnum_]; done)
    | (simp [packnum_, OMap, size, valtype_numtype, unpack, lanetype_packtype]; done)
    | (exfalso; cases Hwf; simp_all [unpack, numtype_Inn, numtype_Fnn])
```

## Final Lean check output

`cd spectec/src/test-lean-claude && lake env lean <scratch>/Work_final.lean` (exit 0; no errors, no warnings; only the `#print axioms` lines):
```
'TLC.ieq_bit_proof' depends on axioms: [sorryAx]
'TLC.ine_bit_proof' depends on axioms: [sorryAx]
'TLC.icmp_total_bit_proof' depends on axioms: [sorryAx]
'TLC.Forall_zipWith_proof' depends on axioms: [propext]
'TLC.Forall2_all_proof' does not depend on any axioms
'TLC.Forall_map_P_proof' depends on axioms: [propext, Quot.sound]
'TLC.vrelop_some_proof' depends on axioms: [propext, sorryAx, feq_bit, fge_bit, fgt_bit, fle_bit, flt_bit, fne_bit]
'TLC.invsigned_total_32m1_proof' depends on axioms: [propext, sorryAx]
'TLC.Forall_list_slice_proof' depends on axioms: [propext]
'TLC.mem_bytes_wf_proof' depends on axioms: [propext]
'TLC.wf_config_mem_bytes_proof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TLC.all_and_Forall_proof' depends on axioms: [propext, Quot.sound]
'TLC.Forall_and_all_proof' depends on axioms: [propext, Quot.sound]
'TLC.packnum_not_none_proof' depends on axioms: [propext]
```

`lake env lean <scratch>/TypeProgressMerged.lean` (whole TypeProgress.lean with the 14 proofs substituted): 0 errors; `Elapsed 0:04.98, Maximum resident set size 3887616 kB`. `declaration uses sorry` warnings in the region 1020-1280 are only at lines 1025 (`res_bool_bit`), 1268 (`lanes_nth_wf`), 1280 (`vstore_lane_progress`), none at the 14 targets.

`lake env lean <scratch>/TypeProgressMerged2.lean` (axiomatized earlier sorry lemmas) `#print axioms` excerpt: `TLC.vrelop_some` depends on axioms: [propext, sorryAx (only via extend___is_wf), Quot.sound, feq_bit, fge_bit, fgt_bit, flane_some, fle_bit, flt_bit, fne_bit, ige_total, igt_total, ile_total, ilt_total, jlane_some, lanes_Fnn_form, lanes_Jnn_form, lanes_size_eq, res_bool_bit, zip_lane_rel]; `TLC.wf_config_mem_bytes` depends on [propext, Classical.choice, Quot.sound] (standard); `TLC.mem_bytes_wf` [propext]; `TLC.packnum_not_none` [propext]; `TLC.Forall2_all` none.

## Safety check at END
```
safety check [prove-H11] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T130504.658965104Z-prove-H11-1478934.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

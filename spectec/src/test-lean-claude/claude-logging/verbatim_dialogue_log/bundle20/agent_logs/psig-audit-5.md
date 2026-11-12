# psig-audit-5: independent signature audit of progress chunk 5

## Task
Independent SIGNATURE AUDIT of the translator's (psig-5) Lean output for chunk 5 of
`type_progress.v` (lines 2214-2624, 31 declarations). For each Rocq declaration: check the Lean
signature states the same thing as Rocq (binders, premises, conclusion, quantifiers). Flag
mismatch / undocumented-deviation / suspicious / doc-only. No Lean runs, no repo edits.

Read: brief `scratchpad/briefs/progress_sig_brief.md`, task `scratchpad/briefs/task_psig_5.md`.

## Safety check (START), run from /home/zhengyew/spectec

```
safety check [psig-audit-5] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T115339.818699235Z-psig-audit-5-1439401.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Per-lemma audit
(written incrementally below)

### Definitions verified (Lean `wasm2.0.lean` / project files vs Rocq `wasm.v`)
- `Forall` (wasm2.0.lean:17) is membership-based, equivalent to `List.Forall`. `Forall₂` (:20) is zip-based.
  `Forall₃` (:23) is `∀ t ∈ (xs₁.zip xs₂).zip xs₃, P t.1.1 t.1.2 t.2`, the same argument order as Rocq's
  inductive `List_Forall3` (wasm.v:88: `R x y z` with x, y, z taken from lists 1, 2, 3).
- `jlane`/`flane` (TypeProgress.lean:112/116) match Rocq type_progress.v:2165-2168 exactly.
- `lane_` ctors: `mk_lane__0 : Jnn → iN`, `mk_lane__1 : Fnn → fN` (:934). `proj_lane__0/1` return `Option` (:952/958).
- Rocq `res_N := N` (wasm.v:342). `!(x) := the x` (`None ↦ default_val`, wasm.v:12,310). `x [| a |] := lookup_total`
  (`seq.nth default_val`, wasm.v:10,312). `(u :> N)` for uN is `proj_uN_0` (wasm.v:529).
- `%BN` is binN_scope, where `<` is `N.lt` (a Prop) (wasm.v:139-153). `list_slice l i j` drops i, then takes j
  (wasm.v:56-63), so it equals `List.take j (List.drop i l)`, as in the generated code (wasm2.0.lean:9567).
  `list_zipWith` is map over the truncating `seq.zip` (wasm.v:22), so it equals `List.zipWith`.
  `list_repeat x n := List.repeat x (N.to_nat n)` (wasm.v:19).
- `nat_of_bool` (wasm2.0.lean:2646) and Rocq `res_bool` (wasm.v:4192) come from the same spectec def 3-numerics:9.1-9.22.
- `vec_ = vN = iN = uN` (abbrevs :964, :411, :200), so `wf_uN 128 c` with `c : vec_` type-checks in both.
- `fun_vbinop_ : … → Option (List vec_) → Prop` (:6862) and `fun_vrelop_ : … → Option vec_ → Prop` (:8404)
  match Rocq (wasm.v:8160/9705). Both backends generate the same "before_case" fallthrough structure
  (92 occurrences of `fun_vbinop__before_..._case_52`/`fun_vrelop__before_..._case_36` in each).
- `fun_inv_signed_` (:2669) has the same two cases as Rocq (wasm.v:4211). For i = -1, N = 32, case_1 applies.
- `fun_ilt_` (:3754) is total on wf inputs because `fun_signed_` is total. `ieq_`/`ine_` return `mk_uN (nat_of_bool _)`.
- `packnum_` (:4596) is a def. It returns `some` on every `wf_num_ (unpack lt)` input, since the I8/I16 cases are
  `OMap … (size (valtype_numtype I32)) = some _`.
- `lanes_` is opaque in Lean (:4644) and an Axiom in Rocq (wasm.v:6117). Rocq's `lanes_nth_wf` proof uses
  `lanes__is_wf` + `lanes_len`. Lean has both: `lanes__is_wf` (wasm2.0.lean:4651, sorry) and
  `axiom lanes_len` (HelperLemmas.lean:785). So the Lean statement is as provable as Rocq's.
- `meminst` derives `Inhabited` (:11458), so the default has BYTES = [] and the out-of-range case of
  `mem_bytes_wf` holds trivially. `fun_mem` (:12237) uses `[..]!`. The chain wf_config → wf_state →
  wf_store → `Forall wf_meminst MEMS` holds (:11964, :11554, :11516).
- `Step.vstore_lane_val` (:14779) states the premise as `(v_M : Rat) = ((128 : Rat) / (v_N : Rat))` with
  `v_N = jsize v_Jnn`, which confirms the translator's claim about the Rat form. Like Rocq, it has no
  bounds premise.
- `wf_val`/`wf_num_` (:11328/:906): a CONST I32 value has `wf_uN 32`. `wf_bit` is `i = 0 ∨ i = 1`. `wf_dim` is in {1,2,4,8,16}.
  `wf_ishape` (:1309) is `wf_shape v_shape ∧ fun_lanetype v_shape = lanetype_Jnn J`.
- Name clashes: none of the 31 names is declared in wasm2.0.lean or any project .lean file.
- All 31 doc-comment line numbers match the Rocq headers (2214 … 2619).

### Per-lemma verdicts (Rocq binders, premises and conclusion compared one by one)
| # | Rocq | Verdict | Notes |
|---|---|---|---|
| 1 | zip_flane_wf | OK | `fop : N → fN → fN → List fN`. The zip-based Forall₂ conclusion is equivalent because `L1.length = L2.length` is a premise. The doc says so. |
| 2 | zip_lane_rel | OK | Forall₃ arg order `vs L1 L2` matches. Equivalent under the premise plus the `vs.length = L1.length` conjunct. The doc says so. |
| 3 | vbinop_some | OK | types sh/op/c1/c2 and `some r : Option (List vec_)` match |
| 4 | mk_uN_eta | OK | `(u :> N)` is `proj_uN_0 u` |
| 5 | res_bool_bit | OK | `res_bool` is `nat_of_bool` (same spectec def) |
| 6 | ieq_bit | OK | |
| 7 | ine_bit | OK | |
| 8 | icmp_total_bit | OK | conjunct order ilt/igt/ile/ige matches; `r : u32` |
| 9 | Forall_zipWith | OK | explicit A B C as in Rocq; truncating zip on both sides |
| 10 | Forall2_all | OK | length premise kept; equivalent |
| 11 | Forall_map_P | OK | binder order P Q f l matches |
| 12 | vrelop_some | OK | `some r : Option vec_` |
| 13 | invsigned_total_32m1 | OK | `(0:Int) - 1` |
| 14 | Forall_list_slice | OK | `{T}` implicit as in Rocq; take/drop order correct |
| 15 | mem_bytes_wf | OK | default meminst has BYTES = [] |
| 16 | wf_config_mem_bytes | OK | binders s f ais x |
| 17 | all_and_Forall | OK | `List.all l p = true`; `is_true` is `= true` |
| 18 | Forall_and_all | OK | |
| 19 | packnum_not_none | OK | `!= None` is `≠ none` |
| 20 | lanes_nth_wf | OK | `%BN <` is `N.lt` (a Prop); index in range |
| 21 | vstore_lane_progress | OK | binders s f n1 memarg laneidx c1 J M; the Qeq_bool premise is `=` on Rat, same as the Step rule |
| 22 | Forall2_map_l | OK | map preserves length, so equivalent |
| 23 | invert_typeof_I32_wf | OK | |
| 24 | size_list_repeat | OK | Kept rather than NOT PORTED. That is a judgement call, flagged by the translator, and harmless. |
| 25 | Forall_list_repeat | OK | |
| 26 | bit_of_wf1 | OK | |
| 27 | wf_dim_le16 | OK | |
| 28 | wf_ishape_inv | OK | |
| 29 | holds_upto_intro | OK | `TLC.holds_upto` = `Forall P (List.range n)` matches Rocq's `iotaN 0 n` |
| 30 | jlane_proj_wf | OK | |
| 31 | jlane_map_proj | OK | |

Ltacs `vlane_close`/`bit_close`/`vrelop_close` (2252/2380/2386) are not on the task list, so having no markers for them is fine.

### Non-blocking usability note (not a fidelity problem)
`Forall_zipWith` is stated over `List.zipWith`, following the brief's table, so it is faithful to Rocq.
Lean's generated `fun_vrelop_` writes the lane-wise results as `Map₂ f l1 l2`
(= `List.zipWith (·  ·) (List.map f l1) l2`, wasm2.0.lean:27-28,8410), where Rocq writes `list_zipWith f l1 l2`.
`apply Forall_zipWith` against `Map₂` would unify with `f := fun g x => g x` and leave an unprovable side goal.
When porting `vrelop_some`'s proof, rewrite with a small `Map₂ f l1 l2 = List.zipWith f l1 l2` lemma first.

### Result
31/31 OK, 0 problems.

## Safety check (END), run from /home/zhengyew/spectec

```
safety check [psig-audit-5] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T120102.765656476Z-psig-audit-5-1440774.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written by this agent: only this log (no scratch files were needed; no Lean runs; no repo edits).

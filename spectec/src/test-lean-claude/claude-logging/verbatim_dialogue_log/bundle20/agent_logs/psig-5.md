# psig-5 log — bundle20 progress signature translation, chunk 5 of 6

## Task

Translate 31 Rocq declarations of `spectec/test-rocq/theories/type_progress.v` (lines 2214-2624) into
Lean 4 signatures (bodies `sorry`), in Rocq order:
zip_flane_wf, zip_lane_rel, vbinop_some, mk_uN_eta, res_bool_bit, ieq_bit, ine_bit, icmp_total_bit,
Forall_zipWith, Forall2_all, Forall_map_P, vrelop_some, invsigned_total_32m1, Forall_list_slice,
mem_bytes_wf, wf_config_mem_bytes, all_and_Forall, Forall_and_all, packnum_not_none, lanes_nth_wf,
vstore_lane_progress, Forall2_map_l, invert_typeof_I32_wf, size_list_repeat, Forall_list_repeat,
bit_of_wf1, wf_dim_le16, wf_ishape_inv, holds_upto_intro, jlane_proj_wf, jlane_map_proj

Brief: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/progress_sig_brief.md`
Task file: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/task_psig_5.md`
Scratch: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-5/Chunk.lean`

Safety rule: write only this log file inside the repo + scratch files in the scratch dir; no repo edits;
no state-changing git; no agents spawned.

## Safety check (START)

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-5`

```
safety check [psig-5] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113435.239337142Z-psig-5-1430555.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Reading

- Brief and task file (fully).
- Pre-extracted statements: `scratchpad/progress/progress_rocq_stmts.md` entries [145]-[178].
- `type_progress.v` 2200-2260 (zip_lane_wf sibling + zip_flane_wf/zip_lane_rel with proofs) and the
  comment lines/lemma heads of 2282-2624 (awk filter).
- `TypeProgress.lean` 1-200 (definitions `jlane`, `flane`, `typeof`, ...; style).
- `wasm.v` (Rocq generated): `lookup_total`, `list_repeat` (`List.repeat x (N.to_nat n)`),
  `list_zipWith` (`map … (zip xs ys)`, truncating), `list_slice` (drop i then take j), `holds_upto`
  (wasm.v:107), `res_N := N` (342), `res_bool` (4192, 3-numerics.spectec:9.1-9.22), `List_Forall3`
  (88, arg order `R l l' l''`), Rocq result types of `fun_vbinop_` (`option (seq vec_)`),
  `fun_vrelop_` (`option vec_`), `fun_inv_signed_` (`res_N -> Z -> N`), and the
  `vstore_lane_val` rule premise `((v_M : Q) == ((128%N : Q) / (v_N : Q))%Q)%Q` (16435).
- `wasm2.0.lean`: `Forall`/`Forall₂`/`Forall₃` (17-24, zip-based), `uN`/`proj_uN_0`/`wf_uN`
  (166-180), `bit`/`wf_bit` (137-145), `dim`/`wf_dim` (775-790), `lane_`/`wf_lane_`/`proj_lane__0/1`
  (934-962), `sz` (992), `ishape`/`wf_ishape` (1299-1312), `nat_of_bool` (2646; SAME spectec source
  3-numerics.spectec:9.1-9.22 as Rocq `res_bool`), `ieq_`/`ine_`/`fun_ilt_`/`fun_igt_`/`fun_ile_`/
  `fun_ige_` (3684-3775), `fun_vbinop_ : … → Option (List vec_) → Prop` (6862), `fun_vrelop_ : … →
  Option vec_ → Prop` (8404), `fun_inv_signed_ : N → Int → Nat → Prop` (2669), `meminst` (11458,
  derives Inhabited), `admininstr.VSTORE_LANE` (11624), `Step.vstore_lane_val` (14779; renders the
  Rocq `Qeq` premise as `(v_M : Rat) = ((128 : Rat) / (v_N : Rat))`), slices rendered as
  `List.take j (List.drop i l)` (e.g. 9567).
- `ExtensionLemmas.lean:89`: `TLC.holds_upto P n := Forall P (List.range n)` (abbrev) — in scope.
- Name-clash grep of all 31 names over wasm2.0/HelperLemmas/Subtyping/TypingLemmas/
  TypePreservationPure/ExtensionLemmas/TypePreservation/TypeProgress: **no clashes**.

## Per-lemma decisions (31/31 ported; 0 NOT PORTED; 0 forced deviations)

General mappings used (translation table, not deviations): `seq`→`List`; `N`/`res_N`→`N` (=`Nat`);
`size l`→`l.length`; `!(o)`→`Option.get!`; `l [| k |]`→`l[k]!`; `(u :> N)` (uN coercion)→`proj_uN_0 u`;
`%BN`/`%num` comparisons→Prop `<`/`≤` on `Nat`; `List.Forall`→`Forall`; `List.Forall2`→`Forall₂`;
`List_Forall3`→`Forall₃` (same arg order); `seq.map`→`List.map`; Rocq's explicit type binders
`forall (A B : Type)` kept explicit; `{T : Type}` (Forall_list_slice) kept implicit.

| # | Rocq (line) | Lean | Decision |
|---|---|---|---|
| 1 | zip_flane_wf (2214) | zip_flane_wf | OK. `fop : N → fN → fN → List fN` (Rocq `res_N := N`). `Forall₂` only in the CONCLUSION; the length fact Rocq's `Forall2` carries is already the premise `L1.length = L2.length` → equivalent, no hlen. |
| 2 | zip_lane_rel (2230) | zip_lane_rel | OK. `List_Forall3`→zip-based `Forall₃` in the conclusion; lengths given by conclusion `vs.length = L1.length` + premise `L1.length = L2.length` → equivalent. |
| 3 | vbinop_some (2282) | vbinop_some | OK. `fun_vbinop_ … (some r)`, `r : List vec_` (Rocq `option (seq vec_)`). |
| 4 | mk_uN_eta (2327) | mk_uN_eta | OK. `uN.mk_uN (proj_uN_0 u) = u`. |
| 5 | res_bool_bit (2332) | res_bool_bit | OK. Rocq `res_bool` = Lean generated `nat_of_bool` (same spectec def 3-numerics.spectec:9.1-9.22). |
| 6 | ieq_bit (2335) | ieq_bit | OK. |
| 7 | ine_bit (2338) | ine_bit | OK. |
| 8 | icmp_total_bit (2341) | icmp_total_bit | OK. Four parenthesised `∃` conjuncts (right-assoc `∧` = Rocq `/\`). |
| 9 | Forall_zipWith (2360) | Forall_zipWith | OK. `list_zipWith f l1 l2` (map over truncating mathcomp `zip`) → `List.zipWith f l1 l2`. |
| 10 | Forall2_all (2367) | Forall2_all | OK. `Forall₂` in the conclusion; length is a premise → equivalent. |
| 11 | Forall_map_P (2375) | Forall_map_P | OK. |
| 12 | vrelop_some (2400) | vrelop_some | OK. `fun_vrelop_ … (some r)`, `r : vec_`. |
| 13 | invsigned_total_32m1 (2442) | invsigned_total_32m1 | OK. `(0 - 1)%Z` kept literally as `(0 : Int) - 1`. |
| 14 | Forall_list_slice (2447) | Forall_list_slice | OK. `list_slice l i j` → `List.take j (List.drop i l)` (form used by the generated code). |
| 15 | mem_bytes_wf (2458) | mem_bytes_wf | OK. `BYTES (ms [| k |])` → `(ms[k]!).BYTES` (`meminst` derives `Inhabited`). |
| 16 | wf_config_mem_bytes (2471) | wf_config_mem_bytes | OK. |
| 17 | all_and_Forall (2486) | all_and_Forall | OK. mathcomp `all` → `List.all`; `is_true` coercions → `· = true`. Meaningful in Lean (`const_list` is `List.all`), so ported. |
| 18 | Forall_and_all (2494) | Forall_and_all | OK (converse). |
| 19 | packnum_not_none (2503) | packnum_not_none | OK. boolean `!= None` → `≠ none`. |
| 20 | lanes_nth_wf (2513) | lanes_nth_wf | OK. `(k < v_N)%BN` → `k < v_N`. |
| 21 | vstore_lane_progress (2527) | vstore_lane_progress | OK. `Qeq_bool (M : Q) ((128%num : Q) / ((jsize J) : Q))%Q = true` → `(M : Rat) = ((128 : Rat) / (jsize J : Rat))` (Qeq is value equality; Lean `Rat` is normalised; this is exactly how generated `Step.vstore_lane_val` renders the same spectec premise). Binder names `memarg`/`laneidx` kept (shadow the types, harmless). |
| 22 | Forall2_map_l (2551) | Forall2_map_l | OK. `Forall₂` conclusion; lengths equal by `List.length_map` → equivalent. |
| 23 | invert_typeof_I32_wf (2556) | invert_typeof_I32_wf | OK. |
| 24 | size_list_repeat (2568) | size_list_repeat | OK. `(List.replicate n x).length = n` (= core `List.length_replicate`). Kept (not NOT PORTED) because it is a meaningful list fact used by name in Rocq proofs, unlike `length_size`. |
| 25 | Forall_list_repeat (2575) | Forall_list_repeat | OK. |
| 26 | bit_of_wf1 (2579) | bit_of_wf1 | OK. |
| 27 | wf_dim_le16 (2587) | wf_dim_le16 | OK. Binder `M` shadows the generated `abbrev M`, harmless. |
| 28 | wf_ishape_inv (2594) | wf_ishape_inv | OK. `∃ (J : Jnn) (M : N), …`. |
| 29 | holds_upto_intro (2604) | holds_upto_intro | OK. Uses `TLC.holds_upto` (ExtensionLemmas.lean:89). |
| 30 | jlane_proj_wf (2614) | jlane_proj_wf | OK. |
| 31 | jlane_map_proj (2619) | jlane_map_proj | OK. |

Not in my list (and so not emitted): the three `Ltac`s in this line range, `vlane_close` (2252),
`bit_close` (2380), `vrelop_close` (2386) — Rocq tactic macros with no declaration counterpart.

No `Forall₂` occurs as a PREMISE anywhere in this chunk, so no `hlen` deviation was needed; the four
`Forall₂`/`Forall₃` CONCLUSIONS (zip_flane_wf, zip_lane_rel, Forall2_all, Forall2_map_l) are
equivalent to Rocq's because the length fact is a premise / part of the conclusion / automatic.

## Lean check

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/psig-5/Chunk.lean`
First run: 31 lines of output, all `warning: declaration uses 'sorry'` (one per theorem, lines
10, 24, 35, 43, 50, 56, 61, 67, 79, 87, 94, 101, 109, 116, 124, 131, 140, 147, 155, 162, 175, 193,
200, 209, 215, 221, 226, 232, 242, 249, 257); **no errors, no other diagnostics**. Last lines:

```
…/agents/psig-5/Chunk.lean:242:8: warning: declaration uses `sorry`
…/agents/psig-5/Chunk.lean:249:8: warning: declaration uses `sorry`
…/agents/psig-5/Chunk.lean:257:8: warning: declaration uses `sorry`
```

## Safety check (END)

Command (from `/home/zhengyew/spectec`):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-5`

```
safety check [psig-5] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T114124.414276783Z-psig-5-1435411.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written: this log (inside the target dir) and
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-5/Chunk.lean`
(scratch, outside the repo). No repo file edited; no git commands; no agents spawned.

## Result

31/31 declarations ported (all OK; 0 forced deviations; 0 NOT PORTED). Chunk compiles with only
`sorry` warnings.

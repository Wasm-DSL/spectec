# psig-6 log (bundle20 progress signature translation, chunk 6 of 6)

## Task

Translate 32 Rocq declarations of `spectec/test-rocq/theories/type_progress.v` (lines 2636-6159) into
Lean 4 signatures (bodies `sorry`), in Rocq order:
evens_odds_ind, evens_odds_concat, evens_odds_size, Forall_evens, Forall_odds, Forall2_of_Forall,
list_slice_size_eq, zip_lane_wf2, zip_wf, size_zipWith_eq, shape_lanes_even, add_sub_parens,
call_indirect_progress, vcvtop_lane_total, vcvtop_lanes_total, setproduct2_Forall, setproduct1_Forall,
setproduct_Forall, setproduct_nonempty, setproduct_pick, halfop_total, zeroop_total, zero_lane_wf,
vcvtop_step_full, vcvtop_step_half, vcvtop_step_zero, vcvtop_zero_numtype, vcvtop_full_lsize,
vload_shape64_wf, vload_shape64_stuck, vcvtop_trunc_sat_i16_wf_instr, vcvtop_trunc_sat_i16_stuck.

Scratch dir: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-6/`
(only `Chunk.lean` there). No repo file other than this log is written.

## Safety check (START), run from /home/zhengyew/spectec

```
$ bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-6
safety check [psig-6] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113605.161518765Z-psig-6-1432040.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## What I read

- Brief `briefs/progress_sig_brief.md` (fully), task file `briefs/task_psig_6.md`.
- Statements: `scratchpad/progress/progress_rocq_stmts.md` entries [181]-[222] (sed range only).
- `TypeProgress.lean` lines 1-200 (definitions/style) and 1250-1327 (main theorems, style).
- Rocq source `type_progress.v` 2615-2740, comment/header lines of 2727-3085, and 6085-6159.
- Rocq `wasm.v`: `list_zipWith` (truncating `seq.zip`), `list_slice` (= drop `i` then take `j`),
  `binN_scope` (`%BN`: `+` = `N.add`, `-` = `N.sub`, `<=` = `N.le` (Prop), `>?` = `N_gtb` (bool)),
  coercions `Z.to_N : Z >-> N`, `Z.of_N : N >-> Z`, `proj_uN_0_coercion : Coercion uN N`,
  `|x| = N.of_nat (size x)`; Rocq `concat_`/`setproduct_` take `X : eqType`.
- Lean `wasm2.0.lean` (the one in test-lean-claude; grep + short ranges): `Forall`/`Forall₂`
  (zip-based), `concat_`, `setproduct{,1,2}_` (take `X : Type`), `uN`/`wf_uN`, `lanetype`, `Jnn`,
  `Fnn`, `dim`, `lsize`, `shape`, `wf_shape`, `fun_lanetype`, `lane_`, `wf_lane_`, `proj_lane__0`,
  `proj_num__0`, `fun_zero`, `half`, `zero`, `vcvtop__` + `wf_vcvtop__`, `memarg`, `vloadop_`,
  `wf_vloadop_`, `packnum_`, `lanes_`, `inv_lanes_`, `fun_zeroop`/`fun_halfop`/`fun_lcvtop__`
  headers, `fun_mem`, `meminst`, constructors `instr/admininstr.{CONST,VCONST,VCVTOP,VLOAD,CALL_INDIRECT}`;
  `vec_ = vN = iN = uN`, `M = Nat`, `idx = u32 = uN`.
- Name clashes: grep for all 32 names as `theorem|lemma|def|abbrev|axiom|opaque|inductive` in the
  project `.lean` files and both `wasm2.0.lean` copies: **none found**; no `_p` suffix needed.

## Rocq cross-check (read-only, scratch dir only)

`add_sub_parens` mixes `N`/`Z` coercions, so its elaboration was checked with the local opam
switch's `coqc` (`spectec/test-rocq/_opam`) against the compiled
`spectec/_build/default/test-rocq/theories/wasm.vo` (read only), in a scratch file
`agents/psig-6/rocq/Chk2.v`. That `.vo` is stale (no `BN` scope, no `N`/`Z` coercions), so the
scratch file re-declares wasm.v's `binN_scope` notations, `N_gtb`, and the two coercions verbatim.
Result:

```
add_sub_parens
     : ∀ (n1 n2 : N) (n3 : Z),
         (n3 <= Z.of_N n2)%Z
         → (n1 + Z.to_N (Z.of_N n2 - n3))%BN =
           Z.to_N (Z.of_N (n1 + n2)%BN - n3)
```

(A first attempt that also contained `vload_shape64_stuck` hung in `:>` typeclass search against
the stale `.vo`; it was abandoned. My cleanup `pkill -f <pattern>` matched its own shell and exited
144; it killed only that coqc job. Nothing outside the scratch dir was touched.)

## Translation conventions used (all equivalences, not deviations)

- `~~ odd (size l)` (mathcomp bool) → `¬ Odd l.length` (Mathlib `Odd`, available via
  `HelperLemmas`' `import Mathlib.Tactic`; `#check` with `pp.fullNames` confirms root `Odd`).
- `~~ vcvtop_trunc_sat_i16 op` → `vcvtop_trunc_sat_i16 op = false`.
- `x != None`, `l != [::]` → `x ≠ none`, `l ≠ []`; `!(x)` → `Option.get! x`.
- `(|l| >? 0)%BN` (bool) → Prop `l.length > 0`; `c \in l` → `c ∈ l`.
- `(i :> N)` → `proj_uN_0 i`; `|BYTES m|` → `m.BYTES.length`; `%BN` `+`/`<=` → Nat `+`/`≤`.
- `list_slice l i j` → `List.take j (List.drop i l)`; `list_zipWith` → `List.zipWith`.
- `Z.of_N` → `Nat → Int` cast; `Z.to_N` → `Int.toNat`.
- Rocq `X : eqType` / `T : eqType` (forced only by Rocq's `concat_`/`setproduct*_` signatures) →
  `Type`, as the Lean generated defs take a plain `Type`. Noted in the doc comments.
- Untyped Rocq binders get their Rocq-inferred types (`c1 : uN` from `wf_uN 128 c1`,
  `v_i : num_`, `x : tableidx`, `y : typeidx`, `z : state`, `ao : memarg`, `h : half`, `z : zero`).

## Per-lemma decisions

| Rocq (line) | Lean | Result |
|---|---|---|
| evens_odds_ind (2636) | `evens_odds_ind` | OK |
| evens_odds_concat (2645) | `evens_odds_concat` | OK (`¬ Odd`; `eqType`→`Type`) |
| evens_odds_size (2652) | `evens_odds_size` | OK (`¬ Odd`) |
| Forall_evens (2658) | `Forall_evens` | OK |
| Forall_odds (2664) | `Forall_odds` | OK |
| Forall2_of_Forall (2670) | `Forall2_of_Forall` | OK: length already a premise, so zip-based `Forall₂` conclusion is equivalent |
| list_slice_size_eq (2679) | `list_slice_size_eq` | OK (`take j (drop i _)`) |
| zip_lane_wf2 (2687) | `zip_lane_wf2` | OK: length already a premise |
| zip_wf (2701) | `zip_wf` | OK (truncating zip on both sides) |
| size_zipWith_eq (2710) | `size_zipWith_eq` | OK |
| shape_lanes_even (2715) | `shape_lanes_even` | OK (`¬ Odd`) |
| add_sub_parens (2727) | `add_sub_parens` | OK (elaboration checked with coqc) |
| call_indirect_progress (2734) | `call_indirect_progress` | OK |
| vcvtop_lane_total (2817) | `vcvtop_lane_total` | OK |
| vcvtop_lanes_total (2849) | `vcvtop_lanes_total` | **DEVIATION**: conjunct `vs.length = L.length` added after the `Forall₂` conjunct of the conclusion (Rocq's `Forall2 _ vs L` implies it; without it the Lean statement is trivially true with `vs = []`) |
| setproduct2_Forall (2871) | `setproduct2_Forall` | OK (`eqType`→`Type`) |
| setproduct1_Forall (2875) | `setproduct1_Forall` | OK (`eqType`→`Type`) |
| setproduct_Forall (2882) | `setproduct_Forall` | OK (`eqType`→`Type`) |
| setproduct_nonempty (2889) | `setproduct_nonempty` | OK (`eqType`→`Type`) |
| setproduct_pick (2897) | `setproduct_pick` | OK (`>?` bool → Prop `>`; `\in` → `∈`) |
| halfop_total (2943) | `halfop_total` | OK |
| zeroop_total (2951) | `zeroop_total` | OK |
| zero_lane_wf (2959) | `zero_lane_wf` | OK |
| vcvtop_step_full (2969) | `vcvtop_step_full` | OK |
| vcvtop_step_half (2991) | `vcvtop_step_half` | OK |
| vcvtop_step_zero (3012) | `vcvtop_step_zero` | OK |
| vcvtop_zero_numtype (3064) | `vcvtop_zero_numtype` | OK |
| vcvtop_full_lsize (3076) | `vcvtop_full_lsize` | OK |
| vload_shape64_wf (6103) | `vload_shape64_wf` | OK |
| vload_shape64_stuck (6107) | `vload_shape64_stuck` | OK |
| vcvtop_trunc_sat_i16_wf_instr (6124) | `vcvtop_trunc_sat_i16_wf_instr` | OK |
| vcvtop_trunc_sat_i16_stuck (6132) | `vcvtop_trunc_sat_i16_stuck` | OK |

NOT PORTED: none. (The Ltacs `vcvtop_cases`/`vcvtop_cases_full` and the definitions
`vcvtop_trunc_sat_i16`/`halfop_of`/`zeroop_of` in this line range are not in my list; the
definitions are already in TypeProgress.lean.)

## Lean check

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/agents/psig-6/Chunk.lean`
(one process at a time; three runs in total: first check, a `#check` verification copy
`ChunkChk.lean` (deleted afterwards), and the final check after a doc-comment wording fix.)

Final run: exit 0; 32 output lines, all `declaration uses 'sorry'` warnings (one per declaration),
0 errors. Last lines:

```
.../agents/psig-6/Chunk.lean:268:8: warning: declaration uses `sorry`
.../agents/psig-6/Chunk.lean:277:8: warning: declaration uses `sorry`
.../agents/psig-6/Chunk.lean:286:8: warning: declaration uses `sorry`
```

`#check` verification (from the `ChunkChk.lean` run), for example:

```
add_sub_parens : ∀ (n1 n2 : ℕ), ∀ n3 ≤ ↑n2, n1 + (↑n2 - n3).toNat = (↑(n1 + n2) - n3).toNat
TLC.evens_odds_size : ∀ (T : Type) (l : List T), ¬Odd l.length → (TLC.evens l).length = (TLC.odds l).length
```

## Safety check (END), run from /home/zhengyew/spectec

```
$ bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-6
safety check [psig-6] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T114808.142122037Z-psig-6-1437880.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written: this log (repo), and in the scratch dir only `agents/psig-6/Chunk.lean`,
`agents/psig-6/final_check.txt`, `agents/psig-6/rocq/{Chk.v,Chk2.v,*.glob,...}` (coqc outputs).

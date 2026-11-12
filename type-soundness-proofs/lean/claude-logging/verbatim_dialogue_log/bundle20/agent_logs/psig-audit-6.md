# psig-audit-6 — independent signature audit of progress chunk 6

Task: independently audit the translator's (psig-6) Lean signatures for the 32 Rocq declarations of
`type_progress.v` lines 2636-6159 (chunk 6). For each: check binder order, premises, conclusion,
quantifiers vs. Rocq; flag mismatch / undocumented-deviation / suspicious / doc-only.
No Lean was run (per task). No repo file other than this log was written.

## Safety check (START)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-audit-6
safety check [psig-audit-6] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T120853.798872292Z-psig-audit-6-1443285.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Read

- brief `scratchpad/briefs/progress_sig_brief.md`, task `scratchpad/briefs/task_psig_6.md`
- (below) Rocq statements and definitions consulted

## Per-lemma audit

(filled incrementally)

### Sources checked (all read-only, via grep / sed ranges)

- Rocq statements: `scratchpad/progress/progress_rocq_stmts.md` entries [181]-[222]; context and proofs in
  `spectec/test-rocq/theories/type_progress.v` 2620-2870, 6095-6140.
- Rocq library: `wasm.v` 20-26 (`list_zipWith` = map over mathcomp `zip`, which truncates), 55-64
  (`list_slice` = drop i then take j), 135-200 (`binN_scope`: `+` = N.add, `<=` = N.le (Prop),
  `>?` = N_gtb; coercions `Z.to_N : Z >-> N`, `Z.of_N : N >-> Z`), 279/309/310 (`:>` = `coerce`,
  `|x|` = `N.of_nat (size x)`, `!(x)` = `the x`), 529 (`proj_uN_0` is the `uN -> N` coercion),
  385-416 (`concat_`, `setproduct*_` take `X : eqType`), generated relation signatures of
  `fun_halfop`/`fun_zeroop` (`option (option _)` outputs) and `fun_lcvtop__` (`option (seq lane_)` output).
- `axioms.v`: `lanes_len` (43), `trunc_sat_total`/`demote_nonempty`/`promote_nonempty` (95-99).
- Lean: `TypeProgress.lean` 100-155 (`jlane`, `flane`, `evens`, `odds`, `vcvtop_trunc_sat_i16`,
  `halfop_of`, `zeroop_of` - all match the Rocq definitions clause by clause); `wasm2.0.lean`:
  `Forall`/`Forall₂` (17-21, zip-based), `concat_`/`setproduct*_` (90-118, `X : Type`, same clauses),
  `uN`/`iN`/`vN`/`vec_`/`u32`/idx abbrevs, `dim`, `shape`, `lane_`, `sz`, `half`, `zero`,
  `vcvtop__*`, `memarg`, `vloadop_`, `wf_vloadop_`, `wf_vcvtop__*`, `wf_instr` VCVTOP case (2104-2108),
  `packnum_`, `fun_zero`, `fzero`(+`fzero_is_wf`), `lanes_`/`inv_lanes_` (OPAQUE, 4644/4659),
  `fun_zeroop`/`fun_halfop`/`fun_lcvtop__`/`fun_vcvtop__` signatures, `Step_pure.vcvtop` (13990),
  `Step_read.vload_shape_oob`/`vload_shape_val` (14575-14590), `fun_mem`, `meminst`, `state`, `config`,
  constructor argument orders of `instr`/`admininstr` `CONST`, `CALL_INDIRECT`, `VCONST`, `VCVTOP`, `VLOAD`.
- `HelperLemmas.lean`: `import Mathlib.Tactic` (so `Odd` is Mathlib's; no project `Odd`), Lean axioms
  `lanes_len` (785), `trunc_sat_total`/`demote_nonempty`/`promote_nonempty` (849-856).
- Name-clash grep for all 32 names over the project `.lean` files: no existing declaration.

### Per-lemma verdicts

| # | Rocq (line) | Verdict | Notes |
|---|---|---|---|
| 1 | evens_odds_ind (2636) | OK | binders `T P`, 3 premises, `∀ l, P l` identical. |
| 2 | evens_odds_concat (2645) | OK | `~~ odd (size l)` ≡ `¬ Odd l.length`; `T : eqType`→`Type` mirrors the generated Lean `concat_ (X : Type)` (doc comment says so); `[:: a; b]`→`[a, b]`. |
| 3 | evens_odds_size (2652) | OK | |
| 4 | Forall_evens (2658) | OK | Lean `evens` = Rocq `evens` (same clauses). |
| 5 | Forall_odds (2664) | OK | |
| 6 | Forall2_of_Forall (2670) | OK | length is already premise 4, so zip-based `Forall₂` conclusion + premise ≡ inductive `Forall2`. |
| 7 | list_slice_size_eq (2679) | OK | verified `list_slice l i j` = `take j (drop i l)` from `wasm.v:57`; `i j : N`→`Nat`. |
| 8 | zip_lane_wf2 (2687) | OK | all 5 premises in order; conclusion verbatim with `!(·)`→`Option.get!`; length premise present. |
| 9 | zip_wf (2701) | OK | both zipWiths truncate; no length needed. |
| 10 | size_zipWith_eq (2710) | OK | |
| 11 | shape_lanes_even (2715) | OK | `lanes_` is opaque in Lean, but Lean has axiom `lanes_len` (same as Rocq's, which the Rocq proof uses) so it is provable, not vacuous. |
| 12 | add_sub_parens (2727) | OK | independently re-derived the elaboration: `n3 : Z` (from `(n3 <= n2)%Z`), `n1 : N`, LHS `N.add n1 (Z.to_N (Z.of_N n2 - n3))`, RHS `Z.sub (Z.of_N (n1+n2)) n3 : Z` coerced by `Z.to_N` because `@eq` takes its type from the LHS (`N`). Lean `Int.toNat` = `Z.to_N`. True statement (also for negative `n3`). |
| 13 | call_indirect_progress (2734) | OK | binder types `store frame num_ tableidx typeidx` as inferred; `!=`→`≠`; `[a] ++ [b]` kept. |
| 14 | vcvtop_lane_total (2817) | OK | `~~ b`→`b = false` (equivalent). Provable in Lean: needed axioms `trunc_sat_total`/`demote_nonempty`/`promote_nonempty` are ported. |
| 15 | vcvtop_lanes_total (2849) | OK (documented DEVIATION) | added conjunct `vs.length = L.length` after the `Forall₂` conjunct is forced (literal zip-based form holds with `vs = []`) and exactly restores Rocq's meaning; doc comment has a **Deviation:** note. Also matches what Lean's `fun_vcvtop__` rules need (they carry explicit `List.length var_lst = List.length c_1_lst` premises). |
| 16 | setproduct2_Forall (2871) | OK | `X : eqType`→`Type` (mirrors generated `setproduct2_ (X : Type)`), documented. |
| 17 | setproduct1_Forall (2875) | OK | same. |
| 18 | setproduct_Forall (2882) | OK | same. |
| 19 | setproduct_nonempty (2889) | OK | same; `!= [::]`→`≠ []`. |
| 20 | setproduct_pick (2897) | OK | `(|l| >? 0)%BN` = `N_gtb (N.of_nat (size l)) 0` ≡ `l.length > 0`; `c \in l` ≡ `c ∈ l` (uN eqType is Leibniz). `c : vec_` = codomain of `inv_lanes_`. Note (no action): Lean's `fun_vcvtop__` premise uses `List.contains (Map ..) v128`, so proofs need `List.contains_iff`/`elem_iff` (uN derives `LawfulBEq`). |
| 21 | halfop_total (2943) | OK | Lean `fun_halfop : … → Option (Option half) → Prop` same as Rocq. |
| 22 | zeroop_total (2951) | OK | same for `fun_zeroop`. |
| 23 | zero_lane_wf (2959) | OK | `packnum_ : lanetype → num_ → Option lane_`, `fun_zero : numtype → num_` (defs, not opaque); `fzero_is_wf` exists. |
| 24 | vcvtop_step_full (2969) | OK | binder order `L1 L2 M op c1`; `c1 : uN` (first use `wf_uN 128 c1`; `vec_` = `vN` = `iN` = `uN` abbrevs); 7 premises in order; `VCVTOP` arg order (dest, src) matches Rocq and `Step_pure.vcvtop`. Non-vacuous (CONVERT/TRUNC_SAT without half/zero). |
| 25 | vcvtop_step_half (2991) | OK | `h : half`. |
| 26 | vcvtop_step_zero (3012) | OK | `Some ZERO`→`some zero.ZERO`. Non-vacuous (F64→I32 TRUNC_SAT ZERO, DEMOTE ZERO). |
| 27 | vcvtop_zero_numtype (3064) | OK | `z : zero`. |
| 28 | vcvtop_full_lsize (3076) | OK | |
| 29 | vload_shape64_wf (6103) | OK | Lean `wf_vloadop_` case_0 premise `((64*1 : Rat)) = 128/2` true. |
| 30 | vload_shape64_stuck (6107) | OK | `(i :> N)` = `proj_uN_0 i` (instance `proj_uN_0_coercion`), `(OFFSET ao :> N)` = `proj_uN_0 ao.OFFSET`, `|BYTES ..|` = `.BYTES.length`, `%BN <=` = `N.le`; grouping `(i + off) + 8` preserved. True in Lean: `vload_shape_val` needs `jsize Jnn = 64*2 = 128` (no such Jnn) and `vload_shape_oob` needs `> length`. |
| 31 | vcvtop_trunc_sat_i16_wf_instr (6124) | OK | `instr.VCVTOP` (Rocq `VCVTOP` = instr ctor); Lean `wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2` allows `sizenn F32 = 2 * lsizenn I16` with `some ZERO`. |
| 32 | vcvtop_trunc_sat_i16_stuck (6132) | OK | Lean `fun_lcvtop__` TRUNC_SAT cases exist only for I32/I64 destinations (wasm2.0.lean 9463-9478), so true in Lean (zero case needs ≥1 lane, given by axiom `lanes_len`). |

Doc comments: all 32 cite the correct `type_progress.v` line, and the one-line descriptions are accurate
(checked against the Rocq comments at 6095-6123 for the counterexample lemmas).

Coverage: the 32 names of `task_psig_6.md` all present, in Rocq order, one `-- @@` marker each.
Declarations in the range that are not in this chunk (defs `vcvtop_trunc_sat_i16`/`halfop_of`/`zeroop_of`,
Ltacs `vcvtop_cases`/`vcvtop_cases_full`, `t_progress_be`, `Instr_ok_Instrs_ok`, `Instr_ok2_ind'`,
`t_progress_e`, `t_progress`) are handled elsewhere (already in TypeProgress.lean or other chunks).
Translator log `psig-6.md` reports 0 Lean errors (not re-run here, per task).

### Result

32/32 signatures state the same thing as Rocq. One documented, forced deviation (`vcvtop_lanes_total`
length conjunct) is correct and necessary. No mismatches, no undocumented deviations, nothing suspicious.

## Safety check (END)

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-audit-6
safety check [psig-audit-6] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T121726.747454260Z-psig-audit-6-1445526.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written by this agent: only this log (plus the empty scratch dir
`scratchpad/agents/psig-audit-6/`). No Lean was run; no repo file was edited.

# psig-audit-4: independent signature audit of progress chunk 4

## Task
Audit the translator's (psig-4) Lean signatures for the 32 Rocq declarations of
`spectec/test-rocq/theories/type_progress.v` lines 1761-2212 (binop_not_none ... zip_lane_wf).
For each one, check that binder order, premises, conclusion and quantifiers match Rocq, or that a
NOT PORTED note is justified. Flag mismatch / undocumented-deviation / suspicious / doc-only.
I do not run Lean, and I do not edit any repo file except this log.

## Safety check (START)
Command (from /home/zhengyew/spectec):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-audit-4`

```
safety check [psig-audit-4] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T120132.350017997Z-psig-audit-4-1440924.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## What I read
- Brief: scratchpad/briefs/progress_sig_brief.md; task: scratchpad/briefs/task_psig_4.md
- Rocq statements: scratchpad/progress/progress_rocq_stmts.md entries [110]-[144]
- All 32 doc-comment line numbers checked against the extracted statements. They all match
  (1761, 1774, 1787, 1800, 1824, 1836, 1854, 1858, 1865, 1874, 1884, 1897, 1905, 1916, 1927, 1938,
  1953, 1968, 2004, 2032, 2059, 2092, 2103, 2119, 2135, 2149, 2170, 2179, 2187, 2190, 2193, 2200).

## Definition checks (wasm2.0.lean / project files / Rocq wasm.v)
(filled in below as I go)
Types and arity, Lean (wasm2.0.lean) vs Rocq (wasm.v). All of them match:
- `Forall` (17) = `∀ x ∈ l, P x`. `Forall₂` (20) is ZIP-BASED: `∀ t ∈ l.zip l', P t.1 t.2`, so it
  carries no length fact. `N := Nat` (44). `iN := uN` (200), `vec_ := vN := iN` (964, 411).
- `fun_binop_ : numtype → binop_ → num_ → num_ → Option (List num_) → Prop` (3411) = wasm.v:4880.
  Catch-all `fun_binop__case_38` (3556) is `¬ before → … none`.
- `fun_relop_ … → Option num_ → Prop` (3814) = wasm.v:5285. The before-predicate (3786) has 24
  premise-free constructors.
- `fun_cvtop__ … → Option (List num_) → Prop` (4038) = wasm.v:5494. Before-predicate at 3966.
- `fun_testop_` is a def returning `Option num_` (3574) = wasm.v:5046 (a Definition).
- `fun_vunop_ : shape → vunop_ → vec_ → Option (List vec_) → Prop` (5636) = wasm.v:7106. The
  before-predicate `…_case_26` is at 5396, and the catch-all case_26 at 5873.
- `fun_iabs_ : N → iN → iN → Prop` (4400). `fun_imin_/imax_/iadd_sat_/isub_sat_ : N → sx → iN → iN → iN → Prop`
  (4424/4458/4492/4514) = wasm.v:5836/5855/5907 (`res_N = N`, wasm.v:342). They are built from
  `fun_signed_` and `fun_inv_signed_` (2659/2669), which are inductives and total on in-range input.
  `sat_s_` (2693) is a real def and matches wasm.v:4226. None of these are opaque.
- `wf_num_/wf_binop_/wf_testop_/wf_relop_/wf_cvtop__/wf_vunop_`: the argument orders are the same
  as in Rocq. `wf_vunop_` ties the shape to (J, M) in both.
- `lane_`, `wf_lane_`, `proj_lane__0 : lane_ → Option iN`, `proj_lane__1 : lane_ → Option fN`
  (934-962) = wasm.v:1597-1615.
- `lanes_` is `opaque` in Lean (4644), and in Rocq it is also an `Axiom` (wasm.v:6117). The Lean
  trust base is the same as Rocq's: the generated `lanes__is_wf` (4651, sorry; Rocq uses the same
  lemma at type_progress.v:2174) and the axiom `lanes_len` (HelperLemmas.lean:785 = axioms.v:43).
  So `lanes_Jnn_form`, `lanes_Fnn_form` and `lanes_size_eq` can be proved in Lean, and they are
  not suspicious.
- Rocq `!( x )` := `the x` (wasm.v:310) maps to `Option.get!`. Under every premise in this chunk
  the argument is `some _`, so the default value never matters.
- `jlane`/`flane` (TypeProgress.lean:112/116) match Rocq 2165/2167.
- Name clashes: I grepped all 32 names as theorem/def/axiom/abbrev in every project .lean file. None
  exists outside the chunk.
- type_progress.v has no Section, Variable or Hypothesis, so there are no hidden binders.

## Per-declaration verdicts
| # | Rocq (line) | Verdict | Notes |
|---|---|---|---|
| 1 | binop_not_none (1761) | OK | binders, the 4 premises and `lst ≠ none` all match |
| 2 | relop_before (1774) | OK | |
| 3 | relop_not_none (1787) | OK | `c : Option num_` matches the type of `fun_relop_` |
| 4 | cvtop_before (1800) | OK | |
| 5 | cvtop_not_none (1824) | OK | |
| 6 | testop_not_none (1836) | OK | a function, `≠ none` |
| 7 | Forall_all (1854) | OK | `is_true` becomes `= true`, and mathcomp `all P l` becomes `l.all P` (argument order is right) |
| 8 | all_Forall (1858) | OK | |
| 9 | Forall_exists_Forall2 (1865) | OK (documented deviation, justified) | `Forall₂ ∧ length` is exactly equivalent to inductive Forall2, and the literal version would be trivial with `la = []`. Style note: the translator's coverage note says this "matches the Vals_ok / from_mathlib_forall₂ precedent", but those put the length FIRST (TypingLemmas.lean:1776, HelperLemmas.lean:889). That is cosmetic only, and the Lean doc comment does not make the claim. |
| 10 | Forall2_size_eq (1874) | SUSPICIOUS (vacuous) | With the added `hlen` the conclusion is literally a premise (a tautology). Project precedent HelperLemmas.lean:293 marks the identical Rocq lemma `Forall2_seq_size` (helper_lemmas.v:159, `Forall2 R l l' -> \|l\| = \|l'\|`) NOT PORTED for exactly this reason. Recommend NOT PORTED. |
| 11 | wf_lane_Jnn_inv (1884) | OK | the bool `!= None` premise becomes `≠ none` |
| 12 | wf_lane_Jnn_some (1897) | OK | |
| 13 | wf_lane_Fnn_inv (1905) | OK | |
| 14 | Forall_lane_Jnn (1916) | OK | |
| 15 | Forall_lane_map_wf (1927) | OK | |
| 16 | Forall_lane_fop_wf (1938) | OK | `fop : N → fN → List fN` matches `res_N -> fN -> seq fN` |
| 17 | iabs_lane_total (1953) | OK | |
| 18 | Forall_iabs_total (1968) | OK (documented deviation, justified) | The length conjunct is needed by the `(List.length var_0_lst) = (List.length lane_1_lst)` premises of the generated iabs cases. I confirmed these in the before-predicate constructor at wasm2.0.lean:5621ff and in `fun_vunop__case_0` at 5637ff. |
| 19 | vunop_real (2004) | OK | the premise `∀ J M, sh = … → (lanes_ sh val).all (· != none) = true` is faithful, and so is the conclusion conjunction |
| 20 | vunop_total (2032) | OK | |
| 21 | vunop_not_none (2059) | OK | |
| 22 | sat_s_range (2092) | OK | Rocq `(2%num ^ (v_N-1)%BN)%BN` is `N.pow 2 (N.sub v_N 1)` (binN_scope, wasm.v:141-145) cast to Z. Lean computes `((2^(v_N-1) : Nat) : Int)`, which is the same value and equals the bound used inside `sat_s_` (`Int.toNat (v_N - 1)`). |
| 23 | imin_total_wf (2103) | OK | |
| 24 | imax_total_wf (2119) | OK | |
| 25 | iadd_sat_total_wf (2135) | OK | |
| 26 | isub_sat_total_wf (2149) | OK | |
| 27 | lanes_Jnn_form (2170) | OK | provable via `lanes__is_wf`, as in Rocq |
| 28 | lanes_Fnn_form (2179) | OK | |
| 29 | jlane_some (2187) | OK | `Forall (fun l => proj_lane__0 l ≠ none)`. This is the exact form of the generated `fun_vunop_` premises. |
| 30 | flane_some (2190) | OK | |
| 31 | lanes_size_eq (2193) | OK | via `lanes_len` (HelperLemmas.lean:785) |
| 32 | zip_lane_wf (2200) | OK | The translator was right not to add `hlen`: the length is already a Rocq premise, so the zip-based conclusion is equivalent to Rocq's. |

The doc comment references are correct as well: the uses at 1982/3941 and 1973/2861/3937, case
numbers 38/24/36/26, wasm.v:342 and HelperLemmas.lean:785 all point where they say.
Minor optional note: `Forall_all`/`all_Forall` amount to `List.all_eq_true` once `Forall` is
unfolded. Keeping them is fine, because `Forall` is the generated def and the bool premise of
`vunop_real` needs this bridge.

## Result
31 OK and 1 flagged (Forall2_size_eq: suspicious, vacuous; recommend NOT PORTED per the
HelperLemmas.lean:293 precedent). No mismatches and no undocumented deviations.

## Safety check (END)
Command (from /home/zhengyew/spectec):
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-audit-4`

```
safety check [psig-audit-4] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T120825.043777929Z-psig-audit-4-1443107.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```
Files written: this log only. Scratch dir created (left empty):
/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-audit-4/
I did not run Lean and did not edit any repo file.

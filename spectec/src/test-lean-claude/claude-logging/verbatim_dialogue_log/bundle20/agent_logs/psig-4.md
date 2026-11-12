# psig-4 log (bundle20 progress port: signature translation, chunk 4 of 6)

## Task

Translate 32 Rocq declarations of `spectec/test-rocq/theories/type_progress.v` (lines 1761-2212) into
Lean 4 signatures (bodies `sorry`), in Rocq order:
binop_not_none, relop_before, relop_not_none, cvtop_before, cvtop_not_none, testop_not_none, Forall_all,
all_Forall, Forall_exists_Forall2, Forall2_size_eq, wf_lane_Jnn_inv, wf_lane_Jnn_some, wf_lane_Fnn_inv,
Forall_lane_Jnn, Forall_lane_map_wf, Forall_lane_fop_wf, iabs_lane_total, Forall_iabs_total, vunop_real,
vunop_total, vunop_not_none, sat_s_range, imin_total_wf, imax_total_wf, iadd_sat_total_wf,
isub_sat_total_wf, lanes_Jnn_form, lanes_Fnn_form, jlane_some, flane_some, lanes_size_eq, zip_lane_wf.

Brief: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/progress_sig_brief.md`
Task file: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/briefs/task_psig_4.md`
Scratch: `/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-4/Chunk.lean`

## Safety check (START), verbatim

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-4
safety check [psig-4] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T113312.723146652Z-psig-4-1429037.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Reading

(filled in incrementally below)

- Brief + task file read fully.
- `TypeProgress.lean` 1-200 (defs `is_const`..`zeroop_of`, `jlane`/`flane` at Rocq 2165/2167 are
  already defined there; motives); style of sibling chunk psig-3 (`binop_before` etc.: explicit
  binders before the colon, premises as arrows).
- Statements: `scratchpad/progress/progress_rocq_stmts.md` entries [110]-[144]; original Rocq
  source `type_progress.v` 1740-2215 (comments + proofs, for context). All 32 Rocq line numbers
  re-verified with `grep -n "^Lemma <name>"`. Entries in that range NOT in my list (and therefore
  not emitted): Ltac `vunop_case` (1980), Definitions `jlane` (2165) / `flane` (2167) (already in
  TypeProgress.lean).
- `wasm2.0.lean`: `Forall`/`Forall₂` (17/20; take `Type` args; `Forall₂` zip-based), `N := Nat` (44),
  `uN`/`wf_uN` (166/176), `iN := uN` (200), `fN`/`wf_fN` (277/283), `lanetype`/`lanetype_Fnn`/
  `lanetype_Jnn` (627/637/680), `dim` (775), `lsize` (808), `shape.X`/`wf_shape` (818/823),
  `sizenn`/`lsizenn` (853/865), `lane_`/`wf_lane_`/`proj_lane__0`/`proj_lane__1` (934-958),
  `vec_ := vN := iN` (964/411), `sat_s_` (2693), `fabs_ (v_N : N) ...` (2721: Rocq `res_N` is `N`),
  `fun_binop__before_..._case_38` (3263), `fun_binop_` (3411), `fun_testop_` (3574, a `def` returning
  `Option num_`), `fun_relop__before_..._case_24`/`fun_relop_` (3786/3814),
  `fun_cvtop___before_..._case_36`/`fun_cvtop__` (3966/4038), `fun_iabs_`/`fun_imin_`/`fun_imax_`/
  `fun_iadd_sat_`/`fun_isub_sat_` (4400-4514), `lanes_` (4644, `opaque`),
  `fun_vunop__before_..._case_26`/`fun_vunop_` (5396/5636).
  Observation: the generated `fun_vunop_` iabs cases carry `Forall₂ ... var_0_lst lane_1_lst` AND a
  separate `(List.length var_0_lst) = (List.length lane_1_lst)` premise (e.g. wasm2.0.lean:5622-5626).
- Rocq `wasm.v:141` `binN_scope` (`%BN`): `-`/`^` are `N.sub`/`N.pow`; `wasm.v:342` `res_N := N`.
- Lean has `lanes_len` (HelperLemmas.lean:785, axiom), so `lanes_size_eq` stays provable.
- Precedent for Rocq `Forall2` in a conclusion/definition: `Vals_ok` (TypingLemmas.lean:1776) and
  `from_mathlib_forall₂` (HelperLemmas.lean:889) pair the zip-based `Forall₂` with a length equality.
- Downstream Rocq uses of `Forall2_size_eq` (1982 in Ltac `vunop_case`, 3941) extract the size
  equality from the `Forall2` produced by `Forall_iabs_total` / `Forall_exists_Forall2`, so in Lean
  those conclusions must carry the length fact explicitly.
- Name-clash check: none of the 32 names is declared in any project `.lean` file
  (`grep "\b(theorem|lemma|def|abbrev|axiom|opaque) <name>\b" *.lean`).

## Translation conventions used

- Explicit binders before the colon, premises as arrows (psig-3 style). Rocq's implicitly typed
  binders get the types Rocq infers (`nt : numtype`, `b : binop_`, `n1 n2 : num_`,
  `lst : Option (List num_)`, `v_sx : sx`, `i1 i2 : iN`, ...). The vector argument `val` of the
  `vunop_*` lemmas is typed `vec_` (Rocq infers `uN` from `wf_uN 128 val`; `vec_ := vN := iN := uN`
  are reducible abbrevs, so this is the same statement).
- `lst <> None` ↦ `lst ≠ none`; boolean `x != None` in Prop position ↦ `x ≠ none` (same form as the
  generated `fun_vunop_` premises); boolean `!=` inside a `bool` predicate (`all (fun l => ... != None)`)
  ↦ `!=` (`bne`), with the outer `is_true` ↦ `= true`.
- mathcomp `all P l` ↦ `l.all P` (`List.all`); `size l` / `(|l|)` ↦ `l.length`; `!(x)` ↦ `Option.get! x`;
  `res_N` ↦ `N`; `X lt (mk_dim M)` ↦ `shape.X lt (dim.mk_dim M)`; `mk_lane__0/1` ↦ `lane_.mk_lane__0/1`.
- `sat_s_range`: Rocq `((2%num ^ (v_N - 1)%BN)%BN : Z)` (N power, truncated N subtraction, cast to Z)
  ↦ `((2 ^ (v_N - 1) : Nat) : Int)`; `(0 - _)%Z` kept as `(0 : Int) - _` (not `-_`). `#check`
  confirmed it elaborates to `(0:ℤ) - ↑((2:ℕ) ^ (v_N - (1:N))) ≤ sat_s_ v_N z ∧ ...`.

## Per-declaration decisions

| Rocq (line) | Lean | Decision |
|---|---|---|
| binop_not_none (1761) | `binop_not_none` | OK |
| relop_before (1774) | `relop_before` | OK |
| relop_not_none (1787) | `relop_not_none` | OK |
| cvtop_before (1800) | `cvtop_before` | OK |
| cvtop_not_none (1824) | `cvtop_not_none` | OK |
| testop_not_none (1836) | `testop_not_none` | OK (`fun_testop_` is a `def` returning `Option num_` on both sides) |
| Forall_all (1854) | `Forall_all` | OK |
| all_Forall (1858) | `all_Forall` | OK |
| Forall_exists_Forall2 (1865) | `Forall_exists_Forall2` | DEVIATION: conclusion `Forall2 R la l` ↦ `(Forall₂ R la l ∧ la.length = l.length)`. Without it the zip-based conclusion is trivially true with `la = []` (strictly weaker than Rocq); Rocq callers (1982, 3941) extract exactly this length fact. |
| Forall2_size_eq (1874) | `Forall2_size_eq` | DEVIATION (hlen rule): + `la.length = lb.length →` right after the `Forall₂` premise; literal statement is false in Lean (`la = []`, `lb = [b]`). With it the statement is a tautology (`fun _ h => h`). Kept for 1-1 correspondence; main thread may prefer NOT PORTED. |
| wf_lane_Jnn_inv (1884) | `wf_lane_Jnn_inv` | OK |
| wf_lane_Jnn_some (1897) | `wf_lane_Jnn_some` | OK |
| wf_lane_Fnn_inv (1905) | `wf_lane_Fnn_inv` | OK |
| Forall_lane_Jnn (1916) | `Forall_lane_Jnn` | OK |
| Forall_lane_map_wf (1927) | `Forall_lane_map_wf` | OK |
| Forall_lane_fop_wf (1938) | `Forall_lane_fop_wf` | OK (`res_N` ↦ `N`) |
| iabs_lane_total (1953) | `iabs_lane_total` | OK |
| Forall_iabs_total (1968) | `Forall_iabs_total` | DEVIATION: conclusion `Forall2 R vs ls` ↦ `(Forall₂ R vs ls ∧ vs.length = ls.length)` (same reason; the generated `fun_vunop_` iabs cases need the separate length premise). |
| vunop_real (2004) | `vunop_real` | OK |
| vunop_total (2032) | `vunop_total` | OK |
| vunop_not_none (2059) | `vunop_not_none` | OK |
| sat_s_range (2092) | `sat_s_range` | OK |
| imin_total_wf (2103) | `imin_total_wf` | OK |
| imax_total_wf (2119) | `imax_total_wf` | OK |
| iadd_sat_total_wf (2135) | `iadd_sat_total_wf` | OK |
| isub_sat_total_wf (2149) | `isub_sat_total_wf` | OK |
| lanes_Jnn_form (2170) | `lanes_Jnn_form` | OK (uses `TLC.jlane`) |
| lanes_Fnn_form (2179) | `lanes_Fnn_form` | OK (uses `TLC.flane`) |
| jlane_some (2187) | `jlane_some` | OK |
| flane_some (2190) | `flane_some` | OK |
| lanes_size_eq (2193) | `lanes_size_eq` | OK (Lean `lanes_` is `opaque`; provable from axiom `lanes_len`, HelperLemmas.lean:785) |
| zip_lane_wf (2200) | `zip_lane_wf` | OK. No hlen: Rocq's `Forall2` conclusion adds only `size L1 = size L2`, already a premise, so the zip-based conclusion is equivalent. |

No NOT PORTED entries; no name clashes (Lean would have reported "already declared").

## Lean check

`cd /home/zhengyew/spectec/spectec/src/test-lean-claude && timeout 900 lake env lean <scratch>/psig-4/Chunk.lean`
(first attempt compiled; 1 run + 1 `#check` verification run on a scratch copy, since deleted)

exit=0, 32 output lines, all `declaration uses `sorry``, no errors. Last lines:
```
.../scratchpad/agents/psig-4/Chunk.lean:249:8: warning: declaration uses `sorry`
.../scratchpad/agents/psig-4/Chunk.lean:256:8: warning: declaration uses `sorry`
.../scratchpad/agents/psig-4/Chunk.lean:266:8: warning: declaration uses `sorry`
```
Merge markers: 32 `-- @@` lines, verified identical (in order) to the task list.

## Safety check (END), verbatim

```
$ cd /home/zhengyew/spectec && bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh "" psig-4
safety check [psig-4] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T114201.007384817Z-psig-4-1435710.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Files written: this log (inside the target dir) and `Chunk.lean` / `check1.txt` in my scratch dir
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/psig-4/`.
No repo file edited, no state-changing git command, no agents spawned.

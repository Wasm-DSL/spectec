# Upstream re-sync (`6582b3a39`) and the last `sorry`s (bundle21)

Written for: you (the user), and the next session.
Date: 2026-10-15. Upstream: `rocq-backend-proof` `6582b3a39` ("Proof is complete!") on top of spec
commit `4cf9f29c5` ("CR changes"), merged into this branch as `39aca4a5b`.

## 0. Bottom line

- **The blocking issues that kept `sorry`s in the port are solved upstream.** Both stuck vector
  instructions are now invalid, and the bulk-memory `2^32` corner case is gone. Rocq's
  `Step_read_is_wf` and `t_progress_be` are now `Qed`.
- **The hand-written port now has no `sorry` except the 16 you marked for deletion.**
  `Step_read_is_wf` is now proved in `wasm2.0.lean`, as in Rocq, and `TypeProgress.lean`'s two `sorry`s are gone.
- **What cannot be done:** 62 `sorry`s remain in the generated `wasm2.0.lean`. Each states that
  an *uninterpreted* builtin (`iand_`, `fadd_`, `lanes_`, `nbytes_`, ...) returns a well-formed
  value. These functions are `opaque` in Lean and `Axiom`s in Rocq, so nothing about their values
  can be proved; Rocq leaves exactly the same 62 `Admitted`. Removing them needs real definitions
  for those builtins (as you did for `rat_to_nat`), which is a generator/spec decision, or accepting
  them as the trusted base, as Rocq does.
- **Not landed yet:** the auto-mode permission classifier refused overwriting the repo's `.lean`
  files (your regenerated `wasm2.0.lean` is uncommitted). Everything was done and checked in a
  scratch copy of the project and is ready as one self-tested patch; §6 says how to apply it.

## 1. The blocking issues from bundle20, checked against the new upstream

| Issue (bundle20) | Status now | Evidence |
|---|---|---|
| `VLOAD (SHAPE 64 X 1)` well formed but stuck | **fixed** | `vloadop_` `SHAPE` now needs `M > 1` (`wf_vloadop_` in the regenerated model); Rocq refutes the case with it |
| `VCVTOP F32→I16 TRUNC_SAT … ZERO` well formed but stuck | **fixed** | `TRUNC_SAT` now needs an `Inn` destination (`vcvtop__Fnn_1_M_1_Inn_2_M_2`); the case no longer exists |
| `Step_read_is_wf` false (memory.fill/copy/init push `CONST I32 2^32`) | **fixed** | the three `succ` rules push `$iadd_(32, i, 1)`, which wraps; `iadd_` is a real `def`; Rocq's `Step_read_is_wf` is `Qed` |
| (B) `Moduleinst_ok`'s hoisted `\|addrs\| > 0` (no `$invoke` config is `Config_ok`) | **still open** | premise still generated; the bundle20 witness's `invoke_config_not_ok` still checks |
| (C) `Globaltype_ok` admits only mutable globals | **still open** | single `some MUT` constructor; `s_imm_not_ok` still checks |
| `vstore_lane-oob` adds `N` bits where it means `N/8` bytes | still open | unchanged; it affects neither theorem |

B and C narrow what preservation and progress talk about but block no `sorry`; they need a SpecTec
fix (`middlend/sideconditions.ml` for B; `Globaltype_ok`'s `MUT?` rendering for C).

Other upstream changes absorbed: `$ishl_`/`$ishr_` take an `iN(N)` shift amount and `$vshiftop_`
reduces it modulo the lane size (Rocq deleted its `ishl_wf`/`ishr_wf` axioms accordingly).

## 2. What changed in the Lean port

All changes mirror upstream. Declaration-level audit against the repo's current files: removed 2
axioms + 5 `TypeProgress` declarations (exactly Rocq's removals), re-stated 9 lemmas (exactly
Rocq's), no other statement changed anywhere. Your readability rewrites (`t_preservation`,
`t_progress`, `t_progress_e`, `br_reduce` & co.) are untouched.

- **`wasm2.0.lean`** (your regeneration, which I verified is byte-identical to what the current
  `main.exe … --lean` produces):
  - the bundle19 hand-edits patch re-applied (no rejected hunk; 3 hunks needed fuzz because
    source-location comments moved);
  - `vshiftop__is_wf` adjusted to the modulo shift amount;
  - **`Step_read_is_wf` proved** (126 lines of helper lemmas in a new hand-written block plus a 214-line proof over the 47 `Step_read` rules, ported from Rocq's proof; it uses only three opaque-builtin facts that Rocq's proof also uses: `extend___is_wf`, `inv_lanes__is_wf`, `lanes__is_wf`);
  - a new hand-edits patch for the next regeneration:
    `bundle21/user_requested_documents/wasm2.0_hand_edits.patch` (+ README).
- **`HelperLemmas.lean`**: `ishl_wf`/`ishr_wf` deleted, as upstream.
- **`TypeProgress.lean`**:
  - `vcvtop_trunc_sat_i16` and its premise on 9 lemmas deleted;
  - the 4 counterexample lemmas deleted (the two `*_wf*` ones would now be false);
  - `binop_total`/`binop_before` use the generated `ishl__is_wf`/`ishr__is_wf`;
  - `t_progress_be_vshiftop` uses the modulo shift amount;
  - `t_progress_be_vload_pack`: `SHAPE 64 X 1` refuted with `M > 1` (was `sorry`);
  - `t_progress_be_vcvtop`: the I16 `TRUNC_SAT` case split is gone (was `sorry`).
- **Doc comments** updated where they called `Step_read_is_wf` `Admitted`/false or described the
  stuck cases (`TypePreservation.lean`, `TypeProgress.lean`, the `HelperLemmas` axiom header).

## 3. `sorry` inventory

| Where | bundle20 | now |
|---|---|---|
| `TypeProgress.lean` | 2 (the stuck cases) | **0** |
| `TypePreservation*`, `TypingLemmas`, `Subtyping`, `ExtensionLemmas` (live code) | 0 | 0 |
| marked `TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED` | 16 | 16 (untouched, as you asked in bundle20; most are false under the zip-based `Forall₂`, so deleting them is the way to zero) |
| `wasm2.0.lean` | 63 (62 opaque-builtin `*_is_wf` + `Step_read_is_wf`) | 62 (the opaque-builtin `*_is_wf`; exactly Rocq's `Admitted` set minus `res_list_eq_dec`) |

## 4. What the main theorems rest on now

| Theorem | axioms (`#print axioms`) | `sorry` dependencies (`#sorry_deps`) |
|---|---|---|
| `t_preservation` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`; **no project axiom** | **32**, all generated `*_is_wf` of opaque builtins (was 33: `Step_read_is_wf` is gone) |
| `t_progress` | the standard ones + **15** project axioms, each mirroring Rocq's `axioms.v` (was 17: `ishl_wf`/`ishr_wf` deleted, as upstream) | **56**, all generated `*_is_wf` of opaque builtins (was 59: the two stuck subcases and `Step_read_is_wf` are gone) |

Every remaining `sorry` dependency is `Admitted` in Rocq as well.

## 5. How this was checked

- Regeneration: re-ran the generator into the scratchpad; byte-identical to your `wasm2.0.lean`.
- Full `lake build` of the scratch project: clean, 3006 jobs; `declaration uses sorry` only for the 62 + 16 above.
- Every statement change audited against Rocq `6582b3a39` (script + side-by-side read).
- `#print axioms` / `#sorry_deps` for `t_preservation` and `t_progress` (§4).
- The bundle20 non-vacuity witness re-run against the new model: hypotheses still satisfiable,
  sorry-free.
- The patch was self-tested: applied with `git apply` to copies of the repo files, it reproduces
  the checked scratch files byte for byte.
- Safety: nothing outside `spectec/src/test-lean-claude` changed (checks in §7).

## 6. Landing the changes (needs your OK)

**Update (16:18 local):** you applied the patch at 16:05 and rebuilt; all nine modules were
recompiled at 16:08-16:10, and the repo's Lean files are byte-identical to the checked versions.
`NOTES.md`, `SUMMARY.md` and `is_wf_theorems.md` have been updated accordingly. The rest of this
section describes the situation before that.

- **Before your clarification,** the auto-mode permission classifier refused two attempts to write
  this bundle's `prompt_21.md` ("Logging/Audit Tampering", then "Irreversible Local Destruction").
- **After you said the auto-memory note does not apply,** writing new files under
  `claude-logging/` worked.
- **Still refused, as "Irreversible Local Destruction":**
  - copying the four checked `.lean` files over the repo's;
  - even copying your uncommitted regenerated `wasm2.0.lean` out to the scratchpad as a backup.

  The likely reason is that `wasm2.0.lean` holds uncommitted work of yours that git cannot restore.

So the Lean changes are **not applied**. They are ready as one reviewed patch, self-tested to
reproduce the checked files exactly when applied to the repo's current files:

```sh
cd /home/zhengyew/spectec
git apply --check spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/user_requested_documents/bundle21_lean_changes.patch   # dry run
git apply spectec/src/test-lean-claude/claude-logging/verbatim_dialogue_log/bundle21/user_requested_documents/bundle21_lean_changes.patch           # wasm2.0.lean, HelperLemmas.lean,
                                                        # TypePreservation.lean, TypeProgress.lean
cd spectec/src/test-lean-claude && lake build           # expect: clean, 3006 jobs
```

`git apply -R` undoes it. Your regenerated `wasm2.0.lean` is the patch's pre-image, so undoing it
restores your file exactly. A byte-identical copy is also kept at `/tmp/claude-1002/-home-zhengyew-spectec/74fc8884-a65c-4404-8595-c22db6588f09/scratchpad/ana/wasm_new.lean`.

Alternatively, add a permission rule allowing Claude to edit files under
`spectec/src/test-lean-claude`, and tell me to go ahead; I will then apply the patch, rebuild in the
repo, and update `NOTES.md`/`SUMMARY.md`/`is_wf_theorems.md`. Those three are held back until the
Lean changes are in, so they never describe code that is not there.

## 7. Safety and housekeeping

- Baseline: `claude-logging/safety-checks/check-20261015T044132Z.txt` (written by `check.sh` at the
  start, before the denials). Later checks went to the scratchpad. Every one, including those run
  by the agents, verified zero changes outside `spectec/src/test-lean-claude`.
- One untracked file appeared **inside** the target directory at 04:52Z:
  `.lake/build/lib/lean/wasm2.0.trace.nobuild` (1 KB, a Lake "no-build" trace for your stale
  `wasm2.0.lean`). Nothing in this session ran Lake in the repo. The likely trigger is the IDE's
  Lean server reacting to an agent opening a repo `.lean` file with Claude's file-reading tool
  (bundle20 saw the same effect), though your own editor may have done it. It is harmless; delete
  it or let your next build replace it. Agents now read `.lean` files only with `cat`/`sed`.

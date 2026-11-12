# `*_is_wf` theorem tracking

Per user instruction: track every `*_is_wf` theorem from `wasm2.0.lean`
that this project ends up relying on, with a true/false/unknown
assessment. Unknown (still `sorry` in `wasm2.0.lean`) ones are treated as
true-for-now unless trivial to prove ourselves. A separate, parallel
Claude effort is auditing `*_is_wf` theorems directly — expect
`wasm2.0.lean` to change under us; re-check before trusting.

## Status as of session 1 (Phase 1: skeleton complete, no proofs filled in yet)

(**Superseded** — see the table below; `Step_is_wf` has been used since bundle16.)

**None used yet.** All lemma proofs across `HelperLemmas.lean`,
`Subtyping.lean`, `TypingLemmas.lean`, `TypePreservationPure.lean`,
`ExtensionLemmas.lean`, `TypePreservation.lean` are currently `sorry`
placeholders (Phase 1 only stated signatures, didn't write actual proof
terms). No `*_is_wf` theorem has been invoked in an actual proof term
yet, so there is nothing to track here.

The two axioms ported into `HelperLemmas.lean` (`nbytes_len`, `ibytes_len`)
reference the *opaque definitions* `nbytes_`/`ibytes_`/`wrap__`/`size`
from `wasm2.0.lean`, not their `*_is_wf` companion theorems
(`nbytes__is_wf`, `ibytes__is_wf`, `wrap___is_wf`) — those weren't needed
for stating the axioms themselves.

## Table (append rows here as Phase 2/3 proofs come to depend on `*_is_wf` theorems)

| `*_is_wf` theorem | Used by (our lemma/file) | Status in `wasm2.0.lean` (sorry/proved) | Assessed true/false/unknown | Notes |
|---|---|---|---|---|
| `Step_is_wf` | `TypePreservation.t_preservation` (since bundle16; not logged here at the time — added bundle17) | `sorry` | **likely FALSE as stated** (see bundle17 note below) | Upstream `wasm.v:17702` is hand-edited to take an extra `Store_ok (fun_store z)` premise, and its read case goes through `Step_read_is_wf`, which is `Admitted` upstream with the author's note that 3 cases are not derivable. The Lean statement has no `Store_ok` premise. Rocq's `store_extension_reduce` and `t_preservation_type` also call it. |
| `Step_pure_is_wf` | will be needed by `TypePreservationPure.t_pure_preservation` (Rocq's proof calls it to get `wf_admininstr` of the reduct) | `sorry` | believed TRUE | `Qed` upstream (`wasm.v:15794-15987`). bundle9 recorded an *older* upstream comment calling it provably false; that predates the 2026-09-28 well-formedness rework and is superseded. |
| `Step_read_is_wf` | will be needed by `TypePreservation.t_read_preservation` (Rocq calls it at the top of the proof) | `sorry` | **FALSE in 3 corner cases** (upstream author's analysis) | `Admitted` upstream (`wasm.v:17354-17698`), hand-edited to take `Store_ok (fun_store z)`. Author's note: memory.fill-succ, memory.copy-le, memory.init-succ push `CONST I32 (i + 1)` with `i = 2^32 - 1` allowed by `Memtype_ok` (2^16 pages = 2^32 bytes), and `2^32` is not a u32. This is a spec-level issue, independent of the backend. |

### bundle17 note (2026-10-02)

- The three rows above are the only `*_is_wf` facts the preservation proofs touch.
  Since `Config_ok` itself contains `wf_config`, the `Step_read_is_wf` corner case means
  `t_preservation` is false in that corner case in **both** Rocq and Lean (Rocq's `Qed`
  for `t_preservation` rests on the `Admitted` `Step_read_is_wf`). That is an upstream
  spec issue, separate from the Lean-only `with_mem` issue in
  `verbatim_dialogue_log/bundle17/user_requested_documents/with_mem_slice_update_issue.md`.
- `wasm2.0.lean` is out of bounds for this project; nothing was changed there.

### bundle18 note (2026-10-03)

- `store_extension_reduce` was proved **without** `Step_is_wf` (Rocq uses it). It depends
  only on `nbytes__is_wf`, `ibytes__is_wf`, `vbytes__is_wf`, `wrap___is_wf` (the byte
  sequences written by the four memory-store rules; opaque functions, believed TRUE) and on
  the flagged `TypePreservation.rat_to_nat_natCast` (not an `_is_wf`, but also unprovable:
  `rat_to_nat` is `opaque`).
- `t_pure_preservation` now uses `Step_pure_is_wf` (believed TRUE; `Qed` upstream).
- `t_preservation_type` uses `Step_is_wf` (FALSE in the corner case below).
- `t_read_preservation` (still `sorry`) should use `Step_read_is_wf`, as Rocq does. The
  statement itself is false in the memory.fill/copy/init `CONST I32 2^32` corner case, so
  some false lemma is unavoidable there.

### bundle19 note (2026-10-04) — supersedes the table's status column and step 3 below

- **The user asked for proofs inside `wasm2.0.lean`** of every `sorry` theorem whose Rocq
  counterpart is filled in. So `wasm2.0.lean` is now edited for that purpose, and step 3's
  "not ours to edit" no longer applies.
- **Done:** 89 of the 152 `*_is_wf` theorems are proved, which is all of the ones that are
  `Qed` in Rocq. The 63 still `sorry` are exactly Rocq's `Admitted` list. Hand edits are
  re-appliable via `verbatim_dialogue_log/bundle19/user_requested_documents/wasm2.0_hand_edits.patch`.
- **`Step_is_wf`:** proved. It is now stated with Rocq's hand-edited `Store_ok (fun_store z)`
  premise and moved after `Store_ok`. The bundle17 "likely FALSE" verdict was about the
  premise-less form, and is resolved except through `Step_read_is_wf`.
- **`Step_pure_is_wf`:** proved (TRUE).
- **`Step_read_is_wf`:** `sorry`, with Rocq's `Store_ok` premise added. It is FALSE in the
  memory.fill/copy/init corner case; the user says a spec fix is pending. It is the only
  `sorry` dependency of `t_read_preservation`.
- **New rows, all `sorry`, all `Admitted` in Rocq:** 32 numeric-operation theorems that
  `t_preservation` now reaches through the proved `Step_pure_is_wf` (29) and
  `store_extension_reduce` (4: `nbytes__is_wf`, `ibytes__is_wf`, `vbytes__is_wf`,
  `wrap___is_wf`). The 29 are the `_is_wf` of `convert__`, `demote__`, `extend__`, `fabs_`,
  `fceil_`, `ffloor_`, `fnearest_`, `fneg_`, `fsqrt_`, `ftrunc_`, `iand_`, `iandnot_`,
  `ibitselect_`, `iclz_`, `ictz_`, `inot_`, `inv_lanes_`, `ior_`, `ipopcnt_`, `irev_`,
  `ishl_`, `ishr_`, `ixor_`, `lanes_`, `promote__`, `reinterpret__`, `trunc__`, `trunc_sat__`
  and `wrap__`.
  - **Unprovable:** every one of these functions is `opaque` in `wasm2.0.lean`. The fix
    would be the one used for `rat_to_nat`: generate real definitions.
  - **Not false:** each statement holds for some implementation (return 0, `[]`, `none`,
    or `fN.POS fNmag.INF`, since `wf_fNmag N INF` holds for every `N`), and each mentions a
    different opaque function.
- **Full list:** `#sorry_deps TLC.t_preservation` gives 33 declarations, these 32 plus
  `Step_read_is_wf`.

### bundle20 note (2026-10-05)

- Re-verified: the 63 `sorry` theorems in `wasm2.0.lean` are exactly the 63 `Admitted` theorems
  in `wasm.v` (set comparison by script). `#sorry_deps TLC.t_preservation` is still the same 33.
- The progress port (`TypeProgress.lean`) will additionally use `Step_is_wf` (proved) and, through
  it, `Step_read_is_wf`. Lean's `Step.ctxt_*` congruence rules require `wf_config` of the inner
  configurations, as Rocq's do.
- Isabelle's `step_wf`/`Step_read_is_wf` lack the `Store_ok` premise and are false as stated
  (table.size pushes an unbounded `|REFS|`). This independently confirms the hand-added premise.

### bundle21 note (2026-10-15)

- Upstream `6582b3a39` proves Rocq's `Step_read_is_wf` (`Qed`): spec commit `4cf9f29c5` makes
  memory.fill-succ/memory.copy-le/memory.init-succ push `CONST I32 $iadd_(32, i, 1)`, which removes
  the `2^32` corner case. **Proved in Lean too** (bundle21, `wasm2.0.lean`, with a sixth
  hand-written helper block). Its proof uses `extend___is_wf`, `inv_lanes__is_wf` and
  `lanes__is_wf` (opaque builtins, `Admitted` in Rocq), exactly as Rocq's does.
- `ishl__is_wf`/`ishr__is_wf` changed statement (`$ishl_`/`$ishr_` now take an `iN(N)` shift
  amount). `TypeProgress.binop_total`/`binop_before` now use them in place of the deleted project
  axioms `ishl_wf`/`ishr_wf` (deleted upstream too).
- `vshiftop__is_wf`'s bundle19 proof was adjusted: `$vshiftop_` now passes the shift amount modulo
  the lane size.
- The 63 → **62** `sorry` theorems in `wasm2.0.lean` are now exactly Rocq's 62 `Admitted`
  `*_is_wf` of `Axiom` (Lean: `opaque`) functions; Rocq's only other `Admitted` is
  `res_list_eq_dec`, which Lean derives automatically.
- `#sorry_deps TLC.t_preservation`: 32 (was 33); `#sorry_deps TLC.t_progress`: 56 (was 59). All
  are `*_is_wf` of opaque builtins. They can be removed only by giving those builtins real
  definitions in the generator, as was done for `rat_to_nat`.
- The re-apply patch for regenerations is now
  `verbatim_dialogue_log/bundle21/user_requested_documents/wasm2.0_hand_edits.patch`.

## How to fill this in going forward

When a Phase 2/3 proof needs to invoke some `Foo_is_wf` theorem from
`wasm2.0.lean`:
1. Check whether it's currently `sorry` or has a real proof
   (`grep -A3 "theorem Foo_is_wf" wasm2.0.lean` then look for `sorry` vs a
   tactic proof).
2. If it has a real proof already: mark "proved" in the table, no further
   action.
3. If it's `sorry`: try to prove it yourself if it looks simple (a few
   lines); if you do, note "proved by us" in the table and consider
   whether to leave your proof in a note here vs. actually fixing it in
   `wasm2.0.lean` — **remember `wasm2.0.lean` is not ours to edit** (it's
   the parallel effort's file); if you need the fact, restate it as your
   own local lemma in one of our files instead, referencing the
   `wasm2.0.lean` theorem name in a comment for traceability.
4. If it's `sorry` and non-trivial: mark "unknown, treated as true" in
   the table and move on — per user instruction, this is acceptable
   default behavior, just log it here so it's auditable.
5. If you have reason to believe it's actually FALSE (e.g. you found a
   counterexample): mark "false" and describe the counterexample; flag
   prominently to the user, since this would be a serious finding
   affecting both this project and the parallel `*_is_wf` audit.

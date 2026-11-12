# Rocq changes since the bundle3 resync baseline (`a8b585cdb` → `58af2e2f9`)

Written for: a future Claude session and the user. Covers step 2 of the
bundle9 instructions: "examine the new changes pushed to `rocq-backend-proof`
... analyze them and provide a summary."

## Headline: this is a small, targeted delta — no action needed on our side

Verified live branch tip via `gh api repos/Wasm-DSL/spectec/branches/rocq-backend-proof`
(also cross-checked against `curl` on the public REST API directly, since a
prior bundle noted `gh` occasionally goes silent in this environment): current
HEAD is `58af2e2f9135fcee4cd1aaf9c94695007910fb2f` ("Some more cases done",
DCupello, 2026-09-24T11:55:57Z) — exactly the commit already merged into this
repo's `lean-backend` branch (`868bca93f`, per the session-opening `git
status`). **The local checkout is already fully up to date; no re-sync was
needed this bundle.**

Diffed directly against `a8b585cdb` (the commit bundle3 through bundle8's work
was all done against):

```
 spectec/test-rocq/theories/type_progress.v | 318 ++++++++++++++++++++++++++++-
 spectec/test-rocq/theories/wasm.v          |  43 ++--
 2 files changed, 343 insertions(+), 18 deletions(-)
```

**Confirmed via a separate diff that `spectec/src/test-lean-claude/` itself
(our own directory) has zero changes in this range** — this single commit
touches only two Rocq files, neither of which any of our 6 already-ported
Lean files (`HelperLemmas`, `Subtyping`, `TypingLemmas`, `TypePreservationPure`,
`ExtensionLemmas`, `TypePreservation`) is a port of. `wasm2.0.lean` (the
auto-generated backend file, maintained by the parallel `*_is_wf` effort) is
also untouched — confirmed via `git log -1 -- spectec/src/test-lean-claude/wasm2.0.lean`
showing no commits in this range at all. **This satisfies step 3 of the
bundle9 instructions ("make any updates to the existing proof if their
equivalents have been changed") trivially: there is nothing to update.**

## What actually changed

### 1. `type_progress.v`: two more `t_progress_be` SIMD lane-cases closed

Recall from `bundle3/updated_documents/resync_impact_report.md` §3d:
`type_progress.v`'s only gap is `t_progress_be`, which previously had its
VUNOP/VBINOP/VTESTOP/VRELOP/VSHIFTOP/VBITMASK/VSWIZZLE/VSHUFFLE cases
entirely admitted in one block (`1-8: admit.`), attributed to the
`lane_`-union generator-encoding obstacle (the fact that `proj_lane__2 l ≠
None` isn't derivable from `wf_lane_` alone for an integer shape, since
`wf_lane_` is satisfied by any of the three `lane_` union injections).

This commit closes **two of those eight cases for real** (`Qed`, not
`Admitted`):

- **VUNOP**: proved via three new substantial lemmas (`vunop_real`,
  `vunop_total`, `vunop_not_none`, ~110 lines combined) that sidestep the
  `lane_`-union ambiguity by case-splitting on whether the operator's shape
  is a `Jnn` (integer) or `Fnn` (float) lane type up front, rather than
  trying to derive `proj_lane__2 l ≠ None` in general. `vunop_not_none`
  itself still has **one internal `admit.`** (for the case where an integer
  shape's lanes are well-formed for `wf_lane_ (lanetype_Jnn J)` but happen
  to be encoded via the `mk_lane__0`/`mk_lane__1` injection rather than
  `mk_lane__2` — the author's own comment: "this is not derivable as
  stated," i.e. still the same underlying obstacle, just isolated to a
  smaller residual case).
- **VTESTOP**: proved directly and fully (no residual admit) — the author's
  comment explains why this one case is easier than its seven siblings:
  `Instr_ok__vtestop`'s reduction rule has a genuine catch-all
  (`~ Step_pure_before_vtestop_false`), so *either* the "true" case applies
  *or* the catch-all does, regardless of which `lane_` injection is in play
  — no need to pin down the injection at all.

Net effect on the admit count within this specific case-group: was 1 admit
statement covering 8 cases (`1-8: admit.`); now VUNOP is fully proved (with
its own 1 residual internal admit in a helper lemma), VTESTOP is fully
proved, and the remaining 6 cases (VBINOP, VRELOP, VSHIFTOP, VBITMASK,
VSWIZZLE, VSHUFFLE) are still admitted (`1: admit.` + `1-5: admit.` after the
VUNOP/VTESTOP cases are pulled out). Whole-file `admit.`-occurrence count is
now 7 (up from what an earlier digest characterized as "5 sites for
`t_progress_be`" — the two counting methods aren't directly comparable, since
Coq's `N-M: admit.` numeric-goal-selector syntax closes multiple goals with
one textual `admit.` occurrence; not worth reconciling precisely since this
file isn't being actively ported yet, see below).

Two small generic list/bool helper lemmas were also added near the top of
the vector section (`Forall_all`/`all_Forall`, `all_and_Forall`/
`Forall_and_all`, `Forall_exists_Forall2`, `Forall2_size_eq`) — standard
`List.Forall` ↔ `all` (boolean) bridging, purely mechanical, no semantic
content beyond what their names say.

**Relevance to us**: none yet — `type_progress.v` is Tier I in
`proof_prioritization.md` (not started; explicitly deferred pending Tiers
B–H). Noted here for when that tier is picked up: two more real Rocq case
proofs are now available to port directly instead of needing to be derived
from scratch, and the shape of the remaining gap (now isolated to 6 lane-op
families instead of 8, plus one smaller residual case inside VUNOP's own
proof) is more precisely characterized than before.

### 2. `wasm.v`: one lemma fully closed, plus pointers to a NOT-YET-AVAILABLE `wf_counterexamples.v`

One previously fully-`Admitted` lemma (a `wf_uN` bound on the result of
subtracting an arbitrary truncated quantity, used by the unsigned-remainder
case of some numeric operator) is now `Qed`-proved, via a new helper lemma
`Hrem` establishing the needed bound directly. This is `wasm.v`, which
corresponds to `wasm2.0.lean` (auto-generated, not something this project
ports by hand) — **not directly actionable by us**, but worth knowing the
generated Lean file's own `*_is_wf`-style companion (if one exists for the
same fact) might now also be provable where it wasn't before; not checked
this turn since nothing in our 6 files currently depends on it (see
`is_wf_theorems.md`, still empty).

**More interesting, and worth flagging to the user directly**: five comments
were added at existing `Admitted`/`admit.` sites in `wasm.v`, each citing a
specific theorem name as "Mechanised: `<name>` in `wf_counterexamples.v`":

| Site (existing gap) | Cited counterexample theorem |
|---|---|
| `fone_is_wf`'s inverse direction (N=7 case) | `fone_is_wf_false` |
| `wf_byte`/UTF-8 encoding admit | `utf8_is_wf_false` |
| the VBITMASK `Step_pure` admit | `Step_pure_is_wf_false` |
| the packed-load `Step_read` admit | `Step_read_is_wf_false` |
| the `RUNELEM`/element-init `wf_instr` admit | `runelem_is_wf_false` |
| the `RUNDATA`/data-init `wf_instr` admit | `rundata_is_wf_false` |

**`wf_counterexamples.v` itself does not exist anywhere in this commit, this
branch, or (per a live GitHub code search) anywhere in the
`Wasm-DSL/spectec` repository at all.** These are forward-references to a
file the author has apparently written locally but not yet pushed — the
comments name specific theorems asserting that `fone_is_wf`, `utf8_is_wf`,
`Step_pure_is_wf`, `Step_read_is_wf`, `runelem_is_wf`, and `rundata_is_wf`
are each **provably FALSE**, with concrete counterexamples (one is spelled
out inline: "`v_N = 7` is a counterexample" for `fone_is_wf`).

**This is directly relevant to the user's separate, parallel `*_is_wf` audit
effort on `wasm2.0.lean`** (mentioned in this project's own standing
instructions — see `NOTES.md`). If `wasm2.0.lean` has theorems of the same
or matching names (`fone_is_wf`, `utf8_is_wf`, etc. — Lean-side naming may
differ slightly), the parallel effort should know Rocq-side counterexamples
apparently already exist for at least these six, even though the mechanised
file backing them isn't pushed yet. **Checked whether this affects our own
work**: grepped all 6 ported Lean files for these six names — only one
passing *comment* mention (`TypePreservationPure.lean:189`, a stray
parenthetical, not a load-bearing dependency). None of our proofs currently
invoke any of these six as a hypothesis, so nothing in this project is
currently at risk from this finding. Recommend flagging this file's
existence (and its absence upstream) to whoever owns the parallel `*_is_wf`
audit, since they may want to ask the Rocq author directly for
`wf_counterexamples.v` rather than re-deriving these six counterexamples
independently.

## Bottom line for steps 3–6

- **Step 3 (update existing proofs for changed Rocq equivalents): nothing to
  do.** Confirmed by direct diff that none of the 6 already-ported Rocq files
  changed in this range.
- **Step 4 (`Vals_ok_non_bot`)**: unaffected by this delta (lives in
  `typing_lemmas.v`, not touched) — proceeding as the user separately
  specified; see `vals_ok_non_bot_resolution.md`.
- **Step 5/6 (continue "What's next" / keep porting)**: unaffected in
  substance — the `proof_prioritization.md` ordering from bundle3's addendum
  is still current; only Tier I (`type_progress.v`, not started) gets a
  slightly more precise description of its remaining gap, captured above and
  reflected in this bundle's `proof_prioritization_update.md`.

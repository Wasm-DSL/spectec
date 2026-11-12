# Insights for the next turn (end of bundle20)

Written for: the next Claude session on this project, possibly a different session or model.
Everything here was true at the end of bundle20 (2026-10-05); check names and line numbers before
relying on them. Read the bundle18/bundle16 insight docs for older Lean lessons; this one only adds
what is new.

## 0. Standing rules (unchanged)

- **Never modify anything outside `spectec/src/test-lean-claude`.** Check after every batch with
  `bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh [BASELINE] [LABEL]`
  (from the repo root).
  - It is race-free since bundle20 (unique sub-second filenames, `grep -a`).
  - The bundle20 baseline is `check-20261005T051653Z.txt`. Start each new turn with a fresh
    `check.sh` run and use its output as the new baseline.
  - Pre-existing out-of-target entries (`spectec/test-lean/todaywasm*.lean`, untracked repo-root
    files) are the user's. Never touch them.
- **Agents.** Every agent must get the safety order verbatim, run the check at start and end, and
  log under `bundle<N>/agent_logs/`. Agents write only their own log plus scratch files in the
  session scratchpad.
- **Logging.** Each exchange gets `bundle<N>/` with `prompt_N.md` (verbatim; append mid-turn
  messages), `response_N.md`, `response_N_modelinfo.md` and `user_requested_documents/`. Never edit
  older bundles.
- **Fidelity.** Signatures must match Rocq; proofs are free (proof irrelevance). Document every
  deviation.
- **Effort.** Imitate Rocq first, then use its intuition; stop and report significant issues.
- Ignore `TODO FROM USER` notes (they are the user's own); the 16 dead `sorry`s are marked with one.

## 1. State at the end of bundle20

- **Preservation:** audited, complete, non-vacuous. See `preservation_audit_report.md` (it includes
  a hand-checking guide).
- **Progress:** `TypeProgress.lean` is new, 8005 lines, everything proved except two subcases that
  are false as the spec stands (Rocq `admit`s them too). See `progress_port_status.md` and
  `progress_port_deviations.md`.
- **Open items for the user** (reported, not ours to fix):
  - B. `Moduleinst_ok`'s hoisted non-emptiness premise (from SpecTec's
    `middlend/sideconditions.ml`).
  - C. `Globaltype_ok` admits only mutable globals.
  - The two stuck vector instructions.
  - The `Step_read_is_wf` 2^32 corner case.
  - The `vstore_lane-oob` `N`-bits typo.
- **Remaining `sorry`s in the hand-written files:**
  - the 16 marked dead ones (15 `HelperLemmas` + `Val_ok_store`);
  - the 2 known-false progress subcases.
- `wasm2.0.lean` still has its 63 `sorry`s, exactly Rocq's `Admitted` set.

## 2. Techniques that worked well in bundle20 (reuse them)

### 2.1 Generate case-lemma statements from Lean's own recursor

To split a big induction (Rocq `Scheme … Induction for …` plus bullets) into independent
lemmas, print the minor premises of the auto-generated recursor with a tiny meta-program:

```lean
import ExtensionLemmas
open Lean Meta Elab Command
elab "#minors " id:ident : command => liftTermElabM do
  let info ← getConstInfo id.getId
  forallTelescope info.type fun xs _ => do
    let mut i : Nat := 0
    for x in xs do
      logInfo m!"[{i}] {← x.fvarId!.getUserName} : {← inferType x}"
      i := i + 1
set_option pp.funBinderTypes true
set_option pp.proofs true
#minors Instrs_ok.rec
```

Then turn each printed premise into `theorem <name>_<ctor> : <premise with motive_i replaced by
your motive defs> := sorry`. Define the motives with the derivation as an extra, unused argument,
as Rocq's do, so that `motive_1 C x tf (Ctor …)` maps to `P C x tf (Ctor …)` verbatim. Two
round-trip problems with the pretty-printer:

1. **Record literals.** `{ TYPES := …, … } ++ C` needs `( … : context)`. Put each one on a single
   line, or you hit the indentation-sensitive parse error.
2. **`Rat` casts are dropped**, e.g. `((2 ^ …) : Rat) ≤ …` in the memory rules. Splice the original
   premise text from the generated source back in by position. A store parameter prints as `a✝³`;
   rename it.

Scripts: `bundle20/checkpoints/` holds the merge scripts; the generator logic is described in
`progress_port_deviations.md` §0.

### 2.2 Agents prove in scratch; the main thread merges

- An agent copies the target's header verbatim into `Work.lean` (`import TypeProgress`), renames
  it `<name>_proof`, proves it, and adds the guard `example : type_of% @<name>_proof = type_of% @<name> := rfl`.
  The guard fails on any statement drift.
- The returned tactic block then drops into the real file unchanged. The splice script is
  `checkpoints/merge_proofs.py`.
  - Beware: a regex that swallows the newline after `sorry` glues the next declaration onto the
    proof.
  - Validate the merged copy with `lake env lean <copy>` *before* installing.
- **Ordering rule for agents:** use only declarations that come *before* the target in the file.
  Earlier `sorry`'d lemmas are fine.
- Do not rebuild a module that running agents import. Install merged proofs only when no agent is
  running Lean.

### 2.3 Signature audits with pre-extracted side-by-side files

A Python extractor (strip Rocq `(* *)` comments, take each Rocq statement up to `Proof`, pair it
with the Lean declaration by name or by doc-comment citation) made audits cheap and parallel. Copies
live in the session scratchpad (`sigs/extract.py`, `extract_model.py`); re-create them if the
scratchpad is gone. They are about 100 lines of Python.

### 2.4 Budget and usage limits

- 11 concurrent Opus agents hit the account usage limit within about 6 minutes (≈2.1M tokens).
- Since then: at most 3 concurrent Lean-running agents (machine RAM is also tight: the user's
  editor runs 6 Lean servers, and each `lake env lean` peaks at ≈3.6 GB RSS, mostly shared
  olean pages).
- Use Sonnet for simple helper-lemma batches, and use text-only auditors.
- The progress proof phase used ≈5.9M subagent tokens for 280 targets.

## 3. New Lean pitfalls (from the 43 prover agents)

- **`omega` ignores facts stated with the type abbreviations `N`, `M`, `n`** (all
  `abbrev … := Nat` in the generated file). A hypothesis `h : @LE.le N _ M 16` or `v_n : n` is
  invisible to `omega`. Restate it, e.g. `have h' : @LE.le Nat _ M 16 := h`, or use explicit
  `@Eq Nat`.
- **More auto-promoted parameters** (each takes no binder slot in `cases … with`):
  - `wf_num_`'s numtype index: `num__case_0` takes 5 names, `num__case_1` takes 4;
  - `Expr_ok2`'s store: `mk_Expr_ok2` takes 7, not 8;
  - `Frame_ok`'s store: `rename_i` takes 11 names;
  - `wf_uN`'s `v_N` when it is a literal.
- `simp only [proj_uN_0]` can also rewrite `memarg.OFFSET` projections into `memarg.2.1`, which
  breaks `omega` atoms. Rewrite only the specific `proj_uN_0 (uN.mk_uN n) = n` instances.
- The generated `wf_uN` bound is `Int.toNat ((2:Int)^v_N - 1)`. `omega` sees `(↑2)^v_N` as a
  different atom from `2^v_N`, so bridge it once by hand.
- A lambda binder inside a `Rat`-cast context needs an explicit `(k : Nat)` annotation.
- `Forall` and `Forall₂` are the generated non-inductive defs: `Forall P l` is `∀ x ∈ l, P x`, and
  `Forall₂ R l l'` is zip-based. Rocq proofs that do `induction HForall` become pointwise
  arguments.

## 4. Consistency of the project axioms (new knowledge)

- Rocq's `|x| = q` with `q : Q` is **floored**: `Qfloor` then `Z.to_N` (wasm.v:194-200).
  `rat_to_nat` is exactly that composite.
- Lean's exact-`Rat` reading of `ibytes_len'`/`ibytes_len''` derived `False`; they are now fixed.
  When porting any Rocq statement with `|…| = (… / …)%Q` or `(… : N)` around a `Q`, use
  `rat_to_nat`.
- All 23 project axioms now mirror `axioms.v` and constrain only `opaque` functions. Progress uses
  17 of them, and preservation uses none.

## 5. If the user regenerates `wasm2.0.lean`

1. Re-apply `bundle19/user_requested_documents/wasm2.0_hand_edits.patch` (hand-written `*_is_wf`
   proofs, re-signed `Step_*_is_wf`).
2. `lake build`. Expect breakage only where a generated definition changed.
3. If the user fixes B (the `Moduleinst_ok` non-emptiness premise), the proofs that rebuild
   `Moduleinst_ok` will need a small edit: `Extend_store_moduleinst` (40-argument reconstruction),
   the witness, and `t_progress`'s `Moduleinst_ok` step. If they fix C (`Globaltype_ok`), little
   should break, since no hand-written proof mentions `Globaltype_ok`.
4. If they make the two stuck vector instructions reducible (or invalid), the two `sorry`s in
   `t_progress_be_vload_pack`/`t_progress_be_vcvtop` become provable. Each is isolated in one
   branch with a comment.

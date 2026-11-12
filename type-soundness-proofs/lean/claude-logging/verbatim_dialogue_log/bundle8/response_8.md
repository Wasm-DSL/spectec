## Major find: `spectec/test-lean/typing_lemmas.lean` — a near-complete prior manual attempt

Scanned `spectec/test-lean/typing_lemmas.lean` (2071 lines, the user's own
earlier hand-written Lean port, predating this Claude-driven project) and
its siblings (`typing_lemmas_OLD.lean`, `typing_lemmas_aesop.lean`). Key
findings before touching anything:

- **Confirmed byte-identical `wasm2.0.lean`** between `spectec/test-lean/`
  and `spectec/src/test-lean-claude/` (`diff -q`, exit 0) — so anything that
  compiled there is guaranteed to compile against *this* project's backend
  output too, no adaptation needed for constructor names/shapes.
- The file currently builds with **only one real remaining `sorry`**
  (`instrtype_sub_refl`, a lemma this project already has proved
  independently in `Subtyping.lean`) — everything else, including the full
  `ai_principal_typing` definition and `instr_typing_inversion`/
  `ai_typing_inversion`, is already proved.
- It depends on `Mathlib.Tactic` and a small `custom_notation.lean` (`f->`
  for `mkFunctype`, `sub<` for `Valtype_sub`, `subs<` for `ResulttypeSub`)
  — both trivially mappable onto this project's own identically-named
  definitions.

**Ported into this project's `TypingLemmas.lean`** (after checking
correctness, per your instruction):
- `ai_principal_typing` (the ~340-line, 50+ case definition — **the**
  central blocker for this whole file's inversion lemmas).
- `instr_principal_typing`'s partner `principal_typing_conversion`.
- `instr_typing_inversion` (full proof, ~19 non-trivial case bodies).
- `ai_typing_inversion` (the master administrative inversion lemma, 6-way
  case split on `Instr_ok2`).
- `injective_admininstr_instr` (68×68 mechanical case bash).

**One real bug found and fixed while checking correctness** (exactly what
you asked me to check for): the source file's `BR_TABLE` case in
`ai_principal_typing` wrote
`∀ l ∈ ls, ∃ r, ... ∧ ... ∧ ∃ r', ...` with no parens around the `∀`'s
body. Lean's parser puts the trailing `∃ r', LABELS[l']? = r' ∧ ts subs< r'`
clause *inside* the `∀ l ∈ ls` binder, so whenever `ls = []` (a valid
`BR_TABLE` with only a default target), that clause becomes vacuously true
and the default label's own validity/subtyping requirement silently
disappears. Checked against the live Rocq `ai_principal_typing`
(`typing_lemmas.v:414`, fetched at the still-current
`a8b585cdb536b2b2e53ff45fa8010de88f05a042`), which states the `ls`-Foralls
and the two `l'` conditions as five independent top-level conjuncts — fixed
here by parenthesizing the `∀` explicitly, matching Rocq.

**BEq-vs-`DecidableEq` check** (per your specific warning about
pre-`derive_deceq` code): grepped `typing_lemmas.lean` for `BEq`/
`DecidableEq`/`decide` — none appear in the file at all, so nothing to fix
there specifically; the concern doesn't apply to the parts I ported.

**One area flagged rather than silently trusted**: the `LOAD`/`STORE`
packed-access cases use an `Inn`-restricted existential (vacuously
unsatisfiable for F32/F64), which matches an *older* reading of Rocq's own
`ai_principal_typing` (which used to have explicit `F32`/`F64 => False`
arms). The *current* live Rocq source no longer excludes F32/F64 for
packed `STORE` at all (those arms are commented out upstream) — a live
upstream-vs-port discrepancy, not a mistake made this session. Left as the
more conservative reading; documented in-line, flagged for revisit only if
a downstream packed-`STORE` proof needs it.

## Infrastructure change: `Mathlib.Tactic` now imported in `TypingLemmas.lean`

Needed for the ported proofs (`omega`, `norm_num`, `exact_mod_cast`,
`positivity`, `linarith`, `simp_all` with a larger default set). Mathlib
was already a resolved `lakefile.lean` dependency, just unused; fetched the
prebuilt oleans via `lake exe cache get` (~6.4 GB, a few minutes) rather
than compiling from source — smoke-tested with a standalone `omega` file
before committing to the approach. One regression from this: `simp_all`'s
larger default simp-set made `injective_admininstr_instr`'s 68×68 case bash
exceed the default heartbeat budget (it took ~26s in bundle7, before
Mathlib); fixed with a local `set_option maxHeartbeats 1000000 in`.

## Debugging notes: `cases`/`case` binder-order surprises

Porting `ai_typing_inversion` surfaced a sharper version of the "leading
index doesn't get a name" rule already known from earlier bundles: for
several `Instr_ok`/`Instr_ok2`/`Ref_ok` constructors, hypotheses that
mention an *already-bound* piece of data (e.g. `wf_instr (BR_TABLE l_lst
l')`, which mentions `l_lst`/`l'`) get bound **earlier** in `cases`'s
actual argument order than their source-declaration position — sometimes
reordered ahead of hypotheses that appear textually before them. Resolved
each such case empirically via `trace_state`+`sorry` probes (dumping the
real post-`cases` context, then reading off the true types) rather than
guessing from the source declaration order — this was the only reliable
method found. Also found one case (`Ref_ok.func`, inside `ai_typing_inversion`'s
`ref` branch) where even `cases h with | func names... =>` didn't bind
names as expected for reasons that remained unclear after two probe
rounds; switched to plain `cases h` followed by `rename_i` for that one
spot, which worked immediately and is likely the more robust idiom to
reach for first next time this kind of naming confusion recurs.

## The `Vals_ok_non_bot` gap: analysis document, not a fix

Per your instruction, did **not** attempt to fix `Vals_ok_non_bot` this
turn. Wrote up the root cause (this codebase's `Forall₂` is a zip-based
`def`, not Rocq's length-forcing inductive `Forall2`, so the lemma is
literally false as stated — confirmed with a concrete counterexample) and
three options ranging from a local length-hypothesis patch to redefining
`Vals_ok` itself, plus a note that the newly-available `Mathlib.Tactic`
import makes a `List.Forall₂`-bridging fix cheap if wanted. See
`bundle8/vals_ok_non_bot_analysis.md`.

**Verified**: full project `lake build` exits 0, zero errors (3005 jobs,
Mathlib now included in the build graph). Safety check re-run clean — only
the same pre-existing untracked scratch files outside
`spectec/src/test-lean-claude/` seen in every prior bundle; the one large
new filesystem change this turn (~6.4 GB of downloaded Mathlib `.olean`
cache) landed entirely inside `spectec/src/test-lean-claude/.lake/`, inside
the permitted directory.

Current `sorry` tally: `TypingLemmas.lean` **17** (down from 20),
`HelperLemmas.lean` 29, `Subtyping.lean` 32, `TypePreservationPure.lean` 33,
`ExtensionLemmas.lean` 79, `TypePreservation.lean` 17.

## What's next

`ai_val_principal_typing_inversion` and the `ais_*_vals*`/`construct_ai_maybe`
cluster are now unblocked on the `ai_principal_typing` side, but several
still need either `instr_of`'s real body or the `Vals_ok_non_bot` gap
resolved first (per your instruction, leaving that alone until you've had a
chance to review the analysis doc). `instr_of`'s ~50-case mechanical body
is likely the next highest-leverage target. Continuing unless redirected.

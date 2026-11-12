# `Vals_ok_non_bot`: resolution (Options 2 + 3 implemented)

Written for: a future Claude session and the user, recording what was
actually done in response to `bundle8/vals_ok_non_bot_analysis.md`. That
document is left untouched (historical record); this is the follow-up
"what we did about it."

## Decision (user's, verbatim from the bundle9 prompt)

> With regards to `.../bundle8/vals_ok_non_bot_analysis.md`, my choice is to
> do a combination of Options 2 (Redefine `Vals_ok` itself to bake in the
> length fact. Do the necessary refactoring as well) and 3 (Add a generic
> bridge lemma to Mathlib's own `List.Forall₂`...). Option 2 is the
> baseline, and I think Option 3 might make some proofs down the line more
> ergonomic.

## What was implemented

### Option 3: generic `Forall₂` ↔ `List.Forall₂` bridge, in `HelperLemmas.lean`

Added `import Mathlib.Tactic` to `HelperLemmas.lean` (previously
Mathlib-free; cost is negligible since Mathlib's oleans were already fetched
in bundle8) and two new lemmas, in a new "`Forall₂` bridge to Mathlib's
`List.Forall₂`" section at the end of the file:

```lean
theorem to_mathlib_forall₂ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (hlen : l1.length = l2.length) (h : Forall₂ R l1 l2) : List.Forall₂ R l1 l2

theorem from_mathlib_forall₂ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) : l1.length = l2.length ∧ Forall₂ R l1 l2
```

`to_mathlib_forall₂` needs an explicit length hypothesis (our `Forall₂` is
weaker than Mathlib's without one); `from_mathlib_forall₂` doesn't, since
Mathlib's `List.Forall₂` already forces equal length via
`List.Forall₂.length_eq`. Both proved via `List.forall₂_iff_zip`
(`Mathlib.Data.List.Forall2`), which states almost exactly this
equivalence already. Not a port of any Rocq lemma — new project-local
infrastructure, placed in `HelperLemmas.lean` (general-purpose helpers) so
it's available to every downstream file, not just `TypingLemmas.lean`.

### Option 2: `Vals_ok` redefined to bake in the length fact

`TypingLemmas.lean`:

```lean
def Vals_ok (v_S : store) (v_vals : List val) (v_ts : List valtype) : Prop :=
  v_ts.length = v_vals.length ∧ Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals
```

(was: `Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals`, no length conjunct).

**"Necessary refactoring" performed**: grepped every use of `Vals_ok` across
the project (`ExtensionLemmas.lean:508`, `TypePreservation.lean:60,61,69,70,123`,
plus `TypingLemmas.lean`'s own `ais_vals_typing_inversion`/`construct_ais_vals`)
— all six call sites were already `sorry`-bodied before this change, so
none of them could break; no proof needed re-deriving. `Vals_ok`'s type
signature (`store → List val → List valtype → Prop`) is unchanged, only its
internal definition, so every caller's *statement* still typechecks as-is.

**`Vals_ok_non_bot` itself restated to route through `Vals_ok` rather than
the bare `Forall₂`** Rocq states directly (`typing_lemmas.v:2071` — line
number shifted slightly from the `:1927` an earlier digest cited, current
HEAD `58af2e2f9`; same lemma). This is a deliberate, documented deviation
from a literal signature transcription: Rocq's own `Forall2` already carries
the length fact for free (it's baked into the inductive's shape), so a
literal Rocq signature naturally has no separate length hypothesis to state.
Since this project's `Forall₂` does *not* carry that fact, `Vals_ok` is
exactly the Lean-side stand-in for what Rocq gets for free — routing
`Vals_ok_non_bot`'s hypothesis through it (rather than bolting an
`hlen : v_ts.length = v_val.length` hypothesis directly onto the bare
`Forall₂`, i.e. Option 1) keeps the fix centralized in one place instead of
repeated at every lemma that needs it. This falls under the project's
standing "obvious optimizations" allowance for representational gaps
between Rocq's inductive `Forall2` and this backend's zip-based `Forall₂`
— the same class of judgment call already made for `Extend_*`'s `wf_*`
hypotheses and the `holds_upto` idiom.

Proof (mirrors Rocq's own induction-on-`v_val` structure, translated through
the Mathlib bridge):

```lean
theorem Vals_ok_non_bot (v_S : store) (v_val : List val) (v_ts : List valtype) :
    Vals_ok v_S v_val v_ts → Forall (fun t => t ≠ valtype.BOT) v_ts := by
  rintro ⟨hlen, hforall⟩
  have h2 : List.Forall₂ (fun t v => Val_ok v_S v t) v_ts v_val := to_mathlib_forall₂ hlen hforall
  clear hforall hlen
  induction h2 with
  | nil => intro t ht; simp at ht
  | cons hval _ ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Val_ok_non_bot v_S _ t hval
      · exact ih t ht
```

Compiled clean on the first attempt (no debugging round needed). Full
project `lake build` after this change: exit 0, zero errors (3005 jobs).
`TypingLemmas.lean`'s `sorry` count: 17 → 15 (one real proof; the count
delta is 2, not 1, because the old doc comment's own prose also contained
the literal substring `sorry`, which the tracking `grep -c sorry` picks up
as well as the actual `:= sorry` term — not a second lemma).

## What was deliberately NOT done

- **`ais_vals_typing_inversion` and `construct_ais_vals` themselves are still
  `sorry`.** They were already blocked on `ai_principal_typing`'s real body
  (Tier C) per bundle7/8, not solely on this gap — fixing `Vals_ok` unblocks
  them from *this* obstacle but they remain gated on the other one. Not
  attempted this turn; queued in `proof_prioritization.md`'s bundle9 update.
- **The dead `Forall2_nth`/`Forall2_lookup`/`Forall2_forall2*`/
  `Forall2_list_update_func*` family in `HelperLemmas.lean`** (still `sorry`,
  ~14 lemmas) has the exact same representational gap `Vals_ok_non_bot` had
  (each implicitly assumes the length fact Rocq's inductive `Forall2` gives
  for free) — per bundle3's resync notes these no longer correspond to any
  lemma in the current Rocq source (all removed upstream), so per the
  project's "lemma-for-lemma" mandate there is no live Rocq lemma left to be
  faithful to. Left untouched: not worth spending effort matching a target
  that no longer exists, though the new `to_mathlib_forall₂` bridge would
  make fixing them cheap if a future need arises (e.g. if a currently-live
  lemma turns out to need one of them as a lower-level building block).
- **`funcinst_same`** (`ExtensionLemmas.lean`, flagged since bundle2/3 as the
  same class of gap) was not revisited — per bundle3's resync notes, the
  corresponding Rocq name was removed upstream entirely with no obvious
  direct replacement found, so it's a separate open question (possibly
  resolved a different way in the current Rocq source, not yet checked) —
  out of scope for this specific `Vals_ok` fix.

# `Vals_ok_non_bot`: the `Forall₂` length gap, and options for fixing it

Written for: Yong Zheng Yew, to review later and decide how to proceed. Not
acted on this session per your explicit instruction to leave it be for now —
this is comments/suggestions only.

## The problem, restated precisely

In `TypingLemmas.lean`:

```lean
def Vals_ok (v_S : store) (v_vals : List val) (v_ts : List valtype) : Prop :=
  Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals

theorem Vals_ok_non_bot (v_S : store) (v_val : List val) (v_ts : List valtype) :
    Forall₂ (fun t v => Val_ok v_S v t) v_ts v_val → Forall (fun t => t ≠ valtype.BOT) v_ts
```

`wasm2.0.lean`'s generated `Forall₂` is a `def`, not an inductive:

```lean
def Forall₂ {α₁ α₂ : Type} (P : α₁ → α₂ → Prop) (xs₁ : List α₁) (xs₂ : List α₂) : Prop :=
  ∀ t ∈ xs₁ |>.zip xs₂, P (t.1) (t.2)
```

`List.zip` stops at the shorter list, so `Forall₂ P xs₁ xs₂` says nothing at
all about the tail of whichever list is longer. Concretely: with
`v_ts := [valtype.BOT]` and `v_val := []`, the hypothesis
`Forall₂ (fun t v => Val_ok v_S v t) v_ts v_val` reduces to `∀ p ∈ [], _`,
which is vacuously `True` — yet the conclusion `Forall (· ≠ BOT) [BOT]` is
false. **The theorem as stated is false**, not just hard.

Rocq's `Forall2` (used in the source `typing_lemmas.v`) is the *inductive*
version, which has no `nil`/`cons` mismatch case at all — `Forall2 P [] (x
:: xs)` and `Forall2 P (x :: xs) []` are simply not inhabited. That's why
the Rocq proof of the analogous lemma goes through by structural induction
without ever needing to worry about length: the "both lists are the same
length" fact comes for free from the inductive's own shape, rather than
needing to be threaded through as a side condition.

This is the same phenomenon flagged for `funcinst_same` during the earlier
resync work (see `bundle3/updated_documents/rocq_proof_intuition_addendum.md`
if you want the other example side by side) — it's a structural mismatch
between how the SpecTec Lean backend encodes `Forall`/`Forall₂` (predicate
over the zip) versus how Rocq's `Forall2` is encoded (inductive, length
implied). It will very likely recur anywhere else a Rocq `Forall2` fact is
used length-sensitively.

## Where this actually bites

Grepped `Forall₂` usage: only `Vals_ok` uses it directly in this codebase's
target lemma set right now. Downstream, `ais_vals_typing_inversion` and
`construct_ais_vals` (both still `sorry`) also go through `Vals_ok`, so
they inherit the same gap if their Rocq proofs rely on
`Vals_ok_non_bot`-style length-sensitive reasoning (checked: Rocq's
`construct_ais_vals` does an induction that keeps `v_vals`/`ts` in lockstep,
so it implicitly relies on them being the same length throughout — the Lean
port of that lemma will need *some* resolution of this gap before it can be
proved faithfully, not just `Vals_ok_non_bot` in isolation).

## Options, roughly ordered by how invasive they are

1. **Strengthen the theorem statement with an explicit length hypothesis.**
   ```lean
   theorem Vals_ok_non_bot (v_S : store) (v_val : List val) (v_ts : List valtype)
       (hlen : v_ts.length = v_val.length) :
       Forall₂ (fun t v => Val_ok v_S v t) v_ts v_val → Forall (fun t => t ≠ valtype.BOT) v_ts
   ```
   This is provable (induction on both lists together, using `hlen` to keep
   them in lockstep) and is the smallest possible change. Downside: every
   *caller* now has to carry/prove the length fact too, which may or may not
   already be available at each call site — needs checking case by case.
   `Vals_ok`'s own callers mostly come from `Instrs_ok2`-inversion lemmas
   where a length fact is often independently derivable from a
   `Resulttype_sub` fact in context (`resulttype_sub_size_eq`, already
   proved in `Subtyping.lean`), so this is likely *not* a heavy burden in
   practice, just a bit of extra plumbing at each use site.

2. **Redefine `Vals_ok` itself to bake in the length fact**, e.g.
   ```lean
   def Vals_ok (v_S : store) (v_vals : List val) (v_ts : List valtype) : Prop :=
     v_ts.length = v_vals.length ∧ Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals
   ```
   This keeps the *usage* of `Vals_ok` at call sites unchanged (no extra
   hypothesis to plumb through), at the cost of every place that
   *constructs* a `Vals_ok` fact needing to also supply the length proof
   (usually trivial — it typically falls out of whatever built the value
   list in the first place). This is closer in spirit to Rocq's inductive
   `Forall2` (which *is* "zip + implied length"), and is probably the
   cleanest fix if you're willing to touch `Vals_ok`'s definition. Would
   need re-checking `Vals_ok`'s two or three existing call sites (all
   currently `sorry`, so nothing already-proved would break).

3. **Add a generic bridge lemma to Mathlib's own `List.Forall₂`**, along
   the lines of what the prior Lean session's own
   `spectec/test-lean/typing_lemmas.lean` already sketches at its very top
   (`to_mathlib_forall₂`/`from_mathlib_forall₂`, lines 15–26 of that file):
   ```lean
   theorem to_mathlib_forall₂ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
       (hlen : l1.length = l2.length) (h : Forall₂ R l1 l2) : List.Forall₂ R l1 l2 :=
     List.forall₂_iff_zip.mpr ⟨hlen, fun hab => h _ hab⟩
   ```
   i.e. still requires the length fact up front (this doesn't sidestep the
   real issue, it just converts a proved `Forall₂` fact into Mathlib's
   `List.Forall₂` so the rest of that library's lemmas become available —
   `List.Forall₂.length_eq`, induction principles, etc.). Useful as a
   *supplement* to option 1 or 2 (once you have the length fact one way or
   another, converting to `List.Forall₂` may make the rest of the proof of
   `Vals_ok_non_bot`, `construct_ais_vals`, etc. much shorter — Mathlib's
   `List.Forall₂` has a real induction principle, unlike this codebase's
   zip-based one). Note this file was NOT ported into this project's own
   `TypingLemmas.lean` this session — only mentioned here as available,
   since `Mathlib.Tactic` is now imported for `ai_principal_typing`'s port
   (see below) — so this bridge would be cheap to add if wanted (no new
   dependency required, it's already imported).
4. **Do nothing at the definition level, only patch each affected lemma's
   *statement*** the way option 1 does, on a lemma-by-lemma basis, without
   touching `Vals_ok`'s own definition. This is what I'd lean towards if
   you want to keep changes minimal and localized, since `Vals_ok_non_bot`
   is currently the only lemma actually blocked on this — no urgency to
   redesign `Vals_ok` itself until a second or third lemma turns out to need
   the same fix.

## My suggestion, if it's useful

Start with option 1 (add `hlen : v_ts.length = v_val.length` to
`Vals_ok_non_bot`'s own signature) and see how it propagates. If, once you
get to `ais_vals_typing_inversion`/`construct_ais_vals`, the length
threading turns out to be a recurring tax at *every* call site (not just
these two), that's the signal to switch to option 2 (bake the length fact
into `Vals_ok`'s definition once, centrally) rather than keep patching
individual theorem statements.

## Context: why `Mathlib.Tactic` is now available to help with this

Separately from this specific gap: this session added
`import Mathlib.Tactic` to `TypingLemmas.lean` in order to port
`ai_principal_typing`, `instr_typing_inversion`, `ai_typing_inversion`, and
`principal_typing_conversion` from `spectec/test-lean/typing_lemmas.lean`
(per your go-ahead this bundle). That file already depends on Mathlib
(`import Mathlib.Tactic`), and Mathlib was already a resolved-but-unused
`lakefile.lean` dependency in `test-lean-claude` — fetched the prebuilt
oleans via `lake exe cache get` (~6.4 GB, a few minutes) rather than
compiling Mathlib from source. This means the `to_mathlib_forall₂`-style
bridge in option 3 above, and any other Mathlib `List`/`List.Forall₂`
lemma, is now available for free in `TypingLemmas.lean` without any further
dependency work — worth knowing when you come back to this.

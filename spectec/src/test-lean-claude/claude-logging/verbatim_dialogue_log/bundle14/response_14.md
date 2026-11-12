## Signature audit: 12 findings, 11 fixed, 1 confirmed-correct-as-is

Triaged all 12. `Subtyping.lean` and `TypePreservationPure.lean` came back completely clean — good sign for how carefully those got ported.

**A real soundness gap, fixed**: `ai_principal_typing`'s `GLOBAL_SET` case (`TypingLemmas.lean`) was quantifying over any mutability, so as stated it would have accepted `global.set` on an *immutable* global. Pinned to `some r_MUT.MUT`, matching `Instr_ok`'s own constructor (which already had the pin — `instr_typing_inversion`'s generic proof pipeline picked it up with no further changes).

**Two more gaps in the same `def`, fixed, with small knock-on proof patches**: the `RETURN` case was missing a conjunct (`Instr_ok v_C RETURN (...)`); the `FRAME_` case discarded its own arity argument via `_`, so it couldn't even state the `ts.length = v_n` conjunct Rocq has (its sibling `LABEL_` case does this correctly, for contrast). Both fixed. Since `ai_principal_typing` itself has zero sorries, I had to patch the two theorems that construct instances of it (`instr_typing_inversion`'s RETURN case, `ai_typing_inversion`'s FRAME_ case) — the FRAME_ fix was trivial, it already had the exact fact bound as `hlen` a few lines up. Rebuilt clean after each edit; `TypingLemmas.lean`/`Subtyping.lean` stayed at 0 sorries throughout. Also had to patch this bundle's own freshly-written `frame_vals_preserves` to destructure one more field.

**4 signatures in `TypePreservation.lean`, all `sorry`'d, all missing the same `wf_config` hypothesis** — mechanical, zero-risk fix.

**3 more instances of the hard-coded-`Option` bug** (`s_invert_mems`, `s_invert_tables`, `memory_grow_mem_extension`) — same class already caught once for `construct_meminsts_grow` earlier this bundle, but these three weren't. Generalized to genuine `Option Nat`.

**`list_slice_update` was actually wrong, not just missing a hypothesis**: the `take`/`append`/`drop` definition only preserves length when the update slice's length matches exactly; Rocq's real recursive definition stops early and is unconditionally length-preserving. Redefined it to match Rocq's real algorithm and proved the length lemma for real (no more sorry) via `induction ... using list_slice_update.induct`.

**Left alone, on purpose**: the `STORE`-packed-float case — traced it and Lean's stricter version is actually the correct one; current upstream Rocq has a live inconsistency between `ai_principal_typing` (which has a commented-out exclusion) and `Instr_ok` (which still excludes it structurally). Worth reporting upstream, not a Lean bug.

Also fixed a doc-accuracy issue the audit surfaced: `TypePreservation.lean`'s header claimed only 3 of 13 declarations are `Admitted`; `num_default_is_well_formed`'s cited Rocq lemma is actually entirely commented out, not `Admitted`, so it was neither of the two buckets the header described.

`lake build` clean throughout (checked after every edit, not just at the end). Safety check clean.

Updated tally: `HelperLemmas.lean` 27, `Subtyping.lean` 0, `TypingLemmas.lean` 0, `TypePreservationPure.lean` 10, `ExtensionLemmas.lean` 76, `TypePreservation.lean` 12 — 350 declarations total, 125 still `sorry`.

That closes out everything from this turn's resync-and-audit request.

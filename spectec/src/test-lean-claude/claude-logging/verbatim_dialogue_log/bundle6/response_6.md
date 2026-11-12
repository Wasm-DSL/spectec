## Continued Phase 2: context-update lemmas + the seq-typing-inversion cluster

Re-checked the live GitHub branch first — still `a8b585cdb`, unchanged.

**`TypingLemmas.lean`'s context-update lemmas** (Tier B #5, 7 lemmas) — all
fully definitional or one-line: `upd_label_overwrite`,
`upd_label_is_same_as_append`, `upd_local_is_same_as_append`,
`upd_local_return_is_same_as_append`, `upd_return_is_same_as_append` are
all `rfl` (each `upd_*` is a plain record-field update, so composing or
restating them collapses definitionally); `upd_label_unchanged` is
`intro h; subst h; rfl`; `upd_label_unchanged_typing` is a one-line
corollary of it via `rw`.

**The `instrs_seq_typing_inversion`/`ais_seq_typing_inversion`/
`ais_composition_typing` cluster** (Tier B #6 — flagged in
`proof_prioritization.md` as "the single biggest land-mine already found
and fixed," and the highest-value remaining item not blocked by
`ai_principal_typing`) — ported the complete proof from a prior Lean
session's `spectec/test-lean/test-lean-claude/SeqTypingInversion.lean`
(`instrs_ok_nil_sub_gen`, `instrs_ok_nil_sub`, `instrs_ok_nil_refl`,
`instrs_ok_widen_in`, `instrs_ok_widen_out`, `instrs_ok_cons_gen`), then
re-derived the entire thing a second time for the administrative
(`Instrs_ok2`/store-threaded) setting since no prior version of that half
existed, and finally proved `ais_composition_typing` (generalizing from a
single head instruction to an arbitrary prefix) by induction, which had no
prior-session version at all.

This was the most debugging-intensive stretch of this whole project so
far. Real issues found and fixed, all via `lake build` feedback:
- `Instr_ok`/`Instrs_ok` are declared as a **mutual inductive** in
  `wasm2.0.lean`; using `induction h using Instrs_ok.rec with` without
  telling Lean what to do about `Instr_ok`'s 72 unrelated cases produces 72
  "alternative not provided" errors. Fixed by setting
  `(motive_1 := fun _ _ _ _ => True)` (trivializing the other mutual type)
  plus a trailing `| _ => intros; trivial` catch-all — a pattern the prior
  session's file already used, which I'd initially dropped by mistake.
- `Instr_ok2`/`Instrs_ok2` turned out to be a **3-way mutual inductive**
  together with `Expr_ok2` (not just 2-way, as I'd assumed from the
  non-administrative side) — needed both `motive_1` and `motive_3`
  trivialized. Also needed a full extra arity-debugging round: my first
  guess at the trivial motives' argument count was wrong (I assumed the
  store index counted toward the motive's arity; it doesn't — `store` is
  treated as a fixed shared parameter across the whole mutual family, not
  a per-case index), caught immediately by a precise Lean elaborator error
  spelling out the exact expected type.
- The store-indexed constructors also don't get a fresh pattern name for
  their leading `store` argument the way `context` does (confirmed
  earlier in bundle5 for a different lemma, re-confirmed here) — every
  `Instrs_ok2.rec`/`Instr_ok2`-derived case pattern in this cluster omits
  it.
- Two genuine algebra/logic bugs in my own first draft: a
  `resulttype_sub_trans`/`resulttype_sub_app` argument-order slip in two
  places (chaining subtyping facts through the wrong middle type), and a
  swapped-tuple-component bug in `ais_composition_typing`'s inductive step
  (used the *head* instruction's typing fact where the *rest*-of-the-list
  fact was needed, and vice versa) — both caught by `lake build`'s type
  errors, not guessed at.

**Verified**: full project `lake build` exits 0 with zero errors after all
fixes. Safety check re-run clean.

Current `sorry` tally: `HelperLemmas.lean` 28, `Subtyping.lean` 29,
`TypingLemmas.lean` 33 (down from 43), `TypePreservationPure.lean` 29,
`ExtensionLemmas.lean` 76, `TypePreservation.lean` 12.

## What's next

Per `proof_prioritization_addendum.md`'s corrected ordering, the remaining
easy Tier B items (`inst_match`-adjacent `construct_ais_*`/`construct_ai_*`
clusters, tiers 9/10) and the `ExtensionLemmas.lean` inversion-lemma tier
(#7) are next, before the genuinely hard Tier C blocker
(`instr_of`/`ai_principal_typing`'s ~50/57-case bodies).

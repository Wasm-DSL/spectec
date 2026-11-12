## 56 sorries closed, 83 → 27 — and `t_preservation` is proved

**Per-file**: `ExtensionLemmas.lean` 50 → **2**, `TypePreservation.lean` 8 → **3**,
`TypePreservationPure.lean` 10 → **7**, `HelperLemmas.lean` 15 → 15 (unchanged
count, but +6 new lemmas). `Subtyping.lean`/`TypingLemmas.lean` still 0.

**Of the 27 left, only 5 are genuine remaining work** — all in
`TypePreservationPure.lean` (`br_zero`, `br_succ`, `br_table_lt`, `br_table_ge`,
`return_label`). The rest: 5 deliberate mirrors of Rocq `Admitted`s, 2 signatures
that are unprovable as stated *and* dropped upstream (`Val_ok_store`,
`funcinst_same` — analysed in the triage doc), and the 15 dead `HelperLemmas`
`nat→N` lemmas.

**`t_preservation`** — the Rocq source's own "ultimate goal of project" — **is
proved**, along with every lemma on its critical path that is both provable and
inside the editable directory: `reduce_inst_unchanged`,
`t_preservation_vs_type'`, `t_preservation_vs_type`, `step_moduleinst`,
`Extend_store_moduleinst`, `Extend_store_ais`. `#print axioms` confirms its only
non-standard dependency is `sorryAx`, from the three Rocq-`Admitted` SIMD gaps
plus `Step_is_wf` (which is `sorry` in the *generated* `wasm2.0.lean`, outside
the directory I'm allowed to touch).

**What actually unlocked this** — three things, in order of leverage:

1. **Rocq's `Externaddr_invert_funcs`/`_tables`/`_mems`/`_globals` had no Lean
   counterpart at all.** bundle15's triage ("Template C") predicted porting them
   would drop ~9 lemmas a tier; in practice it unblocked ~30, cascading all the
   way to `Extend_store_ais`.
2. **bundle15's "`obtain` loses identifiers" mystery was a misdiagnosis.** Two
   unrelated facts were conflated: Lean can't dependently eliminate a hypothesis
   whose inductive *index* is an opaque term (`l[i]!`, `p.1`, `x.TYPE`), and
   separately, a constructor arg that unification assigns to an existing variable
   keeps its binder slot but silently loses your name for it. The general fix is
   to do each inversion once in a helper lemma over bare variables. All three
   lemmas flagged last bundle fell immediately; their doc comments are rewritten
   from FLAGGED to RESOLVED.
3. **Lean already generates the mutual recursor Rocq needs a hand-written
   `Scheme` for**, with the store as a *parameter* rather than an index — so
   `Extend_store_ais`, the hardest single entry in the triage, is a direct
   term-mode application and went through first try.

Also built "Template B" (the `List.modify`↔zip bridge the `construct_*` family
needed) in `HelperLemmas.lean`, which closed all 7 `construct_*` lemmas including
both `_grow` ones.

**Documents** (new copies in `bundle16/user_requested_documents/`, prior bundles
untouched): `extension_lemmas_triage_v2.md`, `proof_dependencies_v5.md`,
`proof_prioritization_v6.md`, and — per your request —
`insights_for_next_turn.md`, which is deliberately long: it covers the
opaque-index inversion rule, an empirical table of `cases` binder-slot counts for
every inductive I touched, the `dependent induction` encoding, the mutual-recursor
recipe, the zip-based `Forall₂` do's and don'ts, a list of dead ends not to
repeat, and step-by-step routes for the remaining 5. `NOTES.md` updated in place.

`lake build` clean. Safety check clean throughout — and I verified the two
out-of-target git entries (`spectec/test-lean/todaywasm*.lean`) are byte-identical
before and after my work, i.e. pre-existing and not mine.

Three things worth your attention, flagged rather than changed:
`Extend_store_datainsts'`'s Lean signature quietly diverges from Rocq's
(`Forall` with `datatype.OK` hard-coded vs Rocq's `Forall2 … aa ts`);
`construct_meminsts_grow` still hard-codes the page-count max as present where
Rocq's is a genuine `Option` (and is now *proved* at the narrower signature, so
generalising it later is real work); and `table_grow_table_extension` takes
`Option uN` where its memory sibling takes `Option Nat`.

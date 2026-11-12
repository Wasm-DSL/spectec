## Status update

I've made major progress on the Rocq→Lean translation since the crash. Quick recap:

**Research phase (complete):** Fully digested all 6 Rocq lemma files (`helper_lemmas.v`, `subtyping.v`, `typing_lemmas.v`, `type_preservation_pure.v`, `extension_lemmas.v`, `type_preservation.v`) plus the core `wasm.v` and the prior Lean attempt in `spectec/test-lean/`. All digests are saved to `spectec/src/test-lean-claude/claude-logging/for-claude/` for any future session to pick up cold.

**Translation phase (Phase 1 — skeleton — complete):** Created 6 new Lean files, one per Rocq lemma file, with **every lemma signature stated and matched field-for-field against the Rocq original**. The whole project builds cleanly:

| Lean file | Ports | Declarations |
|---|---|---|
| `HelperLemmas.lean` | `helper_lemmas.v` + `axioms.v` | ~48 |
| `Subtyping.lean` | `subtyping.v` | ~35 |
| `TypingLemmas.lean` | `typing_lemmas.v` | ~50 |
| `TypePreservationPure.lean` | `type_preservation_pure.v` | 29 |
| `ExtensionLemmas.lean` | `extension_lemmas.v` | ~55 |
| `TypePreservation.lean` | `type_preservation.v` (capstone, incl. top-level `t_preservation`) | 13 |

Two honest caveats, both logged clearly in-file: (1) `TypingLemmas.lean`'s `instr_of` and `ai_principal_typing` are large per-instruction-case definitions still stubbed with `sorry` bodies, not just stubbed proofs — real remaining work; (2) a handful of lemmas are deliberately left `sorry` because the *original Rocq proof itself* is incomplete there (all SIMD-related, plus one control-flow case) — faithfully mirrored, not a bug.

Safety checks confirm nothing outside `spectec/src/test-lean-claude/` was touched throughout. Full technical notes and a prioritized Phase-2 TODO list (which proofs to fill in first, including several already proven in prior sessions that can likely be reused) are in `claude-logging/for-claude/NOTES.md`.

I'll continue into Phase 2 (filling in real proofs) now unless you'd like to redirect me.
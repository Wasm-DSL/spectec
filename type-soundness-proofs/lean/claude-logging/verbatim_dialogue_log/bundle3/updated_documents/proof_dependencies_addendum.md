# Addendum to `bundle2/user_requested_documents/proof_dependencies.md`

Do not edit that file. This addendum records what the 2026-09-23 resync (see
`resync_impact_report.md`) changes about the dependency graph.

## The file-level chain for the 6 already-ported files is unaffected

`HelperLemmas` → `Subtyping` → `TypingLemmas` → `TypePreservationPure` →
`ExtensionLemmas` → `TypePreservation` remains a correct build order. Nothing
in the resync changes which of these files depends on which — only their
*content* (see `resync_impact_report.md` §3 for the per-file deltas: renamed
extension-lemma names, closed SIMD gaps in the two preservation files, a few
added/removed helper/typing lemmas).

## New: `type_progress.v` is a 7th file, parallel to Preservation, not after it

Confirmed by its own `Require Import` list: `wasm`, `helper_lemmas`,
`helper_tactics`, `typing_lemmas`, `extension_lemmas`, `subtyping`, `axioms`.
**No import of `type_preservation` or `type_preservation_pure`.** So the
correct picture is:

```
                              ┌── TypePreservationPure → TypePreservation
HelperLemmas → Subtyping → TypingLemmas ─┤
                              └── ExtensionLemmas ──┘   (Extension feeds both
                                                          Preservation and,
                                                          separately, Progress)
                                        │
                                        └── TypeProgress   (needs TypingLemmas +
                                                             ExtensionLemmas +
                                                             Subtyping + Axioms,
                                                             NOT Preservation)
```

This corrects `proof_prioritization.md` Tier H #37's assumption that Progress
would need "everything `type_preservation.v` needs, plus its own machinery."
It doesn't — it needs a strict subset of Preservation's dependencies (no
transitive need for anything Preservation-specific), plus its own large body
of new lemmas (canonical-forms/`invert_typeof_*`, br/return label-finding,
numeric-operator totality — see `digest_type_progress.md`).

**Practical consequence**: once `HelperLemmas`/`Subtyping`/`TypingLemmas`/
`ExtensionLemmas` are solid, `TypePreservationPure`→`TypePreservation` and
`TypeProgress` can be worked on **in parallel** (by this session across
turns, or even by two separate efforts) rather than strictly sequentially.
This matters for scheduling future work, especially given the "may be
interrupted" operating constraint this whole project runs under.

## Within-file dependency notes for the new content

- The ~50 new vector-instruction lemmas added to `TypePreservationPure`'s
  Rocq source (`Step_pure__v*_preserves` family) each depend on their
  corresponding `ais_v*_typing_inversion` lemma, mirroring the existing
  non-vector `Step_pure__*_preserves` ↔ inversion-lemma pattern already in
  this file — no new *kind* of dependency, just more instances of the
  existing shape. Same for `TypePreservation`'s new vload/vstore lemmas.
- Within `type_progress.v` itself (see `digest_type_progress.md` for the
  full layer breakdown): layer 1 (list plumbing) and layer 2
  (`typeof`/`invert_typeof_*`) have no internal blockers; layer 4 (numeric
  totality) needs layer 2; layer 3 (br/return machinery) is needed before
  `t_progress_e`; `call_indirect_progress` and `t_progress_be` need layers
  1–4; `t_progress_e` needs `t_progress_be` + layer 3; `t_progress` needs
  `t_progress_e`.

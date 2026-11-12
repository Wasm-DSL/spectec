## Continuing Phase 2

Re-checked the live GitHub branch first (`gh api
repos/Wasm-DSL/spectec/branches/rocq-backend-proof`) — still `a8b585cdb`, no
new commits since bundle3, so no re-sync was needed before continuing.

Per bundle3's `proof_prioritization_addendum.md`, the first item on the
revised ordering was a rename/reshape pass over `ExtensionLemmas.lean`
(everything else was blocked on it or would have compounded on stale
names). This turned out to be substantially bigger than a pure rename: I
diffed every declaration in the current `extension_lemmas.v` against what
this project's `ExtensionLemmas.lean` was built against, and found that
beyond the wholesale `store_extension_*` → `Extend_store_*`/`extend_*_refl*`
rename, roughly 25 lemmas were also **reshaped** — new `wf_*` premises, and
a move from a `Forall₂`/existential-split conclusion style to an
index-based `holds_upto P n` idiom that mirrors a definition Rocq's own
`wasm.v` introduced (`holds_upto P n := Forall P (iotaN 0 n)`, exactly
`Forall P (List.range n)` here). `minst_invert_funcs`/`_tables`/`_globals`/
`_mems` were also genuinely generalized to use the unified `Externtype_sub`
relation instead of exact-equality or bespoke per-kind subtyping — a real
semantic change, not cosmetic.

I rewrote `ExtensionLemmas.lean` in full against the current source:
introduced the `holds_upto` definition, renamed every `_refl0`-style lemma
(pure renames, same math — `func_extension_refl0` → `extend_funcinst_refl_0`
etc.), added the 6 new lemmas the current source has that we didn't
(`limits_sub_refl`/`_trans`, `externtype_sub_refl`/`_trans`,
`externtype_global_eq`/`_func_eq`, `Extend_store_refs'`), and restated every
lemma whose shape changed (the `extend_*_refl` list-lifted family,
`se_invert_*`, the 7 per-instruction extension-fact lemmas, all 8
`addrs_*`/`addrss_*_extension` lemmas, `construct_tableinsts_grow`/
`construct_meminsts`/`construct_meminsts_grow`) to match. `Val_ok_store` and
`funcinst_same` are flagged (no matching upstream declaration found under
any obvious name) rather than deleted, since nothing else in this project
references them. Also added the 7 new `axioms.v` axioms to
`HelperLemmas.lean` (all vector/SIMD or inverse-bijection facts — the
existing two, `nbytes_len`/`ibytes_len`, are byte-for-byte unchanged
upstream and needed no changes).

This was a signature-only pass, matching how this project originally
scoped "Phase 1" work — every lemma that was `sorry` before is still
`sorry`, just against a corrected signature. No proofs were attempted this
turn.

**Verified**: full project `lake build` from
`spectec/src/test-lean-claude` completes with exit code 0 and zero errors
(only the expected `sorry`/pre-existing-file warnings) after this pass — I
hit one self-inflicted ordering bug along the way (used `forall_range_refl`
before its own definition when I first laid out the file) and fixed it by
moving the three `forall_range_*` helper lemmas earlier; confirmed clean
after the fix. Safety check re-run and clean — only the same pre-existing
untracked scratch files outside `spectec/src/test-lean-claude/` that have
been present since this conversation's opening `git status`.

Updated `claude-logging/for-claude/NOTES.md` in place with a dated summary
of this pass and what's next (per the project's own convention of treating
that file as living documentation, not part of the versioned dialogue log).

## What's next

Per `proof_prioritization_addendum.md`'s revised ordering, now that the
rename/reshape pass is done: Tier B's corrected list (starting with
`HelperLemmas.lean`'s tier-0 cluster, minus the lemmas that no longer exist
upstream), then Tier C/D, with Tier E2 (the newly-real vector preservation
lemmas) and Tier I (`type_progress.v`) available to run in parallel once
the earlier tiers are in reasonable shape. I'll continue into actual proof-
filling next unless redirected.

## Comments updated across the seven proof files; no code changed

I read all 21 bundles and the living notes first, and I'm following the same standing rules (safety boundary, safety checks, verbatim logging). This exchange is logged as bundle22.

**What changed**
- I changed 626 of the 1,211 comments in `HelperLemmas`, `Subtyping`, `TypingLemmas`, `TypePreservationPure`, `ExtensionLemmas`, `TypePreservation` and `TypeProgress`.
- **Rocq citations** now point at the current `spectec/test-rocq/theories`, which is upstream `rocq-backend-proof` `6582b3a39` and still the live tip.
  - About 300 citations were stale, pinned to the old `5b03ae067` checkout or to `95c256c2c`.
  - `TypeProgress`'s "bullet at line N" citations were re-pointed using a line-by-line diff between the two Rocq revisions. I checked that each one lands on the matching Rocq bullet.
  - Lemmas that upstream has removed are cited at their old revision and marked "since removed upstream".
- **Status and history**: I removed claims that are no longer true:
  - "Phase 1 … proofs `sorry`" and "MAJOR TODO: bodies are `sorry`";
  - "SIMD excluded" and "mirrors Rocq `Admitted`";
  - FLAGGED/RESOLVED notes, resync narration, and `bundleN`/date tags.

  The headers now say every file is fully proved. Pointers to documents in `claude-logging/` are kept.
- **Comments that were simply wrong**, now fixed:
  - `construct_ais_vals` described Rocq's right-induction (`last_ind`). The Lean proof uses left induction.
  - The `TypePreservationPure` header said SIMD was excluded, but the file has a SIMD section.
  - `wf_store_parts` named the wrong hypothesis (`Store_ok` instead of `wf_store`).
  - The `vunop`/`vtestop` case lemmas said Rocq has no bullet for them. It has one for each.
  - `Extend_store_datainsts'` said `Datainst_ok` is always true. It now has a `< 2^32` bound. The comment now also records that the lemma uses `Forall … datatype.OK`, where Rocq uses `Forall2 … aa ts`.
  - Smaller ones: `Instr_ok` now has 73 rules, not 72; two "above"/"below" references were backwards; the old name `store_extension_vals` is now `Extend_store_vals`; the Ltac macros the comments named are defined in `typing_lemmas.v` and two other proof files, not `helper_tactics.v`.
- **Your `Val_ok_store` deletion**: the doc comment you left behind had no declaration after it, which is a parse error in `ExtensionLemmas.lean`. I turned it into `--` lines in your `DELETED BECAUSE NOT USED` style. I also updated the Rocq citations under your other `DELETED` markers.

**Left alone**
- Every `TODO FROM USER`, and your own comments inside `t_preservation`.
- `wasm2.0.lean`. Its hand-written comments are accurate, and the bundle21 hand-edits patch relies on them as markers. `ExtendedDeriveDecEq.lean` and `OLD_wasm2.0.lean` are also unchanged.

**Checks**
- **Only comments changed.** After every edit batch I compared each file, with comments stripped, against the state at session start, and they are identical.
- Every comment parses in Lean, and every doc comment still sits on a declaration.
- **I did not run `lake build`.** The machine had about 1.2 GB free, swap was full, and your editor had three Lean workers open. To confirm, run `lake build` in `spectec/src/test-lean-claude`. Docstrings are stored in the compiled files, so it will rebuild from `HelperLemmas` onward.
- The safety check found nothing changed outside `spectec/src/test-lean-claude`.

**Also worth knowing**
- Your preservation walkthrough (`spectec/test-lean/temp_zy_learning/.../wasm-type-preservation-walkthrough`) quotes doc comments verbatim, so some of its quotes no longer match the source. I didn't touch it, since it is outside the directory.
- My changes alone are in `bundle22/user_requested_documents/bundle22_comment_updates.patch`. Your uncommitted deletions are not in it. I tested that applying it reproduces the current files exactly.
- `NOTES.md` and `SUMMARY.md` have a bundle22 entry.

Written for: you. The two reports linked below are written for you and for anyone checking the proofs by hand.

## Preservation audited and sound; progress ported and proved except Rocq's two false cases

**Task 1: done.** The 16 unused `sorry`s are marked `-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED`. None is referenced anywhere.

**Task 2, preservation: it is meaningfully complete and makes sense.** Full report, including how to check it by hand: `bundle20/user_requested_documents/preservation_audit_report.md`.
- `t_preservation` states the same thing as Rocq's `t_preservation` and Isabelle's `preservation`.
- The generated Lean and Rocq models match one-to-one: same constructors, and the same premises across all 346 shared relations. Every zip-based `Forall₂` on the path comes with a length premise.
- Its signatures match Rocq's, apart from the documented length deviations.
- It is not vacuous: `preservation_nonvacuity_witness.lean` is a Lean-checked example where its assumptions hold.
- It depends on no project axiom. Its only `sorry`s are the 33 generated facts that Rocq also leaves `Admitted`.

The audit found four real problems. A second agent independently confirmed each one.
- **(A) Fixed: two ported axioms were contradictory.** `ibytes_len'` and `ibytes_len''` each implied `False`; I checked this in Lean. They read Rocq's `|x| = q` as an exact equation, but Rocq rounds `q` down. I restated them with `rat_to_nat`, which rounds the same way. Nothing had used them.
- **(B) Upstream, your call.** SpecTec's `middlend/sideconditions.ml` pulls an "address list is non-empty" check out of a loop in `Moduleinst_ok`. As a result, no `$invoke` configuration is ever `Config_ok`. This affects Lean, Rocq and Isabelle equally.
- **(C) Upstream, your call.** The generated `Globaltype_ok` only accepts mutable globals; the spec allows either. Again, all three backends.
- **(D) Fixed.** Four unused `s_invert_*` lemmas were trivially true in Lean, because the zip-based `Forall₂` doesn't force equal lengths. They now state the length.

B and C narrow what preservation, and now progress, cover. They don't make either theorem false.

**Task 3, progress: ported and proved, apart from the same two cases Rocq leaves open.** The new `TypeProgress.lean` is 8,005 lines and is in the lakefile.
- **Signatures first.**
  - All 223 Rocq declarations are ported, or noted in place as not needed (Ltac and Scheme declarations, plus 2 lemmas that become meaningless in Lean).
  - Six agents translated the ~190 lemma statements and a separate agent checked each batch against Rocq. One problem came up, and it was fixed.
  - The 90 case lemmas for `t_progress_be` and `t_progress_e` were generated directly from the induction principles Lean derives, so they fit by construction.
- **Proofs.**
  - All 280 proof obligations are proved, porting the Rocq proofs case by case. None of the proofs changed any statement.
  - The only `sorry`s left are the two subcases Rocq `admit`s, because they're false under the current spec: `VLOAD (SHAPE 64 X 1)` and `F32→I16 TRUNC_SAT` vector conversion. Lean now proves both are stuck.
- **What `t_progress` rests on.**
  - `sorry`s: those 2 subcases, `Step_read_is_wf`, and 56 generated numeric well-formedness facts. Rocq leaves all 56 `Admitted`.
  - Axioms: 17 project axioms, each mirroring one in Rocq's `axioms.v`.
- Deviations from Rocq are listed in `progress_port_deviations.md`; the full status is in `progress_port_status.md`. The main design choices:
  - each Rocq bullet became its own case lemma;
  - `TypeProgress.lean` imports `TypePreservation` to reuse Lean-only helpers;
  - 5 length conditions were added where Lean's `Forall₂` needs them;
  - the two decidability lemmas became `def`s.
- `HelperLemmas.lean` gained Rocq's 12 progress-only axioms and `Forall2_size`/`Forall2_size2`.
- One Lean-only preservation helper was renamed so the Rocq progress lemma `wf_config_frame` keeps its name.

**Decisions for you**
1. The two stuck vector instructions.
2. The 2^32 corner case in bulk memory operations (`Step_read_is_wf`).
3. B and C above: whether to fix them upstream.
4. Whether `TypeProgress.lean` importing `TypePreservation` is acceptable. Rocq's progress file doesn't import preservation.
5. Optionally, a documentation cleanup pass. 166 of the Rocq line citations in comments are stale.

`lake build` is clean (3006 jobs). Remaining `sorry`s:
- `HelperLemmas`: 15 and `ExtensionLemmas`: 1, all marked for deletion;
- `TypeProgress`: 2, the known-false subcases;
- every other hand-written file: 0;
- `wasm2.0.lean`: 63, exactly Rocq's `Admitted` set.

Every safety check, including those run by agents, verified nothing changed outside `spectec/src/test-lean-claude`. The whole exchange is logged in bundle20, including the usage-limit interruption, your two mid-turn questions with my replies, and every agent's log (indexed in `agent_logs/README.md`). `NOTES.md`, `SUMMARY.md` and `is_wf_theorems.md` are updated, and `insights_for_next_turn.md` records the new techniques and pitfalls.

If it would help reviewers, I can publish the preservation report as a private page you can share.

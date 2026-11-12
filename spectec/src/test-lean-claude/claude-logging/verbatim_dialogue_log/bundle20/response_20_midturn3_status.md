# Interim status reply to mid-turn input 3 (verbatim)

The turn is long for two reasons. First, the account usage limit killed the first audit wave
(11 agents), and the session sat idle from about 13:30 until your 18:47 "continue". Second, the
progress port is big: Rocq's `type_progress.v` is 6,159 lines, and `t_progress_be` alone is 2,427.

**Done**
1. **Task 1.** The 16 unused `sorry`s are marked `TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED`.
2. **Preservation audit: complete.** The report and a hand-checking guide are in
   `bundle20/user_requested_documents/preservation_audit_report.md`. Verdict: preservation is
   complete and makes sense.
   - Its statement equals Rocq's and Isabelle's.
   - It is non-vacuous; the witness is machine-checked.
   - It rests only on the 33 generated `sorry`s that Rocq also leaves `Admitted`.

   The audit found four significant problems, all independently verified:
   - (A) Two ported axioms (`ibytes_len'`, `ibytes_len''`) were inconsistent and derived `False`.
     **Fixed**; nothing had used them.
   - (B) No `$invoke` configuration is ever `Config_ok`. A SpecTec middle-end bug adds a
     non-emptiness premise to `Moduleinst_ok`.
   - (C) `Globaltype_ok` admits only mutable globals.

     B and C affect Lean, Rocq and Isabelle alike. They narrow what preservation covers but don't
     break it, so they are yours to fix upstream.
   - (D) Four unused `s_invert_*` lemmas were vacuous under the zip-based `Forall₂`. **Fixed.**
3. **Progress signatures: done.** The new `TypeProgress.lean` (in the lakefile) has:
   - the 15 definitions;
   - all ~190 lemma statements, translated, independently audited against Rocq, with 1 fix;
   - 90 `t_progress_be`/`t_progress_e` case lemmas generated mechanically from Lean's own
     recursors.

   `t_progress_be`/`t_progress_e` are already assembled from those cases. The deviations are
   listed in `progress_port_deviations.md`.
4. **Progress proofs: in progress.** So far 42 of 280 targets are proved and validated in a scratch
   merge, including the top-level `t_progress` and `Instr_ok_Instrs_ok`.

**Running now:** the proof workflow. 4 of 43 batches are done and 3 are running. Left: 9
helper-lemma batches and all 27 case batches (the 90 instruction cases), 3 agents at a time.

**Left to do**
1. Finish the remaining proof batches. Rough estimate: 3–5 more hours. The case batches are the
   hard part. Two subcases (`VLOAD SHAPE 64x1` and the `F32→I16 TRUNC_SAT` vcvtop) are false as
   the spec stands. They will stay `sorry`, as they are `admit`ted in Rocq.
2. Merge the proofs into `TypeProgress.lean`, run a full build and an axioms check, and retry
   whatever failed.
3. Write the final documents: progress status, updated NOTES/insights, `response_20.md`, model
   info, and a final safety check.

Everything so far is built, checkpointed and safety-checked. If you'd rather stop earlier, say
so and I'll merge whatever is proved at that point and write it all up.

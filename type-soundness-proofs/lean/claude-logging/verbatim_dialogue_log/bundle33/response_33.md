# Response 33 (verbatim)

---

Written for: you. The report is also meant for later sessions.

**The proof is repaired.** All nine modules compile against the new `wasm2.0.lean` with 0 errors and 0 `sorry`, and no theorem depends on `sorryAx`.

**What changed: 17 lines in 4 modules**
- `TypingLemmas`: I deleted the two match arms on the removed `admininstr.EXTEND`, in `instr_of` and `ai_principal_typing`, and renumbered 3 constructor references.
- `TypePreservationPure` (2 lines), `TypePreservation` (2) and `TypeProgress` (8): renumbered constructor references only.
- Every rename is `instr_case_K`/`admininstr_case_K` → K−1 for K ≥ 20, the same shift as in bundle32. Each was chosen by which instruction the constructor is about, not by arithmetic.
- All 17 were necessary: put back any one of them, and Lean reports an error at that line.
- Not touched: `wasm2.0.lean`, `OLD_wasm2.0.lean`, `ExtendedDeriveDecEq`, `HelperLemmas`, `Subtyping` and `ExtensionLemmas`.

**Checks** (fresh build of the installed files, in the scratchpad)
- The build logs are identical to the old ones once line numbers and timings are stripped, including the same 171 warnings.
- Every user-level theorem has the same axioms as before. `t_preservation` has 35 and `t_progress` 74.
- The `Inhabited`-default audit finds 0 of 5,496 theorems needing a default. I also gave it a positive control: two scratch theorems that do read a default. It caught exactly those two, so the zero means something.

**The report:** `claude-logging/verbatim_dialogue_log/bundle33/user_requested_documents/old_vs_new_diff_report.md`
- **Text.** 211 lines of OLD differ from NEW, and every one is accounted for:
  - 7 deleted lines that mention `EXTEND`;
  - 173 constructor renumberings: 102 in the generated model, 56 in the model's proofs and 15 in the proof modules;
  - 31 generated comments whose spec position moved up one line.
- **Constructs and bytes.** No top-level construct was added, removed or reordered. 53 have changed text, all listed. At the byte level nothing else changed: encoding, line endings and final newlines are the same.
- **Lean level.** I compared every declaration of both builds: 12,818 vs 12,787.
  - No user-level theorem, definition or type changed its statement.
  - Removed: only `EXTEND`, its well-formedness cases, and declarations Lean generates automatically.
  - The inductive types' structure differs only by the removed constructor and the resulting shift of later constructor indices.
- **Changed proof terms.** 115 theorems and 5 definitions have a different proof term, mostly without a source change. A probe shows these are exactly the user-level declarations whose terms refer directly to a declaration whose type changed or that is new: 120 of 120, and none of the 2,527 unchanged ones.
  - In practice that means a case eliminator of the four inductives, or `ai_principal_typing`'s matcher.
- **Evidence of necessity.** All 56 renames in the model's proofs have direct evidence that they were needed:
  - bundle32's compile of the unrenamed copy;
  - for 13 lines that compile never reached, a new compile that reverts only them and gets one error on each.
- **Appendices.** They give every changed line in full text, the full md5 sums, and how each verifier finding was handled.

**`temp_port_reference`** (your mid-turn suggestion). I had used it only for a final byte-for-byte comparison, so I went through its records too. They agree with mine on every check:
- the same 73 edits;
- the same 43 removed and 12 added declarations;
- the same warnings, the same axioms for four headline theorems, and the same audit result;
- the same five stale comments.

It also prompted the audit's positive control. One of its caveats is out of date: it says the generated `Step_*` statements were never shown false with a Lean witness, but bundles 23 and 29 did.

**Verification of the report.** Independent read-only readers checked versions 1 to 3 in three rounds and raised 77 points. None found an error in the repair or in the line accounting.
- The points were about precision and completeness: one miscount in an appendix, an over-broad necessity column, and wording that claimed more than was checked.
- They led to the cause probe, the inductive-metadata comparison, the byte-level facts and the full-text appendix.
- All 77 are addressed in version 4, as Appendix E records. No fourth reader has checked the version 4 fixes.

**Worth knowing**
- **Pre-existing, unchanged by this port:** `Step_read_is_wf` and `Step_is_wf` are still the bundle29 re-statements, with the extra `Store_ok` premise and the split configuration. So "zero `sorry`" covers 87 of the 89 generated theorems as generated, plus those two in the weaker form. Their generated forms were shown false in bundles 23 and 29; that witness wasn't kept, so I didn't re-run it on the new model.
- **Stale comments:** five comments in `TypingLemmas` still say `instr` has 68 constructors (now 67). Six line-number citations of `wasm2.0.lean` in proof-module comments were already wrong before and still are. I left them alone. Say if you want them updated.
- **`lake build`:** I didn't run it. Neither state has a Lake build in the repo; the next build will recompile `wasm2.0` and the seven proof modules.
- **Safety:**
  - Every check found changes only in the four proof modules and my new log files, apart from `spectec/temp-wasm-3/scrap.md`. That is your own notes file, which you edited several times during the turn. It's documented in `safety-checks/note-20261111T181000Z-bundle33-user-scrap-edit.md` and left alone.
  - Final check: `claude-logging/safety-checks/check-20261111T192751.491811167Z-bundle33-final-447013.txt`.

If you'd like to read the report in a browser, I can publish it as a private page.

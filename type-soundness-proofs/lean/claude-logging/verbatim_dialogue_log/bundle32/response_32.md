# Response 32 (verbatim)

---

Written for: you. `deviations_in_copying.md` is also meant for later sessions.

## Your expectation holds, and `wasm2.0.lean` is updated

**The check (read-only, done first)**
- `OLD_wasm2.0.lean` is byte-identical to HEAD's `wasm2.0.lean`, the bundle29 model with all proofs.
- The new `wasm2.0.lean` is byte-identical to what the HEAD generator produces. I rebuilt the generator in the scratchpad to check this.
- **EXTEND's removal is the only change.** I ran the same generator on the spec with only the `EXTEND numtype n` line put back, and it reproduced the old generated base byte for byte. So the merge's other generator changes have no effect on 2.0: the ImproveIds fix, the Sideconditions let-reordering and DefToRel's `hint(axiom)`.
- In the model, the removal deletes 5 lines and renumbers the later `wf_instr`/`wf_admininstr` constructors: `*_case_K` becomes `*_case_{K−1}` for K ≥ 20. No top-level construct appears, disappears or moves.

**The update**
- **What was copied:**
  - the proofs of all 89 generated theorems;
  - both hand edits: `Step_read_is_wf` and `Step_is_wf` re-stated below `Store_ok` with the `Store_ok` premise, and their originals commented out;
  - all 92 `HELPER LEMMA CREATED BY CLAUDE` lemmas, each at its old position.

  This was a mechanical 3-way merge, not hand editing.
- **Top-level constructs:** all 897 have the same names in the same order as in `OLD_wasm2.0.lean`.
- **`sorry`:** there are none in code. The word still occurs twice, in the commented-out generated originals (`--   sorry`), exactly as in OLD. A plain `grep -c sorry` will therefore report 2.
- **Build:** it compiles with 0 errors. The 89 warnings are the same unused-variable warnings OLD has.
- **Axioms and defaults:** every theorem has the same axioms as before, none depends on `sorryAx`, and none needs an `Inhabited` default.

**Deviations: 56 lines, all of one kind**
- Each one renames a constructor reference in a proof, `admininstr_case_K` → `admininstr_case_{K−1}`. Left alone, an old name would point at a different instruction. For example, old 20 (VCONST) would become VVUNOP, and old 73 (TRAP) would no longer exist.
- Where they are:
  - `Step_read_is_wf` 28, `Step_pure_is_wf` 14, `Step_is_wf` 10;
  - 4 helpers, 1 line each.
- No statement changed, and no variable names needed changing.
- The full list, line by line, is in `claude-logging/verbatim_dialogue_log/bundle32/user_requested_documents/deviations_in_copying.md`.

**Verification**
- I had three independent read-only agents each try to refute one claim: that the copy is complete, that the names and order match, and that the deviation log is complete. None could.
- The result is byte-identical to the trial port in `spectec/src/temp_port_reference/`. A session that isn't in this log made that port with a different method. I built mine first and compared afterwards.

**Ready for repair (nothing fixed)**
- A static scan of the downstream modules finds 17 lines to change:

  | module | lines | what |
  |---|---|---|
  | `TypingLemmas` | 5 | 2 `admininstr.EXTEND` match arms to delete, 3 renames |
  | `TypePreservationPure` | 2 | renames |
  | `TypePreservation` | 2 | renames |
  | `TypeProgress` | 8 | renames |

  Details are in `bundle32/evidence/outputs/downstream_static_scan.txt`.
- The trial port folder also has patches for those modules, which it says compile. I haven't checked that.
- I didn't run `lake build`, since it writes into `.lake/build`. Expect the downstream modules to fail until those lines are fixed.

**Safety and logging**
- The final check found that only `wasm2.0.lean` and new files under `claude-logging/` changed. The report is `claude-logging/safety-checks/check-20261111T115006.417535838Z-bundle32-final-370836.txt`. The agents' start and end checks were all OK too.
- This exchange is logged in `bundle32/`, with the tools and outputs in `evidence/`.
- I didn't update `NOTES.md` or `SUMMARY.md`; they haven't been updated since bundle22. Say if you want that.

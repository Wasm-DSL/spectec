# audit-hygiene: Lean-internal trust and hygiene audit (bundle20 preservation audit)

Agent label: `audit-hygiene` (subagent spawned by the bundle20 workflow orchestration script).
Date: 2026-10-05.

## Task (one paragraph)

Scan all eight Lean files in `spectec/src/test-lean-claude/` (`wasm2.0.lean`,
`ExtendedDeriveDecEq.lean`, `HelperLemmas.lean`, `Subtyping.lean`, `TypingLemmas.lean`,
`TypePreservationPure.lean`, `ExtensionLemmas.lean`, `TypePreservation.lean`) plus
`lakefile.lean` for trust-expanding or suspicious constructs (`sorry`, `admit`, `axiom`, `opaque`,
`native_decide`, `decide`, `implemented_by`, `@[extern`, `unsafe`, `partial def`, `ofReduceBool`,
`trustCompiler`, every `set_option`, custom `macro`/`syntax`/`elab`/`notation`/`macro_rules`,
suspicious `instance`s); for each of the 11 `axiom`s in `HelperLemmas.lean`, find its Rocq
counterpart, compare statements, decide whether the functions it constrains are `opaque` or real
`def`s in the current `wasm2.0.lean`, check truth (if real defs) or joint satisfiability (if opaque),
and check for conflicts with proved theorems; assess whether the 12 further Rocq axioms the progress
port will need can be stated consistently; list every `opaque` in `wasm2.0.lean` with its body;
assess `ExtendedDeriveDecEq.lean`; and confirm that the 63 remaining `sorry` theorems in
`wasm2.0.lean` are exactly the `*_is_wf` theorems that are `Admitted` in Rocq's `wasm.v`. Read-only:
no Lean runs, no repo writes except this log.

## Safety check at START

### First run (13:27:54 local): spurious `DIFFERENCE FOUND` (false positive, diagnosed below)

My very first action was the start safety check. It printed `DIFFERENCE FOUND`. Verbatim output
(the 256 `<` lines are the full filtered baseline; the new side was empty):

<details><summary>Verbatim output of first run (261 lines; click to expand)</summary>

```
safety check [audit-hygiene] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
grep: spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt: binary file matches
DIFFERENCE FOUND (lines outside spectec/src/test-lean-claude differ from baseline):
grep: spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt: binary file matches
1,256d0
< --- git status (porcelain) ---
<  M spectec/test-lean/todaywasm2.0.lean
<  D spectec/test-lean/todaywasm3.0.lean
< ?? Irreducible.lean
< ?? Irreducible2.lean
< ?? PrintFalse.lean
< ?? specification/bleh/
< ?? spectec/BEQ_INHABITED_RELD_FIX_PLAN.md
< ?? spectec/FETCH_HEAD
< ?? spectec/check_wasm2.0.lean
< ?? spectec/check_wasm2.0.v
< ?? spectec/check_wasm2.0_OLD.lean
< ?? spectec/diegochanges.diff
< ?? spectec/diegowasm2.0.lean
< ?? "spectec/diegowasm3.0 copy.lean"
< ?? spectec/diegowasm3.0.lean
< ?? spectec/oldwasm2.0.lean
< ?? spectec/src/temp_zy_dev/scraps.md
< ?? spectec/temp-wasm-3/email_stuff.md
< ?? spectec/test-rocq/_opam/
< ?? spectec/test-rocq/echo
< ?? spectec/test-rocq/rocq-temp.export
< ?? spectec/test-rocq/test-rocq.opam
< ?? spectec/test-rocq/upd_label_unchanged_typing_verified_walkthrough.md
< ?? spectec/wasm1.0_00-elab.il
< ?? spectec/wasm1.0_01-ite.il
< ?? spectec/wasm1.0_02-let-intro-mech.il
< ?? spectec/wasm1.0_03-typefamily-removal.il
< ?? spectec/wasm1.0_04-remove-indexed-types.il
< ?? spectec/wasm1.0_05-totalize.il
< ?? spectec/wasm1.0_06-else.il
< ?? spectec/wasm1.0_07-else-simplification.il
< ?? spectec/wasm1.0_08-uncase-removal.il
< ?? spectec/wasm1.0_09-sub-expansion.il
< ?? spectec/wasm1.0_10-pattern-simp.il
< ?? spectec/wasm1.0_11-sub.il
< ?? spectec/wasm1.0_12-definition-to-relation.il
< ?? spectec/wasm1.0_13-sideconditions.il
< ?? spectec/wasm1.0_14-alias-demut.il
< ?? spectec/wasm1.0_15-improve-ids.il
< ?? spectec/wasm1.0_16-single-pattern-match.il
< ?? spectec/wasm1.0_ast_00-elab.il
< ?? spectec/wasm1.0_ast_01-ite.il
< ?? spectec/wasm1.0_ast_02-let-intro-mech.il
< ?? spectec/wasm1.0_ast_03-typefamily-removal.il
< ?? spectec/wasm1.0_ast_04-remove-indexed-types.il
< ?? spectec/wasm1.0_ast_05-totalize.il
< ?? spectec/wasm1.0_ast_06-else.il
< ?? spectec/wasm1.0_ast_07-else-simplification.il
< ?? spectec/wasm1.0_ast_08-uncase-removal.il
< ?? spectec/wasm1.0_ast_09-sub-expansion.il
< ?? spectec/wasm1.0_ast_10-pattern-simp.il
< ?? spectec/wasm1.0_ast_11-sub.il
< ?? spectec/wasm1.0_ast_12-definition-to-relation.il
< ?? spectec/wasm1.0_ast_13-sideconditions.il
< ?? spectec/wasm1.0_ast_14-alias-demut.il
< ?? spectec/wasm1.0_ast_15-improve-ids.il
< ?? spectec/wasm1.0_ast_16-single-pattern-match.il
< ?? spectec/wasm2.0_00-elab.il
< ?? spectec/wasm2.0_01-ite.il
< ?? spectec/wasm2.0_02-let-intro-mech.il
< ?? spectec/wasm2.0_03-typefamily-removal.il
< ?? spectec/wasm2.0_04-remove-indexed-types.il
< ?? spectec/wasm2.0_05-totalize.il
< ?? spectec/wasm2.0_06-else.il
< ?? spectec/wasm2.0_07-else-simplification.il
< ?? spectec/wasm2.0_08-uncase-removal.il
< ?? spectec/wasm2.0_09-sub-expansion.il
< ?? spectec/wasm2.0_10-pattern-simp.il
< ?? spectec/wasm2.0_11-sub.il
< ?? spectec/wasm2.0_12-definition-to-relation.il
< ?? spectec/wasm2.0_13-sideconditions.il
< ?? spectec/wasm2.0_14-alias-demut.il
< ?? spectec/wasm2.0_15-improve-ids.il
< ?? spectec/wasm2.0_16-single-pattern-match.il
< ?? spectec/wasm2.0_ast_00-elab.il
< ?? spectec/wasm2.0_ast_01-ite.il
< ?? spectec/wasm2.0_ast_02-let-intro-mech.il
< ?? spectec/wasm2.0_ast_03-typefamily-removal.il
< ?? spectec/wasm2.0_ast_04-remove-indexed-types.il
< ?? spectec/wasm2.0_ast_05-totalize.il
< ?? spectec/wasm2.0_ast_06-else.il
< ?? spectec/wasm2.0_ast_07-else-simplification.il
< ?? spectec/wasm2.0_ast_08-uncase-removal.il
< ?? spectec/wasm2.0_ast_09-sub-expansion.il
< ?? spectec/wasm2.0_ast_10-pattern-simp.il
< ?? spectec/wasm2.0_ast_11-sub.il
< ?? spectec/wasm2.0_ast_12-definition-to-relation.il
< ?? spectec/wasm2.0_ast_13-sideconditions.il
< ?? spectec/wasm2.0_ast_14-alias-demut.il
< ?? spectec/wasm2.0_ast_15-improve-ids.il
< ?? spectec/wasm2.0_ast_16-single-pattern-match.il
< ?? spectec/wasm3.0.v
< ?? spectec/wasm3.0_00-elab.il
< ?? spectec/wasm3.0_01-ite.il
< ?? spectec/wasm3.0_02-let-intro-mech.il
< ?? spectec/wasm3.0_03-typefamily-removal.il
< ?? spectec/wasm3.0_04-remove-indexed-types.il
< ?? spectec/wasm3.0_05-totalize.il
< ?? spectec/wasm3.0_06-else.il
< ?? spectec/wasm3.0_07-else-simplification.il
< ?? spectec/wasm3.0_08-uncase-removal.il
< ?? spectec/wasm3.0_09-sub-expansion.il
< ?? spectec/wasm3.0_10-pattern-simp.il
< ?? spectec/wasm3.0_11-sub.il
< ?? spectec/wasm3.0_12-definition-to-relation.il
< ?? spectec/wasm3.0_13-sideconditions.il
< ?? spectec/wasm3.0_14-alias-demut.il
< ?? spectec/wasm3.0_15-improve-ids.il
< ?? spectec/wasm3.0_16-single-pattern-match.il
< ?? spectec/wasm3.0_ast_00-elab.il
< ?? spectec/wasm3.0_ast_01-ite.il
< ?? spectec/wasm3.0_ast_02-let-intro-mech.il
< ?? spectec/wasm3.0_ast_03-typefamily-removal.il
< ?? spectec/wasm3.0_ast_04-remove-indexed-types.il
< ?? spectec/wasm3.0_ast_05-totalize.il
< ?? spectec/wasm3.0_ast_06-else.il
< ?? spectec/wasm3.0_ast_07-else-simplification.il
< ?? spectec/wasm3.0_ast_08-uncase-removal.il
< ?? spectec/wasm3.0_ast_09-sub-expansion.il
< ?? spectec/wasm3.0_ast_10-pattern-simp.il
< ?? spectec/wasm3.0_ast_11-sub.il
< ?? spectec/wasm3.0_ast_12-definition-to-relation.il
< ?? spectec/wasm3.0_ast_13-sideconditions.il
< ?? spectec/wasm3.0_ast_14-alias-demut.il
< ?? spectec/wasm3.0_ast_15-improve-ids.il
< ?? spectec/wasm3.0_ast_16-single-pattern-match.il
< ?? spectec/zy_sandbox.v
< 
< spectec/test-lean/todaywasm2.0.lean
< spectec/test-lean/todaywasm3.0.lean
< Irreducible.lean
< Irreducible2.lean
< PrintFalse.lean
< specification/bleh/
< spectec/BEQ_INHABITED_RELD_FIX_PLAN.md
< spectec/FETCH_HEAD
< spectec/check_wasm2.0.lean
< spectec/check_wasm2.0.v
< spectec/check_wasm2.0_OLD.lean
< spectec/diegochanges.diff
< spectec/diegowasm2.0.lean
< "spectec/diegowasm3.0
< spectec/diegowasm3.0.lean
< spectec/oldwasm2.0.lean
< spectec/src/temp_zy_dev/scraps.md
< spectec/temp-wasm-3/email_stuff.md
< spectec/test-rocq/_opam/
< spectec/test-rocq/echo
< spectec/test-rocq/rocq-temp.export
< spectec/test-rocq/test-rocq.opam
< spectec/test-rocq/upd_label_unchanged_typing_verified_walkthrough.md
< spectec/wasm1.0_00-elab.il
< spectec/wasm1.0_01-ite.il
< spectec/wasm1.0_02-let-intro-mech.il
< spectec/wasm1.0_03-typefamily-removal.il
< spectec/wasm1.0_04-remove-indexed-types.il
< spectec/wasm1.0_05-totalize.il
< spectec/wasm1.0_06-else.il
< spectec/wasm1.0_07-else-simplification.il
< spectec/wasm1.0_08-uncase-removal.il
< spectec/wasm1.0_09-sub-expansion.il
< spectec/wasm1.0_10-pattern-simp.il
< spectec/wasm1.0_11-sub.il
< spectec/wasm1.0_12-definition-to-relation.il
< spectec/wasm1.0_13-sideconditions.il
< spectec/wasm1.0_14-alias-demut.il
< spectec/wasm1.0_15-improve-ids.il
< spectec/wasm1.0_16-single-pattern-match.il
< spectec/wasm1.0_ast_00-elab.il
< spectec/wasm1.0_ast_01-ite.il
< spectec/wasm1.0_ast_02-let-intro-mech.il
< spectec/wasm1.0_ast_03-typefamily-removal.il
< spectec/wasm1.0_ast_04-remove-indexed-types.il
< spectec/wasm1.0_ast_05-totalize.il
< spectec/wasm1.0_ast_06-else.il
< spectec/wasm1.0_ast_07-else-simplification.il
< spectec/wasm1.0_ast_08-uncase-removal.il
< spectec/wasm1.0_ast_09-sub-expansion.il
< spectec/wasm1.0_ast_10-pattern-simp.il
< spectec/wasm1.0_ast_11-sub.il
< spectec/wasm1.0_ast_12-definition-to-relation.il
< spectec/wasm1.0_ast_13-sideconditions.il
< spectec/wasm1.0_ast_14-alias-demut.il
< spectec/wasm1.0_ast_15-improve-ids.il
< spectec/wasm1.0_ast_16-single-pattern-match.il
< spectec/wasm2.0_00-elab.il
< spectec/wasm2.0_01-ite.il
< spectec/wasm2.0_02-let-intro-mech.il
< spectec/wasm2.0_03-typefamily-removal.il
< spectec/wasm2.0_04-remove-indexed-types.il
< spectec/wasm2.0_05-totalize.il
< spectec/wasm2.0_06-else.il
< spectec/wasm2.0_07-else-simplification.il
< spectec/wasm2.0_08-uncase-removal.il
< spectec/wasm2.0_09-sub-expansion.il
< spectec/wasm2.0_10-pattern-simp.il
< spectec/wasm2.0_11-sub.il
< spectec/wasm2.0_12-definition-to-relation.il
< spectec/wasm2.0_13-sideconditions.il
< spectec/wasm2.0_14-alias-demut.il
< spectec/wasm2.0_15-improve-ids.il
< spectec/wasm2.0_16-single-pattern-match.il
< spectec/wasm2.0_ast_00-elab.il
< spectec/wasm2.0_ast_01-ite.il
< spectec/wasm2.0_ast_02-let-intro-mech.il
< spectec/wasm2.0_ast_03-typefamily-removal.il
< spectec/wasm2.0_ast_04-remove-indexed-types.il
< spectec/wasm2.0_ast_05-totalize.il
< spectec/wasm2.0_ast_06-else.il
< spectec/wasm2.0_ast_07-else-simplification.il
< spectec/wasm2.0_ast_08-uncase-removal.il
< spectec/wasm2.0_ast_09-sub-expansion.il
< spectec/wasm2.0_ast_10-pattern-simp.il
< spectec/wasm2.0_ast_11-sub.il
< spectec/wasm2.0_ast_12-definition-to-relation.il
< spectec/wasm2.0_ast_13-sideconditions.il
< spectec/wasm2.0_ast_14-alias-demut.il
< spectec/wasm2.0_ast_15-improve-ids.il
< spectec/wasm2.0_ast_16-single-pattern-match.il
< spectec/wasm3.0.v
< spectec/wasm3.0_00-elab.il
< spectec/wasm3.0_01-ite.il
< spectec/wasm3.0_02-let-intro-mech.il
< spectec/wasm3.0_03-typefamily-removal.il
< spectec/wasm3.0_04-remove-indexed-types.il
< spectec/wasm3.0_05-totalize.il
< spectec/wasm3.0_06-else.il
< spectec/wasm3.0_07-else-simplification.il
< spectec/wasm3.0_08-uncase-removal.il
< spectec/wasm3.0_09-sub-expansion.il
< spectec/wasm3.0_10-pattern-simp.il
< spectec/wasm3.0_11-sub.il
< spectec/wasm3.0_12-definition-to-relation.il
< spectec/wasm3.0_13-sideconditions.il
< spectec/wasm3.0_14-alias-demut.il
< spectec/wasm3.0_15-improve-ids.il
< spectec/wasm3.0_16-single-pattern-match.il
< spectec/wasm3.0_ast_00-elab.il
< spectec/wasm3.0_ast_01-ite.il
< spectec/wasm3.0_ast_02-let-intro-mech.il
< spectec/wasm3.0_ast_03-typefamily-removal.il
< spectec/wasm3.0_ast_04-remove-indexed-types.il
< spectec/wasm3.0_ast_05-totalize.il
< spectec/wasm3.0_ast_06-else.il
< spectec/wasm3.0_ast_07-else-simplification.il
< spectec/wasm3.0_ast_08-uncase-removal.il
< spectec/wasm3.0_ast_09-sub-expansion.il
< spectec/wasm3.0_ast_10-pattern-simp.il
< spectec/wasm3.0_ast_11-sub.il
< spectec/wasm3.0_ast_12-definition-to-relation.il
< spectec/wasm3.0_ast_13-sideconditions.il
< spectec/wasm3.0_ast_14-alias-demut.il
< spectec/wasm3.0_ast_15-improve-ids.il
< spectec/wasm3.0_ast_16-single-pattern-match.il
< spectec/zy_sandbox.v
```

</details>

### Diagnosis of the false positive (read-only)

- I had done nothing before this check (it was my first command), so nothing could be mine.
- `grep` reported `binary file matches` for the new check file, so `grep -v test-lean-claude`
  emitted nothing for the NEW side and the diff showed every baseline line as deleted (`1,256d0`).
- `check.sh` names its output `check-<UTC second>.txt` and writes with `> "$OUT"`. Another
  sibling agent's check produced `check-20261005T052753Z.txt` in the same moment; two concurrent
  writers to the same-second file name (truncate + write at a stale offset) leave NUL holes,
  which makes grep classify the file as binary. By the time I inspected it, the file was clean
  (`file` says `ASCII text`, zero NUL bytes, zero non-printable bytes).
- Re-doing the script's comparison by hand with `grep -a` on the current contents:
  `NO DIFFERENCE outside target dir` for both `check-20261005T052753Z.txt` and
  `check-20261005T052754Z.txt`.
- Suggestion for the main session (not acted on; I may not edit the script): use `grep -a` in
  `verify_against_baseline.sh` and/or a sub-second/PID-unique file name in `check.sh` to avoid this
  race when several agents run checks simultaneously.

### Second run (13:28:38 local), verbatim

```
safety check [audit-hygiene] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052838Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

Proceeding with the read-only audit on the basis of the clean re-run.

## Work log (incremental)


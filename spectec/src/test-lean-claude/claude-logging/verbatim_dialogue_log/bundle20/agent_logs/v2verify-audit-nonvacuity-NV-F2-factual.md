# v2verify-audit-nonvacuity-NV-F2-factual (adversarial verifier, FACTUAL lens)

## Task
Adversarially re-derive every factual claim of auditor finding NV-F2 ("Globaltype_ok only admits
mutable globals (spec says MUT?), so every Store_ok store and every valid module has only mutable
globals", severity major, known-undocumented). Open every cited file/line myself, try to refute,
and return confirmed / partially-confirmed (with corrected severity) / refuted. Read-only w.r.t.
the repo except this log file. No Lean runs, no agents spawned.

## Safety check (START)
```
safety check [v2verify-audit-nonvacuity-NV-F2-factual] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112112.499480571Z-v2verify-audit-nonvacuity-NV-F2-factual-1417090.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Read so far
- Shared brief `scratchpad/briefs/audit_brief_v2.md` (full).
- No partial log from the first wave existed at this path.

- `wasm2.0.lean` (grep + `sed -n`): 12684-12692 (`Globaltype_ok`), 12710-12720 (`Externtype_ok.global`),
  13462-13480 (`Global_ok`), 15511-15530 (`Context_ok`), 15915-15935 (`Globalinst_ok`),
  15990-16030 (`Store_ok`), 16315-16327 (`State_ok`/`Config_ok`), 16175-16181 (`Extend_globalinst`);
  line 697 (`abbrev «mut» : Type := Option r_MUT`), 713-714 (`globaltype.mk_globaltype`).
- `specification/wasm-2.0/6-typing.spectec` 18-40, 50-54, 586-597, 644-648, 675-681;
  `B-soundness.spectec` 150-166, 250-260, 303-311; `1-syntax.spectec:162` (`syntax mut = MUT?`).
- `spectec/test-rocq/theories/wasm.v` 14683-14687 (+ grep of all `Globaltype_ok` uses).
- Isabelle `scratchpad/isabelle/isabelle_reference_output_wasm2.thy` 11390-11395 (+ grep); `imports`
  lines of every `.thy` in that dir; grep `mk_Globaltype_ok` (Properties.thy:241).
- `grep -c Globaltype_ok` in the six hand-written Lean files; `ExtensionLemmas.lean` 1160-1185;
  `TypePreservation.lean` ~1098-1114 (call site of `global_set_global_extension`).
- `claude-logging/for-claude/digest_wasm_v.md` 255-270; grep of NOTES.md, gap_analysis_v1.md,
  signature_audit_v1.md, bundle14 prompt/response, is_wf_theorems.md for any documentation.
- SpecTec pipeline source: `spectec/src/middlend/undep.ml` 157-166, `spectec/src/exe-spectec/main.ml` 310-335.
- Auditor log `agent_logs/audit-nonvacuity.md` 74-96, 344-402, 431 and its scratch files
  `scratchpad/agents/audit-nonvacuity/{run6.txt,Witness.lean}` (raw Lean output; I did NOT run Lean).

## Method
Opened every cited location myself and re-derived each claim; searched for refutation angles:
(1) Isabelle proof importing a hand-fixed theory instead of the generated one; (2) the length/zip
loophole in `Forall₂` letting an immutable global escape `Globalinst_ok`; (3) the restriction already
being documented somewhere (would make it "known-documented"); (4) the `MUT?` reading being contestable;
(5) the hand-written proofs silently depending on the restriction; (6) consistency of the
machine-checked claims with raw Lean output.

## Claim-by-claim results
| # | Claim | Result |
|---|---|---|
| 1 | Lean `Globaltype_ok` single ctor fixed to `some r_MUT.MUT` (wasm2.0.lean:12688-12689) | CONFIRMED verbatim |
| 2 | Rocq same (wasm.v:14685-14686) | CONFIRMED verbatim: `Globaltype_ok (mk_globaltype (Some MUT) t)` |
| 3 | Isabelle same (thy:11392-11394) | CONFIRMED verbatim; all Isabelle proof theories `imports ... isabelle_reference_output_wasm2` directly (no hand-fixed copy), Properties.thy:241 even uses `mk_Globaltype_ok` |
| 4 | Spec rule `|- MUT? t : OK` (6-typing.spectec:35-36) | CONFIRMED |
| 5 | `Store_ok` requires `Forall₂ Globalinst_ok`; `Globalinst_ok` requires `Globaltype_ok (mk_globaltype v_mut t)` | CONFIRMED (15997-15998; 15923). Zip loophole closed: explicit `(List.length globalinst_lst) = (List.length globaltype_lst)` premise at 15997, and `s = {GLOBALS := globalinst_lst, ...}` |
| 6 | No config over such a store is `Config_ok` | CONFIRMED: `Config_ok` needs `State_ok` (16327), which needs `Store_ok s` (16317); spec B-soundness 303-311 same |
| 7 | `Global_ok` has `Globaltype_ok gt → gt = mk_globaltype v_mut t →` with `v_mut` unconstrained (13471-13472) | CONFIRMED; spec 591-595 `-- if gt = mut t`. Module_ok (spec 675-680) needs `Global_ok` per global; imports also blocked: `Import_ok` → `Externtype_ok` → `Externtype_ok/global` → `Globaltype_ok` (spec 50-52, 644-646; Lean 12714-12717) |
| 8 | Immutable globals intended to be allowed | SUPPORTED, additionally by `Extend_globalinst` (`-- if mut = MUT \/ val = val'`, spec B-soundness:258-260; Lean 16177), which presupposes immutable globals in valid stores |
| 9 | Not a Lean porting deviation | CONFIRMED (identical in all 3 backends) |
| 10 | Witness uses a mutable global; t_preservation non-vacuous | CONSISTENT with auditor raw output `run6.txt` (`hyps_satisfiable` standard axioms only) and log line 70 |
| 11 | Machine-checked `immutable_globaltype_not_ok` (no axioms), `s_imm_not_ok` (standard axioms) | CONSISTENT: statements in `Witness.lean` (sha prefix bf19d3956a35e023 = log) match finding verbatim; `run6.txt`: `'NonVacuity.immutable_globaltype_not_ok' does not depend on any axioms`, `'NonVacuity.s_imm_not_ok' depends on axioms: [propext, Classical.choice, Quot.sound]`. Proof scripts sound by inspection (`intro h; cases h` on `none` vs `some MUT`). |
| 12 | Flagged only in digest_wasm_v.md:260-268, never confirmed/analysed | CONFIRMED: flag text at 261-268; NOTES.md/gap_analysis/signature_audit/bundle14/is_wf_theorems.md mentions of "immutable"/`some r_MUT.MUT` are all about the unrelated `ai_principal_typing` GLOBAL_SET fix (NOTES.md:385-386). So "known-undocumented" is accurate. |
| 13 | 0 occurrences of `Globaltype_ok` in the 6 hand-written files | CONFIRMED (0/0/0/0/0/0) |
| 14 | Root cause "looks like" `MUT?` (Opt iteration, no iter var) → constant `Some MUT`; "not traced" | CONJECTURE CORRECT, now traced: `middlend/undep.ml:162-164` `(* HACK - Change IterE of option and list with no iteration variable into a OptE *) | IterE (e1, (Opt, [])) -> OptE (Some e1)`; pass `Undep` is enabled for `| Rocq | Lean ->` at `exe-spectec/main.ml:317-323`. |
| 15 | (recommendation, hedged) upstream fix should have little direct effect on Lean proofs | PLAUSIBLE: `global_set_global_extension` (ExtensionLemmas:1167-1181) takes mutability as a hypothesis; its caller (TypePreservation.lean ~1100-1112) obtains it from module-instance typing (`minst_invert_globals`) + the GLOBAL.SET instruction type (`hgt`), not from `Globaltype_ok` inversion. `ExtensionLemmas.lean:162` discards the `Globaltype_ok` premise with `_`. Not exhaustively verified. |

## Verdict
CONFIRMED, severity major (unchanged). Every cited file:line and snippet is exact; no refutation
angle succeeded. Not critical: `t_preservation` remains true and non-vacuous and the Lean statement
matches Rocq exactly (shared upstream pipeline artifact). Not lower than major: it is an undocumented
coverage restriction of the soundness result relative to the Wasm spec (immutable globals, defined
or imported, are excluded from every valid module and every `Store_ok` store), which a reviewer must know.
Small additions: imports are blocked too (via `Externtype_ok`), the root cause is the `undep.ml` HACK,
and `Extend_globalinst`'s immutable branch is never exercised on `Store_ok` stores under this restriction.

## Uncertainties
- I did not run Lean (brief forbids it for my task); machine-check claims rest on the auditor's raw
  output files, which are internally consistent.
- I did not confirm that `MUT?` elaborates to `IterE(MUT,(Opt,[]))` in the IL (did not run spectec);
  the `undep.ml` HACK is the only rewrite that produces this shape, so the trace is highly likely.
- Isabelle's pipeline lives on another branch; I verified only its generated output, not its middlend.

## Safety check (END)
```
safety check [v2verify-audit-nonvacuity-NV-F2-factual] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112648.270703751Z-v2verify-audit-nonvacuity-NV-F2-factual-1422567.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```
Files written by me: this log only (plus an empty scratch dir
`scratchpad/agents/v2verify-audit-nonvacuity-NV-F2-factual/` outside the repo).

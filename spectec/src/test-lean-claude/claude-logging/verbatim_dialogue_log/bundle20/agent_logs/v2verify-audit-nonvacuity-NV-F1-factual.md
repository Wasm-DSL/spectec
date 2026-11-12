# v2verify-audit-nonvacuity-NV-F1-factual (adversarial verifier, FACTUAL lens)

## Task

Adversarially verify finding NV-F1 from auditor "audit-nonvacuity" (bundle20 preservation
audit). The finding says: the generated `Moduleinst_ok` (Lean, Rocq, Isabelle) has an extra
`|...| > 0` nonemptiness premise over the module instance's
global/mem/table/func addresses. The spec does not have this premise. It comes from
`middlend/sideconditions.ml` (the `MemE` side condition plus `iterPr` dropping the `*`
iteration). As a result an all-empty module instance, which `fun_invoke` uses, is never
typable. Severity claimed: major. My job is to open every cited file/line, re-derive each
factual claim, and try to refute it.

Safety: read-only w.r.t. the repo except this log; scratch files only in
`/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/agents/v2verify-audit-nonvacuity-NV-F1-factual/`.
No Lean runs (not allowed by my task prompt), no lake, no spawned agents.

## Safety check (START), verbatim

```
safety check [v2verify-audit-nonvacuity-NV-F1-factual] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T111924.472408458Z-v2verify-audit-nonvacuity-NV-F1-factual-1416355.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Work log (incremental)

No partial log from the first wave existed at my path, so I started fresh.

### What I read (files + ranges)

- Brief: `scratchpad/briefs/audit_brief_v2.md` (all).
- `wasm2.0.lean`: 15671-15740 (`Moduleinst_ok`, single constructor), 15743-15780 (`Frame_ok`),
  16315-16333 (`State_ok`, `Config_ok`), 15445-15490 (`fun_invoke`), plus a grep of all 14 `> 0`
  premises and the lines after them (9556-9637, 13790-13880).
- `specification/wasm-2.0/B-soundness.spectec`: 196-232. `specification/wasm-2.0/9-module.spectec`: 190-197.
- `spectec/src/middlend/sideconditions.ml`: 1-175 (all). `spectec/src/il/ast.ml`: 16-20 (`iter` type).
  `spectec/src/exe-spectec/main.ml`: 300-336 (which targets enable which passes).
- `spectec/test-rocq/theories/wasm.v`: 17155, 17170-17176. `type_progress.v`: grep `invoke`.
- Isabelle `scratchpad/isabelle/isabelle_reference_output_wasm2.thy`: 13615, 13630-13643.
- `TypePreservation.lean`: 502-540 (`reduce_inst_unchanged`).
- Auditor's log `agent_logs/audit-nonvacuity.md` (60-90, 315-350, 386-402, 413-422) and the auditor's
  scratch `scratchpad/agents/audit-nonvacuity/{Witness.lean,run6.txt}`.
- `agent_logs/audit-isabelle.md`: 146-147, 269-275.
- Prior project docs, checked for earlier mentions: `for-claude/NOTES.md`, `for-claude/digest_wasm_v.md`,
  `for-claude/digest_prior_lean_attempts.md`, `bundle13/.../signature_audit_v1.md`,
  `bundle17/.../gap_analysis_v1.md` (grep).

### Method

I re-derived each claim from the source, line by line. I did not run Lean, since my task prompt does
not allow it. Instead I re-derived the two "machine-checked" lemmas by hand from the constructor
shapes, and cross-checked the auditor's raw Lean output file against its log.

### Claim-by-claim results

| # | Claim in NV-F1 | Result | Evidence |
|---|---|---|---|
| 1 | Lean `Moduleinst_ok` has `|GLOBAL* ++ MEM* ++ TABLE* ++ FUNC*| > 0` | TRUE | `wasm2.0.lean:15690` `(List.length ((Map ... externaddr.GLOBAL ...) ++ (...MEM... ++ (...TABLE... ++ ...FUNC...)))) > 0 →` |
| 2 | Spec only has the per-export membership under `*` | TRUE | `B-soundness.spectec:230` `-- (if exportinst.ADDR <- (GLOBAL globaladdr)* (MEM memaddr)* (TABLE tableaddr)* (FUNC funcaddr)*)*`; no other nonemptiness premise in the rule (196-230) |
| 3 | `sideconditions.ml:62-63` emits `|xs| > 0` for a membership | TRUE | l.62 `| MemE (_exp, exp) ->`, l.63 `[IfPr (CmpE (\`GtOp, \`NatT, LenE exp ..., NumE (\`Nat Z.zero) ...` (nit: not under `NegPr`, where `t_prem` returns `([], false)`) |
| 4 | `iterPr` drops `exportinst` and returns the bare premise | TRUE | l.22-28 (l.21 = doc comment); l.27 `if iter <= List1 && vars' = [] then pr.it else`; `ast.ml:16-20` `Opt | List | List1 | ListN of ...` so `List <= List1`. Path: `t_rule'` (l.135-141) -> `t_prem` IterPr branch (l.81-89) -> `collect_prem collector2 prem'` -> `t_exp` MemE -> `iterPr (IfPr(|cat|>0), (List,[exportinst]))`; `exportinst` is not free in `|cat|>0` -> `vars'=[]` -> `pr.it` |
| 5 | Hoisting is wrong for zero iterations | TRUE | `(P)*` over `exportinst*=[]` is vacuous; bare `P` is not |
| 6 | Same premise in Rocq and Isabelle; pass is shared | TRUE | `wasm.v:17174` `...funcaddr_lst))))|) >? 0%N)%BN ->`; Isabelle `.thy:13634` `... funcaddr_lst))))) > 0) \<Longrightarrow>`; `main.ml:317-319` `| Rocq | Lean -> ... enable_pass Sideconditions;` |
| 7 | Not false or vacuous (satisfiable witness) | TRUE | auditor's `run6.txt` l.2: `'NonVacuity.c1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]` (witness with `GLOBALS := [0]`) |
| 8 | Empty GLOBALS/MEMS/TABLES/FUNCS module => never `Config_ok` | TRUE (wording loose: configs, not frames, are `Config_ok`) | `Config_ok` (16325-16333) -> `State_ok` (16315-16321) -> `Frame_ok` (15743-15769) -> `Moduleinst_ok s v_moduleinst C` (single ctor, conclusion record built from the list vars) -> the four lists `[]` make l.15690 `0 > 0` |
| 9 | `fun_invoke` uses exactly the all-empty module instance | TRUE | `wasm2.0.lean:15454-15466` `f = ({ LOCALS := [] MODULE := { TYPES := [] FUNCS := [] GLOBALS := [] ... EXPORTS := [] ...` ; spec `9-module.spectec:196-197` `def $invoke(s, fa, val^n) = s; f; val^n (CALL_ADDR fa) -- if f = { MODULE {} }` |
| 10 | `t_preservation` never applies to an invocation's initial config | TRUE, and understated | `t_preservation : ... Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts` (run6 l.1). Also `TypePreservation.lean:536-539` `reduce_inst_unchanged : Step (...s f...) (...s' f'...) → f.MODULE = f'.MODULE`, so NO config reachable from `$invoke` is `Config_ok`, not just the initial one |
| 11 | Machine-checked `emptyMI_not_ok`, `invoke_config_not_ok` (standard axioms only) | TRUE (from recorded output; my own derivation agrees) | auditor `Witness.lean:224,231` (no `sorry`/`axiom`/`native_decide` in the file); `run6.txt` l.9-10 `[propext, Classical.choice, Quot.sound]`; Witness.lean mtime 19:12:00, run6 19:12:02 |
| 12 | audit-isabelle independently reported it as F1 | TRUE | `audit-isabelle.md:146` `F1 [major, NEW] \`Moduleinst_ok\` has a hoisted premise ... > 0` |
| 13 | The other 13 `> 0` premises are benign | TRUE | grep finds exactly 14. Trivially true: 2082, 11832 (length of a 4-element literal). The other 11 (9556, 9570, 9586, 9607, 9622, 9637, 13798, 13808, 13830, 13863, 13874) each have a top-level `List.contains <same list> ...` within 2 lines |
| 14 | "new" | TRUE | not in NOTES.md, the digests, signature_audit_v1 or gap_analysis_v1 (grep for `> 0`/`emptyMI`/`MODULE {}`/`hoisted`/`iterPr`); only audit-isabelle in this same wave. Rocq `type_progress.v` has no invoke-typing lemma (only a comment at l.5762) |

Minor citation nits, none of which change the substance: `iterPr` is l.22-28 and `flatten_empty_iter` is
l.114-120 (the cited ranges include the doc comments); the `fun_invoke` record ends at l.15466, not
15464. `flatten_empty_iter` is not the proximate cause here, because `iterPr` already strips the
iteration. It matters only for the recommendation: it would re-strip an `IterPr(_, (List, []))` if
only `iterPr` were fixed. The auditor's log body says "Lean l.15688" in one place, but the finding
JSON has the correct l.15690.

### Severity assessment

`major` stands. Not `critical`: the theorem is neither false nor vacuous (machine-checked satisfiable
witness), and Lean matches Rocq exactly. It is a shared generator artifact, not a port deviation. Not
`minor`: it changes the meaning of `Config_ok` relative to the spec, and it is undocumented. Through
`reduce_inst_unchanged` it excludes every configuration reachable from `$invoke`, which a reviewer must
know about for any end-to-end soundness claim.

### Verdict

CONFIRMED, severity major. I could not refute any factual claim. The one substantive correction runs
the other way: the coverage loss is wider than stated, because it covers all configurations reachable
from an invocation, not just the initial one.

## Safety check (END), verbatim

```
safety check [v2verify-audit-nonvacuity-NV-F1-factual] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112429.236325975Z-v2verify-audit-nonvacuity-NV-F1-factual-1419430.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Uncertainties

- I did not run Lean myself (not permitted for this task). The "machine-checked" status of
  `emptyMI_not_ok`/`invoke_config_not_ok` rests on the auditor's recorded raw output (`run6.txt`) and on my
  own hand re-derivation from the constructor shapes. Both agree.
- I did not re-run SpecTec to dump the IL after the `Sideconditions` pass, because building or running it
  would write outside my sanctioned locations. The attribution to `iterPr` comes from reading the code
  path. That attribution is consistent with the premise appearing identically in all three backends'
  outputs.
- The only files I wrote: this log, plus the two safety-check logs that the check script itself creates.

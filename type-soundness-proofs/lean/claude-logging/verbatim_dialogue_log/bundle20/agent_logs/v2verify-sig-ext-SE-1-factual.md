# v2verify-sig-ext-SE-1-factual (adversarial verifier, FACTUAL lens)

## Task

Adversarially verify finding SE-1 reported by auditor "sig-ext" in the bundle20 preservation
audit: "s_invert_funcs/_globals/_mems/_tables are vacuous in Lean (existential list +
zip-based Forall2)", severity major. Re-derive every factual claim from the cited files and
lines; try to refute. Read-only w.r.t. the repo except this log file. Lean is NOT run.

## Safety check (START), verbatim

```
safety check [v2verify-sig-ext-SE-1-factual] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112420.292417890Z-v2verify-sig-ext-SE-1-factual-1419254.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

(No partial log from a first wave existed at this path.)

## Work log

### What I read

- Brief `scratchpad/briefs/audit_brief_v2.md` (all 169 lines).
- `wasm2.0.lean`: 1-40 (`Forall₂` def at 20-21), 11402-11408 (`structure funcinst`:
  TYPE/MODULE/CODE), 15985-16010 (`Store_ok` ctor; length premises from 15994).
- `ExtensionLemmas.lean`: 1-30 (imports/header), 135-160, 210-290 (the four lemmas +
  proofs), 1222-1236 and 2116-2130 (the only other mentions; both inside `/-- -/` doc comments).
- Greps over the six Lean files, `lakefile.lean` and `ExtendedDeriveDecEq.lean` for
  `namespace`/`open`/`export` and any `Forall₂` (re)declaration.
- Rocq `test-rocq/theories/extension_lemmas.v`: 1-10 (imports), 40-60, 72-90, 104-125,
  173-192; `wasm.v:13157-13161` (`Record funcinst`); greps over `theories/*.v` for any
  `Forall2`/`List` redefinition and for uses of `s_invert_*`.
- Prior logs (grep of `s_invert_*` over `claude-logging/`, excluding bundle20):
  `NOTES.md:228-246`, bundle13 `signature_audit_v1.md` rows 10-11, bundle15
  `extension_lemmas_triage_v1.md` rows 55-58 and l.32/182, bundle17 `gap_analysis_v1.md`
  (no `s_invert` mention at all; l.110-118 = hlen context), bundle14 prompt/response,
  `digest_subtyping_and_extension_lemmas.md:235-240`.

### Method

Re-derived each claim from the sources and tried to refute it via: (1) name-resolution
shadowing (a `TLC.Forall₂`, an `open List`, or Mathlib's inductive `List.Forall₂`);
(2) a Rocq-side redefinition of `List.Forall2`; (3) hidden uses of the four lemmas;
(4) prior documentation of the issue; (5) whether each Rocq lemma really carries content
(record-eta tautology check). Lean NOT run (the brief forbids it); I derived the vacuity
by hand from `List.zip l [] = []`.

### Claim-by-claim results

| # | Claim | Result |
|---|-------|--------|
| 1 | `wasm2.0.lean:20-21` `Forall₂ P xs₁ xs₂ := ∀ t ∈ xs₁ \|>.zip xs₂, P t.1 t.2` | TRUE (verbatim). |
| 2 | The four Lean conclusions are `∃ xs, Forall₂ P s.X xs` (l.223/232/254/269) | TRUE. Exact lines. |
| 3 | `Forall₂` there is the zip-based root def | TRUE. No `TLC.Forall₂`, no `open List`/`export` in any of the six files (only `open scoped Classical` in Subtyping). Mathlib's `List.Forall₂` is namespaced. Decisive: each proof gives `fun p hp => ...` as the `Forall₂` proof, which only type-checks against the `∀ t ∈ zip` def. |
| 4 | Witness `[]` proves each conclusion for every store, without `Store_ok` | TRUE: `s.X.zip [] = []` (`List.zip_nil_right`), so `∀ t ∈ [], …` holds trivially. Checked by hand, not run in Lean. |
| 5 | Rocq uses inductive `List.Forall2`, which forces equal length; Rocq globals/mems/tables carry real content | TRUE. Fully qualified `List.Forall2` (Stdlib, imported l.1). No redefinition in `theories/*.v`. Content: `Val_ok s v_v v_vt` per global (v.74-83); `v_n = pagediv b_lst` plus `v_n ≤ m ≤ 2^16` for a declared max, per memory (v.106-116); `Tabletype_ok tbt` and `Forall (Ref_ok s · rt)` per table (v.175-187). |
| 6 | Doc comments say "signature confirmed identical" / "Unaffected by the resync" | TRUE: l.220-222 (funcs) and l.231 (globals). mems/tables say "Signature resynced … Otherwise unaffected by the resync" (l.241-253, 265-268). |
| 7 | None of the four is used in the six Lean files | TRUE. The only other hits, l.1230 and l.2124, are inside doc comments. No other Lean file under test-lean-claude (outside .lake) mentions them. |
| 8 | Not recorded in NOTES or the bundle13/15/17 audits | TRUE. NOTES:237 only lists them as proved. bundle13 #10-11 flag the hard-coded-`Option` bug. bundle15 rates proof difficulty and mentions "zip-based Forall₂" without noticing the vacuity. bundle17 never mentions them. Not in the brief's §5 known list. |
| 9 | `Store_ok` ctor has `List.length _ = List.length _` premises (wasm2.0.lean:15994ff) | TRUE: one per component, from l.15994. Currently bound as `_` in the four proofs, so the recommended fix is easy. |
| 10 | Evidence citation "extension_lemmas.v:74-79" | Slightly short: the statement runs 74-83. Cosmetic. |

### Refinements (do not change the verdict)

- **s_invert_funcs has no content in Rocq either.** `funcinst` has exactly three fields in
  both Rocq (`wasm.v:13157-13161`) and Lean (`wasm2.0.lean:11402-11406`). The Rocq predicate
  `∃ minst v_func, f = {| funcinst_TYPE := t; funcinst_MODULE := minst; CODE := v_func |}`
  therefore holds for any `f` with `t := funcinst_TYPE f` (record eta). Witness
  `fts := map funcinst_TYPE (store_FUNCS s)` proves Rocq's lemma without `Store_ok`; note its
  own `(* May add more here *)`. So the Lean version of s_invert_funcs is vacuous, but it is
  not *materially* different from Rocq: both are equivalent to `True`. The content loss is
  confined to globals/mems/tables. That matches the content list in the finding, but not its
  blanket "the statements are materially different from Rocq".
- **Context supporting `major`.** Rocq's preservation proof does use these lemmas
  (`type_preservation.v:775` tables, `1247` mems, `1824` funcs, `2039` globals, `2071` tables).
  The Lean port gets the same facts by other routes (the bare-variable
  `globalinst_ok_invert`/`meminst_ok_invert`/`tableinst_ok_invert` helpers). So
  `t_preservation` is unaffected. However, a reviewer mapping Rocq proof steps to Lean
  lemmas by statement text would be misled: the text looks the same and the doc comments
  assert identity, yet three of the four Lean lemmas are content-free where Rocq's are
  load-bearing.

### Verdict

**confirmed**, severity **major** kept. It is a real undocumented semantic mismatch (three
ported statements are vacuous where Rocq's carry content), and the doc comments assert the
opposite. Under the brief's rubric it is not `minor`, because the meaning changes. It is not
`critical`, because preservation does not depend on these lemmas. Recommended fix as in the
finding. For s_invert_funcs the fix is optional: it is a tautology in Rocq too.

## Safety check (END), verbatim

```
safety check [v2verify-sig-ext-SE-1-factual] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T112851.842240610Z-v2verify-sig-ext-SE-1-factual-1427224.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

## Uncertainties

- I proved the vacuity by hand (`List.zip l [] = []`), not in Lean, because the brief
  forbids running Lean. It relies only on a standard core simp lemma, so I am confident in it.
- The severity (major vs minor) is a judgement call. The lemmas are unused in Lean, so
  preservation is unaffected. I kept `major` because the brief defines `minor` as "no effect
  on meaning", and this deviation does change meaning.

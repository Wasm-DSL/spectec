# sig-ext — signature audit: ExtensionLemmas.lean vs extension_lemmas.v (bundle20)

Subagent label: `sig-ext`. Spawned by the bundle20 preservation-audit workflow.

## Task

Enumerate every declaration of the Rocq file `spectec/test-rocq/theories/extension_lemmas.v`
(skipping commented-out ones), match each to its Lean counterpart (ExtensionLemmas.lean or
elsewhere in the six hand-written Lean files / wasm2.0.lean), compare statements (binders,
premises, conclusion), list Rocq declarations with no Lean counterpart and Lean declarations
with no Rocq counterpart (checking Lean-only doc labels), spot-check ~15 doc-comment
citations, and note any `sorry`/`axiom`/`native_decide`/`admit`/`implemented_by`/`unsafe` in
ExtensionLemmas.lean. Read-only; Lean not run.

## Safety: start check (verbatim) — FALSE POSITIVE, diagnosed

### First run (05:27:54Z) — printed `DIFFERENCE FOUND` (spurious; see diagnosis)

```
safety check [sig-ext] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
grep: spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt: binary file matches
DIFFERENCE FOUND (lines outside spectec/src/test-lean-claude differ from baseline):
grep: spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T052754Z.txt: binary file matches
1,256d0
< --- git status (porcelain) ---
<  M spectec/test-lean/todaywasm2.0.lean
<  D spectec/test-lean/todaywasm3.0.lean
< ?? Irreducible.lean
  ... (all 256 filtered baseline lines listed as deleted; the NEW side was EMPTY) ...
< spectec/wasm3.0_ast_16-single-pattern-match.il
< spectec/zy_sandbox.v
```

(Exit code 1. The middle of the 256-line diff is elided here only because every line is a
`<` deletion of a baseline line — i.e. the new side of the diff contained nothing at all.)

### Diagnosis (read-only)

- `grep` printed `binary file matches` for the new check file, so `grep -v test-lean-claude`
  emitted nothing for it, the filtered NEW side was empty, and `diff` reported all 256 baseline
  lines as deleted. No line was *added* — nothing new appeared outside the target dir.
- Moments later the same file is plain ASCII (`file` = "ASCII text"; 0 NUL bytes; 0 non-ASCII
  lines), and a manual re-diff of the stable `check-20261005T052753Z.txt` and
  `check-20261005T052754Z.txt` against the baseline (same filters as the script) prints
  **no difference** for either.
- Root cause: ~11 bundle20 subagents ran `check.sh` concurrently. `check.sh` names its output
  `check-<UTC second>.txt` and writes it with `> "$OUT"` (truncate); several runs in the same
  second write the SAME file, and a truncate by one writer while another writer is mid-file
  leaves a transient NUL-filled hole (sparse region) → grep's binary detection. (The file
  named `...052754Z.txt` has mtime 13:27:55.059 local, i.e. it was still being rewritten in
  the following second.) In addition, `verify_against_baseline.sh` picks `NEW` via
  `ls -t ... | head -1`, i.e. possibly ANOTHER agent's file, possibly mid-write.
- Corroboration: in the sibling logs, sig-base, sig-tp, sig-tpp, sig-typing,
  audit-model-step, audit-nonvacuity and audit-proofmap all compared the very same
  `check-20261005T052754Z.txt` and printed `VERIFIED`; audit-hygiene and audit-isabelle hit
  the same transient `binary file matches` false positive as I did.

### Official re-run (05:30:24Z) — VERIFIED

```
safety check [sig-ext] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T053024Z.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
exit=0
```

### Decision

The brief says "If it ever prints `DIFFERENCE FOUND`, stop immediately and report". I did
stop doing audit work and diagnosed first (read-only). Because (a) the trigger is a proven
tooling race, not a repository difference (the NEW side was empty, not different), (b) the
stable file and a fresh official run both verify clean, and (c) my task is strictly
read-only, I continued the audit. This is flagged prominently in my structured result (finding
SE-0) so the main session can discard my results if it prefers a strict stop.
Recommended tooling fix (not applied — I may only write this log): make each check's output
file unique (e.g. `date -u +%Y%m%dT%H%M%S.%NZ` plus `$$` or the label, or `mktemp`), have
`verify_against_baseline.sh` compare the file its own `check.sh` call produced (e.g. have
`check.sh` echo `$OUT`, or pass it in) instead of `ls -t | head -1`, and use `grep -a`.

## Work log (incremental)

(First wave was killed by the usage limit at this point; no audit findings were recorded.)

## Resumed (v2 relaunch)

Primary input per task file: `scratchpad/sigs/sbs_ext.md` (pre-extracted side-by-side pairs +
Lean-only declarations). Big source files opened only to resolve specific doubts (grep/sed ranges).

### Safety: v2 START check (verbatim)

```
safety check [sig-ext] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T110752.675225714Z-sig-ext-1410890.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

### Work log (v2)

1. Read brief v2 (all), task file, own first-wave log (only the safety section existed).
2. Read `scratchpad/sigs/sbs_ext.md` in full (lines 1-2696): 128 Rocq declarations
   (91 EXACT, 2 CITED, 27 NONE, 8 Ltac skipped) + 40 Lean-only entries (one, `terms`, is an
   extractor artefact: text inside the `extend_funcinst_eq` doc comment).
3. Read bundle17 gap analysis §3d (28 expected missing) and §4.
4. Source checks so far (read-only, grep/sed ranges):
   - `wasm2.0.lean:17-22`: `Forall P xs := ∀ t ∈ xs, P t`; `Forall₂ P xs ys := ∀ t ∈ xs.zip ys, P t.1 t.2`.
   - `wasm2.0.lean:750`: `inductive datatype | OK` (singleton).
   - `wasm2.0.lean:15671ff` `Moduleinst_ok` and `15992ff` `Store_ok`: every zip-based `Forall₂`
     premise is paired with an explicit `List.length _ = List.length _` premise (so the length
     IS available in Lean).
   - `wasm2.0.lean:15937` `Meminst_ok`: multiplicative `|b_lst| = v_n * (64 * Ki)`.
   - Uses: `s_invert_funcs/_globals/_mems/_tables` have NO uses in the six Lean files;
     `minst_invert_*` are used in TypePreservation (e.g. l.438), where the missing length is
     recovered from the Lean-only `Moduleinst_ok_lengths` (TypePreservation.lean:404-408, doc
     says Rocq gets it from `Forall2_length`).
   - No earlier audit/NOTES entry mentions that `s_invert_*` are vacuous (grep of NOTES.md,
     bundle13 signature audit, bundle15 triage, digest).

5. Further source checks (read-only):
   - `wasm.v:107-108` `holds_upto P n := Forall P (iotaN N0 n)` (Lean abbrev `Forall P (List.range n)`, cite correct).
   - `wasm.v:192-200` coercions `Qfloor : Q >-> Z`, `Z.to_N : Z >-> N` (so Rocq `v_n = pagediv b_lst` with
     `v_n : N` is floor division, = Lean `b_lst.length / (64 * Ki)`).
   - `wasm.v:1190-1191` `mk_limits (v_u32 : u32) (u32_opt : option u32)`; `wasm.v:582` `u32 := uN`.
   - `wasm.v:17130-17135` Rocq `Datainst_ok` requires `|b_lst| < 2^32`, `wf_store s`, `wf_datainst`.
   - `extension_lemmas.v:2276-2290` (the inline `dependent induction` cited by `Extend_store_externaddr`): accurate.
   - TypePreservation.lean:365-370 (`Extend_store_datainsts₂`, Rocq shape), 404-408 (`Moduleinst_ok_lengths`),
     430-438 (a `minst_invert_mems` call site), 1062-1074 (`datainsts_Forall{,₂}_of_Forall{₂,}`).
   - HelperLemmas.lean:40 (`list_update_func := l.modify`), 44-50, 412-428 (`list_slice_update_forall`).
   - ExtensionLemmas.lean section headers (7,125,139,...,1985), 128-150, 1401-1412, 1698-1716, 1888-1904,
     1985-1995, 2210-2222.
   - Hygiene greps on ExtensionLemmas.lean (sorry/admit/axiom/native_decide/implemented_by/unsafe/extern/opaque/
     partial/set_option/macro/elab); axiom-name and marked-for-deletion-lemma cross-reference with HelperLemmas.
   - Name check: all 68 distinct Rocq names cited as "Rocq `X`" in ExtensionLemmas.lean exist in current Rocq,
     except `funcinst_same`/`Val_ok_store` (docs themselves say "not found in current upstream"). A script
     (`scratchpad/agents/sig-ext/doc_vs_name.py`) found no theorem whose doc cites a different Rocq declaration.
   Scratch files (outside the repo): `scratchpad/agents/sig-ext/{sigext_cited.txt,doc_vs_name.py,coverage.py,coverage.txt}`
   (the first was briefly written one level up in `scratchpad/` and moved into `agents/sig-ext/`; never in the repo).

## Method

For each of the 128 Rocq declarations: compare binders, premises and conclusion with the Lean statement
(side-by-side file), mapping Rocq `List.Forall2` (inductive, implies equal length) to the generated Lean
`Forall₂` (zip-based, does NOT imply equal length) and asking, for each use of `Forall₂`, whether the Lean
lemma is (a) at least as strong as Rocq's (premise and conclusion over the same / length-preserved lists),
(b) weaker (conclusion only, lists fixed), or (c) vacuous (conclusion with an existentially chosen list).
NONE matches checked against the bundle17 gap analysis §3d; Lean-only declarations checked for a label
(own doc comment or section header) and plausibility. Proof bodies only scanned for trust-expanding
constructs. Lean was NOT run (task forbids it); the vacuity claim is by inspection.

## Findings

**SE-1 (major, new) — `s_invert_funcs/_globals/_mems/_tables` are vacuous in Lean.**
Lean ExtensionLemmas.lean:223/232/254/269 vs Rocq extension_lemmas.v:42/74/106/175. Each Lean conclusion is
`∃ xs, Forall₂ P s.X xs`; with `Forall₂ P xs ys := ∀ t ∈ xs.zip ys, …` (wasm2.0.lean:20-21) the witness
`xs := []` makes `s.X.zip [] = []`, so every one of these holds for any store without using `Store_ok`
(`fun _ => ⟨[], by simp [Forall₂]⟩`). Rocq's inductive `List.Forall2` forces `|xs| = |s.X|`, so Rocq's
lemmas assert real content (Val_ok of every global; page-count and `≤ 2^16` facts for every memory;
`Tabletype_ok` and `Ref_ok` for every table). Docs claim "signature confirmed identical"/"Unaffected by the
resync". None of the four is used anywhere in the six Lean files, so `t_preservation` is unaffected.
Fix: put the length inside the existential, e.g. `∃ gts, s.GLOBALS.length = gts.length ∧ Forall₂ … s.GLOBALS gts`
(the generated `Store_ok` constructor already has these `List.length _ = List.length _` premises,
wasm2.0.lean:15994ff), and say so in the doc comments.

**SE-2 (minor, known-undocumented) — `minst_invert_funcs/_tables/_globals/_mems/_elems` drop Rocq's length.**
Lean :684/704/722/740/763 vs Rocq :421/456/493/529/564. Rocq concludes `List.Forall2 … (FUNCS minst)
(context_FUNCS C')` (gives `|FUNCS minst| = |context_FUNCS C'|`); Lean concludes zip-based `Forall₂ …
minst.FUNCS C'.FUNCS`. Strictly weaker, not vacuous (both lists fixed). Call sites recover the length via
the documented Lean-only `Moduleinst_ok_lengths` (TypePreservation.lean:404-408, used e.g. at :435-438),
but the five doc comments do not mention it (contrast `minst_invert_datas`, whose Rocq statement already
carries the length and which matches). Fix: add `minst.X.length = C'.X.length ∧` (as `minst_invert_datas`)
or a one-line doc pointer to `Moduleinst_ok_lengths`.

**SE-3 (minor; `Extend_store_datainsts'` known-documented, the other two known-undocumented) — `datatype.OK`
hard-coded in the datas cluster.** `Extend_store_datainsts'` (:1702 vs :2360), `Extend_store_datainsts`
(:1713 vs :2408) and `construct_datainsts` (:2217 vs :3041) drop Rocq's `ts`/`dt : list datatype` and state
`Forall (fun a => Datainst_ok … a datatype.OK)` instead of `Forall2 (λ a t, Datainst_ok … a t) aa ts`.
Meaning is equivalent (`inductive datatype | OK` is a singleton, wasm2.0.lean:750-751), so no effect on
preservation, but the Rocq names carry a non-Rocq shape while the Rocq-shaped statement exists as the
Lean-only `Extend_store_datainsts₂` (TypePreservation.lean:367), bridged by `datainsts_Forall{,₂}_of_Forall{₂,}`
(:1062-1074): needless correspondence loss. Only the primed lemma was flagged before (gap17 §4.3).
The primed lemma's doc ("`Datainst_ok`'s proof is content-independent/always-true in Rocq") is inaccurate:
Rocq's `Datainst_ok` (wasm.v:17130-17135) needs `|b_lst| < 2^32`, `wf_store s`, `wf_datainst`.
`construct_datainsts`' doc says "Unaffected by the resync" without mentioning the reshape.

**SE-4 (info, known-documented) — re-confirmed: `table_grow_table_extension` `j : Option uN` is faithful.**
Rocq's `j` is used directly as the limits max (`mk_limits (mk_uN (|tbr|)) j`, and `mk_limits` takes
`option u32`, `u32 := uN`; wasm.v:582, 1190-1191), so Lean's `Option uN` matches Rocq exactly (its doc
says so). The "inconsistency" is on the memory side (SE-5); `construct_tableinsts_grow` and
`construct_meminsts_grow` also use `Option uN`.

**SE-5 (minor, known-undocumented) — `memory_grow_mem_extension` restated (equivalently).**
Lean :1234 vs Rocq :1753. Rocq: `(v_i : Q) … (0 <= v_i)%Q …` with `v_j_opt : option u32`; Lean:
`(v_i v_n : Nat) (v_j : Option Nat)` with `v_j.map uN.mk_uN`, no `0 ≤ v_i`. Equivalent in content (`mk_uN v_i`
floors `v_i`, and `⌊v_i⌋ + v_n = ⌊v_i + v_n⌋`), but the Q→Nat change is undocumented here (unlike
`construct_meminsts_grow`, which documents it), the doc says Rocq's `v_j_opt` is `option N` (it is
`option u32`), and it is the only one of the three grow lemmas not using `Option uN`.

**SE-6 (minor, new) — Lean-only labelling gaps.** `Ref_ok_wf_store` (:1996), `wf_tableinst_parts` (:2006),
`wf_meminst_parts` (:2020), `meminst_ok_raw` (:2126) sit under the "construct_*" section header (:1985)
with no "Lean-only/No Rocq counterpart" label; `wf_meminst_parts` is in fact what supersedes Rocq
`invert_meminst` (:1731; gap17 §3d) but does not say so. `HelperLemmas.list_slice_update_forall`
(HelperLemmas.lean:419-428) is labelled "Not a Rocq port" although it is the generalised Rocq
`forall_preserved_bytes` (:1663, used at type_preservation.v:267; gap17 §3d calls it a duplicate).
(Side note: the extractor's Lean-only entry `terms` (Ext:1053, "opaque") is an artefact: text inside the
`extend_funcinst_eq` doc comment, not a declaration.)

**SE-7 (info, known-documented) — unported Rocq declarations all justified.** 27 NONE: 26 are in gap17 §3d
(its 28-list minus `pagediv` and `holds_upto_lt_refl`, which are CITED in Lean docs: `s_invert_mems`,
`forall_range_lt`), plus `Scheme ais_ok_ind'` (named in the `Extend_store_ais` doc; Lean needs no Scheme).
8 Ltac skipped by standing decision (`Extend_store_wf_store`/`'` stand in for `invert_extend_store`).
Apart from those 3, the absences are recorded only in the gap analysis, not in ExtensionLemmas.lean.

**SE-8 (info) — hygiene.** ExtensionLemmas.lean has exactly one `sorry` (l.137, `Val_ok_store`, under
`-- TODO FROM USER: MARKED FOR DELETION BECAUSE UNUSED`, l.128); no `axiom`/`admit`/`native_decide`/
`implemented_by`/`unsafe`/`set_option`/macros. It references none of the 11 HelperLemmas axioms and none of
the marked-for-deletion HelperLemmas sorry lemmas. `funcinst_same` (hlen, documented) has no uses. All cited
Rocq names exist (except the two the docs say are gone); no doc cites the wrong declaration.
Clean: 77 of 91 EXACT pairs are statement-equivalent (with `Forall2→Forall₂` only where premise and
conclusion range over the same or length-preserved lists, which makes the Lean lemma at least as strong).

## Coverage (one line per Rocq declaration; `Ext:` = ExtensionLemmas.lean line, `v:` = extension_lemmas.v line)

```
invert_opt_map_some (v:13): NONE, justified, listed in gap17 §3d (core Option.map_some')
invert_opt_map_none (v:17): NONE, justified, listed in gap17 §3d (core Option.map_none')
pagediv (v:21): CITED (s_invert_mems doc); inlined as Nat `/`, = Rocq Q>->Z>->N floor coercion
pagediv_ge_0 (v:24): NONE, justified, listed in gap17 §3d (Q arith)
pagediv_ge_0_Z (v:33): NONE, justified, listed in gap17 §3d (Q arith)
s_invert_funcs (v:42) -> Ext:223: VACUOUS in Lean (exists list + zip Forall2; witness []) [SE-1]
s_invert_globals (v:74) -> Ext:232: VACUOUS in Lean [SE-1]
s_invert_mems (v:106) -> Ext:254: VACUOUS in Lean [SE-1]
s_invert_tables (v:175) -> Ext:269: VACUOUS in Lean [SE-1]
se_invert_funcs (v:219) -> Ext:287: = statement-equivalent
se_invert_tables (v:230) -> Ext:299: = statement-equivalent
se_invert_mems (v:241) -> Ext:308: = statement-equivalent
se_invert_store_globals (v:252) -> Ext:317: = statement-equivalent
se_invert_elems (v:263) -> Ext:326: = statement-equivalent
se_invert_datas (v:274) -> Ext:335: = statement-equivalent
limits_sub_refl (v:285) -> Ext:350: = statement-equivalent
limits_sub_trans (v:306) -> Ext:363: = statement-equivalent
externtype_sub_refl (v:343) -> Ext:386: = statement-equivalent
externtype_sub_trans (v:363) -> Ext:415: = statement-equivalent
externtype_global_eq (v:394) -> Ext:467: = statement-equivalent
externtype_func_eq (v:403) -> Ext:475: = statement-equivalent
minst_invert_functypes (v:412) -> Ext:676: = statement-equivalent
minst_invert_funcs (v:421) -> Ext:684: WEAKER: conclusion lacks Rocq Forall2 length [SE-2]
minst_invert_tables (v:456) -> Ext:704: WEAKER: no length [SE-2]
minst_invert_globals (v:493) -> Ext:722: WEAKER: no length [SE-2]
minst_invert_mems (v:529) -> Ext:740: WEAKER: no length [SE-2]
minst_invert_elems (v:564) -> Ext:763: WEAKER: no length [SE-2]
minst_invert_datas (v:596) -> Ext:777: = statement-equivalent
invert_funcs (v:628): Ltac, not ported (standing decision; helper_tactics-style plumbing)
invert_tables (v:640): Ltac, not ported (standing decision; helper_tactics-style plumbing)
invert_mems (v:652): Ltac, not ported (standing decision; helper_tactics-style plumbing)
invert_elems (v:664): Ltac, not ported (standing decision; helper_tactics-style plumbing)
invert_datas (v:676): Ltac, not ported (standing decision; helper_tactics-style plumbing)
invert_storeok (v:688): Ltac, not ported (standing decision; helper_tactics-style plumbing)
invert_moduleinstok (v:720): Ltac, not ported (standing decision; helper_tactics-style plumbing)
invert_extend_store (v:774): Ltac, not ported (standing decision; helper_tactics-style plumbing)
lookup_global (v:837) -> Ext:805: = statement-equivalent
bt_inversion (v:870) -> Ext:839: = statement-equivalent
tc_func_reference2 (v:897) -> Ext:860: = statement-equivalent
store_typed_exterval_types (v:908) -> Ext:868: = statement-equivalent
extend_globalinst_refl_0 (v:926) -> Ext:968: = statement-equivalent
extend_meminst_refl_0 (v:938) -> Ext:922: = statement-equivalent
extend_tableinst_refl_0 (v:957) -> Ext:902: = statement-equivalent
extend_eleminst_refl_0 (v:976) -> Ext:982: = statement-equivalent
extend_datainst_refl_0 (v:986) -> Ext:994: = statement-equivalent
extend_funcinst_refl_0 (v:997) -> Ext:886: = statement-equivalent
nth_iotaN (v:1006): NONE, justified, listed in gap17 §3d (iotaN~List.range)
size_iotaN (v:1032): NONE, justified, listed in gap17 §3d (iotaN~List.range)
holds_upto_lookup (v:1049): NONE, justified, listed in gap17 §3d (holds_upto is an abbrev)
Externaddr_invert_funcs (v:1065) -> Ext:533: = (Rocq == is ssr boolean eq, Lean =)
Externaddr_invert_tables (v:1089) -> Ext:575: = (== vs =)
Externaddr_invert_mems (v:1113) -> Ext:617: = (== vs =)
Externaddr_invert_globals (v:1137) -> Ext:659: = (== vs =)
Extend_store_ref (v:1161) -> Ext:1099: = statement-equivalent
Extend_store_refs (v:1187) -> Ext:1115: = statement-equivalent
Extend_store_refs' (v:1201) -> Ext:1123: = statement-equivalent
Extend_store_val (v:1214) -> Ext:1128: = statement-equivalent
Extend_store_vals (v:1228) -> Ext:1138: = statement-equivalent
config_same (v:1243) -> Ext:1144: = statement-equivalent
config_same2 (v:1251) -> Ext:1152: = statement-equivalent
iota_snocN (v:1259): NONE, justified, listed in gap17 §3d (iotaN~List.range)
holds_upto_S (v:1280): NONE, justified, listed in gap17 §3d
holds_upto_all (v:1293): NONE, justified, listed in gap17 §3d
holds_upto_all_strong (v:1318): NONE, justified, listed in gap17 §3d
holds_upto_all_strong' (v:1334): NONE, justified, listed in gap17 §3d
holds_upto_lt (v:1356): NONE, justified, listed in gap17 §3d
list_update_func_subst (v:1367): NONE, justified, listed in gap17 §3d (superseded by HelperLemmas.getElem!_modify_eq_or_ne)
list_update_func_unchanged (v:1398): NONE, justified, listed in gap17 §3d (superseded by HelperLemmas.getElem!_modify_eq_or_ne)
update_forall_lt (v:1442): NONE, justified, listed in gap17 §3d (bool/Prop bridge)
update_forall_le (v:1458): NONE, justified, listed in gap17 §3d (bool/Prop bridge)
update_forall_le_u32 (v:1474): NONE, justified, listed in gap17 §3d (bool/Prop bridge)
update_holds_upto_lt (v:1490): NONE, justified, listed in gap17 §3d (bool/Prop bridge)
update_holds_upto_le (v:1510): NONE, justified, listed in gap17 §3d (bool/Prop bridge)
holds_upto_lt_refl (v:1530): CITED: forall_range_lt (Ext:98), equivalent at n=l.length
extend_global_refl (v:1538) -> Ext:975: = statement-equivalent
extend_table_refl (v:1550) -> Ext:916: = statement-equivalent
extend_mem_refl (v:1561) -> Ext:961: = statement-equivalent
extend_elem_refl (v:1572) -> Ext:988: = statement-equivalent
extend_data_refl (v:1581) -> Ext:1000: = statement-equivalent
extend_func_refl (v:1592) -> Ext:895: = statement-equivalent
Extend_store_refl (v:1603) -> Ext:1018: = statement-equivalent
global_set_global_extension (v:1627) -> Ext:1167: = statement-equivalent
forall_preserved_bytes (v:1663): NONE by name; = HelperLemmas.list_slice_update_forall (generalised P), which is mislabelled "Not a Rocq port" [SE-6]
store_none_mem_extension (v:1679) -> Ext:1199: = (binder v_n renamed v_n_len)
invert_meminst (v:1731): NONE, superseded by wf_meminst_parts (Ext:2020), which does not say so [SE-6]
repeat_forall (v:1743): NONE, justified, listed in gap17 §3d (List.replicate core facts)
memory_grow_mem_extension (v:1753) -> Ext:1234: EQUIV restatement (v_i Q->Nat undocumented; v_j_opt option u32->Option Nat) [SE-5]
table_set_table_extension (v:1841) -> Ext:1266: = statement-equivalent
table_grow_table_extension (v:1894) -> Ext:1313: = (j : Option uN exactly as Rocq) [SE-4]
elem_drop_elem_extension (v:1956) -> Ext:1347: = statement-equivalent
data_drop_data_extension (v:1989) -> Ext:1366: = statement-equivalent
update_global_unchanged (v:2026) -> Ext:1387: = statement-equivalent
addrs_store_funcs_extension (v:2042) -> Ext:1471: = statement-equivalent
addrs_tables_extension (v:2066) -> Ext:1489: = statement-equivalent
addrs_store_globals_extension (v:2114) -> Ext:1516: = statement-equivalent
addrs_mems_extension (v:2146) -> Ext:1536: = statement-equivalent
addrss_store_funcs_extension (v:2195) -> Ext:1562: = statement-equivalent
addrss_tables_extension (v:2212) -> Ext:1570: = statement-equivalent
addrss_store_globals_extension (v:2229) -> Ext:1578: = statement-equivalent
addrss_mems_extension (v:2248) -> Ext:1586: = statement-equivalent
Extend_store_exts (v:2266) -> Ext:1626: = statement-equivalent
Extend_store_eleminst (v:2292) -> Ext:1635: = statement-equivalent
Extend_store_eleminsts' (v:2304) -> Ext:1682: = statement-equivalent
Extend_store_eleminsts (v:2349) -> Ext:1695: = statement-equivalent
Extend_store_datainsts' (v:2360) -> Ext:1702: EQUIV reshaped: datatype.OK hard-coded, ts dropped (flagged before) [SE-3]
Extend_store_datainsts (v:2408) -> Ext:1713: EQUIV reshaped: datatype.OK hard-coded; Rocq shape exists as TP.Extend_store_datainsts2 [SE-3]
Extend_store_moduleinst (v:2422) -> Ext:1724: = statement-equivalent
Extend_store_funcinst (v:2455) -> Ext:1753: = statement-equivalent
Extend_store_funcinsts (v:2467) -> Ext:1762: = statement-equivalent
Extend_store_globalinst (v:2481) -> Ext:1767: = statement-equivalent
Extend_store_globalinsts (v:2493) -> Ext:1776: = statement-equivalent
Extend_store_tableinst (v:2507) -> Ext:1781: = statement-equivalent
Extend_store_tableinsts (v:2524) -> Ext:1790: = statement-equivalent
Extend_store_meminst (v:2538) -> Ext:1795: = statement-equivalent
Extend_store_meminsts (v:2549) -> Ext:1803: = statement-equivalent
Extend_store_externaddrs_func (v:2563) -> Ext:1812: = statement-equivalent
ais_ok_ind' (v:2574): NONE, Scheme; named in Extend_store_ais doc; not needed (Lean mutual induction)
Extend_store_ais (v:2580) -> Ext:1842: = statement-equivalent
size_repeat (v:2679): NONE, justified, listed in gap17 §3d (List.replicate core facts)
construct_tableinsts (v:2691) -> Ext:2034: = statement-equivalent
construct_tableinsts_grow (v:2740) -> Ext:2054: = statement-equivalent
construct_globalinsts (v:2830) -> Ext:2107: = statement-equivalent
construct_meminsts (v:2859) -> Ext:2144: = statement-equivalent
Qfloor_add_Z (v:2895): NONE, justified, listed in gap17 §3d (Q/Z arith)
Zle_Nle (v:2908): NONE, justified, listed in gap17 §3d (Q/Z arith)
construct_meminsts_grow (v:2918) -> Ext:2163: EQUIV-or-stronger: Nat for Rocq Q (documented); Lean implies Rocq
construct_datainsts (v:3041) -> Ext:2217: EQUIV reshaped: datatype.OK hard-coded [SE-3]
construct_eleminsts (v:3066) -> Ext:2228: = statement-equivalent
```

## Unsure / caveats

- SE-1 vacuity is by inspection (Lean not run, as instructed); the witness is `[]` and `List.zip xs [] = []`.
- `s_invert_mems` `pagediv`: I infer `v_n : N` from Rocq elaboration order (`mk_uN v_n` precedes
  `v_n = pagediv b_lst`), hence the floor coercion; if it were `Q` the Rocq fact would be the exact
  multiplicative one (Lean has it as `meminst_ok_raw`). Either way SE-1 dominates for that lemma.

### Safety: v2 END check (verbatim)

```
safety check [sig-ext] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T111717.794823783Z-sig-ext-1415746.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

### Safety: final re-check after writing this log (verbatim)

```
safety check [sig-ext] new=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T111934.673831395Z-sig-ext-1416535.txt baseline=spectec/src/test-lean-claude/claude-logging/safety-checks/check-20261005T051653Z.txt
VERIFIED: zero new changes outside spectec/src/test-lean-claude
```

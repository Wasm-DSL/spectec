# bundle33: generate the old-vs-new diff report from the machine data (no table is typed by hand).
import json, re, collections, hashlib, sys, os
B = sys.argv[1]; OUT = sys.argv[2]
J = lambda p: json.load(open(f'{B}/{p}'))
diff = J('work/diff33.json'); cm = J('work/ctor_map33.json'); edits = J('work/edits33.json')
envd = J('work/envdiff33.json'); envc = J('work/envcat33.json')
rows = diff['rows']; summ = diff['summary']
MODS = ['ExtendedDeriveDecEq', 'wasm2.0', 'HelperLemmas', 'Subtyping', 'TypingLemmas', 'TypePreservationPure',
        'ExtensionLemmas', 'TypePreservation', 'TypeProgress']
md5 = lambda p: hashlib.md5(open(p, 'rb').read()).hexdigest()
meaning = cm['wf_admininstr']['instr_of_old_ctor']
def esc(s): return s.replace('|', '\\|')
def code(s): s = s.strip(); return '`` ' + s + ' ``' if '`' in s else '`' + s + '`'
L = []; w = L.append
# ---------------------------------------------------------------- header
w('# Old vs new: the `EXTEND` removal across the model and the proof\n')
w('Bundle 33, 2026-11-11. Compares two complete states of `spectec/src/test-lean-claude/`:\n')
w('- **OLD**: the old proof together with `OLD_wasm2.0.lean`, the model that still has `EXTEND`. This is HEAD `afb06bf8d`: its `wasm2.0.lean` is byte-identical to `OLD_wasm2.0.lean`.')
w('- **NEW**: the new proof together with `wasm2.0.lean`, i.e. the files now in the working tree. The model is the bundle32 port; the proof modules are as repaired this turn.\n')
w('| module | OLD md5 | NEW md5 | lines OLD → NEW |')
w('|---|---|---|---|')
for m in MODS:
    a, b = md5(f'{B}/old/src/{m}.lean'), md5(f'{B}/final/src/{m}.lean'); s = summ[m]
    w(f'| `{m}.lean` | `{a[:8]}…` | `{b[:8]}…`{" (same)" if a == b else ""} | {s["old_lines"]:,} → {s["new_lines"]:,} |')
w('\nOLD\'s `wasm2.0.lean` is `OLD_wasm2.0.lean`; NEW\'s is `wasm2.0.lean`. All counts and tables below are generated from the files and from Lean, by the scripts listed in §9.\n')
# ---------------------------------------------------------------- 0. bottom line
n_rows = len(rows); n_model = sum(1 for r in rows if r['file'] == 'wasm2.0'); n_down = n_rows - n_model
cats = collections.Counter((r['file'] == 'wasm2.0', r['cat']) for r in rows)
w('## 0. Bottom line\n')
w(f'- **One cause.** The mech-backend merge deleted one line of the Wasm 2.0 spec: the dead instruction `EXTEND numtype n`. Every difference below follows from that.')
w(f'- **Text.** {n_rows} lines of OLD differ from NEW: {n_model} in the model and {n_down} in the proof modules. Every one falls into four kinds, and none is unexplained:')
w(f'  - {cats[(True, "EXTEND-removed")] + cats[(False, "EXTEND-removed")]} lines deleted, because they mention the removed constructor: {cats[(True, "EXTEND-removed")]} in the model and {cats[(False, "EXTEND-removed")]} match arms in `TypingLemmas`.')
w(f'  - {cats[(True, "ctor-renumber/generated")] + cats[(True, "ctor-renumber/hand-layer")] + cats[(False, "ctor-renumber/proof-module")]} lines renumber a well-formedness constructor name, `instr_case_K`/`admininstr_case_K` → K−1 for K ≥ 20:')
w(f'    - {cats[(True, "ctor-renumber/generated")]} in the generated model;')
w(f'    - {cats[(True, "ctor-renumber/hand-layer")]} in the model\'s proofs (the bundle32 port);')
w(f'    - {cats[(False, "ctor-renumber/proof-module")]} in the proof modules.')
w(f'  - {cats[(True, "source-location")]} generated comments cite a spec position, and that position moves up one line.')
w('- **Structure.** No top-level construct was added, removed, renamed or reordered in any of the nine files. The 1,869 constructs match OLD one for one. 53 of them have changed text: 24 in code and 29 only in their source-position comment.')
w('- **Statements.** No theorem, definition or inductive type changed its statement. This is checked in Lean, by comparing all 12,775 declarations common to both builds, with the constructor numbers mapped (§5).')
w('  - The constructor `EXTEND` itself is gone, from `instr` and `admininstr`, together with its two well-formedness cases.')
w('  - The only other declarations that changed are ones Lean generates automatically.')
w('- **Soundness.** Both states compile with 0 errors and 0 `sorry`, and no theorem depends on `sorryAx`.')
w('  - Every theorem present in both has the same axioms. `t_preservation` has 35 and `t_progress` 74, the same lists as before.')
w('  - The `Inhabited`-default audit finds no theorem needing a default: 0 of 5,517 (OLD) and 0 of 5,496 (NEW).')
w('  - The warnings are the same 171 messages in both.\n')
# ---------------------------------------------------------------- 1. summary table
w('## 1. Line-level summary\n')
w('| file | lines OLD → NEW | deleted (`EXTEND`) | constructor renumbered | spec position comment | total OLD lines differing |')
w('|---|---|---|---|---|---|')
for m in MODS:
    s = summ[m]; dl = s.get('EXTEND-removed', 0); rn = sum(v for k, v in s.items() if k.startswith('ctor-renumber')); sl = s.get('source-location', 0)
    extra = ''
    if m == 'wasm2.0': extra = f' ({s.get("ctor-renumber/generated", 0)} generated + {s.get("ctor-renumber/hand-layer", 0)} hand layer)'
    w(f'| `{m}.lean` | {s["old_lines"]:,} → {s["new_lines"]:,} | {dl} | {rn}{extra} | {sl} | {dl + rn + sl} |')
w(f'| **total** | | {sum(summ[m].get("EXTEND-removed", 0) for m in MODS)} | {sum(v for m in MODS for k, v in summ[m].items() if k.startswith("ctor-renumber"))} | {sum(summ[m].get("source-location", 0) for m in MODS)} | **{n_rows}** |')
w('\nHow the lines were matched:')
w('- From each OLD file, delete the lines that mention the removed constructor (§3.1, §4.1).')
w('- The remaining lines then align one for one with the NEW file, which has exactly the same length.')
w('- Each differing pair is classified by the rule that maps it, so no line-matching heuristic is involved. 0 pairs are left unexplained.')
w('- Four modules are byte-identical in OLD and NEW: `ExtendedDeriveDecEq`, `HelperLemmas`, `Subtyping` and `ExtensionLemmas`.\n')
# ---------------------------------------------------------------- 2. cause
w('## 2. The cause\n')
w('**The spec change.** mech-backend commit `28073cddd` ("Remove extend instruction") deleted line 474 of `specification/wasm-2.0/1-syntax.spectec`:')
w('```\n  | EXTEND numtype n                 hint(show %.EXTEND#%#_#S)\n```')
w('**No other generator change matters.** In bundle32 the HEAD generator was run on the spec with only that line restored. It reproduced the old generated base byte for byte. So the merge\'s other generator changes have no effect on the Wasm 2.0 Lean output: the ImproveIds name-clash fix, the Sideconditions let-reordering and DefToRel\'s `hint(axiom)`. (Evidence: `bundle32/evidence/outputs/generator_check.txt`.)\n')
w('**What the instruction was.** In Wasm 2.0 terms, `instr.EXTEND numtype n` was a dead production. In OLD:')
w('- it is mentioned only by the five generated lines of §3.1 and by two match arms in `TypingLemmas`;')
w('- no validation rule mentions it. `Instr_ok` has 73 rules in both versions;')
w('- no reduction rule mentions it. `Step_pure`, `Step_read` and `Step` have 54, 47 and 23 rules in both versions.\n')
w('**The real extension instructions are unaffected.** They live under other constructors, all unchanged:')
w('- `i32.extend8_s` and the like are `UNOP` with `unop_Inn.EXTEND n`;')
w('- `i64.extend_i32_s/u` is `CVTOP` with `cvtop__Inn_1_Inn_2.EXTEND sx`;')
w('- the SIMD extensions are `VCVTOP` with `vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND half sx`.\n')
w('**Why so many names moved.** The backend names the constructors of the generated well-formedness predicates by position. The K-th constructor (from 0) of `wf_instr` is `instr_case_K`, and likewise `admininstr_case_K` for `wf_admininstr`. `EXTEND` was constructor 19 of both `instr` and `admininstr`, so every later case moved down by one:')
w('- `wf_instr`: 68 → 67 cases;')
w('- `wf_admininstr`: 74 → 73 cases.\n')
w('The two predicates share numbering for K ≤ 67. The six administrative-only instructions are `admininstr_case_68`–`73` in OLD.')
w('The renaming was done by meaning, not by arithmetic. Each OLD constructor was matched to the NEW constructor with an identical text: arguments, premises and conclusion. Every case was matched uniquely (67 of 67 and 73 of 73), with nothing ambiguous and nothing unmatched.\n')
# ---------------------------------------------------------------- 3. model
w('## 3. The model: `OLD_wasm2.0.lean` → `wasm2.0.lean` (%d lines)\n' % n_model)
w('### 3.1 Deleted: the five lines that mention `EXTEND`\n')
w('| OLD line | construct | deleted line |'); w('|---|---|---|')
for r in rows:
    if r['file'] == 'wasm2.0' and r['cat'] == 'EXTEND-removed': w(f'| {r["old"]} | `{r["kind"]} {r["construct"]}` | {code(esc(r["before"]))} |')
w('')
w('### 3.2 Renumbered constructor declarations in the generated model (%d lines)\n' % cats[(True, 'ctor-renumber/generated')])
w('Each line declares one constructor of `wf_instr` or `wf_admininstr`. Only the name changed; the rest of each declaration is identical. The full map, with the instruction each case is about:\n')
w('| OLD → NEW | instruction | in `wf_instr` | in `wf_admininstr` |'); w('|---|---|---|---|')
gen_lines = {}
for r in rows:
    if r['cat'] == 'ctor-renumber/generated':
        mm = re.match(r'\s*\| ((?:admin)?instr_case)_(\d+)', r['before']); gen_lines[(mm.group(1), int(mm.group(2)))] = (r['old'], r['new'])
w('| `*_case_0` … `*_case_18` | (unchanged) | 19 cases, same names | 19 cases, same names |')
w('| `*_case_19` | **`EXTEND`, deleted** (§3.1) | OLD line %d | OLD line %d |' % (
    [r['old'] for r in rows if r['cat'] == 'EXTEND-removed' and 'wf_instr' in r['before']][0],
    [r['old'] for r in rows if r['cat'] == 'EXTEND-removed' and 'wf_admininstr' in r['before']][0]))
for k in range(20, 74):
    a = gen_lines.get(('instr_case', k)); b = gen_lines.get(('admininstr_case', k))
    ins = f'line {a[0]} → {a[1]}' if a else '—'; adm = f'line {b[0]} → {b[1]}' if b else '—'
    w(f'| `_case_{k}` → `_case_{k - 1}` | `{meaning[f"admininstr_case_{k}"]}` | {ins} | {adm} |')
assert len(gen_lines) == cats[(True, 'ctor-renumber/generated')] == 48 + 54
w(f'\n{sum(1 for k in gen_lines if k[0] == "instr_case")} `wf_instr` lines + {sum(1 for k in gen_lines if k[0] == "admininstr_case")} `wf_admininstr` lines = {len(gen_lines)}. No other generated line refers to these constructors.\n')
w('### 3.3 Source-position comments (%d lines)\n' % cats[(True, 'source-location')])
w('The generator heads some constructs with a comment that gives the spec position they come from. Every `1-syntax.spectec:L.c` with L ≥ 475 now reads L−1, because one spec line above it was deleted. The %d affected comments head these constructs, listed with OLD → NEW line:\n' % cats[(True, 'source-location')])
locs = [r for r in rows if r['cat'] == 'source-location']
w(', '.join(f'`{r["construct"]}` ({r["old"]}→{r["new"]})' for r in locs) + '.\n')
ex = locs[0]; w(f'Example (`{ex["construct"]}`): {code(ex["before"])} → {code(ex["after"])}.\n')
w('### 3.4 The model\'s proofs: renumbered references (%d lines)\n' % cats[(True, 'ctor-renumber/hand-layer')])
w('These are the deviations of the bundle32 port. Every one renames a `wf_admininstr` constructor inside a proof body; no statement changed. They are logged line by line in `bundle32/user_requested_documents/deviations_in_copying.md` and listed again in Appendix A.\n')
w('| construct | lines | renamings (OLD → NEW, instruction × lines) |'); w('|---|---|---|')
agg = collections.OrderedDict()
for r in rows:
    if r['cat'] != 'ctor-renumber/hand-layer': continue
    for fam, k in re.findall(r'\b((?:admin)?instr_case)_(\d+)\b', r['before']):
        if int(k) >= 20: agg.setdefault(r['construct'], collections.Counter())[(int(k), meaning[f'admininstr_case_{k}'])] += 1
for c, v in agg.items():
    w(f'| `{c}` | {sum(v.values())} | ' + ', '.join(f'{k}→{k - 1} `{mn}` ×{n}' for (k, mn), n in sorted(v.items())) + ' |')
w('')
# ---------------------------------------------------------------- 4. proof modules
w('## 4. The proof modules (%d lines)\n' % n_down)
w('Line numbers are OLD → NEW. The error column shows what Lean reports for the OLD line against the NEW model. Each module was compiled with the earlier modules already repaired.\n')
errs = {}
for m in ['TypingLemmas', 'TypePreservationPure', 'TypePreservation', 'TypeProgress']:
    for p in [f'{B}/unrep/logs/{m}.log'] + ([f'{B}/unrep/logs/TypePreservationPure_only1072fixed.log'] if m == 'TypePreservationPure' else []):
        txt = open(p).read()
        txt = re.sub(r'\n?WALL [^\n]*$', '', txt.rstrip())
        for blk in re.split(r'\n(?=\S+\.lean:\d+:\d+: )', txt):
            mm = re.match(r'\S+\.lean:(\d+):\d+: error[^:]*: (.*)', blk, re.S)
            if mm:
                msg = re.sub(r'\s+', ' ', mm.group(2)).strip()
                errs.setdefault((m, int(mm.group(1))), []).append(msg if len(msg) <= 260 else msg[:257] + '…')
first_unrep = open(f'{B}/new/logs_unrepaired/TypingLemmas.log').read()
w('### 4.1 Deleted: two match arms on the removed constructor\n')
w('| module | OLD line | construct | deleted line | why |'); w('|---|---|---|---|---|')
why = {'instr_of': '`instr_of : admininstr → Option instr` is the partial inverse of `admininstr_instr`, from Rocq `typing_lemmas.v:124`. It has one arm per `admininstr` constructor (74 in OLD, 73 in NEW); the `EXTEND` arm no longer type-checks.',
       'ai_principal_typing': '`ai_principal_typing` gives the principal type of an administrative instruction. Its `EXTEND` arm said `False`. With the constructor gone, the arm is an invalid pattern.'}
for e in edits:
    if e['kind'] == 'delete':
        msg = re.search(r'TypingLemmas\.lean:%d:\d+: error: (.*)' % e['line'], first_unrep).group(1)
        w(f'| `{e["module"]}` | {e["line"]} | `def {e["owner"]}` | {code(esc(e["before"]))} | {why[e["owner"]]} Lean: "{esc(msg)}" |')
w('')
w('### 4.2 Renumbered constructor references (15 lines)\n')
ctx = {
 'instr_typing_inversion': 'Inverts `Instr_ok` into the principal type. The `vconst` case destructs `wf_instr (VCONST …)`.',
 'construct_ai_val': 'Types a value as an administrative instruction. The vector case builds `wf_instr (VCONST V128 c)`.',
 'construct_ais_trap': '`TRAP` has every type. It needs `wf_admininstr TRAP`.',
 'Step_pure__local_tee_preserves': 'Preservation for `local.tee x` ↪ `val val local.set x`. It destructs `wf_admininstr (LOCAL_TEE x)` and builds `wf_instr (LOCAL_SET x)`.',
 'wf_vconst_parts': 'Destructs `wf_admininstr (VCONST vt c)` into its two premises.',
 't_read_preservation': 'Preservation of `Step_read`, `call_addr` case (a function call becomes `FRAME_ n f [LABEL_ n [] body]`). It destructs the well-formedness of that `FRAME_` to reach the `LABEL_` inside.',
 'wf_forall_admin_val': 'Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`.',
 'wf_config_label': 'Rocq `type_progress.v:857`. It destructs `wf_admininstr (LABEL_ n bes es)`.',
 'wf_config_frame': 'Rocq `type_progress.v:870`. It destructs `wf_admininstr (FRAME_ n f es)`.',
 't_progress_e_Instr_ok2_frame': 'Progress, frame case. The body is well formed under the inner frame, by destructing `wf_admininstr (FRAME_ …)`.'}
w('| module | line OLD → NEW | construct | change | instruction | role of the line | error without the change |'); w('|---|---|---|---|---|---|---|')
for e in edits:
    if e['kind'] != 'rename': continue
    newline = e['line'] - (2 if e['module'] == 'TypingLemmas' and e['line'] > 454 else (1 if e['module'] == 'TypingLemmas' and e['line'] > 131 else 0))
    ch = '; '.join(f'`{o}` → `{n}`' for o, n, _ in e['renames']); ins = ', '.join(sorted({mn for _, _, mn in e['renames']}))
    er = errs.get((e['module'], newline if e['module'] == 'TypingLemmas' else e['line']), [])
    er = [x for x in er] or ['(none of its own; see note)']
    w(f'| `{e["module"]}` | {e["line"]} → {newline} | `{e["owner"]}` | {ch} | `{ins}` | {ctx[e["owner"]]} | {esc(" / ".join(dict.fromkeys(er)))} |')
w('\nWhere two OLD lines are listed, Lean also reports the neighbouring missing alternative: "Alternative `…_{K−1}` has not been provided". The error for `TypePreservationPure` line 1085 only shows once line 1072 is fixed, because it sits inside that alternative: "Type mismatch: `wf_instr.instr_case_44 v_x hwfl` has type `wf_instr (instr.LOCAL_TEE v_x)` but is expected to have type `wf_instr (instr.LOCAL_SET v_x)`".')
w('\nIn the `TypingLemmas` run behind this table, only the two arms of §4.1 had been deleted, so its line numbers are already the NEW ones. In the first compile of the unrepaired module, the two invalid patterns made `instr_of` and `ai_principal_typing` fail. That cascaded into 80 errors, including the `rfl` failures in `instr_of_admininstr_instr`, and hid line 570 (`instr_typing_inversion` became a `sorry` declaration).\n')
w('Nothing else in the four modules mentions a renumbered constructor or the removed one. The other two `EXTEND` tokens in `TypeProgress` (lines 3496 and 3705) are the SIMD conversion `vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND`, which still exists.\n')
# ---------------------------------------------------------------- per construct
w('## 5. Lean-level comparison (elaborated declarations)\n')
w('**How.** Both builds were loaded in Lean, and every declaration of the nine modules was dumped with three things: a hash of its type, a hash of its value (both ignore binder names) and, for theorems, its axioms. In the OLD dump the constructors `wf_instr.instr_case_K` and `wf_admininstr.admininstr_case_K` with K ≥ 20 were first renamed to K−1, together with the same constructors of their `.below`, and the removed case was marked. The comparison is therefore by meaning.\n')
w('**Totals.**')
w(f'- OLD has 12,818 declarations (5,526 theorems); NEW has 12,787 (5,505 theorems).')
w(f'- {12818 - len(envd["only_old"]):,} are common to both.')
w(f'- {len(envd["only_old"])} are only in OLD and {len(envd["only_new"])} only in NEW.\n')
def catlist(k):
    c = envc[k]['categories']; return '; '.join(f'{v} {lab}' for lab, v in sorted(c.items(), key=lambda x: -x[1]))
w(f'- **Removed ({len(envd["only_old"])}).**')
w('  - User-visible (4): `instr.EXTEND`, `admininstr.EXTEND`, and the `EXTEND` cases of `wf_instr` and `wf_admininstr`.')
w('  - The rest are generated by Lean: the removed constructors\' `elim`/`inj`/`injEq`/`noConfusion`/`sizeOf_spec`, their `.below` cases, the `DecidableEq` sub-proofs, and the equation lemma for the deleted arm of `admininstr_instr`, `instr_of` and `ai_principal_typing` (`eq_68`, `eq_74`, `eq_56`).')
w('  - Also removed are trailing members of numbered auxiliary families (`_proof_N`, `_simp_N`, `match_N.eq_N`) and of hygienic helper names, which shrink by one. By category: ' + catlist('only_old') + '. Full list in Appendix B.')
w(f'- **Added ({len(envd["only_new"])}).** All are renumbered auxiliaries: hygienic name counters, and auxiliary proof and simp lemma numbering. No new user-level declaration and no new axiom. ' + catlist('only_new') + '.')
w(f'- **Statements: none changed.** No user-level theorem, definition, inductive type or constructor has a different type. The {len(envd.get("type_changed_thm", []))} theorems, {len(envd.get("type_changed_def", []))} definitions and {len(envd.get("type_changed_rec", []))} recursors with a different type are all generated by Lean:')
w('  - recursors and case eliminators of the four changed inductives, which have one minor premise fewer;')
w('  - per-constructor `X.CTOR.elim` of the constructors after `EXTEND`;')
w('  - positionally numbered equation lemmas, matcher and splitter auxiliaries;')
w('  - `DecidableEq` sub-proofs.')
ud = envc['value_changed_def']['user_level']
w(f'- **Definitions whose elaborated value changed ({len(envd["value_changed_def"])}; {len(ud)} user-level).**')
w('  - `admininstr_instr`, `instr_of` and `ai_principal_typing` each lost their `EXTEND` arm.')
w('  - `br_reduce_decidable` and `return_reduce_decidable` (`TypeProgress`) have unchanged source, but they case-split on an `admininstr` with a `| _ =>` wildcard, so their terms now have one case fewer.')
w('  - The rest are derived or auxiliary: ' + catlist('value_changed_def').replace('; 5 USER-LEVEL (listed)', '') + '.')
ut = envc['value_changed_thm']['user_level']
edited = {e['owner'] for e in edits if e['kind'] == 'rename'} | set(agg)
same = sorted(t for t in edited if ('TLC.' + t) not in ut and t not in ut)
w(f'- **Proof terms that changed: {len(ut)} user-level theorems** (list in Appendix B). Most have unchanged source. Their proofs destruct an `instr`/`admininstr` or its well-formedness, or run a tactic over every case, and that now produces one case fewer.')
w(f'  - Of the 17 theorems edited in §3.4 and §4.2, these {len(same)} have the same proof term as before once constructor numbers are mapped: ' + ', '.join(f'`{t}`' for t in same) + '.')
w('  - The edits in these theorems were pure renamings.')
w('- **Axioms: unchanged.**')
w('  - Every theorem present in both builds has the same set of axioms.')
w('  - The only 4 differences are numbered auxiliaries, `br_reduce_decidable._proof_81/82/120/124`, whose numbers now point at other sub-proofs.')
w('  - `TLC.t_preservation` uses 35 axioms: `propext`, `Classical.choice`, `Quot.sound` and 32 of the model\'s `*_is_wf` axioms.')
w('  - `TLC.t_progress` uses 74: the same three, 56 `*_is_wf` axioms and 15 project axioms from Rocq\'s `axioms.v`.')
w('  - Both lists are identical in OLD and NEW, and no theorem depends on `sorryAx` in either.')
w('- **`Inhabited` defaults.** This is the kernel replay of all eight project modules with every `Inhabited` instance opaque.')
w('  - OLD: 0 of 5,517 theorems need a default value.')
w('  - NEW: 0 of 5,496 theorems need one.')
w('  - The difference of 21 theorems is exactly the removed minus the added theorems above.\n')
# ---------------------------------------------------------------- 6. per-construct table
w('## 6. Every top-level construct whose text changed\n')
w('All nine files have the same top-level constructs in the same order in OLD and NEW: 897, 24, 118, 52, 97, 85, 135, 143 and 318. The 53 constructs with changed text:\n')
w('| file | construct | change |'); w('|---|---|---|')
pc = collections.OrderedDict()
for r in rows: pc.setdefault((r['file'], r['kind'], r['construct']), collections.Counter())[r['cat']] += 1
lab = {'EXTEND-removed': 'line(s) mentioning `EXTEND` deleted', 'ctor-renumber/generated': 'constructor declarations renumbered',
       'ctor-renumber/hand-layer': 'constructor references renumbered in the proof', 'ctor-renumber/proof-module': 'constructor references renumbered in the proof',
       'source-location': 'spec position in the header comment'}
for (f, k, c), v in pc.items():
    if set(v) == {'source-location'}: continue
    w(f'| `{f}` | `{k} {c}` | ' + '; '.join(f'{lab[x]} ({n})' for x, n in v.items()) + ' |')
only_loc = [c for (f, k, c), v in pc.items() if set(v) == {'source-location'}]
w(f'| `wasm2.0` | {len(only_loc)} more constructs: ' + ', '.join(f'`{c}`' for c in only_loc) + ' | spec position in the header comment (1 line each) |')
w('')
# ---------------------------------------------------------------- 7. builds
w('## 7. Builds\n')
w('Both states were compiled from scratch in the scratchpad, one Lean process at a time (12 GB cap), with the toolchain\'s `lean` v4.32.0 called directly. The repo\'s `.lake/build` was not used. The NEW error and warning counts are from the fresh build of the installed repo files.\n')
def chain(p):
    d = {}
    for l in open(p):
        mm = re.match(r'(\w+) (\S+) rc=(\d+) errors=(\d+) warnings=(\d+) sorry-warnings=(\d+) olean=(\w+) WALL ([\d.]+) s  MAXRSS (\d+) KB', l)
        if mm: d[mm.group(2)] = mm.groups()
    return d
co, cn = chain(f'{B}/logs/chain_old.txt'), chain(f'{B}/logs/chain_final_from_repo.txt')
cs = chain(f'{B}/logs/chain_new_unrepaired.txt'); cs.update(chain(f'{B}/logs/chain_new_repaired_1.txt'))
w('| module | errors OLD / NEW | `sorry` warnings OLD / NEW | warnings OLD / NEW | time (s): OLD / NEW scratch / NEW repo |'); w('|---|---|---|---|---|')
for m in MODS:
    a, b, c = co[m], cn[m], cs[m]
    assert c[3] == b[3] == '0' and c[4] == b[4]
    w(f'| `{m}` | {a[3]} / {b[3]} | {a[5]} / {b[5]} | {a[4]} / {b[4]} | {float(a[7]):.0f} / {float(c[7]):.0f} / {float(b[7]):.0f} |')
w('\nThe warnings are the same 171 messages in OLD and NEW; only their line numbers move, where lines were deleted above them. They are 94 unused variables, 51 Mathlib naming-convention lints and 26 other linter suggestions (tactics that do nothing, unused `simp` arguments, `Try this` hints).')
w('"NEW scratch" is the build in which the repair was made; "NEW repo" is the fresh build of the installed files, which are byte-identical to it. Times vary with machine load (the editor\'s Lean servers were running throughout) and are not a property of the change. Peak memory was about 4.8 GB, in `TypeProgress`.\n')
# ---------------------------------------------------------------- 8. notes
w('## 8. Left unchanged, and other notes\n')
w('- **Comments that count instructions.** Five comments in `TypingLemmas` still say 68 where `instr` now has 67 constructors. They are at NEW lines 187 ("68-case transcription"), 1477, 1480 and 1482 ("each of `instr`\'s 68 constructors", "68×68 cases", "the 68×68 case bash") and 1690 ("the other 68").')
w('  - I left them as they were: they are comments, and line 1482 records a past measurement.')
w('  - Line 772 ("Rocq destructs both instructions (68×68)") describes Rocq and is still accurate.')
w('  - Line 197 ("all 73 cases") counts `Instr_ok` rules, which are still 73.')
w('- **The word `sorry` in comments.** No code contains `sorry`, but the word appears in comments:')
w('  - in `wasm2.0.lean`, the commented-out generated originals `--   sorry` at lines 15430 and 15563, as in bundle32;')
w('  - in status notes saying a module has no `sorry`: `TypePreservationPure` line 18, `TypePreservation` lines 19 and 2024, `TypeProgress` lines 47 and 51.')
w('  - So a plain `grep sorry` over the nine modules finds 7 lines, and none is a proof hole. (`OLD_wasm2.0.lean` has the same two commented-out lines.)')
w('- **Untouched files.** `wasm2.0.lean` and `OLD_wasm2.0.lean` were not modified this turn. Neither were `ExtendedDeriveDecEq`, `HelperLemmas`, `Subtyping` or `ExtensionLemmas`.')
w('- **Cross-check with the trial port.** All nine NEW files are byte-identical to `spectec/src/temp_port_reference/trial_port/`. That port was made outside this log by a patch-based procedure; I compared only after my own result compiled.')
w('- **`lake build`.** I didn\'t run it, because it writes `.lake/build`. That directory is stale, so the next `lake build` or editor session rebuilds all nine modules, which takes about 2–3 minutes. Until then, the editor may show errors in modules that import the new `wasm2.0`.\n')
# ---------------------------------------------------------------- 9. method
w('## 9. Method and evidence\n')
w('Everything is in `claude-logging/verbatim_dialogue_log/bundle33/evidence/`:')
w('- `tools/`:')
w('  - `scan33.py`: finds every affected code reference, by constructor meaning;')
w('  - `apply33.py`: applies the 17 edits, checking each expected line;')
w('  - `diff33.py`: does the line accounting of §1, §3, §4 and §6;')
w('  - `EnvDump33.lean`, `envdiff33.py` and `envcat33.py`: the Lean-level comparison of §5;')
w('  - `RunAudit33.lean`: the `Inhabited` audit;')
w('  - `chain33.sh`, `lrun33.sh` and `check33.sh`: the serial build and the safety checks;')
w('  - `report33.py`: generates this report.')
w('- `outputs/`:')
w('  - build logs of OLD, of NEW before repair, of NEW after repair and of the fresh repo build;')
w('  - the error logs of the unrepaired modules;')
w('  - `diff33_all_changed_lines.tsv`, with all 211 lines;')
w('  - unified diffs `*.diff`;')
w('  - the constructor map;')
w('  - the declaration dumps (`dump_old.tsv.gz`, `dump_new.tsv.gz`) and their comparison (`envdiff33.json`, `envcat33.json`);')
w('  - the audit outputs.\n')
# ---------------------------------------------------------------- appendices
w('## Appendix A. All %d changed lines of the model\'s proofs (§3.4)\n' % cats[(True, 'ctor-renumber/hand-layer')])
w('| OLD → NEW line | construct | OLD text → NEW text |'); w('|---|---|---|')
for r in rows:
    if r['cat'] == 'ctor-renumber/hand-layer':
        b = r['before'].strip(); a = r['after'].strip()
        w(f'| {r["old"]} → {r["new"]} | `{r["construct"]}` | {code(esc(b))} → {code(esc(a))} |')
w('')
w('## Appendix B. Lean-level lists (§5)\n')
w(f'**Only in OLD ({len(envd["only_old"])}):** ' + ', '.join(f'`{n}`' for n in envd['only_old']) + '.\n')
w(f'**Only in NEW ({len(envd["only_new"])}):** ' + ', '.join(f'`{n}`' for n in envd['only_new']) + '.\n')
mods_of = {}
for p in ['dump_new.tsv']:
    for l in open(f'{B}/probes/{p}'):
        f = l.rstrip('\n').split('\t')
        if len(f) == 6: mods_of[f[2]] = f[0]
byM = collections.OrderedDict()
for n in ut: byM.setdefault(mods_of.get(n, '?'), []).append(n)
w(f'**User-level theorems whose elaborated proof term changed ({len(ut)}), by module:**\n')
for m in sorted(byM, key=lambda x: MODS.index(x.strip('«»')) if x.strip('«»') in MODS else 99):
    w(f'- `{m}` ({len(byM[m])}): ' + ', '.join(f'`{n.replace("TLC.", "")}`' for n in byM[m]))
w('\n(`TLC.` prefix omitted.)')
open(OUT, 'w').write('\n'.join(L) + '\n')
print('written', OUT, len(L), 'lines')

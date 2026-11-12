p = '/tmp/claude-1002/-home-zhengyew-spectec/0793c03a-21df-4d2d-9729-4ba22978b528/scratchpad/b33/tools/report33.py'
s = open(p).read()
def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, ('NOT FOUND/UNIQUE', old[:120], s.count(old)); s = s.replace(old, new)
s = s.replace('(v3: after two rounds of independent verification.)', '(v4: after three rounds of independent verification.)')
# ---- facts for v4
rep("# ------------------------------------------------------------------ text", r'''# ---- v4 facts
NEC4 = json.load(open(f'{B}/work/necessity33.json'))['per_line']
nec_own = [k for k, v in NEC4.items() if v[0] == 'own']; nec_term = [k for k, v in NEC4.items() if v[0] == 'same-term']; nec_alt = [k for k, v in NEC4.items() if v[0] == 'inside-alternative']
assert all(v[2] for v in NEC4.values() if v[0] == 'inside-alternative')
n13 = json.load(open(f'{B}/nec13/result.json')); n13_errs = len(n13['errors'])
first_names = collections.Counter()
for n in set(envc['value_changed_thm']['user_level']) | set(envc['value_changed_def']['user_level']):
    fh = CF[n][1].split(',')[0]; first_names[re.sub(r'^_private\.\w+\.0\.', '', fh)] += 1
simp_rm = sorted(n for n in envd['only_old'] if n.endswith('.injEq') or n.endswith('.sizeOf_spec'))
tot_vt = len(envd.get('value_changed_thm', [])); tot_vd = len(envd.get('value_changed_def', []))
gen_vt = tot_vt - len(envc['value_changed_thm']['user_level'])
ckinds = collections.Counter(c['kind'] if not (c['kind'] == 'set_option' and c['name'].rstrip().endswith(' in')) else 'set_option … in' for m in MODS for c in constructs(rd('final', m)))
DECL_K = {'theorem', 'lemma', 'def', 'inductive', 'structure', 'class', 'abbrev', 'opaque', 'axiom', 'instance', 'private', 'protected', 'noncomputable', 'partial', 'unsafe', 'example'}
n_decl_proper = sum(v for k, v in ckinds.items() if k in DECL_K)
n_prefix = ckinds.get('@[', 0) + ckinds.get('UNKNOWN', 0) + ckinds.get('set_option … in', 0)
other_cmds = {k: v for k, v in ckinds.items() if k not in DECL_K and k not in ('@[', 'UNKNOWN', 'set_option … in', 'derive_deceq')}
doc_cites = [(os.path.relpath(f, docs_dir), i + 1) for f in living for i, l in enumerate(open(f)) if re.search(r'wasm2\.0\.lean.*\b\d{3,5}\b', l)]
dig10 = open(f'{docs_dir}/for-claude/digest_wasm_v.md').read().split('\n')
dig_analogue = [i + 1 for i, l in enumerate(dig10) if 'Rocq analogue of `wasm2.0.lean`' in l]
dig73 = [i + 1 for i, l in enumerate(dig10) if '(73 cases)' in l]
ext_names = audit_inst.group(2).split(', ')
# ------------------------------------------------------------------ text''')
# header
rep("""w('- **What is computed.** Every table, and every count and list derived from the data, is computed by `report33.py` (§9) from the files, the build logs and the Lean outputs. The explanations are mine, as are a few fixed references inside them: spec positions, tool versions, and line numbers quoted in an explanation. Two rounds of independent readers checked them against the files (§9, Appendix E).')""",
"""w('- **What is computed.** The tables and the main counts are computed by `report33.py` (§9) from the files, the build logs and the Lean outputs, and the generator asserts many of the facts it prints. Some numbers in the explanations are typed into it by hand.')
w('- **What was checked.** Three rounds of independent read-only readers checked versions 1 to 3 against the files (Appendix E). The fixes made after the third round, in this version 4, were checked by the generator\\'s assertions and by me, not by a fourth reader.')""")
# §0 changed terms
rep("""w(f'  - **Changed terms.** Terms changed in {len(envc["value_changed_def"]["user_level"])} user-level definitions and {len(envc["value_changed_thm"]["user_level"])} user-level theorems. For user-level declarations, these are exactly the ones whose terms refer to an eliminator or equation lemma that changed (§5).')""",
"""w(f'  - **Changed terms.** Terms changed in {len(envc["value_changed_def"]["user_level"])} user-level definitions and {len(envc["value_changed_thm"]["user_level"])} user-level theorems. For user-level declarations, these are exactly the ones whose terms refer directly to a declaration whose type changed or that is new. Mostly that is a case eliminator of the four inductives or the matcher of `ai_principal_typing` (§5).')""")
# §2 hint wording
rep("""w('- So neither that hint nor the merge\\'s generator changes affect the Wasm 2.0 Lean output. Those changes are:')""",
"""w('- So the hint\\'s removal contributes nothing to the OLD → NEW difference: neither OLD\\'s base nor the HEAD spec has the hint. (With the hint, the generator emits an extra `fzero_is_wf`.)')
w('- Nor do the merge\\'s generator changes affect the Wasm 2.0 Lean output. Those changes are:')""")
# §4.2 per-line roles for wf_forall_admin_val, row source wording
rep("""    w(f'| `{e["module"]}` | {e["line"]} → {nl} | `{e["owner"]}` | {ch} | `{ins}` | {ctx[e["owner"]]} | {esc(" / ".join(dict.fromkeys(er)))} |')""",
"""    role = ctx[e['owner']]
    if e['owner'] == 'wf_forall_admin_val':
        role = ('Converse direction: destructs `wf_admininstr (VCONST vt c)` to build `wf_val`.' if e['line'] == 814 else
                'Values are well formed iff their `admininstr` images are; this line builds the image\\'s well-formedness for one kind of value.')
    w(f'| `{e["module"]}` | {e["line"]} → {nl} | `{e["owner"]}` | {ch} | `{ins}` | {role} | {esc(" / ".join(dict.fromkeys(er)))} |')""")
rep("""w('- The other twelve rows come from compiling each unrepaired module against the repaired earlier ones.\\n')""",
"""w('- Eleven of the other twelve rows come from compiling each unrepaired module against the repaired earlier ones. The `TypePreservationPure` line 1085 row comes from a compile with line 1072 already fixed.\\n')""")
# §5 method wording
rep("""w('- a 32-bit structural hash of its type: Lean\\'s `Expr.hash`, which ignores binder names, binder annotations and metadata;')""",
"""w('- a 32-bit structural hash of its type: Lean\\'s `Expr.hash`, which ignores binder names, binder annotations and the contents of metadata nodes;')""")
rep("""w('Equal hashes are strong evidence that two terms are equal, not proof: a change would be missed only through a 32-bit hash collision.')""",
"""w('Equal hashes are strong evidence that two terms are equal, not proof.')
w('- Changes only in binder names, binder annotations or metadata contents are invisible to the hash by design. The line accounting rules them out here.')
w('- Any other change would be missed only through a 32-bit collision.')""")
rep("""w('- **Environment extensions** were not compared at this level: attributes, simp sets, instances, reducibility and docstrings. All of them are written in the source, and the line accounting (§1) shows that no such line changed.\\n')""",
"""w('- **Environment extensions** were not compared directly: attributes, simp sets, instances, reducibility and docstrings.')
w('  - Those written in the source are covered by the line accounting (§1), which shows that no such line changed.')
w(f'  - The simp-set entries Lean adds by itself for each constructor changed only by the removed constructor\\'s {len(simp_rm)} lemmas (' + ', '.join(f'`{n}`' for n in simp_rm) + '), which are listed under Removed.\\n')""")
# §5 totals of value changes
rep("""w('- The four byte-identical modules have no changed declaration at this level either.\\n')""",
"""w('- The four byte-identical modules have no changed declaration at this level either.')
w(f'- In all, {tot_vt} theorems and {tot_vd} definitions changed value. Of the theorems, {len(envc["value_changed_thm"]["user_level"])} are user-level and {gen_vt} generated: ' + catlist('value_changed_thm', drop=('USER-LEVEL (listed)',)) + '.\\n')""")
# §5 metadata wording
rep("""w(f'**Inductive metadata.** A separate dump recorded every inductive, constructor and recursor: parameters, indices, constructor lists, constructor indices and field counts, and recursor motives, minor premises and rules. OLD was mapped by meaning. Of {fmt(n_meta_old)} OLD and {fmt(n_meta_new)} NEW entries, the only differences are:')""",
"""w(f'**Inductive metadata.** A separate dump recorded, for every inductive, constructor and recursor, OLD mapped by meaning:')
w('- the numbers of parameters, indices, constructors, motives, minor premises and rules;')
w('- the constructor lists;')
w('- each constructor\\'s index and field count.')
w(f'The recursor rules themselves (their right-hand sides) were not compared. Of {fmt(n_meta_old)} OLD and {fmt(n_meta_new)} NEW entries, the only differences are:')""")
# §5 cause probe wording
rep("""w('  - Classified by the first such reference: ' + '; '.join(f'{v} {k}' for k, v in sorted(CA['first_hit_categories'].items(), key=lambda x: -x[1])) + '.')
w('  - In Wasm terms: their proofs destruct an instruction or its well-formedness, or rewrite with an equation of `ai_principal_typing`, `instr_of` or `admininstr_instr`, whose case analyses now have one case fewer.')""",
"""w('  - The first such reference, by name: ' + ', '.join(f'`{k}` {v}' for k, v in first_names.most_common()) + '.')
w('  - In Wasm terms, their proofs destruct an instruction or its well-formedness, or unfold `ai_principal_typing` (or `instr_of`/`admininstr_instr`). The case analyses behind those now have one case fewer.')""")
rep("""w('- So, for user-level declarations, a changed term coincides exactly with a direct use of something the removal changed.\\n')""",
"""w('- So, for user-level declarations, a changed term coincides exactly with a direct reference to a declaration whose type changed or that is new.')
w('- The criterion leaves out declarations whose value changed but whose type did not, such as `admininstr_instr` and `instr_of`. Using those does not change a term: `ai_typing_inversion\\'` uses both, and its term is unchanged.\\n')""")
# Inhabited wording
rep("""w(f'This is a kernel replay of the eight project modules other than `ExtendedDeriveDecEq`, with the {n_inst_mod} `Inhabited` instances defined in the modules, and the {n_inst_ext} external ones they use, made opaque:')""",
"""w(f'This is a kernel replay of the eight project modules other than `ExtendedDeriveDecEq`. It makes opaque the {n_inst_mod} `Inhabited` instances defined in the modules, plus {n_inst_ext} external names they use: {n_inst_ext - (1 if "Inhabited.mk" in ext_names else 0)} instances and the structure constructor `Inhabited.mk`.')""")
# §6 counts
rep("""w(f'- Attribute lines, `initialize` and `set_option … in` prefixes count as separate entries. Counting declarations only gives {fmt(n_decl_entries)} (' + ', '.join(f'`{m}` {ckind[m]["decl"]}' for m in MODS if ckind[m]["prefix"]) + '; the rest unchanged).')""",
"""w(f'- So the {fmt(n_cons)} entries are {fmt(n_decl_proper)} declarations, {ckinds.get("derive_deceq", 0)} `derive_deceq` commands, {sum(other_cmds.values())} other commands (' + ', '.join(f'{v} `{k}`' for k, v in sorted(other_cmds.items(), key=lambda x: -x[1])) + f'), and {n_prefix} prefix entries (an attribute line, an `initialize` and a `set_option … in`).')""")
# §8 cross-check wording, witness sources, docs
rep("""w('**Cross-check with the trial port** (`spectec/src/temp_port_reference/`). That port was made outside this log, by a patch-based procedure. I compared against it only after my own result compiled, and its records agree with mine everywhere (`evidence/outputs/trial_port_crosscheck.txt`):')""",
"""w('**Cross-check with the trial port** (`spectec/src/temp_port_reference/`). That port was made outside this log, by a patch-based procedure. I compared against it only after my own result compiled. Its records agree with mine on every check below, and one of its caveats is out of date (`evidence/outputs/trial_port_crosscheck.txt`):')""")
rep("""w('- **The generated forms are false.** Bundles 23 and 29 showed this with a Lean witness, using axioms `propext`, `Classical.choice` and `Quot.sound` only (`bundle29/evidence/unedited_Step_read_is_wf_false.log`).')""",
"""w('- **The generated forms are false.** Bundles 23 and 29 showed this with a Lean witness. Bundle29\\'s log (`bundle29/evidence/unedited_Step_read_is_wf_false.log`) shows it uses only `propext`, `Classical.choice` and `Quot.sound`; bundle 23\\'s draft describes its version as using "no axioms".')""")
rep("""w('  - Those lines describe Rocq\\'s `wasm.v`, which still has `instr_EXTEND` (`spectec/test-rocq/theories/wasm.v:3282`), so they are accurate.')""",
"""w('  - Those lines describe Rocq\\'s `wasm.v`, which still has `instr_EXTEND` (`spectec/test-rocq/theories/wasm.v:3282`), so they are accurate as a description of Rocq.')
w(f'  - The same digest calls `wasm.v` "the Rocq analogue of `wasm2.0.lean`" (line {dig_analogue[0] if dig_analogue else "?"}). Its Rocq case numbering, with `instr_EXTEND` as case 19, now differs from Lean\\'s from case 20 on.')
w(f'  - A pre-existing slip: line {dig73[0] if dig73 else "?"} says "(73 cases)" for Rocq\\'s `wf_admininstr`, which has cases 0–73.')
w(f'  - The living docs also cite `wasm2.0.lean` by line number in {len(doc_cites)} places (' + ', '.join(f'`{f}:{l}`' for f, l in doc_cites) + '). These were written against earlier versions of the model and predate this port.')
w('  - I left all of these unchanged.')""")
# §9 tools/evidence
rep("""w('- `report33.py`: generates this report. `report33_v1.py` and `report33_v2.py` generated the earlier versions, and `patch_v3*.py` turned v2 into v3;')""",
"""w('- `report33.py`: generates this version.')
w('  - `report33_v1.py`, `report33_v2.py` and `report33_v3.py` generated the earlier versions.')
w('  - `patch_v3*.py` and `patch_v4.py` record the main edits between versions; some small fixes were made directly, so diff the generator versions for the full change;')
w('- `necessity33.py`: classifies the evidence that each of the 56 renames in the model\\'s proofs is needed;')""")
rep("""w('- the audit outputs, including the positive control (`audit_ctl.txt`);')""",
"""w('- the audit outputs and logs, including the positive control (`audit_ctl.txt`) and the memory figures of §7 (`audit_old.log`, `audit_new.log`);')
w('- the compile of NEW with only the 13 inner renames reverted (`nec13_compile.log`, `nec13_result.json`) and `necessity33.json`;')""")
rep("""w('- None of the 49 points found an error in the repair or in the line accounting. Appendix E says how each was addressed in this version 3.')""",
"""w('- Two more checked version 3 (`workflow_verify_v3_result.json`): `V3-DELTA` checked every new or changed claim, and `V3-RESOLVE` checked Appendix E. They raised 28 findings.')
w('- None of the 77 points found an error in the repair or in the line accounting. Appendix E says how each was addressed.')""")
# Appendix A
rep("""w(f'The last column is from bundle32\\'s compile of the unrenamed copy (`bundle32/evidence/outputs/compile_verbatim_copy_72_errors.log`, 72 errors on {len(errlines)} lines; line numbers are NEW\\'s). {len(NEC["own"])} of the {n_hand} lines failed on the line itself. The other {len(NEC["noown"])} failed on an adjacent line of the same term or `cases`, given as "near L".\\n')""",
"""w(f'The last column shows the evidence that each rename is needed.')
w(f'- **Bundle32\\'s compile of the unrenamed copy** (`bundle32/evidence/outputs/compile_verbatim_copy_72_errors.log`, 72 errors on {len(errlines)} lines, numbered as in NEW):')
w(f'  - {len(nec_own)} lines failed on the line itself ("this line");')
w(f'  - {len(nec_term)} failed on a neighbouring line of the same term ("same term, L").')
w(f'- **The other {len(nec_alt)}** sit inside a `cases` alternative whose renamed pattern line, given as "inside L", failed first, so Lean never elaborated them.')
w(f'  - For those, NEW was compiled again with only these {len(nec_alt)} lines reverted to their OLD text. It gave {n13_errs} errors, one on each reverted line ("+ own error when reverted").\\n')""")
rep("""        ec = 'this line' if r['new'] in NEC['own'] else f'near {nearest(r["new"])}'""",
"""        v = NEC4[str(r['new'])]
        ec = 'this line' if v[0] == 'own' else (f'same term, {", ".join(str(x) for x in v[1])}' if v[0] == 'same-term' else f'inside {v[1]}; + own error when reverted')""")
# Appendix E: fix CRITIC-3 row, add third-round table
rep("""('CRITIC-3', 'No per-module or per-kind totals', 'Tables added in §5, and the 3 generated theorems that changed value but not type are listed.'),""",
"""('CRITIC-3', 'No per-module or per-kind totals; value-change totals', 'Tables added in §5. §5 also gives the value-change totals (theorems and definitions, by category) and lists every generated theorem that changed value but not type (7 of them).'),""")
rep("""for fid, pt, res in RESOLUTIONS: w(f'| {fid} | {pt} | {res} |')""",
"""for fid, pt, res in RESOLUTIONS: w(f'| {fid} | {pt} | {res} |')
w('\\n**Third round, on version 3** (D = `V3-DELTA`, R = `V3-RESOLVE`). The fixes are in this version 4; no fourth reader checked them.\\n')
w('| finding | point | how it is addressed in version 4 |'); w('|---|---|---|')
for fid, pt, res in RESOLUTIONS_V3: w(f'| {fid} | {pt} | {res} |')""")
rep("RESOLUTIONS = [", r'''RESOLUTIONS_V3 = [
 ('D-1, R-6', 'Appendix E said 3 generated value-only theorems where §5 lists 7; the value-change totals were missing', 'Row corrected, and §5 now gives the totals.'),
 ('D-2, R-2', 'Appendix A: one "near" cell pointed into another alternative; 13 lines never failed themselves', 'The column now distinguishes "this line", "same term" and "inside L". A new compile with only those 13 lines reverted gives one error on each (`nec13`).'),
 ('D-3', '§2 overreached on the `$fzero` hint', 'Reworded: the hint\'s removal contributes nothing to OLD → NEW; with the hint, the generator emits `fzero_is_wf`.'),
 ('D-4, R-10', 'The probe criterion was paraphrased too broadly', '§0 and §5 state the tested criterion (type changed or new) and give the first references by name. §5 notes that value-only changes such as `admininstr_instr` were not in the set, with an example.'),
 ('D-5, R-1', '"What is computed" still overstated; new prose unverified', 'The header now says that some numbers are hand-typed, and that the version 4 fixes were not checked by a fourth reader.'),
 ('D-6, R-7', '1,866 is not a declarations-only count', '§6 breaks the 1,869 entries down by kind, all computed.'),
 ('D-7, R-5b', 'The metadata dump records counts, not recursor rules', 'Reworded in §5.'),
 ('D-8, R-5a', 'Auto-generated simp entries are not written in the source', '§5 names the 4 removed `injEq`/`sizeOf_spec` lemmas.'),
 ('D-9', '`meta_cause33.py` could not be re-run against the v3 `envcat33.py`', 'Fixed, and re-run: `cause33.json` is reproduced identically.'),
 ('D-10, R-8a', 'The source of the probe memory figure was missing from the evidence', '`audit_old.log` and `audit_new.log` are now in `outputs/`.'),
 ('D-11, R-8c', 'The patch scripts do not reproduce the generator', '§9 says so; every generator version is kept.'),
 ('D-12, R-3', '"agree everywhere" contradicted by the next bullet', 'Reworded: the records agree on every check, and one caveat is out of date.'),
 ('D-13, R-9', '`Inhabited.mk` is a constructor, not an instance', '§5 says so.'),
 ('D-14, R-11', '"each unrepaired module" was not true of the 1085 row', 'Corrected in §4.2.'),
 ('D-15', 'Bundle 23 described the witness as using "no axioms"', '§8 gives both sources.'),
 ('D-16, R-4', 'Hash method: changes in names and annotations are missed by design, not only through a collision', 'Reworded in §5 Method.'),
 ('R-8b', '`b32_necessity.json` had no producing tool', 'Replaced by `necessity33.py` and its `necessity33.json`.'),
 ('R-12', 'Two sub-points not addressed: the role of `TypeProgress` 814, and Rocq numbering in `digest_wasm_v.md`', 'The role column is now per line, with 814 in the converse direction. §8 notes the digest\'s Rocq numbering, its "(73 cases)" slip and its line-number citations, all unchanged.'),
]
RESOLUTIONS = [''')
open(p, 'w').write(s)
print('v4 patch ok')

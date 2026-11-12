p = '/tmp/claude-1002/-home-zhengyew-spectec/0793c03a-21df-4d2d-9729-4ba22978b528/scratchpad/b33/tools/report33.py'
s = open(p).read()
def rep(old, new):
    global s
    assert s.count(old) == 1, ('NOT FOUND/UNIQUE', old[:110], s.count(old)); s = s.replace(old, new)
# more facts needed by the text
rep("# ------------------------------------------------------------------ text", r'''fz = subprocess.run(['git', '-C', '/home/zhengyew/spectec', 'log', '--format=%h', '-1', '--', 'specification/wasm-2.0/C-hints.spectec'], capture_output=True, text=True, env=dict(os.environ, GIT_OPTIONAL_LOCKS='0')).stdout.strip()
orig_same = all(MO[a - 1:a + 4] == MN[b - 1:b + 4] for a, b in [(old_sorry_model[0] - 4, commented[0] - 4), (old_sorry_model[1] - 4, commented[1] - 4)])
info_lines = len(open(f'{B}/final/logs/TypeProgress.log').read().split('\nTypeProgress.lean:')[0].split('\n'))
chk = [(m, i + 1) for m in MODS for i, l in enumerate(rd('final', m)) if l.strip().startswith('#check')]
audit_inst = re.search(r'module Inhabited instances made opaque: (\d+); external instances made opaque: \[(.*?)\]', open(f'{B}/probes/audit_new.txt').read())
n_inst_mod, n_inst_ext = int(audit_inst.group(1)), len(audit_inst.group(2).split(', '))
recs_rules = [c['name'] for c in im_rec if re.search(r'rules=(\d+)', c['old']).group(1) != re.search(r'rules=(\d+)', c['new']).group(1)]
recs_norules = [c['name'] for c in im_rec if c['name'] not in recs_rules]
cases_in = {}
for e in edits:
    if e['kind'] == 'rename':
        cs = constructs(rd('final', e['module'])); o = [c for c in cs if c['name'] == e['owner']][0]
        cases_in[e['owner']] = 'cases' in '\n'.join(rd('final', e['module'])[o['line'] - 1:o['end']])
for c in agg:
    cs = constructs(MN); o = [x for x in cs if x['name'] == c][0]; cases_in[c] = 'cases' in '\n'.join(MN[o['line'] - 1:o['end']])
vnt_ref = {n: CA['examples'].get(n) for n in v_not_t}
CF = {}
for l in open(f'{B}/probes/cause_new.tsv'):
    f = l.rstrip('\n').split('\t')
    if len(f) == 4: CF[f[1]] = (int(f[2]), f[3])
# ------------------------------------------------------------------ text''')
# header: computed claim + directory
rep("""w('- **Computed, not typed.** Every count, line number and listed name below is computed by `report33.py` (§9) from the files, the build logs and the Lean outputs. The explanatory prose is mine, and an independent reader checked it against the files.')""",
"""w('- **What is computed.** Every table, and every count and list derived from the data, is computed by `report33.py` (§9) from the files, the build logs and the Lean outputs. The explanations are mine, as are a few fixed references inside them: spec positions, tool versions, and line numbers quoted in an explanation. Two rounds of independent readers checked them against the files (§9, Appendix E).')""")
rep("""w('  - The other two are outside both builds, and you changed them before bundle32: `OLD_wasm2.0.lean` was replaced by HEAD\\'s model, and `wasm2.0_prevattempt.lean` was deleted.')""",
"""w(f'  - The other two are outside both builds, since the lakefile does not build them. You changed both before bundle32:')
w(f'    - At HEAD, `OLD_wasm2.0.lean` held an older model ({fmt(head_old[1])} lines, md5 `{head_old[0][:8]}…`). It now holds HEAD\\'s `wasm2.0.lean` ({fmt(wt_old_lines)} lines, md5 `{wt_old_md5[:8]}…`).')
w(f'    - `wasm2.0_prevattempt.lean` ({fmt(head_prev[1])} lines, md5 `{head_prev[0][:8]}…` at HEAD) was deleted.')""")
# §0
rep("""w(f'- **One cause.** The mech-backend merge deleted one line of the Wasm 2.0 spec: the dead instruction `EXTEND numtype n`. Every difference below follows from that.')""",
"""w(f'- **One cause.** The mech-backend merge deleted one line of the Wasm 2.0 spec: the dead instruction `EXTEND numtype n`. Every difference below follows from that. (The merge also removed a `$fzero` hint, but OLD\\'s model had already been generated without it; see §2.)')""")
rep("""w('  - The constructor `EXTEND` itself is gone, from `instr` and `admininstr`, together with its two well-formedness cases.')
w('  - Every other declaration whose type changed is one Lean generates automatically.')
w(f'  - Values changed in {len(envc["value_changed_def"]["user_level"])} user-level definitions and {len(envc["value_changed_thm"]["user_level"])} user-level proof terms. Almost all are unchanged source that now case-splits over one constructor fewer.')""",
"""w('  - The constructor `EXTEND` itself is gone, from `instr` and `admininstr`, together with its two well-formedness cases.')
w('  - **Unchanged statements, smaller types.** The check compares statements by name. Statements that mention `instr` or `admininstr` keep their text, but now range over types with one constructor fewer. That is the intended effect, and it changes nothing of substance: no typing rule ever mentioned `EXTEND` (§2), so no configuration satisfying the main theorems\\' typing hypotheses could contain it, even in OLD.')
w('  - Every other declaration whose type changed is one Lean generates automatically.')
w(f'  - **Changed terms.** Terms changed in {len(envc["value_changed_def"]["user_level"])} user-level definitions and {len(envc["value_changed_thm"]["user_level"])} user-level theorems. For user-level declarations, these are exactly the ones whose terms refer to an eliminator or equation lemma that changed (§5).')""")
rep("""w(f'  - The {nwarn} warnings are the same messages in both.\\n')""",
"""w(f'  - The build logs are identical once line numbers and timings are stripped: the same {nwarn} warnings and the same info output.\\n')""")
# §1 bytes
rep("""w('- Four modules are byte-identical: ' + ', '.join(f'`{m}`' for m in MODS if md5(f'{B}/old/src/{m}.lean') == md5(f'{B}/final/src/{m}.lean')) + '.\\n')""",
"""w('- Four modules are byte-identical: ' + ', '.join(f'`{m}`' for m in MODS if md5(f'{B}/old/src/{m}.lean') == md5(f'{B}/final/src/{m}.lean')) + '.')
w(f'- **Bytes.** All {len(BF)} files (9 OLD, 9 NEW) are valid UTF-8 with LF line endings, no byte-order mark and exactly one final newline. Their trailing whitespace and tabs are {"the same in OLD and NEW" if tw_same else "NOT the same"}. Sizes and full md5 sums are in Appendix D.\\n')""")
# §2
rep("""w('**No other generator change matters.** In bundle32 the HEAD generator was run on the spec with only that line restored, and it reproduced the old generated base byte for byte (`bundle32/evidence/outputs/generator_check.txt`). So the merge\\'s other generator changes have no effect on the Wasm 2.0 Lean output:')""",
"""w(f'**No other change matters.** The merge also brought in mech-backend\\'s removal of `def $fzero hint(wfopt)` from `C-hints.spectec` (commit `{fz}`). OLD\\'s generated base had already been produced without that hint (bundle29).')
w('- In bundle32 the HEAD generator was run on the HEAD spec with only the `EXTEND` line restored, and it reproduced OLD\\'s generated base byte for byte (`bundle32/evidence/outputs/generator_check.txt`).')
w('- So neither that hint nor the merge\\'s generator changes affect the Wasm 2.0 Lean output. Those changes are:')""")
rep("""w(f'The renaming was done by meaning, not by arithmetic. Each OLD case was matched to the NEW case with identical text: arguments, premises and conclusion. All matched uniquely ({rc["wf_instr"][1]} of {rc["wf_instr"][1]} and {rc["wf_admininstr"][1]} of {rc["wf_admininstr"][1]}); none was ambiguous or unmatched.\\n')""",
"""mi = {k: sum(1 for v in cmap[k]['map'].values() if isinstance(v, str)) for k in cmap}
assert all(cmap[k]['unmatched_old'] == [f'{"instr" if k == "wf_instr" else "admininstr"}_case_19'] and not cmap[k]['ambiguous'] and not cmap[k]['unmatched_new'] for k in cmap)
w(f'The renaming was done by meaning, not by arithmetic. Every OLD case except the removed case 19 matched exactly one NEW case with identical text: arguments, premises and conclusion. That gives {mi["wf_instr"]} matches in `wf_instr` and {mi["wf_admininstr"]} in `wf_admininstr`. Case 19 has no counterpart, no NEW case is left over, and no match is ambiguous.\\n')""")
# §4
rep("""w('| module | line OLD → NEW | construct | change | instruction | role of the line | error without the change |'); w('|---|---|---|---|---|---|---|')""",
"""w('The full OLD and NEW text of all 17 changed lines is in Appendix C.\\n')
w('| module | line OLD → NEW | construct | change | instruction | role of the line | error without the change |'); w('|---|---|---|---|---|---|---|')""")
rep("""w('- The table above therefore comes from a second compile, in which only the two arms of §4.1 were deleted. Its line numbers are the NEW ones.\\n')""",
"""w('- So the table\\'s three `TypingLemmas` rows come from a second compile of that module, with only the two arms of §4.1 deleted. Their line numbers are the NEW ones.')
w('- The other twelve rows come from compiling each unrepaired module against the repaired earlier ones.\\n')""")
# §5 method
rep("""w('- a hash of its type;')
w('- a hash of its value (both hashes ignore binder names);')
w('- for theorems, its axioms.\\n')""",
"""w('- a 32-bit structural hash of its type: Lean\\'s `Expr.hash`, which ignores binder names, binder annotations and metadata;')
w('- the same hash of its value;')
w('- for theorems, its axioms.\\n')
w('Equal hashes are strong evidence that two terms are equal, not proof: a change would be missed only through a 32-bit hash collision.')
w('- **Inductive metadata** is not covered by the hashes, so it was compared separately (below).')
w('- **Environment extensions** were not compared at this level: attributes, simp sets, instances, reducibility and docstrings. All of them are written in the source, and the line accounting (§1) shows that no such line changed.\\n')""")
# §5 totals: add tables
rep("""w(f'**Totals.** OLD has {fmt(n_old)} declarations ({fmt(t_old)} theorems), and NEW has {fmt(n_new)} ({fmt(t_new)} theorems). {fmt(common)} are common to both; {len(envd["only_old"])} are only in OLD and {len(envd["only_new"])} only in NEW.\\n')""",
"""w(f'**Totals.** OLD has {fmt(n_old)} declarations ({fmt(t_old)} theorems), and NEW has {fmt(n_new)} ({fmt(t_new)} theorems). {fmt(common)} are common to both; {len(envd["only_old"])} are only in OLD and {len(envd["only_new"])} only in NEW.\\n')
w('| module | declarations OLD → NEW | removed | added | type or value changed |'); w('|---|---|---|---|---|')
for m, c in pm.items(): w(f'| `{m}` | {fmt(c["old"])} → {fmt(c["new"])} | {c["removed"]} | {c["added"]} | {c["changed"]} |')
w('\\nBy kind (OLD → NEW): ' + ', '.join(f'{k} {fmt(a)} → {fmt(b)}' for k, (a, b) in pk.items() if a or b) + '.')
w(f'- Types or values changed only for kinds ' + ', '.join(f'`{k}`' for k in kinds_changed) + '. No axiom, opaque or inductive type changed its type or value.')
w('- The four byte-identical modules have no changed declaration at this level either.\\n')""")
# §5 removed
rep("""w('- **User-visible (4):** `instr.EXTEND`, `admininstr.EXTEND`, and the `EXTEND` cases of `wf_instr` and `wf_admininstr`.')
w('- **Generated by Lean:** the removed constructors\\' `elim`/`inj`/`injEq`/`noConfusion`/`sizeOf_spec`, and their `.below` cases.')
w('- **The ends of numbered families.** Lean numbers many auxiliary declarations by position: equation lemmas `eq_N` (one per match arm), `_proof_N`, `_simp_N`, `match_N.eq_N`, `DecidableEq` sub-proofs, and hygienic names `_hyg.N`. When a family shrinks, its highest numbers disappear and the members after the removed one are renumbered.')
w(f'  - For example, the deleted arms of `admininstr_instr`, `instr_of` and `ai_principal_typing` take away the last equation lemmas, {gone}.')
w(f'  - The lemmas from each deleted arm onward now state the next arm\\'s equation. Their types changed: {fams}.')""",
"""w(f'- **The removed instruction ({len(rm_ext)}):**')
w('  - `instr.EXTEND` and `admininstr.EXTEND`;')
w('  - the `EXTEND` cases of `wf_instr` and `wf_admininstr`, and of their `.below`;')
w('  - the lemmas Lean generates for each removed constructor: `elim`, `inj`, `injEq`, `noConfusion` and `sizeOf_spec`.')
w(f'- **Ends of numbered families that shrank ({len(rm_end)}).** Lean numbers many auxiliary declarations by position: equation lemmas `eq_N` (one per match arm), `_proof_N`, and `DecidableEq` sub-proofs. When such a family loses a member, its highest numbers disappear and the members after the removed one are renumbered.')
w('  - The families, with their size OLD → NEW: ' + '; '.join(f'`{st}N` {a}→{b}' for st, (a, b) in end_fams.items()) + '.')
w(f'  - For example, the deleted arms of `admininstr_instr`, `instr_of` and `ai_principal_typing` take away their last equation lemmas, {gone}.')
w(f'  - The lemmas from each deleted arm onward now state the next arm\\'s equation, so their types changed: {fams}.')
w(f'- **Renumbered without shrinking ({len(rm_ren)}).** These belong to families that kept their size but were renumbered, or are hygienic names whose counter moved. Each has a counterpart among the {len(envd["only_new"])} added names.')""")
rep("""w('All are renumbered auxiliaries of the same kind: ' + catlist('only_new') + '. There is no new user-level declaration and no new axiom.\\n')""",
"""w('All are the renumbered counterparts just described: ' + catlist('only_new') + '. There is no new user-level declaration and no new axiom.\\n')""")
# §5 statements: add metadata
rep("""for k, lab in [('type_changed_thm', 'theorems'), ('type_changed_def', 'definitions'), ('type_changed_rec', 'recursors')]:
    w(f'- {lab}: ' + catlist(k) + '.')
w('')""",
"""for k, lab in [('type_changed_thm', 'theorems'), ('type_changed_def', 'definitions'), ('type_changed_rec', 'recursors')]:
    w(f'- {lab}: ' + catlist(k) + '.')
w('')
w(f'**Inductive metadata.** A separate dump recorded every inductive, constructor and recursor: parameters, indices, constructor lists, constructor indices and field counts, and recursor motives, minor premises and rules. OLD was mapped by meaning. Of {fmt(n_meta_old)} OLD and {fmt(n_meta_new)} NEW entries, the only differences are:')
w(f'- the {len(IM["only_old"])} removed constructors: `EXTEND` of `instr` and `admininstr`, and case 19 of `wf_instr`, `wf_admininstr` and their `.below`;')
w(f'- {len(im_ind)} inductive types with one constructor fewer: ' + ', '.join(f'`{x}`' for x in im_ind) + ';')
w(f'- {im_ctor} constructors whose index went down by exactly 1, with everything else equal. These are the constructors after `EXTEND`: 48 of `instr`, 54 of `admininstr`, and the same numbers for `wf_instr`, `wf_admininstr` and their `.below`;')
w(f'- {len(im_rec)} recursors with one minor premise fewer: ' + ', '.join(f'`{x}`' for x in recs_rules) + ' also have one rule fewer, while ' + ', '.join(f'`{x}`' for x in recs_norules) + ' (the auxiliary recursors of the nested types) keep their 2 rules.\\n')
w('This index shift explains the remaining generated changes: the types of the per-constructor `X.CTOR.elim`, the values of `ctorIdx`/`noConfusionType`, and the `DecidableEq` sub-proofs.\\n')""")
# §5 proof terms
rep("""w('Most of these theorems have unchanged source. Their proofs destruct an `instr`/`admininstr` or its well-formedness, or run a tactic over every case, and that now produces one case fewer. Appendix B lists them.\\n')
w(f'Of the {len(edited)} theorems edited in §3.4 and §4.2, these {len(same)} have the same proof term as before, once constructor numbers are mapped: ' + ', '.join(f'`{t}`' for t in same) + '. Their edits were pure renamings.\\n')""",
"""w('Most of these theorems have unchanged source; Appendix B lists them. A probe on NEW listed, for every theorem and definition, the declarations its term refers to directly, and marked those whose type changed or that are new:')
w(f'- **All {CA["user_changed_total"]} changed user-level declarations refer to such a declaration** ({len(ut)} theorems and {len(ud)} definitions; {CA["user_changed_refer"]} of {CA["user_changed_total"]}).')
w('  - Classified by the first such reference: ' + '; '.join(f'{v} {k}' for k, v in sorted(CA['first_hit_categories'].items(), key=lambda x: -x[1])) + '.')
w('  - In Wasm terms: their proofs destruct an instruction or its well-formedness, or rewrite with an equation of `instr_of`/`ai_principal_typing`/`admininstr_instr`, and those now have one case fewer.')
w(f'- **None of the {fmt(ucg(False, False))} unchanged user-level declarations refers to one.**')
w('- So, for user-level declarations, a changed term coincides exactly with a direct use of something the removal changed.\\n')
w(f'All {len(edited)} theorems edited in §3.4 and §4.2 were pure renamings.')
w(f'- These {len(same)} have the same proof term as before, once constructor numbers are mapped: ' + ', '.join(f'`{t}`' for t in same) + '. They only apply a constructor.')
w(f'- The other {len(edited) - len(same)} {"each do" if all(cases_in[t] for t in edited if t not in same) else "mostly do"} a `cases` on `wf_instr`/`wf_admininstr`, whose eliminator lost a case.\\n')
if v_not_t:
    w(f'Among generated declarations, {len(v_not_t)} theorems changed value but not type: ' + ', '.join(f'`{n}`' for n in v_not_t) + '. ' + ('Each refers directly to a changed declaration (' + '; '.join(f'`{n.split(".")[-2] if "." in n else n}` → `{CF[n][1].split(",")[0]}`' for n in v_not_t if n in CF and CF[n][0] > 0) + ').' if all(n in CF and CF[n][0] > 0 for n in v_not_t) else 'Not all of them refer directly to a changed declaration.') + '\\n')""")
# §5 audit wording + control
rep("""w('This is a kernel replay of the eight project modules other than `ExtendedDeriveDecEq`, with every `Inhabited` instance opaque:')""",
"""w(f'This is a kernel replay of the eight project modules other than `ExtendedDeriveDecEq`, with the {n_inst_mod} `Inhabited` instances defined in the modules, and the {n_inst_ext} external ones they use, made opaque:')""")
rep("So the harness does detect default-dependent proofs with this toolchain and build. The control module was never in the repo.\\n')",
    "So the harness does detect default-dependent proofs with this toolchain and build. The control module was never among the project\\'s modules; a copy is kept as evidence (`evidence/tools/AuditCtl33.lean`).\\n')")
# §6 definition of counted constructs
rep("""w(f'All nine files have the same top-level constructs, in the same order, in OLD and NEW: ' + ', '.join(f'`{m}` {cons[m]}' for m in MODS) + f', {fmt(n_cons)} in all. These {len(pc)} have changed text:\\n')""",
"""w(f'All nine files have the same top-level constructs, in the same order, in OLD and NEW: ' + ', '.join(f'`{m}` {cons[m]}' for m in MODS) + f', {fmt(n_cons)} in all.')
w('- **What counts as a construct.** Entries are as counted by `toplevel32.py`: every command that starts at column 0 outside comments, except `deriving` clauses.')
w(f'- Attribute lines, `initialize` and `set_option … in` prefixes count as separate entries. Counting declarations only gives {fmt(n_decl_entries)} (' + ', '.join(f'`{m}` {ckind[m]["decl"]}' for m in MODS if ckind[m]["prefix"]) + '; the rest unchanged).')
w(f'- The one-for-one match holds either way.\\n')
w(f'These {len(pc)} have changed text:\\n')""")
# §7 warnings, logs, memory, lake
rep("""w(f'\\n**Warnings.** The {nwarn} warnings are the same messages in OLD and NEW; only their line numbers move, where lines were deleted above them. They are:')
w(f'- {wc["unused variable"]} unused variables;')
w(f'- {wc["naming lint"]} Mathlib naming-convention lints;')
w(f'- {wc["other lint"]} other linter suggestions: tactics that do nothing, unused `simp` arguments, and `Try this` hints.\\n')""",
"""w(f'\\n**Logs.** The OLD and NEW build logs are {"identical" if logs_same else "NOT identical"} once line numbers and timings are stripped. Only line numbers move, where lines were deleted above them. The logs contain:')
w(f'- the same {nwarn} warnings: ' + '; '.join(f'{v} {k}' for k, v in sorted(wsc.items(), key=lambda x: -x[1])) + ';')
w(f'- the same info output: {info_lines - 1} lines printed by the `#check Instrs_ok2.rec` left inside a proof at `TypeProgress` line {[l for (m, l) in chk if m == "TypeProgress"][0]}.\\n')""")
rep("""w(f'**Memory.** Peak resident memory was {peak / 1024 / 1024:.2f} GiB ({fmt(peak)} KiB), in `TypeProgress`.\\n')""",
"""w(f'**Memory.** The compiles peaked at {peak / 1024 / 1024:.2f} GiB ({fmt(peak)} KiB), in OLD\\'s `TypeProgress`; NEW\\'s `TypeProgress` peaked at {fmt(new_tp_rss)} KiB. The Lean probes of §5 peaked higher, at {probe_peak / 1024 / 1024:.2f} GiB ({fmt(probe_peak)} KiB), in the `Inhabited` audit runs.\\n')
w('**No Lake build of either state.** The repo\\'s `.lake/build` matches neither state.')
w('- Its traces record warning counts that differ even from OLD\\'s: 93 for `wasm2.0`, against 89.')
w('- It holds oleans for modules the lakefile no longer builds (`custom_notation`, `sandbox_5`, `sandbox_10`).')
w('- Both states were therefore checked only by these scratch builds with the bare `lean` binary. The lakefile sets no Lean options, and Lake\\'s recorded setup for `wasm2.0` has empty options, so a Lake build should behave the same. That was not run.\\n')""")
# §8 citations table, re-stated theorems, docs, cross-check
rep("""w(f'**The word `sorry`.** No code contains `sorry`, but the word appears on {len(sorry_lines)} comment lines of the nine NEW modules:')""",
"""w('**Comments that cite model line numbers.** Six comments in the proof modules cite `wasm2.0.lean` by a line number beyond the first deleted line. All six were already wrong in OLD, and the declarations they name moved again, by 2 or 5 lines:\\n')
w('| comment (NEW file:line) | cites line | names | actually at OLD → NEW |'); w('|---|---|---|---|')
for (m, l, cited, nm, a, b) in cit_rows: w(f'| `{m}:{l}` | {cited} | `{nm}` | {a} → {b} |')
w(f'\\nThe comments that cite lines 9, 12 and 20 are right in both versions. The one citing line 798 for `size` was already wrong in OLD: it is at line {size_old} in both.')
w('I left all of them as they are.\\n')
w(f'**The word `sorry`.** No code contains `sorry`, but the word appears on {len(sorry_lines)} comment lines of the nine NEW modules:')""")
rep("""w(f'**Pre-existing, and the same in OLD and NEW: two re-stated theorems.** The fresh generator output has {gen_sorry} `sorry`s.')
w(f'- In both OLD and NEW, {gen_sorry - len(commented)} of those theorems are proved as generated.')
w('- The generated `Step_read_is_wf` and `Step_is_wf` are commented out (their `--   sorry` lines are ' + ' and '.join(str(x) for x in commented) + '). They are re-stated below `Store_ok` with an extra `Store_ok (fun_store z)` premise, as done in bundle29.')
w('- So "zero `sorry`" covers the generated statements, except these two, which hold only in that weaker form.')
w('- This port did not change either of them, apart from the renamings in their proofs (§3.4).\\n')""",
"""w(f'**Pre-existing, and the same in OLD and NEW: two re-stated theorems.** The fresh generator output, `spectec/test-lean/todaywasm2.0.lean` (md5 `{md5("/home/zhengyew/spectec/spectec/test-lean/todaywasm2.0.lean")[:8]}…`), has {gen_sorry} `sorry`s.')
w(f'- **Proved as generated:** {gen_sorry - len(commented)} of those theorems, in both OLD and NEW.')
w('- **Commented out:** the generated `Step_read_is_wf` and `Step_is_wf`, with their `--   sorry` at lines ' + ' and '.join(str(x) for x in commented) + f'. The commented-out text is {"identical" if orig_same else "NOT identical"} in OLD and NEW.')
w('- **Re-stated:** each is re-stated below `inductive Store_ok` with three changes, as in bundle29:')
w('  - it moves below `Store_ok`;')
w('  - it takes the configuration as `(z : state) (admininstr_lst : List admininstr)`, with `config.mk_config z admininstr_lst` in the hypotheses;')
w('  - it gets the premise `Store_ok (fun_store z)`.')
w('- **The generated forms are false.** Bundles 23 and 29 showed this with a Lean witness, using axioms `propext`, `Classical.choice` and `Quot.sound` only (`bundle29/evidence/unedited_Step_read_is_wf_false.log`).')
w('  - The counterexample is a well-formed configuration whose store holds a table of 2^32 references. It steps by `table.size` to `CONST I32 2^32`, which is not a well-formed `u32`.')
w('  - The witness source was not kept, so it was not re-run on NEW. The counterexample does not involve `EXTEND`.')
w('- **What "zero `sorry`" covers:** all generated statements except these two, which hold only in the weaker re-stated form. This port changed them only by the renamings in their proofs (§3.4).\\n')""")
rep("""w(f'**Documentation.** The living docs (`claude-logging/README.md`, `for-claude/*.md`, `for-humans/*.md`) mention no renumbered case and no `EXTEND` constructor ({living_hits} matching lines).')
w(f'- Historical logs in earlier bundles and in `safety-checks/` do mention old case numbers ({hist_files} files).')
w('- They are records of past turns, so I left them as they are.\\n')""",
"""w('**Documentation.**')
w(f'- **Living docs** (`claude-logging/README.md`, `for-claude/*.md`, `for-humans/*.md`): they mention `EXTEND` or numbered `*_case_` names only in ' + ', '.join(sorted({f'`{f}`' for f, _, _ in living_hits_l})) + ' (lines ' + ', '.join(str(l) for _, l, _ in living_hits_l) + ').')
w('  - Those lines describe Rocq\\'s `wasm.v`, which still has `instr_EXTEND` (`spectec/test-rocq/theories/wasm.v:3282`), so they are accurate.')
w(f'- **Historical logs:** {sum(hist_by_bundle.values())} files mention old case numbers, all under `verbatim_dialogue_log/` (' + ', '.join(f'{k} {v}' for k, v in sorted(hist_by_bundle.items(), key=lambda x: int(x[0][6:]))) + f'); {hist_sc} are in `safety-checks/`. They are records of past turns, so I left them as they are.\\n')""")
rep("""w('- **Edits:** its `patches/edits_73.log` lists the same 73 edits, matched one for one by file, kind and text: 56 + 15 renamings and 2 deleted arms.')""",
"""w('- **Edits:** its `patches/edits_73.log` lists the same 73 edits: 56 + 15 renamings and 2 deleted arms. They match one for one by file, kind and text. That log truncates long lines, so the texts were matched as prefixes.')""")
rep("""w('- **Comments:** it flags the same five stale "68" comments.\\n')""",
"""w('- **Comments:** it flags the same five stale "68" comments.')
w('- **One point where it is out of date.** Its caveat that the falsity of the generated `Step_*` forms "has not been confirmed with a Lean witness" overlooks the bundle 23/29 witness above.\\n')""")
# §9 lists
rep("""w('- `report33.py`: generates this report; `toplevel32.py` and `ctor_map32.py` come from bundle32.\\n')""",
"""w('- `IndMeta33.lean` and `Cause33.lean`, analysed by `meta_cause33.py`: the inductive-metadata comparison and the probe of why each proof term changed;')
w('- `AuditCtl33.lean` and `RunAuditCtl33.lean`: the audit\\'s positive control;')
w('- `report33.py`: generates this report. `report33_v1.py` and `report33_v2.py` generated the earlier versions, and `patch_v3*.py` turned v2 into v3;')
w('- `toplevel32.py` and `ctor_map32.py` come from bundle32.\\n')""")
rep("""w('- the audit outputs, including the positive control (`audit_ctl.txt`, `AuditCtl33.lean`);')""",
"""w('- the audit outputs, including the positive control (`audit_ctl.txt`);')
w('- the inductive-metadata dumps and their comparison (`indmeta_*.tsv`, `indmeta_diff33.json`), and the cause probe (`cause_new.tsv`, `cause_set.txt`, `cause33.json`);')""")
rep("""w('**`verification/`:** the reports of the independent verifiers. `V-REPORT-1` checked the first version of this report; its 17 points are fixed in this one.\\n')""",
"""w('**`verification/`:** the reports of the independent, read-only verifiers.')
w('- `V-REPORT-1` checked version 1 of this report and raised 17 points.')
w('- Three more checked version 2 (`workflow_reverify_result.json`): `V2-FIX` checked whether those points were resolved, `V2-FRESH` did a fresh refutation, and `V2-CRITIC` looked for completeness. They raised 32 findings.')
w('- None of the 49 points found an error in the repair or in the line accounting. Appendix E says how each was addressed in this version 3.')
w('- Versions 1 and 2 of the report are kept next to the verifier reports.\\n')""")
# Appendix A columns
rep("""w('| OLD → NEW line | construct | OLD text → NEW text |'); w('|---|---|---|')
for r in rows:
    if r['cat'] == 'ctor-renumber/hand-layer': w(f'| {r["old"]} → {r["new"]} | `{r["construct"]}` | {code(esc(r["before"]))} → {code(esc(r["after"]))} |')
w('')""",
"""w(f'The last column is from bundle32\\'s compile of the unrenamed copy (`bundle32/evidence/outputs/compile_verbatim_copy_72_errors.log`, 72 errors on {len(errlines)} lines; line numbers are NEW\\'s). {len(NEC["own"])} of the {n_hand} lines failed on the line itself. The other {len(NEC["noown"])} failed on an adjacent line of the same term or `cases`, given as "near L".\\n')
w('| OLD → NEW line | construct | instruction | OLD text → NEW text | error in the unrenamed compile |'); w('|---|---|---|---|---|')
for r in rows:
    if r['cat'] == 'ctor-renumber/hand-layer':
        ins = ', '.join(sorted({meaning[f'admininstr_case_{k}'] for _, k in re.findall(r'\\b((?:admin)?instr_case)_(\\d+)\\b', r['before']) if int(k) >= 20}))
        ec = 'this line' if r['new'] in NEC['own'] else f'near {nearest(r["new"])}'
        w(f'| {r["old"]} → {r["new"]} | `{r["construct"]}` | `{ins}` | {code(esc(r["before"]))} → {code(esc(r["after"]))} | {ec} |')
w('')""")
# Appendix C, D, E appended at the end
rep("""w(f'\\n**User-level definitions whose elaborated value changed ({len(ud)}):** ' + ', '.join(f'`{n}`' for n in ud) + '.')""",
"""w(f'\\n**User-level definitions whose elaborated value changed ({len(ud)}):** ' + ', '.join(f'`{n}`' for n in ud) + '.\\n')
w(f'## Appendix C. All {n_down} changed lines of the proof modules (§4)\\n')
w('| module | line OLD → NEW | construct | OLD text | NEW text |'); w('|---|---|---|---|---|')
for r in rows:
    if r['file'] != 'wasm2.0': w(f'| `{r["file"]}` | {r["old"]} → {r["new"] if r["new"] else "—"} | `{r["construct"]}` | {code(esc(r["before"]))} | {code(esc(r["after"])) if r["after"] is not None else "(deleted)"} |')
w('')
w('## Appendix D. Byte-level facts (§1)\\n')
w('| module | OLD bytes | OLD md5 | NEW bytes | NEW md5 |'); w('|---|---|---|---|---|')
for m in MODS:
    a, b = BF[('old', m)], BF[('final', m)]; w(f'| `{m}.lean` | {fmt(a["size"])} | `{a["md5"]}` | {fmt(b["size"])} | `{b["md5"]}` |')
w('')
w('## Appendix E. Verifier findings and how each was addressed\\n')
w('Each verifier finding (V1 = `V-REPORT-1` on version 1; FIX, FRESH and CRITIC = the three verifiers on version 2) is in `verification/`. None found an error in the repair or in the line accounting. Several found the same point independently; such points are listed once.\\n')
w('| finding | point | how it is addressed in version 3 |'); w('|---|---|---|')
for fid, pt, res in RESOLUTIONS: w(f'| {fid} | {pt} | {res} |')""")
open(p, 'w').write(s)
print('stage 2 ok')

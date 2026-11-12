import json, re, sys
from collections import Counter, OrderedDict
sys.path.insert(0, sys.argv[1]); from toplevel32 import constructs, code_mask
W = sys.argv[2]
L = open(W + '/cand1.lean').read()[:-1].split('\n'); code = code_mask(L); cons = constructs(L)
devs = json.load(open(W + '/cand1.lean.devs.json')); cm = json.load(open(W + '/ctor_map.json'))['wf_admininstr']
hel = []
for i, l in enumerate(L):
    if l.strip() == '/- HELPER LEMMA CREATED BY CLAUDE -/':
        hel.append(next(c['name'] for c in cons if c['line'] > i + 1))
def kind(n):
    if n in hel: return 'helper lemma'
    if n in ('Step_read_is_wf', 'Step_is_wf'): return 'hand-edited generated theorem'
    return 'generated theorem'
per = OrderedDict()
for d in devs:
    n = d['construct'].split(' ', 1)[1]; per.setdefault(n, []).append(d)
used = sorted({r for d in devs for r in map(tuple, d['renames'])}, key=lambda x: int(x[0].split('_')[-1]))
o = []
o.append('# Deviations when copying into the regenerated `wasm2.0.lean` (bundle32)\n')
o.append('Written for: the user, and later sessions. Date: 2026-11-11.\n')
o.append('This is the exhaustive list of every place where text copied from `OLD_wasm2.0.lean` (the theorems\' proofs, the two hand-edited theorems, and the 92 helper lemmas marked `/- HELPER LEMMA CREATED BY CLAUDE -/`) differs from the copy in the new `spectec/src/test-lean-claude/wasm2.0.lean`.\n')
o.append('## 1. Summary\n')
o.append('- **One kind of deviation, %d lines, in %d top-level constructs.** Every deviation renames a `wf_admininstr` constructor reference, `admininstr_case_K` to `admininstr_case_{K-1}` (K ≥ 20).' % (len(devs), len(per)))
o.append('  - **Why:** the regenerated model no longer has the `EXTEND numtype n` instruction. So the generated `wf_admininstr` lost its constructor `admininstr_case_19` (`admininstr.EXTEND`), and every later constructor moved down by one. In the same way, `wf_instr` lost `instr_case_19` and renumbered `instr_case_20..67` to `19..66`, but the copied text never refers to a renumbered `instr_case_K`.')
o.append('  - **Each rename is by meaning, not by arithmetic.** The new name is the unique new constructor whose full text (argument telescope, premises and conclusion) is identical to the old constructor\'s. `admininstr_case_19` (EXTEND), the only constructor without a counterpart, is never referenced.')
o.append('  - **All %d lines are inside proof bodies.** No theorem or helper statement changed, and no line was added, removed or moved.' % len(devs))
o.append('- **Everything else was copied verbatim.** That is 1,865 hand-written lines, the same count as in `OLD_wasm2.0.lean`:')
o.append('  - the proofs of all 89 generated theorems;')
o.append('  - the two hand edits, as in OLD: `Step_read_is_wf` and `Step_is_wf` moved below `Store_ok` and given a `Store_ok (fun_store z)` premise, with the commented-out generated originals and notes left at the generated places;')
o.append('  - all 92 helper lemmas, in 23 blocks, each marked and at the same position among the other top-level constructs.')
o.append('- **The deviations are necessary.** Compiling the verbatim copy gives 72 errors, and every one is within 2 lines of one of these %d lines. With the renames, the file compiles with 0 errors and no `sorry`.\n' % len(devs))
o.append('## 2. Deviations per construct\n')
o.append('| construct | kind | lines renamed | renames |')
o.append('|---|---|---|---|')
for n, ds in per.items():
    rs = Counter(tuple(r) for d in ds for r in map(tuple, d['renames']))
    o.append('| `%s` | %s | %d | %s |' % (n, kind(n), len(ds), ', '.join('`%s`→`%s` (×%d)' % (a, b, c) for (a, b), c in sorted(rs.items(), key=lambda x: int(x[0][0].split('_')[-1])))))
o.append('')
o.append('## 3. Constructor renames used\n')
o.append('Old name (in `OLD_wasm2.0.lean`), new name (in `wasm2.0.lean`), and the instruction the constructor is about. Each pair is the unique match by the constructor\'s full text.\n')
o.append('| old | new | constructor for | lines |')
o.append('|---|---|---|---|')
cnt = Counter(tuple(r) for d in devs for r in map(tuple, d['renames']))
for a, b in used:
    o.append('| `%s` | `%s` | `admininstr.%s` | %d |' % (a, b, cm['instr_of_old_ctor'][a], sum(1 for d in devs if [a, b] in d['renames'])))
o.append('')
o.append('## 4. Every deviation, line by line\n')
o.append('Line numbers: `OLD` = `OLD_wasm2.0.lean`, `new` = the installed `wasm2.0.lean`. The text is the full line with leading spaces trimmed; only the constructor name differs between "before" and "after".\n')
o.append('| # | construct | OLD line | new line | before | after |')
o.append('|---|---|---|---|---|---|')
for k, d in enumerate(devs, 1):
    n = d['construct'].split(' ', 1)[1]
    esc = lambda s: s.strip().replace('|', '\\|')
    o.append('| %d | `%s` | %d | %d | `%s` | `%s` |' % (k, n, d['old_line'], d['new_line'], esc(d['before']), esc(d['after'])))
o.append('')
open(sys.argv[3], 'w').write('\n'.join(o) + '\n')
print('per construct:', {n: len(ds) for n, ds in per.items()}, 'renames used:', len(used))

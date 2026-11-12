# bundle32 structural verification of the candidate wasm2.0.lean against OLD_wasm2.0.lean (OLD),
# the old generated base (G_old) and the new generated model (G_new).
# Usage: python3 -I verify32.py G_old OLD G_new CAND TOOLSDIR CTORMAP DEVSJSON
# Checks (each prints PASS/FAIL):
#  1. top-level constructs: same (kind, name) list, same order, CAND vs OLD (exhaustive)
#  2. helper lemmas: every `/- HELPER LEMMA CREATED BY CLAUDE -/` marker in OLD has a counterpart in CAND,
#     attached to the same theorem name, in the same order; same count; each marker directly precedes a theorem
#  3. theorems: the 89 generated theorems in G_new all present in CAND; statements of the 87 non-hand-edited
#     theorems byte-identical to G_new's (up to the final `:=` / `:= by`); the 2 hand-edited statements
#     identical to OLD's
#  4. generated text: removing CAND's hand-written regions gives back G_new except the 186 replaced lines
#     (the 87 `sorry`/`:=` tails and the 2 commented-out originals); i.e. every G_new line appears, in order
#  5. hand-written text: CAND's non-generated lines equal OLD's non-generated lines except exactly the
#     logged deviation lines (DEVSJSON), and each logged deviation is a constructor rename per CTORMAP
#  6. no `sorry` outside comments; the word occurs only in the 2 commented-out original statements
#  7. helper placement: each helper sits in the block directly above the first top-level construct that
#     mentions it (as in OLD), and nothing earlier mentions it
import re, sys, json, difflib
sys.path.insert(0, sys.argv[5]); from toplevel32 import constructs, code_mask
G_old_p, OLD_p, G_new_p, CAND_p, _, CMAP_p, DEVS_p = sys.argv[1:8]
def rd(p):
    s = open(p).read(); assert s.endswith('\n'); return s[:-1].split('\n')
G_old, OLD, G_new, CAND = rd(G_old_p), rd(OLD_p), rd(G_new_p), rd(CAND_p)
cmap = json.load(open(CMAP_p)); devs = json.load(open(DEVS_p))
ok_all = True
def report(name, ok, detail=''):
    global ok_all
    ok_all &= ok
    print(('PASS' if ok else 'FAIL'), name, ('- ' + detail if detail else ''))

# 1. top-level constructs
cO, cC, cN = constructs(OLD), constructs(CAND), constructs(G_new)
kO = [(c['kind'], c['name']) for c in cO]; kC = [(c['kind'], c['name']) for c in cC]
unk = [c for c in cO + cC if c['kind'] == 'UNKNOWN']
report('1a no unrecognised column-0 code lines', not unk, str(unk[:5]))
report('1b top-level (kind,name) sequence CAND == OLD (set and order)', kO == kC,
       'OLD %d constructs, CAND %d' % (len(kO), len(kC)))
if kO != kC:
    for op in difflib.SequenceMatcher(None, kO, kC, autojunk=False).get_opcodes():
        if op[0] != 'equal': print('   diff', op, kO[op[1]:op[2]][:5], kC[op[3]:op[4]][:5])
report('1c set of names equal', set(kO) == set(kC) and len(set(kO)) == len(set(kC)))
dupO = sorted({k for k in kO if kO.count(k) > 1 and k[0] not in ('mutual', 'end')})
print('   (duplicate (kind,name) pairs in OLD, excluding mutual/end: %s)' % dupO)
from collections import Counter
print('   construct kinds in CAND:', dict(Counter(k for k, _ in kC)))
# generated constructs of G_new are a subsequence of CAND's, in order (CAND = G_new + helpers, with the
# two hand-edited theorems moved)
kN = [(c['kind'], c['name']) for c in cN]
moved = {('theorem', 'Step_read_is_wf'), ('theorem', 'Step_is_wf')}
helpers_C = []
mark = '/- HELPER LEMMA CREATED BY CLAUDE -/'
def helper_names(L, cons):
    out = []
    for i, l in enumerate(L):
        if l.strip() == mark:
            nxt = next(c for c in cons if c['line'] > i + 1)
            out.append((i + 1, nxt['kind'], nxt['name'], nxt['line'] == i + 2))
    return out
hO, hC = helper_names(OLD, cO), helper_names(CAND, cC)
kC_nohelp = [k for k in kC if not (k[0] == 'theorem' and k[1] in {h[2] for h in hC})]
kN_nomoved = [k for k in kN if k not in moved]; kC_nomoved = [k for k in kC_nohelp if k not in moved]
report('1d CAND minus helpers minus moved theorems == G_new minus moved theorems (order)', kN_nomoved == kC_nomoved,
       'G_new %d constructs' % len(kN))
# 2. helpers
report('2a helper marker count OLD == CAND', len(hO) == len(hC), 'OLD %d, CAND %d' % (len(hO), len(hC)))
report('2b helper names, same order', [h[2] for h in hO] == [h[2] for h in hC])
report('2c every marker immediately followed by a theorem line', all(h[1] == 'theorem' and h[3] for h in hC))
report('2d helper names unique', len({h[2] for h in hC}) == len(hC))
# helper neighbourhood: for each helper, the previous and next non-helper construct are the same in OLD and CAND
def neighbours(cons, hset):
    res = {}
    seq = [(c['kind'], c['name']) for c in cons]
    for idx, k in enumerate(seq):
        if k[0] == 'theorem' and k[1] in hset:
            p = next((seq[j] for j in range(idx - 1, -1, -1) if not (seq[j][0] == 'theorem' and seq[j][1] in hset)), None)
            n = next((seq[j] for j in range(idx + 1, len(seq)) if not (seq[j][0] == 'theorem' and seq[j][1] in hset)), None)
            res[k[1]] = (p, n)
    return res
hset = {h[2] for h in hO}
report('2e each helper has the same preceding and following non-helper construct in OLD and CAND',
       neighbours(cO, hset) == neighbours(cC, hset))
# 3. theorems
def theorem_texts(L, cons):
    out = {}
    for c in cons:
        if c['kind'] == 'theorem': out[c['name']] = '\n'.join(L[c['line'] - 1:c['end']])
    return out
tN, tC, tO = theorem_texts(G_new, cN), theorem_texts(CAND, cC), theorem_texts(OLD, cO)
gen_thms = [k[1] for k in kN if k[0] == 'theorem']
report('3a generated theorems in G_new all present in CAND', all(t in tC for t in gen_thms), '%d generated theorems' % len(gen_thms))
def stmt_of_generated(txt):
    assert txt.endswith(':=\n  sorry'), txt[-40:]
    return txt[:-len(':=\n  sorry')]
bad = []
for t in gen_thms:
    if ('theorem', t) in moved: continue
    s = stmt_of_generated(tN[t])
    if not (tC[t].startswith(s + ':=') ): bad.append(t)
report('3b statements of the %d non-hand-edited generated theorems byte-identical to G_new' % (len(gen_thms) - 2), not bad, str(bad[:5]))
def stmt_upto_assign(txt):
    # the hand-edited statements end with ':= by' on the last premise line
    i = txt.index(':= by'); return txt[:i]
report('3c hand-edited Step_read_is_wf / Step_is_wf statements identical to OLD',
       all(stmt_upto_assign(tC[t]) == stmt_upto_assign(tO[t]) for t in ('Step_read_is_wf', 'Step_is_wf')))
report('3d theorem count CAND == OLD', len(tC) == len(tO), 'OLD %d, CAND %d' % (len(tO), len(tC)))
nonhelper_thms = [t for t in tC if t not in hset]
report('3e non-helper theorems in CAND == generated theorems', sorted(nonhelper_thms) == sorted(gen_thms), '%d' % len(nonhelper_thms))
# 4. generated text preserved
sm = difflib.SequenceMatcher(None, G_new, CAND, autojunk=False)
missing = []
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag in ('replace', 'delete'): missing += list(range(i1, i2))
miss_txt = Counter()
for i in missing:
    l = G_new[i]
    if l == '  sorry': miss_txt['  sorry'] += 1
    elif l.rstrip().endswith(':='): miss_txt['statement line ending in :='] += 1
    else: miss_txt['other: ' + l] += 1
other = {k: v for k, v in miss_txt.items() if k.startswith('other')}
ok4 = (miss_txt['  sorry'] == 89 and miss_txt['statement line ending in :='] == 89 and sum(other.values()) == 8 and set(other) <= {
    'other: /- Well-Formedness Theorem at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 -/',
    'other: theorem Step_read_is_wf (var_0 : config) (var_1 : List admininstr) :',
    'other:   wf_config var_0 →', 'other:   Step_read var_0 var_1 →',
    'other:   Forall (fun (var_1_elem : admininstr) => wf_admininstr var_1_elem) var_1 :=',
    'other: /- Well-Formedness Theorem at: ../specification/wasm-2.0/8-reduction.spectec:5.10-5.14 -/',
    'other: theorem Step_is_wf (var_0 : config) (var_1 : config) :', 'other:   Step var_0 var_1 →',
    'other:   wf_config var_1 :='})
report('4 G_new lines not kept verbatim in CAND are only the sorry/:= tails and the 2 commented-out originals', ok4,
       '%d G_new lines replaced: %s' % (len(missing), dict(miss_txt)))
# 5. hand-written text vs OLD (via G_old alignment)
def hand_lines(base, L):
    s = difflib.SequenceMatcher(None, base, L, autojunk=False); out = []
    for tag, i1, i2, j1, j2 in s.get_opcodes():
        if tag != 'equal': out += [(j + 1, L[j]) for j in range(j1, j2)]
    return out
hO_lines = hand_lines(G_old, OLD); hC_lines = hand_lines(G_new, CAND)
report('5a hand-written line count OLD == CAND', len(hO_lines) == len(hC_lines), 'OLD %d, CAND %d' % (len(hO_lines), len(hC_lines)))
diffs = [(a, b) for a, b in zip(hO_lines, hC_lines) if a[1] != b[1]]
dev_pairs = {(d['old_line'], d['new_line']) for d in devs}
report('5b differing hand-written lines are exactly the logged deviations', {(a[0], b[0]) for a, b in diffs} == dev_pairs,
       '%d differing, %d logged' % (len(diffs), len(dev_pairs)))
allmap = {}
for ind in ('wf_instr', 'wf_admininstr'): allmap.update(cmap[ind]['map'])
def renamed_ok(a, b):
    return re.sub(r'\b(?:admininstr_case_|instr_case_)\d+\b', lambda m: allmap[m.group(0)], a) == b
report('5c every deviation is exactly a constructor rename by meaning (ctor map)', all(renamed_ok(a[1], b[1]) for a, b in diffs))
# 6. sorry
code = code_mask(CAND)
report('6a no `sorry` in code (outside comments)', not any(re.search(r'\bsorry\b', c) for c in code))
occ = [i + 1 for i, l in enumerate(CAND) if re.search(r'\bsorry\b', l)]
report('6b `sorry` occurs only in the 2 commented-out originals', len(occ) == 2 and all(CAND[i - 1].startswith('--   sorry') for i in occ), str(occ))
# 7. helper placement (directly above first user, nothing earlier mentions it)
cons = cC; seq = []
for c in cons:
    seq.append((c, '\n'.join(code[c['line'] - 1:c['end']])))
bad7 = []
for h in hC:
    name = h[2]; pat = re.compile(r'(?<![\w.\'!?₀-₉])' + re.escape(name) + r'(?![\w\'!?₀-₉])')
    idx = next(i for i, (c, _) in enumerate(seq) if c['kind'] == 'theorem' and c['name'] == name)
    users = [i for i, (c, t) in enumerate(seq) if i != idx and pat.search(t)]
    if not users: bad7.append((name, 'unused')); continue
    first = users[0]
    if first < idx: bad7.append((name, 'used before')); continue
    # everything between helper and first user must be helpers (the same block)
    between = [seq[i][0] for i in range(idx + 1, first)]
    if any(not (b['kind'] == 'theorem' and b['name'] in hset) for b in between): bad7.append((name, 'not directly above first user', seq[first][0]['name']))
report('7 helper placement: each helper is in the block directly above its first user', not bad7, str(bad7[:8]))
print('ALL PASS' if ok_all else 'SOME CHECKS FAILED')

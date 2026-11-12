#!/usr/bin/env python3
"""V-EXH: second, algorithm-independent check (difflib instead of GNU diff).
1. H_old := difflib opcodes of G_old -> OLD.
2. Rebuild expected candidate: walk G_new; for every H_old hunk, find its G_new position via the
   G_old->G_new equal-block mapping, and splice in OLD's hand text. Refuse if a hunk touches a model-delta line.
3. Apply the 56 logged deviations (by new_line) and compare byte-for-byte to cand1."""
import sys, json, difflib

W = sys.argv[1]; A = sys.argv[2]
def rd(p):
    s = open(p, encoding='utf-8').read(); assert s.endswith('\n'); return s.split('\n')[:-1]
G_old = rd(f'{W}/G_old.lean'); OLD = rd(f'{W}/OLD.lean'); G_new = rd(f'{W}/G_new.lean'); C = rd(f'{W}/cand1.lean')

# Use a large-but-not-junking matcher; autojunk=False so frequent lines (blank, sorry) are not junked.
def ops(a, b):
    return difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes()

H = [o for o in ops(G_old, OLD) if o[0] != 'equal']
print('difflib G_old->OLD non-equal opcodes:', len(H),
      ' removed gen lines:', sum(i2 - i1 for _, i1, i2, _, _ in H),
      ' inserted hand lines:', sum(j2 - j1 for _, _, _, j1, j2 in H))
H2 = [o for o in ops(G_new, C) if o[0] != 'equal']
print('difflib G_new->cand1 non-equal opcodes:', len(H2),
      ' removed gen lines:', sum(i2 - i1 for _, i1, i2, _, _ in H2),
      ' inserted hand lines:', sum(j2 - j1 for _, _, _, j1, j2 in H2))

# old->new map for generated lines
m = {}
delta = set()
for tag, i1, i2, j1, j2 in ops(G_old, G_new):
    if tag == 'equal':
        for k in range(i2 - i1): m[i1 + k] = j1 + k
    else:
        delta.update(range(i1, i2))
# boundary map: position p in G_old (0..len) -> position in G_new, defined when line p-1 or p is mapped consistently
def mappos(p):
    if p < len(G_old) and p in m: return m[p]
    if p - 1 in m: return m[p - 1] + 1
    return None

exp = []; inew = 0; issues = []
for tag, i1, i2, j1, j2 in H:
    # hunk replaces G_old[i1:i2] by OLD[j1:j2]
    if any(x in delta for x in range(i1, i2)):
        issues.append(('hunk touches model delta', i1, i2))
    p1 = mappos(i1) if i1 < i2 else mappos(i1)
    if i1 < i2:
        ln = [m.get(x) for x in range(i1, i2)]
        if None in ln or ln != list(range(ln[0], ln[0] + len(ln))):
            issues.append(('non-contiguous mapping', i1, i2, ln)); continue
        p1 = ln[0]; p2 = ln[-1] + 1
    else:
        # pure insertion before G_old[i1]: require both neighbours mapped adjacently
        a = m.get(i1 - 1); b = m.get(i1)
        if i1 > 0 and a is None or i1 < len(G_old) and b is None or (a is not None and b is not None and b != a + 1):
            issues.append(('insertion point ambiguous', i1, a, b))
        p1 = p2 = (a + 1) if a is not None else b
    exp.extend(G_new[inew:p1]); exp.extend(OLD[j1:j2]); inew = p2
exp.extend(G_new[inew:])
print('reconstruction issues:', issues)
print('expected length:', len(exp), ' cand1 length:', len(C))

devs = json.load(open(f'{W}/cand1.lean.devs.json'))
exp_dev = list(exp)
for d in devs:
    k = d['new_line'] - 1
    assert exp_dev[k] == d['before'], ('before text mismatch at expected line', d['new_line'], exp_dev[k], d['before'])
    exp_dev[k] = d['after']
diffs = [(i + 1, a, b) for i, (a, b) in enumerate(zip(exp, C)) if a != b]
print('expected(verbatim) vs cand1: differing lines =', len(diffs))
print('  differing line numbers == logged new_lines:', sorted(x[0] for x in diffs) == sorted(d['new_line'] for d in devs))
print('expected(+56 logged renames) == cand1 exactly:', exp_dev == C)
# byte-level check (newline at end, no stray chars)
print('byte-identical after re-join:', ('\n'.join(exp_dev) + '\n').encode() == open(f'{W}/cand1.lean', 'rb').read())

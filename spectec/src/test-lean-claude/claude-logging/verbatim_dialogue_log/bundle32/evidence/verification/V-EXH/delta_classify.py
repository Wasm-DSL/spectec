#!/usr/bin/env python3
"""V-EXH: classify every G_old -> G_new difference. Anything not explained by the EXTEND removal is printed."""
import sys, re, difflib
W = sys.argv[1]
def rd(p):
    s = open(p, encoding='utf-8').read(); assert s.endswith('\n'); return s.split('\n')[:-1]
G_old = rd(f'{W}/G_old.lean'); G_new = rd(f'{W}/G_new.lean')

def norm(l):
    l = re.sub(r'\b(admininstr_case|instr_case)_\d+\b', r'\1_N', l)
    l = re.sub(r'spectec:\d+\.\d+-\d+\.\d+', 'spectec:POS', l)
    return l

ops = difflib.SequenceMatcher(None, G_old, G_new, autojunk=False).get_opcodes()
removed_extend = []; unexplained = []; renum = 0; pos = 0
for tag, i1, i2, j1, j2 in ops:
    if tag == 'equal': continue
    a = G_old[i1:i2]; b = G_new[j1:j2]
    # drop EXTEND lines (and continuation lines of a dropped EXTEND constructor) from the old side
    a_kept = []
    for l in a:
        if 'EXTEND' in l:
            removed_extend.append(l)
        else:
            a_kept.append(l)
    if 'EXTEND' in ''.join(b):
        unexplained.append(('EXTEND in new', i1 + 1, b))
    if [norm(x) for x in a_kept] == [norm(x) for x in b]:
        for x, y in zip(a_kept, b):
            if x != y:
                if 'spectec:' in x: pos += 1
                else: renum += 1
    else:
        unexplained.append((tag, i1 + 1, i2, j1 + 1, j2, a, b))
print('removed EXTEND lines:', len(removed_extend))
for l in removed_extend: print('   ', l)
print('renumbering-only changed lines:', renum, ' source-position comment lines:', pos)
print('unexplained hunks:', len(unexplained))
for u in unexplained: print(u)
# renumbering sanity: every renumbered case number decreases by exactly 1 and is >= 19 (old numbering >= 20)
bad = []
for tag, i1, i2, j1, j2 in ops:
    if tag != 'replace': continue
    a = [l for l in G_old[i1:i2] if 'EXTEND' not in l]; b = G_new[j1:j2]
    for x, y in zip(a, b):
        for (ka, na), (kb, nb) in zip(re.findall(r'\b(admininstr_case|instr_case)_(\d+)\b', x),
                                      re.findall(r'\b(admininstr_case|instr_case)_(\d+)\b', y)):
            if ka != kb or int(nb) != int(na) - 1 or int(na) < 20: bad.append((x, y))
print('renumberings that are not K -> K-1 with K >= 20:', bad)

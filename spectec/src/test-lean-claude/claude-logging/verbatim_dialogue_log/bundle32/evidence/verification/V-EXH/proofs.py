#!/usr/bin/env python3
"""V-EXH (e): for each of the generated theorems, compare its full block (header .. end) in OLD vs cand1,
and check that cand1's statement text equals the generated statement in G_new (modulo ':=' line / hand edits)."""
import sys, re, json
W = sys.argv[1]
def rd(p):
    s = open(p, encoding='utf-8').read(); assert s.endswith('\n'); return s.split('\n')[:-1]
G_old = rd(f'{W}/G_old.lean'); OLD = rd(f'{W}/OLD.lean'); G_new = rd(f'{W}/G_new.lean'); C = rd(f'{W}/cand1.lean')
devs = json.load(open(f'{W}/cand1.lean.devs.json'))
dev_old = {d['old_line']: d for d in devs}

TH = re.compile(r'^theorem\s+(\S+)')
def theorems(L):
    return [(i + 1, TH.match(l).group(1)) for i, l in enumerate(L) if TH.match(l)]
def block(L, start):  # start 1-based header line; returns (start, end) 1-based inclusive
    j = start
    while j < len(L) and (L[j] == '' or L[j][0].isspace()): j += 1
    e = j
    while e > start and L[e - 1] == '': e -= 1
    return start, e

gen_old = theorems(G_old); gen_new = theorems(G_new)
names = [n for _, n in gen_old]
print('generated theorems: G_old', len(gen_old), ' G_new', len(gen_new), ' same names/order:', names == [n for _, n in gen_new])
O = dict((n, i) for i, n in theorems(OLD)); Cc = dict((n, i) for i, n in theorems(C))
tot = 0; bad = []; withdev = {}; proof_lines = 0; sorry_left = []
for n in names:
    if n not in O or n not in Cc:
        bad.append(('missing', n, n in O, n in Cc)); continue
    so, eo = block(OLD, O[n]); sc, ec = block(C, Cc[n])
    bo = OLD[so - 1:eo]; bc = C[sc - 1:ec]
    tot += len(bo)
    if len(bo) != len(bc):
        bad.append(('length', n, len(bo), len(bc))); continue
    for k, (a, b) in enumerate(zip(bo, bc)):
        if a != b:
            d = dev_old.get(so + k)
            if d and d['before'] == a and d['after'] == b and d['new_line'] == sc + k:
                withdev[n] = withdev.get(n, 0) + 1
            else:
                bad.append(('line', n, so + k, sc + k, a, b))
    # proof present? the block must not contain a bare 'sorry' token
    if any(re.search(r'\bsorry\b', l) for l in bc): sorry_left.append(n)
    # statement check vs G_new: generated statement = header .. line ending with ':=' ; cand1 has it ending ':= by'
    gs, ge = block(G_new, dict((nn, i) for i, nn in gen_new)[n])
    gb = G_new[gs - 1:ge]
    assert gb[-1].strip() == 'sorry', (n, gb[-1])
    gstmt = gb[:-1]
    if n in ('Step_read_is_wf', 'Step_is_wf'):
        continue  # hand-edited statements, checked separately
    cstmt = bc[:len(gstmt)]
    if cstmt[:-1] != gstmt[:-1] or not (cstmt[-1] == gstmt[-1] + ' by' or cstmt[-1] == gstmt[-1]):
        bad.append(('statement', n, gstmt[-1], cstmt[-1]))
    proof_lines += len(bc) - len(gstmt)
print('theorem blocks compared:', len(names), ' total OLD block lines:', tot, ' proof lines (excl. statements):', proof_lines)
print('theorems with logged deviations:', withdev, ' total', sum(withdev.values()))
print('problems:', len(bad))
for b in bad: print('  ', b)
print('generated theorems whose cand1 block still contains sorry:', sorry_left)
# how does each statement end in cand1? (':= by' vs ':=' + term)
ends = {}
for n in names:
    sc, ec = block(C, Cc[n])
    # find the line that ends the statement (first line containing ':=' at end or ':= by')
    for l in C[sc - 1:ec]:
        if l.rstrip().endswith(':= by') or l.rstrip().endswith(':='):
            ends[l.rstrip()[-5:]] = ends.get(l.rstrip()[-5:], 0) + 1; break
print('statement endings in cand1:', ends)
# global sorry count (as token, anywhere incl. comments)
for nm, L in [('G_old', G_old), ('OLD', OLD), ('G_new', G_new), ('cand1', C)]:
    occ = [(i + 1, l) for i, l in enumerate(L) if re.search(r'\bsorry\b', l)]
    print(nm, 'lines with token sorry:', len(occ), [x for x in occ if not x[1].lstrip().startswith('--')][:5] if nm in ('OLD', 'cand1') else '')

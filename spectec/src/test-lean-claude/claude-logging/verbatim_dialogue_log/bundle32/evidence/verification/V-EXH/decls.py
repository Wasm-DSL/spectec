#!/usr/bin/env python3
"""V-EXH: declaration-level checks (marker-based and marker-independent helper enumeration; theorem proofs)."""
import sys, re, json
W = sys.argv[1]
def rd(p):
    s = open(p, encoding='utf-8').read(); assert s.endswith('\n'); return s.split('\n')[:-1]
G_old = rd(f'{W}/G_old.lean'); OLD = rd(f'{W}/OLD.lean'); G_new = rd(f'{W}/G_new.lean'); C = rd(f'{W}/cand1.lean')
devs = json.load(open(f'{W}/cand1.lean.devs.json'))
dev_old = {d['old_line']: d for d in devs}; dev_new = {d['new_line']: d for d in devs}

MARK = '/- HELPER LEMMA CREATED BY CLAUDE -/'
# a declaration header: optional attributes/modifiers then a keyword, at column 0
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque|axiom|example)\b\s*([^\s:({\[]*)')

def decls(L):
    out = []
    for i, l in enumerate(L):
        m = DECL.match(l)
        if m: out.append((i + 1, m.group(1), m.group(2), l))
    return out

def col0_kinds(L):
    k = {}
    for l in L:
        if l and not l[0].isspace():
            w = l.split()[0]
            k[w] = k.get(w, 0) + 1
    return k

D = {n: decls(L) for n, L in [('G_old', G_old), ('OLD', OLD), ('G_new', G_new), ('C', C)]}
for n in D: print(n, 'declarations:', len(D[n]), ' theorems:', sum(1 for d in D[n] if d[1] == 'theorem'),
                  ' lemmas:', sum(1 for d in D[n] if d[1] == 'lemma'))

# ---- marker-based enumeration
def markers(L): return [i + 1 for i, l in enumerate(L) if l == MARK]
def marker_like(L): return [(i + 1, l) for i, l in enumerate(L) if 'HELPER' in l or 'CREATED BY CLAUDE' in l]
mo, mc = markers(OLD), markers(C)
print('exact marker lines: OLD', len(mo), ' cand1', len(mc), ' G_old', len(markers(G_old)), ' G_new', len(markers(G_new)))
print('marker-like lines (HELPER / CREATED BY CLAUDE) not exactly the marker: OLD',
      [x for x in marker_like(OLD) if x[1] != MARK], ' cand1', [x for x in marker_like(C) if x[1] != MARK])

def next_decl_after(L, line):
    for j in range(line, len(L)):
        m = DECL.match(L[j])
        if m: return j + 1, m.group(1), m.group(2)
    return None

def block_end(L, start):
    """end (inclusive, 1-based) of the declaration starting at `start`: up to the line before the next
    column-0 non-blank line, excluding trailing blank lines"""
    j = start  # 0-based index of the line after the header
    while j < len(L) and (L[j] == '' or L[j][0].isspace()):
        j += 1
    e = j  # exclusive 0-based
    while e > start and L[e - 1] == '': e -= 1
    return e  # 1-based inclusive end == e

helpers_old = []
for m in mo:
    nd = next_decl_after(OLD, m)
    helpers_old.append((m, nd))
    if nd[0] != m + 1: print('  marker not immediately followed by declaration header: OLD', m, '->', nd)
helpers_c = []
for m in mc:
    nd = next_decl_after(C, m)
    helpers_c.append((m, nd))
    if nd[0] != m + 1: print('  marker not immediately followed by declaration header: cand1', m, '->', nd)
print('helper decl kinds (OLD):', sorted(set(h[1][1] for h in helpers_old)))
names_mark_old = [h[1][2] for h in helpers_old]; names_mark_c = [h[1][2] for h in helpers_c]
print('helpers by marker: OLD', len(names_mark_old), 'distinct', len(set(names_mark_old)),
      '; cand1', len(names_mark_c), 'distinct', len(set(names_mark_c)))
print('helper name sequence identical OLD vs cand1:', names_mark_old == names_mark_c)

# ---- marker-independent enumeration
gold_names = {d[2] for d in D['G_old']}
gnew_names = {d[2] for d in D['G_new']}
extra_old = [d for d in D['OLD'] if d[2] not in gold_names]
extra_c = [d for d in D['C'] if d[2] not in gnew_names]
print('declarations in OLD not declared in G_old:', len(extra_old), ' kinds', sorted(set(d[1] for d in extra_old)))
print('declarations in cand1 not declared in G_new:', len(extra_c), ' kinds', sorted(set(d[1] for d in extra_c)))
print('marker-independent set == marker set (OLD):', [d[2] for d in extra_old] == names_mark_old)
print('marker-independent set == marker set (cand1):', [d[2] for d in extra_c] == names_mark_c)
for d in extra_old:
    if d[2] not in names_mark_old: print('   UNMARKED new decl in OLD:', d)
# duplicate declaration names
from collections import Counter
for n in D:
    dup = [k for k, v in Counter(d[2] for d in D[n]).items() if v > 1]
    print(n, 'duplicate declared names:', dup)
# declarations whose name appears commented-out etc: count of '-- theorem' lines
for n, L in [('OLD', OLD), ('C', C)]:
    print(n, 'commented-out theorem headers:', [(i + 1, l) for i, l in enumerate(L) if re.match(r'^--\s*theorem', l)])

# ---- full-text comparison of every helper (marker .. end of decl)
def helper_text(L, m, hdr):
    e = block_end(L, hdr)
    return L[m - 1:e], m, e
mism = []; n_lines = 0
for (mo_, ndo), (mc_, ndc) in zip(helpers_old, helpers_c):
    to, so, eo = helper_text(OLD, mo_, ndo[0]); tc, sc, ec = helper_text(C, mc_, ndc[0])
    n_lines += len(to)
    if len(to) != len(tc):
        mism.append(('len', ndo[2], len(to), len(tc))); continue
    for k, (a, b) in enumerate(zip(to, tc)):
        if a != b:
            d = dev_old.get(so + k)
            if not (d and d['before'] == a and d['after'] == b and d['new_line'] == sc + k):
                mism.append(('line', ndo[2], so + k, sc + k, a, b))
print('helper full-text comparison: lines compared', n_lines, ' unexplained mismatches', len(mism))
for x in mism: print('  ', x)
# helpers containing deviations
hd = {}
for (mo_, ndo) in helpers_old:
    to, so, eo = helper_text(OLD, mo_, ndo[0])
    k = [l for l in range(so, eo + 1) if l in dev_old]
    if k: hd[ndo[2]] = len(k)
print('helpers with logged deviations:', hd)
# contiguous blocks of helpers (groups separated by non-helper top-level material)
blocks = []
prev_end = None
for (m, nd) in helpers_old:
    _, s, e = helper_text(OLD, m, nd[0])
    if prev_end is not None and all(l == '' for l in OLD[prev_end:s - 1]):
        blocks[-1].append(nd[2])
    else:
        blocks.append([nd[2]])
    prev_end = e
print('helper blocks (consecutive helpers separated only by blank lines):', len(blocks), [len(b) for b in blocks])
json.dump(dict(helpers=names_mark_old, blocks=blocks), open(sys.argv[2] + '/helpers.json', 'w'), indent=1)

#!/usr/bin/env python3
"""V-ORD comparisons. Usage: python3 -I compare.py DIR (DIR holds G_old/OLD/G_new/cand1 .json)."""
import difflib
import json
import os
import sys
from collections import Counter

D = sys.argv[1]
F = {k: json.load(open(os.path.join(D, k + '.json'), encoding='utf-8')) for k in ('G_old', 'OLD', 'G_new', 'cand1')}
MOVED = {'Step_read_is_wf', 'Step_is_wf'}
fail = []


def seq(k, filt=None):
    cs = F[k]['constructs']
    return [(c['kind'], c['name']) for c in cs if (filt is None or filt(c))]


def show_diff(a, b, la, lb, limit=60):
    sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)
    out = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            continue
        out.append(f'  {tag}: {la}[{i1}:{i2}]={a[i1:i2][:8]} vs {lb}[{j1}:{j2}]={b[j1:j2][:8]}')
    return out[:limit]


def compare(label, a, b, la, lb):
    eq = (a == b)
    print(f'[{"OK" if eq else "DIFF"}] {label}: len {la}={len(a)} len {lb}={len(b)}')
    if not eq:
        fail.append(label)
        for l in show_diff(a, b, la, lb):
            print(l)
    return eq


print('=== per-kind counts')
kinds = sorted(set(c['kind'] for k in F for c in F[k]['constructs']))
hdr = 'kind'.ljust(14) + ''.join(k.rjust(8) for k in F)
print(hdr)
for kd in kinds:
    print(kd.ljust(14) + ''.join(str(sum(1 for c in F[k]['constructs'] if c['kind'] == kd)).rjust(8) for k in F))
print('total'.ljust(14) + ''.join(str(len(F[k]['constructs'])).rjust(8) for k in F))
print('helpers'.ljust(14) + ''.join(str(sum(c['helper'] for c in F[k]['constructs'])).rjust(8) for k in F))
print('deriving'.ljust(14) + ''.join(str(sum(len(c['deriving_lines']) for c in F[k]['constructs'])).rjust(8) for k in F))
print('helper thm'.ljust(14) + ''.join(str(sum(1 for c in F[k]['constructs'] if c['helper'] and c['kind'] == 'theorem')).rjust(8) for k in F))
print('non-thm helper'.ljust(14) + ''.join(str(sum(1 for c in F[k]['constructs'] if c['helper'] and c['kind'] != 'theorem')).rjust(8) for k in F))
print('multi-marker'.ljust(14) + ''.join(str(sum(1 for c in F[k]['constructs'] if c['marker_count'] > 1)).rjust(8) for k in F))

print('\n=== duplicates (kind,name) within each file (mutual/end excluded)')
for k in F:
    cnt = Counter((c['kind'], c['name']) for c in F[k]['constructs'] if c['kind'] not in ('mutual', 'end'))
    d = {x: n for x, n in cnt.items() if n > 1}
    cnt2 = Counter(c['name'] for c in F[k]['constructs'] if c['kind'] not in ('mutual', 'end'))
    d2 = {x: n for x, n in cnt2.items() if n > 1}
    print(f'  {k}: dup (kind,name)={d}  dup name across kinds={d2}')

print('\n=== exact sequence comparisons')
compare('cand1 vs OLD: (kind,name) full sequence', seq('cand1'), seq('OLD'), 'cand1', 'OLD')
compare('cand1 vs OLD: set of (kind,name)', sorted(set(seq('cand1'))), sorted(set(seq('OLD'))), 'cand1', 'OLD')
compare('G_new vs G_old: (kind,name) full sequence', seq('G_new'), seq('G_old'), 'G_new', 'G_old')
# helper flags & deriving & header comments, construct by construct, cand1 vs OLD
a = [(c['kind'], c['name'], c['helper'], tuple(c.get('deriving', []))) for c in F['cand1']['constructs']]
b = [(c['kind'], c['name'], c['helper'], tuple(c.get('deriving', []))) for c in F['OLD']['constructs']]
compare('cand1 vs OLD: (kind,name,helper-flag,deriving)', a, b, 'cand1', 'OLD')
a = [(c['kind'], c['name'], c['helper'], tuple(c.get('deriving', []))) for c in F['G_new']['constructs']]
b = [(c['kind'], c['name'], c['helper'], tuple(c.get('deriving', []))) for c in F['G_old']['constructs']]
compare('G_new vs G_old: (kind,name,helper-flag,deriving)', a, b, 'G_new', 'G_old')


def is_moved_restated(file, c):
    return c['kind'] == 'theorem' and c['name'] in MOVED


nonhelper = lambda c: not c['helper'] and not (c['kind'] == 'theorem' and c['name'] in MOVED)
compare('cand1 minus helpers minus moved theorems vs G_new minus the 2 theorems', seq('cand1', nonhelper), seq('G_new', nonhelper), 'cand1', 'G_new')
compare('OLD minus helpers minus moved theorems vs G_old minus the 2 theorems (method sanity)', seq('OLD', nonhelper), seq('G_old', nonhelper), 'OLD', 'G_old')

print('\n=== positions of the two theorems in each file')
for k in F:
    for i, c in enumerate(F[k]['constructs']):
        if c['kind'] == 'theorem' and c['name'] in MOVED:
            prev_nh = next((F[k]['constructs'][j] for j in range(i - 1, -1, -1) if not F[k]['constructs'][j]['helper']), None)
            nxt_nh = next((F[k]['constructs'][j] for j in range(i + 1, len(F[k]['constructs'])) if not F[k]['constructs'][j]['helper']), None)
            prev_any = F[k]['constructs'][i - 1]
            nxt_any = F[k]['constructs'][i + 1] if i + 1 < len(F[k]['constructs']) else None
            print(f'  {k}: idx {i} line {c["line"]} {c["name"]} | prev={prev_any["kind"]} {prev_any["name"]} (helper={prev_any["helper"]}) '
                  f'| next={nxt_any["kind"] if nxt_any else None} {nxt_any["name"] if nxt_any else None} '
                  f'| prev non-helper={prev_nh["kind"]} {prev_nh["name"]} | next non-helper={nxt_nh["kind"] if nxt_nh else None} {nxt_nh["name"] if nxt_nh else None}')

print('\n=== helper neighbours (nearest preceding / following non-helper construct), cand1 vs OLD')


def neighbours(k):
    cs = F[k]['constructs']
    res = {}
    blocks = []
    cur = None
    for i, c in enumerate(cs):
        if not c['helper']:
            cur = None
            continue
        prev_nh = next(((cs[j]['kind'], cs[j]['name']) for j in range(i - 1, -1, -1) if not cs[j]['helper']), None)
        nxt_nh = next(((cs[j]['kind'], cs[j]['name']) for j in range(i + 1, len(cs)) if not cs[j]['helper']), None)
        pos_in_block = 0
        j = i - 1
        while j >= 0 and cs[j]['helper']:
            pos_in_block += 1
            j -= 1
        if cur is None:
            cur = []
            blocks.append(cur)
        cur.append(c['name'])
        key = (c['kind'], c['name'])
        if key in res:
            print(f'  DUPLICATE helper {key} in {k}')
        res[key] = (prev_nh, nxt_nh, pos_in_block, c['line'])
    return res, blocks


nc, bc = neighbours('cand1')
no, bo = neighbours('OLD')
print(f'  helpers: cand1={len(nc)} OLD={len(no)}; helper blocks: cand1={len(bc)} OLD={len(bo)}')
print(f'  block sizes cand1={[len(b) for b in bc]}')
print(f'  block sizes OLD  ={[len(b) for b in bo]}')
print(f'  blocks identical (names, order): {bc == bo}')
mism = 0
for key in sorted(set(nc) | set(no)):
    if key not in nc or key not in no:
        print(f'  MISSING {key}: in cand1={key in nc} in OLD={key in no}')
        mism += 1
        continue
    if nc[key][:3] != no[key][:3]:
        print(f'  NEIGHBOUR MISMATCH {key}: cand1={nc[key]} OLD={no[key]}')
        mism += 1
print(f'  neighbour mismatches: {mism}')
if mism:
    fail.append('helper neighbours')

# Check that each helper block's preceding/following non-helper constructs exist in G_new adjacently
print('\n=== helper insertion points vs G_new adjacency')
gseq = seq('G_new')
gpos = {}
for i, x in enumerate(gseq):
    gpos.setdefault(x, []).append(i)
bad = 0
for key, (p, nx, pib, line) in nc.items():
    if pib != 0:
        continue
    if p is None or nx is None:
        print(f'  helper block at {key} has no prev/next non-helper: {p} {nx}')
        continue
    if p[1] in MOVED or nx[1] in MOVED:
        print(f'  helper block starting {key} borders a moved theorem: prev={p} next={nx}')
        continue
    ip = gpos.get(p, [])
    inx = gpos.get(nx, [])
    if len(ip) != 1 or len(inx) != 1 or inx[0] != ip[0] + 1:
        # if a moved theorem sits between them in G_new, report
        between = gseq[ip[0] + 1:inx[0]] if (len(ip) == 1 and len(inx) == 1 and inx[0] > ip[0]) else None
        print(f'  helper block starting {key}: prev={p}@{ip} next={nx}@{inx} not adjacent in G_new; between={between}')
        bad += 1
print(f'  non-adjacent insertion points (excluding moved-theorem borders): {bad}')

print('\n=== header comment comparison cand1 vs OLD (per construct, by index)')
hd = 0
for c1, c0 in zip(F['cand1']['constructs'], F['OLD']['constructs']):
    if c1['header'] != c0['header']:
        hd += 1
        if hd <= 15:
            print(f'  cand1 L{c1["line"]} {c1["kind"]} {c1["name"]}: {c1["header"]}  | OLD L{c0["line"]}: {c0["header"]}')
print(f'  header differences: {hd}')
print('\n=== header comment comparison cand1 vs G_new (non-helper, non-moved, aligned)')
a = [c for c in F['cand1']['constructs'] if nonhelper(c)]
b = [c for c in F['G_new']['constructs'] if nonhelper(c)]
hd = 0
for c1, c0 in zip(a, b):
    if c1['header'] != c0['header']:
        hd += 1
        if hd <= 15:
            print(f'  cand1 L{c1["line"]} {c1["kind"]} {c1["name"]}: {c1["header"]}  | G_new L{c0["line"]}: {c0["header"]}')
print(f'  header differences: {hd}')

print('\n=== RESULT: failures =', fail)

#!/usr/bin/env python3
"""Supplementary V-ORD checks. Usage: python3 -I supp.py DIR"""
import json
import os
import re
import sys

D = sys.argv[1]
F = {k: json.load(open(os.path.join(D, k + '.json'), encoding='utf-8')) for k in ('G_old', 'OLD', 'G_new', 'cand1')}
MOVED = {'Step_read_is_wf', 'Step_is_wf'}
nonhelper = lambda c: not c['helper'] and not (c['kind'] == 'theorem' and c['name'] in MOVED)

# (a) every header difference cand1-vs-OLD must be explained by the generated model change
print('=== (a) header differences cand1 vs OLD, explained by G_new vs G_old?')
c1 = F['cand1']['constructs']
o = F['OLD']['constructs']
gn = [c for c in F['G_new']['constructs'] if nonhelper(c)]
go = [c for c in F['G_old']['constructs'] if nonhelper(c)]
gn_by = {}
for i, c in enumerate(gn):
    gn_by[(c['kind'], c['name'], sum(1 for x in gn[:i] if (x['kind'], x['name']) == (c['kind'], c['name'])))] = c
go_by = {}
for i, c in enumerate(go):
    go_by[(c['kind'], c['name'], sum(1 for x in go[:i] if (x['kind'], x['name']) == (c['kind'], c['name'])))] = c
seen = {}
unexpl = 0
ndiff = 0
for a, b in zip(c1, o):
    key0 = (a['kind'], a['name'])
    occ = seen.get(key0, 0)
    seen[key0] = occ + 1
    if a['header'] == b['header']:
        continue
    ndiff += 1
    if not nonhelper(a):
        print(f'  UNEXPLAINED (hand-layer construct) cand1 L{a["line"]} {key0}: {a["header"]} vs OLD {b["header"]}')
        unexpl += 1
        continue
    # count occurrence among nonhelper constructs
    k = (a['kind'], a['name'], sum(1 for x in c1[:c1.index(a)] if nonhelper(x) and (x['kind'], x['name']) == key0))
    g_new_h = gn_by[k]['header']
    g_old_h = go_by[k]['header']
    # expected: cand1 header = OLD header with the generated comment replaced by G_new's
    a_gen = [h for h in a['header'] if h not in b['header']]
    b_gen = [h for h in b['header'] if h not in a['header']]
    ok = (a_gen == [h for h in g_new_h if h not in g_old_h]) and (b_gen == [h for h in g_old_h if h not in g_new_h])
    if not ok:
        unexpl += 1
        print(f'  UNEXPLAINED cand1 L{a["line"]} {key0}: cand1-only={a_gen} OLD-only={b_gen} G_new={g_new_h} G_old={g_old_h}')
    else:
        print(f'  explained: L{a["line"]} {a["kind"]} {a["name"]}: {b_gen[0][-40:]} -> {a_gen[0][-40:]}')
print(f'  total header diffs={ndiff}, unexplained={unexpl}')
cnt_gen_hdr_diff = sum(1 for x, y in zip(gn, go) if x['header'] != y['header'])
print(f'  header diffs between G_new and G_old (aligned non-moved constructs) = {cnt_gen_hdr_diff}')

# (b) helper-block counting under two definitions
print('\n=== (b) helper block counts')
def runs(cs, member):
    r = []
    cur = None
    for c in cs:
        if member(c):
            if cur is None:
                cur = []
                r.append(cur)
            cur.append(c['name'])
        else:
            cur = None
    return r
for k in ('OLD', 'cand1'):
    cs = F[k]['constructs']
    r1 = runs(cs, lambda c: c['helper'])
    r2 = [x for x in runs(cs, lambda c: c['helper'] or (c['kind'] == 'theorem' and c['name'] in MOVED and c['line'] > 16000))
          if any(n not in MOVED for n in x)]
    print(f'  {k}: maximal runs of helpers = {len(r1)}; runs of hand-layer (helpers + re-stated theorems) = {len(r2)}')

# (c) body-level comparison of generated constructs: cand1 vs G_new
print('\n=== (c) code-only bodies of non-helper, non-moved constructs: cand1 vs G_new')
a = [c for c in c1 if nonhelper(c)]
same = diff = 0
stmt_bad = []
for x, y in zip(a, gn):
    if x['body_norm'] == y['body_norm']:
        same += 1
        continue
    diff += 1
    # expected only for generated theorems whose `:= sorry` got a proof
    yb = y['body_norm']
    if x['kind'] == 'theorem' and yb.endswith(':= sorry'):
        stmt = yb[:-len('sorry')]
        if not x['body_norm'].startswith(stmt):
            stmt_bad.append((x['line'], x['name']))
    else:
        stmt_bad.append((x['line'], x['name'], 'non-theorem body differs'))
print(f'  identical={same} differing={diff}; differing ones whose statement (text up to ":= sorry") is NOT a prefix: {stmt_bad}')
thm_with_sorry = sum(1 for y in gn if y['kind'] == 'theorem' and y['body_norm'].endswith(':= sorry'))
print(f'  G_new non-moved theorems ending ":= sorry": {thm_with_sorry}')

print('\n=== (c2) same for OLD vs G_old (method sanity)')
a = [c for c in o if nonhelper(c)]
same = diff = 0
stmt_bad = []
for x, y in zip(a, go):
    if x['body_norm'] == y['body_norm']:
        same += 1
        continue
    diff += 1
    yb = y['body_norm']
    if x['kind'] == 'theorem' and yb.endswith(':= sorry'):
        if not x['body_norm'].startswith(yb[:-len('sorry')]):
            stmt_bad.append((x['line'], x['name']))
    else:
        stmt_bad.append((x['line'], x['name'], 'non-theorem body differs'))
print(f'  identical={same} differing={diff}; bad={stmt_bad}')

# (d) proofs of generated theorems cand1 vs OLD; helpers cand1 vs OLD
print('\n=== (d) hand-layer bodies cand1 vs OLD (expect differences only where the log lists deviations)')
dif = []
for x, y in zip(c1, o):
    if x['kind'] == 'theorem' and x['body_norm'] != y['body_norm']:
        dif.append((x['name'], x['line'], y['line'], 'helper' if x['helper'] else 'gen/moved'))
for d in dif:
    print('  differs:', d)
print(f'  theorems whose code-only body differs cand1 vs OLD: {len(dif)}')

# (e) sorry / admit / EXTEND in code-only text of cand1
print('\n=== (e) code-only tokens in cand1')
txt = open(os.path.join('/tmp/claude-1002/-home-zhengyew-spectec/0793c03a-21df-4d2d-9729-4ba22978b528/scratchpad/b32/work', 'cand1.lean'), encoding='utf-8').read()
sys.path.insert(0, D)
from extract import lex  # noqa: E402
code_lines, cmt_lines, _ = lex(txt)
for w in ('sorry', 'admit', 'EXTEND', 'instr_case_67', 'admininstr_case_73', 'native_decide', 'axiom'):
    hits = [i + 1 for i, l in enumerate(code_lines) if re.search(r"(?<![\w'.])" + re.escape(w) + r"(?![\w'!?])", l)]
    print(f'  {w}: {len(hits)} code lines {hits[:10]}')
cm_sorry = [i + 1 for i, l in enumerate(cmt_lines) if 'sorry' in l]
print(f'  sorry inside comments: {cm_sorry}')

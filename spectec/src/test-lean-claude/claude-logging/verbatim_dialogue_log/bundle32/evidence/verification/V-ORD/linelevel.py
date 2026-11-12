#!/usr/bin/env python3
"""Raw line-level alignment of cand1 vs OLD per construct (V-ORD cross-check).

For each construct pair aligned by index (sequences are already known to be equal):
  * hand-layer constructs (helpers, theorems): raw lines from header_start..end must be
    identical except at lines listed in the deviation JSON (old_line/new_line), and the
    line counts must be equal (no added/removed/moved line);
  * generated non-theorem constructs: cand1 raw lines must equal G_new's raw lines and
    OLD raw lines must equal G_old's (so all differences are explained by the regen).
Usage: python3 -I linelevel.py AGENTDIR WORKDIR
"""
import json
import os
import sys

A, W = sys.argv[1], sys.argv[2]
J = {k: json.load(open(os.path.join(A, k + '.json'), encoding='utf-8')) for k in ('G_old', 'OLD', 'G_new', 'cand1')}
R = {k: open(os.path.join(W, k + '.lean'), encoding='utf-8').read().split('\n') for k in ('G_old', 'OLD', 'G_new', 'cand1')}
devs = json.load(open(os.path.join(W, 'cand1.lean.devs.json'), encoding='utf-8'))
dev_pairs = {(d['old_line'], d['new_line']): d for d in devs}
dev_old = {d['old_line'] for d in devs}
dev_new = {d['new_line'] for d in devs}
MOVED = {'Step_read_is_wf', 'Step_is_wf'}

found_pairs = set()
problems = []
c1, o = J['cand1']['constructs'], J['OLD']['constructs']
gn, go = J['G_new']['constructs'], J['G_old']['constructs']
nonhelper = lambda c: not c['helper'] and not (c['kind'] == 'theorem' and c['name'] in MOVED)
gn_nh = [c for c in gn if nonhelper(c)]
go_nh = [c for c in go if nonhelper(c)]
k_nh = 0
total_hand_lines = 0
for a, b in zip(c1, o):
    la = R['cand1'][a['header_start'] - 1:a['end']]
    lb = R['OLD'][b['header_start'] - 1:b['end']]
    is_nh = nonhelper(a)
    if is_nh:
        g_a = gn_nh[k_nh]
        g_b = go_nh[k_nh]
        k_nh += 1
    if a['kind'] == 'theorem':
        # theorem: compare cand1 vs OLD line by line (statement lines included)
        if len(la) != len(lb):
            problems.append(f'line count differs for theorem {a["name"]}: cand1 {len(la)} OLD {len(lb)}')
            continue
        for off, (x, y) in enumerate(zip(la, lb)):
            ln_a = a['header_start'] + off
            ln_b = b['header_start'] + off
            if x != y:
                if (ln_b, ln_a) in dev_pairs and dev_pairs[(ln_b, ln_a)]['before'] == y and dev_pairs[(ln_b, ln_a)]['after'] == x:
                    found_pairs.add((ln_b, ln_a))
                else:
                    problems.append(f'UNLOGGED diff in {a["name"]}: OLD L{ln_b} {y!r} vs cand1 L{ln_a} {x!r}')
            elif (ln_b, ln_a) in dev_pairs:
                problems.append(f'logged deviation but lines equal: OLD L{ln_b} cand1 L{ln_a}')
        # count hand-written lines: for generated theorems only the proof part counts; skip
        if not is_nh or True:
            pass
    else:
        if a['helper']:
            problems.append(f'non-theorem helper?? {a}')
        # generated non-theorem: cand1 must equal G_new raw text (except header comments around moved thms)
        ga = R['G_new'][g_a['line'] - 1:g_a['end']]
        gb = R['G_old'][g_b['line'] - 1:g_b['end']]
        ca = R['cand1'][a['line'] - 1:a['end']]
        ob = R['OLD'][b['line'] - 1:b['end']]
        if ca != ga:
            problems.append(f'generated construct {a["kind"]} {a["name"]} (cand1 L{a["line"]}) differs from G_new L{g_a["line"]} at raw level')
        if ob != gb:
            problems.append(f'generated construct {b["kind"]} {b["name"]} (OLD L{b["line"]}) differs from G_old L{g_b["line"]} at raw level')
        # headers: cand1 header block vs G_new header block, raw (comment) lines
missing = set(dev_pairs) - found_pairs
print(f'deviation entries in JSON: {len(devs)}; matched by raw line diffs: {len(found_pairs)}; JSON entries not observed: {sorted(missing)}')
print(f'problems: {len(problems)}')
for p in problems[:50]:
    print('  ', p)

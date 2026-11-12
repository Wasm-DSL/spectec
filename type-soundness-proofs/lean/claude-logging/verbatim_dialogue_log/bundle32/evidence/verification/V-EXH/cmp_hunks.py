#!/usr/bin/env python3
"""V-EXH independent check: compare hand layer of OLD (vs G_old) with hand layer of cand1 (vs G_new).
Parses GNU diff normal-format output; maps G_old anchors to G_new via difflib on G_old vs G_new."""
import sys, re, json, difflib

W = sys.argv[1]   # work dir
A = sys.argv[2]   # agent dir

def rd(p):
    with open(p, encoding='utf-8') as f:
        s = f.read()
    assert s.endswith('\n')
    return s.split('\n')[:-1]

G_old = rd(f'{W}/G_old.lean'); OLD = rd(f'{W}/OLD.lean')
G_new = rd(f'{W}/G_new.lean'); C = rd(f'{W}/cand1.lean')

hdr = re.compile(r'^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$')

def parse(p):
    hunks = []
    cur = None
    for ln in rd(p):
        m = hdr.match(ln)
        if m:
            a1 = int(m.group(1)); a2 = int(m.group(2) or a1)
            t = m.group(3)
            b1 = int(m.group(4)); b2 = int(m.group(5) or b1)
            cur = dict(t=t, a1=a1, a2=a2, b1=b1, b2=b2, rem=[], add=[])
            hunks.append(cur)
        elif ln.startswith('< '):
            cur['rem'].append(ln[2:])
        elif ln.startswith('> '):
            cur['add'].append(ln[2:])
        elif ln == '---':
            pass
        else:
            raise SystemExit('bad diff line: ' + ln)
    return hunks

H_old = parse(f'{A}/gold_old.diff')
H_new = parse(f'{A}/gnew_cand1.diff')

# independent sanity: rebuild OLD from G_old + H_old, and cand1 from G_new + H_new (validates parsing)
def apply(G, H):
    out = []; i = 0  # i = 0-based index into G
    for h in H:
        if h['t'] == 'a':
            upto = h['a1']           # insert after line a1 (1-based) -> keep G[0:a1]
            out.extend(G[i:upto]); i = upto
            out.extend(h['add'])
        else:
            s = h['a1'] - 1; e = h['a2']
            out.extend(G[i:s]); i = e
            assert G[s:e] == h['rem'], ('rem mismatch', h['a1'])
            out.extend(h['add'])
    out.extend(G[i:])
    return out
assert apply(G_old, H_old) == OLD, 'parse/apply check failed for OLD'
assert apply(G_new, H_new) == C, 'parse/apply check failed for cand1'
print('parse+apply roundtrip OK for both diffs')

# map G_old line index -> G_new line index for lines in 'equal' blocks
sm = difflib.SequenceMatcher(None, G_old, G_new, autojunk=False)
m_old2new = {}
delta_old_lines = set()
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag == 'equal':
        for k in range(i2 - i1):
            m_old2new[i1 + k] = j1 + k
    else:
        delta_old_lines.update(range(i1, i2))
        if i1 == i2:
            delta_old_lines.add(('ins_before', i1))
print('model delta: G_old lines not in equal blocks:', len([x for x in delta_old_lines if isinstance(x, int)]))

devs = json.load(open(f'{W}/cand1.lean.devs.json'))
dev_by_old = {d['old_line']: d for d in devs}
assert len(dev_by_old) == len(devs) == 56

problems = []
found_devs = []
n_same_add = 0
for k, (ho, hn) in enumerate(zip(H_old, H_new), 1):
    if ho['t'] != hn['t'] or len(ho['rem']) != len(hn['rem']) or len(ho['add']) != len(hn['add']):
        problems.append(('shape', k, ho, hn)); continue
    # anchor check: the G_old anchor lines must map to the G_new anchor lines
    if ho['t'] == 'a':
        anchors = [(ho['a1'] - 1, hn['a1'] - 1)]   # the line after which we insert
    else:
        anchors = [(ho['a1'] - 1 + x, hn['a1'] - 1 + x) for x in range(ho['a2'] - ho['a1'] + 1)]
        # plus the context line just before and after
        anchors += [(ho['a1'] - 2, hn['a1'] - 2), (ho['a2'], hn['a2'])]
    for io, inew in anchors:
        mo = m_old2new.get(io)
        if mo != inew:
            problems.append(('anchor', k, io + 1, inew + 1, mo + 1 if mo is not None else None,
                             G_old[io] if io < len(G_old) else None, G_new[inew] if inew < len(G_new) else None))
    # removed generated lines must be identical (they map 1:1)
    for x, (a, b) in enumerate(zip(ho['rem'], hn['rem'])):
        if a != b:
            problems.append(('rem-differs', k, ho['a1'] + x, hn['a1'] + x, a, b))
    # added (hand) lines
    for x, (a, b) in enumerate(zip(ho['add'], hn['add'])):
        ol = ho['b1'] + x; nl = hn['b1'] + x
        assert OLD[ol - 1] == a and C[nl - 1] == b
        if a == b:
            n_same_add += 1
        else:
            found_devs.append((ol, nl, a, b))

print('hunk pairs:', len(H_old), len(H_new))
print('identical hand lines:', n_same_add, ' differing hand lines:', len(found_devs))
print('problems:', len(problems))
for p in problems[:50]:
    print('  ', p)

# compare differing lines with the log
logged = {(d['old_line'], d['new_line']) for d in devs}
found = {(o, n) for o, n, _, _ in found_devs}
print('found-but-not-logged:', sorted(found - logged))
print('logged-but-not-found:', sorted(logged - found))
bad_text = []
for o, n, a, b in found_devs:
    d = dev_by_old.get(o)
    if d is None: continue
    if d['before'] != a or d['after'] != b or d['new_line'] != n:
        bad_text.append((o, n, d['before'] == a, d['after'] == b, d['new_line'] == n))
print('logged entries whose before/after/new_line text does not match files exactly:', bad_text)

# every differing line: is the ONLY difference a substitution admininstr_case_K -> admininstr_case_{K-1}?
pat = re.compile(r'admininstr_case_(\d+)')
nonrename = []
for o, n, a, b in found_devs:
    toks_a = re.split(r'(admininstr_case_\d+)', a); toks_b = re.split(r'(admininstr_case_\d+)', b)
    ok = len(toks_a) == len(toks_b)
    if ok:
        for ta, tb in zip(toks_a, toks_b):
            ma = pat.fullmatch(ta); mb = pat.fullmatch(tb)
            if ma and mb:
                if int(mb.group(1)) != int(ma.group(1)) - 1: ok = False
            elif ta != tb:
                ok = False
    if not ok: nonrename.append((o, n, a, b))
print('differing lines that are not purely admininstr_case_K -> K-1 renames:', nonrename)

json.dump(dict(found_devs=found_devs, problems=[list(map(str, p)) for p in problems]),
          open(f'{A}/cmp_hunks.out.json', 'w'), indent=1, ensure_ascii=False)

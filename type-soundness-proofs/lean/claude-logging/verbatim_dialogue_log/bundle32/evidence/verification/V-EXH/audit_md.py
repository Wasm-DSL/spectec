#!/usr/bin/env python3
"""V-EXH: audit the markdown deviation log (sections 2, 3, 4) directly against the files."""
import sys, re, json
from collections import Counter, defaultdict
W = sys.argv[1]; MD = sys.argv[2]
def rd(p):
    s = open(p, encoding='utf-8').read(); assert s.endswith('\n'); return s.split('\n')[:-1]
G_old = rd(f'{W}/G_old.lean'); OLD = rd(f'{W}/OLD.lean'); G_new = rd(f'{W}/G_new.lean'); C = rd(f'{W}/cand1.lean')
md = open(MD, encoding='utf-8').read().split('\n')
MARK = '/- HELPER LEMMA CREATED BY CLAUDE -/'

def split_row(r):
    # split a markdown table row on unescaped pipes
    cells = re.split(r'(?<!\\)\|', r.strip())
    return [c.strip() for c in cells[1:-1]]
def unbt(c):
    c = c.strip()
    if c.startswith('`') and c.endswith('`'): c = c[1:-1]
    return c.replace('\\|', '|')

# ---- section 4 rows
sec4 = [l for l in md if re.match(r'^\| \d+ \|', l)]
print('section 4 rows:', len(sec4))
rows = []
for r in sec4:
    c = split_row(r)
    assert len(c) == 6, (len(c), r)
    rows.append(dict(n=int(c[0]), construct=unbt(c[1]), ol=int(c[2]), nl=int(c[3]), before=unbt(c[4]), after=unbt(c[5])))
print('row numbers 1..56 in order:', [x['n'] for x in rows] == list(range(1, 57)))
def enclosing(L, line):
    for j in range(line - 1, -1, -1):
        m = re.match(r'^theorem\s+(\S+)', L[j])
        if m:
            kind = 'helper lemma' if j > 0 and L[j - 1] == MARK else 'theorem'
            return m.group(1), kind, j + 1
    return None
bad = []
gen_names = {re.match(r'^theorem\s+(\S+)', l).group(1) for l in G_old if re.match(r'^theorem\s+(\S+)', l)}
for x in rows:
    o = OLD[x['ol'] - 1]; c = C[x['nl'] - 1]
    if o.strip() != x['before']: bad.append(('before', x['n'], o.strip(), x['before']))
    if c.strip() != x['after']: bad.append(('after', x['n'], c.strip(), x['after']))
    if o.strip() == c.strip(): bad.append(('no change', x['n']))
    eo = enclosing(OLD, x['ol']); ec = enclosing(C, x['nl'])
    if eo[0] != x['construct'] or ec[0] != x['construct']: bad.append(('construct', x['n'], eo, ec, x['construct']))
    # inside proof body?  the header .. ':= by' line must precede the deviation line
    hdr = eo[2]
    k = hdr - 1
    while not OLD[k].rstrip().endswith(':= by') and not OLD[k].rstrip().endswith(':='): k += 1
    if not x['ol'] > k + 1: bad.append(('in statement', x['n'], x['ol'], k + 1))
    # indentation preserved?
    if len(o) - len(o.lstrip()) != len(c) - len(c.lstrip()): bad.append(('indent', x['n']))
print('section 4 problems:', bad)

# ---- section 2 table: construct | kind | lines renamed | renames
sec2 = []
in2 = False
for l in md:
    if l.startswith('## 2.'): in2 = True; continue
    if l.startswith('## 3.'): in2 = False
    if in2 and l.startswith('| `'): sec2.append(split_row(l))
print('section 2 rows:', len(sec2))
per = defaultdict(Counter); perlines = Counter()
for x in rows:
    a = re.findall(r'admininstr_case_\d+', x['before']); b = re.findall(r'admininstr_case_\d+', x['after'])
    perlines[x['construct']] += 1
    for p, q in zip(a, b):
        if p != q: per[x['construct']][(p, q)] += 1
bad2 = []
for c in sec2:
    name = unbt(c[0]); kind = c[1]; n = int(c[2])
    renames = re.findall(r'`(admininstr_case_\d+)`→`(admininstr_case_\d+)` \(×(\d+)\)', c[3])
    got = Counter({(p, q): int(k) for p, q, k in renames})
    if perlines[name] != n: bad2.append(('lines', name, perlines[name], n))
    if got != per[name]: bad2.append(('renames', name, dict(per[name]), dict(got)))
    exp_kind = 'helper lemma' if name not in gen_names else ('hand-edited generated theorem' if name in ('Step_read_is_wf', 'Step_is_wf') else 'generated theorem')
    if kind != exp_kind: bad2.append(('kind', name, exp_kind, kind))
print('section 2 constructs listed:', [unbt(c[0]) for c in sec2])
print('section 2 sum of lines:', sum(int(c[2]) for c in sec2), ' constructs with deviations (from rows):', len(perlines))
print('section 2 problems:', bad2)

# ---- section 3 table: old | new | constructor for | lines
sec3 = []
in3 = False
for l in md:
    if l.startswith('## 3.'): in3 = True; continue
    if l.startswith('## 4.'): in3 = False
    if in3 and l.startswith('| `'): sec3.append(split_row(l))
def wf_ctor(L, fam, k):
    """return (full text, conclusion head) of constructor fam_k inside 'inductive wf_admininstr'"""
    start = next(i for i, l in enumerate(L) if l.startswith('inductive wf_admininstr'))
    i = start + 1
    while i < len(L) and not L[i].startswith(f'  | {fam}_{k} ') and not L[i] == f'  | {fam}_{k}' and not L[i].startswith(f'  | {fam}_{k} :'):
        if L[i] and not L[i][0].isspace(): return None
        i += 1
    j = i + 1
    while j < len(L) and L[j].startswith('    '): j += 1
    txt = '\n'.join(L[i:j])
    m = re.search(r'wf_admininstr \(?(admininstr\.[A-Za-z_]+)', txt.split(':', 1)[1] if False else txt[txt.rfind('wf_admininstr'):])
    return re.sub(rf'{fam}_{k}\b', 'CASE', txt), (m.group(1) if m else None)
lines_per_rename = Counter()
for x in rows:
    for p, q in zip(re.findall(r'admininstr_case_\d+', x['before']), re.findall(r'admininstr_case_\d+', x['after'])):
        if p != q: lines_per_rename[(p, q)] += 1
bad3 = []
for c in sec3:
    o = unbt(c[0]); n = unbt(c[1]); ctor = unbt(c[2]); cnt = int(c[3])
    ko = int(o.rsplit('_', 1)[1]); kn = int(n.rsplit('_', 1)[1])
    to = wf_ctor(G_old, 'admininstr_case', ko); tn = wf_ctor(G_new, 'admininstr_case', kn)
    if to is None or tn is None or to[0] != tn[0]: bad3.append(('text differs', o, n))
    if to and to[1] != ctor: bad3.append(('ctor name', o, to[1], ctor))
    if lines_per_rename[(o, n)] != cnt: bad3.append(('count', o, n, lines_per_rename[(o, n)], cnt))
    # uniqueness: no other new constructor has the same text
    others = [k for k in range(0, 80) if k != kn and (lambda t: t is not None and t[0] == to[0])(wf_ctor(G_new, 'admininstr_case', k))]
    if others: bad3.append(('not unique', o, others))
print('section 3 rows:', len(sec3), ' renames covered by rows:', set(lines_per_rename) == {(unbt(c[0]), unbt(c[1])) for c in sec3})
print('section 3 problems:', bad3)
# section 1 numbers
txt = '\n'.join(md)
print('section 1 claims present:', '56 lines, in 7 top-level constructs' in txt, '1,865 hand-written lines' in txt, '92 helper lemmas, in 23 blocks' in txt, '89 generated theorems' in txt)

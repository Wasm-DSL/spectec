import re, sys, json
from collections import Counter, defaultdict
W = sys.argv[1]; Lmd = sys.argv[2]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
old = rd(W + '/OLD.lean'); go = rd(W + '/G_old.lean')
devs = json.load(open(W + '/cand1.lean.devs.json'))
ipat = re.compile(r'(?<![A-Za-z0-9_])(admininstr_case_|instr_case_)(\d+)(?![A-Za-z0-9_])')
per_construct_occ = defaultdict(Counter); per_construct_lines = Counter()
per_pair_lines = Counter(); per_pair_occ = Counter()
order = []
for d in sorted(devs, key=lambda d: d['old_line']):
    c = d['construct'].split()[-1]
    if c not in order: order.append(c)
    per_construct_lines[c] += 1
    b = ipat.findall(d['before']); a = ipat.findall(d['after'])
    pairs = [(p+x, q+y) for (p,x),(q,y) in zip(b,a) if (p,x) != (q,y)]
    for pr in pairs:
        per_construct_occ[c][pr] += 1; per_pair_occ[pr] += 1
    for pr in set(pairs):
        per_pair_lines[pr] += 1
    # also: unchanged ctor refs on the line
    unchanged = [(p+x) for (p,x),(q,y) in zip(b,a) if (p,x) == (q,y)]
    if unchanged: print('line', d['old_line'], 'also has unchanged refs', unchanged)
    if len(pairs) != 1: print('line', d['old_line'], 'has', len(pairs), 'renames')
print('construct order:', order)
for c in order:
    print(c, per_construct_lines[c], sorted(per_construct_occ[c].items(), key=lambda kv: int(kv[0][0].split('_')[-1])))
print('pairs lines:', sorted(per_pair_lines.items(), key=lambda kv: int(kv[0][0].split('_')[-1])))
print('pairs occ  :', sorted(per_pair_occ.items(), key=lambda kv: int(kv[0][0].split('_')[-1])))
print('total pairs', len(per_pair_lines), 'total lines', sum(per_construct_lines.values()))
# kind check: marker before decl in OLD, and presence in G_old
for c in order:
    idx = [i for i,l in enumerate(old) if re.match(r'^theorem ' + re.escape(c) + r'\b', l)]
    gidx = [i for i,l in enumerate(go) if re.match(r'^theorem ' + re.escape(c) + r'\b', l)]
    gcom = [i for i,l in enumerate(old) if re.search(r'theorem ' + re.escape(c) + r'\b', l) and not l.startswith('theorem')]
    marks = [old[i-1].strip() for i in idx]
    print(c, 'OLD decl lines', [i+1 for i in idx], 'marker-before:', marks, '| in G_old at', [i+1 for i in gidx], '| other mentions in OLD at', [i+1 for i in gcom])
# Parse md section 2 table
md = open(Lmd, encoding='utf-8').read().split('\n')
print()
for line in md:
    m = re.match(r'^\| `([^`]+)` \| ([^|]+) \| (\d+) \| (.*) \|$', line)
    if m:
        c = m.group(1); kind = m.group(2).strip(); n = int(m.group(3))
        items = re.findall(r'`(admininstr_case_\d+)`→`(admininstr_case_\d+)` \(×(\d+)\)', m.group(4))
        mine = {k: v for k,v in per_construct_occ[c].items()}
        theirs = {(a,b): int(x) for a,b,x in items}
        print('S2', c, kind, 'lines md', n, 'mine', per_construct_lines[c], '| renames equal (occurrences):', mine == theirs)
    m3 = re.match(r'^\| `(admininstr_case_\d+)` \| `(admininstr_case_\d+)` \| `([^`]+)` \| (\d+) \|$', line)
    if m3:
        pr = (m3.group(1), m3.group(2))
        print('S3', pr, m3.group(3), 'lines md', m3.group(4), 'mine lines', per_pair_lines[pr], 'occ', per_pair_occ[pr])

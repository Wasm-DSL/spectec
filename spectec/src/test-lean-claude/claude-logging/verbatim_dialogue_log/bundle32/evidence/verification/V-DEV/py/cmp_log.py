import re, sys, json
W = sys.argv[1]; V = sys.argv[2]; L = sys.argv[3]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
old = rd(W + '/OLD.lean'); cand = rd(W + '/cand1.lean')
c = json.load(open(V + '/classify.json'))
nlo = {int(k): v for k,v in c['newline_of_old'].items()}
mine = []
for (ol, before, after) in c['hand_changed']:
    nl = nlo[ol]
    assert cand[nl-1] == after, (ol, nl)
    assert old[ol-1] == before
    mine.append((ol, nl, before, after))
mine.sort()
devs = json.load(open(W + '/cand1.lean.devs.json'))
logged = sorted((d['old_line'], d['new_line'], d['before'], d['after']) for d in devs)
print('mine', len(mine), 'json', len(logged))
print('exact equality of (old_line,new_line,before,after) sets:', mine == logged)
sm = set(mine); sl = set(logged)
print('in mine not json:', sorted(sm - sl)[:10])
print('in json not mine:', sorted(sl - sm)[:10])
# check json 'renames' field consistency with before/after
ipat = re.compile(r'(?<![A-Za-z0-9_])(instr_case_|admininstr_case_)(\d+)(?![A-Za-z0-9_])')
bad = 0
for d in devs:
    b = ipat.findall(d['before']); a = ipat.findall(d['after'])
    pairs = [(p+x, q+y) for (p,x),(q,y) in zip(b,a) if (p,x)!=(q,y)]
    if len(b)!=len(a): bad+=1; print('len mismatch', d)
    if sorted(set(map(tuple,pairs))) != sorted(set(map(tuple,d['renames']))):
        bad+=1; print('renames mismatch', d['old_line'], pairs, d['renames'])
    # check that before/after differ only in constructor names
    if ipat.sub('X', d['before']) != ipat.sub('X', d['after']):
        bad+=1; print('other textual diff', d['old_line'])
print('json renames-field inconsistencies:', bad)
# Now parse the markdown section 4 table
md = open(L, encoding='utf-8').read().split('\n')
rows = []
for line in md:
    m = re.match(r'^\| (\d+) \| `([^`]*)` \| (\d+) \| (\d+) \| `(.*)` \| `(.*)` \|$', line)
    if m:
        rows.append((int(m.group(1)), m.group(2), int(m.group(3)), int(m.group(4)), m.group(5).replace('\\|','|'), m.group(6).replace('\\|','|')))
print('md rows parsed:', len(rows), 'numbering 1..56 contiguous:', [r[0] for r in rows] == list(range(1,57)))
mdset = sorted((r[2], r[3], r[4], r[5]) for r in rows)
mine_trim = sorted((ol, nl, b.strip(), a.strip()) for (ol,nl,b,a) in mine)
print('md section4 equals my computation (trimmed text):', mdset == mine_trim)
for x,y in zip(mdset, mine_trim):
    if x != y: print('MD', x); print('ME', y)
# check md 'construct' column vs json construct
jc = {(d['old_line']): d['construct'] for d in devs}
mism = [(r[2], r[1], jc[r[2]]) for r in rows if not jc[r[2]].endswith(' ' + r[1])]
print('md construct vs json construct mismatches:', mism)
# check strip: before with leading spaces trimmed - check none has trailing spaces
print('any before/after with trailing whitespace:', [d['old_line'] for d in devs if d['before'] != d['before'].rstrip() or d['after'] != d['after'].rstrip()])

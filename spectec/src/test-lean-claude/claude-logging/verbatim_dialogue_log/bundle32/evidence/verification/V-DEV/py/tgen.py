import re, sys
W = sys.argv[1]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
go = rd(W + '/G_old.lean'); gn = rd(W + '/G_new.lean')
locpat = re.compile(r'1-syntax\.spectec:(\d+)\.(\d+)-(\d+)\.(\d+)')
TH = 552  # refs with line >= TH shift down by one (no refs between 438 and 551)
def shiftloc(m):
    a,b,c,d = map(int, m.groups())
    if a >= TH: a -= 1
    if c >= TH: c -= 1
    return '1-syntax.spectec:%d.%d-%d.%d' % (a,b,c,d)
ipat = re.compile(r'(?<![A-Za-z0-9_])(instr_case_|admininstr_case_)(\d+)(?![A-Za-z0-9_])')
def ren(m):
    k = int(m.group(2))
    if k >= 20: k -= 1
    return m.group(1) + str(k)
def T(line):
    line = locpat.sub(shiftloc, line)
    line = ipat.sub(ren, line)
    return line
EXT = [
 '  | EXTEND (v_numtype : numtype) (v_n : n) : instr',
 '  | instr_case_19 (v_numtype : numtype) (v_n : n) : wf_instr (instr.EXTEND v_numtype v_n)',
 '  | EXTEND (v_numtype : numtype) (v_n : n) : admininstr',
 '  | instr.EXTEND x0 x1 => admininstr.EXTEND x0 x1',
 '  | admininstr_case_19 (v_numtype : numtype) (v_n : n) : wf_admininstr (admininstr.EXTEND v_numtype v_n)',
]
# find positions of these in G_old
pos = [i for i,l in enumerate(go) if l in EXT]
print('EXTEND-line positions in G_old (1-based):', [p+1 for p in pos], 'count', len(pos))
# also any line mentioning EXTEND at all
print('lines mentioning EXTEND in G_old:', [(i+1) for i,l in enumerate(go) if 'EXTEND' in l])
print('lines mentioning EXTEND in G_new:', [(i+1) for i,l in enumerate(gn) if 'EXTEND' in l])
tg = [T(l) for i,l in enumerate(go) if i not in set(pos)]
print('len T(G_old)', len(tg), 'len G_new', len(gn))
diffs = [(i+1, a, b) for i,(a,b) in enumerate(zip(tg, gn)) if a != b]
print('line diffs after T:', len(diffs))
for d in diffs[:20]: print(d)
# count how many lines T changed (excluding deletions)
chg = sum(1 for i,l in enumerate(go) if i not in set(pos) and T(l) != l)
print('G_old lines changed by T:', chg)
# which kinds
kinds = {'loc':0,'ren':0,'both':0}
for i,l in enumerate(go):
    if i in set(pos): continue
    a = locpat.sub(shiftloc,l) != l
    b = ipat.sub(ren,l) != l
    if a and b: kinds['both']+=1
    elif a: kinds['loc']+=1
    elif b: kinds['ren']+=1
print(kinds)

import re, sys, json
W = sys.argv[1]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
old = rd(W + '/OLD.lean'); cand = rd(W + '/cand1.lean')
locpat = re.compile(r'1-syntax\.spectec:(\d+)\.(\d+)-(\d+)\.(\d+)')
TH = 552
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
EXT = [
 '  | EXTEND (v_numtype : numtype) (v_n : n) : instr',
 '  | instr_case_19 (v_numtype : numtype) (v_n : n) : wf_instr (instr.EXTEND v_numtype v_n)',
 '  | EXTEND (v_numtype : numtype) (v_n : n) : admininstr',
 '  | instr.EXTEND x0 x1 => admininstr.EXTEND x0 x1',
 '  | admininstr_case_19 (v_numtype : numtype) (v_n : n) : wf_admininstr (admininstr.EXTEND v_numtype v_n)',
]
pos = [i for i,l in enumerate(old) if l in EXT]
print('EXTEND-line positions in OLD:', [p+1 for p in pos])
print('EXTEND-line positions in cand1:', [i+1 for i,l in enumerate(cand) if l in EXT])
ps = set(pos)
# Mapping from T(OLD) index to OLD line number
kept = [i for i in range(len(old)) if i not in ps]
to = [locpat.sub(shiftloc, ipat.sub(ren, old[i])) for i in kept]
print('len T(OLD)', len(to), 'len cand1', len(cand))
diffs = [(kept[j]+1, j+1, to[j], cand[j]) for j in range(min(len(to),len(cand))) if to[j] != cand[j]]
print('line diffs between T(OLD) and cand1:', len(diffs))
for d in diffs[:30]: print(d)
# Lines that T changed in OLD
changed = [(i+1, old[i], to[j]) for j,i in enumerate(kept) if to[j] != old[i]]
print('OLD lines changed by T:', len(changed))
json.dump({'changed': changed, 'kept_map': kept}, open(sys.argv[2], 'w'))

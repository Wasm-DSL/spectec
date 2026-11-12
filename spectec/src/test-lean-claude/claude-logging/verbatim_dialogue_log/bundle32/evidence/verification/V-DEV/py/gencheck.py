import re, sys, json, difflib
W = sys.argv[1]; V = sys.argv[2]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
go = rd(W + '/G_old.lean'); old = rd(W + '/OLD.lean'); gn = rd(W + '/G_new.lean'); cand = rd(W + '/cand1.lean')
c = json.load(open(V + '/classify.json'))
gmap = {int(k): v for k,v in c['gmap'].items()}
locpat = re.compile(r'1-syntax\.spectec:(\d+)\.(\d+)-(\d+)\.(\d+)')
TH = 552
def shiftloc(m):
    a,b,cc,d = map(int, m.groups())
    if a >= TH: a -= 1
    if cc >= TH: cc -= 1
    return '1-syntax.spectec:%d.%d-%d.%d' % (a,b,cc,d)
ipat = re.compile(r'(?<![A-Za-z0-9_])(instr_case_|admininstr_case_)(\d+)(?![A-Za-z0-9_])')
def ren(m):
    k = int(m.group(2))
    if k >= 20: k -= 1
    return m.group(1) + str(k)
def T(l): return locpat.sub(shiftloc, ipat.sub(ren, l))
gT = set(i+1 for i,l in enumerate(go) if T(l) != l and i+1 not in (1925, 2034, 11544, 11625, 11747))
gen_changed_old = [x[0] for x in c['gen_changed']]
mapped = set(gmap[x] for x in gen_changed_old)
print('G_old lines changed by T:', len(gT), '; OLD generated changed lines mapped to G_old:', len(mapped), '; equal:', gT == mapped)
for e in [1953, 2062, 12206, 12287, 12409]:
    print('OLD EXTEND line', e, '-> G_old', gmap.get(e))
# alignment of cand1 vs G_new
sm = difflib.SequenceMatcher(None, gn, cand, autojunk=False)
matched = set()
for a,b,size in sm.get_matching_blocks():
    for t in range(size): matched.add(b+t+1)
print('cand1 lines unmatched with G_new (hand layer):', len(cand) - len(matched))
gm = set()
for a,b,size in sm.get_matching_blocks():
    for t in range(size): gm.add(a+t+1)
print('G_new lines unmatched in cand1:', len(gn) - len(gm))
# Check the hand layer of cand1 equals the hand layer of OLD with renames applied, in order
hand_c = [cand[i-1] for i in range(1, len(cand)+1) if i not in matched]
hand_o = [old[i-1] for i in c['hand_old']]
print('hand layers equal after T:', [T(x) for x in hand_o] == hand_c, len(hand_o), len(hand_c))
nd = sum(1 for a,b in zip(hand_o, hand_c) if a != b)
print('hand lines differing:', nd)

import re, sys, json
W = sys.argv[1]; V = sys.argv[2]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
old = rd(W + '/OLD.lean')
c = json.load(open(V + '/classify.json'))
hand = sorted(c['hand_old'])
M = '/- HELPER LEMMA CREATED BY CLAUDE -/'
regions = []
s = hand[0]; p = hand[0]
for x in hand[1:]:
    if x == p + 1: p = x
    else:
        regions.append((s,p)); s = x; p = x
regions.append((s,p))
print('contiguous hand-layer regions:', len(regions))
withm = [(a,b, sum(1 for i in range(a,b+1) if old[i-1]==M)) for a,b in regions]
wm = [r for r in withm if r[2] > 0]
print('regions containing helper markers:', len(wm), 'total markers', sum(r[2] for r in wm))
for r in wm: print('  ', r)

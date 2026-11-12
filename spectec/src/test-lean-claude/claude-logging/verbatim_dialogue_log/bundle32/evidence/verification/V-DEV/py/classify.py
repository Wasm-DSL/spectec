import re, sys, json, difflib
W = sys.argv[1]; V = sys.argv[2]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
go = rd(W + '/G_old.lean'); old = rd(W + '/OLD.lean'); gn = rd(W + '/G_new.lean'); cand = rd(W + '/cand1.lean')
toc = json.load(open(V + '/toc.json'))
kept = toc['kept_map']
newline_of_old = {i+1: j+1 for j,i in enumerate(kept)}
# alignment OLD vs G_old with difflib
sm = difflib.SequenceMatcher(None, go, old, autojunk=False)
gen_old = set()  # OLD line numbers (1-based) that are matched to G_old lines
gmap = {}
for a,b,size in sm.get_matching_blocks():
    for t in range(size):
        gen_old.add(b+t+1); gmap[b+t+1] = a+t+1
print('OLD lines matched to G_old:', len(gen_old), 'of', len(old), '; G_old lines', len(go))
hand_old = [i for i in range(1, len(old)+1) if i not in gen_old]
print('OLD hand-layer lines (unmatched):', len(hand_old))
# G_old lines not matched (replaced/removed by hand layer)
gmatched = set(gmap.values())
g_unmatched = [i for i in range(1, len(go)+1) if i not in gmatched]
print('G_old lines unmatched in OLD:', len(g_unmatched))
for i in g_unmatched: print('  G_old', i, repr(go[i-1]))
changed = toc['changed']
gen_changed = [c for c in changed if c[0] in gen_old]
hand_changed = [c for c in changed if c[0] not in gen_old]
print('changed generated lines:', len(gen_changed), 'changed hand lines:', len(hand_changed))
json.dump({'hand_changed': hand_changed, 'gen_changed': gen_changed, 'hand_old': hand_old, 'gmap': gmap, 'newline_of_old': newline_of_old}, open(V + '/classify.json','w'))
# check gen_changed lines correspond to G_old lines that T changes

import re, sys, json
W = sys.argv[1]; V = sys.argv[2]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
old = rd(W + '/OLD.lean')
c = json.load(open(V + '/classify.json'))
hand = set(c['hand_old'])
# find tactic lines (in hand layer) that do case splits without named alternatives and are followed by bullets/next/case
for i in sorted(hand):
    l = old[i-1]
    m = re.search(r'\b(cases|induction|rcases|match)\b\s+(.*)$', l)
    if not m: continue
    rest = m.group(2)
    if ' with' in rest and m.group(1) in ('cases','induction'):
        # named alternatives: check next line starts with '|'
        continue
    if '<;>' in l: continue
    # look ahead for bullets
    ind = len(l) - len(l.lstrip())
    nxt = old[i] if i < len(old) else ''
    if nxt.strip().startswith('·') or nxt.strip().startswith('next') or nxt.strip().startswith('case ') or nxt.strip().startswith('all_goals') or nxt.strip().startswith('any_goals'):
        print(i, repr(l.strip()), '-> next:', repr(nxt.strip()[:60]))

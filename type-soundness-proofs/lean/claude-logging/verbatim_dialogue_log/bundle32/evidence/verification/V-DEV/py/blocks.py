import re, sys
W = sys.argv[1]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
for fn in ['OLD.lean', 'cand1.lean']:
    L = rd(W + '/' + fn)
    M = '/- HELPER LEMMA CREATED BY CLAUDE -/'
    # top-level declarations: column-0 keyword lines
    decl = re.compile(r'^(theorem|lemma|def|inductive|abbrev|instance|structure|opaque|axiom|noncomputable|private|protected|partial|class|macro|syntax|notation|set_option|open|namespace|end|section|mutual|attribute|deriving|@\[)\b')
    items = []
    for i,l in enumerate(L):
        if decl.match(l):
            helper = i > 0 and L[i-1] == M
            nm = re.match(r'^\S+\s+(\S+)', l)
            items.append((i+1, helper, nm.group(1) if nm else l[:30]))
    helpers = [x for x in items if x[1]]
    # marker lines each followed by a decl?
    marks = [i+1 for i,l in enumerate(L) if l == M]
    bad = [m for m in marks if not decl.match(L[m])]
    runs = 0; prev = False
    for x in items:
        if x[1] and not prev: runs += 1
        prev = x[1]
    print(fn, 'decls', len(items), 'helper decls', len(helpers), 'markers', len(marks), 'markers not followed by a decl', bad, 'blocks', runs)
    # helper names
    print('  helper kinds:', sorted(set(re.match(r'^(\S+)', L[x[0]-1]).group(1) for x in helpers)))
    # duplicates names
    from collections import Counter
    cn = Counter(x[2] for x in helpers)
    print('  duplicate helper names:', [k for k,v in cn.items() if v>1])
print()
L = rd(W + '/OLD.lean')
M = '/- HELPER LEMMA CREATED BY CLAUDE -/'
decl = re.compile(r'^(theorem|lemma|def|inductive|abbrev|instance|structure|opaque|axiom|noncomputable|private|protected|partial|class|macro|syntax|notation|set_option|open|namespace|end|section|mutual|attribute|deriving|@\[)\b')
items = []
for i,l in enumerate(L):
    if decl.match(l):
        helper = i > 0 and L[i-1] == M
        nm = re.match(r'^\S+\s+(\S+)', l)
        items.append((i+1, helper, nm.group(1) if nm else l[:30]))
runs = []
cur = None
for idx,x in enumerate(items):
    if x[1]:
        if cur is None: cur = [x]
        else: cur.append(x)
    else:
        if cur is not None:
            runs.append((cur, x)); cur = None
if cur is not None: runs.append((cur, None))
for k,(r,after) in enumerate(runs):
    print(k+1, 'lines', r[0][0], '-', r[-1][0], 'n', len(r), 'first', r[0][2], 'last', r[-1][2], '| next decl:', after[0] if after else None, after[2] if after else None)

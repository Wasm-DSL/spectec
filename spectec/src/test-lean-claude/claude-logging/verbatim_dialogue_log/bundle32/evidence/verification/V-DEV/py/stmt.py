import re, sys, json
W = sys.argv[1]; V = sys.argv[2]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
for fname, key in [('OLD.lean', 'old_line'), ('cand1.lean', 'new_line')]:
    L = rd(W + '/' + fname)
    devs = json.load(open(W + '/cand1.lean.devs.json'))
    # top-level decl starts: column-0 lines beginning with theorem/lemma/def/inductive/etc
    starts = [i+1 for i,l in enumerate(L) if re.match(r'^(theorem|lemma|def|inductive|abbrev|instance|structure|opaque|axiom|noncomputable|private|protected|partial|mutual|class|@\[)', l)]
    import bisect
    res = {}
    for d in devs:
        ln = d[key]
        k = bisect.bisect_right(starts, ln) - 1
        s = starts[k]
        head = L[s-1]
        name = re.match(r'^(?:theorem|lemma|def)\s+(\S+)', head)
        # statement end: first line from s whose text contains ':=' (outside comments)
        e = None
        for j in range(s, ln+1):
            t = L[j-1]
            if ':=' in t:
                e = j; break
        res.setdefault((name.group(1) if name else head[:40], s, e), []).append(ln)
        if e is None or e >= ln:
            print(fname, 'LOGGED LINE NOT AFTER STATEMENT END:', ln, head, e)
        if not d['construct'].endswith(' ' + (name.group(1) if name else '?')):
            print(fname, 'construct mismatch', ln, d['construct'], head)
    for (nm, s, e), lns in res.items():
        print(fname, nm, 'decl line', s, 'stmt ends', e, '| first logged', min(lns), 'last logged', max(lns), 'n', len(lns))
        print('    stmt end text:', repr(L[e-1]))

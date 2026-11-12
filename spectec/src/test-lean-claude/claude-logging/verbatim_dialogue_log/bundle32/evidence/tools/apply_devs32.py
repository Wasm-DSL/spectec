# Apply meaning-preserving constructor renames to HAND-WRITTEN lines only, using the constructor map.
import re, sys, json
sys.path.insert(0, sys.argv[5]); from toplevel32 import constructs, owner
cand0, meta, cmap_p, out_p = sys.argv[1:5]
L = open(cand0).read()[:-1].split('\n'); src = json.load(open(meta))['src']; cm = json.load(open(cmap_p))
OLD = open(sys.argv[6]).read()[:-1].split('\n')
maps = {}
for ind in ('wf_instr', 'wf_admininstr'):
    for k, v in cm[ind]['map'].items(): maps[k] = v
cons = constructs(L); devs = []
for i, s in enumerate(src):
    if s[0] != 'hand': continue
    l = L[i]
    def rep(m):
        old = m.group(0); new = maps[old]
        if new is None: raise SystemExit('reference to removed constructor %s at line %d' % (old, i + 1))
        return new
    nl = re.sub(r'\b(?:admininstr_case_|instr_case_)\d+\b', rep, l)
    if nl != l:
        assert OLD[s[2] - 1] == l
        o = owner(cons, i + 1)
        devs.append({'new_line': i + 1, 'old_line': s[2], 'construct': '%s %s' % (o['kind'], o['name']),
                     'renames': sorted(set((a, maps[a]) for a in re.findall(r'\b(?:admininstr_case_|instr_case_)\d+\b', l) if maps[a] != a)),
                     'before': l, 'after': nl})
        L[i] = nl
open(out_p, 'w').write('\n'.join(L) + '\n')
json.dump(devs, open(out_p + '.devs.json', 'w'), indent=1)
print('deviation lines:', len(devs), '| constructs touched:', len(set(d['construct'] for d in devs)))
for d in devs: print(d['old_line'], '->', d['new_line'], d['construct'], d['renames'])

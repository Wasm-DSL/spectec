# Build old->new constructor maps for wf_instr / wf_admininstr by matching each constructor's full text
# (argument telescope, premises and conclusion), ignoring only the constructor's own name.
import re, sys, json
def ctors(path, ind):
    L = open(path).read().split('\n'); i = next(k for k, l in enumerate(L) if l.startswith('inductive %s ' % ind) or l.startswith('inductive %s:' % ind))
    out = {}; cur = None; buf = []
    for l in L[i + 1:]:
        if not l.startswith('  '):
            break
        m = re.match(r'  \| (\S+)(.*)$', l)
        if m:
            if cur: out[cur] = '\n'.join(buf)
            cur = m.group(1); buf = [m.group(2)]
        else:
            buf.append(l)
    if cur: out[cur] = '\n'.join(buf)
    return out
res = {}
for ind in ['wf_instr', 'wf_admininstr']:
    o, n = ctors(sys.argv[1], ind), ctors(sys.argv[2], ind)
    ntext = {}
    for k, v in n.items(): ntext.setdefault(v, []).append(k)
    mp = {}
    for k, v in o.items():
        cands = ntext.get(v, [])
        mp[k] = cands[0] if len(cands) == 1 else (None if not cands else cands)
    concl = {k: re.findall(r'(?:wf_instr|wf_admininstr) \((?:admin)?instr\.(\w+)', v)[-1] if re.findall(r'(?:wf_instr|wf_admininstr) \((?:admin)?instr\.(\w+)', v) else re.findall(r'(?:wf_instr|wf_admininstr) (?:admin)?instr\.(\w+)', v)[-1] for k, v in o.items()}
    res[ind] = {'n_old': len(o), 'n_new': len(n), 'map': mp, 'instr_of_old_ctor': concl,
                'unmatched_old': [k for k, v in mp.items() if v is None], 'ambiguous': [k for k, v in mp.items() if isinstance(v, list)],
                'unmatched_new': sorted(set(n) - {v for v in mp.values() if isinstance(v, str)})}
    print(ind, 'old ctors', len(o), 'new ctors', len(n), 'unmatched old', res[ind]['unmatched_old'], 'ambiguous', res[ind]['ambiguous'], 'unmatched new', res[ind]['unmatched_new'])
    renamed = {k: v for k, v in mp.items() if isinstance(v, str) and k != v}
    print('  renamed:', len(renamed), ' unchanged:', sum(1 for k, v in mp.items() if k == v))
json.dump(res, open(sys.argv[3], 'w'), indent=1)

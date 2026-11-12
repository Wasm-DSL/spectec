import re, sys, json
V = sys.argv[1]
od = json.load(open(V + '/wf_admin_old.json')); nd = json.load(open(V + '/wf_admin_new.json'))
for k in [20,43,44,46,47,48,49,51,52,53,54,55,56,57,66,67,71,72,73]:
    o = od['admininstr_case_%d' % k]; n = nd['admininstr_case_%d' % (k-1)]
    txt = ' '.join(x.strip() for x in o)
    m = re.search(r'wf_admininstr \((admininstr\.\S+)', txt) or re.search(r'wf_admininstr (admininstr\.\S+)', txt)
    mn = re.search(r'wf_admininstr \(?(admininstr\.[A-Za-z_]+)', ' '.join(x.strip() for x in n))
    print(k, '->', k-1, (m.group(1) if m else txt[:120]), '| new:', mn.group(1) if mn else None, '| lines old', len(o), 'new', len(n))

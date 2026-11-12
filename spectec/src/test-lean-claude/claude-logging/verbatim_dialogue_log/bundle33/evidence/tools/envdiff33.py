# bundle33: compare the old and new environment dumps (old names already mapped by meaning).
import sys, collections, json
def load(p):
    d = {}
    for l in open(p):
        l = l.rstrip('\n')
        if not l: continue
        m, k, n, th, vh, ax = l.split('\t'); assert n not in d, n; d[n] = dict(mod=m, kind=k, th=th, vh=vh, ax=ax)
    return d
O, N = load(sys.argv[1]), load(sys.argv[2])
only_o = sorted(set(O) - set(N)); only_n = sorted(set(N) - set(O)); common = sorted(set(O) & set(N))
print('old', len(O), 'new', len(N), 'common', len(common), 'only old', len(only_o), 'only new', len(only_n))
print('== only in old:'); [print('  ', O[n]['mod'], O[n]['kind'], n) for n in only_o]
print('== only in new:'); [print('  ', N[n]['mod'], N[n]['kind'], n) for n in only_n]
cat = collections.defaultdict(list)
for n in common:
    o, w = O[n], N[n]
    if o['mod'] != w['mod']: cat['module_changed'].append(n)
    if o['kind'] != w['kind']: cat['kind_changed'].append(n)
    if o['th'] != w['th']: cat['type_changed_' + w['kind']].append(n)
    if o['vh'] != w['vh']: cat['value_changed_' + w['kind']].append(n)
    if o['ax'] != w['ax']: cat['axioms_changed'].append(n)
for k in sorted(cat):
    print(f'== {k}: {len(cat[k])}')
    for n in cat[k][:400]: print('  ', N[n]['mod'], n)
json.dump({'only_old': only_o, 'only_new': only_n, **cat}, open(sys.argv[3], 'w'), indent=1)
# per-module counts
cnt = collections.Counter((N[n]['mod'], N[n]['kind']) for n in N); cnto = collections.Counter((O[n]['mod'], O[n]['kind']) for n in O)
print('== per module/kind counts (old -> new):')
for key in sorted(set(cnt) | set(cnto)): print('  ', key, cnto.get(key, 0), '->', cnt.get(key, 0))

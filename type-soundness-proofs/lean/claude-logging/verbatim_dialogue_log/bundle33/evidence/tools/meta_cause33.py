# bundle33: analyse the inductive-metadata dumps (OLD renamed by meaning vs NEW) and the cause probe.
import json, re, collections, sys
B = sys.argv[1]
def load(p):
    d = {}
    for l in open(p):
        f = l.rstrip('\n').split('\t')
        if len(f) == 5: d[f[2]] = f
    return d
O, N = load(f'{B}/probes/indmeta_old.tsv'), load(f'{B}/probes/indmeta_new.tsv')
out = {'only_old': sorted(set(O) - set(N)), 'only_new': sorted(set(N) - set(O)), 'changed': []}
for n in sorted(set(O) & set(N)):
    if O[n][3:] != N[n][3:]: out['changed'].append({'name': n, 'kind': N[n][1], 'old': O[n][3] + (' | ' + O[n][4] if O[n][4] != '-' else ''), 'new': N[n][3] + (' | ' + N[n][4] if N[n][4] != '-' else '')})
print('metadata entries OLD', len(O), 'NEW', len(N), '| only OLD', len(out['only_old']), '| only NEW', len(out['only_new']), '| changed', len(out['changed']))
print('only OLD:', out['only_old'])
byk = collections.Counter(c['kind'] for c in out['changed']); print('changed by kind:', dict(byk))
# classify changes
cls = collections.Counter(); owner = collections.Counter()
for c in out['changed']:
    if c['kind'] == 'ctor':
        mo = re.search(r'cidx=(\d+)', c['old']).group(1); mn = re.search(r'cidx=(\d+)', c['new']).group(1)
        rest_o = re.sub(r'cidx=\d+', '', c['old']); rest_n = re.sub(r'cidx=\d+', '', c['new'])
        ind = re.search(r'induct=(\S+)', c['new']).group(1)
        cls[('ctor: only the constructor index decreased by 1' if int(mo) - int(mn) == 1 and rest_o == rest_n else 'ctor: OTHER', ind)] += 1
    elif c['kind'] == 'induct':
        cls[('induct: one constructor fewer', c['name'])] += 1
        print('  induct', c['name'], '::', c['old'][:110], '=>', c['new'][:110])
    else:
        cls[('rec: ' + ('one minor premise and one rule fewer' if re.search(r'minors=(\d+)', c['old']).group(1) != re.search(r'minors=(\d+)', c['new']).group(1) else 'OTHER'), c['name'])] += 1
        print('  rec', c['name'], '::', c['old'], '=>', c['new'])
for (k, ind), v in sorted(cls.items()): print(f'  {v:3d}  {k}  [{ind}]')
json.dump(out, open(f'{B}/work/indmeta_diff33.json', 'w'), indent=1)
# ---------------- cause analysis
envd = json.load(open(f'{B}/work/envdiff33.json')); envc = json.load(open(f'{B}/work/envcat33.json'))
user_changed = set(envc['value_changed_thm']['user_level']) | set(envc['value_changed_def']['user_level'])
all_changed = set(envd.get('value_changed_thm', [])) | set(envd.get('value_changed_def', []))
C = {}
for l in open(f'{B}/probes/cause_new.tsv'):
    f = l.rstrip('\n').split('\t')
    if len(f) == 4: C[f[1]] = (int(f[2]), f[3], f[0])
miss = [n for n in user_changed if n not in C]
print('\ncause probe: values scanned', len(C), '; user-level changed', len(user_changed), '; not found in probe', len(miss), miss[:5])
ref = [n for n in user_changed if C[n][0] > 0]; noref = sorted(n for n in user_changed if C[n][0] == 0)
print('user-level changed values that refer directly to a declaration whose type changed (or that is new):', len(ref), 'of', len(user_changed))
print('  ... that do not:', noref)
# contingency over all scanned values
tab = collections.Counter()
for n, (h, ex, m) in C.items(): tab[(n in all_changed, h > 0)] += 1
print('all values: changed&refers', tab[(True, True)], '| changed&no-ref', tab[(True, False)], '| unchanged&refers', tab[(False, True)], '| unchanged&no-ref', tab[(False, False)])
# what the user-level changed ones refer to (categories of the hit names)
def hcat(x):
    if re.search(r'^(instr|admininstr|wf_instr|wf_admininstr)(\.below)?\.(casesOn|rec|recOn|brecOn|below|noConfusion|noConfusionType|ctorIdx)', x) or re.search(r'^(instr|admininstr)\.[A-Z_0-9]+\.elim$', x): return 'eliminators of the changed inductives'
    if re.search(r'\.eq_\d+$|match_\d+', x): return 'equation lemmas / matchers of the changed definitions'
    if re.search(r'_proof_|_simp_|_hyg|decEq|_sparseCasesOn', x): return 'renumbered or regenerated auxiliaries'
    return 'other: ' + x
hc = collections.Counter()
for n in ref:
    for x in [y for y in C[n][1].split(',') if y][:1]: hc[hcat(x)] += 1
print('first referenced changed declaration, by category:', dict(hc))
json.dump({'user_changed_refer': len(ref), 'user_changed_total': len(user_changed), 'user_changed_noref': noref, 'contingency': {str(k): v for k, v in tab.items()}, 'first_hit_categories': dict(hc),
           'examples': {n: C[n][1] for n in sorted(ref)[:400]}}, open(f'{B}/work/cause33.json', 'w'), indent=1)
# ---------------- user-level contingency (internal names classified by the same rules as envcat33.py)
src = open(f'{B}/tools/envcat33.py').read()
ns = {}; exec(src[src.index('RULES = ['):src.index('def cat(')], ns)  # v4: robust to the v3 signature cat(n, k='')
RULES = ns['RULES']
def internal(n): return any(re.search(p, n) for p, _ in RULES)
only_new = set(envd['only_new'])
ut = collections.Counter()
for n, (h, ex, m) in C.items():
    if n in only_new or internal(n): continue
    ut[(n in all_changed, h > 0)] += 1
print('USER-LEVEL values: changed&refers', ut[(True, True)], '| changed&no-ref', ut[(True, False)], '| unchanged&refers', ut[(False, True)], '| unchanged&no-ref', ut[(False, False)])
j = json.load(open(f'{B}/work/cause33.json')); j['user_level_contingency'] = {str(k): v for k, v in ut.items()}; json.dump(j, open(f'{B}/work/cause33.json', 'w'), indent=1)

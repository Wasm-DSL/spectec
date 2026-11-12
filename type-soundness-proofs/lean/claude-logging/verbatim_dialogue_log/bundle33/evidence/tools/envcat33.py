# bundle33: categorize the environment differences (envdiff33.json) for the report.
import json, re, collections, sys
B = sys.argv[1]; d = json.load(open(f'{B}/work/envdiff33.json'))
mods = {}
for p in ['dump_old.tsv', 'dump_new.tsv']:
    for l in open(f'{B}/probes/{p}'):
        f = l.rstrip('\n').split('\t')
        if len(f) == 6: mods.setdefault(f[2], f[0])
RULES = [
 (r'(^|\.)(instr|admininstr)\.EXTEND$', 'the removed constructor itself'),
 (r'_case_19_EXTEND_removed$', 'the removed EXTEND case of wf_instr / wf_admininstr (or of its .below)'),
 (r'\.EXTEND\.(elim|inj|injEq|noConfusion|sizeOf_spec)$', 'auto-generated lemmas/eliminators of the removed constructor'),
 (r'\.decEq\._proof_\d+$', 'derived DecidableEq auxiliary proofs (numbered per constructor)'),
 (r'match_on_same_ctor.*_hyg', 'derived-instance helpers with hygienic names (counter shifted)'),
 (r'(^|\.)(rec|rec_\d+|casesOn|recOn|below|below_\d+|brecOn|brecOn_\d+|binductionOn|noConfusionType|noConfusion|ctorIdx|toCtorIdx|ctorElim|ctorElimType)(\.go|\.eq)?$', 'recursors / case eliminators / structural-recursion helpers / no-confusion of the changed inductives'),
 (r'\.below\.', 'constructors of the auxiliary .below inductive'),
 (r'^(instr|admininstr)\.[A-Z_0-9]+\.elim$', 'per-constructor eliminators X.CTOR.elim of the changed inductives'),
 (r'\._sizeOf_\d+$|\.sizeOf_spec$|_sizeOf_inst$', 'derived SizeOf'),
 (r'_auxDecEq|^instBEq|^instDecidableEq|\.beq|decEq', 'derived DecidableEq / BEq'),
 (r'\.match_\d+\.eq_\d+$|\.match_\d+\.splitter|_sparseCasesOn|\.match_\d+$|\.match_\d+\.', 'pattern-matching auxiliaries (matchers, splitters, their equations)'),
 (r'\.eq_\d+$|\.eq_def$', 'equation lemmas of definitions by pattern matching (one per arm, numbered)'),
 (r'\._proof_\d+(_\d+)?$', 'auxiliary proof terms (numbered per declaration)'),
 (r'\._simp_\d+_\d+$|\._simp_\d+$', 'auxiliary simp lemmas (numbered)'),
 (r'\._unsafe_rec$|\._sunfold$|\._f$|_cstage|_closed', 'compiler / structural-recursion auxiliaries'),
]
def cat(n, k=''):
    for pat, lab in RULES:
        if re.search(pat, n):
            # v3 (after verifier V2-FIX): a hygienic helper present under the same name in both builds did not get a new
            # counter; its type/value changed because it cases on an inductive that lost a constructor
            if lab.startswith('derived-instance helpers with hygienic names') and k not in ('only_old', 'only_new'):
                return 'derived DecidableEq helpers (match_on_same_ctor) of the changed inductives, same name in both builds'
            return lab
    return None
out = {}
for k, names in d.items():
    c = collections.Counter(); user = []
    for n in names:
        lab = cat(n, k)
        if lab is None or lab in ('the removed constructor itself', 'the removed EXTEND case of wf_instr / wf_admininstr (or of its .below)') and not n.startswith('wf_') and False:
            pass
        if lab is None: user.append(n); c['USER-LEVEL (listed)'] += 1
        else: c[lab] += 1
    out[k] = dict(total=len(names), categories=dict(c), user_level=sorted(user, key=lambda n: (mods.get(n, '?'), n)))
    print(f'== {k}: {len(names)}')
    for lab, v in c.most_common(): print(f'     {v:5d}  {lab}')
    if user: print('     user-level:', ', '.join(f'{mods.get(n,"?")}:{n}' for n in out[k]['user_level'][:200]))
json.dump(out, open(f'{B}/work/envcat33.json', 'w'), indent=1)

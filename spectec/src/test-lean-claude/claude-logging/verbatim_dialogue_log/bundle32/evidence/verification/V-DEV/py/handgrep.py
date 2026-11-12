import re, sys, json
W = sys.argv[1]; V = sys.argv[2]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
old = rd(W + '/OLD.lean')
c = json.load(open(V + '/classify.json'))
hand = c['hand_old']
with open(V + '/hand_old.txt', 'w', encoding='utf-8') as f:
    for i in hand:
        f.write('%6d: %s\n' % (i, old[i-1]))
pats = {
 'instr_case_any': r'(?<![A-Za-z0-9_])instr_case_\d+',
 'admininstr_case_any': r'(?<![A-Za-z0-9_])admininstr_case_\d+',
 'case_19': r'(?<![A-Za-z0-9_])(admin)?instr_case_19(?![0-9])',
 'EXTEND': r'EXTEND',
 'rec/casesOn/etc': r'\.(rec|recOn|casesOn|brecOn|binductionOn|below|noConfusion|toCtorIdx|ctorIdx|ctorElim|ctorElimType)\b',
 'rcases/obtain': r'\b(rcases|obtain|rintro)\b',
 'cases': r'\bcases\b',
 'induction': r'\binduction\b',
 'match': r'\bmatch\b',
 'next': r'\bnext\b',
 'case kw': r'^\s*case\s',
 'constructor tactic': r'\bconstructor\b',
 'injection/simp only on ctor': r'\binjection\b',
 'wf_instr': r'\bwf_instr\b',
}
for k,p in pats.items():
    hits = [i for i in hand if re.search(p, old[i-1])]
    print('%-26s %4d hits' % (k, len(hits)), hits[:40])

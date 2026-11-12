# bundle33: scan the downstream proof modules for every reference affected by the EXTEND removal.
# Code (outside comments): tokens (admin)?instr_case_N mapped through the constructor map (by meaning);
# EXTEND tokens with their qualifier. Comments: the same tokens plus EXTEND, reported separately.
import re, sys, json
sys.path.insert(0, sys.argv[1]); from toplevel32 import code_mask, constructs, owner
cm = json.load(open(sys.argv[2])); srcdir = sys.argv[3]; mods = sys.argv[4].split(',')
mp = {'instr_case': cm['wf_instr']['map'], 'admininstr_case': cm['wf_admininstr']['map']}
meaning = {'instr_case': cm['wf_instr']['instr_of_old_ctor'], 'admininstr_case': cm['wf_admininstr']['instr_of_old_ctor']}
out = {}
for m in mods:
    L = open(f'{srcdir}/{m}.lean').read().split('\n'); C = code_mask(L); cons = constructs(L)
    res = {'code_renames': [], 'code_extend': [], 'code_unmapped': [], 'comment_hits': []}
    for i, (l, c) in enumerate(zip(L, C), 1):
        own = owner(cons, i); oname = own['name'] if own else None
        for mt in re.finditer(r'\b(admininstr_case|instr_case)_(\d+)\b', c):
            # make sure it's not the tail of a longer identifier like foo_instr_case_3 (\b handles letters/_ before? '_' is a word char so \b fails) -> fine
            fam, k = mt.group(1), mt.group(2); old = f'{fam}_{k}'; new = mp[fam].get(old)
            if new is None: res['code_unmapped'].append((i, old, l.strip()))
            elif new != old: res['code_renames'].append((i, old, new, meaning[fam][old], oname, l.strip()))
        for mt in re.finditer(r'([\w.]*)\bEXTEND\b', c):
            res['code_extend'].append((i, mt.group(0), oname, l.strip()))
        com = ''.join(ch for ch, cc in zip(l, c.ljust(len(l))) if True)  # placeholder
        # comment part = characters of l not in code: recompute crudely as l minus code if code is a prefix
        commentpart = l if not c else (l[len(c):] if l.startswith(c) else l)
        if re.search(r'\b(admininstr_case|instr_case)_\d+\b|EXTEND|\b6[78]\b|\b7[34]\b', commentpart):
            res['comment_hits'].append((i, oname, l.strip()))
    out[m] = res
    print(f'== {m}: code renames {len(res["code_renames"])}, code EXTEND tokens {len(res["code_extend"])}, unmapped {len(res["code_unmapped"])}, comment hits {len(res["comment_hits"])}')
    for r in res['code_renames']: print('   R', r[0], r[1], '->', r[2], f'({r[3]})', 'in', r[4], '|', r[5][:150])
    for r in res['code_extend']: print('   E', r[0], r[1], 'in', r[2], '|', r[3][:150])
    for r in res['code_unmapped']: print('   U', r)
    for r in res['comment_hits']: print('   C', r[0], 'in', r[1], '|', r[2][:170])
json.dump(out, open(sys.argv[5], 'w'), indent=1)

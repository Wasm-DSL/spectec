# Classify every difference between the old generated model (G_old) and the new one (G_new).
# Normalize G_old: drop EXTEND lines, renumber instr_case_K/admininstr_case_K (K>=20 -> K-1),
# shift 1-syntax.spectec source positions after line 474 by -1. Residual differences => non-EXTEND change.
import re, sys, difflib
old = open(sys.argv[1]).read().split('\n'); new = open(sys.argv[2]).read().split('\n')
dropped = []
def shift_loc(m):
    def f(n): n=int(n); return str(n-1) if n > 474 else str(n)
    return '1-syntax.spectec:%s.%s-%s.%s' % (f(m.group(1)), m.group(2), f(m.group(3)), m.group(4))
norm = []
for i, l in enumerate(old):
    if ('instr.EXTEND' in l) or re.match(r'\s*\| EXTEND \(v_numtype : numtype\) \(v_n : n\) : (admin)?instr\s*$', l):
        dropped.append((i+1, l)); continue
    l2 = re.sub(r'\b(admininstr_case_|instr_case_)(\d+)\b', lambda m: m.group(1)+(str(int(m.group(2))-1) if int(m.group(2))>=20 else m.group(2)), l)
    l2 = re.sub(r'1-syntax\.spectec:(\d+)\.(\d+)-(\d+)\.(\d+)', shift_loc, l2)
    norm.append(l2)
print("old lines:", len(old), "new lines:", len(new), "dropped EXTEND lines:", len(dropped))
for n,l in dropped: print("  dropped old line %d: %s" % (n, l))
# residual check
sm = difflib.SequenceMatcher(None, norm, new, autojunk=False)
res = [op for op in sm.get_opcodes() if op[0] != 'equal']
print("residual differences after normalization:", len(res))
for op in res[:50]:
    print(op); print("   old:", norm[op[1]:op[2]][:5]); print("   new:", new[op[3]:op[4]][:5])
# Also: does any EXTEND remain in new? any instr_case_19 meaning?
print("EXTEND occurrences in new:", sum('EXTEND' in l for l in new))
# Check which case numbers were affected (are there instr_case_19 in old that is EXTEND?)
for name in ['instr_case_19','admininstr_case_19']:
    print(name, 'old:', [l.strip()[:110] for l in old if re.search(r'\b%s\b'%name, l)][:3])
    print(name, 'new:', [l.strip()[:110] for l in new if re.search(r'\b%s\b'%name, l)][:3])

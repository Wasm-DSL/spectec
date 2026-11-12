# bundle33: evidence that each of the 56 renames in the model's proofs is needed.
# (1) bundle32's compile of the unrenamed copy (72 errors): error on the line itself, or on a neighbouring line (+-2) of
#     the same term; (2) otherwise the line sits inside a `cases` alternative whose renamed pattern line failed first, so
#     Lean never elaborated it: for those, b33/nec13 compiled NEW with only those lines reverted (errors per line).
import json, re, sys
B = sys.argv[1]; E = sys.argv[2]
txt = open(E).read(); err = set(int(m.group(1)) for m in re.finditer(r'^wasm2\.0\.lean:(\d+):\d+: error', txt, re.M))
N = open(f'{B}/final/src/wasm2.0.lean').read().split('\n'); ind = lambda l: len(l) - len(l.lstrip(' '))
d = json.load(open(f'{B}/work/diff33.json')); rows = [r for r in d['rows'] if r['cat'] == 'ctor-renumber/hand-layer']
n13 = json.load(open(f'{B}/nec13/result.json'))['errors']
out = {}
for r in rows:
    L = r['new']
    if L in err: out[L] = ['own', L]; continue
    near = [x for x in range(L - 2, L + 3) if x in err and x != L]
    li = ind(N[L - 1]); hdr = None; k = L - 1
    while k > 0 and not near:
        t = N[k - 1]
        if t.strip().startswith('|') and ind(t) < li:
            if k in err: hdr = k; break
            li = ind(t)
        if t and not t[0].isspace(): break
        k -= 1
    if near: out[L] = ['same-term', sorted(near)]
    else: out[L] = ['inside-alternative', hdr, str(L) in n13]
json.dump({'per_line': {str(k): v for k, v in out.items()}, 'errlines': sorted(err)}, open(f'{B}/work/necessity33.json', 'w'), indent=1)
from collections import Counter
print(Counter(v[0] for v in out.values()), 'inside-alternative lines with their own error when reverted alone:', sum(1 for v in out.values() if v[0] == 'inside-alternative' and v[2]))

# Count list indexing `...]!` (IL IdxE) inside iteration sources of inductive relations.
import re, sys
exec(open(sys.argv[2]).read().split('rows = []')[0])   # reuse parser: text, match, src_spans, units, unit_of
def top_of(u):
    k = u
    while not re.match(r'(inductive|def|theorem|axiom|opaque|lemma|abbrev|structure|instance) ', text[units[k]:units[k]+12]): k -= 1
    return text[units[k]:units[k]+60].split('\n')[0]
n_all = n_src = 0; ex = []
for m in re.finditer(r'\]!', text):
    p = m.start(); u = unit_of(p)
    if not top_of(u).startswith('inductive '): continue
    n_all += 1
    if any(s <= p < t for s, t in src_spans):
        n_src += 1; ex.append((text.count('\n', 0, p) + 1, top_of(u)[:50]))
print(f"xs[i]! in inductive relations: {n_all}; inside an iteration source: {n_src}")
for e in ex[:10]: print("   line", e[0], e[1])

# Classify every `Option.get! X` in a generated Lean model:
#   src  = X sits inside an iteration *source* argument (the list after the lambda of Map/Forall/Forall2/Forall3)
#   body = everywhere else
# and whether the same declaration/constructor contains a guard `X' ≠ none` with X' equal to X up to
# iteration-variable renumbering. Read-only; prints a summary and examples.
import re, sys, collections
text = open(sys.argv[1], encoding='utf-8').read()
# paren matching
match = {}; st = []
for i, ch in enumerate(text):
    if ch == '(': st.append(i)
    elif ch == ')': match[st.pop()] = i
def group_end(i):          # i at '(' -> index after ')'; or identifier token
    if text[i] == '(': return match[i] + 1
    m = re.compile(r'[^\s()]+').match(text, i); return m.end()
def skip_ws(i):
    while text[i] in ' \t\n': i += 1
    return i
NSRC = {'Map': 1, 'Forall': 1, 'Forall₂': 2, 'Forall₃': 3}
src_spans = []
for m in re.finditer(r'(?<![\w.])(Map|Forall₃|Forall₂|Forall) \(fun ', text):
    lam = m.start(1) + len(m.group(1)) + 1
    j = match[lam] + 1
    for _ in range(NSRC[m.group(1)]):
        j = skip_ws(j); e = group_end(j); src_spans.append((j, e)); j = e
# declaration / constructor units
units = []
for m in re.finditer(r'(?m)^(inductive|def|theorem|axiom|opaque|lemma|abbrev|structure|instance) |^  \| ', text):
    units.append(m.start())
units.append(len(text))
def unit_of(p):
    lo, hi = 0, len(units) - 1
    while lo < hi - 1:
        mid = (lo + hi) // 2
        if units[mid] <= p: lo = mid
        else: hi = mid
    return lo
norm = lambda s: re.sub(r'_\d+_elem', '_elem', re.sub(r'(iter_\d+)_\d+', r'\1', s))
guards = collections.defaultdict(set)
for m in re.finditer(r'\(([^()]*(?:\([^()]*\)[^()]*)*)\) ≠ none', text):
    guards[unit_of(m.start())].add(norm(m.group(1)))
rows = []
for m in re.finditer(r'Option\.get! ', text):
    a = skip_ws(m.end()); e = group_end(a); arg = text[a:e]
    if arg.startswith('(') and arg.endswith(')'): arg = arg[1:-1]
    p = m.start(); u = unit_of(p)
    insrc = any(s <= p < t for s, t in src_spans)
    guarded = norm(arg) in guards[u]
    head = text[units[u]:units[u]+120].split('\n')[0]
    rows.append((insrc, guarded, arg, head))
c = collections.Counter((r[0], r[1]) for r in rows)
print(f"Option.get! occurrences: {len(rows)}")
for k in [(True, False), (True, True), (False, True), (False, False)]:
    print(f"  {'in iteration source' if k[0] else 'elsewhere           '}  {'guarded  ' if k[1] else 'UNGUARDED'}: {c[k]}")
def where(head):
    m = re.match(r'\s*\| (\S+)', head) or re.match(r'\S+ (\S+)', head)
    return m.group(1) if m else head
for k, title in [((True, False), 'in source, unguarded'), ((False, False), 'elsewhere, unguarded'), ((True, True), 'in source, guarded')]:
    sel = [r for r in rows if (r[0], r[1]) == k]
    fam = collections.Counter(re.sub(r'_case_\d+$', '', where(r[3])) for r in sel)
    print(f"--- {title}: {len(sel)} in {len(fam)} relations/decls")
    for name, n in fam.most_common(): print(f"     {n:4d}  {name}")
    for r in sel[:3]: print(f"     e.g. get! ({r[2]})   in {where(r[3])}")

# --- refined: only inductive relations (generated model text); guards incl. unparenthesised ones
print("=== refined (inductive declarations only)")
line_of = lambda p: text.count('\n', 0, p) + 1
def top_of(u):
    k = u
    while not re.match(r'(inductive|def|theorem|axiom|opaque|lemma|abbrev|structure|instance) ', text[units[k]:units[k]+12]): k -= 1
    return text[units[k]:units[k]+90].split('\n')[0]
cnt = collections.Counter(); resid = []
for m in re.finditer(r'Option\.get! ', text):
    a = skip_ws(m.end()); e = group_end(a); arg = text[a:e]
    if arg.startswith('(') and arg.endswith(')'): arg = arg[1:-1]
    p = m.start(); u = unit_of(p); top = top_of(u)
    if not top.startswith('inductive '): continue
    insrc = any(s <= p < t for s, t in src_spans)
    plain = set(re.findall(r'(?<![\w.])(\w+) ≠ none', text[units[u]:units[u+1]]))
    guarded = norm(arg) in (guards[u] | plain)
    closed = not re.search(r'\b(v_|var_|lane_|nt|i|l|c|ci_lst|sh|z|x|k)\w*\b(?! :)', re.sub(r'\b(valtype_\w+|numtype\.\w+|Inn\.\w+|Fnn\.\w+|size|proj_\w+|lanetype_\w+|Jnn\.\w+|packtype\.\w+)\b', '', arg))
    key = ('src' if insrc else 'else', 'guarded' if guarded else ('closed' if closed else 'UNGUARDED'))
    cnt[key] += 1
    if key[1] != 'guarded': resid.append((line_of(p), key, where(text[units[u]:units[u]+120].split('\n')[0]), arg[:70], top[:55]))
for k, v in sorted(cnt.items()): print(f"  {k[0]:5s} {k[1]:10s} {v}")
print("--- every unguarded / closed occurrence:")
for r in resid: print(f"{r[0]:6d} {r[1][0]:4s} {r[1][1]:9s} {r[2]:26s} get! ({r[3]})  [{r[4]}]")

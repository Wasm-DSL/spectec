# bundle32 3-way line merge. base = G_old (old generated model, = todaywasm2.0_shouldwork),
# ours = OLD (OLD_wasm2.0.lean = G_old + hand layer), theirs = G_new (new generated model).
# Output: candidate = G_new + OLD's hand layer (hand-written lines copied verbatim; no edits here).
# Generated lines are always taken from G_new; hand-written lines always from OLD.
import re, sys, json, difflib
g_old_p, old_p, g_new_p, out_p, meta_p = sys.argv[1:6]
def rd(p):
    s = open(p).read(); assert s.endswith('\n'); return s[:-1].split('\n')
G_old, OLD, G_new = rd(g_old_p), rd(old_p), rd(g_new_p)
def is_extend_instr(l):
    return ('instr.EXTEND' in l) or re.match(r'\s*\| EXTEND \(v_numtype : numtype\) \(v_n : n\) : (admin)?instr\s*$', l) is not None
def shift_loc(m):
    f = lambda n: str(int(n) - 1) if int(n) > 474 else n
    return '1-syntax.spectec:%s.%s-%s.%s' % (f(m.group(1)), m.group(2), f(m.group(3)), m.group(4))
def norm(l):
    l = re.sub(r'\b(admininstr_case_|instr_case_)(\d+)\b', lambda m: m.group(1) + (str(int(m.group(2)) - 1) if int(m.group(2)) >= 20 else m.group(2)), l)
    return re.sub(r'1-syntax\.spectec:(\d+)\.(\d+)-(\d+)\.(\d+)', shift_loc, l)
# T: G_old index -> G_new index (None for the dropped EXTEND lines); verified exact.
T = [None] * len(G_old); k = 0
for i, l in enumerate(G_old):
    if is_extend_instr(l): continue
    assert norm(l) == G_new[k], (i, l, G_new[k]); T[i] = k; k += 1
assert k == len(G_new)
tchanged = {i for i in range(len(G_old)) if T[i] is None or G_new[T[i]] != G_old[i]}
sm = difflib.SequenceMatcher(None, G_old, OLD, autojunk=False)
ops = sm.get_opcodes()
out, src, problems, used_new, replaced_new = [], [], [], [], []
stats = {'equal': 0, 'replace': 0, 'insert': 0, 'delete': 0}
hunks = []
for tag, i1, i2, j1, j2 in ops:
    stats[tag] += 1
    if tag == 'equal':
        for d in range(i2 - i1):
            i = i1 + d
            if T[i] is not None:
                out.append(G_new[T[i]]); src.append(('gen', T[i] + 1, j1 + d + 1)); used_new.append(T[i])
    else:
        hunks.append({'tag': tag, 'gold': [i1 + 1, i2], 'old': [j1 + 1, j2], 'gold_text': G_old[i1:i2], 'old_text_head': OLD[j1:min(j2, j1 + 3)]})
        for i in range(i1, i2):
            if i in tchanged: problems.append({'gold_line': i + 1, 'text': G_old[i], 'hunk': [tag, i1 + 1, i2, j1 + 1, j2]})
            if T[i] is not None: replaced_new.append(T[i])
        for j in range(j1, j2):
            out.append(OLD[j]); src.append(('hand', None, j + 1))
# coverage: every G_new line is either emitted once (in order) or replaced by the hand layer
assert used_new == sorted(used_new) and len(set(used_new)) == len(used_new)
cov = sorted(used_new + replaced_new)
assert cov == list(range(len(G_new))), 'G_new coverage mismatch'
open(out_p, 'w').write('\n'.join(out) + '\n')
json.dump({'stats': stats, 'n_hunks': len(hunks), 'problems': problems, 'hunks': hunks,
           'src': src}, open(meta_p, 'w'))
print('opcodes:', stats, '| non-equal hunks:', len(hunks), '| problems (hand layer touches a T-changed generated line):', len(problems))
print('G_new lines emitted:', len(used_new), 'replaced by hand layer:', len(replaced_new), 'total', len(G_new))
print('candidate lines:', len(out), '| hand lines:', sum(1 for s in src if s[0] == 'hand'), '| OLD lines:', len(OLD))
for p in problems: print('PROBLEM', p)

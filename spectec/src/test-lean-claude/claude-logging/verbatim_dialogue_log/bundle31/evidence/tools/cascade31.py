"""bundle31 sorry-out cascade (adapted from b29/tools/cascade29.py).
Usage: cascade31.py <srcdir> <workdir> <builddir> mod1 mod2 ...
For each module in order: compile a copy (in <workdir>/src) against <builddir>; every declaration
with an error first gets `sorry` as its proof; if it still fails, it is deleted; repeat until the
module compiles, then write its olean into <builddir>. Report: <workdir>/report.json."""
import re, subprocess, sys, json, os
sys.path.insert(0, '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/tools')
from leanparse import items, join, split_stmt_proof
B = '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/b31'
DECLKINDS = ('theorem', 'lemma', 'def', 'abbrev', 'instance', 'inductive', 'structure', 'axiom', 'opaque')
srcdir, work, build = sys.argv[1], sys.argv[2], sys.argv[3]
mods = sys.argv[4:]
os.makedirs(work + '/src', exist_ok=True)
def compile(mod, out=False):
    args = [B + '/tools/lrun31.sh', build, work + '/src', mod + '.lean']
    if out: args += ['-o', build + '/' + mod + '.olean']
    r = subprocess.run(args, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr
def err_lines(log, mod):
    return sorted(set(int(m.group(1)) for m in re.finditer(r'^' + re.escape(mod) + r'\.lean:(\d+):\d+: error', log, re.M)))
report = json.load(open(work + '/report.json')) if os.path.exists(work + '/report.json') else {}
for mod in mods:
    src = open(srcdir + '/' + mod + '.lean', encoding='utf-8').read()
    rounds = []; sorried = set(); deleted = set()
    for rnd in range(12):
        open(work + '/src/' + mod + '.lean', 'w', encoding='utf-8').write(src)
        rc, log = compile(mod)
        errs = err_lines(log, mod)
        open(work + f'/{mod}_round{rnd}.log', 'w').write(log)
        if not errs:
            rc, log = compile(mod, out=True)
            rounds.append({'round': rnd, 'errors': 0})
            break
        its = items(src)
        starts = []; ln = 1
        for it in its:
            starts.append(ln); ln += it['text'].count('\n') + 1
        bad = set()
        for e in errs:
            bad.add(max(i for i, s in enumerate(starts) if s <= e))
        this_s, this_d = [], []
        for k in sorted(bad, reverse=True):
            it = its[k]
            nm = it['name'] or it['text'][:40]
            if it['kind'] in ('theorem', 'lemma', 'def', 'abbrev', 'instance') and nm not in sorried:
                s, p = split_stmt_proof(it['text'])
                if p:
                    tail = it['text'][len(it['text'].rstrip()):]
                    it['text'] = s + ':= sorry' + tail
                    sorried.add(nm); this_s.append(nm); continue
            it['text'] = '-- [cascade: deleted ' + str(nm) + ']\n'
            deleted.add(nm); this_d.append(nm)
            if k > 0 and its[k-1]['kind'] == 'other' and its[k-1]['text'].lstrip().startswith('/--'):
                its[k-1]['text'] = '-- [cascade: deleted doc comment]\n'
            if k > 0 and its[k-1]['kind'] == 'other' and its[k-1]['text'].lstrip().startswith('set_option'):
                its[k-1]['text'] = '-- [cascade: deleted set_option]\n'
        src = join(its)
        rounds.append({'round': rnd, 'errors': len(errs), 'error_decls': len(bad), 'sorried': this_s, 'deleted': this_d})
        print(mod, 'round', rnd, 'errors', len(errs), 'decls', len(bad), 'sorried', len(this_s), 'deleted', len(this_d), flush=True)
    n_decls = sum(1 for it in items(open(srcdir + '/' + mod + '.lean', encoding='utf-8').read()) if it['kind'] in DECLKINDS)
    report[mod] = {'decls': n_decls, 'sorried': sorted(sorried - deleted), 'deleted': sorted(deleted), 'rounds': rounds}
    json.dump(report, open(work + '/report.json', 'w'), indent=1)
    print(mod, 'DONE: decls', n_decls, 'sorried', len(sorried - deleted), 'deleted', len(deleted), flush=True)

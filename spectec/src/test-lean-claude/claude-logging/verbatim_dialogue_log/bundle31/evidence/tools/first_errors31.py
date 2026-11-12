import re, sys, json
sys.path.insert(0, '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/tools')
from leanparse import items
srcf, logf, mod = sys.argv[1], sys.argv[2], sys.argv[3]
src = open(srcf).read(); its = items(src)
starts = []; ln = 1
for it in its:
    starts.append(ln); ln += it['text'].count('\n') + 1
log = open(logf).read()
msgs = re.split(r'(?m)^(?=' + re.escape(mod) + r'\.lean:\d+:\d+: )', log)
first = {}
for m in msgs:
    mm = re.match(re.escape(mod) + r'\.lean:(\d+):(\d+): error[^:]*: (.*)', m)
    if not mm: continue
    e = int(mm.group(1)); k = max(i for i, s in enumerate(starts) if s <= e)
    nm = its[k]['name']
    body = [x.strip() for x in m.strip().split('\n') if x.strip()]
    first.setdefault(nm, []).append((e, ' | '.join(body[:5])[:400]))
out = {nm: {'line': starts[[it['name'] for it in its].index(nm)], 'nerr': len(es), 'first': es[0][1]} for nm, es in first.items()}
json.dump(out, open(logf + '.json', 'w'), indent=1)
for nm, o in out.items():
    print(f"### {nm} L{o['line']} ({o['nerr']} err): {o['first'][:330]}")

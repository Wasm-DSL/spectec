"""Collect per-construct data for the bundle31 report: original text (repo version), first errors
against the new model without the function views (bundle29 cascade, round 0 = all errors of the
original files) and with them (bundle31 scope2 / scope1 logs), cluster, final text (if a final
merged dir is given). Usage: report_data31.py [<final src dir>]"""
import re, sys, json
SP = '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad'
B = SP + '/b31'
sys.path.insert(0, SP + '/tools'); sys.path.insert(0, B + '/tools')
from leanparse import items
from units31 import units
MODS = ['HelperLemmas', 'Subtyping', 'TypingLemmas', 'TypePreservationPure', 'ExtensionLemmas', 'TypePreservation', 'TypeProgress']
def unit_map(text):
    return {u['name']: u['text'] for u in units(text) if u['name']}
def errs(src_text, log_text, mod):
    its = items(src_text); starts = []; ln = 1
    for it in its:
        starts.append(ln); ln += it['text'].count('\n') + 1
    out = {}
    for m in re.split(r'(?m)^(?=' + re.escape(mod) + r'\.lean:\d+:\d+: )', log_text):
        mm = re.match(re.escape(mod) + r'\.lean:(\d+):(\d+): error', m)
        if not mm: continue
        e = int(mm.group(1)); k = max(i for i, s in enumerate(starts) if s <= e)
        nm = its[k]['name']
        lines = [x for x in m.strip().split('\n') if x.strip()]
        out.setdefault(nm, []).append('\n'.join(lines[:12])[:1500])
    return out
r29 = json.load(open(SP + '/b29/cascade/report.json'))
r31 = json.load(open(B + '/cascade2/report.json'))
cl = json.load(open(B + '/clusters.json'))
owner = {}
for lab, (m, names) in cl['clusters'].items():
    for n in names.split(): owner[n] = lab
orig = {m: open(B + '/orig/' + m + '.lean').read() for m in MODS}
origu = {m: unit_map(orig[m]) for m in MODS}
noshim_err = {}
for m in ['ExtensionLemmas', 'TypePreservation', 'TypeProgress']:
    noshim_err[m] = errs(orig[m], open(SP + f'/b29/cascade/{m}_round0.log').read(), m)
withshim_err = {}
for m in ['TypePreservation', 'TypeProgress']:
    withshim_err[m] = errs(open(B + f'/scope2/{m}.lean').read(), open(B + f'/scope2/{m}.full.log').read(), m)
withshim_err['ExtensionLemmas'] = errs(open(B + '/scope1/ExtensionLemmas.lean').read(), open(B + '/scope1/ExtensionLemmas.full.log').read(), 'ExtensionLemmas')
final = None
if len(sys.argv) > 1:
    final = {m: unit_map(open(sys.argv[1] + '/' + m + '.lean').read()) for m in MODS}
entries = {}
def add(name, mod, category):
    e = {'name': name, 'module': mod, 'category': category, 'cluster': owner.get(name, 'main'),
         'orig_text': origu[mod].get(name, ''),
         'noshim_errors': noshim_err.get(mod, {}).get(name, [])[:3],
         'withshim_errors': withshim_err.get(mod, {}).get(name, [])[:3],
         'noshim_cascade': ('deleted' if name in r29[mod]['deleted'] else 'sorried' if name in r29[mod]['sorried'] else 'compiled'),
         'withshim_cascade': ('deleted' if name in r31.get(mod, {'deleted': []})['deleted'] else 'sorried' if name in r31.get(mod, {'sorried': []})['sorried'] else 'compiled')}
    if final is not None: e['final_text'] = final[mod].get(name, '')
    entries[name] = e
for m, v in r29.items():
    for n in v['sorried'] + v['deleted']:
        add(n, m, 'repaired by agents' if n in owner else 'fixed without proof changes (function views) or restated by the main session')
add('mem_bytes_wf', 'TypeProgress', 'changed by the main session (default-independence; not broken)')
json.dump(entries, open(B + '/report/entries.json', 'w'), indent=1, ensure_ascii=False)
from collections import Counter
print(len(entries), Counter(e['category'] for e in entries.values()))
print('no noshim errors recorded for:', [n for n, e in entries.items() if not e['noshim_errors']])

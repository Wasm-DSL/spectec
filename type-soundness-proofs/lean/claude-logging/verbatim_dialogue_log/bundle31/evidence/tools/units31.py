"""bundle31: unit-level diff / validation / merge of agent copies of a Lean module.

A *unit* is a top-level declaration together with the doc comment / attribute / `set_option` lines
directly above it (key = the declaration name), or any other top-level item (section headers,
comments, `namespace`, ...; key = its text plus an occurrence counter). The cascade's markers
`-- [cascade: deleted doc comment]` + `-- [cascade: deleted X]` form the unit of X.

CLI:
  units31.py check <base.lean> <copy.lean> <assigned names, comma-separated>
      Validate an agent copy against the base: only assigned units may change, new units may be
      inserted (new helper declarations), nothing may be removed; no `sorry` may remain in an
      assigned or inserted unit. Prints a summary; exit 1 on violations.
  units31.py merge <base.lean> <out.lean> <copy1.lean>:<names1> <copy2.lean>:<names2> ...
      Apply all agents' changes to the base and write the merged module.
"""
import re, sys, difflib
sys.path.insert(0, '/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/tools')
from leanparse import items

DEL = re.compile(r'^-- \[cascade: deleted (\S+)\]\s*$')
ATTACH = re.compile(r'^(/--|@\[|set_option .* in\s*$|-- \[cascade: deleted doc comment\])')

def units(text):
    its = items(text)
    out, pending, seen = [], [], {}
    def flush_pending():
        for p in pending:
            k = ('other', p['text'])
            seen[k] = seen.get(k, 0) + 1
            out.append({'key': k + (seen[k],), 'name': None, 'text': p['text']})
        pending.clear()
    for it in its:
        t = it['text']
        m = DEL.match(t.split('\n')[0]) if it['kind'] == 'other' else None
        if it['name'] is not None or m:
            name = it['name'] if it['name'] is not None else m.group(1)
            txt = ''.join(p['text'] + '\n' for p in pending) + t
            pending.clear()
            out.append({'key': ('decl', name), 'name': name, 'text': txt})
        elif it['kind'] == 'other' and ATTACH.match(t.lstrip()) and t.lstrip() == t:
            pending.append(it)
        else:
            flush_pending()
            k = ('other', t)
            seen[k] = seen.get(k, 0) + 1
            out.append({'key': k + (seen[k],), 'name': None, 'text': t})
    flush_pending()
    return out

def norm(t):
    return t.rstrip()

def diff(base_u, copy_u, assigned):
    """Return (replacements {key: text}, insertions [(before_key or None, [units])], violations)."""
    bk = [u['key'] for u in base_u]; ck = [u['key'] for u in copy_u]
    sm = difflib.SequenceMatcher(a=bk, b=ck, autojunk=False)
    repl, ins, viol = {}, [], []
    bmap = {u['key']: u for u in base_u}
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            for a, b in zip(base_u[i1:i2], copy_u[j1:j2]):
                if norm(a['text']) != norm(b['text']):
                    if a['name'] in assigned:
                        repl[a['key']] = b['text']
                    else:
                        viol.append(f"modified unassigned unit {a['key'][:2]!r}")
        elif tag == 'insert':
            before = bk[i1] if i1 < len(bk) else None
            ins.append((before, copy_u[j1:j2]))
        else:
            for a in base_u[i1:i2]:
                viol.append(f"removed/reordered base unit {a['key'][:2]!r}")
            if tag == 'replace':
                before = bk[i2] if i2 < len(bk) else None
                ins.append((before, copy_u[j1:j2]))
    base_names = {u['name'] for u in base_u if u['name']}
    for before, us in ins:
        for u in us:
            if u['name'] is None:
                viol.append(f"inserted non-declaration item: {u['text'][:60]!r}")
            elif u['name'] in base_names:
                viol.append(f"inserted a second unit named {u['name']}")
    for k, t in repl.items():
        if re.search(r'(?<![\w.])sorry(?![\w])', strip_comments(t)):
            viol.append(f"sorry remains in assigned unit {k[1]}")
    for before, us in ins:
        for u in us:
            if re.search(r'(?<![\w.])sorry(?![\w])', strip_comments(u['text'])):
                viol.append(f"sorry in inserted unit {u['name']}")
    untouched = [n for n in assigned if ('decl', n) not in repl and ('decl', n) in bmap]
    return repl, ins, viol, untouched

def strip_comments(t):
    t = re.sub(r'/-.*?-/', '', t, flags=re.S)
    return re.sub(r'--[^\n]*', '', t)

def apply(base_u, changes):
    """changes: list of (repl, ins). Returns merged text."""
    repl_all, ins_all = {}, {}
    for repl, ins in changes:
        for k, t in repl.items():
            assert k not in repl_all, f'two agents replaced {k}'
            repl_all[k] = t
        for before, us in ins:
            ins_all.setdefault(before, []).extend(us)
    names = {}
    for us in ins_all.values():
        for u in us:
            assert u['name'] not in names, f"two inserted units named {u['name']}"
            names[u['name']] = 1
    out = []
    for u in base_u:
        for v in ins_all.get(u['key'], []):
            out.append(v['text'])
        out.append(repl_all.get(u['key'], u['text']))
    for v in ins_all.get(None, []):
        out.append(v['text'])
    return '\n'.join(out)

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'check':
        base, copy, assigned = sys.argv[2], sys.argv[3], set(x for x in sys.argv[4].split(',') if x)
        bu = units(open(base, encoding='utf-8').read()); cu = units(open(copy, encoding='utf-8').read())
        repl, ins, viol, untouched = diff(bu, cu, assigned)
        print('replaced assigned units:', ', '.join(sorted(k[1] for k in repl)) or '-')
        print('assigned units NOT changed:', ', '.join(untouched) or '-')
        for before, us in ins:
            print('inserted before', before[1] if before and before[0] == 'decl' else (before[1][:40] if before else 'EOF'), ':', ', '.join(str(u['name']) for u in us))
        if viol:
            print('VIOLATIONS:'); print('\n'.join('  ' + v for v in viol)); sys.exit(1)
        print('OK (no violations)')
    elif cmd == 'merge':
        base, out = sys.argv[2], sys.argv[3]
        bu = units(open(base, encoding='utf-8').read())
        changes = []
        for spec in sys.argv[4:]:
            copy, names = spec.rsplit(':', 1)
            cu = units(open(copy, encoding='utf-8').read())
            repl, ins, viol, untouched = diff(bu, cu, set(names.split(',')))
            if viol:
                print('VIOLATIONS in', copy); print('\n'.join('  ' + v for v in viol)); sys.exit(1)
            changes.append((repl, ins))
        open(out, 'w', encoding='utf-8').write(apply(bu, changes))
        print('merged', len(changes), 'copies into', out)

import re, sys, json
W = sys.argv[1]
def rd(p):
    with open(p, encoding='utf-8') as f:
        return f.read().split('\n')
def ctors(lines, header):
    i = lines.index(header)
    j = i + 1
    out = []  # list of (name, start_line, text_lines)
    cur = None
    while j < len(lines):
        l = lines[j]
        if l.strip() == '' or (not l.startswith(' ') and not l.startswith('\t')):
            break
        m = re.match(r'^  \| (\S+)', l)
        if m:
            if cur: out.append(cur)
            cur = [m.group(1), j+1, [l]]
        else:
            cur[2].append(l)
        j += 1
    if cur: out.append(cur)
    return out, j
go = rd(W + '/G_old.lean'); gn = rd(W + '/G_new.lean')
for hdr in ['inductive wf_admininstr : admininstr → Prop where', 'inductive wf_instr : instr → Prop where']:
    co, endo = ctors(go, hdr); cn, endn = ctors(gn, hdr)
    print(hdr, 'old ctors', len(co), 'new ctors', len(cn), 'old end line', endo, 'new end', endn)
    print('  old names:', co[0][0], '...', co[-1][0], ' new names:', cn[0][0], '...', cn[-1][0])
    # check names sequential
    pre = 'admininstr_case_' if 'admininstr' in hdr else 'instr_case_'
    print('  old sequential:', [c[0] for c in co] == [pre+str(k) for k in range(len(co))], ' new sequential:', [c[0] for c in cn] == [pre+str(k) for k in range(len(cn))])
    od = {c[0]: c for c in co}; nd = {c[0]: c for c in cn}
    # compare K->K-1 (K>=20) and K->K (K<=18)
    def body(c):
        t = '\n'.join(c[2])
        return re.sub(r'^  \| \S+', '  | NAME', t)
    bad = []
    for k in range(len(co)):
        on = pre + str(k)
        if k == 19:
            print('  old', on, 'text:', od[on][2])
            continue
        nk = k - 1 if k >= 20 else k
        nn = pre + str(nk)
        if nn not in nd: bad.append((on, 'missing new')); continue
        if body(od[on]) != body(nd[nn]): bad.append((on, nn))
    print('  mismatching pairs:', bad)
    # uniqueness: for each old ctor text, how many new ctors have same body
    from collections import Counter
    cnt = Counter(body(c) for c in cn)
    nonuniq = [c[0] for c in co if cnt[body(c)] != 1]
    print('  old ctors whose body does not match exactly one new ctor:', nonuniq)
    # Which old ctors have body appearing nowhere in new
    if 'admininstr' in hdr:
        json.dump({c[0]: c[2] for c in co}, open(sys.argv[2] + '/wf_admin_old.json','w'))
        json.dump({c[0]: c[2] for c in cn}, open(sys.argv[2] + '/wf_admin_new.json','w'))

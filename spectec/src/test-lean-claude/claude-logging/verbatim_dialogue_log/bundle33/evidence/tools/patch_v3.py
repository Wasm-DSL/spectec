p = '/tmp/claude-1002/-home-zhengyew-spectec/0793c03a-21df-4d2d-9729-4ba22978b528/scratchpad/b33/tools/report33.py'
s = open(p).read()
def rep(old, new):
    global s
    assert s.count(old) == 1, ('NOT FOUND/UNIQUE', old[:100], s.count(old)); s = s.replace(old, new)
s = s.replace('(v2: after the verifier\'s review.)', '(v3: after two rounds of independent verification.)')
# ---------------------------------------------------------------- extra computed facts
rep("# ------------------------------------------------------------------ text", r'''# ---- v3 facts
import unicodedata
cmap = {k: cm[k] for k in ('wf_instr', 'wf_admininstr')}
def fam_stem(n): return re.sub(r'\d+$', '', n) if re.search(r'\d$', n) else None
def fam_count(D, st): return sum(1 for x in D if re.sub(r'\d+$', '', x) == st and re.search(r'\d$', x))
rm_ext, rm_end, rm_ren = [], [], []
for n in envd['only_old']:
    if 'EXTEND' in n: rm_ext.append(n); continue
    st = fam_stem(n); assert st, n
    (rm_end if fam_count(DN, st) < fam_count(DO, st) else rm_ren).append(n)
assert len(rm_ren) == len(envd['only_new']) and all(fam_count(DN, fam_stem(n)) == fam_count(DO, fam_stem(n)) for n in envd['only_new'])
end_fams = collections.OrderedDict()
for n in sorted(rm_end):
    st = fam_stem(n); end_fams[st] = (fam_count(DO, st), fam_count(DN, st))
# per-module / per-kind
pm = collections.OrderedDict((('«wasm2.0»' if m == 'wasm2.0' else m), collections.Counter()) for m in MODS)
for n, f in DO.items(): pm[f[0]]['old'] += 1
for n, f in DN.items(): pm[f[0]]['new'] += 1
for n in envd['only_old']: pm[DO[n][0]]['removed'] += 1
for n in envd['only_new']: pm[DN[n][0]]['added'] += 1
tchg = set(envd.get('type_changed_thm', [])) | set(envd.get('type_changed_def', [])) | set(envd.get('type_changed_rec', []))
vchg = set(envd.get('value_changed_thm', [])) | set(envd.get('value_changed_def', []))
for n in tchg | vchg: pm[DN[n][0]]['changed'] += 1
pk = collections.OrderedDict((k, (sum(1 for f in DO.values() if f[1] == k), sum(1 for f in DN.values() if f[1] == k))) for k in ['thm', 'def', 'ctor', 'induct', 'rec', 'axiom', 'opaque', 'quot'])
kinds_changed = sorted({DN[n][1] for n in tchg | vchg})
v_not_t = sorted(n for n in envd.get('value_changed_thm', []) if n not in tchg)
# inductive metadata and cause probe
IM = json.load(open(f'{B}/work/indmeta_diff33.json')); CA = json.load(open(f'{B}/work/cause33.json'))
im_ctor = sum(1 for c in IM['changed'] if c['kind'] == 'ctor'); im_ind = [c['name'] for c in IM['changed'] if c['kind'] == 'induct']
im_rec = [c for c in IM['changed'] if c['kind'] == 'rec']
for c in IM['changed']:
    if c['kind'] == 'ctor':
        assert int(re.search(r'cidx=(\d+)', c['old']).group(1)) - int(re.search(r'cidx=(\d+)', c['new']).group(1)) == 1 and re.sub(r'cidx=\d+', '', c['old']) == re.sub(r'cidx=\d+', '', c['new'])
n_meta_old = sum(1 for _ in open(f'{B}/probes/indmeta_old.tsv')); n_meta_new = sum(1 for _ in open(f'{B}/probes/indmeta_new.tsv'))
uc = CA['user_level_contingency']; ucg = lambda a, b: uc.get(str((a, b)), 0)
# byte level
def bytefacts(p):
    b = open(p, 'rb').read(); t = b.decode('utf-8')
    return dict(size=len(b), md5=hashlib.md5(b).hexdigest(), cr=b.count(b'\r'), bom=b.startswith(b'\xef\xbb\xbf'), final_nl=b.endswith(b'\n') and not b.endswith(b'\n\n'),
                trailing_ws=sum(1 for l in t.split('\n') if l != l.rstrip(' \t')), tabs=t.count('\t'))
BF = {(st, m): bytefacts(f'{B}/{st}/src/{m}.lean') for st in ('old', 'final') for m in MODS}
assert all(not f['cr'] and not f['bom'] and f['final_nl'] for f in BF.values())
tw_same = all(BF[('old', m)]['trailing_ws'] == BF[('final', m)]['trailing_ws'] and BF[('old', m)]['tabs'] == BF[('final', m)]['tabs'] for m in MODS)
# warnings sub-kinds and whole-log identity
def wsub(msg):
    if 'is not explicitly referenced' in msg: return 'unused variable'
    if 'does not follow the mathlib naming' in msg: return 'Mathlib naming-convention lint'
    if 'tactic does nothing' in msg: return '"tactic does nothing"'
    if msg.startswith('Used `'): return '"Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"'
    if 'simp argument is unused' in msg: return '"This simp argument is unused"'
    if msg.startswith('Try this'): return '"Try this" suggestion'
    if msg.startswith("try 'simp' instead of 'simpa'"): return "\"try 'simp' instead of 'simpa'\""
    if 'never executed' in msg: return '"this tactic is never executed"'
    return 'other: ' + msg[:60]
wsc = collections.Counter(wsub(x) for m in MODS for x in W[('new', m)])
def norm_log(p):
    t = open(p).read()
    t = re.sub(r'(?m)^\S+\.lean:\d+:\d+: ', '', t); t = re.sub(r'(?m)^(Command exited with non-zero status \d+|WALL .*)$\n?', '', t)
    return t
logs_same = all(norm_log(f'{B}/old/logs/{m}.log') == norm_log(f'{B}/final/logs/{m}.log') for m in MODS)
n_info = sum(len(re.findall(r'(?m)^\S+\.lean:\d+:\d+: info', open(f'{B}/final/logs/{m}.log').read())) for m in MODS)
def maxrss(p):
    v = re.findall(r'MAXRSS (\d+) KB', open(p).read()); return int(v[-1]) if v else 0
probe_logs = [f'{B}/probes/{x}' for x in ('envdump_old.log', 'envdump_new.log', 'audit_old.log', 'audit_new.log', 'indmeta_old.log', 'indmeta_new.log', 'cause_new.log')] + [f'{B}/ctl/audit_ctl.log']
probe_peak = max(maxrss(p) for p in probe_logs)
new_tp_rss = int(cn['TypeProgress'][8])
# documentation
living_hits_l = [(os.path.relpath(f, docs_dir), i + 1, l.strip()) for f in living for i, l in enumerate(open(f)) if re.search(r'EXTEND|(admin)?instr_case_\d+', l)]
hist_by_bundle = collections.Counter(); hist_sc = 0
for root, _, files in os.walk(docs_dir):
    for f in files:
        pth = os.path.join(root, f)
        if '/bundle33' in pth: continue
        try: hit = any(re.search(r'\b(admin)?instr_case_(19|[2-7][0-9])\b', l) for l in open(pth, errors='ignore'))
        except Exception: hit = False
        if not hit: continue
        if '/safety-checks/' in pth: hist_sc += 1
        mm = re.search(r'/verbatim_dialogue_log/(bundle\d+)/', pth)
        if mm: hist_by_bundle[mm.group(1)] += 1
# comment citations of model line numbers (which declaration each names is read from the comment; positions computed)
CIT = [('HelperLemmas', 678, '4203', 'opaque nbytes_ '), ('HelperLemmas', 726, '2652', 'opaque truncz '), ('HelperLemmas', 734, '4644', 'opaque lanes_ '),
       ('TypingLemmas', 838, '11261', 'def val_ref '), ('Subtyping', 15, '12669', 'inductive Valtype_sub '), ('Subtyping', 15, '12675', 'inductive Resulttype_sub ')]
def decl_line(lines, head): hs = [i + 1 for i, l in enumerate(lines) if l.startswith(head)]; assert len(hs) == 1, head; return hs[0]
cit_rows = []
for (m, l, cited, head) in CIT:
    L_ = rd('final', m); assert cited in L_[l - 1], (m, l, cited)
    cit_rows.append((m, l, cited, head.split()[1], decl_line(MO, head), decl_line(MN, head)))
size_cited = [l for l in rd('final', 'HelperLemmas') if 'wasm2.0.lean:798' in l]; size_old = decl_line(MO, 'def size '); size_new = decl_line(MN, 'def size ')
# HEAD's versions of the two non-module files
def headfile(rel):
    b = subprocess.run(['git', '-C', '/home/zhengyew/spectec', 'show', f'HEAD:{rel}'], capture_output=True, env=dict(os.environ, GIT_OPTIONAL_LOCKS='0')).stdout
    return hashlib.md5(b).hexdigest(), b.count(b'\n')
head_old = headfile('spectec/src/test-lean-claude/OLD_wasm2.0.lean'); head_prev = headfile('spectec/src/test-lean-claude/wasm2.0_prevattempt.lean')
wt_old_md5 = md5('/home/zhengyew/spectec/spectec/src/test-lean-claude/OLD_wasm2.0.lean'); wt_old_lines = sum(1 for _ in open('/home/zhengyew/spectec/spectec/src/test-lean-claude/OLD_wasm2.0.lean'))
# bundle32 compile of the unrenamed copy (necessity of the 56 model-proof renames)
NEC = json.load(open(f'{B}/work/b32_necessity.json')); errlines = NEC['errlines']
def nearest(l): return min(errlines, key=lambda x: (abs(x - l), x))
# construct counts by definition
ckind = {}
for m in MODS:
    cc = collections.Counter(); 
    for c in constructs(rd('final', m)):
        k = c['kind']
        if k == '@[' or k == 'UNKNOWN' or (k == 'set_option' and c['name'].rstrip().endswith(' in')): cc['prefix'] += 1
        else: cc['decl'] += 1
    ckind[m] = cc
n_decl_entries = sum(ckind[m]['decl'] for m in MODS)
# ------------------------------------------------------------------ text''')
open(p, 'w').write(s)
print('stage 1 ok')

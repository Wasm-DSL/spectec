# bundle33: generate the old-vs-new diff report. Every count, line number and listed name is computed here from the
# files, the build logs and the Lean outputs; the explanatory prose is hand-written. (v3: after two rounds of independent verification.)
import json, re, collections, hashlib, sys, os, subprocess, gzip
B = sys.argv[1]; OUT = sys.argv[2]; TOOLS = sys.argv[3]
sys.path.insert(0, TOOLS); from toplevel32 import constructs, code_mask
J = lambda p: json.load(open(f'{B}/{p}'))
diff = J('work/diff33.json'); cm = J('work/ctor_map33.json'); edits = J('work/edits33.json')
envd = J('work/envdiff33.json'); envc = J('work/envcat33.json')
rows = diff['rows']; summ = diff['summary']
MODS = ['ExtendedDeriveDecEq', 'wasm2.0', 'HelperLemmas', 'Subtyping', 'TypingLemmas', 'TypePreservationPure',
        'ExtensionLemmas', 'TypePreservation', 'TypeProgress']
REPAIRED = ['TypingLemmas', 'TypePreservationPure', 'TypePreservation', 'TypeProgress']
rd = lambda st, m: open(f'{B}/{st}/src/{m}.lean').read().split('\n')
md5 = lambda p: hashlib.md5(open(p, 'rb').read()).hexdigest()
meaning = cm['wf_admininstr']['instr_of_old_ctor']
def esc(s): return s.replace('|', '\\|')
def code(s): s = s.strip(); return '`` ' + s + ' ``' if '`' in s else '`' + s + '`'
def fmt(n): return f'{n:,}'
# ------------------------------------------------------------------ computed facts
# constructs
cons = {}
for m in MODS:
    a = [(c['kind'], c['name']) for c in constructs(rd('old', m))]; b = [(c['kind'], c['name']) for c in constructs(rd('final', m))]
    assert a == b, m; cons[m] = len(a)
n_cons = sum(cons.values())
pc = collections.OrderedDict()
for r in rows: pc.setdefault((r['file'], r['kind'], r['construct']), collections.Counter())[r['cat']] += 1
loc_only = [k for k, v in pc.items() if set(v) == {'source-location'}]; code_changed = [k for k in pc if k not in loc_only]
# rule / constructor counts
def nctors(lines, ind):
    idx = [k for k, l in enumerate(lines) if re.match(r'^inductive %s\b' % re.escape(ind), l)]; assert idx, ind
    n = 0
    for l in lines[idx[0] + 1:]:
        if l.strip() == '': continue
        if not l.startswith(' ') and not l.startswith('--') and not l.startswith('/-'): break
        if re.match(r'^\s*\|\s*\S', l): n += 1
    return n
MO, MN = rd('old', 'wasm2.0'), rd('final', 'wasm2.0')
rc = {ind: (nctors(MO, ind), nctors(MN, ind)) for ind in ['instr', 'admininstr', 'wf_instr', 'wf_admininstr', 'Instr_ok', 'Step_pure', 'Step_read', 'Step']}
for ind in ['Instr_ok', 'Step_pure', 'Step_read', 'Step']: assert rc[ind][0] == rc[ind][1]
extend_mentions_old = [(i + 1, l) for i, l in enumerate(MO) if re.search(r'\b(admin)?instr\.EXTEND\b|^\s*\| EXTEND \(v_numtype', l)]
# spec commit
gs = subprocess.run(['git', '-C', '/home/zhengyew/spectec', 'show', '28073cddd', '--', 'specification/wasm-2.0/1-syntax.spectec'],
                    capture_output=True, text=True, env=dict(os.environ, GIT_OPTIONAL_LOCKS='0')).stdout
hunk = re.search(r'^@@ -(\d+),\d+ \+\d+,\d+ @@ (.*)$', gs, re.M); start = int(hunk.group(1)); frag = hunk.group(2).strip()
body = gs[hunk.end():].split('\n')[1:]; ln = start; deleted = None
for l in body:
    if l.startswith('-'): deleted = (ln, l[1:]); break
    ln += 1
spec_line, spec_text = deleted
subj = re.search(r'^    (.+)$', gs, re.M).group(1)
# dumps / env
def load_dump(p):
    d = {}
    for l in gzip.open(p, 'rt') if p.endswith('.gz') else open(p):
        f = l.rstrip('\n').split('\t')
        if len(f) == 6: d[f[2]] = f
    return d
DO, DN = load_dump(f'{B}/probes/dump_old.tsv'), load_dump(f'{B}/probes/dump_new.tsv')
n_old, n_new = len(DO), len(DN); t_old = sum(1 for f in DO.values() if f[1] == 'thm'); t_new = sum(1 for f in DN.values() if f[1] == 'thm')
common = len(set(DO) & set(DN)); assert len(set(DO) - set(DN)) == len(envd['only_old']) and len(set(DN) - set(DO)) == len(envd['only_new'])
thm_removed = sum(1 for n in envd['only_old'] if DO[n][1] == 'thm'); thm_added = sum(1 for n in envd['only_new'] if DN[n][1] == 'thm')
assert t_old - t_new == thm_removed - thm_added
def mainax(p):
    t = open(p).read(); res = {}
    for nm in ['t_preservation', 't_progress']:
        mm = re.search(r'axioms of TLC\.%s \((\d+)\): \[(.*?)\]' % nm, t, re.S)
        res[nm] = [x.strip() for x in mm.group(2).split(',')]; assert len(res[nm]) == int(mm.group(1))
    res['sorry'] = int(re.search(r'depending on sorryAx: (\d+)', t).group(1)); return res
AO, AN = mainax(f'{B}/probes/envdump_old.log'), mainax(f'{B}/probes/envdump_new.log')
assert AO['t_preservation'] == AN['t_preservation'] and AO['t_progress'] == AN['t_progress'] and AO['sorry'] == AN['sorry'] == 0
def axsplit(lst):
    std = [a for a in lst if a in ('propext', 'Classical.choice', 'Quot.sound')]; wf = [a for a in lst if a.endswith('_is_wf')]
    tlc = [a for a in lst if a.startswith('TLC.')]; assert len(std) + len(wf) + len(tlc) == len(lst); return len(std), len(wf), len(tlc)
ax_pres, ax_prog = axsplit(AN['t_preservation']), axsplit(AN['t_progress'])
axch = envd['axioms_changed']; axdesc = ', '.join(f'`{n}` {{{DO[n][5].replace("-", "")}}}→{{{DN[n][5].replace("-", "")}}}' for n in axch)
def audit(p):
    t = open(p).read(); return (int(re.search(r'module constants: (\d+)', t).group(1)), int(re.search(r'theorems checked: (\d+)', t).group(1)),
                                int(re.search(r'theorems needing a default value: (\d+)', t).group(1)))
UO, UN = audit(f'{B}/probes/audit_old.txt'), audit(f'{B}/probes/audit_new.txt')
edd_c = sum(1 for f in DO.values() if f[0] == 'ExtendedDeriveDecEq'); edd_t = sum(1 for f in DO.values() if f[0] == 'ExtendedDeriveDecEq' and f[1] == 'thm')
assert n_old - UO[0] == edd_c and t_old - UO[1] == edd_t
eqfam = collections.Counter(); eqgone = []
for n in envd.get('type_changed_thm', []):
    mm = re.match(r'^(?:TLC\.)?(admininstr_instr|instr_of|ai_principal_typing)\.eq_\d+$', n)
    if mm: eqfam[mm.group(1)] += 1
for n in envd['only_old']:
    mm = re.match(r'^(?:TLC\.)?(admininstr_instr|instr_of|ai_principal_typing)\.eq_(\d+)$', n)
    if mm: eqgone.append((mm.group(1), int(mm.group(2))))
narms = {'admininstr_instr': None, 'instr_of': None, 'ai_principal_typing': None}
# warnings and builds
def parse_log(p):
    t = open(p).read(); t = re.sub(r'\n?(Command exited with non-zero status \d+\n?)?WALL [^\n]*\n?$', '', t.rstrip())
    blocks = re.split(r'\n(?=\S+\.lean:\d+:\d+: )', t); out = []
    for b in blocks:
        mm = re.match(r'\S+\.lean:(\d+):\d+: (error|warning)[^:]*: (.*)', b, re.S)
        if mm: out.append((int(mm.group(1)), mm.group(2), mm.group(3).strip()))
    return out
def wcat(msg):
    if 'is not explicitly referenced' in msg: return 'unused variable'
    if 'does not follow the mathlib naming' in msg: return 'naming lint'
    return 'other lint'
W = {}; SW = {}
for st, d in [('old', 'old/logs'), ('new', 'final/logs')]:
    for m in MODS:
        ms = parse_log(f'{B}/{d}/{m}.log')
        W[(st, m)] = sorted(x[2] for x in ms if x[1] == 'warning')
        SW[(st, m)] = len(re.findall(r"declaration uses ['`]sorry['`]", open(f'{B}/{d}/{m}.log').read()))
nwarn = sum(len(W[('new', m)]) for m in MODS); assert all(W[('old', m)] == W[('new', m)] for m in MODS)
wc = collections.Counter(wcat(x) for m in MODS for x in W[('new', m)])
def chain(p):
    d = {}
    for l in open(p):
        mm = re.match(r'(\w+) (\S+) rc=(\d+) errors=(\d+) warnings=(\d+) sorry-warnings=(\d+) olean=(\w+) WALL ([\d.]+) s  MAXRSS (\d+) KB', l)
        if mm: d[mm.group(2)] = mm.groups()
    return d
co, cn = chain(f'{B}/logs/chain_old.txt'), chain(f'{B}/logs/chain_final_from_repo.txt')
cs = chain(f'{B}/logs/chain_new_unrepaired.txt'); cs.update(chain(f'{B}/logs/chain_new_repaired_1.txt'))
peak = max(int(x[8]) for c in (co, cn, cs) for x in c.values())
# errors of unrepaired modules
first = parse_log(f'{B}/new/logs_unrepaired/TypingLemmas.log'); first_err = [x for x in first if x[1] == 'error']
TLold = rd('old', 'TypingLemmas'); TLcons = constructs(TLold)
from toplevel32 import owner as owner_of
rfl_lines = collections.Counter(x[0] for x in first_err if x[2].startswith('Tactic `rfl` failed'))
rfl_line, rfl_n = rfl_lines.most_common(1)[0]; rfl_owner = owner_of(TLcons, rfl_line)['name']
sorry_decl = [x for x in first if x[1] == 'warning' and 'declaration uses' in x[2] and 'sorry' in x[2]]
sorry_owners = sorted({owner_of(TLcons, x[0])['name'] for x in sorry_decl})
errs = collections.defaultdict(list)
for m in REPAIRED:
    for p in [f'{B}/unrep/logs/{m}.log'] + ([f'{B}/unrep/logs/TypePreservationPure_only1072fixed.log'] if m == 'TypePreservationPure' else []):
        for (l, k, msg) in parse_log(p):
            if k == 'error':
                ls = msg.split('\n'); first = ls[0].strip()
                if first in ('Type mismatch', 'Application type mismatch: The argument'):
                    keep = [first]
                    for x in ls[1:]:
                        if not x.strip(): break
                        keep.append(x.strip())
                    msg = ' '.join(keep)
                else: msg = first
                errs[(m, l)].append(msg if len(msg) <= 260 else msg[:257] + '…')
# §8 facts
TLn = rd('final', 'TypingLemmas')
def find(pat):
    hits = [i + 1 for i, l in enumerate(TLn) if pat in l]; assert len(hits) == 1, (pat, hits); return hits[0]
stale = [(find('check on the 68-case'), '"the 68-case transcription"'), (find("each of `instr`'s 68"), "\"each of `instr`'s 68 constructors\""),
         (find('68×68 cases, mechanical'), '"68×68 cases, mechanical"'), (find('the 68×68 case bash'), '"the 68×68 case bash"'),
         (find('in the other 68'), '"in the other 68"')]
rocq68 = find('Rocq destructs both instructions (68×68)'); tilde74 = find('~74 cases uniformly'); all73 = find('confirmed by reading all 73 cases')
sorry_lines = []
for m in MODS:
    L = rd('final', m); C = code_mask(L)
    for i, (l, c) in enumerate(zip(L, C)):
        if re.search(r'\bsorry\b', l): sorry_lines.append((m, i + 1, bool(re.search(r'\bsorry\b', c)), l.strip()))
assert not any(x[2] for x in sorry_lines)
old_sorry_model = [i + 1 for i, l in enumerate(MO) if re.search(r'\bsorry\b', l)]
# trial port
tp = '/home/zhengyew/spectec/spectec/src/temp_port_reference/trial_port'
tp_same = all(md5(f'{tp}/{m}.lean') == md5(f'{B}/final/src/{m}.lean') for m in MODS)
# repo-directory facts
st = subprocess.run(['git', '-C', '/home/zhengyew/spectec', 'status', '--porcelain', '--ignore-submodules=all', '--', 'spectec/src/test-lean-claude'],
                    capture_output=True, text=True, env=dict(os.environ, GIT_OPTIONAL_LOCKS='0')).stdout.split('\n')
st = [l for l in st if l and 'claude-logging' not in l]
ctl = open(f'{B}/ctl/audit_ctl.txt').read()
ctl_checked = int(re.search(r'theorems checked: (\d+)', ctl).group(1)); ctl_fail = int(re.search(r'theorems needing a default value: (\d+)', ctl).group(1))
ctl_names = re.findall(r'^--- (\S+)$', ctl, re.M); assert ctl_checked == UN[1] + 3 and sorted(ctl_names) == ['audit_ctl_model', 'audit_ctl_nat']
xc = open(f'{B}/work/trial_port_crosscheck.txt').read()
assert '73/73; mine left unmatched: 0' in xc and xc.count('same set True') == 4 and 'equal after translating the 4 removed-case markers to the last case names: True' in xc and 'only in NEW: mine 12, trial port 12; equal: True' in xc
gen_sorry = sum(1 for l in open('/home/zhengyew/spectec/spectec/test-lean/todaywasm2.0.lean') if re.match(r'^\s*sorry\s*$', l))
commented = [i + 1 for i, l in enumerate(MN) if re.match(r'^--\s+sorry\s*$', l)]
docs_dir = '/home/zhengyew/spectec/spectec/src/test-lean-claude/claude-logging'
living = [f'{docs_dir}/README.md'] + [f'{docs_dir}/{d}/{f}' for d in ('for-claude', 'for-humans') for f in sorted(os.listdir(f'{docs_dir}/{d}')) if f.endswith('.md')]
pat_old = re.compile(r'\b(admin)?instr_case_(19|[2-7][0-9])\b|\binstr\.EXTEND\b|\badmininstr\.EXTEND\b')
living_hits = sum(1 for f in living for l in open(f) if pat_old.search(l))
hist_files = 0
for root, _, files in os.walk(docs_dir):
    if '/bundle33' in root or root.endswith('bundle33'): continue
    if not (root.startswith(f'{docs_dir}/verbatim_dialogue_log') or root.startswith(f'{docs_dir}/safety-checks')): continue
    for f in files:
        try:
            if any(re.search(r'\b(admin)?instr_case_(19|[2-7][0-9])\b', l) for l in open(os.path.join(root, f), errors='ignore')): hist_files += 1
        except IsADirectoryError: pass
# ---- v3 facts
import unicodedata
cmap = {k: cm[k] for k in ('wf_instr', 'wf_admininstr')}
def fam_stem(n): return re.sub(r'\d+$', '', n) if re.search(r'\d$', n) else None
def fam_count(D, st): return sum(1 for x in D if re.sub(r'\d+$', '', x) == st and re.search(r'\d$', x))
rm_ext, rm_end, rm_ren = [], [], []
for n in envd['only_old']:
    if 'EXTEND' in n: rm_ext.append(n); continue
    fst = fam_stem(n); assert fst, n
    (rm_end if fam_count(DN, fst) < fam_count(DO, fst) else rm_ren).append(n)
assert len(rm_ren) == len(envd['only_new']) and all(fam_count(DN, fam_stem(n)) == fam_count(DO, fam_stem(n)) for n in envd['only_new'])
end_fams = collections.OrderedDict()
for n in sorted(rm_end):
    fst = fam_stem(n); end_fams[fst] = (fam_count(DO, fst), fam_count(DN, fst))
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
v_not_t = sorted(n for n in envd.get('value_changed_thm', []) if n not in tchg and n not in set(envc['value_changed_thm']['user_level']))
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
lake_w = len(re.findall(r'"level": ?"warning"', open('/home/zhengyew/spectec/spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace').read()))
fz = subprocess.run(['git', '-C', '/home/zhengyew/spectec', 'log', '--format=%h', '-1', '--', 'specification/wasm-2.0/C-hints.spectec'], capture_output=True, text=True, env=dict(os.environ, GIT_OPTIONAL_LOCKS='0')).stdout.strip()
orig_same = all(MO[a - 1:a + 4] == MN[b - 1:b + 4] for a, b in [(old_sorry_model[0] - 4, commented[0] - 4), (old_sorry_model[1] - 4, commented[1] - 4)])
info_lines = len(open(f'{B}/final/logs/TypeProgress.log').read().split('\nTypeProgress.lean:')[0].split('\n'))
chk = [(m, i + 1) for m in MODS for i, l in enumerate(rd('final', m)) if l.strip().startswith('#check')]
audit_inst = re.search(r'module Inhabited instances made opaque: (\d+); external instances made opaque: \[(.*?)\]', open(f'{B}/probes/audit_new.txt').read())
n_inst_mod, n_inst_ext = int(audit_inst.group(1)), len(audit_inst.group(2).split(', '))
recs_rules = [c['name'] for c in im_rec if re.search(r'rules=(\d+)', c['old']).group(1) != re.search(r'rules=(\d+)', c['new']).group(1)]
recs_norules = [c['name'] for c in im_rec if c['name'] not in recs_rules]
cases_in = {}
for e in edits:
    if e['kind'] == 'rename':
        cons_list = constructs(rd('final', e['module'])); o = [c for c in cons_list if c['name'] == e['owner']][0]
        cases_in[e['owner']] = 'cases' in '\n'.join(rd('final', e['module'])[o['line'] - 1:o['end']])
for c in sorted({r['construct'] for r in rows if r['cat'] == 'ctor-renumber/hand-layer'}):
    cons_list = constructs(MN); o = [x for x in cons_list if x['name'] == c][0]; cases_in[c] = 'cases' in '\n'.join(MN[o['line'] - 1:o['end']])
vnt_ref = {n: CA['examples'].get(n) for n in v_not_t}
CF = {}
for l in open(f'{B}/probes/cause_new.tsv'):
    f = l.rstrip('\n').split('\t')
    if len(f) == 4: CF[f[1]] = (int(f[2]), f[3])
RESOLUTIONS = [
 ('V1-1', 'The equation lemmas named as removed were misidentified', '§5 Removed now separates the last lemmas of shrinking families (`eq_68`, `eq_74`, `eq_56`) from the renumbered lemmas from each deleted arm onward, whose types changed.'),
 ('V1-2', '§0 axiom claim unqualified', '§0 and §5 say "every user-level theorem", and §5 names the 4 numbered auxiliaries that differ.'),
 ('V1-3', '§0 statement claim unqualified', '§0 says "user-level" and reports changed terms separately.'),
 ('V1-4, FIX-2', 'Category list of the type changes incomplete, then 4 helpers mislabelled', 'The lists are generated from all categories. The 4 `match_on_same_ctor` helpers present in both builds have their own label.'),
 ('V1-5, FIX-3, CRITIC-11', '"Families shrink by one" imprecise', '§5 Removed splits the 43 into 16 for the removed instruction, 15 ends of shrinking families (each with its size OLD → NEW) and 12 renumbered names.'),
 ('V1-6, FIX-1, FRESH-6, CRITIC-11', '"Every number is computed" overstated', 'The header now says which parts are computed and which are hand-written. §2\'s match counts are read from the constructor map.'),
 ('V1-7', '`chain33.sh` counted `sorry` warnings with the wrong quotes', 'The tool is fixed. §7 recounts from the logs, and §9 documents the defect.'),
 ('V1-8, FRESH-8', 'Construct counts unlabelled, and their definition', '§6 labels each file\'s count, defines what is counted, and gives the declaration-only count.'),
 ('V1-9', 'Line 197 should be 196', 'The line numbers in §8 are computed from the NEW files.'),
 ('V1-10', '"~74 cases" comment', 'Listed in §8 as describing Rocq.'),
 ('V1-11', '"four kinds" for three', 'Now "three kinds".'),
 ('V1-12', 'Shell output inside an error cell', 'The `/usr/bin/time` lines are stripped.'),
 ('V1-13', 'Wrong footnote on the error column', 'Rewritten as "How to read the error column".'),
 ('V1-14', '`TypePreservation:2024` is not a status note', 'It is now described as a docstring about `Step_read_is_wf`\'s history.'),
 ('V1-15', '`TLC.` dropped from private names', 'Only a leading `TLC.` is omitted.'),
 ('V1-16, CRITIC-10', 'Lake rebuild scope; no Lake build of either state', '§8 says "at least `wasm2.0` and the seven modules that import it". §7 says neither state has a Lake build, and why the bare-`lean` builds should match.'),
 ('V1-17', 'Audit module set unnamed', '§5 names the excluded module and the instances made opaque.'),
 ('FIX-4', '"its 17 points are fixed" overstated', '§9 rewritten, and this appendix added.'),
 ('FIX-5', 'Only the TypingLemmas rows come from the second compile', 'Corrected in §4.2.'),
 ('FIX-6, FRESH-1, FRESH-3, CRITIC-7', 'Documentation claim false; historical logs not in `safety-checks/`', '§8 lists the `digest_wasm_v.md` lines, which describe Rocq\'s `wasm.v`, and counts the historical files per bundle (0 in `safety-checks/`).'),
 ('FIX-7, FRESH-5', 'Control module "never in the repo"; files in the wrong list', 'Reworded, and §9 lists `AuditCtl33.lean` and `RunAuditCtl33.lean` under `tools/`.'),
 ('FIX-8, FRESH-10', '"67 of 67" counts NEW cases', 'Reworded: every OLD case except case 19 matched.'),
 ('FRESH-2', 'The merge\'s `$fzero` hint removal is not mentioned', '§0 and §2 name commit `5d6980fef` and say why it does not contribute.'),
 ('FRESH-4, CRITIC-6', 'Re-stated theorems: three changes, witness not cited, file not named', '§8 lists the three changes, names the generator output and its md5, cites the bundle 23/29 witness, says it was not re-run on NEW, and notes the trial port\'s outdated caveat.'),
 ('FRESH-7, CRITIC-14', 'Memory peak; warning kinds; info output; audit wording', '§7 gives compile and probe peaks, every warning kind and the info output, and states that the logs are identical. §5 states exactly which instances the audit makes opaque.'),
 ('FRESH-9', 'Cross-check matched by prefix', '§8 says so.'),
 ('CRITIC-1', 'The 15 proof-module lines not shown as text', 'Appendix C gives all 17 lines in full.'),
 ('CRITIC-2', 'Statement check is name-level; inductive contents not compared', '§0 explains why name-level equality is enough here, and §5 adds the inductive-metadata comparison.'),
 ('CRITIC-3', 'No per-module or per-kind totals', 'Tables added in §5, and the 3 generated theorems that changed value but not type are listed.'),
 ('CRITIC-4', 'Hash method under-described; constructor-index shift not stated', '§5 Method gives the hash width and what it ignores. The metadata comparison shows the index shift and what it explains.'),
 ('CRITIC-5', 'Cause of the changed terms asserted, not checked', 'The cause probe in §5: 120 of 120 changed user-level declarations refer to a changed declaration, and none of the unchanged ones do. §5 also explains which edited theorems keep their terms.'),
 ('CRITIC-8', 'No byte-level facts', '§1 "Bytes" and Appendix D.'),
 ('CRITIC-9', 'Comments citing model line numbers', 'Table in §8.'),
 ('CRITIC-12', 'HEAD contents of the two non-module files', 'The header gives their lines and md5.'),
 ('CRITIC-13', 'Appendix A lacks instructions and evidence of necessity', 'Instruction column, plus the bundle32 compile column.'),
]
# ------------------------------------------------------------------ text
L = []; w = L.append
cat = collections.Counter((r['file'] == 'wasm2.0', r['cat']) for r in rows)
n_rows = len(rows); n_model = sum(1 for r in rows if r['file'] == 'wasm2.0'); n_down = n_rows - n_model
n_del = cat[(True, 'EXTEND-removed')] + cat[(False, 'EXTEND-removed')]
n_gen, n_hand, n_proof = cat[(True, 'ctor-renumber/generated')], cat[(True, 'ctor-renumber/hand-layer')], cat[(False, 'ctor-renumber/proof-module')]
n_loc = cat[(True, 'source-location')]
assert n_del + n_gen + n_hand + n_proof + n_loc == n_rows and not any(r['cat'] == 'UNEXPLAINED' for r in rows)
w('# Old vs new: the `EXTEND` removal across the model and the proof\n')
w('Bundle 33, 2026-11-11. This report compares two complete states of `spectec/src/test-lean-claude/`.\n')
w('- **OLD:** the old proof together with `OLD_wasm2.0.lean`, the model that still has `EXTEND`. This is HEAD `afb06bf8d`, whose `wasm2.0.lean` is byte-identical to `OLD_wasm2.0.lean`.')
w('- **NEW:** the new proof together with `wasm2.0.lean`, i.e. the files now in the working tree. The model is the bundle32 port, and the proof modules are as repaired this turn.\n')
w('| module | OLD md5 | NEW md5 | lines OLD → NEW | top-level constructs |')
w('|---|---|---|---|---|')
for m in MODS:
    a, b = md5(f'{B}/old/src/{m}.lean'), md5(f'{B}/final/src/{m}.lean'); s = summ[m]
    w(f'| `{m}.lean` | `{a[:8]}…` | `{b[:8]}…`{" (same)" if a == b else ""} | {fmt(s["old_lines"])} → {fmt(s["new_lines"])} | {cons[m]} |')
w('\nThese nine files are the modules that `lakefile.lean` builds. In OLD the model file is `OLD_wasm2.0.lean`; in NEW it is `wasm2.0.lean`.')
w('- **What is computed.** Every table, and every count and list derived from the data, is computed by `report33.py` (§9) from the files, the build logs and the Lean outputs. The explanations are mine, as are a few fixed references inside them: spec positions, tool versions, and line numbers quoted in an explanation. Two rounds of independent readers checked them against the files (§9, Appendix E).')
w('- **The whole directory.** `git status` for the directory, not counting `claude-logging/`, lists: ' + ', '.join(f'`{l[3:].split("/")[-1]}` ({ {"M": "modified", "D": "deleted"}.get(l[:2].strip(), l[:2].strip()) })' for l in st) + '.')
w('  - `wasm2.0.lean` and the four repaired modules are the subject of this report.')
w(f'  - The other two are outside both builds, since the lakefile does not build them. You changed both before bundle32:')
w(f'    - At HEAD, `OLD_wasm2.0.lean` held an older model ({fmt(head_old[1])} lines, md5 `{head_old[0][:8]}…`). It now holds HEAD\'s `wasm2.0.lean` ({fmt(wt_old_lines)} lines, md5 `{wt_old_md5[:8]}…`).')
w(f'    - `wasm2.0_prevattempt.lean` ({fmt(head_prev[1])} lines, md5 `{head_prev[0][:8]}…` at HEAD) was deleted.')
w('  - `lakefile.lean`, `lake-manifest.json` and `lean-toolchain` are unchanged.\n')
# 0
w('## 0. Bottom line\n')
w(f'- **One cause.** The mech-backend merge deleted one line of the Wasm 2.0 spec: the dead instruction `EXTEND numtype n`. Every difference below follows from that. (The merge also removed a `$fzero` hint, but OLD\'s model had already been generated without it; see §2.)')
w(f'- **Text.** {n_rows} lines of OLD differ from NEW: {n_model} in the model and {n_down} in the proof modules. Each falls into one of three kinds, and none is unexplained:')
w(f'  - **{n_del} lines deleted**, because they mention the removed constructor: {cat[(True, "EXTEND-removed")]} in the model and {cat[(False, "EXTEND-removed")]} match arms in `TypingLemmas`.')
w(f'  - **{n_gen + n_hand + n_proof} lines renumber a well-formedness constructor name**, `instr_case_K`/`admininstr_case_K` → K−1 for K ≥ 20:')
w(f'    - {n_gen} in the generated model;')
w(f'    - {n_hand} in the model\'s proofs (the bundle32 port);')
w(f'    - {n_proof} in the proof modules.')
w(f'  - **{n_loc} generated comments** cite a spec position that moved up one line.')
w(f'- **Structure.** No top-level construct was added, removed, renamed or reordered in any of the nine files.')
w(f'  - All {fmt(n_cons)} constructs match OLD one for one.')
w(f'  - {len(pc)} have changed text: {len(code_changed)} in code, and {len(loc_only)} only in their source-position comment.')
w(f'- **Statements.** No user-level theorem, definition, inductive type or constructor changed its statement. This is checked in Lean, over the {fmt(common)} declarations common to both builds, with constructor numbers mapped (§5).')
w('  - The constructor `EXTEND` itself is gone, from `instr` and `admininstr`, together with its two well-formedness cases.')
w('  - **Unchanged statements, smaller types.** The check compares statements by name. Statements that mention `instr` or `admininstr` keep their text, but now range over types with one constructor fewer. That is the intended effect, and it changes nothing of substance: no typing rule ever mentioned `EXTEND` (§2), so no configuration satisfying the main theorems\' typing hypotheses could contain it, even in OLD.')
w('  - Every other declaration whose type changed is one Lean generates automatically.')
w(f'  - **Changed terms.** Terms changed in {len(envc["value_changed_def"]["user_level"])} user-level definitions and {len(envc["value_changed_thm"]["user_level"])} user-level theorems. For user-level declarations, these are exactly the ones whose terms refer to an eliminator or equation lemma that changed (§5).')
w(f'- **Soundness.** Both states compile with 0 errors and 0 `sorry`, and no theorem depends on `sorryAx`.')
w(f'  - Every user-level theorem present in both has the same axioms. The only {len(axch)} differences are numbered auxiliary sub-proofs whose numbers shifted.')
w(f'  - `t_preservation` has {len(AN["t_preservation"])} axioms and `t_progress` {len(AN["t_progress"])}, the same lists as in OLD.')
w(f'  - The `Inhabited`-default audit finds no theorem needing a default: {UO[2]} of {fmt(UO[1])} in OLD and {UN[2]} of {fmt(UN[1])} in NEW.')
w(f'  - The build logs are identical once line numbers and timings are stripped: the same {nwarn} warnings and the same info output.\n')
# 1
w('## 1. Line-level summary\n')
w('| file | lines OLD → NEW | deleted (`EXTEND`) | constructor renumbered | spec position comment | total OLD lines differing |')
w('|---|---|---|---|---|---|')
for m in MODS:
    s = summ[m]; dl = s.get('EXTEND-removed', 0); rn = sum(v for k, v in s.items() if k.startswith('ctor-renumber')); sl = s.get('source-location', 0)
    extra = f' ({s.get("ctor-renumber/generated", 0)} generated + {s.get("ctor-renumber/hand-layer", 0)} in proofs)' if m == 'wasm2.0' else ''
    w(f'| `{m}.lean` | {fmt(s["old_lines"])} → {fmt(s["new_lines"])} | {dl} | {rn}{extra} | {sl} | {dl + rn + sl} |')
w(f'| **total** | | {n_del} | {n_gen + n_hand + n_proof} | {n_loc} | **{n_rows}** |')
w('\n**How the lines were matched:**')
w('- From each OLD file, delete the lines that mention the removed constructor (§3.1, §4.1).')
w('- The remaining lines align one for one with the NEW file, which has exactly the same length.')
w('- Each differing pair is classified by the rule that maps it, so no line-matching heuristic is involved.')
w('- 0 pairs are left unexplained.')
w('- Four modules are byte-identical: ' + ', '.join(f'`{m}`' for m in MODS if md5(f'{B}/old/src/{m}.lean') == md5(f'{B}/final/src/{m}.lean')) + '.')
w(f'- **Bytes.** All {len(BF)} files (9 OLD, 9 NEW) are valid UTF-8 with LF line endings, no byte-order mark and exactly one final newline. Their trailing whitespace and tabs are {"the same in OLD and NEW" if tw_same else "NOT the same"}. Sizes and full md5 sums are in Appendix D.\n')
# 2
w('## 2. The cause\n')
w(f'**The spec line.** mech-backend commit `28073cddd` ("{subj}") deleted line {spec_line} of `specification/wasm-2.0/1-syntax.spectec`, in the numeric-instruction fragment (`{frag.split(" = ")[0]}`):')
w(f'```\n{spec_text}\n```')
w(f'**No other change matters.** The merge also brought in mech-backend\'s removal of `def $fzero hint(wfopt)` from `C-hints.spectec` (commit `{fz}`). OLD\'s generated base had already been produced without that hint (bundle29).')
w('- In bundle32 the HEAD generator was run on the HEAD spec with only the `EXTEND` line restored, and it reproduced OLD\'s generated base byte for byte (`bundle32/evidence/outputs/generator_check.txt`).')
w('- So neither that hint nor the merge\'s generator changes affect the Wasm 2.0 Lean output. Those changes are:')
w('  - the ImproveIds name-clash fix;')
w('  - the Sideconditions let-reordering;')
w('  - DefToRel\'s `hint(axiom)`.\n')
w('**What the instruction was.** In Wasm 2.0 terms, `instr.EXTEND numtype n` was a dead production. In OLD:')
w(f'- it is mentioned only on the {len(extend_mentions_old)} generated lines of §3.1 and in two match arms in `TypingLemmas`;')
w(f'- no validation rule mentions it, and `Instr_ok` has {rc["Instr_ok"][0]} rules in both versions;')
w(f'- no reduction rule mentions it, and `Step_pure`, `Step_read` and `Step` have {rc["Step_pure"][0]}, {rc["Step_read"][0]} and {rc["Step"][0]} rules in both versions.\n')
w('**The real extension instructions are unchanged.** They live under other constructors:')
w('- `i32.extend8_s` and its siblings are `UNOP` with `unop_Inn.EXTEND n`;')
w('- `i64.extend_i32_s/u` is `CVTOP` with `cvtop__Inn_1_Inn_2.EXTEND sx`;')
w('- the SIMD extensions are `VCVTOP` with `vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND half sx`.\n')
w('**Why so many names moved.** The backend names the constructors of the well-formedness predicates by position: constructor K (from 0) of `wf_instr` is `instr_case_K`, and likewise `admininstr_case_K` for `wf_admininstr`.')
w(f'- `EXTEND` was constructor 19 of both `instr` and `admininstr` ({rc["instr"][0]} → {rc["instr"][1]} and {rc["admininstr"][0]} → {rc["admininstr"][1]} constructors).')
w(f'- So every later case moved down by one: `wf_instr` goes from {rc["wf_instr"][0]} to {rc["wf_instr"][1]} cases, and `wf_admininstr` from {rc["wf_admininstr"][0]} to {rc["wf_admininstr"][1]}.')
w('- The two predicates number their cases alike for K ≤ 67. In OLD, cases 68–73 of `wf_admininstr` are the six administrative-only instructions.\n')
mi = {k: sum(1 for v in cmap[k]['map'].values() if isinstance(v, str)) for k in cmap}
assert all(cmap[k]['unmatched_old'] == [f'{"instr" if k == "wf_instr" else "admininstr"}_case_19'] and not cmap[k]['ambiguous'] and not cmap[k]['unmatched_new'] for k in cmap)
w(f'The renaming was done by meaning, not by arithmetic. Every OLD case except the removed case 19 matched exactly one NEW case with identical text: arguments, premises and conclusion. That gives {mi["wf_instr"]} matches in `wf_instr` and {mi["wf_admininstr"]} in `wf_admininstr`. Case 19 has no counterpart, no NEW case is left over, and no match is ambiguous.\n')
# 3
w(f'## 3. The model: `OLD_wasm2.0.lean` → `wasm2.0.lean` ({n_model} lines)\n')
w('### 3.1 Deleted: the five lines that mention `EXTEND`\n')
w('| OLD line | construct | deleted line |'); w('|---|---|---|')
for r in rows:
    if r['file'] == 'wasm2.0' and r['cat'] == 'EXTEND-removed': w(f'| {r["old"]} | `{r["kind"]} {r["construct"]}` | {code(esc(r["before"]))} |')
assert [r['old'] for r in rows if r['file'] == 'wasm2.0' and r['cat'] == 'EXTEND-removed'] == [x[0] for x in extend_mentions_old]
w('')
w(f'### 3.2 Renumbered constructor declarations in the generated model ({n_gen} lines)\n')
w('Each of these lines declares one case of `wf_instr` or `wf_admininstr`. Only the name changed; the rest of the declaration is identical. The full map, with the instruction each case is about:\n')
w('| OLD → NEW | instruction | `wf_instr` line OLD → NEW | `wf_admininstr` line OLD → NEW |'); w('|---|---|---|---|')
gen = {}
for r in rows:
    if r['cat'] == 'ctor-renumber/generated':
        mm = re.match(r'\s*\| ((?:admin)?instr_case)_(\d+)', r['before']); gen[(mm.group(1), int(mm.group(2)))] = (r['old'], r['new'])
w('| `*_case_0` … `*_case_18` | (unchanged) | 19 cases, same names | 19 cases, same names |')
d19 = {k: r['old'] for r in rows if r['cat'] == 'EXTEND-removed' and r['file'] == 'wasm2.0' for k in (['wf_instr'] if 'wf_instr (' in r['before'] else ['wf_admininstr'] if 'wf_admininstr (' in r['before'] else [])}
w(f'| `*_case_19` | **`EXTEND`, deleted** (§3.1) | {d19["wf_instr"]} → — | {d19["wf_admininstr"]} → — |')
for k in range(20, rc['wf_admininstr'][0]):
    a = gen.get(('instr_case', k)); b = gen.get(('admininstr_case', k))
    w(f'| `_case_{k}` → `_case_{k - 1}` | `{meaning[f"admininstr_case_{k}"]}` | {f"{a[0]} → {a[1]}" if a else "—"} | {f"{b[0]} → {b[1]}" if b else "—"} |')
ni, na = sum(1 for k in gen if k[0] == 'instr_case'), sum(1 for k in gen if k[0] == 'admininstr_case')
w(f'\nThat is {ni} `wf_instr` lines and {na} `wf_admininstr` lines, {ni + na} in all. No other generated line refers to these cases.\n')
w(f'### 3.3 Source-position comments ({n_loc} lines)\n')
w(f'The generator heads some constructs with a comment giving the spec position they come from. Every `1-syntax.spectec:L.c` with L > {spec_line} now reads L−1, because the line above it was deleted. The {n_loc} affected comments head these constructs (OLD → NEW line):\n')
locs = [r for r in rows if r['cat'] == 'source-location']
w(', '.join(f'`{r["construct"]}` ({r["old"]}→{r["new"]})' for r in locs) + '.\n')
w(f'Example, `{locs[0]["construct"]}`: {code(locs[0]["before"])} → {code(locs[0]["after"])}.\n')
w(f'### 3.4 The model\'s proofs: renumbered references ({n_hand} lines)\n')
w('These are the deviations of the bundle32 port. Every one renames a `wf_admininstr` case inside a proof body; no statement changed. They are logged line by line in `bundle32/user_requested_documents/deviations_in_copying.md`, and listed again in Appendix A.\n')
w('| construct | lines | renamings (OLD → NEW, instruction × lines) |'); w('|---|---|---|')
agg = collections.OrderedDict()
for r in rows:
    if r['cat'] != 'ctor-renumber/hand-layer': continue
    for fam, k in re.findall(r'\b((?:admin)?instr_case)_(\d+)\b', r['before']):
        if int(k) >= 20: agg.setdefault(r['construct'], collections.Counter())[(int(k), meaning[f'admininstr_case_{k}'])] += 1
for c, v in agg.items(): w(f'| `{c}` | {sum(v.values())} | ' + ', '.join(f'{k}→{k - 1} `{mn}` ×{n}' for (k, mn), n in sorted(v.items())) + ' |')
w('')
# 4
w(f'## 4. The proof modules ({n_down} lines)\n')
w('**What the error column shows.** It is what Lean reports for the OLD line when compiled against the NEW model. Each module was compiled with the earlier modules already repaired.\n')
w('### 4.1 Deleted: two match arms on the removed constructor\n')
w('| module | OLD line | construct | deleted line | why |'); w('|---|---|---|---|---|')
why = {'instr_of': f'`instr_of : admininstr → Option instr` is the partial inverse of `admininstr_instr` (Rocq `typing_lemmas.v:124`). It has one arm per `admininstr` constructor ({rc["admininstr"][0]} in OLD, {rc["admininstr"][1]} in NEW), and the `EXTEND` arm no longer type-checks.',
       'ai_principal_typing': '`ai_principal_typing` gives the principal type of an administrative instruction. Its `EXTEND` arm said `False`, and with the constructor gone the arm is an invalid pattern. Deleting a `False` arm in front of the final `| _ => True` would normally make that case `True`, but here the case no longer exists, so no other arm changes meaning.'}
for e in edits:
    if e['kind'] == 'delete':
        msg = [x[2] for x in first_err if x[0] == e['line']][0]
        w(f'| `{e["module"]}` | {e["line"]} | `def {e["owner"]}` | {code(esc(e["before"]))} | {why[e["owner"]]} Lean: "{esc(re.sub(chr(10), " ", msg))}" |')
w('')
w(f'### 4.2 Renumbered constructor references ({n_proof} lines)\n')
ctx = {
 'instr_typing_inversion': 'Inverts `Instr_ok` into the principal type. Its `vconst` case destructs `wf_instr (VCONST …)`.',
 'construct_ai_val': 'Types a value as an administrative instruction. The vector case builds `wf_instr (VCONST V128 c)`.',
 'construct_ais_trap': '`TRAP` has every type. The proof needs `wf_admininstr TRAP`.',
 'Step_pure__local_tee_preserves': 'Preservation for `local.tee x` ↪ `val val local.set x`. It destructs `wf_admininstr (LOCAL_TEE x)` and builds `wf_instr (LOCAL_SET x)`.',
 'wf_vconst_parts': 'Destructs `wf_admininstr (VCONST vt c)` into its two premises.',
 't_read_preservation': 'Preservation of `Step_read`, `call_addr` case: a function call becomes `FRAME_ n f [LABEL_ n [] body]`. It destructs the well-formedness of that `FRAME_` to reach the `LABEL_` inside.',
 'wf_forall_admin_val': 'Values are well formed iff their `admininstr` images are: `VCONST`, `REF_NULL`, `REF_FUNC_ADDR`, `REF_HOST_ADDR`.',
 'wf_config_label': 'Rocq `type_progress.v:857`. It destructs `wf_admininstr (LABEL_ n bes es)`.',
 'wf_config_frame': 'Rocq `type_progress.v:870`. It destructs `wf_admininstr (FRAME_ n f es)`.',
 't_progress_e_Instr_ok2_frame': 'Progress, frame case. The body is well formed under the inner frame, by destructing `wf_admininstr (FRAME_ …)`.'}
w('The full OLD and NEW text of all 17 changed lines is in Appendix C.\n')
w('| module | line OLD → NEW | construct | change | instruction | role of the line | error without the change |'); w('|---|---|---|---|---|---|---|')
shift = lambda m, l: l - sum(1 for e in edits if e['kind'] == 'delete' and e['module'] == m and e['line'] < l)
for e in edits:
    if e['kind'] != 'rename': continue
    nl = shift(e['module'], e['line']); names = {x for o, n, _ in e['renames'] for x in (o, n)}
    newn = {n for o, n, _ in e['renames']}
    er = list(errs.get((e['module'], nl), [])) + [x for x in errs.get((e['module'], nl - 1), []) if 'has not been provided' in x and any(f'`{nm}`' in x for nm in newn)]
    ch = '; '.join(f'`{o}` → `{n}`' for o, n, _ in e['renames']); ins = ', '.join(sorted({mn for _, _, mn in e['renames']}))
    w(f'| `{e["module"]}` | {e["line"]} → {nl} | `{e["owner"]}` | {ch} | `{ins}` | {ctx[e["owner"]]} | {esc(" / ".join(dict.fromkeys(er)))} |')
w('\n**How to read the error column.**')
w('- "Alternative … has not been provided" is reported at the `cases … with` line, which for some rows is the line above the edit. It is listed in the row of the edit it belongs to.')
w('- The error for `TypePreservationPure` line 1085 appears only once line 1072 is fixed, because it sits inside that alternative.\n')
w(f'**The first compile hid line 570.** In that compile of the unrepaired `TypingLemmas`, the two invalid patterns of §4.1 made `instr_of` and `ai_principal_typing` fail.')
w(f'- That cascaded into {len(first_err)} errors, including {rfl_n} `rfl` failures at line {rfl_line} (`{rfl_owner}`).')
w(f'- It also turned ' + ', '.join(f'`{x}`' for x in sorry_owners) + ' into `sorry` declarations, which hid the error at line 570.')
w('- So the table\'s three `TypingLemmas` rows come from a second compile of that module, with only the two arms of §4.1 deleted. Their line numbers are the NEW ones.')
w('- The other twelve rows come from compiling each unrepaired module against the repaired earlier ones.\n')
w('**Nothing else needs changing.** No other code line in the four modules mentions a renumbered or removed constructor. The other two `EXTEND` tokens in `TypeProgress`, at lines 3496 and 3705, are the SIMD conversion `vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND`, which still exists.\n')
# 5
w('## 5. Lean-level comparison (elaborated declarations)\n')
w('**Method.** Both builds were loaded in Lean, and every declaration of the nine modules was dumped with:')
w('- a 32-bit structural hash of its type: Lean\'s `Expr.hash`, which ignores binder names, binder annotations and metadata;')
w('- the same hash of its value;')
w('- for theorems, its axioms.\n')
w('Equal hashes are strong evidence that two terms are equal, not proof: a change would be missed only through a 32-bit hash collision.')
w('- **Inductive metadata** is not covered by the hashes, so it was compared separately (below).')
w('- **Environment extensions** were not compared at this level: attributes, simp sets, instances, reducibility and docstrings. All of them are written in the source, and the line accounting (§1) shows that no such line changed.\n')
w('In the OLD dump, the cases `wf_instr.instr_case_K` and `wf_admininstr.admininstr_case_K` with K ≥ 20 were first renamed to K−1. So were the same cases of their auxiliary `.below` inductives, and the removed case was marked. The comparison is therefore by meaning.\n')
w(f'**Totals.** OLD has {fmt(n_old)} declarations ({fmt(t_old)} theorems), and NEW has {fmt(n_new)} ({fmt(t_new)} theorems). {fmt(common)} are common to both; {len(envd["only_old"])} are only in OLD and {len(envd["only_new"])} only in NEW.\n')
w('| module | declarations OLD → NEW | removed | added | type or value changed |'); w('|---|---|---|---|---|')
for m, c in pm.items(): w(f'| `{m}` | {fmt(c["old"])} → {fmt(c["new"])} | {c["removed"]} | {c["added"]} | {c["changed"]} |')
w('\nBy kind (OLD → NEW): ' + ', '.join(f'{k} {fmt(a)} → {fmt(b)}' for k, (a, b) in pk.items() if a or b) + '.')
w(f'- Types or values changed only for kinds ' + ', '.join(f'`{k}`' for k in kinds_changed) + '. No axiom, opaque or inductive type changed its type or value.')
w('- The four byte-identical modules have no changed declaration at this level either.\n')
def catlist(k, drop=()):
    c = envc[k]['categories']; return '; '.join(f'{v} {lab}' for lab, v in sorted(c.items(), key=lambda x: -x[1]) if lab not in drop)
fams = ', '.join(f'`{f}` ({n})' for f, n in sorted(eqfam.items()))
gone = ', '.join(f'`{f}.eq_{k}`' for f, k in sorted(eqgone))
w(f'### Removed ({len(envd["only_old"])})\n')
w(f'- **The removed instruction ({len(rm_ext)}):**')
w('  - `instr.EXTEND` and `admininstr.EXTEND`;')
w('  - the `EXTEND` cases of `wf_instr` and `wf_admininstr`, and of their `.below`;')
w('  - the lemmas Lean generates for each removed constructor: `elim`, `inj`, `injEq`, `noConfusion` and `sizeOf_spec`.')
w(f'- **Ends of numbered families that shrank ({len(rm_end)}).** Lean numbers many auxiliary declarations by position: equation lemmas `eq_N` (one per match arm), `_proof_N`, and `DecidableEq` sub-proofs. When such a family loses a member, its highest numbers disappear and the members after the removed one are renumbered.')
w('  - The families, with their size OLD → NEW: ' + '; '.join(f'`{st}N` {a}→{b}' for st, (a, b) in end_fams.items()) + '.')
w(f'  - For example, the deleted arms of `admininstr_instr`, `instr_of` and `ai_principal_typing` take away their last equation lemmas, {gone}.')
w(f'  - The lemmas from each deleted arm onward now state the next arm\'s equation, so their types changed: {fams}.')
w(f'- **Renumbered without shrinking ({len(rm_ren)}).** These belong to families that kept their size but were renumbered, or are hygienic names whose counter moved. Each has a counterpart among the {len(envd["only_new"])} added names.')
w('- **By category:** ' + catlist('only_old') + '. The full list is in Appendix B.\n')
w(f'### Added ({len(envd["only_new"])})\n')
w('All are the renumbered counterparts just described: ' + catlist('only_new') + '. There is no new user-level declaration and no new axiom.\n')
w('### Statements\n')
w(f'No user-level theorem, definition, inductive type or constructor has a different type. The {len(envd.get("type_changed_thm", []))} theorems, {len(envd.get("type_changed_def", []))} definitions and {len(envd.get("type_changed_rec", []))} recursors whose type differs are all generated by Lean:')
for k, lab in [('type_changed_thm', 'theorems'), ('type_changed_def', 'definitions'), ('type_changed_rec', 'recursors')]:
    w(f'- {lab}: ' + catlist(k) + '.')
w('')
w(f'**Inductive metadata.** A separate dump recorded every inductive, constructor and recursor: parameters, indices, constructor lists, constructor indices and field counts, and recursor motives, minor premises and rules. OLD was mapped by meaning. Of {fmt(n_meta_old)} OLD and {fmt(n_meta_new)} NEW entries, the only differences are:')
w(f'- the {len(IM["only_old"])} removed constructors: `EXTEND` of `instr` and `admininstr`, and case 19 of `wf_instr`, `wf_admininstr` and their `.below`;')
w(f'- {len(im_ind)} inductive types with one constructor fewer: ' + ', '.join(f'`{x}`' for x in im_ind) + ';')
w(f'- {im_ctor} constructors whose index went down by exactly 1, with everything else equal. These are the constructors after `EXTEND`: 48 of `instr`, 54 of `admininstr`, and the same numbers for `wf_instr`, `wf_admininstr` and their `.below`;')
w(f'- {len(im_rec)} recursors with one minor premise fewer: ' + ', '.join(f'`{x}`' for x in recs_rules) + ' also have one rule fewer, while ' + ', '.join(f'`{x}`' for x in recs_norules) + ' (the auxiliary recursors of the nested types) keep their 2 rules.\n')
w('This index shift explains the remaining generated changes: the types of the per-constructor `X.CTOR.elim`, the values of `ctorIdx`/`noConfusionType`, and the `DecidableEq` sub-proofs.\n')
ud = envc['value_changed_def']['user_level']; ut = envc['value_changed_thm']['user_level']
w(f'### Definitions whose elaborated value changed ({len(envd["value_changed_def"])}, of which {len(ud)} user-level)\n')
w('- `admininstr_instr`, `instr_of` and `ai_principal_typing` each lost their `EXTEND` arm.')
w('- `br_reduce_decidable` and `return_reduce_decidable` (`TypeProgress`) have unchanged source. They case-split on an `admininstr` with a `| _ =>` wildcard, so their terms now have one case fewer.')
w('- The rest are derived or auxiliary: ' + catlist('value_changed_def', drop=('USER-LEVEL (listed)',)) + '.\n')
edited = {e['owner'] for e in edits if e['kind'] == 'rename'} | set(agg)
same = sorted(t for t in edited if ('TLC.' + t) not in ut and t not in ut)
w(f'### Proof terms that changed ({len(ut)} user-level theorems)\n')
w('Most of these theorems have unchanged source; Appendix B lists them. A probe on NEW listed, for every theorem and definition, the declarations its term refers to directly, and marked those whose type changed or that are new:')
w(f'- **All {CA["user_changed_total"]} changed user-level declarations refer to such a declaration** ({len(ut)} theorems and {len(ud)} definitions; {CA["user_changed_refer"]} of {CA["user_changed_total"]}).')
w('  - Classified by the first such reference: ' + '; '.join(f'{v} {k}' for k, v in sorted(CA['first_hit_categories'].items(), key=lambda x: -x[1])) + '.')
w('  - In Wasm terms: their proofs destruct an instruction or its well-formedness, or rewrite with an equation of `ai_principal_typing`, `instr_of` or `admininstr_instr`, whose case analyses now have one case fewer.')
w(f'- **None of the {fmt(ucg(False, False))} unchanged user-level declarations refers to one.**')
w('- So, for user-level declarations, a changed term coincides exactly with a direct use of something the removal changed.\n')
w(f'All {len(edited)} theorems edited in §3.4 and §4.2 were pure renamings.')
w(f'- These {len(same)} have the same proof term as before, once constructor numbers are mapped: ' + ', '.join(f'`{t}`' for t in same) + '. They only apply a constructor.')
w(f'- The other {len(edited) - len(same)} {"each do" if all(cases_in[t] for t in edited if t not in same) else "mostly do"} a `cases` on `wf_instr`/`wf_admininstr`, whose eliminator lost a case.\n')
if v_not_t:
    w(f'Among generated theorems, {len(v_not_t)} changed value but not type. ' + ('Each refers directly to a changed declaration:' if all(n in CF and CF[n][0] > 0 for n in v_not_t) else 'NOT all of them refer directly to a changed declaration:'))
    for n in v_not_t: w(f'- `{n}` → `{CF[n][1].split(",")[0]}`' if n in CF else f'- `{n}`')
    w('')
w('### Axioms\n')
w(f'- **Unchanged for user-level theorems.** Every user-level theorem present in both builds has the same set of axioms.')
w(f'  - The only {len(axch)} theorems whose axioms differ are numbered auxiliaries: {axdesc}.')
w('  - Their numbers now point at other sub-proofs.')
w(f'- **`TLC.t_preservation`** uses {len(AN["t_preservation"])} axioms: the {ax_pres[0]} standard ones (`propext`, `Classical.choice`, `Quot.sound`) and {ax_pres[1]} of the model\'s `*_is_wf` axioms.')
w(f'- **`TLC.t_progress`** uses {len(AN["t_progress"])}: the {ax_prog[0]} standard ones, {ax_prog[1]} `*_is_wf` axioms and {ax_prog[2]} project axioms from Rocq\'s `axioms.v`.')
w(f'- Both lists are identical in OLD and NEW, and no theorem depends on `sorryAx` in either.\n')
w('### `Inhabited` defaults\n')
w(f'This is a kernel replay of the eight project modules other than `ExtendedDeriveDecEq`, with the {n_inst_mod} `Inhabited` instances defined in the modules, and the {n_inst_ext} external ones they use, made opaque:')
w(f'- OLD: {UO[2]} of {fmt(UO[1])} theorems need a default value.')
w(f'- NEW: {UN[2]} of {fmt(UN[1])}.')
w(f'- The difference of {UO[1] - UN[1]} is the {thm_removed} removed theorems minus the {thm_added} added.')
w(f'- **Positive control.** The audit was run again on NEW together with a scratch module of three control theorems, two of which read a default value. It checked {fmt(ctl_checked)} theorems and reported exactly those two (' + ', '.join(f'`{n}`' for n in sorted(ctl_names)) + '). So the harness does detect default-dependent proofs with this toolchain and build. The control module was never among the project\'s modules; a copy is kept as evidence (`evidence/tools/AuditCtl33.lean`).\n')
# 6
w('## 6. Every top-level construct whose text changed\n')
w(f'All nine files have the same top-level constructs, in the same order, in OLD and NEW: ' + ', '.join(f'`{m}` {cons[m]}' for m in MODS) + f', {fmt(n_cons)} in all.')
w('- **What counts as a construct.** Entries are as counted by `toplevel32.py`: every command that starts at column 0 outside comments, except `deriving` clauses.')
w(f'- Attribute lines, `initialize` and `set_option … in` prefixes count as separate entries. Counting declarations only gives {fmt(n_decl_entries)} (' + ', '.join(f'`{m}` {ckind[m]["decl"]}' for m in MODS if ckind[m]["prefix"]) + '; the rest unchanged).')
w(f'- The one-for-one match holds either way.\n')
w(f'These {len(pc)} have changed text:\n')
w('| file | construct | change |'); w('|---|---|---|')
lab = {'EXTEND-removed': 'line mentioning `EXTEND` deleted', 'ctor-renumber/generated': 'case declarations renumbered',
       'ctor-renumber/hand-layer': 'case references renumbered in the proof', 'ctor-renumber/proof-module': 'case references renumbered in the proof',
       'source-location': 'spec position in the header comment'}
for (f, k, c), v in pc.items():
    if (f, k, c) in loc_only: continue
    w(f'| `{f}` | `{k} {c}` | ' + '; '.join(f'{lab[x]} ({n})' for x, n in v.items()) + ' |')
w(f'| `wasm2.0` | {len(loc_only)} more constructs: ' + ', '.join(f'`{c}`' for (_, _, c) in loc_only) + ' | spec position in the header comment (1 line each) |')
w('')
# 7
w('## 7. Builds\n')
w('**How the builds were run.**')
w('- Both states were compiled from scratch in the scratchpad, one Lean process at a time, under a 12 GB memory cap.')
w('- The toolchain\'s `lean` v4.32.0 was called directly; the repo\'s `.lake/build` was not used.')
w('- The NEW error, `sorry` and warning counts are from the fresh build of the installed repo files.\n')
w('| module | errors OLD / NEW | `sorry` warnings OLD / NEW | warnings OLD / NEW | time (s): OLD / NEW scratch / NEW repo |'); w('|---|---|---|---|---|')
for m in MODS:
    a, b, c = co[m], cn[m], cs[m]; assert a[3] == b[3] == c[3] == '0'
    w(f'| `{m}` | {a[3]} / {b[3]} | {SW[("old", m)]} / {SW[("new", m)]} | {len(W[("old", m)])} / {len(W[("new", m)])} | {float(a[7]):.0f} / {float(c[7]):.0f} / {float(b[7]):.0f} |')
w(f'\n**Logs.** The OLD and NEW build logs are {"identical" if logs_same else "NOT identical"} once line numbers and timings are stripped. Only line numbers move, where lines were deleted above them. The logs contain:')
w(f'- the same {nwarn} warnings: ' + '; '.join(f'{v} {k}' for k, v in sorted(wsc.items(), key=lambda x: -x[1])) + ';')
w(f'- the same info output: {info_lines} lines printed by the `#check Instrs_ok2.rec` left inside a proof at `TypeProgress` line {[l for (m, l) in chk if m == "TypeProgress"][0]}.\n')
w('**Times.** "NEW scratch" is the build in which the repair was made, and "NEW repo" the fresh build of the installed files, which are byte-identical to it. Times vary with machine load, since the editor\'s Lean servers were running throughout; they are not a property of the change.\n')
w(f'**Memory.** The compiles peaked at {peak / 1024 / 1024:.2f} GiB ({fmt(peak)} KiB), in OLD\'s `TypeProgress`; NEW\'s `TypeProgress` peaked at {fmt(new_tp_rss)} KiB. The Lean probes of §5 peaked higher, at {probe_peak / 1024 / 1024:.2f} GiB ({fmt(probe_peak)} KiB), in the `Inhabited` audit runs.\n')
w('**No Lake build of either state.** The repo\'s `.lake/build` matches neither state.')
w(f'- Its traces record warning counts that differ even from OLD\'s: {lake_w} for `wasm2.0`, against {len(W[("old", "wasm2.0")])}.')
w('- It holds oleans for modules the lakefile no longer builds (`custom_notation`, `sandbox_5`, `sandbox_10`).')
w('- Both states were therefore checked only by these scratch builds with the bare `lean` binary. The lakefile sets no Lean options, and Lake\'s recorded setup for `wasm2.0` has empty options, so a Lake build should behave the same. That was not run.\n')
# 8
w('## 8. Left unchanged, and other notes\n')
w(f'**Comments that count instructions.** {len(stale)} comments in `TypingLemmas` still say 68, though `instr` now has {rc["instr"][1]} constructors.')
w('- Where (NEW lines): ' + '; '.join(f'line {l}, {t}' for l, t in stale) + '.')
w(f'- I left them as they were: they are comments, and line {stale[3][0]} records a past measurement.')
w(f'- Line {tilde74}, "~74 cases uniformly", describes Rocq\'s tactic script, so I didn\'t count it as stale. Read as a statement about Lean, it would now be 73.')
w(f'- Line {rocq68}, "Rocq destructs both instructions (68×68)", also describes Rocq.')
w(f'- Line {all73}, "all 73 cases", counts `Instr_ok` rules, which are still {rc["Instr_ok"][1]}.\n')
w(f'**Comments that cite model line numbers.** {len({(m, l) for (m, l, *_) in cit_rows})} comments in the proof modules cite `wasm2.0.lean` by {len(cit_rows)} line numbers beyond the first deleted line. All {len(cit_rows)} citations were already wrong in OLD, and the declarations they name moved again, by 2 or 5 lines:\n')
w('| comment (NEW file:line) | cites line | names | actually at OLD → NEW |'); w('|---|---|---|---|')
for (m, l, cited, nm, a, b) in cit_rows: w(f'| `{m}:{l}` | {cited} | `{nm}` | {a} → {b} |')
w(f'\nThe comments that cite lines 9, 12 and 20 are right in both versions. The one citing line 798 for `size` was already wrong in OLD: it is at line {size_old} in both.')
w('I left all of them as they are.\n')
w(f'**The word `sorry`.** No code contains `sorry`, but the word appears on {len(sorry_lines)} comment lines of the nine NEW modules:')
for (m, l, _, t) in sorry_lines:
    kind = 'commented-out generated original' if t.startswith('--') else ('docstring: `Step_read_is_wf` used to be `sorry`' if 'Admitted' in t or 'until the spec' in t else 'status note saying there is no `sorry`')
    w(f'- `{m}` line {l}: {kind};')
w(f'- so a plain `grep sorry` finds these {len(sorry_lines)} lines, and none is a proof hole. `OLD_wasm2.0.lean` has the same two commented-out lines, at {old_sorry_model[0]} and {old_sorry_model[1]}.\n')
w('**Files not touched this turn:** `wasm2.0.lean`, `OLD_wasm2.0.lean`, ' + ', '.join(f'`{m}`' for m in MODS if m not in REPAIRED and m != 'wasm2.0') + '.\n')
w(f'**Pre-existing, and the same in OLD and NEW: two re-stated theorems.** The fresh generator output, `spectec/test-lean/todaywasm2.0.lean` (md5 `{md5("/home/zhengyew/spectec/spectec/test-lean/todaywasm2.0.lean")[:8]}…`), has {gen_sorry} `sorry`s.')
w(f'- **Proved as generated:** {gen_sorry - len(commented)} of those theorems, in both OLD and NEW.')
w('- **Commented out:** the generated `Step_read_is_wf` and `Step_is_wf`, with their `--   sorry` at lines ' + ' and '.join(str(x) for x in commented) + f'. The commented-out text is {"identical" if orig_same else "NOT identical"} in OLD and NEW.')
w('- **Re-stated:** each is re-stated below `inductive Store_ok` with three changes, as in bundle29:')
w('  - it moves below `Store_ok`;')
w('  - it takes the configuration as `(z : state) (admininstr_lst : List admininstr)`, with `config.mk_config z admininstr_lst` in the hypotheses;')
w('  - it gets the premise `Store_ok (fun_store z)`.')
w('- **The generated forms are false.** Bundles 23 and 29 showed this with a Lean witness, using axioms `propext`, `Classical.choice` and `Quot.sound` only (`bundle29/evidence/unedited_Step_read_is_wf_false.log`).')
w('  - The counterexample is a well-formed configuration whose store holds a table of 2^32 references. It steps by `table.size` to `CONST I32 2^32`, which is not a well-formed `u32`.')
w('  - The witness source was not kept, so it was not re-run on NEW. The counterexample does not involve `EXTEND`.')
w('- **What "zero `sorry`" covers:** all generated statements except these two, which hold only in the weaker re-stated form. This port changed them only by the renamings in their proofs (§3.4).\n')
w('**Documentation.**')
w(f'- **Living docs** (`claude-logging/README.md`, `for-claude/*.md`, `for-humans/*.md`): they mention `EXTEND` or numbered `*_case_` names only in ' + ', '.join(sorted({f'`{f}`' for f, _, _ in living_hits_l})) + ' (lines ' + ', '.join(str(l) for _, l, _ in living_hits_l) + ').')
w('  - Those lines describe Rocq\'s `wasm.v`, which still has `instr_EXTEND` (`spectec/test-rocq/theories/wasm.v:3282`), so they are accurate.')
w(f'- **Historical logs:** {sum(hist_by_bundle.values())} files mention old case numbers, all under `verbatim_dialogue_log/` (' + ', '.join(f'{k} {v}' for k, v in sorted(hist_by_bundle.items(), key=lambda x: int(x[0][6:]))) + f'); {hist_sc} are in `safety-checks/`. They are records of past turns, so I left them as they are.\n')
w('**Cross-check with the trial port** (`spectec/src/temp_port_reference/`). That port was made outside this log, by a patch-based procedure. I compared against it only after my own result compiled, and its records agree with mine everywhere (`evidence/outputs/trial_port_crosscheck.txt`):')
w(f'- **Files:** all nine NEW files are {"byte-identical" if tp_same else "NOT identical"} to its `trial_port/`.')
w('- **Edits:** its `patches/edits_73.log` lists the same 73 edits: 56 + 15 renamings and 2 deleted arms. They match one for one by file, kind and text. That log truncates long lines, so the texts were matched as prefixes.')
w('- **Declarations:** its declaration diff `logs/constants_diff_v0_vs_v2.tsv` has the same 43 removed and 12 added declarations as §5. It compares by name, so it names the removed cases by their last numbers (`_case_67`, `_case_73`) rather than by meaning.')
w('- **Warnings, axioms and the audit:** it finds the same warnings, the same axiom counts for `t_preservation` (35), `t_progress` (74), `Step_is_wf` (35) and `Step_read_is_wf` (6), and the same audit result. My dumps give the same four sets in OLD and NEW.')
w('- **Comments:** it flags the same five stale "68" comments.')
w('- **One point where it is out of date.** Its caveat that the falsity of the generated `Step_*` forms "has not been confirmed with a Lean witness" overlooks the bundle 23/29 witness above.\n')
w('**`lake build`.** I didn\'t run it, because it writes `.lake/build`.')
w('- That directory predates these changes, so the next `lake build` or editor session rebuilds at least `wasm2.0` and the seven modules that import it, which takes a few minutes.')
w('- `ExtendedDeriveDecEq` is unchanged.')
w('- Until the rebuild, the editor may show errors.\n')
# 9
w('## 9. Method and evidence\n')
w('Everything is in `claude-logging/verbatim_dialogue_log/bundle33/evidence/`.\n')
w('**`tools/`:**')
w('- `scan33.py`: finds every affected code reference, by constructor meaning;')
w('- `apply33.py`: applies the 17 edits, asserting each expected line;')
w('- `diff33.py`: the line accounting;')
w('- `EnvDump33.lean`, `envdiff33.py` and `envcat33.py`: the Lean-level comparison;')
w('- `RunAudit33.lean`: the `Inhabited` audit;')
w('- `chain33.sh`, `lrun33.sh` and `check33.sh`: the serial build and the safety checks;')
w('- `IndMeta33.lean` and `Cause33.lean`, analysed by `meta_cause33.py`: the inductive-metadata comparison and the probe of why each proof term changed;')
w('- `AuditCtl33.lean` and `RunAuditCtl33.lean`: the audit\'s positive control;')
w('- `report33.py`: generates this report. `report33_v1.py` and `report33_v2.py` generated the earlier versions, and `patch_v3*.py` turned v2 into v3;')
w('- `toplevel32.py` and `ctor_map32.py` come from bundle32.\n')
w('**`outputs/`:**')
w('- the build logs;')
w('- the error logs of the unrepaired modules;')
w(f'- `diff33_all_changed_lines.tsv`, with all {n_rows} lines;')
w('- the unified diffs `*.diff`;')
w('- the constructor map;')
w('- the declaration dumps `dump_old.tsv.gz` and `dump_new.tsv.gz`, and their comparison `envdiff33.json`/`envcat33.json`;')
w('- the audit outputs, including the positive control (`audit_ctl.txt`);')
w('- the inductive-metadata dumps and their comparison (`indmeta_*.tsv`, `indmeta_diff33.json`), and the cause probe (`cause_new.tsv`, `cause_set.txt`, `cause33.json`);')
w('- `trial_port_crosscheck.txt`.\n')
w('**`verification/`:** the reports of the independent, read-only verifiers.')
w('- `V-REPORT-1` checked version 1 of this report and raised 17 points.')
w('- Three more checked version 2 (`workflow_reverify_result.json`): `V2-FIX` checked whether those points were resolved, `V2-FRESH` did a fresh refutation, and `V2-CRITIC` looked for completeness. They raised 32 findings.')
w('- None of the 49 points found an error in the repair or in the line accounting. Appendix E says how each was addressed in this version 3.')
w('- Versions 1 and 2 of the report are kept next to the verifier reports.\n')
w('**A known defect in the build summaries.** The `sorry-warnings=` field of the `chain_*.txt` summaries was counted with the wrong quote character, so it always reads 0. The tool is fixed in `evidence/tools/chain33.sh`, and the counts in §7 are recounted from the logs.')
w('- The only log with such warnings is the first, unrepaired `TypingLemmas` compile: 7 warnings, all from error recovery.')
w('- No final log contains the word `sorry`.\n')
# appendices
w(f'## Appendix A. All {n_hand} changed lines of the model\'s proofs (§3.4)\n')
w(f'The last column is from bundle32\'s compile of the unrenamed copy (`bundle32/evidence/outputs/compile_verbatim_copy_72_errors.log`, 72 errors on {len(errlines)} lines; line numbers are NEW\'s). {len(NEC["own"])} of the {n_hand} lines failed on the line itself. The other {len(NEC["noown"])} failed on an adjacent line of the same term or `cases`, given as "near L".\n')
w('| OLD → NEW line | construct | instruction | OLD text → NEW text | error in the unrenamed compile |'); w('|---|---|---|---|---|')
for r in rows:
    if r['cat'] == 'ctor-renumber/hand-layer':
        ins = ', '.join(sorted({meaning[f'admininstr_case_{k}'] for _, k in re.findall(r'\b((?:admin)?instr_case)_(\d+)\b', r['before']) if int(k) >= 20}))
        ec = 'this line' if r['new'] in NEC['own'] else f'near {nearest(r["new"])}'
        w(f'| {r["old"]} → {r["new"]} | `{r["construct"]}` | `{ins}` | {code(esc(r["before"]))} → {code(esc(r["after"]))} | {ec} |')
w('')
w('## Appendix B. Lean-level lists (§5)\n')
w(f'**Only in OLD ({len(envd["only_old"])}):** ' + ', '.join(f'`{n}`' for n in envd['only_old']) + '.\n')
w(f'**Only in NEW ({len(envd["only_new"])}):** ' + ', '.join(f'`{n}`' for n in envd['only_new']) + '.\n')
byM = collections.OrderedDict()
for n in ut: byM.setdefault(DN[n][0], []).append(n)
w(f'**User-level theorems whose elaborated proof term changed ({len(ut)}), by module** (a leading `TLC.` is omitted):\n')
for m in sorted(byM, key=lambda x: MODS.index(x.strip('«»'))):
    w(f'- `{m}` ({len(byM[m])}): ' + ', '.join(f'`{n[4:] if n.startswith("TLC.") else n}`' for n in byM[m]))
w(f'\n**User-level definitions whose elaborated value changed ({len(ud)}):** ' + ', '.join(f'`{n}`' for n in ud) + '.\n')
w(f'## Appendix C. All {n_down} changed lines of the proof modules (§4)\n')
w('| module | line OLD → NEW | construct | OLD text | NEW text |'); w('|---|---|---|---|---|')
for r in rows:
    if r['file'] != 'wasm2.0': w(f'| `{r["file"]}` | {r["old"]} → {r["new"] if r["new"] else "—"} | `{r["construct"]}` | {code(esc(r["before"]))} | {code(esc(r["after"])) if r["after"] is not None else "(deleted)"} |')
w('')
w('## Appendix D. Byte-level facts (§1)\n')
w('| module | OLD bytes | OLD md5 | NEW bytes | NEW md5 |'); w('|---|---|---|---|---|')
for m in MODS:
    a, b = BF[('old', m)], BF[('final', m)]; w(f'| `{m}.lean` | {fmt(a["size"])} | `{a["md5"]}` | {fmt(b["size"])} | `{b["md5"]}` |')
w('')
w('## Appendix E. Verifier findings and how each was addressed\n')
w('Each verifier finding (V1 = `V-REPORT-1` on version 1; FIX, FRESH and CRITIC = the three verifiers on version 2) is in `verification/`. None found an error in the repair or in the line accounting. Several found the same point independently; such points are listed once.\n')
w('| finding | point | how it is addressed in version 3 |'); w('|---|---|---|')
for fid, pt, res in RESOLUTIONS: w(f'| {fid} | {pt} | {res} |')
open(OUT, 'w').write('\n'.join(L) + '\n')
print('written', OUT, len(L), 'lines')

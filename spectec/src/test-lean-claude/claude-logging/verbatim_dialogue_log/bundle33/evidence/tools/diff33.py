# bundle33: exhaustive line-level accounting of (old proof + OLD_wasm2.0.lean) vs (new proof + wasm2.0.lean).
# Every differing line is paired and classified; anything not explained by the rules is reported UNEXPLAINED.
import re, sys, json, difflib, collections
sys.path.insert(0, sys.argv[1]); from toplevel32 import constructs, owner
B = sys.argv[2]; cm = json.load(open(f'{B}/work/ctor_map33.json'))
MODS = ['ExtendedDeriveDecEq', 'wasm2.0', 'HelperLemmas', 'Subtyping', 'TypingLemmas', 'TypePreservationPure',
        'ExtensionLemmas', 'TypePreservation', 'TypeProgress']
DEL_PATTERNS = [r'^  \| EXTEND \(v_numtype : numtype\) \(v_n : n\) : (admin)?instr$',
                r'^  \| (admin)?instr_case_19 \(v_numtype : numtype\) \(v_n : n\) : wf_(admin)?instr \((admin)?instr\.EXTEND v_numtype v_n\)$',
                r'^  \| instr\.EXTEND x0 x1 => admininstr\.EXTEND x0 x1$',
                r'^  \| admininstr\.EXTEND x0 x1 => some \(instr\.EXTEND x0 x1\)$',
                r'^  \| admininstr\.EXTEND _ _ => False$']
def renum(l):
    return re.sub(r'\b(admininstr_case|instr_case)_(\d+)\b',
                  lambda m: (cm['wf_instr' if m.group(1) == 'instr_case' else 'wf_admininstr']['map'].get(f'{m.group(1)}_{m.group(2)}') or 'XX'), l)
def shiftloc(l):
    def f(n): n = int(n); return str(n - 1) if n > 474 else str(n)
    return re.sub(r'1-syntax\.spectec:(\d+)\.(\d+)-(\d+)\.(\d+)', lambda m: f'1-syntax.spectec:{f(m.group(1))}.{m.group(2)}-{f(m.group(3))}.{m.group(4)}', l)
rows = []; summary = {}
for M in MODS:
    O = open(f'{B}/old/src/{M}.lean').read().split('\n'); N = open(f'{B}/final/src/{M}.lean').read().split('\n')
    co, cn = constructs(O), constructs(N)
    # Alignment without heuristics: drop the lines matching the removal patterns from the old file; the rest
    # must then align 1:1 with the new file (same length), and each pair is classified by the rule that maps it.
    dels = [i for i, l in enumerate(O) if any(re.match(p, l) for p in DEL_PATTERNS)]
    keep = [i for i in range(len(O)) if i not in set(dels)]
    assert len(keep) == len(N), (M, len(keep), len(N))
    for i in dels:
        ow = owner(co, i + 1)
        rows.append(dict(file=M, old=i + 1, new=None, cat='EXTEND-removed', kind=ow['kind'], construct=ow['name'], before=O[i], after=None))
    for j, i in enumerate(keep):
        a, b = O[i], N[j]
        if a == b: continue
        ow = owner(cn, j + 1)
        if renum(a) == b:
            region = 'generated' if ow['kind'] == 'inductive' and M == 'wasm2.0' else ('hand-layer' if M == 'wasm2.0' else 'proof-module')
            cat = f'ctor-renumber/{region}'
        elif shiftloc(a) == b: cat = 'source-location'
        elif shiftloc(renum(a)) == b: cat = 'ctor-renumber+source-location'
        else: cat = 'UNEXPLAINED'
        rows.append(dict(file=M, old=i + 1, new=j + 1, cat=cat, kind=ow['kind'], construct=ow['name'], before=a, after=b))
    c = collections.Counter(r['cat'] for r in rows if r['file'] == M)
    summary[M] = dict(old_lines=len(O) - 1, new_lines=len(N) - 1, **c)
json.dump(dict(summary=summary, rows=rows), open(f'{B}/work/diff33.json', 'w'), indent=1, ensure_ascii=False)
for M, s in summary.items(): print(M, s)
print('UNEXPLAINED total:', sum(1 for r in rows if r['cat'] == 'UNEXPLAINED'))
# per construct
pc = collections.OrderedDict()
for r in rows: pc.setdefault((r['file'], r['kind'], r['construct']), collections.Counter())[r['cat']] += 1
print('constructs touched:', len(pc))
for k, v in pc.items():
    if set(v) != {'source-location'}: print('  ', k, dict(v))
print('constructs with only source-location changes:', sum(1 for v in pc.values() if set(v) == {'source-location'}))

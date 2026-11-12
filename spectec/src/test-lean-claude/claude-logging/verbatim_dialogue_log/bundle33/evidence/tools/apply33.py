# bundle33: apply the downstream repair edits derived by scan33.py to pristine copies (orig/) -> new/src/.
# Renames: replace exactly the scanned code tokens on the scanned lines (by meaning, via the constructor map).
# Deletions: the two dead match arms on the removed constructor admininstr.EXTEND (exact line text asserted).
import json, re, sys
B = sys.argv[1]; scan = json.load(open(f'{B}/work/scan33_orig.json'))
DELETE = {('TypingLemmas', 131): '  | admininstr.EXTEND x0 x1 => some (instr.EXTEND x0 x1)',
          ('TypingLemmas', 454): '  | admininstr.EXTEND _ _ => False'}
log = []
for m, res in scan.items():
    L = open(f'{B}/orig/{m}.lean').read().split('\n')
    byline = {}
    for (ln, old, new, meaning, owner, text) in res['code_renames']: byline.setdefault(ln, []).append((old, new, meaning, owner))
    for (ln, tok, owner, text) in res['code_extend']:
        if (m, ln) not in DELETE: assert tok.endswith('.EXTEND') and not tok.startswith(('instr.', 'admininstr.')) or tok == 'EXTEND', (m, ln, tok)
    assert not res['code_unmapped'], res['code_unmapped']
    for ln, items in sorted(byline.items()):
        before = L[ln - 1]; after = before
        for (old, new, meaning, owner) in items:
            n = len(re.findall(r'\b%s\b' % old, after)); assert n == 1, (m, ln, old, n)
            after = re.sub(r'\b%s\b' % old, new, after)
        L[ln - 1] = after; log.append({'module': m, 'line': ln, 'kind': 'rename', 'renames': [(o, n, mn) for (o, n, mn, _) in items], 'owner': items[0][3], 'before': before, 'after': after})
    for (mm, ln), text in sorted(DELETE.items(), reverse=True):
        if mm != m: continue
        assert L[ln - 1] == text, (m, ln, L[ln - 1]); owner = [o for (l2, t, o, _) in res['code_extend'] if l2 == ln][0]
        log.append({'module': m, 'line': ln, 'kind': 'delete', 'owner': owner, 'before': text, 'after': None}); del L[ln - 1]
    open(f'{B}/new/src/{m}.lean', 'w').write('\n'.join(L))
log.sort(key=lambda d: (d['module'], d['line']))
json.dump(log, open(f'{B}/work/edits33.json', 'w'), indent=1, ensure_ascii=False)
for d in log: print(d['module'], d['line'], d['kind'], d['owner'], '|', d['before'].strip()[:90], '=>', (d['after'] or '<deleted>').strip()[:90])
print(len(log), 'edits')

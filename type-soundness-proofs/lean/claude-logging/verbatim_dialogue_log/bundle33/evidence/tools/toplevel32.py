# Top-level construct scanner for the generated Lean model files (block-comment aware, nesting).
import re
KW = ('theorem', 'lemma', 'def', 'inductive', 'structure', 'class', 'abbrev', 'opaque', 'axiom', 'instance',
      'import', 'mutual', 'end', 'derive_deceq', 'namespace', 'section', 'open', 'set_option', 'attribute',
      'macro', 'syntax', 'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'noncomputable',
      'private', 'protected', 'partial', 'unsafe', '@[', 'example', 'elab', 'universe', 'variable')
def code_mask(lines):
    """For each line, the part outside comments (block comments nest; '--' line comments)."""
    depth = 0; out = []
    for l in lines:
        i = 0; code = []
        while i < len(l):
            if depth == 0 and l.startswith('--', i): break
            if l.startswith('/-', i): depth += 1; i += 2; continue
            if depth > 0 and l.startswith('-/', i): depth -= 1; i += 2; continue
            if depth == 0: code.append(l[i])
            i += 1
        out.append(''.join(code))
    return out
def constructs(lines):
    """List of dicts {kind, name, line (1-based), end (1-based, last non-blank code-bearing line)}."""
    code = code_mask(lines); res = []
    for i, c in enumerate(code):
        if not c or c[0] in ' \t': continue
        if c.startswith('deriving'): continue  # continuation of the preceding inductive/structure
        tok = re.match(r'(@\[|[A-Za-z_]+)', c)
        if not tok or tok.group(1) not in KW:
            res.append({'kind': 'UNKNOWN', 'name': c.strip()[:60], 'line': i + 1}); continue
        kind = tok.group(1); rest = c[len(kind):].strip()
        if kind in ('theorem', 'lemma', 'def', 'inductive', 'structure', 'class', 'abbrev', 'opaque', 'axiom', 'derive_deceq', 'import', 'example'):
            name = re.match(r'(\S+)', rest).group(1) if rest else ''
            name = re.split(r'[\s(:{\[]', name)[0] if kind not in ('import',) else name
        elif kind == 'instance':
            name = re.sub(r'\s+', ' ', re.split(r'\bwhere\b|:=', rest)[0]).strip()
        else:
            name = rest
        res.append({'kind': kind, 'name': name, 'line': i + 1})
    for k, r in enumerate(res):
        nxt = res[k + 1]['line'] - 1 if k + 1 < len(res) else len(lines)
        e = nxt
        while e > r['line'] and not code[e - 1].strip(): e -= 1
        r['end'] = e
    return res
def owner(cons, lineno):
    """The construct whose [line, end] contains lineno (1-based), else the next construct (header/comment)."""
    for r in cons:
        if r['line'] <= lineno <= r['end']: return r
    for r in cons:
        if r['line'] > lineno: return dict(r, note='precedes')
    return None

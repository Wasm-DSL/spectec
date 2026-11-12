#!/usr/bin/env python3
"""Independent extractor of top-level Lean 4 constructs (V-ORD verifier).

Usage: python3 -I extract.py FILE.lean OUT.json

Method:
  1. Char-level lexer replaces every comment character with a space while keeping
     newlines (so line/column positions are preserved):
       * `--` (outside block comments and strings) starts a line comment to end of line;
       * `/-` starts a block comment (covers `/--` doc and `/-!` module-doc comments);
         inside a block comment `/-` nests (+1) and `-/` closes (-1), as in Lean 4's
         finishCommentBlock;
       * string literals "..." (with backslash escapes) are kept as code so that comment
         delimiters inside them are not misread.
     Comment text is also recorded per line so header comments can be inspected.
  2. Every line whose code-only text has a non-space character at column 0 is a
     "column-0 code line". Its first token must be a recognised command keyword,
     otherwise it is reported as STRAY. Lines whose first code token is a command
     keyword but not at column 0 are reported too (NONCOL0).
  3. `deriving ...` lines are attached to the preceding declaration.
  4. For each construct, the contiguous block of blank / comment-only lines directly
     above it is its header; the comment text in it is recorded (the helper marker is
     `HELPER LEMMA CREATED BY CLAUDE`).
"""
import json
import re
import sys

KEYWORDS = {
    'import', 'inductive', 'def', 'theorem', 'abbrev', 'structure', 'opaque', 'axiom',
    'derive_deceq', 'mutual', 'end', 'instance', 'deriving',
}
# A wider list used only to flag suspicious command keywords anywhere in code.
ALL_CMD_WORDS = [
    'theorem', 'lemma', 'def', 'abbrev', 'inductive', 'structure', 'class', 'instance',
    'axiom', 'opaque', 'example', 'mutual', 'end', 'namespace', 'section', 'open',
    'set_option', 'attribute', 'variable', 'universe', 'derive_deceq', 'deriving',
    'noncomputable', 'private', 'protected', 'partial', 'unsafe', 'macro', 'macro_rules',
    'syntax', 'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'elab',
    'import', 'export', 'initialize', 'termination_by', 'decreasing_by',
]
MARKER = 'HELPER LEMMA CREATED BY CLAUDE'


def lex(text):
    """Return (code_lines, comment_lines, problems)."""
    n = len(text)
    code = []      # characters of code-only text
    cmt = []       # characters of comment-only text (others -> space)
    i = 0
    depth = 0
    in_line = False
    in_str = False
    problems = []
    while i < n:
        c = text[i]
        if c == '\n':
            # newline always kept in both streams
            if in_str:
                pass  # Lean strings may contain newlines; keep going
            in_line = False
            code.append('\n')
            cmt.append('\n')
            i += 1
            continue
        if in_line:
            code.append(' ')
            cmt.append(c)
            i += 1
            continue
        if depth > 0:
            if text.startswith('/-', i):
                depth += 1
                code.append('  ')
                cmt.append('/-')
                i += 2
                continue
            if text.startswith('-/', i):
                depth -= 1
                code.append('  ')
                cmt.append('-/')
                i += 2
                continue
            code.append(' ')
            cmt.append(c)
            i += 1
            continue
        if in_str:
            if c == '\\' and i + 1 < n:
                code.append(text[i:i + 2])
                cmt.append('  ')
                i += 2
                continue
            if c == '"':
                in_str = False
            code.append(c)
            cmt.append(' ')
            i += 1
            continue
        # plain code state
        if text.startswith('--', i):
            in_line = True
            code.append('  ')
            cmt.append('--')
            i += 2
            continue
        if text.startswith('/-', i):
            depth = 1
            code.append('  ')
            cmt.append('/-')
            i += 2
            continue
        if c == '"':
            in_str = True
        code.append(c)
        cmt.append(' ')
        i += 1
    if depth != 0:
        problems.append(f'EOF inside block comment (depth {depth})')
    if in_str:
        problems.append('EOF inside string literal')
    code_s = ''.join(code)
    cmt_s = ''.join(cmt)
    code_lines = code_s.split('\n')
    cmt_lines = cmt_s.split('\n')
    assert len(code_lines) == len(cmt_lines) == text.count('\n') + 1
    return code_lines, cmt_lines, problems


NAME_RE = re.compile(r'[^\s(:{\[⦃]+')


def norm(s):
    return ' '.join(s.split())


def extract(path):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    raw_lines = text.split('\n')
    code_lines, cmt_lines, problems = lex(text)
    constructs = []
    stray = []
    noncol0 = []
    midline = []
    deriving_orphans = []
    kw_mid_re = re.compile(r"(?<![\w'.!?])(" + '|'.join(map(re.escape, ALL_CMD_WORDS)) + r")(?![\w'!?])")
    for idx, cl in enumerate(code_lines):
        lineno = idx + 1
        stripped = cl.strip()
        if not stripped:
            continue
        first_tok = stripped.split()[0]
        col0 = (cl[0] != ' ')
        # mid-line command keywords (anything after the first token)
        lead = len(cl) - len(cl.lstrip(' '))
        rest_start = lead + len(first_tok)
        for m in kw_mid_re.finditer(cl, rest_start):
            midline.append({'line': lineno, 'word': m.group(1), 'text': raw_lines[idx]})
        if not col0:
            if first_tok in KEYWORDS or first_tok in ALL_CMD_WORDS:
                noncol0.append({'line': lineno, 'tok': first_tok, 'text': raw_lines[idx]})
            continue
        if first_tok not in KEYWORDS:
            stray.append({'line': lineno, 'tok': first_tok, 'text': raw_lines[idx]})
            continue
        if first_tok == 'deriving':
            if not constructs:
                deriving_orphans.append({'line': lineno, 'text': raw_lines[idx]})
            else:
                constructs[-1].setdefault('deriving', []).append(norm(stripped))
                constructs[-1]['deriving_lines'].append(lineno)
            continue
        after = stripped[len(first_tok):].strip()
        if first_tok in ('mutual',):
            name = norm(after)
        elif first_tok == 'end':
            name = norm(after)
        elif first_tok == 'instance':
            if after.startswith(':'):
                name = 'ANON' + norm(after)
            else:
                m = NAME_RE.match(after)
                name = m.group(0) if m else 'ANON?' + norm(after)
        else:
            m = NAME_RE.match(after)
            name = m.group(0) if m else ''
        # header: contiguous blank/comment-only lines directly above
        hdr = []
        j = idx - 1
        while j >= 0 and code_lines[j].strip() == '':
            if cmt_lines[j].strip():
                hdr.append(cmt_lines[j].strip())
            j -= 1
        hdr.reverse()
        constructs.append({
            'line': lineno,
            'kind': first_tok,
            'name': name,
            'header': hdr,
            'header_start': j + 2,  # first line of the header block (1-based)
            'helper': any(MARKER in h for h in hdr),
            'marker_count': sum(h.count(MARKER) for h in hdr),
            'deriving_lines': [],
            'sig': norm(stripped),
        })
    # span end and body text (code-only) per construct
    for k, c in enumerate(constructs):
        end_line = (constructs[k + 1]['header_start'] - 1) if k + 1 < len(constructs) else len(code_lines)
        c['end'] = end_line
        body_code = '\n'.join(code_lines[c['line'] - 1:end_line])
        c['body_norm'] = norm(body_code)
    # markers not attached to any construct header
    marker_lines = [i + 1 for i, l in enumerate(cmt_lines) if MARKER in l]
    attached = set()
    for c in constructs:
        for ln in range(c['header_start'], c['line']):
            if MARKER in cmt_lines[ln - 1]:
                attached.add(ln)
    unattached = [ln for ln in marker_lines if ln not in attached]
    return {
        'path': path,
        'nlines': len(raw_lines) - (1 if text.endswith('\n') else 0),
        'problems': problems,
        'constructs': constructs,
        'stray': stray,
        'noncol0': noncol0,
        'midline': midline,
        'deriving_orphans': deriving_orphans,
        'marker_lines': marker_lines,
        'unattached_markers': unattached,
    }


if __name__ == '__main__':
    res = extract(sys.argv[1])
    with open(sys.argv[2], 'w', encoding='utf-8') as f:
        json.dump(res, f, ensure_ascii=False, indent=1)
    cs = res['constructs']
    print(f"{sys.argv[1]}: lines={res['nlines']} constructs={len(cs)} helpers={sum(c['helper'] for c in cs)} "
          f"stray={len(res['stray'])} noncol0={len(res['noncol0'])} midline_kw={len(res['midline'])} "
          f"deriving_orphans={len(res['deriving_orphans'])} markers={len(res['marker_lines'])} "
          f"unattached_markers={len(res['unattached_markers'])} problems={res['problems']}")

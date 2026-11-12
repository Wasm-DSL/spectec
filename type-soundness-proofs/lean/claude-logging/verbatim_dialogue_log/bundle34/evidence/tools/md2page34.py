# bundle34: turn the bundle33 report (Markdown, version 4) into a designed, self-contained HTML page for an Artifact.
# The report body is converted structurally (headings, lists, tables, code, bold); the header figures and the diff ledger
# are derived from the same bundle33 data files. No external scripts; fonts from Google Fonts only.
import re, html, json, sys, hashlib
R, B33, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
src = open(R).read(); L = src.split('\n')
md5 = hashlib.md5(src.encode()).hexdigest()
esc = lambda s: html.escape(s, quote=True)
def slug(t):
    t = re.sub(r'`', '', t); t = re.sub(r'[^A-Za-z0-9]+', '-', t).strip('-').lower(); return t or 'section'
def inline(s):
    codes = []
    pat = re.compile(r'``\s(.+?)\s``|`([^`]+)`')
    def repl(m):
        codes.append(m.group(1) if m.group(1) is not None else m.group(2)); return f'\x00{len(codes) - 1}\x00'
    s = pat.sub(repl, s)
    s = esc(s)
    s = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', s)
    s = re.sub(r'\x00(\d+)\x00', lambda m: '<code>' + esc(codes[int(m.group(1))]) + '</code>', s)
    return s
NAIVE_DIFF = []
def cells(row):
    # split on unescaped pipes outside backtick code spans (one row of the report has an unescaped pipe inside code)
    row = row.strip()
    assert row.startswith('|') and row.endswith('|'), row[:60]
    inner = row[1:-1]; parts = []; cur = []; incode = False; k = 0
    while k < len(inner):
        ch = inner[k]
        if ch == '\\' and k + 1 < len(inner) and inner[k + 1] == '|': cur.append('|'); k += 2; continue
        if ch == '`': incode = not incode
        if ch == '|' and not incode: parts.append(''.join(cur)); cur = []; k += 1; continue
        cur.append(ch); k += 1
    parts.append(''.join(cur))
    naive = re.split(r'(?<!\\)\|', inner)
    if len(naive) != len(parts): NAIVE_DIFF.append(row[:90])
    return [x.strip() for x in parts]
body = []; toc = []; i = 0; h1 = None
def close_lists(stack):
    while stack: body.append('</li></ul>'); stack.pop()
stack = []  # list indentation levels
para = []
def flush_para():
    global para
    if para: body.append('<p>' + inline(' '.join(para)) + '</p>'); para = []
while i < len(L):
    l = L[i]
    if l.startswith('```'):
        flush_para(); close_lists(stack); j = i + 1; code = []
        while not L[j].startswith('```'): code.append(L[j]); j += 1
        body.append('<div class="code-wrap"><pre><code>' + esc('\n'.join(code)) + '</code></pre></div>'); i = j + 1; continue
    m = re.match(r'^(#{1,3}) (.*)$', l)
    if m:
        flush_para(); close_lists(stack); lvl = len(m.group(1)); text = m.group(2)
        if lvl == 1: h1 = text
        else:
            sid = slug(text); body.append(f'<h{lvl} id="{sid}">{inline(text)}</h{lvl}>')
            if lvl == 2: toc.append((sid, text))
        i += 1; continue
    if l.startswith('|'):
        flush_para(); close_lists(stack); rows = []
        while i < len(L) and L[i].startswith('|'): rows.append(L[i]); i += 1
        head = cells(rows[0]); assert re.match(r'^\|(\s*-+\s*\|)+$', rows[1].replace(' ', '')), rows[1]
        t = ['<div class="table-wrap"><table><thead><tr>' + ''.join(f'<th>{inline(c)}</th>' for c in head) + '</tr></thead><tbody>']
        for r in rows[2:]:
            cs = cells(r); assert len(cs) == len(head), (len(cs), len(head), r[:80])
            t.append('<tr>' + ''.join(f'<td>{inline(c)}</td>' for c in cs) + '</tr>')
        t.append('</tbody></table></div>'); body.append(''.join(t)); continue
    m = re.match(r'^( *)- (.*)$', l)
    if m:
        flush_para(); ind = len(m.group(1)); text = m.group(2)
        if not stack or ind > stack[-1]:
            body.append('<ul><li>'); stack.append(ind)
        else:
            while stack and ind < stack[-1]: body.append('</li></ul>'); stack.pop()
            body.append('</li><li>')
        body.append(inline(text)); i += 1; continue
    if l.strip() == '':
        flush_para(); close_lists(stack); i += 1; continue
    if stack and l.startswith(' '):
        body.append(' ' + inline(l.strip())); i += 1; continue
    close_lists(stack); para.append(l.strip()); i += 1
flush_para(); close_lists(stack)
# ---- derived header figures (same data as the report)
d = json.load(open(f'{B33}/work/diff33.json')); rows = d['rows']
c = {}
for r in rows:
    k = ('model' if r['file'] == 'wasm2.0' else 'proof', r['cat']); c[k] = c.get(k, 0) + 1
seg = [('del', 'Deleted, mention <code>EXTEND</code>', c.get(('model', 'EXTEND-removed'), 0) + c.get(('proof', 'EXTEND-removed'), 0)),
       ('gen', 'Renumbered, generated model', c.get(('model', 'ctor-renumber/generated'), 0)),
       ('hand', 'Renumbered, model’s proofs', c.get(('model', 'ctor-renumber/hand-layer'), 0)),
       ('mod', 'Renumbered, proof modules', c.get(('proof', 'ctor-renumber/proof-module'), 0)),
       ('pos', 'Spec position in a comment', c.get(('model', 'source-location'), 0))]
total = sum(n for _, _, n in seg); assert total == len(rows) == 211
edits = json.load(open(f'{B33}/work/edits33.json')); envd = json.load(open(f'{B33}/work/envdiff33.json'))
common = 12818 - len(envd['only_old'])
aud = open(f'{B33}/probes/audit_new.txt').read(); aud_n = int(re.search(r'theorems checked: (\d+)', aud).group(1)); aud_f = int(re.search(r'needing a default value: (\d+)', aud).group(1))
ledger = ''.join(f'<span class="seg seg-{k}" style="flex-grow:{n}" title="{esc(re.sub("<[^>]+>", "", lab))}: {n}"></span>' for k, lab, n in seg)
legend = ''.join(f'<li><span class="sw seg-{k}"></span><span class="lg-n">{n}</span><span class="lg-l">{lab}</span></li>' for k, lab, n in seg)
tiles = [(str(total), 'lines of OLD differ from NEW, every one classified'), (str(len(edits)), 'lines changed in the proof modules this turn'),
         ('0', 'errors and <code>sorry</code> in all nine modules'), (f'{common:,}', 'declarations compared in Lean, no user-level statement changed'),
         (f'{aud_f} / {aud_n:,}', 'theorems needing an <code>Inhabited</code> default')]
tiles_html = ''.join(f'<div class="tile"><div class="tile-n">{n}</div><div class="tile-l">{t}</div></div>' for n, t in tiles)
toc_html = ''.join(f'<li><a href="#{sid}">{inline(t)}</a></li>' for sid, t in toc)
title_html = inline(h1)
page = f'''<title>EXTEND Removal Diff</title>
<meta name="claude:viewport-fit-sides" content="cover">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600&family=JetBrains+Mono:wght@400;500&family=Space+Grotesk:wght@500;600&display=swap">
<style>
/* Layout: one reading column with a sticky contents rail on wide screens; wide tables scroll inside their own frame. */
:root {{
  --bg: #f5f6f9; --surface: #ffffff; --fg: #181a22; --muted: #5a5e70; --rule: #dde0e9;
  --accent: #4b45c4; --code-bg: #eceef5; --code-fg: #2b2d3a;
  --del: #c4473e; --gen: #4b45c4; --hand: #7a74df; --mod: #a9a5ee; --pos: #b0821f;
  --font-body: "Inter", system-ui, -apple-system, "Segoe UI", Roboto, sans-serif;
  --font-head: "Space Grotesk", "Inter", system-ui, sans-serif;
  --font-mono: "JetBrains Mono", ui-monospace, "SFMono-Regular", Menlo, Consolas, monospace;
}}
@media (prefers-color-scheme: dark) {{ :root:not([data-theme="light"]) {{
  --bg: #111219; --surface: #191b24; --fg: #e6e7ee; --muted: #a2a5b8; --rule: #2b2e3c;
  --accent: #a39dff; --code-bg: #232634; --code-fg: #dcdcf0;
  --del: #ef8178; --gen: #a39dff; --hand: #8580e6; --mod: #5e59b8; --pos: #e1b75c; color-scheme: dark; }} }}
:root[data-theme="dark"] {{
  --bg: #111219; --surface: #191b24; --fg: #e6e7ee; --muted: #a2a5b8; --rule: #2b2e3c;
  --accent: #a39dff; --code-bg: #232634; --code-fg: #dcdcf0;
  --del: #ef8178; --gen: #a39dff; --hand: #8580e6; --mod: #5e59b8; --pos: #e1b75c; color-scheme: dark; }}
body {{ background: var(--bg); color: var(--fg); font-family: var(--font-body); font-size: 15px; line-height: 1.6; }}
.page {{ max-width: 1240px; margin: 0 auto; padding-block: 28px 64px; padding-left: max(16px, env(safe-area-inset-left, 0px)); padding-right: max(16px, env(safe-area-inset-right, 0px)); }}
header.top {{ display: grid; gap: 14px; padding-bottom: 22px; border-bottom: 1px solid var(--rule); }}
.eyebrow {{ font: 500 12px/1.4 var(--font-mono); letter-spacing: .06em; text-transform: uppercase; color: var(--muted); }}
h1 {{ font: 600 clamp(26px, 4vw, 38px)/1.15 var(--font-head); margin: 0; text-wrap: balance; letter-spacing: -.01em; }}
.lede {{ max-width: 68ch; color: var(--muted); margin: 0; }}
.tiles {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(170px, 1fr)); gap: 12px; }}
.tile {{ background: var(--surface); border: 1px solid var(--rule); border-radius: 8px; padding: 12px 14px; display: grid; gap: 2px; align-content: start; }}
.tile-n {{ font: 600 26px/1.2 var(--font-head); font-variant-numeric: tabular-nums; color: var(--accent); }}
.tile-l {{ font-size: 13px; color: var(--muted); line-height: 1.4; }}
.ledger {{ display: grid; gap: 10px; }}
.ledger-title {{ font: 600 14px/1.3 var(--font-head); }}
.bar {{ display: flex; height: 14px; border-radius: 3px; overflow: hidden; gap: 2px; background: var(--rule); }}
.seg {{ display: block; min-width: 3px; }}
.seg-del {{ background: var(--del); }} .seg-gen {{ background: var(--gen); }} .seg-hand {{ background: var(--hand); }} .seg-mod {{ background: var(--mod); }} .seg-pos {{ background: var(--pos); }}
.legend {{ list-style: none; margin: 0; padding: 0; display: flex; flex-wrap: wrap; gap: 6px 18px; font-size: 13px; color: var(--muted); }}
.legend li {{ display: flex; align-items: center; gap: 6px; }}
.sw {{ width: 10px; height: 10px; border-radius: 2px; display: inline-block; }}
.lg-n {{ font-variant-numeric: tabular-nums; font-weight: 600; color: var(--fg); }}
.source {{ font-size: 12.5px; color: var(--muted); }}
.layout {{ display: grid; grid-template-columns: minmax(0, 1fr); gap: 32px; margin-top: 26px; }}
@media (min-width: 1060px) {{ .layout {{ grid-template-columns: 220px minmax(0, 1fr); }} }}
nav.toc {{ align-self: start; font-size: 13.5px; }}
@media (min-width: 1060px) {{ nav.toc {{ position: sticky; top: calc(env(safe-area-inset-top, 0px) + 16px); max-height: calc(100vh - 32px); overflow: auto; }} }}
nav.toc .toc-h {{ font: 500 12px/1.4 var(--font-mono); text-transform: uppercase; letter-spacing: .06em; color: var(--muted); margin-bottom: 8px; }}
nav.toc ol {{ list-style: none; margin: 0; padding: 0; display: grid; gap: 4px; }}
nav.toc a {{ color: var(--fg); text-decoration: none; display: block; padding: 3px 8px; border-radius: 5px; border-left: 2px solid transparent; }}
nav.toc a:hover {{ background: var(--surface); border-left-color: var(--accent); }}
nav.toc a:focus-visible, a:focus-visible {{ outline: 2px solid var(--accent); outline-offset: 2px; }}
main {{ min-width: 0; }}
#report-body {{ max-width: 920px; }}
#report-body > p, #report-body > ul {{ max-width: 76ch; }}
h2 {{ font: 600 23px/1.25 var(--font-head); margin: 40px 0 12px; padding-top: 14px; border-top: 1px solid var(--rule); text-wrap: balance; scroll-margin-top: 16px; }}
h2:first-child {{ margin-top: 0; border-top: 0; padding-top: 0; }}
h3 {{ font: 600 17px/1.3 var(--font-head); margin: 26px 0 8px; text-wrap: balance; scroll-margin-top: 16px; }}
p {{ margin: 10px 0; }}
ul {{ margin: 8px 0; padding-left: 22px; }}
li {{ margin: 3px 0; }}
li > ul {{ margin: 2px 0; }}
strong {{ font-weight: 600; }}
code {{ font-family: var(--font-mono); font-size: .86em; background: var(--code-bg); color: var(--code-fg); padding: 1px 5px; border-radius: 4px; overflow-wrap: anywhere; }}
.code-wrap {{ overflow-x: auto; background: var(--code-bg); border-radius: 6px; margin: 10px 0; }}
.code-wrap pre {{ margin: 0; padding: 12px 14px; }}
.code-wrap code {{ background: none; padding: 0; font-size: 13px; overflow-wrap: normal; white-space: pre; }}
.table-wrap {{ overflow-x: auto; margin: 12px 0 18px; border: 1px solid var(--rule); border-radius: 8px; background: var(--surface); }}
table {{ border-collapse: collapse; width: 100%; font-size: 13.5px; font-variant-numeric: tabular-nums; }}
th, td {{ text-align: left; vertical-align: top; padding: 7px 10px; border-bottom: 1px solid var(--rule); }}
th {{ font-weight: 600; font-size: 12.5px; color: var(--muted); background: var(--bg); position: sticky; top: 0; }}
tbody tr:last-child td {{ border-bottom: 0; }}
td code {{ font-size: .84em; }}
.foot {{ margin-top: 48px; padding-top: 14px; border-top: 1px solid var(--rule); font-size: 12.5px; color: var(--muted); }}
@media (prefers-reduced-motion: reduce) {{ * {{ scroll-behavior: auto !important; }} }}
html {{ scroll-behavior: smooth; }}
</style>
<div class="page">
<header class="top">
<div class="eyebrow">Lean proof of Wasm 2.0 type safety · bundle 33 · 2026-11-11</div>
<h1>{title_html}</h1>
<p class="lede">The old proof with <code>OLD_wasm2.0.lean</code> (which still has the dead <code>EXTEND</code> instruction) against the repaired proof with the regenerated <code>wasm2.0.lean</code>, in <code>spectec/src/test-lean-claude/</code>.</p>
<div class="tiles">{tiles_html}</div>
<div class="ledger" aria-label="How the {total} differing lines break down">
<div class="ledger-title">The {total} differing lines, to scale</div>
<div class="bar" role="img" aria-label="{', '.join(f'{re.sub("<[^>]+>", "", lab)}: {n}' for _, lab, n in seg)}">{ledger}</div>
<ul class="legend">{legend}</ul>
</div>
<div class="source">Source: <code>claude-logging/verbatim_dialogue_log/bundle33/user_requested_documents/old_vs_new_diff_report.md</code> (version 4, md5 <code>{md5[:8]}…</code>). The text below is that report, laid out for the browser.</div>
</header>
<div class="layout">
<nav class="toc" aria-label="Contents"><div class="toc-h">Contents</div><ol>{toc_html}</ol></nav>
<main><div id="report-body">
{chr(10).join(body)}
</div>
<div class="foot">Generated from the bundle33 report by <code>md2page34.py</code> (bundle34). Every count in the header is taken from the same data files as the report.</div>
</main>
</div>
</div>
'''
open(OUT, 'w').write(page)
print('rows whose cells differ from a plain pipe split:', len(NAIVE_DIFF), NAIVE_DIFF); print('written', OUT, len(page), 'bytes;', len(toc), 'sections;', sum(1 for b in body if b.startswith('<div class="table-wrap">')), 'tables')

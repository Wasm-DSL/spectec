"""Splice prover results into a copy of TypeProgress.lean.
Usage: python3 merge_proofs.py <journal.jsonl> <in.lean> <out.lean>
Replaces, for each proved target, the first `:= sorry` (or `:= by sorry`, or a `sorry` line) after its
header with `:= by\n<proof>` (or `:=\n<term>` for term-mode def bodies), adding `noncomputable` if needed."""
import json, re, sys
J, IN, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
proofs = {}
for l in open(J):
    try: d = json.loads(l)
    except Exception: continue
    if d.get("type") != "result": continue
    r = d.get("result")
    if isinstance(r, str):
        try: r = json.loads(r)
        except Exception: continue
    if not isinstance(r, dict) or "results" not in r: continue
    for x in r["results"]:
        if x.get("status") == "proved" and x.get("proof", "").strip():
            proofs[x["name"]] = x
src = open(IN).read()
applied, failed = [], []
for name, x in proofs.items():
    m = re.search(r"^((?:private )?(?:noncomputable )?(?:theorem|def) " + re.escape(name) + r")(?=[\s:({\[])", src, re.M)
    if not m: failed.append((name, "header not found")); continue
    start = m.start()
    nxt = re.search(r"^(?:/--|-- @@|theorem |def |private |noncomputable |end TLC)", src[m.end():], re.M)
    stop = m.end() + (nxt.start() if nxt else len(src) - m.end())
    block = src[start:stop]
    pm = re.search(r":=[ \t]*\n?[ \t]*(?:by[ \t]*\n?[ \t]*)?sorry[ \t]*$", block, re.M)
    if not pm: failed.append((name, "no sorry body")); continue
    body = x["proof"].rstrip()
    lines = body.split("\n")
    # normalise indentation to 2 spaces
    ind = min((len(l) - len(l.lstrip()) for l in lines if l.strip()), default=0)
    lines = ["  " + l[ind:] if l.strip() else "" for l in lines]
    is_term = x.get("notes", "").lower().startswith("term:")
    new_tail = (":=\n" if is_term else ":= by\n") + "\n".join(lines)
    newblock = block[:pm.start()] + new_tail + block[pm.end():]
    if x.get("needs_noncomputable") and not newblock.startswith("noncomputable"):
        newblock = "noncomputable " + newblock
    src = src[:start] + newblock + src[stop:]
    applied.append(name)
open(OUT, "w").write(src)
print("proved results:", len(proofs), "applied:", len(applied), "failed:", failed)

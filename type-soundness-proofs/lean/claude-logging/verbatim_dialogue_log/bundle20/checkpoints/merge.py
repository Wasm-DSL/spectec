"""Assemble TypeProgress.lean in Rocq order from: header, documented defs, chunk outputs
(with `-- @@ name` markers), motives/case lemmas/main theorems (from TypeProgress_initial.lean)."""
import json, re, sys
P = "/tmp/claude-1000/-home-zhengyew-spectec/159a29a7-9080-4c0e-830f-ae0ec8fb4c8d/scratchpad/progress/"
inv = json.load(open(P + "inventory.json"))
init = open(P + "TypeProgress_initial.lean").read()
header = init[:init.index("namespace TLC") + len("namespace TLC\n\n")]
defs_txt = open(P + "defs_documented.lean").read()
# split defs file into top-level blocks separated by blank lines
blocks = [b.strip("\n") for b in re.split(r"\n\s*\n(?=/--|--|def )", defs_txt) if b.strip()]
defblk = {}
notported_eq = None; scheme1 = None
for b in blocks:
    m = re.search(r"^def ([A-Za-z0-9_']+)", b, re.M)
    if m: defblk[m.group(1)] = b
    elif "instr_eqb" in b: notported_eq = b
    elif "Scheme Instr_ok_ind'" in b: scheme1 = b
# motives / cases / mains from the initial file
i_motbe = init.index("/-- Lean-only (bundle20): Rocq's motive `P` (for `Instr_ok`)")
i_mote = init.index("/-- Lean-only (bundle20): Rocq's motive `P` (for `Instr_ok2`)")
i_cases = init.index("/-- Lean-only (bundle20): the `Instr_ok.nop`")
i_ecases = init.index("/-- Lean-only (bundle20): the `plain` case")
i_mainbe = init.index("/-- Rocq `type_progress.v:3086` `t_progress_be`")
i_ioi = init.index("/-- Rocq `type_progress.v:5515` `Instr_ok_Instrs_ok`")
i_maine = init.index("/-- Rocq `type_progress.v:5536` `t_progress_e`")
i_main = init.index("/-- Rocq `type_progress.v:6064` `t_progress`")
i_end = init.index("end TLC")
mot_be = init[i_motbe:i_mote]; mot_e = init[i_mote:i_cases]
cases_be = init[i_cases:i_ecases]; cases_e = init[i_ecases:i_mainbe]
main_be = init[i_mainbe:i_ioi]; ioi = init[i_ioi:i_maine]; main_e = init[i_maine:i_main]; main = init[i_main:i_end]
# chunk segments
segs = {}
for k in range(1, 7):
    try: code = open(P + f"chunk{k}.lean").read()
    except FileNotFoundError: continue
    parts = re.split(r"^-- @@ ([A-Za-z0-9_']+)\s*$", code, flags=re.M)
    for j in range(1, len(parts), 2):
        segs[parts[j]] = parts[j + 1].strip("\n")
out = [header.rstrip("\n") + "\n"]
missing = []
emitted_np_eq = False
for r in inv:
    nm, kind, line = r["name"], r["kind"], r["start"]
    if kind in ("Definition", "Fixpoint"):
        if nm in defblk: out.append(defblk[nm])
        elif nm in ("instr_eqb", "eqinstrP"):
            if not emitted_np_eq: out.append(notported_eq); emitted_np_eq = True
        else: missing.append(nm)
    elif kind == "Ltac":
        out.append(f"-- Ltac `{nm}` (type_progress.v:{line}) NOT PORTED: proof automation; the Lean proofs do\n-- this inline.")
    elif kind == "Scheme":
        if nm == "Instr_ok_ind'": out.append(scheme1)
        else: out.append("-- `Scheme Instr_ok2_ind'`/`Admin_instrs_ok_ind'`/`Expr_ok2_ind'` (type_progress.v:5524) NOT PORTED:\n-- Lean auto-generates the mutual recursor `Instrs_ok2.rec`, used by `t_progress_e` below.")
    elif nm == "t_progress_be": out.append(mot_be.strip("\n")); out.append(cases_be.strip("\n")); out.append(main_be.strip("\n"))
    elif nm == "Instr_ok_Instrs_ok": out.append(ioi.strip("\n"))
    elif nm == "t_progress_e": out.append(mot_e.strip("\n")); out.append(cases_e.strip("\n")); out.append(main_e.strip("\n"))
    elif nm == "t_progress": out.append(main.strip("\n"))
    elif nm in segs: out.append(segs[nm])
    else: missing.append(nm)
out.append("end TLC\n")
src = "\n\n".join(x for x in out if x)
open(P + "TypeProgress_merged.lean", "w").write(src)
print("segments:", len(segs), "missing:", len(missing), missing[:40])

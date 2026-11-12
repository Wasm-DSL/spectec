#!/usr/bin/env bash
# bundle31 final assembly + verification (scratch only; never writes into the repository).
# 1. merge the agents' working copies into the bases (units31.py merge) and apply the post-merge
#    patch (bounded mem_bytes_wf); 2. build ALL modules from source into a fresh build dir (only
#    the Mathlib package oleans are reused); 3. report errors/warnings per module, `sorry`
#    occurrences, the project-wide axiom audit and the default-value audit.
# Usage: final31.sh <outdir under b31/>   (agents' copies are read from b31/agents/<label>/)
set -uo pipefail
SP=/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad
B=$SP/b31; P=/home/zhengyew/spectec/spectec/src/test-lean-claude
O=$(realpath -m "$1"); case "$O" in $B/*) ;; *) echo "outdir must be under $B"; exit 2;; esac
rm -rf "$O"; mkdir -p "$O/src" "$O/build" "$O/logs"
A=$B/agents
names() { tr -d '\n' < "$A/$1/assigned.txt"; }
python3 $B/tools/units31.py merge $B/cascade2/src/TypePreservation.lean "$O/src/TypePreservation.lean" \
  "$A/P1/TypePreservation.lean:$(names P1)" "$A/P23/TypePreservation.lean:$(names P23)" || exit 1
ARGS=()
for l in Q1 Q2 Q3 Q4 Q5 Q6a Q6b; do ARGS+=("$A/$l/TypeProgress.lean:$(names $l)"); done
python3 $B/tools/units31.py merge $B/cascade2/src/TypeProgress.lean "$O/src/TypeProgress.lean" "${ARGS[@]}" || exit 1
python3 $B/tools/postpatch31.py "$O/src/TypeProgress.lean" || exit 1
python3 $B/tools/docpatch31.py "$O/src" || exit 1
cp $P/ExtendedDeriveDecEq.lean $P/wasm2.0.lean "$O/src/"
cp $B/src2/HelperLemmas.lean $B/src2/ExtensionLemmas.lean "$O/src/"
cp $B/orig/Subtyping.lean $B/orig/TypingLemmas.lean $B/orig/TypePreservationPure.lean "$O/src/"
python3 $B/tools/cleanup31.py "$O/src" || exit 1
for m in ExtendedDeriveDecEq wasm2.0 HelperLemmas Subtyping TypingLemmas TypePreservationPure ExtensionLemmas TypePreservation TypeProgress; do
  LRUN_MAXERR=100000 $B/tools/lrun31.sh "$O/build" "$O/src" "$m.lean" -o "$O/build/$m.olean" > "$O/logs/$m.log" 2>&1
  echo "$m: exit $? errors $(grep -c ': error' "$O/logs/$m.log") warnings $(grep -c ': warning' "$O/logs/$m.log") $(grep WALL "$O/logs/$m.log")"
done
echo "--- sorry tokens outside comments, per downstream module"
for m in HelperLemmas Subtyping TypingLemmas TypePreservationPure ExtensionLemmas TypePreservation TypeProgress; do
  echo "$m: $(python3 -c "
import re,sys
t=open('$O/src/$m.lean').read()
t=re.sub(r'/-.*?-/','',t,flags=re.S); t=re.sub(r'--[^\n]*','',t)
print(len(re.findall(r'(?<![\w.])sorry(?![\w])',t)))")"
done
mkdir -p "$O/axcheck" && cp $B/axcheck/AxCheck.lean "$O/axcheck/"
$B/tools/lrun31.sh "$O/build" "$O/axcheck" AxCheck.lean > "$O/logs/axcheck.log" 2>&1
echo "--- axiom audit"; grep -v '^WALL' "$O/logs/axcheck.log" | cut -c1-3000
mkdir -p "$O/audit" && cp $B/audit/RunAuditAll.lean "$O/audit/"
( cd "$O/audit" && AUDIT_BUILD="$O/build" AUDIT_OUT="$O/audit/report.txt" $B/tools/lrun31.sh "$O/build" "$O/audit" RunAuditAll.lean > "$O/logs/audit.log" 2>&1 )
echo "--- default-value audit"; head -c 3000 "$O/audit/report.txt"

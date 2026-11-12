#!/usr/bin/env bash
# Safety check + comparison against a baseline (added bundle20, 2026-10-05; hardened the same
# day after a race was observed when ~11 subagents ran checks concurrently).
#
# Captures `git status --porcelain` exactly like check.sh does, but writes it to a UNIQUE file
# in this directory (sub-second UTC timestamp + label + PID), so concurrent runs can never
# write the same file; then compares every line NOT mentioning spectec/src/test-lean-claude
# against a baseline check file, using `grep -a` so a file can never be misread as binary.
# Prints "VERIFIED: ..." when nothing new changed outside the target directory; otherwise
# prints the difference and exits 1.
#
# Usage (from anywhere inside the repo):
#   bash spectec/src/test-lean-claude/claude-logging/safety-checks/verify_against_baseline.sh [BASELINE] [LABEL]
# BASELINE defaults to the bundle20 baseline (an empty string also selects the default).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
D=spectec/src/test-lean-claude/claude-logging/safety-checks
BASE="${1:-$D/check-20261005T051653Z.txt}"
LABEL="${2:-main}"
SAFE_LABEL=$(printf '%s' "$LABEL" | tr -c 'A-Za-z0-9_-' '_')
TS=$(date -u +%Y%m%dT%H%M%S.%NZ)
OUT="$D/check-${TS}-${SAFE_LABEL}-$$.txt"
TMP="$OUT.partial"
{
  echo "=== Safety check at ${TS} (label: ${LABEL}, pid $$) ==="
  echo "--- git status (porcelain) ---"
  git status --porcelain
  echo ""
  echo "--- Any changes outside spectec/src/test-lean-claude/ ? ---"
  git status --porcelain | awk '{print $2}' | grep -v '^spectec/src/test-lean-claude/' || echo "NONE (clean outside target dir)"
} > "$TMP"
mv "$TMP" "$OUT"
echo "safety check [$LABEL] new=$OUT baseline=$BASE"
if diff <(grep -a -v test-lean-claude "$BASE" | grep -a -v '^=== Safety') \
        <(grep -a -v test-lean-claude "$OUT" | grep -a -v '^=== Safety') > /dev/null; then
  echo "VERIFIED: zero new changes outside spectec/src/test-lean-claude"
else
  echo "DIFFERENCE FOUND (lines outside spectec/src/test-lean-claude differ from baseline):"
  diff <(grep -a -v test-lean-claude "$BASE" | grep -a -v '^=== Safety') \
       <(grep -a -v test-lean-claude "$OUT" | grep -a -v '^=== Safety') || true
  exit 1
fi

#!/usr/bin/env bash
# Safety check: verify no files outside spectec/test-lean/test-lean-claude/ have been
# created, modified, or deleted since the baseline snapshot (00-baseline-git-status.txt)
# taken at the start of the "translate Rocq/Isabelle proofs into Lean" task.
#
# Usage: run from the repo root (/home/zhengyew/spectec):
#   bash spectec/test-lean/test-lean-claude/safety-checks/check.sh
#
# Writes a timestamped report into this same directory and exits non-zero if
# any out-of-scope change is detected.

set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

SCRIPT_DIR="spectec/test-lean/test-lean-claude/safety-checks"
BASELINE="$SCRIPT_DIR/00-baseline-git-status.txt"
TS="$(date -u +%Y%m%dT%H%M%SZ)"
OUT="$SCRIPT_DIR/check-$TS.txt"

CURRENT_STATUS="$(git status --porcelain)"

# Lines belonging to the baseline (pre-existing dirty/untracked state, none of it
# inside test-lean-claude since that folder didn't exist yet).
BASELINE_CONTENT="$(cat "$BASELINE")"

# Any current status line that is NOT in the baseline AND NOT inside
# spectec/test-lean/test-lean-claude/ is an out-of-scope change.
NEW_OUT_OF_SCOPE="$(comm -13 \
  <(echo "$BASELINE_CONTENT" | sort) \
  <(echo "$CURRENT_STATUS" | sort) \
  | grep -v 'test-lean/test-lean-claude/' || true)"

{
  echo "Safety check run at $TS"
  echo "Baseline: $BASELINE"
  echo
  echo "=== Full current git status --porcelain ==="
  echo "$CURRENT_STATUS"
  echo
  echo "=== Lines new since baseline AND outside test-lean-claude/ (should be EMPTY) ==="
  echo "$NEW_OUT_OF_SCOPE"
} > "$OUT"

echo "Report written to $OUT"

if [ -n "$NEW_OUT_OF_SCOPE" ]; then
  echo "FAIL: out-of-scope changes detected:"
  echo "$NEW_OUT_OF_SCOPE"
  exit 1
else
  echo "PASS: no out-of-scope changes detected."
fi

#!/usr/bin/env bash
# Periodic safety check: verify no files outside spectec/src/test-lean-claude/
# have been modified by this Claude session's work.
# Run from repo root (/home/zhengyew/spectec).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
TS=$(date -u +%Y%m%dT%H%M%SZ)
OUT="spectec/src/test-lean-claude/claude-logging/safety-checks/check-${TS}.txt"
{
  echo "=== Safety check at ${TS} ==="
  echo "--- git status (porcelain) ---"
  git status --porcelain
  echo ""
  echo "--- Any changes outside spectec/src/test-lean-claude/ ? ---"
  git status --porcelain | awk '{print $2}' | grep -v '^spectec/src/test-lean-claude/' || echo "NONE (clean outside target dir)"
} > "$OUT"
cat "$OUT"

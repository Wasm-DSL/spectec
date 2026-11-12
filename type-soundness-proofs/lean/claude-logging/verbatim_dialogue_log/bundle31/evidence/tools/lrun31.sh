#!/usr/bin/env bash
# bundle31 serialized, memory-capped Lean runner.
# Usage: lrun31.sh <build-dir under b31/> <work-dir> <file.lean> [extra lean args, e.g. -o out.olean]
# LEAN_PATH = the given scratch build dir first, then ONLY the Mathlib/package oleans of the project
# (read-only; never the project's own .lake/build oleans). Takes the session-wide lock file, so at
# most one Lean process of this session (main session and all subagents) runs at any time.
# Never call lake. Never write into the repository.
set -uo pipefail
SP=/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad
B=$SP/b31
P=/home/zhengyew/spectec/spectec/src/test-lean-claude
BD=$(realpath -m "$1"); WD=$(realpath -m "$2"); shift 2
case "$BD" in $B/*) ;; *) echo "lrun31: build dir must be under $B" >&2; exit 2;; esac
case "$WD" in $SP/*) ;; *) echo "lrun31: work dir must be under $SP" >&2; exit 2;; esac
for a in "$@"; do case "$a" in /home/*|$P*) echo "lrun31: refusing path argument inside the repo: $a" >&2; exit 2;; esac; done
LP=$BD
for d in $P/.lake/packages/*/.lake/build/lib/lean; do LP=$LP:$d; done
cd "$WD" || exit 2
exec 9>$SP/lean.lock
flock 9
/usr/bin/time -f "WALL %e s  MAXRSS %M KB" systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 --quiet env LEAN_PATH=$LP nice -n 10 $HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -j 4 -DmaxErrors=${LRUN_MAXERR:-200} "$@"

#!/usr/bin/env bash
# bundle33: compile the 9 project modules of one scratch state (old|new|...) serially, in dependency order,
# via lrun33.sh (session lock, 12 GB cap, bare toolchain lean, never lake, never the repo's .lake/build).
# Usage: chain33.sh <state> [first-module] [last-module]. Logs to <state>/logs/<M>.log. Stops at the first
# module with errors (Lean writes no .olean for it, so later modules cannot be checked).
set -uo pipefail
B=/tmp/claude-1002/-home-zhengyew-spectec/0793c03a-21df-4d2d-9729-4ba22978b528/scratchpad/b33
S=$1; FIRST=${2:-ExtendedDeriveDecEq}; LAST=${3:-TypeProgress}
ORDER="ExtendedDeriveDecEq wasm2.0 HelperLemmas Subtyping TypingLemmas TypePreservationPure ExtensionLemmas TypePreservation TypeProgress"
mkdir -p $B/$S/logs $B/$S/build
on=0
for M in $ORDER; do
  [ "$M" = "$FIRST" ] && on=1
  [ $on = 1 ] || continue
  rm -f $B/$S/build/$M.olean $B/$S/build/$M.ilean
  $B/tools/lrun33.sh $B/$S/build $B/$S/src $M.lean -o $B/$S/build/$M.olean -i $B/$S/build/$M.ilean > $B/$S/logs/$M.log 2>&1
  rc=$?
  ne=$(grep -c ": error" $B/$S/logs/$M.log); nw=$(grep -c ": warning" $B/$S/logs/$M.log); ns=$(grep -c -E "declaration uses ['\`]sorry['\`]" $B/$S/logs/$M.log)  # bundle33 fix: Lean 4.32 prints backticks
  echo "$S $M rc=$rc errors=$ne warnings=$nw sorry-warnings=$ns olean=$([ -f $B/$S/build/$M.olean ] && echo yes || echo NO) $(grep -o 'WALL.*' $B/$S/logs/$M.log)"
  if [ $rc != 0 ] || [ ! -f $B/$S/build/$M.olean ]; then echo "STOP at $M"; exit 1; fi
  [ "$M" = "$LAST" ] && break
done

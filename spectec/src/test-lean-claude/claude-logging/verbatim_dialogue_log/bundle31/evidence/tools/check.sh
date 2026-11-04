#!/usr/bin/env bash
# bundle31 safety check. Read-only on the repo, except that the report itself is written to
# claude-logging/safety-checks/. Verifies that since the bundle31 baseline nothing changed except
# the downstream proof modules of spectec/src/test-lean-claude (HelperLemmas, Subtyping,
# TypingLemmas, TypePreservationPure, ExtensionLemmas, TypePreservation, TypeProgress .lean) and
# spectec/src/test-lean-claude/claude-logging/**.
# Usage: check.sh <label>
set -uo pipefail
SP=/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad
B=$SP/b31; L=${1:-check}; TS=$(date -u +%Y%m%dT%H%M%S.%NZ)
cd /home/zhengyew/spectec
T=spectec/src/test-lean-claude
OUT=$T/claude-logging/safety-checks/check-${TS}-bundle31-${L}-$$.txt
W=$B/checks/$L-$TS; mkdir -p $W
ALLOWED="HelperLemmas Subtyping TypingLemmas TypePreservationPure ExtensionLemmas TypePreservation TypeProgress"
{
echo "=== bundle31 safety check [$L] at $TS (pid $$); baseline marker $(cat $B/baseline/marker_time.txt)"
echo "Allowed to change this turn: $T/{$(echo $ALLOWED | tr ' ' ',')}.lean and $T/claude-logging/**"
echo "--- 1. git status (porcelain, lock-free) vs bundle31 baseline (lines: < baseline, > now)"
GIT_OPTIONAL_LOCKS=0 git status --porcelain --ignore-submodules=all > $W/git_status.txt
diff $B/baseline/git_status.txt $W/git_status.txt && echo "IDENTICAL to baseline ($(wc -l < $W/git_status.txt) entries)"
echo "--- 2. HEAD"
GIT_OPTIONAL_LOCKS=0 git rev-parse HEAD | diff $B/baseline/head.txt - && echo "HEAD unchanged ($(cat $B/baseline/head.txt))"
echo "--- 3. paths in the repo (outside .git) modified or created after the marker, excluding claude-logging"
find . -path ./.git -prune -o -newer $B/baseline/MARKER -print | grep -v "^./$T/claude-logging" > $W/newer.txt
cat $W/newer.txt; echo "($(wc -l < $W/newer.txt) paths; expected at most ./$T and the allowed .lean files)"
echo "--- 4. .git entries (depth <= 2) modified after the marker"
find .git -maxdepth 2 -newer $B/baseline/MARKER -print > $W/git_newer.txt; cat $W/git_newer.txt; echo "($(wc -l < $W/git_newer.txt) paths)"
echo "--- 5. content checksums under $T (except .lake/packages and claude-logging) vs baseline"
(find $T -path "$T/.lake/packages" -prune -o -path "$T/claude-logging" -prune -o -type f -print0 | sort -z | xargs -0 md5sum) > $W/tlc_md5.txt
grep -v " $T/claude-logging/" $B/baseline/tlc_md5.txt | diff - $W/tlc_md5.txt; echo "(files at baseline excl. logging: $(grep -vc " $T/claude-logging/" $B/baseline/tlc_md5.txt), now: $(wc -l < $W/tlc_md5.txt))"
echo "--- 6. .lake/packages entries (depth <= 2): mtimes vs baseline"
(find $T/.lake/packages -maxdepth 2 -printf '%T@ %p\n' | sort -k2) > $W/pkg_mtimes.txt
diff $B/baseline/pkg_mtimes.txt $W/pkg_mtimes.txt && echo "IDENTICAL"
echo "--- 7. verdict"
EXCL=(-e "./$T")
for m in $ALLOWED; do EXCL+=(-e "./$T/$m.lean"); done
: > $W/benign.txt
for pg in $T/.lake/packages/*/.git; do
  if grep -q -x "./$pg" $W/newer.txt && [ -z "$(find $pg -mindepth 1 -newer $B/baseline/MARKER -print -quit)" ]; then
    EXCL+=(-e "./$pg"); echo "./$pg" >> $W/benign.txt
  fi
done
[ -s $W/benign.txt ] && echo "benign lock churn (package .git directory mtime only, no newer file inside; see the bundle31 note-git-lock-churn report): $(wc -l < $W/benign.txt) paths"
NB=$T/.lake/build/lib/lean/wasm2.0.trace.nobuild; EXTMD5=""
if [ -f $NB ] && [ "$(md5sum < $NB | cut -c1-32)" = "$(cat $B/baseline/external_nobuild_md5.txt 2>/dev/null)" ]; then
  EXCL+=(-e "./$NB" -e "./$T/.lake/build/lib/lean"); EXTMD5=" $NB\$"
  echo "external Lake/IDE artifact (not created by this session; see the bundle31 note-external-nobuild report): ./$NB, md5 unchanged since noted"
fi
BAD=$(cat $W/newer.txt | grep -v -x "${EXCL[@]}" | wc -l)
MEXCL="$(for m in $ALLOWED; do printf ' %s/%s.lean$\\|' "$T" "$m"; done)"
[ -n "$EXTMD5" ] && MEXCL="$MEXCL$EXTMD5\\|"
BADMD5=$(grep -v " $T/claude-logging/" $B/baseline/tlc_md5.txt | diff - $W/tlc_md5.txt | grep '^[<>]' | grep -v "${MEXCL%\\|}" | wc -l)
CHANGED=$(grep -v " $T/claude-logging/" $B/baseline/tlc_md5.txt | diff - $W/tlc_md5.txt | grep '^>' | awk '{print $3}' | sort -u | tr '\n' ' ')
echo "files with changed content (allowed or not): ${CHANGED:-none}"
if [ "$BAD" = 0 ] && [ "$BADMD5" = 0 ]; then echo "OK: nothing outside the allowed downstream .lean files and claude-logging changed since the baseline"; else echo "ATTENTION: $BAD unexpected newer paths, $BADMD5 unexpected checksum lines (see above; may be the user's own concurrent edits)"; fi
} > $W/report.txt 2>&1
cp $W/report.txt $OUT
echo "$OUT"; tail -3 $W/report.txt

#!/usr/bin/env bash
# bundle32 safety check. Read-only on the repo, except that the report itself is written to
# spectec/src/test-lean-claude/claude-logging/safety-checks/. Verifies that since the bundle32 baseline
# (taken before any work this turn) nothing changed except spectec/src/test-lean-claude/wasm2.0.lean and
# spectec/src/test-lean-claude/claude-logging/**. Usage: check32.sh <label>
set -uo pipefail
SP=/tmp/claude-1002/-home-zhengyew-spectec/0793c03a-21df-4d2d-9729-4ba22978b528/scratchpad
B=$SP/b32; L=${1:-check}; TS=$(date -u +%Y%m%dT%H%M%S.%NZ)
cd /home/zhengyew/spectec
T=spectec/src/test-lean-claude
OUT=$T/claude-logging/safety-checks/check-${TS}-bundle32-${L}-$$.txt
W=$B/checks/$L-$TS-$$; mkdir -p $W
{
echo "=== bundle32 safety check [$L] at $TS (pid $$); baseline marker $(cat $B/baseline/marker_time.txt)"
echo "Allowed to change this turn: $T/wasm2.0.lean and $T/claude-logging/**"
echo "--- 1. git status (porcelain, lock-free, submodules ignored) vs bundle32 baseline (< baseline, > now)"
GIT_OPTIONAL_LOCKS=0 git status --porcelain --ignore-submodules=all > $W/git_status.txt
diff $B/baseline/git_status.txt $W/git_status.txt && echo "IDENTICAL to baseline ($(wc -l < $W/git_status.txt) entries)"
echo "--- 2. HEAD"
GIT_OPTIONAL_LOCKS=0 git rev-parse HEAD | diff $B/baseline/head.txt - && echo "HEAD unchanged ($(cat $B/baseline/head.txt))"
echo "--- 3. paths in the repo (outside .git) modified or created after the marker, excluding claude-logging"
find . -path ./.git -prune -o -newer $B/baseline/MARKER -print | grep -v "^./$T/claude-logging" > $W/newer.txt
cat $W/newer.txt; echo "($(wc -l < $W/newer.txt) paths; allowed: ./$T/wasm2.0.lean)"
echo "--- 4. .git entries (depth <= 2) modified after the marker"
find .git -maxdepth 2 -newer $B/baseline/MARKER -print > $W/git_newer.txt; cat $W/git_newer.txt; echo "($(wc -l < $W/git_newer.txt) paths)"
echo "--- 5. content checksums under $T (except .lake/packages and claude-logging) vs baseline"
(find $T -path "$T/.lake/packages" -prune -o -path "$T/claude-logging" -prune -o -type f -print0 | sort -z | xargs -0 md5sum) > $W/tlc_md5.txt
diff $B/baseline/tlc_md5.txt $W/tlc_md5.txt; echo "(files at baseline: $(wc -l < $B/baseline/tlc_md5.txt), now: $(wc -l < $W/tlc_md5.txt))"
echo "--- 6. claude-logging: files changed or removed since baseline (additions are allowed and not listed)"
(find $T/claude-logging -type f -print0 | sort -z | xargs -0 md5sum) > $W/logging_md5.txt
comm -23 <(sort $B/baseline/logging_md5.txt) <(sort $W/logging_md5.txt) > $W/logging_changed.txt
cat $W/logging_changed.txt; echo "($(wc -l < $W/logging_changed.txt) pre-existing logging files changed or removed; $(( $(wc -l < $W/logging_md5.txt) - $(wc -l < $B/baseline/logging_md5.txt) )) net new)"
echo "--- 7. .lake/packages entries (depth <= 2): mtimes vs baseline"
(find $T/.lake/packages -maxdepth 2 -printf '%T@ %p\n' | sort -k2) > $W/pkg_mtimes.txt
diff $B/baseline/pkg_mtimes.txt $W/pkg_mtimes.txt && echo "IDENTICAL"
echo "--- 8. verdict"
EXCL=(-e "./$T/wasm2.0.lean")
: > $W/benign.txt
for pg in $T/.lake/packages/*/.git; do
  if grep -q -x "./$pg" $W/newer.txt && [ -z "$(find $pg -mindepth 1 -newer $B/baseline/MARKER -print -quit)" ]; then
    EXCL+=(-e "./$pg"); echo "./$pg" >> $W/benign.txt
  fi
done
[ -s $W/benign.txt ] && echo "benign lock churn (package .git directory mtime only, no newer file inside; cf. bundle31 note-git-lock-churn): $(wc -l < $W/benign.txt) paths"
BAD=$(grep -v -x "${EXCL[@]}" $W/newer.txt | wc -l)
BADMD5=$(diff $B/baseline/tlc_md5.txt $W/tlc_md5.txt | grep '^[<>]' | grep -v " $T/wasm2.0.lean$" | wc -l)
BADLOG=$(wc -l < $W/logging_changed.txt)
CHANGED=$(diff $B/baseline/tlc_md5.txt $W/tlc_md5.txt | grep '^>' | awk '{print $3}' | sort -u | tr '\n' ' ')
echo "files under $T (excl. logging) with changed content: ${CHANGED:-none}"
echo "wasm2.0.lean md5 now: $(md5sum < $T/wasm2.0.lean | cut -c1-32) (baseline $(grep " $T/wasm2.0.lean$" $B/baseline/tlc_md5.txt | cut -c1-32))"
GITBAD=$(diff $B/baseline/git_status.txt $W/git_status.txt | grep '^[<>]' | grep -v -e " $T/claude-logging/" -e " $T/wasm2.0.lean$" | wc -l)
echo "git status lines changed outside claude-logging and wasm2.0.lean: $GITBAD"
if [ "$BAD" = 0 ] && [ "$BADMD5" = 0 ] && [ "$BADLOG" = 0 ] && [ "$GITBAD" = 0 ]; then
  echo "OK: nothing outside $T/wasm2.0.lean and new files under $T/claude-logging changed since the baseline"
else
  echo "ATTENTION: $BAD unexpected newer paths, $BADMD5 unexpected checksum lines, $BADLOG pre-existing logging files changed, $GITBAD unexpected git status lines (see above; may be the user's own concurrent edits or the IDE)"
fi
} > $W/report.txt 2>&1
cp $W/report.txt $OUT
echo "$OUT"; tail -4 $W/report.txt

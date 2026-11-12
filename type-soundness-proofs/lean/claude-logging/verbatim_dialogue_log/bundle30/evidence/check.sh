#!/usr/bin/env bash
# bundle30 safety check. Read-only on the repo, except that the report itself is written to
# claude-logging/safety-checks/. Verifies that since the bundle30 baseline nothing changed except new
# files under claude-logging/verbatim_dialogue_log/bundle30/ and claude-logging/safety-checks/.
# Usage: check.sh <label>
set -uo pipefail
SP=/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad
B=$SP/b30; L=${1:-check}; TS=$(date -u +%Y%m%dT%H%M%S.%NZ)
cd /home/zhengyew/spectec
T=spectec/src/test-lean-claude
OUT=$T/claude-logging/safety-checks/check-${TS}-bundle30-${L}-$$.txt
W=$B/checks/$L; mkdir -p $W
{
echo "=== bundle30 safety check [$L] at $TS (pid $$); baseline marker $(cat $B/baseline/marker_time.txt)"
echo "Allowed to change this turn: new files under $T/claude-logging/verbatim_dialogue_log/bundle30/ and $T/claude-logging/safety-checks/"
echo "--- 1. git status (porcelain, lock-free) vs bundle30 baseline (lines: < baseline, > now)"
GIT_OPTIONAL_LOCKS=0 git status --porcelain --ignore-submodules=all > $W/git_status.txt
diff $B/baseline/git_status.txt $W/git_status.txt > $W/git_diff.txt && echo "IDENTICAL to baseline ($(wc -l < $W/git_status.txt) entries)"; cat $W/git_diff.txt
echo "--- 2. HEAD"
GIT_OPTIONAL_LOCKS=0 git rev-parse HEAD | diff $B/baseline/head.txt - && echo "HEAD unchanged ($(cat $B/baseline/head.txt))"
echo "--- 3. paths in the repo (outside .git) modified or created after the marker, excluding claude-logging"
find . -path ./.git -prune -o -newer $B/baseline/MARKER -print | grep -v "^./$T/claude-logging" > $W/newer.txt
cat $W/newer.txt; echo "($(wc -l < $W/newer.txt) paths; expected 0)"
echo "--- 4. .git entries (depth <= 2) modified after the marker (informational: the editor's git integration also touches these)"
find .git -maxdepth 2 -newer $B/baseline/MARKER -print > $W/git_newer.txt; cat $W/git_newer.txt; echo "($(wc -l < $W/git_newer.txt) paths)"
echo "--- 5. content checksums under $T (except .lake/packages, including claude-logging) vs baseline"
(find $T -path "$T/.lake/packages" -prune -o -type f -print0 | sort -z | xargs -0 md5sum) > $W/tlc_md5.txt
diff $B/baseline/tlc_md5.txt $W/tlc_md5.txt > $W/md5_diff.txt; cat $W/md5_diff.txt
echo "(files at baseline: $(wc -l < $B/baseline/tlc_md5.txt), now: $(wc -l < $W/tlc_md5.txt))"
echo "--- 6. .lake/packages entries (depth <= 2): mtimes vs baseline"
(find $T/.lake/packages -maxdepth 2 -printf '%T@ %p\n' | sort -k2) > $W/pkg_mtimes.txt
diff $B/baseline/pkg_mtimes.txt $W/pkg_mtimes.txt && echo "IDENTICAL"
echo "--- 7. verdict"
BADNEW=$(wc -l < $W/newer.txt)
BADMD5=$(grep '^[<>]' $W/md5_diff.txt | grep -v -E "^> [0-9a-f]{32}  $T/claude-logging/(verbatim_dialogue_log/bundle30/|safety-checks/)" | wc -l)
BADGIT=$(grep '^[<>]' $W/git_diff.txt | grep -v -E "^> \?\? $T/claude-logging/(verbatim_dialogue_log/bundle30/|safety-checks/)" | wc -l)
BADPKG=$(diff $B/baseline/pkg_mtimes.txt $W/pkg_mtimes.txt | grep -c '^[<>]')
if [ "$BADNEW" = 0 ] && [ "$BADMD5" = 0 ] && [ "$BADGIT" = 0 ] && [ "$BADPKG" = 0 ]; then echo "OK: since the baseline, nothing changed except new files under claude-logging/verbatim_dialogue_log/bundle30/ and claude-logging/safety-checks/"; else echo "ATTENTION: $BADNEW unexpected newer paths, $BADMD5 unexpected checksum lines, $BADGIT unexpected git-status lines, $BADPKG package mtime lines (see above; may be the user's own concurrent edits)"; fi
} > $W/report.txt 2>&1
cp $W/report.txt $OUT
echo "$OUT"; tail -3 $W/report.txt

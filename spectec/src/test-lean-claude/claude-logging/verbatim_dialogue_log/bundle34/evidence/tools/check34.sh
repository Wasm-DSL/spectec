#!/usr/bin/env bash
# bundle34 safety check. Read-only on the repo, except that the report itself is written to
# spectec/src/test-lean-claude/claude-logging/safety-checks/. Verifies that since the bundle34 baseline
# (taken before any work this turn) nothing changed except new files
# under spectec/src/test-lean-claude/claude-logging/. Usage: check33.sh <label>
set -uo pipefail
SP=/tmp/claude-1002/-home-zhengyew-spectec/0793c03a-21df-4d2d-9729-4ba22978b528/scratchpad
B=$SP/b34; L=${1:-check}; TS=$(date -u +%Y%m%dT%H%M%S.%NZ)
cd /home/zhengyew/spectec
T=spectec/src/test-lean-claude
ALLOWED_MODS=""   # bundle34: no project file may change; only new logging files
OUT=$T/claude-logging/safety-checks/check-${TS}-bundle34-${L}-$$.txt
W=$B/checks/$L-$TS-$$; mkdir -p $W
{
echo "=== bundle34 safety check [$L] at $TS (pid $$); baseline marker $(cat $B/baseline/marker_time.txt)"
echo "Allowed to change this turn: new files under $T/claude-logging/ only"
echo "Must NOT change: any project file (all .lean modules included), anything else in the repo"
echo "--- 1. git status (porcelain, lock-free, submodules ignored) vs bundle34 baseline (< baseline, > now)"
GIT_OPTIONAL_LOCKS=0 git status --porcelain --ignore-submodules=all > $W/git_status.txt
diff $B/baseline/git_status.txt $W/git_status.txt && echo "IDENTICAL to baseline ($(wc -l < $W/git_status.txt) entries)"
echo "--- 2. HEAD"
GIT_OPTIONAL_LOCKS=0 git rev-parse HEAD | diff $B/baseline/head.txt - && echo "HEAD unchanged ($(cat $B/baseline/head.txt))"
echo "--- 3. paths in the repo (outside .git) modified or created after the marker, excluding claude-logging"
find . -path ./.git -prune -o -newer $B/baseline/MARKER -print | grep -v "^./$T/claude-logging" > $W/newer.txt
cat $W/newer.txt; echo "($(wc -l < $W/newer.txt) paths)"
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
EXCL=(-e "__nothing__"); for m in $ALLOWED_MODS; do EXCL+=(-e "./$T/$m.lean"); done
: > $W/benign.txt
for pg in $T/.lake/packages/*/.git; do
  if grep -q -x "./$pg" $W/newer.txt && [ -z "$(find $pg -mindepth 1 -newer $B/baseline/MARKER -print -quit)" ]; then
    EXCL+=(-e "./$pg"); echo "./$pg" >> $W/benign.txt
  fi
done
# whitelisted external edits (exact path + md5, documented in a safety-checks note; added 18:10Z after the user edited
# their own scratch notes outside the project)
if [ -f $B/baseline/whitelist.txt ]; then
  for wp in $(awk '{print $1}' $B/baseline/whitelist.txt | sort -u); do
    if grep -q -x "$wp" $W/newer.txt; then
      cur=$(md5sum < "$wp" | cut -c1-32)
      if awk -v p="$wp" -v m="$cur" '$1==p && $2==m {f=1} END {exit !f}' $B/baseline/whitelist.txt; then
        EXCL+=(-e "$wp"); echo "whitelisted external edit (path and md5 $cur documented in note-20261111T181000Z): $wp"
      else echo "WHITELISTED PATH CHANGED AGAIN (md5 $cur not yet documented in the note): $wp"; echo "$wp" >> $W/user_edited.txt; fi
    fi
  done
fi
[ -s $W/benign.txt ] && echo "benign lock churn (package .git directory mtime only, no newer file inside; cf. bundle31 note-git-lock-churn): $(wc -l < $W/benign.txt) paths"
BAD=$(grep -v -x "${EXCL[@]}" $W/newer.txt | wc -l)
MEXCL=(-e "__nothing__"); for m in $ALLOWED_MODS; do MEXCL+=(-e " $T/$m.lean\$"); done
BADMD5=$(diff $B/baseline/tlc_md5.txt $W/tlc_md5.txt | grep '^[<>]' | grep -v "${MEXCL[@]}" | wc -l)
BADLOG=$(wc -l < $W/logging_changed.txt)
CHANGED=$(diff $B/baseline/tlc_md5.txt $W/tlc_md5.txt | grep '^>' | awk '{print $3}' | sort -u | tr '\n' ' ')
echo "files under $T (excl. logging) with changed content: ${CHANGED:-none}"
for f in wasm2.0.lean OLD_wasm2.0.lean; do echo "$f md5 now: $(md5sum < $T/$f | cut -c1-32) (baseline $(grep " $T/$f$" $B/baseline/tlc_md5.txt | cut -c1-32))"; done
GEXCL=(-e " $T/claude-logging/"); for m in $ALLOWED_MODS; do GEXCL+=(-e " $T/$m.lean\$"); done
GITBAD=$(diff $B/baseline/git_status.txt $W/git_status.txt | grep '^[<>]' | grep -v "${GEXCL[@]}" | wc -l)
echo "git status lines changed outside claude-logging and the allowed modules: $GITBAD"
UE=0; [ -f $W/user_edited.txt ] && UE=$(sort -u $W/user_edited.txt | wc -l)
if [ "$BAD" = 0 ] && [ "$BADMD5" = 0 ] && [ "$BADLOG" = 0 ] && [ "$GITBAD" = 0 ]; then
  echo "OK: nothing except new files under $T/claude-logging changed since the baseline"
elif [ "$BAD" = "$UE" ] && [ "$BADMD5" = 0 ] && [ "$BADLOG" = 0 ] && [ "$GITBAD" = 0 ]; then
  echo "OK apart from the user's continuing edits to documented path(s) (note-20261111T181000Z): $(sort -u $W/user_edited.txt | tr '\n' ' ')"
else
  echo "ATTENTION: $BAD unexpected newer paths, $BADMD5 unexpected checksum lines, $BADLOG pre-existing logging files changed, $GITBAD unexpected git status lines (see above; may be the user's own concurrent edits or the IDE)"
fi
} > $W/report.txt 2>&1
cp $W/report.txt $OUT
echo "$OUT"; tail -5 $W/report.txt

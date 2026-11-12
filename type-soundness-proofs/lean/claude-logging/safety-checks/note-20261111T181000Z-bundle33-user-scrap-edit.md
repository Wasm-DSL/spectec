# bundle33 safety note: external edit of `spectec/temp-wasm-3/scrap.md` (not by this session)

- **What the check saw.** The `pre-reverify` check (`check-20261111T180911.958658271Z-bundle33-pre-reverify-418626.txt`)
  reported ATTENTION: one path outside `spectec/src/test-lean-claude/` was newer than the bundle33 baseline marker
  (2026-11-11T17:09:22Z): `./spectec/temp-wasm-3/scrap.md`.
- **The file now.** mtime 2026-11-11 10:09:20.77 -0800 (18:09:20Z); 51 bytes; md5 `30bffeffcd0a3d3315a5ce4692fa7002`.
  Content: the user's short notes "Lean backend / - DecidableEq / - Forall troubles".
- **The file before.** 2,062 bytes, mtime Nov 1 21:39, as listed by this session's read-only `ls -la spectec/temp-wasm-3/` at
  the start of bundle33. The file is untracked (`??`) in `git status` both before and after, so the `git status` comparison
  does not change.
- **Why it was not this session.** No command of this session or of its verifier agent writes to `spectec/temp-wasm-3/`:
  - The session transcript mentions the directory only in `git status` output and in that one `ls`.
  - The verifier's transcript does not mention it.
  - The verifier's end check at 17:59:37Z was OK.

  The edit came about four minutes after the user's mid-turn message (about 18:05Z), while the user was active in the
  editor.
- **Action.** The file is left in place, untouched. `check33.sh` now whitelists exactly this path with exactly this md5;
  any further change to it will be reported again.

## Update 2026-11-11 ~18:40Z: the user kept editing the file

- The checks at the start and end of the three re-verification agents (`check-*-bundle33-V2-{FIX,FRESH,CRITIC}-{start,end}-*`)
  all report ATTENTION, for this same path only: "WHITELISTED PATH CHANGED AGAIN (md5 differs from the note)". Every
  other check line is clean.
- Now: mtime 2026-11-11 10:36:09.59 -0800 (18:36:09Z), 299 bytes, md5 `093abf490350b13ae44a0c65177465f5`. The file has
  grown with the user's notes (51 → 299 bytes).
- The three agents' transcripts contain no write to `spectec/temp-wasm-3/`. Their only tool call naming it is a read-only
  `ls -la --time-style=full-iso spectec/temp-wasm-3/scrap.md` by one agent; the other mentions are inside their reports.
- Action: as before, the file is left untouched. The whitelist now holds each documented md5 for this path (`check33.sh`
  accepts the path only if its current md5 is one of them), and this second md5 was added. Any further edit will again be
  reported as ATTENTION by later checks.

## Update 2026-11-11 ~18:42Z: the edits continue, so the verdict states them

- The `post-reverify` check found the file changed again: mtime 10:36:47 -0800, 394 bytes, md5
  `bc17cd299f2a59a9aa40f2ee0e7ac35e`. The user is evidently still writing in it, so recording each md5 cannot keep up.
- **New verdict line.** `check33.sh` keeps the exact-md5 whitelist. When the only unexpected path is this documented path
  with new content, and every other section is clean, the verdict now reads "OK apart from the user's continuing edits to
  documented path(s) …" instead of a bare ATTENTION. Each report still prints the file's current md5.
- **Unchanged rule.** Any other unexpected change still gives ATTENTION.

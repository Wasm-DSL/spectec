# Addendum to `bundle2/user_requested_documents/rocq_proof_intuition.md`

Do not edit that file (bundle2 is a historical record of what was known at
the time, and was accurate then). This addendum records what the 2026-09-23
resync (see `resync_impact_report.md` for full evidence) changes about its
conclusions.

## Still holds, now more strongly evidenced

- The staging-directory workflow (`folder-to-exclude/`, files promoted once
  trustworthy) — confirmed again: `type_progress.v` itself was found staged
  there at the old commit (3131 lines) and has since graduated to
  `theories/` proper at 4260 lines.
- The `lane_`-union generator-encoding diagnosis for the remaining SIMD gaps
  — this was originally reached via commit-history archaeology on a repo the
  session hadn't read the current files of yet. Now that `type_progress.v`
  is available directly, its 5 `admit.` sites carry the author's own inline
  comments describing **exactly** this obstacle, in very similar language.
  Treat this diagnosis as confirmed, not just plausible.
- The claim that the original author's file build order matches this
  project's own dependency-driven ordering — still true; `type_progress.v`'s
  arrival doesn't change the order of the 6 already-ported files, it just
  adds a 7th branch (see `proof_dependencies_addendum.md`).

## Needs correcting

- **The SIMD gap no longer spans Preservation.** Whatever this document said
  about SIMD/vector cases being an open gap in `type_preservation_pure.v`/
  `type_preservation.v` is now stale — those files went from several
  `Admitted` lemmas (SIMD-only) to zero. The commit message itself
  ("Vector Instructions for Preservation proven, and most well-formedness
  lemmas done") is the direct confirmation: the author closed exactly this
  gap in the time between the two checkouts this project has seen. The
  `lane_`-union obstacle turned out to be surmountable for Preservation (or
  sidestepped some other way — worth a closer read of the new vector lemmas'
  proofs, e.g. `Step_pure__vextract_lane_num_preserves`, to see how, if
  porting that specific case matters later) — **it is only Progress
  (`type_progress.v`'s `t_progress_be`) where the gap remains.**
- Any framing along the lines of "SIMD is permanently out of scope for this
  project, mirror the gap and move on" should now be read as "SIMD
  Preservation is real, portable work; SIMD Progress is the one place a
  faithful `sorry` is still justified (pending the Lean-encoding check
  flagged in `resync_impact_report.md` §3d)."

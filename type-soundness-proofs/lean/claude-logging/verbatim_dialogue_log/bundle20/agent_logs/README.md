# bundle20 subagent logs

Every subagent was given the user's safety order verbatim. Each ran
`safety-checks/verify_against_baseline.sh` at start and end (outputs in its log; the check files
are in `claude-logging/safety-checks/`) and wrote only its own log here plus scratch files in the
session scratchpad. Every final safety check reported `VERIFIED: zero new changes outside
spectec/src/test-lean-claude`.

| Workflow (run id) | Purpose | Agents | Outcome | Logs |
|---|---|---|---|---|
| `preservation-audit` (`wf_19300dcc-f8c`) | first audit wave | 11 | **all killed by the account usage limit** after ~6 min; partial logs only | `audit-*.md`, `sig-tp.md`, `sig-tpp.md`, `sig-ext.md`, `sig-typing.md`, `sig-base.md` (first-wave parts) |
| `preservation-audit-v2` (`wf_67c8bfe9-04b`) | economical relaunch from side-by-side extracts, max 3 concurrent | 6 auditors + 4 verifiers | all done; all 4 major findings confirmed | `audit-model.md`, `audit-isabelle.md`, `audit-nonvacuity.md`, `sig-tp-tpp.md`, `sig-typing-base.md`, `sig-ext.md`, `v2verify-*.md`; structured results in `preservation_audit_v2_results.json` |
| `progress-signatures` (`wf_88e0cc43-5d4`) | translate the 190 Rocq progress lemma statements (6 chunks), audit each, fix | 6 + 6 + 1 | all done; 1 audit problem (chunk 4), fixed | `psig-*.md`, `psig-audit-*.md`, `psig-fix-4.md`; `progress_signatures_results.json` |
| `progress-proofs` (`wf_cb22b074-0c2`) | prove the 280 `sorry` targets (43 batches; Sonnet for helper batches) | 43 | all done; 280/280 proved (2 with one documented known-false `sorry` each) | `prove-*.md`; `progress_proofs_results.json` |

Also here:
- `progress_trust_boundary.txt`: `#print axioms` / `#sorry_deps` for `t_progress`, `t_progress_e`,
  `t_progress_be` and `t_preservation` at the end of bundle20.

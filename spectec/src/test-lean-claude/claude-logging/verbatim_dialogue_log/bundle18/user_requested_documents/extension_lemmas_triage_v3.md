# `ExtensionLemmas.lean` triage — update v3 (bundle18)

Written for: a future Claude session (primary audience) and the user.
Supersedes `bundle16/user_requested_documents/extension_lemmas_triage_v2.md` (kept
untouched). v2 was the closeout of the bundle15 triage (2 `sorry`s left). This short update
records what happened since.

## Headline

| | v1 (bundle15 start) | v2 (bundle16 end) | **v3 (bundle18 end)** |
|---|---:|---:|---:|
| `ExtensionLemmas.lean` `sorry`s | 76 | 2 | **1** |

- **`funcinst_same`**: closed. The user added an `hlen` premise in bundle17 (verified
  sound; it is the same `Forall₂`-length deviation as `Vals_ok`) and it is proved.
- **`Val_ok_store`**: still `sorry`. Dead (rule 1): no current upstream counterpart and no
  users. Recommend deletion (ask the user).

## Changes in bundle18

- **`construct_meminsts_grow`**: signature generalized from a hard-coded
  `some (uN.mk_uN v_j)` maximum to Rocq's genuine optional maximum
  (`v_j_opt : Option uN`, premise `Forall (fun v_j => lim_old + v_n ≤ proj_uN_0 v_j)
  (Option.toList v_j_opt)`). The proof was adapted from `construct_tableinsts_grow`. Its doc
  comment (which claimed "not yet attempted") was rewritten: it is proved. It is now used by
  `TypePreservation.memory_grow_store_ok`.
- No other edits. Everything `store_extension_reduce` needed already existed here
  (`*_extension`, `construct_*`, `minst_invert_*`, `extend_*_refl`, `Extend_store_*s`). The
  new store plumbing (`Store_ok_parts`, `Extend_store_of_parts`, …) lives in
  `TypePreservation.lean`.

## Pitfalls seen in this file (still relevant)

- `simp_all` in contexts holding `Meminst_ok`/`Store_ok` facts can hit
  `maximum recursion depth`. Use targeted `simp only [...] at h` plus `subst` (fixed this way
  in `construct_meminsts_grow`).
- `OMap f o` unfolds to `o.map f`, so `OMap (fun v => uN.mk_uN v) m_opt` is defeq to
  `m_opt.map uN.mk_uN` (constructor applications typecheck directly).

# Reply to the bundle24 follow-up (verbatim)

---

The order matters because each pass only sees what exists when it runs. `DefToRel` creates new iterations, so `Sideconditions` can only give those iterations length premises if it runs after `DefToRel`. But `DefToRel` only turns a partial definition into a relation if `Sideconditions` has already given that definition premises. Each order therefore gets one thing right and misses the other.

### What each pass does that matters here

**`Sideconditions`** (`middlend/sideconditions.ml`) adds premises that make partial operations well defined. It handles every rule, and every definition clause when `sideconditions_on_defs` is on:
- **Indexing:** `l[i]` gets the premise `i < |l|`.
- **Option projection:** `the(o)` (Lean's `Option.get!`) gets `o ≠ none`.
- **Membership:** `x ∈ l` gets `|l| > 0`. This rule is where the `disjoint_` oddity comes from.
- **Iterations over several lists:** if an iteration walks several lists together, it adds length premises, with the first list as the reference.
  - For lists it adds `|xs₁| = |xs₂|`, `|xs₁| = |xs₃|`, and so on.
  - For options it adds `(o₁ = none) ↔ (o₂ = none)`.
  - These are the premises we're missing.
- **Inside iterations:** a side condition of a sub-expression inside an iteration is wrapped in that same iteration.
- **Cleanup:** it drops premises that are trivially true and removes structurally duplicate ones within a rule.

It only sees the iterations that exist when it runs.

**`DefToRel`** (`middlend/deftorel.ml`) does two things:
- **Chooses which definitions become relations** (`must_be_relation`). A definition is converted if:
  - one of its clauses has real premises; or
  - it calls a function that has already become a relation; or
  - one of a few other conditions holds.

  Only definitions with ordinary value parameters can be converted. That is why `disjoint_`, which takes a type parameter, stays a `def` with its premise rendered as an implication.
- **Converts them and rewrites the call sites.** Definition `X` becomes `inductive fun_X args result`. Each call `X(args)` is replaced by a fresh variable `var_k` plus the premise `fun_X args var_k`.
  - If the call sits inside an iteration, such as `$iabs(lane)*`, the premise is iterated too: `Forall₂ (fun var lane => fun_iabs … var) var_k_lst lane_lst`.
  - The fresh list `var_k_lst` is a new iterated variable, listed first.
  - `DefToRel` adds no length premise for that list.

### What each order produces

| | Old: `DefToRel` then `Sideconditions` (side conditions on defs off) | New: `Sideconditions` (side conditions on defs on) then `DefToRel` |
|---|---|---|
| Partial definitions (`sizenn`, `lsize`, `fun_table`, `with_global`, …) | No premises, so they stay functions and indexing falls back to `default` | Get bounds and `≠ none` premises first, so `DefToRel` converts them into relations that carry the bounds (what you wanted) |
| Iterations that `DefToRel` creates | `Sideconditions` runs afterwards and adds `\|var_k_lst\| = \|lane_lst\|`: 283 premises | Created after `Sideconditions` has finished, so no length premises: 0 |
| Option iterations that `DefToRel` creates (the STORE case's `var_0_opt`) | Get the `↔ none` premise | Don't get it, so the packed-store size bound isn't enforced |

Turning on side conditions for definitions without reordering wouldn't work either. The premises would be added after `DefToRel` had already run, so nothing would turn those definitions into relations. They would remain definitions with premises, which the Lean backend renders as implications, as happened with `disjoint_`.

### Why only Lean suffers

The missing premises only matter if the list predicate doesn't already force equal lengths:
- **Isabelle:** `list_all2`/`list_all3` force equal lengths, so these relations are unaffected.
- **Rocq:** the inductive `Forall2` forces equal lengths too.
- **Lean:** the zip-based `Forall₂`/`Forall₃` don't. The result lists can carry extra, unconstrained elements, and that is what makes `vunop__is_wf`, `vbinop__is_wf`, `vcvtop___is_wf` and the `vshiftop` case of `Step_pure_is_wf` unprovable.

### How the fixes relate

- **Running `Sideconditions` again after `DefToRel`** gives both effects. The first run makes partial definitions into relations with bounds; the second adds length and `↔` premises for the new iterations, and its built-in duplicate removal drops everything the first run already added. That's what the experiment showed: 284 length premises restored, no duplicates, nothing lost.
- **Making `Forall₂`/`Forall₃` check lengths** makes Lean independent of the pass order, as Rocq and Isabelle already are. It needs the special case for `fun_utf8`.

> **Unfinished draft.** Copied as it stood when work stopped (bundle23, mid-turn input 5). The
> `@@BOTTOMLINE@@` and `@@SECTION2@@` placeholders were never filled in. Later findings: bundles 24-27,
> in particular bundle27, on `todaywasm2.0_shouldwork`.

# The regenerated `wasm2.0.lean` (sideconditions on defs, `Sideconditions` before `DefToRel`)

Written for: you (the user), and the next session. Date 2026-11-02.
Scratchpad (all evidence, probes and tools):
`/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad`, called `SP` below.

## 0. Bottom line

@@BOTTOMLINE@@

## 1. What the two `main.ml` changes did to the generated model

### 1.1 Mechanism

- `sideconditions_on_defs = true` makes the `Sideconditions` pass also derive side conditions for
  function *definitions*: list indexing `l[i]!` gets `i < |l|`, `Option.get! o` gets `o ≠ none`, and
  zipped iterations get length equalities.
- A Lean `def` cannot carry premises. Because `DefToRel` now runs *after* `Sideconditions`, every
  definition that received a side condition is turned into an inductive relation `fun_X args result`
  with the conditions as premises. Every call of it elsewhere (in other definitions, `wf_*`
  predicates, typing and reduction rules) becomes a relational premise with a fresh `var_k`.

### 1.2 Size of the change (generated part only)

- 608 named generated definitions exist in both files; 538 are unchanged and 70 changed.
- 37 functions became relations:
  - 24 under a new name (`E` → `fun_E`, `sizenn` → `fun_sizenn`, `lsize`, `isize`, `jsize`, `fsize`,
    `sizenn1/2`, `lsizenn(1/2)`, `shsize`, `canon_`, `vvunop_`, `vvbinop_`, `vvternop_`,
    `with_global`, `with_table`, `with_tableinst`, `with_mem`, `with_meminst`, `with_elem`,
    `with_data`, `instexport`);
  - 13 under the same name (`fun_M`, `fun_zero`, `fun_unop_`, `fun_testop_`, `fun_type`, `fun_func`,
    `fun_global`, `fun_table`, `fun_mem`, `fun_elem`, `fun_data`, `fun_local`, `fun_blocktype`).
- 2 new auxiliary relations (`fun_unop__before_…_case_22`, `fun_testop__before_…_case_2`).
- Changed constructors because of relational premises: the `wf_*` predicates that mention sizes
  (`wf_fNmag`, `wf_shape`, `wf_num_`, `wf_lane_`, the `wf_cvtop__*`/`wf_vcvtop__*` families,
  `wf_loadop_Inn`, `wf_instr`/`wf_admininstr` cases 38 and 57), the numeric and vector operator
  relations, `Step_pure`, `Step_read` (+ its 9 `_before_` relations), `Step`, `fun_allocmodule`,
  `fun_instantiate`.
- The typing relations are unchanged: `Store_ok`, `Moduleinst_ok`, `Frame_ok`, `Instr_ok`,
  `Instrs_ok2`, `Config_ok`, …
- 22 generated `*_is_wf` theorems changed shape: they now read
  `fun_X args var_0 → … → ret_val = var_0 → wf ret_val`. The other 68 kept their statements.

### 1.3 What it achieves: indexing no longer goes through `default`

- The accessor relations carry exactly the bounds that make their well-formedness theorems true.
  For example `fun_table_case_0` needs `(f.MODULE.TABLES)[x]! < |s.TABLES|` and `x < |f.MODULE.TABLES|`.
- Kernel audit (§5.3), every `Inhabited` instance made opaque:
  - old model: 11 theorems depended directly on a default value (the six `iswf_*_default`,
    `iswf_table_len_lt`, `iswf_elem_len_lt`, `iswf_mem_len_le`, `iswf_data_byte_lt`,
    `Step_pure_is_wf`);
  - finished new file: **0**.
- Semantic side effect: an out-of-range table/memory/global/… index now makes a rule inapplicable
  instead of reading a default instance. For example `table_get_trap` needs `fun_table z x _`.
  Such configurations are stuck instead of trapping. Validated programs never reach them, but
  progress must now supply the relation witnesses (§4).

### 1.4 Regression A (blocking): length side conditions are no longer generated

- **Cause.** `DefToRel` turns an iterated call `$f(x)*` into
  `Forall₂ (fun var_elem x_elem => fun_f … var_elem) var_k_lst x_lst`, with a fresh list `var_k_lst`.
  With the old order, `Sideconditions` ran afterwards and added `|var_k_lst| = |x_lst|`. Now it runs
  first, so these fresh lists get no length premise.
- **Size.**
  - Premises `(List.length var_k_lst) = (List.length …)`: 283 in the old model, **0** now.
  - `Forall₂`/`Forall₃` premises in generated constructors whose paired lists have no length
    premise: 13 of 404 in the old model (the figure bundle20's audit reported), **171 of 407** now.
- **Why it matters in Lean only.** The Lean backend's `Forall₂`/`Forall₃` are zip-based
  (`∀ t ∈ xs.zip ys, …`), so they say nothing about elements past the shorter list. Rocq's inductive
  `Forall2` forces equal lengths by itself. bundle20's audit noted that the zip encoding "is sound
  only together with the generator's length premises".
- **Affected relations:** `fun_vunop_`, `fun_vbinop_`, `fun_vrelop_`, `fun_vcvtop__` (each also its
  `_before_` relation), `Step_pure` (`vshiftop`, `vbitmask`), `fun_utf8` (case 4), `fun_allocmodule`
  (the instance's exports), and `wf_instr`/`wf_admininstr` case 57 (STORE, through `Option.toList`).
- **Consequences:**
  - These relations are no longer functional: a result list may carry extra, arbitrary elements.
  - Four generated theorems are unprovable as generated: `vunop__is_wf` (4 ABS cases),
    `vbinop__is_wf` (16 MIN/MAX/ADD_SAT/SUB_SAT cases), `vcvtop___is_wf` (3 cases) and
    `Step_pure_is_wf` (its `vshiftop` case). Machine-checked witnesses show that each generated
    statement would force a well-formedness fact about the opaque `inv_lanes_` on an ill-formed
    lane list, which no axiom provides (§5.4). `fun_vrelop_` and `vbitmask` are not affected, because
    they carry a well-formedness premise on the actual output.
  - `wf_instr`/`wf_admininstr` case 57: with `var_0_opt = none`, both the `Forall₂` and the `Forall₃`
    become vacuous. The packed-store bound `sz < |Inn|` is therefore no longer enforced, so
    well-formedness accepts more `STORE` instructions than before.
  - `fun_allocmodule`: the instance's export list is tied to the module's exports only by a zip.
    Allocation can therefore add junk exports or drop some. This is off the type-safety path.
- **Fix options (yours to choose):**
  1. Restore the premise: let `DefToRel` emit `|var_k_lst| = |x_lst|` for the lists it creates, or run
     `Sideconditions` a second time after `DefToRel`. This gives back the old model's exact shape.
  2. Make the Lean backend's `Forall₂`/`Forall₃` length-checking. This removes the whole class at
     once, also for the 13 old cases (e.g. in `fun_instantiate`).

  With either fix, each of the four gaps closes by replacing its single `have hlen … := sorry` with the
  restored premise (§2.3).
- Side note: `DefToRel` emits each iterated call twice (one list for a well-formedness premise, one
  for the result). This is harmless but doubles those premises.

### 1.5 Regression B (blocking for one theorem): `fzero_is_wf` is false as generated

- `wf_fNmag N (SUBNORM m)` now needs `fun_E N _` and `fun_M N _`, which exist only for `N ∈ {32, 64}`.
  `fzero_is_wf (v_N : N) … : wf_fN v_N (fzero v_N)` has no premise on `N`.
- Machine-checked counterexample (no axioms): `¬ wf_fN 0 (fzero 0)` (`SP/probes/Fzero.lean`).
- The old proof only worked because `Option.get! none` defaulted to `0`.
- Nothing depends on it any more:
  - `zero_is_wf` and `default__is_wf` use two helpers, `iswf_fzero_32`/`iswf_fzero_64`;
  - no other project file uses `fzero_is_wf`.
- Fix options: give the theorem a premise on `N` (in the generator: e.g. emit `signif N ≠ none`, as
  `fun_M` itself does; or by a hand edit), or accept it as a known-false `sorry`.

### 1.6 The `Step_read_is_wf`/`Step_is_wf` hand edit is still necessary

- Machine-checked (no axioms; `SP/probes/StepReadFalse.lean`): the generated, unedited statements are
  false. A well-formed configuration whose store holds a table with 2^32 references steps by
  `table.size` to `CONST I32 2^32`, which is not a well-formed `u32`.
- With the hand-edited `Store_ok (fun_store z)` premise, both theorems are proved. The bounds that
  only `Store_ok` provides are used by table.size, memory.size, table.fill/copy/init (`succ`/`le`/`gt`)
  and memory.copy-gt.

### 1.7 Other changes worth knowing (not blocking)

- `fun_with_*` bound only the module-level index (`x < |f.MODULE.X|`), not the store address
  `(f.MODULE.X)[x]! < |s.X|`. An out-of-range address makes `List.modify` a no-op instead of being
  rejected. Well-formedness is preserved either way.
- `disjoint_` now reads `| w :: w'_lst => (List.length w'_lst) > 0 → (! …) && disjoint_ X w'_lst`: a
  side condition rendered as an implication inside a `Bool` body and decided by `decide`. It gives
  the same value as before on every list, but it is a generator wart.
- `fun_instantiate`: duplicated premises were dropped and the rest reordered (harmless).
- Unchanged but worth recalling: `with_table_is_wf`/`with_elem_is_wf` have no premise on the new
  references (there is no `wf_eleminst`), and `fun_with_mem` ignores its second `Nat` (the slice end),
  as in the old model.

@@SECTION2@@


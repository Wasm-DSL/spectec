# Downstream proof repair against the regenerated `wasm2.0.lean` (bundle31)

Date: 2026-11-03. Scratch evidence: `/tmp/claude-1002/-home-zhengyew-spectec/14eafe93-c912-45da-8e28-e9b09c1a6ef6/scratchpad/b31/`
(called `B` below). Line numbers `<Module>.lean:<n>` refer to the installed files in
`spectec/src/test-lean-claude/` unless a section says otherwise.

## 1. Result

- All seven downstream modules compile against the current `wasm2.0.lean` (md5 `4207ecaa…`, unchanged
  this turn), with **0 errors and 0 `sorry`**. Checked by a fresh build of all nine modules from the
  repository sources into an empty scratch build directory (only Mathlib's package oleans reused).
- **No theorem depends on `sorryAx`**: a project-wide axiom audit (`B/axcheck/AxCheck.lean`) over all
  5,517 theorems of the eight project modules (`wasm2.0` and the seven downstream modules) finds none.
- **No theorem reads an `Inhabited` default value**: the kernel replay of all eight modules with every
  `Inhabited` instance made opaque (`B/audit/RunAuditAll.lean`, the bundle23 method extended to the
  downstream modules) re-checks the 5,517 theorems and finds 0 that need a default.
  In the starting state (the broken declarations `sorry`ed), one downstream theorem did
  (`mem_bytes_wf`), and the first assembled version had one more (`t_read_preservation`'s `call`
  case); both were fixed.
- Main theorems, statements unchanged:
  - `t_preservation`: Lean's three standard axioms plus 32 of the model's `*_is_wf` axioms for
    `opaque` functions.
  - `t_progress`: the standard three, 56 model `*_is_wf` axioms, and 15 of the project axioms in
    `HelperLemmas` that port Rocq's `axioms.v` (`lanes_len`, `nbytes_inv`, `ibytes_inv`, `vbytes_inv`,
    `ibits_inv`, `truncz_quot`, `trunc_sat_total`, `demote_nonempty`, `promote_nonempty`, the six
    `f*_bit`). No axiom was added.
- Remaining warnings are linter warnings of kinds that were there before (`TypeProgress` 1,
  `TypePreservation` 7, `ExtensionLemmas` 14, `TypePreservationPure` 47, `TypingLemmas` 9,
  `HelperLemmas` 4; `wasm2.0` keeps its 89).

## 2. What changed in the model, and why the proofs broke

With `sideconditions_on_defs` (user commit `12b021fc9`), every spec function that needs a side
condition (an `!`, a list index, or for `$fzero` the well-formedness of its result), and every
function that calls one, became a relation `fun_<name> args out`:

- **State lookups** `$type`, `$func`, `$global`, `$table`, `$mem`, `$elem`, `$data`, `$local`: in Wasm
  terms `$table(z, x)` is the table instance `S.tables[F.module.tables[x]]`. The old function returned
  a default instance when `x` or the address was out of range; the relation `fun_table z x ti` holds
  only when `x < |F.module.tables|` and `F.module.tables[x] < |S.tables|`, and then
  `ti = S.tables[F.module.tables[x]]`.
- **State updates** `$with_global`, `$with_table`, `$with_tableinst`, `$with_mem`, `$with_meminst`,
  `$with_elem`, `$with_data`, `$growtable`, `$growmemory`, and **`$blocktype`** (which looks up a type
  for `_IDX`).
- **Total functions** that use one of these internally: the bit widths `$lsize`, `$isize`, `$jsize`,
  `$sizenn`, `$lsizenn`, …, `$fzero`, `$zero`, `$default_`; the numeric operators with partial results
  `$unop_`, `$testop_` (an `Option` output); the vector operators `$vvunop_`, `$vvbinop_`,
  `$vvternop_`, `$vunop_`, `$vbinop_`, `$vrelop_`, `$vcvtop__`, ….
- **Execution rules** (`Step`, `Step_read`, `Step_pure`) take the relations as premises, plus the
  restored length premises, wf premises (e.g. `call_addr` now requires `wf_funcinst`, `wf_func` and
  `wf_frame` of the new frame) and, for `call_indirect`'s trap rule, a negated "before" premise.
- **Constructors of the well-formedness predicates** changed shape: `wf_num_`, `wf_lane_` and
  `wf_shape` carry a `fun_sizenn`/`fun_lsize` witness instead of the term `sizenn nt`.

Downstream, this hit the proofs in three ways. (1) Names disappeared (`lsize`, `sizenn`, `fzero`,
`default_`, `with_global`, `vvunop_`, …), so statements and proofs mentioning them no longer
elaborated; the same names that are now relations (`fun_table`, `fun_unop_`, `fun_blocktype`, …) were
applied as functions. (2) Every `cases`/`rcases` on a changed constructor saw a different number of
fields. (3) **Preservation** now receives the relations as hypotheses and has to invert them; that is
mechanical. **Progress** now has to *construct* them, i.e. prove the index bounds from validation and
module-instance typing, which the old functions never needed; that is the main new mathematics.

## 3. How the repair was done

1. **Shared infrastructure** (main session), compiled first:
   - `HelperLemmas`: *function views* of the total relations with the old model's definitions
     (`lsize`, `isize`, `jsize`, `sizenn`, `sizenn1`, `lsizenn`, `lsizenn1`, `lsizenn2`, `fzero`,
     `default_`) and bridging lemmas (`fun_lsize_lsize : fun_lsize lt (lsize lt)`,
     `fun_lsize_eq : fun_lsize lt n → n = lsize lt`, …); *inversion lemmas* for the lookups
     (`fun_table_inv`, …). With the views, 16 declarations compile again with unchanged text.
   - `TypeProgress`, section "Lean-only: index bounds for the state lookups": `Moduleinst_ok_*_addr`
     and `fun_*_typed`, which build a lookup from a validated index and `Moduleinst_ok`.
   - Restated `bt_inversion` (`ExtensionLemmas`) and `wf_config_mem_bytes` (`TypeProgress`), which
     several groups use.
2. A sorry-out cascade against this context left 86 broken declarations (10 in `TypePreservation`,
   76 in `TypeProgress`). Nine agents repaired them in groups (P1, P23 in `TypePreservation`;
   Q1-Q6b in `TypeProgress`), each in a scratch copy of its module where the other groups'
   declarations were `sorry`ed with their statements fixed. All Lean runs went through one lock
   (one process at a time). A unit-level diff tool rejected edits outside an agent's assignment; the
   nine copies were merged by declaration.
3. Fresh full build, axiom audit and default-value audit. The audit found the `call` case of
   `t_read_preservation` (`by simp` rewrote `l[i]!` to `getD default`) and `mem_bytes_wf` (its
   out-of-range case read the default `meminst`); both were fixed (`List.mem_singleton_self`; an
   index-bound premise).
4. The report writers and checkers below also reviewed the code; their flags led to a cleanup:
   doc-comment and comment fixes, the rename `ENone` → `Etestop`, a sturdier proof of
   `Moduleinst_ok_data_addr`, and deletion of 8 new lemmas that nothing used.
5. Report: 11 writers (one per group) and 11 independent checkers, then an update to the installed
   text and a final check.

## 4. Files changed (installed)

| module | lines before → after | changed |
|---|---|---|
| `HelperLemmas.lean` | 841 → 1038 | +199 −2: function views and inversion lemmas (new sections at the end), header and one doc comment |
| `ExtensionLemmas.lean` | 2167 → 2172 | +17 −12: `bt_inversion` |
| `TypePreservation.lean` | 2885 → 2912 | +150 −123: 10 declarations re-proved or restated, header, 4 doc comments |
| `TypeProgress.lean` | 7951 → 8248 | +826 −529: 76 declarations re-proved or restated, the index-bounds section, `wf_config_mem_bytes`, `mem_bytes_wf`, header |
| `Subtyping`, `TypingLemmas`, `TypePreservationPure` | unchanged | |

`wasm2.0.lean`, `OLD_wasm2.0.lean`, `wasm2.0_prevattempt.lean` and `lakefile.lean` were not touched. The
repository's `.lake/build` was not touched either; it is stale (its oleans predate the bundle29
`wasm2.0.lean`), so `lake build` will rebuild every module (about 70 s in total in the scratch build).

## 5. Statement changes

All other statements are unchanged, in particular every `t_progress_be_*`/`t_progress_e_*` case (minor
premises of the typing recursors) and all main theorems.

| construct | module | change | why |
|---|---|---|---|
| `bt_inversion` | ExtensionLemmas | premise `fun_blocktype z bt = mkFunctype bt1 bt2` → `fun_blocktype z bt (mkFunctype bt1 bt2)` | `$blocktype` is a relation |
| `wf_config_mem_bytes` | TypeProgress | takes `fun_mem (state.mk_state s f) x mi` and concludes `Forall wf_byte mi.BYTES` (was: about `(fun_mem … x).BYTES`) | `$mem` is a relation |
| `mem_bytes_wf` | TypeProgress | extra premise `k < ms.length` | default-independence |
| `table_grow_store_ok` | TypePreservation | takes the `table.grow` rule's premises `fun_growtable var_1 n r var_2`, `fun_table (S;F) x var_1` | `$table`, `$growtable` are relations |
| `memory_grow_store_ok` | TypePreservation | same for `fun_growmemory`/`fun_mem` | `$mem`, `$growmemory` are relations |
| `with_mem_store_ok` | TypePreservation | premise `fun_with_mem (S;F) 0 off len b* (S';F')` instead of the equation `with_mem … = (S';F')` | `$with_mem` is a relation |
| `unop_not_none` | TypeProgress | `fun_unop_ nt u n1 ≠ none` → `∃ cs, fun_unop_ nt u n1 (some cs)` | `$unop_` is a relation with an `Option` output |
| `testop_not_none` | TypeProgress | `fun_testop_ nt t n1 ≠ none` → `∃ c, fun_testop_ nt t n1 (some c)` | same for `$testop_` |
| `zero_lane_wf` | TypeProgress | `… (fun_zero nt) …` → `∃ z, fun_zero nt z ∧ …` | `$zero` is a relation |
| `vstore_lane_progress` | TypeProgress | extra first premise `0 < f.MODULE.MEMS.length` | `$with_mem`'s premise needs the memory index bound |

## 6. Observations (none blocks the proof)

1. **Store rules in the spec (upstream, pre-existing).** `Step/store-num-val`, `store-pack-val`,
   `vstore-val` and `vstore_lane-val` (`specification/wasm-2.0/8-reduction.spectec:550-579`) have no
   in-bounds premise; only the `-oob`/`-trap` rules have the bound condition. Read as relations, an
   out-of-bounds store can therefore either trap or take the `-val` step. Also `vstore_lane-oob`
   tests `i + ao.OFFSET + N > |mem|` with `N` in bits, where the Wasm 2.0 spec traps when
   `ea + N/8 > |mem.data|`. The theorems still hold (progress for stores only needs the `-val` rule),
   but the relational semantics is more permissive than Wasm's. Same in `OLD_wasm2.0.lean`.
2. **Unused generated relations.** `Step_read_before_table_fill_zero`, `…_table_copy_zero/le`,
   `…_table_init_zero` and the four `…_memory_*` ones are generated, but no rule uses them (those rules
   carry explicit bound premises; the `copy_zero` predicates are referenced only inside the unused
   `copy_le` ones). The rules that do have a negated `_before_` premise are `Step_read.call_indirect_trap`
   and, in `Step_pure`, `ref_is_null_false` and `vtestop_false`.
3. **The float lane `get!`** (bundle30): the float constructors of `fun_vunop_`/`fun_vbinop_` still
   apply `Option.get! (proj_lane__1 l)` without a `≠ none` premise; no proof depends on it (the default
   audit is clean).
4. **Editor side effects during the turn** (not this session's doing; documented in
   `claude-logging/safety-checks/*note*`): at 09:53:32 +0800 a git process created and removed lock
   files in the nine `.lake/packages/*/.git` directories (no content change), and at 09:57:45 the
   editor's Lake (`lake serve` for this folder) wrote
   `spectec/src/test-lean-claude/.lake/build/lib/lean/wasm2.0.trace.nobuild` (left in place).

## 7. Per-construct report

The user asked, for each top-level construct affected by the regeneration: what broke and why, the
original proof sketch, and the current proof sketch, in Wasm 2.0 terms. 105 existing constructs are
affected (the 104 that broke against the new model, and `mem_bytes_wf`, changed for
default-independence); 47 constructs are new. They are grouped as follows:

- 7.1 New infrastructure (47 constructs, `HelperLemmas` and `TypeProgress`)
- 7.2 Repaired centrally: `bt_inversion`, `wf_config_mem_bytes`, `mem_bytes_wf`, and 16 constructs that compile again unchanged
- 7.3 P1, `TypePreservation`: `Step_read` preservation (2 constructs)
- 7.4 P23, `TypePreservation`: `Step` preservation, store extension, instance invariance (8 constructs)
- 7.5 Q1, `TypeProgress`: numeric operators and canonical forms (14 constructs)
- 7.6 Q2, `TypeProgress`: lane and vector-operator totality lemmas (13 constructs)
- 7.7 Q3, `TypeProgress`: vector progress cases A (8 constructs)
- 7.8 Q4, `TypeProgress`: vector progress cases B and `vcvtop` (9 constructs)
- 7.9 Q5, `TypeProgress`: control, variables and tables (15 constructs)
- 7.10 Q6a, `TypeProgress`: memory instructions (9 constructs)
- 7.11 Q6b, `TypeProgress`: vector memory instructions (8 constructs)

Each section was written by one agent from the original and final code, the recorded errors and the
repair notes, then fact-checked against the code by a second agent, then updated to the installed
text and checked again.

### 7.1 New infrastructure (47 constructs, `HelperLemmas` and `TypeProgress`)

These 47 declarations are new. Nothing like them existed in the original modules. They connect
the regenerated `wasm2.0.lean` (built with `sideconditions_on_defs`, user commit `12b021fc9`) to
proof text that was written against the old model:

- 36 are in `HelperLemmas.lean`, in the section "Function views of total relations (Lean-only)"
  and its subsection "Inversion of the state lookups (Lean-only)".
- 11 are in `TypeProgress.lean`, in the section "Lean-only: index bounds for the state lookups".

None of them ports a Rocq lemma, and all are proved without `sorry`. The audits of the final build
(b31/final4, whose sources are byte-identical to the installed files) cover them as well. No
theorem depends on `sorryAx`. In the kernel replay with every `Inhabited` instance opaque, no
theorem reads a default value. That includes the 37 theorems among these 47 declarations (the
other 10 are definitions), even though the views `lsize`, `isize`, `sizenn` and `sizenn1` use
`Option.get!` and the lookup lemmas mention `l[i]!`. The views are only evaluated
where the option is `some` or the index is in range, and the inversion lemmas return the bound
together with the indexed term.

Nothing in these declarations broke, so the user's three questions take this form here:

- **What broke and why:** what the regeneration removed from the model, and what failed
  downstream as a result.
- **Original proof sketch:** what the old proofs did instead. Usually that was nothing: the old
  model supplied the fact through a total function.
- **Current proof sketch:** the new statement, what it means in Wasm 2.0, its proof, and where it is
  used.

Module names (`HelperLemmas.lean`, `TypeProgress.lean`, …) refer to the installed files in
`spectec/src/test-lean-claude/`; this section cites no line numbers in them. Model line numbers
refer to the scratch copies `b31/model/wasm2.0.lean` (new model, byte-identical to the installed
`wasm2.0.lean`) and `b31/model/OLD_wasm2.0.lean` (old model, byte-identical to the installed
`OLD_wasm2.0.lean`). Spec references point to `specification/wasm-2.0/*.spectec`. In Lean, the
state `(S; F)` is `state.mk_state s f`, and `F.module.tables` is `f.MODULE.TABLES`.

| Family | Count | Replaces (old model) | Now in the model | Used by |
|---|---|---|---|---|
| A. Function views of the size functions | 8 defs + 13 lemmas | the functions `lsize`, `isize`, `jsize`, `sizenn`, `sizenn1`, `lsizenn`, `lsizenn1` and `lsizenn2` | the relations `fun_lsize` … `fun_lsizenn2`. Their constructors have the premise `size … ≠ none` (the i8/i16 cases of `fun_lsize` have none) or `fun_lsize …` | 43 declarations that mention a view: the numeric and SIMD progress lemmas (8 of them with unchanged text) and `num_default_is_well_formed`. 5 more unchanged declarations use the views only through `jlane`, `flane` and `wf_lane_*_inv` |
| B. `fzero` and `default_` | 2 defs + 7 lemmas | the functions `fzero` and `default_`, and the model theorem `fzero_is_wf` (stated for every N) | `fun_fzero` (holds only for N = 32 and 64) and `fun_default_` | 8 declarations: progress and preservation for function calls (`t_progress_e_call_addr`, `t_read_preservation` and the helpers `default_not_none`, `default_val_ok`, `default_vals_ok`), `num_default`, `num_default_is_well_formed` and `zero_lane_wf` |
| C. Inversion of the state lookups | 6 lemmas | the functions `fun_type`, `fun_global`, `fun_table`, `fun_mem`, `fun_elem` and `fun_local` | relations with one constructor each, whose premises are the index bounds | 8 declarations: `t_read_preservation`, `table_grow_store_ok`, `memory_grow_store_ok`, `bt_inversion`, `wf_config_mem_bytes` and 3 store progress cases |
| D. Index bounds and typed lookups | 5 + 6 lemmas | nothing. The old lookups needed no bounds; only `memory.size` derived one (the store-side bound), inline | the same relations, plus the update relations `fun_with_*` | 27 progress cases (`t_progress_be_*`) |

#### A. Function views of the size functions (21 declarations)

**Wasm 2.0.** These functions compute the bit widths that the spec writes |t|
(1-syntax.spectec:208-246):

- `$size(valtype)` is partial (`hint(partial)`). It is 32 or 64 for i32, i64, f32 and f64, and 128
  for v128. It is undefined for reference types and `bot`.
- `$psize` gives 8 for i8 and 16 for i16.
- `$lsize(lanetype)` is the width of a SIMD lane type. It is `$size` for i32/i64/f32/f64 lanes and
  `$psize` for i8/i16 lanes.
- `$isize(Inn) = $size(Inn)`.
- `$jsize(Jnn) = $lsize(Jnn)`, for the integer lane types i8, i16, i32 and i64.
- `$sizenn`, `$sizenn1` and `$sizenn2` (all `= $size`), and `$lsizenn`, `$lsizenn1` and
  `$lsizenn2` (all `= $lsize`), are the "HACK" aliases that let the prose write N, N₁ and N₂.

They appear wherever numbers and lanes get a size:

- `num_(Fnn) = fN($sizenn(Fnn))` (1-syntax.spectec:264).
- The shape condition `$lsize(lanetype) * dim = 128` (1-syntax.spectec:334), which gives the
  shapes i8x16, …, f64x2.
- SIMD operator side conditions, for example `ADD_SAT sx -- if $lsizenn(Jnn) <= 16`
  (1-syntax.spectec:359) and `EXTEND half sx -- if $lsizenn2(Jnn_2) = 2·$lsizenn1(Jnn_1)`
  (1-syntax.spectec:386).
- Reduction premises such as `$jsize(Jnn) = M·2` for `v128.loadMxN` (8-reduction.spectec:505-509).

**What the regeneration removed.** In the old model all eight were Lean functions
(OLD_wasm2.0.lean:718-785). `size` has type `valtype → Option Nat`, so `lsize`, `isize`, `sizenn`
and `sizenn1` read `Option.get! (size …)` in their numeric cases; `jsize` and `lsizenn*` call
`lsize`. The backend now emits relations for all eight (wasm2.0.lean:728-829): the first four
because their bodies use `!`, the other four because they call `lsize`. Each relation has one
constructor per case of the old function (six for `fun_lsize`, one for each of the others):

```lean
-- old model
def lsize (v_lanetype : lanetype) : Nat :=
  match v_lanetype with
  | lanetype.I32 => Option.get! (size (valtype_numtype numtype.I32))   -- likewise I64, F32, F64
  | lanetype.I8 => psize packtype.I8                                   -- likewise I16
-- new model
inductive fun_lsize : lanetype → Nat → Prop where
  | fun_lsize_case_0 :
    (size (valtype_numtype numtype.I32)) ≠ none →
    fun_lsize lanetype.I32 (Option.get! (size (valtype_numtype numtype.I32)))
  ...
  | fun_lsize_case_4 : fun_lsize lanetype.I8 (psize packtype.I8)
```

- `fun_isize`, `fun_sizenn` and `fun_sizenn1` have the premise `size … ≠ none`.
- `fun_jsize`, `fun_lsizenn`, `fun_lsizenn1` and `fun_lsizenn2` have the premise
  `fun_lsize … var_0`, because they call `$lsize`.

Every user of these functions in the model now takes a relation witness and an output variable
instead of a function application:

```lean
-- old: wf_num_.num__case_1 … : wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x → …
-- new: wf_num_.num__case_1 … (var_0 : N) :
--        fun_sizenn (numtype_Fnn v_Fnn) var_0 → wf_fN var_0 var_x → …
-- old: wf_vbinop_Jnn_N.vbinop_Jnn_N_case_2 … : (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 → …
-- new: wf_vbinop_Jnn_N.vbinop_Jnn_N_case_2 … (var_0 : Nat) :
--        fun_lsizenn (lanetype_Jnn v_Jnn) var_0 → var_0 ≤ 16 → …
```

The same change applies to `wf_shape`, the `fun_binop_`, `fun_vbinop_`, `fun_vrelop_`, … cases, the
`vcvtop`/`vextunop`/`vextbinop` side conditions, and the `vload`/`vstore_lane` rules.

**What broke downstream.**

1. Any downstream text that used `lsize`, `sizenn`, … as a function, directly or through a
   definition such as `jlane` or `flane`, stopped compiling, with errors like "Unknown identifier
   `lsize`". 13 of the affected declarations needed no other change:
   `jlane`, `flane`, `jlane_some`, `flane_some`, `jlane_map_proj`, `jlane_proj_wf`,
   `lanes_Jnn_form`, `lanes_Fnn_form`, `Forall_lane_Jnn`, `Forall_iabs_total`,
   `shape_lanes_even`, `wf_opt_num_` and `zip_lane_rel`. Many of the re-proved declarations also
   mention these names.
2. Progress proofs now have to *supply* witnesses that the old rules never asked for, such as
   `fun_sizenn nt N`. They also have to *consume* hypotheses of the form `fun_lsizenn J n ∧ n ≤ 16`
   where the old ones had `lsizenn J ≤ 16`.

**Original sketch.** None was needed. The old model had the functions, and proofs evaluated them
(`simp [lsize, …]`, `decide`).

**Current construct.** Each of the eight functions has a definition and one or two bridging
lemmas:

- `def X`: the old model's definition, copied verbatim. It lives in namespace `TLC`, so unchanged
  proof text that says `lsize` now refers to it.
- `fun_X_X a : fun_X a (X a)`: the relation computes the old value, so it is total.
- `fun_X_eq : fun_X a n → n = X a`: the relation computes no other value, so it is functional.

`lsize`, `sizenn`, `lsizenn`, `lsizenn1` and `lsizenn2` have both lemmas. `isize` and `jsize` have
only `fun_X_X`, and `sizenn1` has only `fun_X_eq`, because the proofs use no more. Where both
exist, they give `fun_X a n ↔ n = X a`. In Wasm terms, `fun_lsize_lsize` and `fun_lsize_eq` say
that every lane type has exactly one bit width:

- |i8| = 8 and |i16| = 16;
- |i32| = |f32| = 32;
- |i64| = |f64| = 64.

`$size` is partial, but it is defined on every number type (the i8 and i16 lanes use `$psize`), so
the premise `size … ≠ none` always holds here.

*Proofs.*

- `fun_X_X`: `fun_lsize_lsize` does `cases` on the lane type, then the constructor;
  `fun_isize_isize` and `fun_sizenn_sizenn` apply the single constructor and do the `cases` inside
  the premise proof. The premise `size … ≠ none` reduces to `some 32 ≠ none`
  and similar (`simp [size, valtype_numtype]`, or `valtype_Inn` for `isize`). The derived relations
  (`jsize`, `lsizenn*`) pass `fun_lsize_lsize`.
- `fun_X_eq`: `cases h; rfl` (`cases h <;> rfl` for `fun_lsize`). For the derived relations
  (`lsizenn*`), `cases h` and then `fun_lsize_eq`.

**Where they are used.** 43 declarations, all in TypeProgress except `num_default_is_well_formed`.

*Builders* supply witnesses to generated constructors:

- `binop_total`, `relop_total`, `unop_not_none` and `testop_not_none` state that every well-typed
  `i32.add`, `f64.lt`, … on well-formed operands has a result. They pass `fun_sizenn_sizenn _`, the
  width N at which the operation is computed, to the cases of `fun_binop_`, `fun_relop_`,
  `fun_unop_` and `fun_testop_`.
- `vbinop_some`, `vrelop_some`, `vunop_real` and `t_progress_be_vshiftop` pass
  `fun_lsizenn_lsizenn _`.
- `vrelop_some` uses `fun_isize_isize` to pick the result lane type `Inn` with
  `$isize(Inn) = $size(Fnn)`. For example, the mask that `f32x4.eq` produces has i32 lanes
  (3-numerics.spectec:538-543).
- `t_progress_be_vload_pack`, `t_progress_be_vload_splat`, `t_progress_be_vload_lane` and
  `vstore_lane_progress` pass `fun_jsize_jsize` for the rule premises `$jsize(Jnn) = M·2` and
  `N = $jsize(Jnn)`. For example, `v128.load16x4_u` extends each lane to the lane type with
  `$jsize = 32`, which is i32.
- `num_default_is_well_formed` (TypePreservation) passes `fun_sizenn_sizenn` to
  `wf_num_.num__case_1`.

*Readers* turn a witness found in a hypothesis into an equation. After that, the side condition is
decided by computation:

- In `vbinop_some`, case `ADD_SAT`, `rwa [fun_lsizenn_eq hn] at hb` turns the validity premise into
  `lsizenn J ≤ 16`. That is the spec's statement that only `i8x16.add_sat_*` and `i16x8.add_sat_*`
  exist.
- In `vcvtop_zero_numtype`, `obtain rfl := fun_lsizenn2_eq hn1; obtain rfl := fun_sizenn1_eq hn0`
  is followed by `decide` on the spec condition `$sizenn1(Fnn_1) = 2·$lsizenn2(Inn_2)`. This rules
  out every float/integer pair except f64x2 → i32x4 (`i32x4.trunc_sat_f64x2_{s,u}_zero`).
- Other uses follow the same pattern:
  - `fun_lsize_eq` in `wf_lane_Jnn_inv`, `vrelop_some`, `t_progress_be_vextunop`,
    `t_progress_be_vextbinop` and `t_progress_be_vcvtop`;
  - `fun_sizenn_eq` in `binop_total`, `binop_before` and `wf_lane_Fnn_inv`;
  - `fun_sizenn1_eq` in `vcvtop_lane_total` and `vcvtop_full_lsize`;
  - `fun_lsizenn1_eq` and `fun_lsizenn2_eq` in those two and in `t_progress_be_vextunop` and
    `t_progress_be_vextbinop`.

*Unchanged text.* The 13 declarations listed above typecheck against the views exactly as they did
against the old functions. Eight of them mention a view directly and are among the 43: `jlane`,
`flane`, `jlane_proj_wf`, `Forall_lane_Jnn`, `Forall_iabs_total`, `shape_lanes_even`, `wf_opt_num_`
and `zip_lane_rel`. The other five (`jlane_some`, `flane_some`, `jlane_map_proj`, `lanes_Jnn_form`
and `lanes_Fnn_form`) use the views only through `jlane`, `flane`, `wf_lane_Jnn_inv` and
`wf_lane_Fnn_inv`.

Three size relations have no view because no downstream text mentions `fsize`, `sizenn2` or
`shsize`: `fun_fsize`, `fun_sizenn2` and `fun_shsize` (`$shsize(Lnn X N) = $lsize(Lnn)·N`,
2-syntax-aux.spectec:42).

#### B. `fzero` and `default_` (9 declarations)

**Wasm 2.0.** `$fzero(N) = POS (SUBNORM 0)` is +0 in fN(N) (1-syntax.spectec:68-69). For this
value to be well-formed (1-syntax.spectec:59-62), a `SUBNORM m` magnitude needs `m < 2^M(N)` and
the exponent `2 − 2^(E(N)−1)`. Here `$M(N) = $signif(N)` and `$E(N) = $expon(N)` are partial. They
are defined only for N = 32 (M = 23, E = 8) and N = 64 (M = 52, E = 11) (1-syntax.spectec:40-52).

`$default_(valtype)` (5-runtime-aux.spectec:7-15, `hint(partial)`) is the starting value of a
declared local when a function is invoked. `Step_read/call_addr` builds the frame
`{LOCALS val^k ($default_(t))*, MODULE mm}` (8-reduction.spectec:131-135). The value is:

- 0 for i32, i64 and v128;
- `$fzero(32)` for f32 and `$fzero(64)` for f64;
- `ref.null` for funcref and externref;
- undefined for `bot`. A local can never have type `bot`, because `Func_ok` requires `t ≠ BOT` for
  each local (6-typing.spectec:588).

**What the regeneration removed.**

In the old model (OLD_wasm2.0.lean:299-307, 11755):

- `def fzero (v_N : N) : fN := fN.POS (fNmag.SUBNORM 0)`, together with the model theorem
  `fzero_is_wf (v_N : N) … : wf_fN v_N (fzero v_N)` for *every* N. That theorem held for every N
  because the old `wf_fNmag` had no definedness premise: its side conditions used the total
  functions `fun_M v_N = Option.get! (signif v_N)` and `E v_N = Option.get! (expon v_N)`, which are
  default values for N ∉ {32, 64}. The proof `⟨Nat.two_pow_pos _, rfl⟩` works whatever their
  value: `0 < 2^k` holds for every k, and the exponent is a free argument of `fNmag_case_1`.
- `def default_ : valtype → Option val` used `fzero 32` and `fzero 64`.
- `Step_read.call_addr` took `Forall (fun t => default_ t ≠ none) t_lst`, with locals
  `val_lst ++ Map (fun t => Option.get! (default_ t)) t_lst`.

In the new model:

- `fun_M` and `fun_E` are relations with the premises `signif N ≠ none` and `expon N ≠ none`.
  `wf_fNmag` takes them as witnesses.
- `fzero` became the following relation:

  ```lean
  inductive fun_fzero : N → fN → Prop where
    | fun_fzero_case_0 (v_N : Nat) :
      wf_fN v_N (fN.POS (fNmag.SUBNORM 0)) → fun_fzero v_N (fN.POS (fNmag.SUBNORM 0))
  ```

  So `fun_fzero N _` holds only for N = 32 and N = 64. +0 exists at the two float widths that
  Wasm 2.0 has, and the "for every N" fact is gone.
- `default_` became `fun_default_ : valtype → Option val → Prop`, with eight constructors:
  - I32, I64, V128, FUNCREF and EXTERNREF, as before;
  - F32 and F64, which take a witness `fun_fzero 32 var_0` or `fun_fzero 64 var_0`;
  - a catch-all,
    `fun_default__case_7 x0 : ¬ fun_default__before_fun_default__case_7 x0 → fun_default_ x0 none`.
    The result is `none` exactly when no other clause applies, which means for BOT.
- `Step_read.call_addr` now takes a list `var_0_lst : List (Option val)` with
  - `var_0_lst.length = t_lst.length`,
  - `Forall₂ (fun o t => fun_default_ t o) var_0_lst t_lst`,
  - `Forall (· ≠ none) var_0_lst`,
  - and locals `val_lst ++ Map Option.get! var_0_lst`.
- `$zero(Fnn) = $fzero($size(Fnn))` (the relation `fun_zero`, wasm2.0.lean:926) also takes
  `fun_fzero` witnesses.

**What broke downstream.**

- `num_default`, `default_vals_ok` and `default_not_none` keep their text unchanged (the final
  cleanup rewrote only `num_default`'s doc comment), but they lost the names `fzero` and `default_`.
- `num_default_is_well_formed` must now give `wf_num_.num__case_1` a `fun_sizenn` witness and a
  `wf_fN` proof whose `wf_fNmag` step takes `fun_E` and `fun_M` witnesses.
- `default_val_ok`, `t_progress_e_call_addr` and the call case of `t_read_preservation` now have to
  produce or consume `fun_default_` witnesses.
- `zero_lane_wf` broke because `$zero` is now the relation `fun_zero`, whose float cases take
  `fun_fzero` witnesses.

**Original sketch.** The old proofs used the functions directly:

- `t_progress_e_call_addr` passed `default_not_none t_lst hbot` to `Step_read.call_addr`.
- `num_default_is_well_formed` unfolded `fzero` and `sizenn` and proved
  `wf_fN 32 (POS (SUBNORM 0))` inline, with `fNmag_case_1 32 (2 - 2^(E 32 - 1)) 0 ⟨by decide, rfl⟩`
  (likewise for 64).

**Current constructs.**

- `fzero` is the old definition: +0 at any N.
  - `fun_fzero_eq : fun_fzero N x → x = fzero N`: when `$fzero(N)` is defined, it is +0.
- `wf_fzero_32 : wf_fN 32 (fzero 32)`: +0 is a well-formed f32. It is a subnormal with mantissa
  0 < 2^23 and exponent 2 − 2^7 = −126. `wf_fzero_64` is the same for f64: 0 < 2^52 and exponent
  2 − 2^10 = −1022.
  *Proof:* `wf_fN.fN_case_0 (wf_fNmag.fNmag_case_1 …)`, with the witnesses
  `fun_E.fun_E_case_0 32 (by decide)` (E = 8) and `fun_M.fun_M_case_0 32 (by decide)` (M = 23). The
  mantissa bound is closed by `decide` and the exponent by `rfl`.
- `fun_fzero_32 : fun_fzero 32 (fzero 32)` and `fun_fzero_64` say that `$fzero(32)` and
  `$fzero(64)` are defined. Each is the constructor applied to the matching wf fact. There is no
  `fun_fzero_fzero` for all N, because it would be false.
- `default_` is the old definition, `none` only for BOT.
  - `fun_default_default t : fun_default_ t (default_ t)` holds for every value type t.
    *Proof:* `cases t`. F32 and F64 pass `fun_fzero_32` and `fun_fzero_64`. BOT uses the
    catch-all, whose negated premise holds because no "before" constructor targets BOT.
  - `fun_default_eq : fun_default_ t o → o = default_ t`.
    *Proof:* `cases h`. F32 and F64 rewrite with `fun_fzero_eq`; the other value constructors
    close by `rfl`. In the catch-all case, `cases t`: BOT is `rfl`, and every other t contradicts
    the premise because its "before" constructor exists. For F32 and F64 that constructor is
    instantiated with `fzero 32` and `fzero 64`.

**Where they are used.** 8 declarations.

- *Progress for a function call* (`t_progress_e_call_addr`). The invoked function's frame needs one
  default value per declared local:
  - the proof instantiates the rule's list with `List.map default_ t_lst`;
  - it proves the `Forall₂` with `fun_default_default`, via `Forall2_map_l`;
  - it gets "not `none`" from `default_not_none`, using `Func_ok`'s `t ≠ BOT`;
  - it gets well-formedness of each default from the regenerated
    `default__is_wf _ _ _ (fun_default_default t) …`.
- *Preservation for a function call* (`t_read_preservation`, case `call_addr`). The rule supplies
  some list `o_lst` with `Forall₂ (fun o t => fun_default_ t o) o_lst t_lst`. Induction with
  `fun_default_eq` gives `o_lst = Map default_ t_lst`. So the frame's locals are exactly the old
  ones, and the unchanged `default_vals_ok` types them (`Val_ok s (default_ t).get! t`).
  `default_val_ok` passes `fun_default_default t` to `default__is_wf`.
- `num_default_is_well_formed` (TypePreservation): the f32 and f64 zeros are well-formed, by
  `wf_num_.num__case_1 … (fun_sizenn_sizenn _) wf_fzero_32 rfl` and the analogous f64 term.
- `zero_lane_wf` (TypeProgress): for every number type, `$zero(nt)` exists and packs into a
  well-formed lane. The F32 and F64 cases are `fun_zero.fun_zero_case_2 _ (by decide) fun_fzero_32`
  and `fun_zero.fun_zero_case_3 _ (by decide) fun_fzero_64`. This is the zero padding that the
  `…_zero` conversions add, for example `f32x4.demote_f64x2_zero` (3-numerics.spectec:596-600).

#### C. Inversion of the state lookups (6 declarations)

**Wasm 2.0.** The state lookups (5-runtime-aux.spectec:74-90) index into the frame's module instance
and the store:

- `$type((s; f), x) = f.MODULE.TYPES[x]`
- `$func((s; f), x) = s.FUNCS[f.MODULE.FUNCS[x]]`, and likewise `$global`, `$table`, `$mem`, `$elem`
  and `$data`
- `$local((s; f), x) = f.LOCALS[x]`

SpecTec indexing is partial. For example, `$table((S; F), x)` is defined only if
x < |F.module.tables| and F.module.tables[x] < |S.tables|.

**What the regeneration removed.** In the old model these were total functions built on Lean's
`getElem!` (`l[i]!` is `default` when i is out of range):

```lean
-- old model (OLD_wasm2.0.lean:11996)
def fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
  match v_state with
  | state.mk_state s f => (s.TABLES)[(f.MODULE.TABLES)[proj_uN_0 v_tableidx]!]!
-- new model (wasm2.0.lean:12864)
inductive fun_table : state → tableidx → tableinst → Prop where
  | fun_table_case_0 (s : store) (f : frame) (x : uN) :
    ((f.MODULE.TABLES)[proj_uN_0 x]!) < (List.length (s.TABLES)) →
    (proj_uN_0 x) < (List.length (f.MODULE.TABLES)) →
    fun_table (state.mk_state s f) x ((s.TABLES)[(f.MODULE.TABLES)[proj_uN_0 x]!]!)
```

`fun_type` and `fun_local` have only one bound, because types and locals live in the frame. The
rules now name the looked-up instance as a variable:

- old: `Step_read.table_get_val … : i < |(fun_table z x).REFS| → …`
- new: `Step_read.table_get_val … (var_0 : tableinst) : i < |var_0.REFS| → … → fun_table z x var_0 → …`

Even the model's own `table_is_wf` used to need `iswf_tableinst_default` (the default table instance
is well-formed) to cover out-of-range indices. The new version uses the bound instead.

**What broke downstream, and why a lemma is needed.** Two kinds of proof text stopped
typechecking:

- proofs that unfolded the function, such as `simp only [fun_blocktype, fun_type, mkFunctype] at hf`
  in the old `bt_inversion`;
- proofs that used the term, such as `(fun_table (state.mk_state v_s v_f) x).REFS` in
  `t_read_preservation`.

Inverting the relation with `cases` substitutes the output only when the output is a variable. Here
the output can be a term. For example, `fun_blocktype z bt (mkFunctype bt1 bt2)` becomes
`fun_type z x (mkFunctype bt1 bt2)`. Then `cases` has to unify `mkFunctype bt1 bt2` with
`f.MODULE.TYPES[x]!`, and it fails. These lemmas state the constructor's content as an equation
instead.

**Original sketch.** None. The function unfolded by `simp` or `rfl`.

**Current constructs.** For X ∈ {global, table, mem, elem}:

`fun_X_inv : fun_X (state.mk_state s f) x v → x < |f.MODULE.Xs| ∧ f.MODULE.Xs[x]! < |s.Xs| ∧ v = s.Xs[f.MODULE.Xs[x]!]!`

`fun_type_inv` and `fun_local_inv` give the single bound together with `ft = f.MODULE.TYPES[x]!` or
`v = f.LOCALS[x]!`.

In Wasm terms, `fun_table_inv` reads: if `$table((S; F), x)` is defined and equals ti, then

- x is a table index of the current module instance;
- its address a = F.module.tableaddrs[x] is an address of the store;
- ti = S.tables[a].

*Proof:* `rintro ⟨⟩` on the only constructor, then return its premises and `rfl`.

**Where they are used.** 8 declarations.

*Preservation (TypePreservation).* `t_read_preservation`:

- `local.get`: `obtain ⟨_, rfl⟩ := fun_local_inv h0`. The value is F.locals[x], which has the
  local's type.
- `global.get`: `fun_global_inv`, then `lookup_global` types S.globals[F.module.globals[x]].value.
- `table.get`: `rw [← (fun_table_inv h2).2.2] at hrefs`. The references of
  S.tables[F.module.tables[x]] are typed by `table_refs_ok`, so the one returned is typed too.
- `table.init`: `fun_elem_inv h4`, together with `elem_refs_ok`.
- `call_indirect`: `(fun_type_inv h0).2`. The callee's type equals F.module.types[y], which is the
  type that validation used.

`table_grow_store_ok` uses `obtain ⟨_, _, htab⟩ := fun_table_inv htab; subst htab`, and
`memory_grow_store_ok` does the same with `fun_mem_inv`. This replaces the instance being grown by
the concrete store entry, S.tables[F.module.tables[x]] or S.mems[F.module.mems[0]], and the old
store-extension argument goes through.

*Progress (TypeProgress).*

- `t_progress_be_store_val`, `t_progress_be_store_pack` and `t_progress_be_vstore_lane`:
  `(fun_mem_inv Hm).1` gives `0 < |F.module.mems|`, which is the premise of the update relation
  `fun_with_mem`.
- `wf_config_mem_bytes` was restated to take a `fun_mem` witness. `fun_mem_inv` gives
  mi = S.mems[F.module.mems[x]] and the bound that the now-bounded `mem_bytes_wf` needs.

*`bt_inversion`* (ExtensionLemmas, restated): in the case `bt = _IDX x`, `(fun_type_inv ht).2` gives
F.module.types[x] = [t₁*] → [t₂*].

`fun_func` and `fun_data` have no inversion lemma, because no downstream proof inverts them:

- `fun_func`: no reduction rule uses `$func(z, x)`. `call` goes through `$funcaddr(z)[x]` and
  `call_addr` through `$funcinst(z)[a]` (8-reduction.spectec:119-135), and both stayed inline
  indexing with explicit bounds.
- `fun_data`: the `memory.init` case of preservation types the byte it reads as an `i32.const`.
  That typing comes from the configuration's well-formedness, not from the data instance.

#### D. Index bounds from `Moduleinst_ok` and typed lookups (11 declarations)

**Why they are needed.** In the old model a lookup was always "defined", so progress never had to
know that an index was in range. Take `table.get x` with x out of range: `fun_table z x` was the
default table instance, and one of the rules `table_get_val` and `table_get_trap` still applied.

In the new model both rules require `fun_table z x ti`. For an out-of-range x neither rule applies,
and the configuration is stuck. That matches the spec, where `$table(z, x)` is then undefined.
Progress must now prove that every lookup a well-typed instruction performs is defined.

Two facts in the progress hypotheses provide that:

1. The instruction's typing rule bounds the index against the context:
   - `Instr_ok.table_get` has `x < |C.TABLES|` (`if C.TABLES[x] = lim rt`,
     6-typing.spectec:390-392);
   - memory instructions have `0 < |C.MEMS|` (`C.MEMS[0] = mt`, for example
     6-typing.spectec:427-429). Wasm 2.0 has at most one memory, with index 0;
   - `Blocktype_ok` for `_IDX x` has `x < |C.TYPES|` (6-typing.spectec:207-209).
2. The configuration typing gives `Moduleinst_ok s f.MODULE C'`, through the motive
   `t_progress_be_P`.

`Moduleinst_ok` (B-soundness.spectec:200-230) provides both bounds that the lookup relations need:

- It pairs each address list of the instance with a type list of the context, through iterated
  premises such as `(Externaddr_ok: s |- GLOBAL globaladdr : GLOBAL globaltype)*`. So the two lists
  have the same length.
- `Externaddr_ok/global` (B-soundness.spectec:131) holds only if `s.GLOBALS[a]` is defined, that
  is, a < |s.GLOBALS|. The generated `Externaddr_ok.global` has the premise `a < List.length s.GLOBALS`.
- Data and element addresses are bounded by premises like
  `(Datainst_ok: s |- s.DATAS[dataaddr] : datatype)*`. The generated premises are
  `Forall (· < |s.DATAS|) dataaddr_lst` and `Forall (· < |s.ELEMS|) elemaddr_lst`.

**Original sketch.** Old progress needed none of this, with one exception.
`t_progress_be_memory_size` needed the memory's `Meminst_ok` entry from `Store_ok`. It derived
`f.MODULE.MEMS[0]! < |s.MEMS|` inline from `Moduleinst_ok_lengths`, `minst_invert_mems` and
`mem_zip_getElem!`. That is exactly the argument that `Moduleinst_ok_mem_addr` now packages. (The
only other index bound in old progress is the `call` rule's `x < |F.module.funcaddrs|`, an
inline-indexing premise in both models, which `t_progress_be_call` gets from `funcs_size`, then as
now.)

**Current constructs.**

`Moduleinst_ok_X_addr`, for X ∈ {global, mem, table, data, elem}:

`Moduleinst_ok_X_addr s minst C i : Moduleinst_ok s minst C → i < |C.Xs| → i < |minst.Xs| ∧ minst.Xs[i]! < |s.Xs|`

In Wasm terms, for tables: a module instance that is valid in store S with context C has, for every
table index x < |C.tables|, an address moduleinst.tableaddrs[x], and that address is < |S.tables|.

*Proof:*

- `Moduleinst_ok_lengths` gives `|minst.Xs| = |C.Xs|`, which transports the bound.
- `minst_invert_X s minst C C h ⟨rfl, …⟩` (instantiated with `inst_match C C`) gives, for every
  pair (a, t) in `minst.Xs.zip C.Xs`, the store bound a < |s.Xs| together with the store entry at a
  and the subtyping of its type to t (for elems: the bound, the entry and the typing of its
  references).
- `mem_zip_getElem!` exhibits the i-th pair.
- For data, `minst_invert_datas s minst C C h ⟨rfl, …⟩` gives the store bound per address
  rather than per pair: every a in `minst.DATAS` has a < |s.DATAS| and a data instance at a (read
  off `Moduleinst_ok`'s premise `Forall (· < |s.DATAS|)`). Its second component is applied to
  `minst.DATAS[i]!`, which lies in `minst.DATAS` by `getElem!_pos` and `List.getElem_mem`, so no
  zip pair is needed.

`fun_X_typed`, for X ∈ {global, mem, table, data, elem}:

`fun_X_typed s f C x : Moduleinst_ok s f.MODULE C → x < |C.Xs| → fun_X (state.mk_state s f) x (s.Xs[f.MODULE.Xs[x]!]!)`

`fun_type_typed` has the hypothesis `x < |C.TYPES|` and the conclusion
`fun_type (state.mk_state s f) x (f.MODULE.TYPES[x]!)`.

In Wasm terms: when the frame's module instance is valid, `$table(z, x)` is defined for every table
index x that validation accepted, and it equals S.tables[F.module.tableaddrs[x]].

*Proof:* apply the relation's only constructor to the two halves of `Moduleinst_ok_X_addr`. For
`fun_type`, transport the bound along `C.TYPES = minst.TYPES` (`minst_invert_functypes`).

**Where they are used.** 27 progress lemmas.

*The common pattern* is `t_progress_be_table_get`:

1. `obtain ⟨ti, Hti⟩ : ∃ ti, fun_table (state.mk_state s f) x ti := ⟨_, fun_table_typed s f C' x Hmod Hlen⟩`.
2. Split on `n < |ti.REFS|`.
3. Step with `Step_read.table_get_val … Hti` or `Step_read.table_get_trap … Hti`.

The same pattern covers:

- the other table instructions, with `fun_table_typed`: `table.set`, `table.size`, `table.fill`,
  `table.copy` and `table.init`;
- `table.init`, which also uses `fun_elem_typed`;
- 14 memory instructions, with `fun_mem_typed s f C' (uN.mk_uN 0)`: `memory.size`, `memory.fill`,
  `memory.copy`, `memory.init`, the `load` and `store` forms, the `v128.load*` forms and
  `v128.store_lane`;
- `memory.init`, which also uses `fun_data_typed`;
- `global.get`, with `fun_global_typed`.

*Block types.* For `bt = _IDX x`, `t_progress_be_block` and `t_progress_be_loop` build
`fun_blocktype z bt ([t₁*] → [t₂*])` from `fun_type_typed` and `lookup_types`. That is the premise
of `Step_read.block` and `Step_read.loop` (`$blocktype(z, _IDX x) = $type(z, x)`,
8-reduction.spectec:63-66).

*Updates.* The update relations `fun_with_global`, `fun_with_table`, `fun_with_elem`, `fun_with_data`
and `fun_with_mem` need only the instance-side bound, because `List.modify` on the store is total:

- `t_progress_be_global_set`, `t_progress_be_table_set`, `t_progress_be_elem_drop`,
  `t_progress_be_data_drop` and `t_progress_be_vstore` use `(Moduleinst_ok_X_addr …).1`.
- The other store cases (`store_val`, `store_pack`, `vstore_lane`) read the same bound with
  `(fun_mem_inv Hm).1` (family C).

`t_progress_be_memory_size` also uses `Moduleinst_ok_mem_addr` directly: `.2` picks the memory's
`Meminst_ok` entry from `Store_ok`.

*Not needed:*

- `local.get`: the bound comes from `C.LOCALS = map typeof F.LOCALS`, and the proof applies
  `fun_local_case_0` directly.
- `call`: `$funcaddr(z)[x]` is inline indexing, and its bound premise was already in the old rule.
- `call_indirect`: the proof splits on the generated "before" predicate. Either the call rule
  applies or the trap rule does.
- `table.grow` and `memory.grow`: the `-fail` rules (8-reduction.spectec:411, 591) have no lookup
  premise. In Wasm 2.0, growing may always fail.

So no progress case builds a `fun_func` witness, and the family has no lemma for function
addresses.

*Illustration.* The following module was run with wat2wasm 1.0.34 and wasmtime 49.0.1. It shows
both kinds of bound:

```wat
(module
  (table $t 2 funcref)
  (func $f)
  (elem (table $t) (i32.const 0) func $f)
  (func (export "is_null") (param i32) (result i32)
    (ref.is_null (table.get $t (local.get 0)))))
```

- The table index is static. Writing `table.get 1` instead is rejected by validation (wat2wasm:
  "table variable out of range: 1 (max 1)"). This is the `x < |C.tables|` premise that
  `fun_table_typed` turns into definedness of `$table(z, x)`.
- The element index is dynamic. `is_null(0)` returns 0, `is_null(1)` returns 1, and `is_null(2)`
  traps with "out of bounds table access". This is the case split on `n < |ti.REFS|` between
  `table.get-val` and `table.get-trap` (8-reduction.spectec:385-391).

#### Per-construct table

| Name | Module | Statement (in words) | Proof idea |
|---|---|---|---|
| `lsize` | HelperLemmas | Definition: the bit width of a lane type. 8 for i8, 16 for i16, 32 for i32/f32, 64 for i64/f64. The old model's `lsize`, copied verbatim. | By cases. Numeric lanes via `Option.get! (size …)`, packed lanes via `psize`. |
| `fun_lsize_lsize` | HelperLemmas | `fun_lsize lt (lsize lt)`: the `$lsize` relation holds of the view for every lane type. | `cases lt <;> constructor`. The premise `size … ≠ none` by `simp [size, valtype_numtype]`. |
| `fun_lsize_eq` | HelperLemmas | `fun_lsize lt n → n = lsize lt`: a lane type has no other width. | `cases h <;> rfl`. |
| `isize` | HelperLemmas | Definition: the width of an integer number type. 32 for i32, 64 for i64. | `Option.get! (size (valtype_Inn I))`. |
| `fun_isize_isize` | HelperLemmas | `fun_isize I (isize I)`. | The constructor. The premise by `cases I <;> simp [size, valtype_Inn]`. |
| `jsize` | HelperLemmas | Definition: the width of an integer lane type (i8, i16, i32, i64), `lsize (lanetype_Jnn J)`. | Definition. |
| `fun_jsize_jsize` | HelperLemmas | `fun_jsize J (jsize J)`. | The constructor applied to `fun_lsize_lsize`. |
| `sizenn` | HelperLemmas | Definition: the spec's N for a number type, `$size(nt)` (32 or 64). | `Option.get! (size (valtype_numtype nt))`. |
| `fun_sizenn_sizenn` | HelperLemmas | `fun_sizenn nt (sizenn nt)`. | The constructor. The premise by `cases nt <;> simp [size, valtype_numtype]`. |
| `fun_sizenn_eq` | HelperLemmas | `fun_sizenn nt n → n = sizenn nt`. | `cases h; rfl`. |
| `sizenn1` | HelperLemmas | Definition: the spec's N₁ for a number type. Same value as `sizenn`. | Same body as `sizenn`. |
| `fun_sizenn1_eq` | HelperLemmas | `fun_sizenn1 nt n → n = sizenn1 nt`. | `cases h; rfl`. |
| `lsizenn` | HelperLemmas | Definition: the spec's N for a lane type, `lsize lt`. | Definition. |
| `fun_lsizenn_lsizenn` | HelperLemmas | `fun_lsizenn lt (lsizenn lt)`. | The constructor applied to `fun_lsize_lsize lt`. |
| `fun_lsizenn_eq` | HelperLemmas | `fun_lsizenn lt n → n = lsizenn lt`. | `cases h`, then `fun_lsize_eq`. |
| `lsizenn1` | HelperLemmas | Definition: the spec's N₁ for a lane type, `lsize lt`. | Definition. |
| `fun_lsizenn1_lsizenn1` | HelperLemmas | `fun_lsizenn1 lt (lsizenn1 lt)`. | The constructor applied to `fun_lsize_lsize lt`. |
| `fun_lsizenn1_eq` | HelperLemmas | `fun_lsizenn1 lt n → n = lsizenn1 lt`. | `cases h`, then `fun_lsize_eq`. |
| `lsizenn2` | HelperLemmas | Definition: the spec's N₂ for a lane type, `lsize lt`. | Definition. |
| `fun_lsizenn2_lsizenn2` | HelperLemmas | `fun_lsizenn2 lt (lsizenn2 lt)`. | The constructor applied to `fun_lsize_lsize lt`. |
| `fun_lsizenn2_eq` | HelperLemmas | `fun_lsizenn2 lt n → n = lsizenn2 lt`. | `cases h`, then `fun_lsize_eq`. |
| `fzero` | HelperLemmas | Definition: positive zero `POS (SUBNORM 0)` at any width N (the old model's `fzero`). The relation `fun_fzero N` holds of it only for N = 32 and 64. | Definition. The binder `_v_N` is unused. |
| `fun_fzero_eq` | HelperLemmas | `fun_fzero N x → x = fzero N`: when `$fzero(N)` is defined, it is +0. | `cases h; rfl`. |
| `wf_fzero_32` | HelperLemmas | `wf_fN 32 (fzero 32)`: +0 is a well-formed f32. Subnormal, mantissa 0 < 2^23, exponent 2 − 2^7 = −126. | `fN_case_0` and `fNmag_case_1`, with `fun_E 32` (E = 8) and `fun_M 32` (M = 23) by `decide`. The exponent by `rfl`. |
| `wf_fzero_64` | HelperLemmas | `wf_fN 64 (fzero 64)`: +0 is a well-formed f64. Mantissa 0 < 2^52, exponent 2 − 2^10 = −1022. | As `wf_fzero_32`, with E = 11 and M = 52. |
| `fun_fzero_32` | HelperLemmas | `fun_fzero 32 (fzero 32)`: `$fzero(32)` is defined. | `fun_fzero_case_0 32 wf_fzero_32`. |
| `fun_fzero_64` | HelperLemmas | `fun_fzero 64 (fzero 64)`: `$fzero(64)` is defined. | `fun_fzero_case_0 64 wf_fzero_64`. |
| `default_` | HelperLemmas | Definition: the default value of a value type (the old model's `default_`). `i32.const 0`, `i64.const 0`, `f32.const +0`, `f64.const +0`, `v128.const 0`, `ref.null funcref`, `ref.null externref`, and `none` for `bot`. | By cases. |
| `fun_default_default` | HelperLemmas | `fun_default_ t (default_ t)` for every value type t. | `cases t`. F32 and F64 with `fun_fzero_32` and `fun_fzero_64`. BOT via the catch-all case, whose "before" premise is refuted by `cases`. |
| `fun_default_eq` | HelperLemmas | `fun_default_ t o → o = default_ t`: the default value is unique. | `cases h`. F32 and F64 by `fun_fzero_eq`. Catch-all: `cases t`. BOT by `rfl`; any other t contradicts the premise by exhibiting its "before" constructor. |
| `fun_type_inv` | HelperLemmas | If `$type((S;F), x) = ft`, then `x < F.module.types.length` and `ft = F.module.types[x]`. | `rintro ⟨⟩` on the only constructor, then the premise and `rfl`. |
| `fun_global_inv` | HelperLemmas | If `$global((S;F), x) = gi`, then `x < F.module.globals.length`, `F.module.globals[x] < S.globals.length` and `gi = S.globals[F.module.globals[x]]`. | `rintro ⟨⟩`, then the two premises and `rfl`. |
| `fun_table_inv` | HelperLemmas | The same for `$table`: both bounds, and `ti = S.tables[F.module.tables[x]]`. | `rintro ⟨⟩`, then the two premises and `rfl`. |
| `fun_mem_inv` | HelperLemmas | The same for `$mem`: both bounds, and `mi = S.mems[F.module.mems[x]]`. | `rintro ⟨⟩`, then the two premises and `rfl`. |
| `fun_elem_inv` | HelperLemmas | The same for `$elem`: both bounds, and `ei = S.elems[F.module.elems[x]]`. | `rintro ⟨⟩`, then the two premises and `rfl`. |
| `fun_local_inv` | HelperLemmas | If `$local((S;F), x) = v`, then `x < F.locals.length` and `v = F.locals[x]`. | `rintro ⟨⟩`, then the premise and `rfl`. |
| `Moduleinst_ok_global_addr` | TypeProgress | If module instance `minst` is valid in store S with context C and `i < C.globals.length`, then `i < minst.globals.length` and `minst.globals[i] < S.globals.length`. | The length from `Moduleinst_ok_lengths`. The store bound from `minst_invert_globals` at the i-th zip pair (`mem_zip_getElem!`). |
| `Moduleinst_ok_mem_addr` | TypeProgress | The same for memory addresses. | As above, with `minst_invert_mems`. |
| `Moduleinst_ok_table_addr` | TypeProgress | The same for table addresses. | As above, with `minst_invert_tables`. |
| `Moduleinst_ok_data_addr` | TypeProgress | The same for data addresses. | The length from `Moduleinst_ok_lengths`. The store bound from `minst_invert_datas` (every data address of the instance is below `S.datas.length`), applied at element i (`getElem!_pos`, `List.getElem_mem`). |
| `Moduleinst_ok_elem_addr` | TypeProgress | The same for element-segment addresses. | As the first row, with `minst_invert_elems`. |
| `fun_global_typed` | TypeProgress | If F's module instance is valid in S with context C and `x < C.globals.length`, then `$global((S;F), x)` is defined and equals `S.globals[F.module.globals[x]]`. | `fun_global_case_0` with both halves of `Moduleinst_ok_global_addr`. |
| `fun_mem_typed` | TypeProgress | The same for `$mem`. Used with x = 0 by 14 memory-instruction progress cases. | `fun_mem_case_0` with `Moduleinst_ok_mem_addr`. |
| `fun_table_typed` | TypeProgress | The same for `$table`. | `fun_table_case_0` with `Moduleinst_ok_table_addr`. |
| `fun_data_typed` | TypeProgress | The same for `$data`. | `fun_data_case_0` with `Moduleinst_ok_data_addr`. |
| `fun_elem_typed` | TypeProgress | The same for `$elem`. | `fun_elem_case_0` with `Moduleinst_ok_elem_addr`. |
| `fun_type_typed` | TypeProgress | If F's module instance is valid with context C and `x < C.types.length`, then `$type((S;F), x)` is defined and equals `F.module.types[x]`. | `fun_type_case_0`, with the bound transported along `C.TYPES = minst.TYPES` (`minst_invert_functypes`). |

#### Observations

- **Deleted as unused.** Eight more lemmas were written for these families and then deleted in the
  final cleanup, because no other proof used them: `fun_isize_eq`, `fun_jsize_eq`,
  `fun_sizenn1_sizenn1`, `fun_fzero_wf`, `fun_func_inv` and `fun_data_inv` (HelperLemmas), and
  `fun_func_typed` and `Moduleinst_ok_func_addr` (TypeProgress; `Moduleinst_ok_func_addr` was used
  only by `fun_func_typed`).

### 7.2 Repaired centrally: `bt_inversion`, `wf_config_mem_bytes`, `mem_bytes_wf`, and 16 constructs that compile again unchanged

#### `bt_inversion` (ExtensionLemmas; theorem) - restated and re-proved
*Statement (Wasm 2.0 terms):* a block type means the same thing at validation time and at run time. Suppose C' ⊢ bt : [t1*] → [t2*] (`Blocktype_ok`), S ⊢ F.module : C (`Moduleinst_ok`), C' agrees with C on types, funcs, globals, tables, mems, elems and datas (`inst_match`), and the run-time elaboration gives $blocktype((S; F), bt) = [bt1*] → [bt2*]. Then t1* = bt1* and t2* = bt2*. It is used in the `block` and `loop` cases of `t_read_preservation` (Step_read/block, Step_read/loop). The third premise changed from an equation to a relation witness:
old `fun_blocktype (state.mk_state v_S r_v_f) b_lstt = mkFunctype bt1 bt2 →`,
new `fun_blocktype (state.mk_state v_S r_v_f) b_lstt (mkFunctype bt1 bt2) →`.

**What broke and why.** The statement no longer elaborated, with the error "type mismatch: `mkFunctype bt1 bt2` has type `functype` but is expected to have type `functype → Prop`". Once `hf` became `sorry`, the `valtype` branch left its goals unsolved (`bt1 = [] ∧ bt2 = []` for ε, `bt1 = [] ∧ [t] = bt2` for t), and in the `typeidx` branch `simp only [fun_blocktype, fun_type, mkFunctype] at hf` made no progress.

The cause is that $blocktype (8-reduction.spectec:63) is now `inductive fun_blocktype : state → blocktype → functype → Prop`, with three constructors:
- `_RESULT ε` gives `[] → []`.
- `_RESULT t` gives `[] → [t]`.
- `_IDX x` requires a premise `fun_type z x ft`.

$type(z, x) = F.module.types[x] is now the relation `fun_type`, whose constructor requires x < |F.module.types|. So the old equation is ill-typed, and neither function can be unfolded any more.

The function views do not help: with them the original text gives the same three errors. $blocktype is partial through $type, so it has no function view. The main session restated the theorem before the repair agents started.

**Original proof sketch.**
- Case on the derivation of C' ⊢ bt : [t1*] → [t2*].
- `valtype` case (bt = `_RESULT t?`, typed [] → t?):
  - Split t? into ε and t.
  - `simp_all [fun_blocktype, mkFunctype]` computes $blocktype(z, _RESULT t?) = [] → t?.
  - Injectivity of the functype constructor then gives bt1 = [] and bt2 = t?.
- `typeidx` case (bt = `_IDX x` with `hlk : C'.types[x] = [t1*] → [t2*]`):
  - `minst_invert_functypes` (from `Moduleinst_ok` and `inst_match`) gives C'.types = F.module.types.
  - `simp only [fun_blocktype, fun_type, mkFunctype] at hf` unfolds $blocktype(z, _IDX x) = $type(z, x) = F.module.types[x], so `hf : F.module.types[x]! = [bt1*] → [bt2*]`.
  - After `rw [hty] at hlk`, `hlk.symm.trans hf` equates the two functypes.
  - Three `injection`s (the functype, then each `list.mk_list`) give t1* = bt1* and t2* = bt2*.

**Current proof sketch.** The case split on `Blocktype_ok` is the same, but the elaboration is now inverted instead of unfolded.
- `valtype` case:
  - After splitting t?, `cases hf` keeps only `fun_blocktype_case_0` (resp. `fun_blocktype_case_1`).
  - Unifying its output `[] → []` (resp. `[] → [t]`) with `mkFunctype bt1 bt2` substitutes bt1 and bt2.
  - `simp_all` closes the goal.
- `typeidx` case:
  - `hty` comes from `minst_invert_functypes` as before.
  - `cases hf` leaves only `fun_blocktype_case_2`, with `ht : fun_type (S; F) x (mkFunctype bt1 bt2)`.
  - The new HelperLemmas inversion lemma `fun_type_inv ht` gives the bound x < |F.module.types| (unused here) and `mkFunctype bt1 bt2 = F.module.types[x]!`.
  - Then `simp only [mkFunctype] at hf`, `rw [hty] at hlk`, `hlk.symm.trans hf.symm` and the same three `injection`s finish.
- The callers (`t_read_preservation` block/loop, cluster P1) pass the new rule premise `fun_blocktype z bt var_0` after substituting `var_0 = t_1* → t_2*`.

#### `num_default` (TypePreservation; def) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* the zero value of each number type, as a `num_`:
- 0 for i32 and i64;
- +0 for f32 and f64, that is $fzero(N) = POS (SUBNORM 0) at N = 32 and 64 (`fzero 32`, `fzero 64`).

It ports Rocq `type_preservation.v:19`. In Lean only `num_default_is_well_formed` uses it. In Rocq that lemma is commented out (`type_preservation.v:75`), so nothing uses `num_default` there.

**What broke and why.** The error was "Unknown identifier `fzero`" in the `F32` and `F64` branches. $fzero (1-syntax.spectec:68) became the relation `fun_fzero N x`, whose only constructor also requires `wf_fN N (POS (SUBNORM 0))`. The old model's `def fzero` therefore no longer exists.

**Original proof sketch.** None: this is a definition by cases on the number type.

**Current proof sketch.** The text of the definition is unchanged (the final cleanup rewrote only its doc comment). `fzero` now resolves to the HelperLemmas function view `fzero (_v_N : N) : fN := fN.POS (fNmag.SUBNORM 0)`, which is the old model's definition.
- `fun_fzero_eq` says that any `fun_fzero N` output is `fzero N`.
- The relation holds of `fzero N` only where `wf_fN N (fzero N)` holds. HelperLemmas proves this for 32 and 64 (`wf_fzero_32/64`, `fun_fzero_32/64`), the only widths `num_default` uses.
- Its user `num_default_is_well_formed` (re-proved in P23) now builds the float cases as `wf_num_.num__case_1 … (fun_sizenn_sizenn _) wf_fzero_32 rfl` (resp. 64).

#### `default_vals_ok` (TypePreservation; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* in a well-formed store S, if every type t in t* has a default value ($default_(t) ≠ ε), then the default values ($default_(t))* have types t* pointwise. In Lean this is a `Forall₂` of `Val_ok s v t` (S ⊢ v : t) between `t_lst` and `Map (fun t => Option.get! (default_ t)) t_lst`. It types the ($default_(t))* part of the locals for `Frame_ok` in the `call_addr` case of `t_read_preservation`, where Step_read/call_addr builds F.locals = val^k ($default_(t))* (the val^k part is typed by the argument values).

**What broke and why.** The error was "Function expected at `default_`", twice in the statement and once in the proof. $default_ (5-runtime-aux.spectec:7) became the relation `fun_default_ : valtype → Option val → Prop`. Its f32/f64 cases go through `fun_fzero`, and its `none` case is guarded by `¬ fun_default__before_fun_default__case_7 t`. The old `def default_` is gone, so autoImplicit turned the name into a variable of unknown type and the statement no longer elaborated. The full log has two more errors (the data file keeps three): in the cons case the call of `default_val_ok` failed with "Unknown identifier `default_val_ok`" (that lemma's statement uses `default_` too), followed by a type mismatch in the argument of the IH.

**Original proof sketch.** Induction on t*, building a mathlib `List.Forall₂`:
- nil: `Forall₂.nil`.
- t :: ts: the head comes from `default_val_ok s t`, which says the default value is well-formed and has type t:
  - `Val_ok.numtype` for i32/i64/f32/f64;
  - `Val_ok.vectype` for v128;
  - `Val_ok.reftype` with `Ref_ok.null` for funcref/externref;
  - BOT is excluded by the hypothesis.
- The tail comes from the IH.
- `from_mathlib_forall₂` converts the result to the model's zip-based `Forall₂`.

**Current proof sketch.** The text and structure are unchanged. `default_` now resolves to the HelperLemmas function view (the old definition). `fun_default_default` says the relation holds of it, and `fun_default_eq` says it is the relation's only output.
- Underneath, `default_val_ok` (re-proved in P1) gets well-formedness from the relation-based `default__is_wf`, applied to the witness `fun_default_default t`.
- In the caller (the `call_addr` case of `t_read_preservation`, P1), the rule now has premises |o*| = |t*| and `Forall₂ (fun o t => fun_default_ t o) o_lst t_lst`. These are first turned into `o_lst = Map default_ t_lst` with `fun_default_eq`, and the rule's `o ≠ none` premise into `Forall (default_ t ≠ none)`. After that, `default_vals_ok` applies as before.

#### `flane` (TypeProgress; def) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* `flane F l` says that l is a float lane of shape F: `l = mk_lane__1 F x` with x a well-formed fN(|F|), written `wf_fN (sizenn (numtype_Fnn F)) x`. This is the spec's lane_(Fnn) = fN($sizenn(Fnn)) (1-syntax.spectec:277).

**What broke and why.** The error was "Unknown identifier `sizenn`" in the body. $sizenn (1-syntax.spectec:234) became the relation `fun_sizenn nt n`, with premise `$size(nt) ≠ ε`. The old `def sizenn` no longer exists. Everything stated with `flane` broke along with it: `flane_some`, `lanes_Fnn_form` and `zip_flane_wf`.

**Original proof sketch.** None: this is a definition (Rocq `type_progress.v:2160`).

**Current proof sketch.** The text is unchanged.
- `sizenn` is now the HelperLemmas function view `sizenn nt := Option.get! (size (valtype_numtype nt))`, which is the old definition. It is tied to the relation by `fun_sizenn_sizenn` and `fun_sizenn_eq`.
- The model's float `wf_lane_` constructor now carries a `fun_sizenn` witness. `wf_lane_Fnn_inv` (re-proved in Q2) turns that witness into `n = sizenn …` with `fun_sizenn_eq` and rewrites the lane's `wf_fN n x` with it, so its unchanged conclusion is again exactly `flane`'s body.

#### `flane_some` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* every lane of a list of `flane F` lanes projects as a float lane (`proj_lane__1 l ≠ none`). It is used in the float case of `vrelop_some` (`fun_vrelop_` has a result), which `t_progress_be_vrelop` uses for progress of e.g. `f32x4.lt`.

**What broke and why.** No error was recorded for it: against the new model it still compiled, because Lean's error recovery kept `flane`'s existential (with `sorry` for the unknown `sizenn …`). It counts as broken because its proof unfolds `flane`: once the cascade replaced the broken `flane` by `sorry`, `flane F l` no longer unfolded to the existential that the proof destructs.

**Original proof sketch.** For l ∈ L, destruct `flane F l` into `l = mk_lane__1 F x` (substituted), then `simp [proj_lane__1]`.

**Current proof sketch.** Identical. It compiles again once `flane` elaborates with the `sizenn` view.

#### `jlane` (TypeProgress; def) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* `jlane J l` says that l is an integer lane of shape J: `l = mk_lane__0 J x` with x ∈ iN(|J|), i.e. 0 ≤ x ≤ 2^|J| − 1, written `wf_uN (lsize (lanetype_Jnn J)) x`. This is the spec's lane_(Jnn) = iN($lsize(Jnn)) (1-syntax.spectec:276).

**What broke and why.** The error was "Unknown identifier `lsize`" in the body. $lsize (1-syntax.spectec:211) became the relation `fun_lsize lt n`, whose numeric cases require `$size(nt) ≠ ε`. The old `def lsize` no longer exists. Most declarations stated with `jlane` broke too, among them `jlane_some`, `jlane_map_proj`, `jlane_proj_wf`, `lanes_Jnn_form`, `zip_lane_rel`, `zip_lane_wf` and `zip_lane_wf2` (some of these also use `lsize` directly). `zip_wf` only passes `jlane` hypotheses through and still compiled.

**Original proof sketch.** None: this is a definition (Rocq `type_progress.v:2158`).

**Current proof sketch.** The text is unchanged.
- `lsize` is now the HelperLemmas function view: the old match on the lane type (`Option.get! (size …)` for i32/i64/f32/f64, `psize` for i8/i16). It is tied to the relation by `fun_lsize_lsize` and `fun_lsize_eq`.
- The model's integer `wf_lane_` constructor now carries a `fun_lsize (lanetype_Jnn J) n` witness. `wf_lane_Jnn_inv` (re-proved in Q2) turns it into `n = lsize …` with `fun_lsize_eq` and rewrites the lane's `wf_uN n x` with it, so its unchanged conclusion is again exactly `jlane`'s body.

#### `jlane_map_proj` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* for a list L of `jlane J` lanes, re-injecting the projected integers gives back L: `map (mk_lane__0 J) (map (get! ∘ proj_lane__0) L) = L`. In the progress case for `i8x16.shuffle` (`t_progress_be_vshuffle`), it discharges the Step_pure/vshuffle premise `Map (mk_lane__0 ·) c'* = $lanes_(c_1) ++ $lanes_(c_2)`.

**What broke and why.** No error was recorded for it (it still compiled against the new model). It counts as broken because its proof unfolds `jlane`, which the cascade replaced by `sorry` after `jlane`'s own error (`lsize` in its body).

**Original proof sketch.**
- Induction on L.
- For l :: L, destruct `jlane J l` into `l = mk_lane__0 J x` (substituted), and apply the IH to the tail.
- After `simp only [List.map_cons, List.cons.injEq]`, the head equation `mk_lane__0 J (get! (proj_lane__0 (mk_lane__0 J x))) = mk_lane__0 J x` holds by `rfl`.

**Current proof sketch.** Identical.

#### `jlane_some` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* every lane of a list of `jlane J` lanes projects as an integer lane (`proj_lane__0 l ≠ none`). It discharges the `proj_lane__0 · ≠ none` premises of the generated integer-shape vector rules. It is used in `vbinop_some`, `vrelop_some`, and the vbitmask, vswizzle, vextunop, vextbinop and vnarrow progress cases.

**What broke and why.** No error was recorded for it (it still compiled against the new model). It counts as broken because its proof unfolds `jlane`, which the cascade replaced by `sorry` after `jlane`'s own error.

**Original proof sketch.** For l ∈ L, destruct `jlane J l` into `l = mk_lane__0 J x`, then `simp [proj_lane__0]`.

**Current proof sketch.** Identical.

#### `lanes_Fnn_form` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* if the float shape F x M is valid (`wf_shape`) and c is a well-formed v128 (`wf_uN 128 c`), every lane of $lanes_(F x M, c) is `flane F`. It is used in the float cases of `vbinop_some` and `vrelop_some`.

**What broke and why.** The errors were "don't know how to synthesize implicit argument `sizenn`" at `@wf_lane_Fnn_inv ?m ?m F l (Hl l hl)`, plus the unsolved goal `flane F l`. Without the views, the statement of `wf_lane_Fnn_inv` mentions the vanished `sizenn` (now the relation `fun_sizenn`). autoImplicit made `sizenn` an implicit argument of unknown type, and that argument cannot be inferred at this use. In addition, `flane` itself had an error.

**Original proof sketch.**
- The model axiom `lanes__is_wf` gives `wf_lane_ F l` for each lane l. It states that the lanes of a well-formed vector at a valid shape are well-formed lanes of lane type $lanetype(sh).
- `wf_lane_Fnn_inv F l` turns this into `∃ x, l = mk_lane__1 F x ∧ wf_fN (sizenn F) x`, which is `flane F l` by definition.

**Current proof sketch.** The text is identical. What changed underneath:
- `sizenn` is the view.
- `wf_lane_Fnn_inv` (re-proved in Q2) inverts the new constructor `wf_lane_.lane__case_1 F' c n Hn Hc Heq`, which has `Hn : fun_sizenn (numtype_Fnn F') n` and `Hc : wf_fN n c`. It rewrites `Hc` with `fun_sizenn_eq Hn`.

#### `lanes_Jnn_form` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* if the integer shape J x M is valid and c is a well-formed v128, every lane of $lanes_(J x M, c) is `jlane J`. It is used in integer `vbinop_some`/`vrelop_some` and in the vbitmask, vswizzle, vshuffle, vextunop, vextbinop and vnarrow progress cases.

**What broke and why.** The errors were "don't know how to synthesize implicit argument `lsize`" at `@wf_lane_Jnn_inv ?m ?m J l Hw (wf_lane_Jnn_some J l Hw)`, plus the unsolved goal `jlane J l`. The mechanism is the same as for `lanes_Fnn_form`: `lsize` vanished (it is now `fun_lsize`), the statement of `wf_lane_Jnn_inv` got an auto-bound implicit, and `jlane` itself had an error.

**Original proof sketch.**
- `lanes__is_wf` gives `wf_lane_ J l` for each lane l.
- `wf_lane_Jnn_some` gives `proj_lane__0 l ≠ none`, because `lane_` has disjoint integer and float constructors.
- `wf_lane_Jnn_inv` then gives `∃ x, l = mk_lane__0 J x ∧ wf_uN (lsize J) x`, which is `jlane J l`.

**Current proof sketch.** The text is identical. Underneath, `wf_lane_Jnn_inv` and `wf_lane_Jnn_some` (re-proved in Q2) match the new constructor `wf_lane_.lane__case_0 J' c n Hn Hc Heq`, which has `Hn : fun_lsize (lanetype_Jnn J') n`. `wf_lane_Jnn_inv` rewrites `Hc : wf_uN n c` with `fun_lsize_eq Hn`.

#### `Forall_iabs_total` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* take a list of in-range J-lanes (`mk_lane__0 J x` with x ∈ iN(|J|)). There are lane results vs with $iabs_(|J|, x) = v lane by lane, each forming a well-formed J-lane. In Lean the lane-by-lane relation is `Forall₂ (fun v l => fun_iabs_ (lsizenn J) (get! (proj_lane__0 l)) v)` plus `vs.length = ls.length`. The lemma supplies the results in the integer `abs` cases (`J x M.abs`, e.g. `i8x16.abs`) of `vunop_real` (a real case of `fun_vunop_` applies), which `t_progress_be_vunop` uses, via `vunop_total` and `vunop_not_none`, for Step_pure/vunop.

**What broke and why.** The errors were "Function expected at `lsize`" and "Function expected at `lsizenn`" in the statement, so the statement no longer elaborated, and the proof then ended with an unsolved goal. $lsize became `fun_lsize`, and $lsizenn (1-syntax.spectec:241) became `fun_lsizenn lt n` with premise `fun_lsize lt n`.

**Original proof sketch.**
- `apply Forall_exists_Forall2`: this turns "each lane has a result" into a list of results with `Forall₂ ∧ length ∧ Forall`.
- For each lane, destruct `l = mk_lane__0 J x` (with `Hx`) and `subst`, so that `get! (proj_lane__0 l)` reduces to x.
- `iabs_lane_total J x Hx` gives v with `fun_iabs_ (lsizenn J) x v` (via `signed_total` and `fun_iabs__case_0`), and the well-formed lane `mk_lane__0 J v` (via `iabs__is_wf`).

**Current proof sketch.** The text is identical. What changed underneath:
- `iabs_lane_total` (re-proved in Q2) builds the result lane with the new constructor's witness: `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) (iabs__is_wf …) rfl`.
- In `vunop_real` (Q2), the new `fun_vunop_` abs cases take the lane width as a variable with a premise `fun_lsizenn (lanetype_Jnn J) var_1`. It is discharged by `fun_lsizenn_lsizenn`, so the results of `Forall_iabs_total` (stated at `lsizenn J`) fit.

#### `Forall_lane_Jnn` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* suppose every lane of a list is a well-formed lane of lane type J (`wf_lane_ (lanetype_Jnn J)`) and projects as an integer lane. Then every lane is `mk_lane__0 J x` with x ∈ iN(|J|). This is the list version of `wf_lane_Jnn_inv`. `vunop_real` uses it to obtain the in-range lanes that `Forall_iabs_total` needs.

**What broke and why.** The error was "Function expected at `lsize`" in the conclusion, so the statement no longer elaborated, and the proof ended with an unsolved goal. The cause is that $lsize became `fun_lsize`.

**Original proof sketch.** Pointwise: `wf_lane_Jnn_inv J l (Hw l hl) (Hs l hl)`.

**Current proof sketch.** The text is identical. It relies on `wf_lane_Jnn_inv`, re-proved in Q2 with `fun_lsize_eq` as described under `lanes_Jnn_form`.

#### `default_not_none` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* every value type other than BOT has a default value. For t* with all t ≠ BOT, $default_(t) ≠ ε. Validation (Func_ok, `(if t =/= BOT)*`) excludes BOT locals, so this lemma yields the defaults that Step_read/call_addr needs. It is used in `t_progress_e_call_addr`.

**What broke and why.** The statement failed with "Function expected at `default_`". In the proof, `simp [default_]` failed in each of the seven non-BOT cases with "Variable `default_` is not a proposition or let-declaration", leaving the goals unsolved. The cause is that $default_ became `fun_default_`.

**Original proof sketch.** Case on t. For BOT, the hypothesis is contradicted. For the other seven types, `simp [default_]` computes `default_ t = some …` and closes `some … ≠ none`.

**Current proof sketch.** The text is identical; `simp [default_]` now unfolds the HelperLemmas view, which has the old definition. In the caller `t_progress_e_call_addr` (Q5), the call_addr step is built with `var_0_lst := List.map default_ t_lst`:
- its `Forall₂ fun_default_` premise comes from `fun_default_default`;
- its `≠ none` premise comes from this lemma.

#### `jlane_proj_wf` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* projecting a list of `jlane J` lanes to their integers gives integers in iN(|J|) (`wf_uN (lsize J)`). In the `i8x16.swizzle` and `i8x16.shuffle` progress cases, it shows that the integers c'* taken from the input lanes are in iN(8). That discharges the `wf_lane_` premises of Step_pure/vswizzle (for the selected lanes) and of Step_pure/vshuffle (for all of c'* and for the selected lanes).

**What broke and why.** The error was "Function expected at `lsize`" in the conclusion, so the statement no longer elaborated. The cause is that $lsize became `fun_lsize`.

**Original proof sketch.**
- Take x in the mapped list. `List.mem_map` gives a lane l ∈ L with x = get! (proj_lane__0 l).
- Destructing `jlane J l` (l = mk_lane__0 J y, with y in range) reduces x to y.
- `exact hy` finishes.

**Current proof sketch.** Identical.

#### `shape_lanes_even` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* a full-width integer shape J x M has an even number of lanes, `¬ Odd |$lanes_(J x M, c)|`. Full width means |J|·M = 128, given as the hypothesis `lsize J * M = 128`. It is used in progress for `extadd_pairwise` (vextunop) and `dot` (vextbinop), where lanes are combined pairwise.

**What broke and why.** The statement failed with "Function expected at `lsize`". In the proof, `simp only [lsize, …]` failed with "Variable `lsize` is not a proposition or let-declaration" and "`simp` made no progress". The cause is that $lsize became `fun_lsize`.

**Original proof sketch.**
- `rw [lanes_len]`, using the axiom |$lanes_(lt x M, c)| = M.
- Case on J ∈ {I32, I64, I8, I16}, and compute `lsize` with `simp only [lsize, lanetype_Jnn, psize, size, valtype_numtype, Option.get!] at H`. This gives 32·M = 128, 64·M = 128, 8·M = 128 or 16·M = 128.
- `omega` gives M ∈ {16, 8, 4, 2}, and `decide` proves `¬ Odd M` in each case.

**Current proof sketch.** The text is identical. `simp only [lsize, …]` unfolds the view, which has the same equations as the old `lsize`. The callers (vextunop/vextbinop progress, Q4) now derive the hypothesis from the new `wf_shape.shape_case_0 _ _ n hn _ h`, which has `hn : fun_lsize J n` and `h : n * M = 128`, by `rw [← fun_lsize_eq hn]`.

#### `wf_config_mem_bytes` (TypeProgress; theorem) - restated and re-proved
*Statement (Wasm 2.0 terms):* in a well-formed configuration (S; F); instr*, the bytes of the memory instance mi = $mem((S; F), x) = S.mems[F.module.mems[x]] are well-formed bytes. It provides the well-formedness of `mi.bytes[i + ao.offset : n]` when progress reads a value back from memory (`load`, `vload`, and their pack, splat, zero and lane forms). The statement now takes the lookup witness:
old `(x : memidx) : wf_config … → Forall wf_byte ((fun_mem (state.mk_state s f) x).BYTES)`,
new `(x : memidx) (mi : meminst) : wf_config … → fun_mem (state.mk_state s f) x mi → Forall wf_byte mi.BYTES`.

**What broke and why.** The error was "Invalid field `BYTES`", because `fun_mem (state.mk_state s f) x` now has type `meminst → Prop`. $mem (5-runtime-aux.spectec:78) became `inductive fun_mem : state → memidx → meminst → Prop`, whose constructor requires F.module.mems[x] < |S.mems| and x < |F.module.mems|. `fun_mem` is partial, so it has no function view, and the statement had to change. The main session restated it.

**Original proof sketch.**
- Invert wf_config, then wf_state, then wf_store, to get `h : Forall wf_meminst S.mems`.
- The old function `fun_mem` unfolded definitionally to `S.mems[F.module.mems[x]!]!`.
- So `mem_bytes_wf _ _ h` closed the goal without any bound. The out-of-range case was covered by the default-value branch of `mem_bytes_wf`.

**Current proof sketch.**
- `fun_mem_inv hm` (new HelperLemmas inversion lemma) gives x < |F.module.mems|, `hlt : F.module.mems[x] < |S.mems|`, and `mi = S.mems[F.module.mems[x]]`.
- `rw` with the last of these, then invert wf_config, wf_state and wf_store as before.
- `mem_bytes_wf _ _ hlt h` closes the goal, using the now-bounded `mem_bytes_wf` with the store-address bound `hlt`.
- The callers (load/vload progress, Q6a/Q6b) pass the same witness `fun_mem (S; F) 0 mi` (`Hm` in the load cases, `Hmem` in the vload cases) that they also use for the step rule's own `fun_mem` premise. They build it with `fun_mem_typed` from S ⊢ F.module : C and the validation fact that C has memory 0.

#### `wf_opt_num_` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* the partial functions $idiv_ / $irem_ return ε on division by zero, and $idiv_ also on signed overflow. A well-formed optional iN(|I|) result of this kind wraps into well-formed I `num_`s, both pointwise and through `list_ num_ (Option.map (mk_num__0 I) o)`. It is used in `binop_total`/`binop_before` for `i32/i64.div_sx` and `rem_sx`.

**What broke and why.** The error was "Function expected at `sizenn`" in the hypothesis, so the statement no longer elaborated. The cause is that $sizenn became `fun_sizenn`. The integer constructor `wf_num_.num__case_0` used in the proof did not change.

**Original proof sketch.**
- Case on o. For `none`, both lists are empty.
- For `some x`, after `cases I`, `wf_num_.num__case_0 _ _ _ (by decide) (Ho x _) rfl` builds `wf_num_ I (mk_num__0 I x)`. Here `Ho x : wf_uN (sizenn I) x` is accepted definitionally as `wf_uN (get! (size I)) x`.
- Both conjuncts follow by `simp` on the singleton lists.

**Current proof sketch.** The text is identical. The `sizenn` view unfolds to the same `Option.get! (size (valtype_numtype nt))`, so the definitional match still works. The callers (`binop_total` and `binop_before`, Q1) now also discharge the `fun_sizenn` premise of the new `fun_binop_` div/rem cases with `fun_sizenn_sizenn`.

#### `zip_lane_rel` (TypeProgress; theorem) - unchanged; compiles again via the function views
*Statement (Wasm 2.0 terms):* let R be a total relation on in-range |J|-bit integers whose results satisfy W. Applied lane-wise to two equal-length lists of `jlane J` lanes, R yields results vs, one per lane pair (`Forall₃`), all satisfying W, with |vs| = |L1|. It is used for integer `vbinop` min/max/add_sat/sub_sat and `vrelop` lt/gt/le/ge (e.g. `i8x16.add_sat_s`, `i32x4.lt_s`), with R = `fun_imin_`, `fun_iadd_sat_`, `fun_ilt_`, … at width `lsizenn J`.

**What broke and why.** The error was "Function expected at `lsize`", twice in the totality hypothesis, so the statement no longer elaborated. The cause is that $lsize became `fun_lsize`.

**Original proof sketch.** Induction on L1, generalizing L2:
- nil: vs = [].
- l1 :: L1':
  - L2 must be a cons, by the length hypothesis.
  - Destruct both heads as `mk_lane__0 J x1` and `mk_lane__0 J x2`, and apply the IH to the tails.
  - The totality hypothesis on x1 and x2 gives r with R x1 x2 r and W r. Take vs = r :: vs'.
  - The `Forall₃` over the zipped lists splits into head and tail membership; the head case is `simpa [proj_lane__0] using Hr`.
  - `Forall W` and the length follow in the same way.

**Current proof sketch.** The text is identical. The callers (`vbinop_some`/`vrelop_some`, Q2) rebuild the result lanes with `wf_lane_.lane__case_0 … (fun_lsize_lsize _)` and discharge the `fun_lsizenn` premises with `fun_lsizenn_lsizenn`.

#### `mem_bytes_wf` (TypeProgress; theorem) - changed for default-independence
*Statement (Wasm 2.0 terms):* the bytes of entry ms[k] of a list of well-formed memory instances (e.g. S.mems) are well-formed bytes. It is now stated for in-range k only:
old `theorem mem_bytes_wf (ms : List meminst) (k : N) :`,
new `theorem mem_bytes_wf (ms : List meminst) (k : N) (hk : k < ms.length) :`.

**What broke and why.** Nothing broke: it compiled unchanged both with and without the function views. The main session's default-value audit (a kernel replay with every `Inhabited` instance opaque) found it to be the only downstream theorem whose proof reads a default value. Its out-of-range case used `(default : meminst).BYTES = []`, mirroring Rocq's default-valued `ms [| k |]`. The main session therefore added the bound.

**Original proof sketch.** `by_cases k < |ms|`:
- In range: `getElem!_pos` and `List.getElem_mem` give ms[k] ∈ ms, hence `wf_meminst ms[k]`. Inverting `meminst_case_` gives the bytes.
- Out of range: `getElem!_neg` turns `ms[k]!` into the default meminst. Its BYTES is `[]` by `rfl`, so the `Forall` holds vacuously.

**Current proof sketch.** Only the in-range branch remains, now using `hk`:
- `getElem!_pos ms k hk` and `List.getElem_mem hk` give `wf_meminst ms[k]!`.
- Generalize `ms[k]!` and invert `wf_meminst.meminst_case_` to get `Forall wf_byte` for the bytes.
- The only caller, `wf_config_mem_bytes`, supplies `hk` as the bound F.module.mems[x] < |S.mems| obtained from `fun_mem_inv`.

### 7.3 P1, `TypePreservation`: `Step_read` preservation (2 constructs)

#### `t_read_preservation` (TypePreservation; theorem) - re-proved

*Statement (Wasm 2.0 terms):* Subject reduction for the read-only reduction `Step_read` (S; F; instr\* ↪ instr'\*, the 47 rules of 8-reduction.spectec that read the state (store and frame) but do not change it: block, loop, call, call_indirect, call_addr, ref.func, local.get, global.get, table.get/size/fill/copy/init, load/vload, memory.size/fill/copy/init). If the configuration is well formed, ⊢ S ok, S ⊢ F.module : C, the locals F.locals have the types C'.locals (`Vals_ok`, lengths included), C' agrees with C on types/funcs/globals/tables/mems/elems/datas (`inst_match`), and S; C' ⊢ instr\* : t1\* → t2\*, then S; C' ⊢ instr'\* : t1\* → t2\*. The statement is unchanged.

**What broke and why.** The proof broke in both cascades. The statement still elaborates. The first recorded errors:
- Without the function views: `Unknown identifier bt_inversion` in the block and loop cases, and `rcases` then fails on the unknown term. The cause is that the statement of `bt_inversion` (ExtensionLemmas) no longer elaborates, so this cascade deleted it. Its premise is `fun_blocktype (S;F) bt = mkFunctype bt1 bt2`, but `fun_blocktype` is now a relation (`state → blocktype → functype → Prop`), so the left side has type `functype → Prop` and the equation is ill-typed.
- With the function views and the restated `bt_inversion`, in block: "`h0` has type `functype`, but `bt_inversion` expects `fun_blocktype (state.mk_state v_s v_f) bt (mkFunctype t_1_lst t_2_lst)`", and "`h3 : k = |val*|`, where `Instr_ok2.label` expects `v_n = |t_2*|`". Loop gets the same `h0` error. The cause is in Step_read/block and Step_read/loop (`-- if $blocktype(z, bt) = t_1^k -> t_2^n`). Each gained an explicit `var_0 : functype`, and the equation `fun_blocktype z bt = t_1* → t_2*` became two premises, `fun_blocktype z bt var_0` and `var_0 = t_1* → t_2*`. The old positional names now bind `var_0` and the shifted premises.

So the theorem breaks on its own, not only through `bt_inversion`. The other cases that the repair edited break for the same kind of reason. This is read off the rule changes, since only the first errors are recorded:
- call_indirect-call: `$type(z, y)` and `$table(z, x)` became variables `ft` and `ti`, with premises `fun_type z y ft`, `fun_table z x ti` and `ft = $funcinst(z)[a].TYPE`. The old `h3`/`h4` (the address bound a < |S.funcs| and the TYPES equation) now name other premises.
- call_addr: `($default_(t))*` became a list o\* of relation outputs. The rule now has the premises |o\*| = |t\*|, `Forall₂ (fun_default_ t o)` and (o ≠ none)\*, and the locals are `val^k (o!)*`. Before, they were `(default_ t ≠ none)*` and `val^k (default_(t)!)*`. Every premise index shifts.
- local.get / global.get: the reduct is now a variable `v` / `gi.VALUE`, constrained by `fun_local z x v` / `fun_global z x gi`. It is no longer the computed F.locals[x] / S.globals[F.module.globals[x]].value.
- table.get-val / table.init-succ: `$table(z, x)` / `$elem(z, y)` became `ti` / `ei`, with `fun_table` / `fun_elem` premises. The old terms `(fun_table (state.mk_state v_s v_f) x).REFS` and `(fun_elem (state.mk_state v_s v_f) y).REFS` no longer typecheck.
- load-num-val: the new leading premise `fun_mem z 0 mi` shifts `wf_num_ nt c` from `h3` to `h4`.

**Original proof sketch.** `Step_read_is_wf` (from wf_config and ⊢ S ok) gives the well-formedness of every reduct instruction (`hwf'`), and `ainstrs_ok_context_store_wf` gives wf C' and wf S. Then the proof does `cases` on the 47 rules:
- Traps (…-trap, …-oob, call_indirect-trap) use `construct_ais_trap`: Instr_ok2/trap types TRAP at any t1\* → t2\*. For the empty reducts (table/memory .fill/.copy/.init-zero), `ais_args3_typing` with the `pt_*` lemma gives ε → ε ≤ t1\* → t2\*. `instrtype_sub_empty` turns that into t1\* ≤ t2\*, and `ais_empty_typing` types ε.
- block/loop: the proof inverts S; C' ⊢ val^k (BLOCK bt instr\*) with `ais_composition_typing`, `ais_vals_typing_inversion` and `ais_single_typing_inversion`/`ai_principal_typing`. This gives C' ⊢ bt : bt1 → bt2 and {LABELS bt2} ++ C' ⊢ instr\* : bt1 → bt2 (for loop {LABELS bt1} ++ C', as in Instr_ok/loop). `bt_inversion` (from S ⊢ F.module : C, C' ⊢ bt : bt1 → bt2, `inst_match` and the rule's `$blocktype(z, bt) = t_1^k → t_2^n`) gives bt1 = t_1\* and bt2 = t_2\*, and `instrtype_sub_compose_eq` (with k = |val\*| = |t_1\*|) gives the subtyping. The proof then rebuilds LABEL_n{ε} val^k instr\* with Instr_ok2/label: the continuation ε : t_2\* → t_2\* comes from `ais_empty_typing`, and the body comes from `construct_ais_vals` and `construct_instrs_from_ais`. The arity n = |t_2\*| is h3. For loop, the continuation `LOOP bt instr*` is typed by `Instr_ok.loop` and the arity k = |t_1\*| is h2.
- call / ref.func: `pt_call`/`pt_ref_func` give C'.funcs[x], `minst_func_externaddr` gives S ⊢ FUNC F.module.funcs[x] : FUNC C'.funcs[x], then Instr_ok2/call_addr or Ref_ok/func finishes.
- call_indirect-call: `pt_call_indirect` gives C'.types[y] = u1\* → u2\*. With C'.types = F.module.types (`minst_invert_functypes`) and the rule's `$type(z, y) = $funcinst(z)[a].TYPE` (h4, definitionally F.module.types[y] = S.funcs[a].type), this is the type of S.funcs[a]. The proof finishes with `Externaddr_ok.func` (the rule's a < |S.funcs|, h3), Instr_ok2/call_addr and `instrtype_sub_compose_le`.
- call_addr: from the typing of val^k (CALL_ADDR a):
  - `pt_call_addr`, `Externaddr_invert_funcs` and `externtype_func_eq`, with the rule's S.funcs[a] = {TYPE t_1\* → t_2\*, MODULE mm, CODE func}, give the function's type.
  - `instrtype_sub_compose_eq` and `resulttype_sub_non_bot` show the arguments have types t_1\*.
  - `Store_ok_parts`, `funcinst_ok_parts` and `func_ok_body` give S ⊢ mm : C0 and {LOCALS t_1\* t\*, LABELS t_2\*, RETURN t_2\*} ++ C0 ⊢ instr\* : ε → t_2\*.
  - `Frame_ok.mk_Frame_ok` for f = {LOCALS val^k ($default_(t))\*, MODULE mm} uses `Forall2_app_intro` of the arguments' `Vals_ok` and `default_vals_ok`. The latter takes the rule's `(default_ t ≠ none)*` (h3). The wf_frame premise is the rule's h7.
  - Finally, Instr_ok2/frame around Instr_ok2/label, with n = |t_2\*| (h10).
- local.get: `pt_local_get` gives C'.locals[x] = t. `Forall2_nth_of_length` on `Vals_ok` (the length equation plus the zip-based pointwise `Val_ok`) gives S ⊢ F.locals[x] : t, which is the reduct `$local(z, x)` by unfolding. `ais_val1` finishes. global.get: `pt_global_get` (C'.globals[x] = mut t) and `lookup_global` give S ⊢ S.globals[F.module.globals[x]].value : t.
- table.get-val: `pt_table_get` gives C'.tables[x] = lim rt. `table_refs_ok` says every ref in S.tables[F.module.tables[x]].refs is valid at rt, and by unfolding these are `$table(z, x).refs`. The rule's bound i < |$table(z, x).refs| (h0, via `getElem!_pos` and `List.getElem_mem`) picks the element, and `ais_ref1` types it.
- Unrolled reducts (table/memory .fill-succ, .copy-le/gt, .init-succ) are built as `ais_cons_pre` chains:
  - The pieces are `ais_const1`/`ais_val1`/`ais_ref1` and the `Instr_ok` rules `table_set`/`table_get`/`table_fill`/`table_copy`/`table_init`/`store_pack`/`load_pack`/`memory_fill`/`memory_copy`/`memory_init`, from the context entries that the `pt_*` lemmas return.
  - table.init-succ types the pushed `$elem(z, y).refs[i]` with `elem_refs_ok` and the rule's bound h0.
- The value results (table.size, memory.size, load, vload) use `const_I32_result`, `ais_const1` (for load-num-val with the rule's `wf_num_ nt c`, h3), or `Step_read__vload_preserves`/`Step_read__vload_lane_preserves`.

**Current proof sketch.** The skeleton is the same, and 37 of the 47 cases are textually unchanged: they never used the premises that moved. Ten cases changed:
- block/loop: `subst` the new premise `ft = t_1* → t_2*` (h1), then pass `h0 : fun_blocktype (S;F) bt (t_1* → t_2*)` to the restated `bt_inversion`. That lemma now inverts the relation: for bt = _IDX x it reads ft = F.module.types[x] with `fun_type_inv` and compares it with C'.types[x] from Blocktype_ok/typeidx. The arity premises are now h4 (block, n = |t_2\*|) and h3 (loop, k = |t_1\*|).
- call_indirect-call: the TYPES equation is `(fun_type_inv h0).2.symm.trans h6`: `fun_type (S;F) y ft` gives ft = F.module.types[y], and the rule gives ft = S.funcs[a].type. The address bound is now h5. The table premises (`fun_table z x ti`, the bound, ti.refs[i] = REF.FUNC_ADDR a) are still unused.
- call_addr:
  - The proof first shows o\* = (default_ t)\*, i.e. `o_lst = Map default_ t_lst`. `to_mathlib_forall₂` turns the new length premise h0 and the zip-based h1 into Mathlib's `List.Forall₂`. Induction with `fun_default_eq` then gives the list equation, because `fun_default_` is functional and its output is the HelperLemmas function view `default_ t`.
  - From h5 ((o ≠ none)\*) it derives `(default_ t ≠ none)*` (`hd`).
  - It rewrites the frame equation h6 and the wf_frame premise h9 from val^k (o!)\* to val^k (default_(t)!)\* and `subst`s f.
  - Then it runs the old argument with `default_vals_ok … hd`, h9 and h12, with h3/h4 for the funcinst/func equations.
- local.get: `obtain ⟨_, rfl⟩ := fun_local_inv h0` replaces the reduct value v by F.locals[x] and drops the bound. The rest is the old proof, which still goes through `Vals_ok`'s length. global.get: `obtain ⟨_, _, rfl⟩ := fun_global_inv h0` replaces gi by S.globals[F.module.globals[x]], and `lookup_global` works as before.
- table.get-val: `rw [← (fun_table_inv h2).2.2] at hrefs` turns `table_refs_ok`'s S.tables[F.module.tables[x]].refs into ti.refs, and the element is picked with the rule's own bound h0 : i < |ti.refs|. table.init-succ does the same with `fun_elem_inv h4`, `elem_refs_ok` and h0 : i < |ei.refs|.
- load-num-val: `ais_const1` takes `wf_num_ nt c` from h4.
- call: this change is for default-independence, not because of the model. `hwf' _ (by simp)` became `hwf' _ (List.mem_singleton_self _)`.
  - The main session made this edit, not the repair agent: the first final build (b31/final1), made from the agent's returned file, still has `by simp` (b31/STATE.md, "Fixes after the first final build").
  - The first final build's default audit flagged this theorem. The audit is a kernel replay with every Inhabited instance opaque; its report is b31/final1/audit/report.txt.
  - In that build, `simp` proved CALL_ADDR (F.module.funcs[x]!) ∈ [CALL_ADDR (F.module.funcs[x]!)] through `List.getElem!_eq_getElem?_getD`. That unfolds `l[i]!` to `l[i]?.getD 0`, so the proof reads Nat's default.
  - The original proof has the same `by simp`.

The repair agent added no lemmas. The proof uses lemmas the main session added: `fun_type_inv`, `fun_local_inv`, `fun_global_inv`, `fun_table_inv`, `fun_elem_inv`, `default_`/`fun_default_eq`, and the restated `bt_inversion`. The audits of the final build b31/final4, whose sources are byte-identical to the installed files (no `sorryAx` dependence, no default reads across all 5517 theorems), include this theorem.

#### `default_val_ok` (TypePreservation; theorem) - re-proved

*Statement (Wasm 2.0 terms):* For a value type t that has a default (every t except the bottom type `BOT`), the default value `$default_(t)` is valid at t in a well-formed store: S ⊢ $default_(t) : t (`Val_ok`). The defaults are CONST i32/i64 0, CONST f32/f64 $fzero(N), VCONST v128 0, and REF.NULL funcref/externref. The statement is unchanged; `default_` now refers to the HelperLemmas function view of the relation `fun_default_`, which has the same definition as the old model's `def default_`.

**What broke and why.** In the new model, `$default_` is the relation `fun_default_ : valtype → Option val → Prop`, and its f32/f64 cases carry a `fun_fzero N z` premise. The generated `default__is_wf` now takes the output as an explicit argument, with the relation as its first premise: `default__is_wf t r o : fun_default_ t o → o ≠ none → r = o.get! → wf_val r`. The old version was `default_ t ≠ none → r = (default_ t).get! → wf_val r`.
- Without the function views, the statement does not elaborate: `default_` is unknown, autoImplicit turns it into a variable, and Lean reports "Function expected at default_". Status: deleted.
- With the function views, the statement elaborates. But `default__is_wf t _ hd rfl` passes `hd : default_ t ≠ none` where `o : Option val` is expected ("Application type mismatch"), which leaves `Val_ok s (default_ t).get! t` unsolved. Status: sorried.

The theorem broke on its own. It is used by `default_vals_ok`, and through that by `t_read_preservation`'s call_addr case.

**Original proof sketch.** `default__is_wf t _ hd rfl` gives wf_val of (default_ t).get!. The proof then splits on t:
- i32/i64/f32/f64: `Val_ok.numtype` (Val_ok/numtype: S ⊢ CONST nt c : nt), with that wf_val.
- v128: `Val_ok.vectype`.
- funcref/externref: `Val_ok.reftype` with `Ref_ok.null` (S ⊢ REF.NULL rt : rt).
- BOT: impossible, because default_ BOT = none contradicts `hd`.

**Current proof sketch.** Identical except for the wf fact, which is now `default__is_wf t _ _ (fun_default_default t) hd rfl`. `fun_default_default t : fun_default_ t (default_ t)` (HelperLemmas) sets the output to `default_ t`. For f32/f64 it supplies the `fun_fzero` premise as `fun_fzero_32`/`fun_fzero_64`, which are built from the well-formedness of +0 at widths 32/64 (`wf_fzero_32`/`wf_fzero_64`). After that, `hd` and `rfl` discharge the remaining premises. The case split on t and the `Val_ok` constructors are unchanged.

### 7.4 P23, `TypePreservation`: `Step` preservation, store extension, instance invariance (8 constructs)

#### `t_preservation_type_aux` (TypePreservation; private theorem) - re-proved

*Statement (Wasm 2.0 terms):* type preservation for one `Step`. This is the generalized form of `t_preservation_type`: the two configurations are variables `c1`, `c2` with equations, so that `induction` applies. Assume `(s; f); ais ↪ (s'; f'); ais'`, and assume:
- both configurations are well-formed (`wf_config`);
- `⊢ s : OK`, `⊢ s' : OK` and `s ⪯ s'` (`Extend_store`);
- `s ⊢ f.MODULE : C` and `s' ⊢ f.MODULE : C`;
- `f.LOCALS` has the types `C'.LOCALS` (`Vals_ok`);
- `C'` agrees with `C` on types/funcs/globals/tables/mems/elems/datas (`inst_match`);
- `s; C' ⊢ ais : t1* → t2*` (`Instrs_ok2`).

Then `s'; C' ⊢ ais' : t1* → t2*`. The statement is unchanged.

**What broke and why.** The recorded errors (the first three) are the same with and without the function views:
- In `case global_set z v x`, `v` has type `state` where `inv_val_arg` expects a `val`. Also, `x` is a proof of `fun_with_global (state.mk_state s f) z v_val✝ v` where `inv_global_set` expects a `globalidx`.
- In `case table_set_val`, `i : state` where `inv_const_arg _ _ numtype.I32` expects a `num_`.

Cause: Lean's `case tag x₁ … xₙ` names the *last* n inaccessible variables of the case, and the rules of seven of the cases that name variables gained arguments and premises (other rules changed too, see below):
- `$with_global`, `$with_table`, `$with_tableinst`, `$with_elem`, `$with_mem` and `$with_data` became relations `fun_with_*`. Each has a premise that carries the index bound, e.g. `x < |f.MODULE.GLOBALS|`. A rule's post-state is now a variable `var_0 : state` with a premise such as `fun_with_global z x val var_0`.
- `Step/table.set-val` also gained `var_1 : tableinst` with `fun_table z x var_1`, because `$table(z, x)` is a relation now. Its bound `i < |var_1.REFS|` is stated over `var_1`.
- `Step/table.grow-succeed` now has `var_2 : Option tableinst` (the old `var_0`, renamed) and the new `var_1 : tableinst` and `var_0 : state`, with `fun_growtable var_1 n ref var_2`, `fun_table z x var_1` and `fun_with_tableinst z x ti var_0`.
- `store-num-val` and `store-pack-val` gained `var_0` with `fun_with_mem z 0 (i + ao.OFFSET) (…/8) b* var_0`.
- `elem.drop` and `data.drop` gained `var_0` with `fun_with_elem z x ε var_0` and `fun_with_data z x ε var_0`.

Binder counts went from 3 to 5 (global.set), 6 to 10 (table.set-val), 9 to 13 (table.grow-succeed), 2 to 4 (elem.drop, data.drop), 9 to 11 (store-num-val) and 11 to 13 (store-pack-val). The old name lists therefore bound the wrong variables. For `global.set`, `z` now named the index, `v` named `var_0`, and `x` named the premise.

**Original proof sketch.** `induction hstep` over the 23 `Step` rules. Every case `injection`s and `subst`s the configuration equations. `ainstrs_ok_context_store_wf` gives `wf_context C'`, and `Extend_store_wf_store'` gives `wf_store s'`.
- `Step/pure`: the state is unchanged, so `t_pure_preservation` applies. `Step/read`: `t_read_preservation`, which takes `wf_config`, `Store_ok`, `Moduleinst_ok`, `Vals_ok` and `inst_match`.
- `Step/ctxt-label`: invert the typing of `label_n{instr0*} ais` (`ais_single_typing_inversion`, `ai_principal_typing`) to the body typing under `C'` with the label `t'*` prepended.
  - The IH gives the reduced body in `s'`.
  - `Extend_store_ais` moves the continuation `instr0*` to `s'`.
  - The typing is rebuilt with `Instr_ok2.label`, `construct_ais_typing_single` and `construct_ais_subtyping`. The new label's `wf_admininstr` comes from `wf_config c2`.
- `Step/ctxt-frame`: invert `frame_n{f0} ais` into `Frame_ok` (locals typed `tl`, module context `C0`) and the body's `Expr_ok2` under `{LOCALS tl} ++ C0` with `RETURN` set.
  - The IH gives the reduced body.
  - `reduce_inst_unchanged` (the inner frame keeps its module), `t_preservation_vs_type` (the inner frame's locals stay typed) and `Extend_store_moduleinst` rebuild `Frame_ok s0' fi'`.
  - `Instr_ok2_frame` closes the case.
- `Step/ctxt-instrs`: split `val* ais ais1` with `ais_composition_typing` and apply the IH on `ais`.
  - `val*` is re-typed in `s'` with `ais_vals_typing_inversion`, `Extend_store_vals` and `construct_ais_vals`.
  - `ais1` is moved to `s'` with `Extend_store_ais`.
  - `construct_ais_compose` recomposes the sequence.
- Rules that reduce to `ε`, apart from the vector stores below (`local.set`, `global.set`, `table.set-val`, `elem.drop`, `store-num-val`, `store-pack-val`, `data.drop`): the operator consumes exactly its operands.
  - `ais_args1_typing`/`ais_args2_typing` combine the operand inversions `inv_val_arg`/`inv_const_arg`/`inv_ref_arg` (type `[] → [t]`) with `inv_local_set`/`inv_global_set`/`inv_table_set`/`inv_store_none`/`inv_store_pack` (type `[t(, t')] → []`). For `elem.drop` and `data.drop`, `inv_elem_drop`/`inv_data_drop` are used directly.
  - Either way the result is `instrtype_sub ([] → []) (t1* → t2*)`. `instrtype_sub_empty` turns this into `t1* ≤ t2*`, and `ais_empty_typing` types `ε`.
  - These cases use the case-bound names `v`, `x`, `i`, `r`, `nt`, `c`, `ao` and `k`.
- Trap rules (`table.set-trap`, `store-num/pack-trap`, `vstore-oob`, `vstore_lane-oob`): `construct_ais_trap`.
- `table.grow-succeed/-fail` and `memory.grow-succeed/-fail`: the result `i32.const c` is typed with `const_I32_result`, which needs:
  - the constant's `wf_num_`, from `wf_config c2` via `wf_const_num`;
  - the subtyping, from `ais_args2_typing` (`inv_ref_arg`, `inv_const_arg`, `inv_table_grow`, giving `[t, t'] → [i32]`) or from `ais_args1_typing` (`inv_const_arg`, `inv_memory_grow`).
- `vstore-val`, `vstore_lane-val`: `Step__vstore_preserves`, `Step__vstore_lane_preserves`.

**Current proof sketch.** The proof is identical; only the `case` binder lists changed. The lists of the seven rules are padded with `_` for the new arguments and premises:
- `case global_set z v x _ _`
- `case table_set_val z i r x _ _ _ _ _ _`
- `case table_grow_succeed z r k x _ _ _ _ _ _ _ _ _`
- `case elem_drop z x _ _`
- `case store_num_val z i nt c ao _ _ _ _ _ _`
- `case store_pack_val z i v_Inn c k ao _ _ _ _ _ _ _`
- `case data_drop z x _ _`

The names again denote the rule's state, operands and index. No new premise (`fun_with_*`, `fun_table`, bounds) is used: typing the reduct needs only the operands' typing, `s ⪯ s'` and (for the grows' result constant) `wf_config`, never the shape of the new store. Cases that name nothing (vstore, memory.grow, traps) were unaffected even though most of their rules also gained arguments and premises. In the final build the theorem depends on no `sorry`. At repair time its only `sorryAx` came from cluster P1's then-unrepaired `t_read_preservation`.

#### `t_preservation_vs_type'_aux` (TypePreservation; private theorem) - re-proved

*Statement (Wasm 2.0 terms):* the locals stay well-typed under one step. This is the generalized form of `t_preservation_vs_type'`. Assume `(s; f); ais ↪ (s'; f'); ais'`, `⊢ s : OK`, `s ⊢ f.MODULE : C`, `f.LOCALS : C'.LOCALS` in `s` (`Vals_ok`), `inst_match C C'` and `s; C' ⊢ ais : t1* → t2*`. Then `f'.LOCALS : C'.LOCALS` in the same store `s`. The statement is unchanged.

**What broke and why.** The errors are the same with and without the function views. `injection hz2` fails ("equality of constructor applications expected") in the `all_goals` block for `global_set`, `table_set_val` and `table_grow_succeed`, which are the three recorded (first) errors; the other store-writing rules, whose post-state is also `var_0`, fail the same way.
- The old block unfolded the post-state with `try simp only [with_global, with_table, with_tableinst, with_elem, with_mem, with_meminst, with_data] at hz2`.
- Those functions no longer exist (they are the relations `fun_with_*`), so the `try` silently does nothing.
- The rules' post-state is now the rule variable `var_0`, constrained by the premise `fun_with_* z … var_0`. As a result, `hz2 : var_0 = state.mk_state s' f'` has a variable on the left, and `injection` fails.

**Original proof sketch.** `induction h`:
- `ctxt-label`: invert the label typing to the body typing under `prepend_label C' t'*`, which keeps `LOCALS`. Then apply the IH.
- `ctxt-instrs`: two `ais_composition_typing` steps isolate `ais` in `val* ais ais1`. Then apply the IH.
- `ctxt-frame`: the outer frame is unchanged (`f' = f`), so the hypothesis `hvals` closes the case.
- `local.set x` with value `v`:
  - Unfolding `with_local` and `injection` give `f'.LOCALS = f.LOCALS[x = v]`.
  - Invert the typing of `v (local.set x)`. `ais_seq_typing_inversion` and `ais_single_val_typing_inversion` give `Val_ok s v tv`. `ais_single_typing_inversion` and `ai_principal_typing` give `local.set x : [t] → []` with `C'.LOCALS[x] = t`.
  - `instrtype_sub_compose_eq`, `Val_ok_non_bot` and `resulttype_sub_non_bot` give `tv = t`.
  - Finally, for the zip of `C'.LOCALS` with the updated locals: the length is the same (`List.length_modify`), and each pair is either an old pair or `(t, v)` (`mem_zip_modify_right`).
- Every other rule (`all_goals`): the post-state's frame is `f`.
  - Either the state is unchanged (pure, read, traps, failed grows),
  - or the post-state was `$with_*((s; f), …)`, which `simp only [with_*] at hz2` unfolded to `(s with …; f)`.
  - `injection` then gives `f' = f`, and `hvals` closes the goal.

**Current proof sketch.** Same, except in the `all_goals` block. The `try simp only [with_*]` became `try casesm fun_with_global _ _ _ _, fun_with_table _ _ _ _ _, fun_with_tableinst _ _ _ _, fun_with_elem _ _ _ _, fun_with_mem _ _ _ _ _ _, fun_with_meminst _ _ _ _, fun_with_data _ _ _ _` (Mathlib `casesm`), which runs after `subst hz1`. It inverts the rule's `fun_with_*` premise:
- Each such relation has one constructor, so the inversion sets `var_0 := state.mk_state {s with …} f`.
- The index-bound premise it introduces is left unused.

Then `injection hz2` gives `f' = f` as before. The doc comment gained one sentence saying this. Per the repair note, the theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

#### `store_extension_reduce_aux` (TypePreservation; private theorem) - re-proved

*Statement (Wasm 2.0 terms):* one step extends the store and keeps it valid. This is the generalized form of `store_extension_reduce`. Assume `(s; f); ais ↪ (s'; f'); ais'`, the initial configuration is well-formed (`wf_config`), `s ⊢ f.MODULE : C`, `s; C' ⊢ ais : t1* → t2*`, `inst_match C C'` and `⊢ s : OK`. Then `s ⪯ s'` and `⊢ s' : OK`. The statement is unchanged.

**What broke and why.** The errors are the same with and without the function views:
- `Unknown identifier with_global` and "`simp` made no progress" in the `global_set` case;
- `Unknown identifier with_table` in `table_set_val`.

The `global.set`, `table.set-val`, `table.grow-succeed`, `elem.drop`, `memory.grow-succeed` and `data.drop` cases unfolded their post-state function, for example with `simp only [with_global] at hz2`; the four memory-store cases passed the equation `with_mem … = (s'; f')` to `with_mem_store_ok`. But `$with_global`, `$with_table`, `$with_tableinst`, `$with_elem`, `$with_mem`, `$with_meminst` and `$with_data` are now the relations `fun_with_*`. Their premise is the index bound, and their result is the rule's new variable `var_0`. In addition:
- The `case` binder lists of these rules no longer lined up with the new rule arguments.
- Three of the per-rule lemmas it dispatches to no longer elaborated (`table_grow_store_ok`, `with_mem_store_ok`, `memory_grow_store_ok`; see below).

**Original proof sketch.** `induction hstep`, with the configurations generalized:
- `pure`, `read`, `local.set` (only the frame changes; `with_local` is unfolded) and every trap or failed-grow rule (`all_goals`): the store is unchanged, so `Extend_store_refl` and `⊢ s : OK` close the case.
- `ctxt-label` and `ctxt-instrs`: invert the typing, then apply the IH. For a label, the body is typed under `C'` with the label prepended (`construct_inst_prepend_label`); for an instruction sequence, `ais_composition_typing` splits it.
- `ctxt-frame`: invert `frame_n{f0} ais` into `Frame_ok`, which gives `s ⊢ f0.MODULE : C0`, and the body typing. Then apply the IH with `C0` and `inst_match_locals_append`.
- `global.set`, `table.set-val`, `elem.drop`, `data.drop`: `simp only [with_X]` and `injection` give `s' = s[.GLOBALS[f.MODULE.GLOBALS[x]].VALUE = v]` (or the analogous update). Then `global_set_store_ok`, `table_set_store_ok`, `elem_drop_store_ok` or `data_drop_store_ok` applies. These lemmas are stated over the explicit store update and take `Store_ok`, `Moduleinst_ok`, `inst_match` and the instruction typing.
- `table.grow-succeed` and `memory.grow-succeed`: the same unfolding for `with_tableinst`/`with_meminst`. Then `table_grow_store_ok`/`memory_grow_store_ok` takes the rule premises encoding `$growtable($table(z, x), n, ref) = ti`: `fun_growtable (fun_table z x) n ref var_0`, `var_0 ≠ none` and `var_0.get! = ti` (for memory: `fun_growmemory (fun_mem z 0) n var_0`, `var_0 ≠ none` and `var_0.get! = mi`).
- `store-num-val`, `store-pack-val`, `vstore-val`, `vstore_lane-val`: the equation `with_mem((s; f), 0, i + ao.OFFSET, len, b*) = (s'; f')` goes to `with_mem_store_ok`, together with two facts:
  - `0 < |C'.MEMS|`, from the instruction typing: `ais_store_mems_inv`, or `ais_vstore_mems_inversion`/`ais_vstore_lane_mems_inversion` after `ais_seq3_last_typing`.
  - The written bytes are well-formed. For `store-num-val`, `nbytes__is_wf` from `wf_num_ nt c`, which comes from `wf_config` via `wf_const_num`. For `store-pack-val`, `ibytes__is_wf ∘ wrap___is_wf ∘ wf_num_Inn_proj`. For `vstore-val`, `vbytes__is_wf` with `wf_vconst_parts`. For the lane store, `ibytes__is_wf` from the rule's own `wf_uN N (lane)` premise.

**Current proof sketch.** The case structure is the same. Each store-writing case now also names the rule's new post-state `var_0` (plus `var_1` in table.set-val, vstore_lane-val and the grows, and `var_2` in the grows) and its `fun_with_*` premise `hw`. `subst hz2` replaces `var_0` by `(s'; f')`. Then:
- `global.set`, `table.set-val`, `elem.drop`, `data.drop`: `cases hw` inverts `fun_with_global`/`fun_with_table`/`fun_with_elem`/`fun_with_data`; the index bound it introduces is not used. This fixes `s'` to the updated store and `f' = f`. The same, unchanged per-rule lemma follows.
- `table.grow-succeed`: `cases hw` on `fun_with_tableinst`. The restated `table_grow_store_ok` then receives the rule's premises `hgrow : fun_growtable var_1 n ref var_2`, `htab : fun_table (s; f) x var_1`, `hne` and `hget`.
- `memory.grow-succeed`: `cases hw` on `fun_with_meminst`. The restated `memory_grow_store_ok` receives `hgrow : fun_growmemory var_1 n var_2`, `hmem : fun_mem (s; f) 0 var_1`, `hne` and `hget`.
- The four stores: `hw : fun_with_mem (s; f) 0 (i + ao.OFFSET) len b* (s'; f')` is passed, without inversion, to the restated `with_mem_store_ok`, which inverts it. The memory and byte facts are as before. The lane store's binder list skips its new `fun_jsize Jnn var_1` and `N = var_1` premises.
- The pure, read, `local.set` and congruence cases are unchanged, and so is the `all_goals` block: the trap rules' new `fun_table`/`fun_mem` premises are never named.

The doc comment was updated: the store-writing rules invert their `fun_with_*` premise, and the four memory stores hand `fun_with_mem` to `with_mem_store_ok`, which inverts it. Per the repair note, the axioms are the model's `nbytes_`/`ibytes_`/`vbytes_`/`wrap__` `*_is_wf` axioms plus the standard three.

#### `table_grow_store_ok` (TypePreservation; theorem) - restated and re-proved

*Statement (Wasm 2.0 terms):* the `table.grow-succeed` case of store extension (Rocq `store_extension_reduce`, "Table Grow"). Assume:
- `⊢ s : OK`, `s ⊢ f.MODULE : C` and `inst_match C C'`;
- `s; C' ⊢ ref (i32.const k) (table.grow x) : t1* → t2*`;
- growing the current table `$table((s; f), x)` by `n` copies of `ref` gives `ti` (`$growtable(…) = ti`).

Then `s ⪯ s[.TABLES[f.MODULE.TABLES[x]] = ti]`, and that store is valid. Only the growth premises of the statement changed. The new premises are those of `Step.table_grow_succeed`, with the same names and order, minus its `fun_with_tableinst` premise (which the caller inverts):
- old: `(var_0 : Option tableinst) … → fun_growtable (fun_table (state.mk_state s f) x) v_n r var_0 → var_0 ≠ none → Option.get! var_0 = ti → …`
- new: `(var_2 : Option tableinst) (var_1 : tableinst) … → fun_growtable var_1 v_n r var_2 → fun_table (state.mk_state s f) x var_1 → var_2 ≠ none → Option.get! var_2 = ti → …`

**What broke and why.** The statement no longer elaborated, so the cascade deleted it, with and without the function views. `fun_table (state.mk_state s f) x` has type `tableinst → Prop`, but `fun_growtable` expects a `tableinst`.
- `$table(z, x)`, i.e. `s.TABLES[f.MODULE.TABLES[x]]`, became the relation `fun_table z x ti`. Its premises are `f.MODULE.TABLES[x] < |s.TABLES|` and `x < |f.MODULE.TABLES|`.
- `Step/table.grow-succeed` now takes the looked-up table as `var_1`, with `fun_table z x var_1` and `fun_growtable var_1 n ref var_2`.

**Original proof sketch.**
- Case-split `$growtable`. The failure constructor contradicts `var_0 ≠ none`. The success constructor gives:
  - the old table `{TYPE [i .. j?] rt, REFS r'*} = $table((s; f), x)` (`hold`);
  - `i' = |r'*| + n` and `i' ≤ j`;
  - `ti = {TYPE [i' .. j?] rt, REFS r'* ref^n}` and its well-formedness.
- From the typing, `ais_table_grow_inv` gives `C'.TABLES[x] = lim rt0` and `s ⊢ ref : rt0`. `getElem?_eq_some_bang` gives `x < |C'.TABLES|`.
- `Moduleinst_ok_lengths` and `inst_match` give `|f.MODULE.TABLES| = |C'.TABLES|`. `minst_invert_tables` with `Forall2_nth_of_length` at `x` then gives two facts about the address `a = f.MODULE.TABLES[x]`:
  - `a < |s.TABLES|`;
  - `s.TABLES[a]` has some type `tbt'` with `TABLE tbt' ≤ TABLE (lim rt0)`. By `externtype_table_sub_inv`, the stored table's reftype is `rt0`.
- `hold.trans hlk` identifies `$growtable`'s input with `s.TABLES[a]`, so `i`, `j?`, `rt` and `r'*` are those of the stored table.
- `Store_ok_parts` and `wf_store_parts` decompose the store. The stored table's `Tableinst_ok` (`tableinst_ok_invert`) pins the old minimum: `i = |r'*|`.
- Build the new table list `ts'`:
  - well-formedness via `Forall_list_update_func` and `wf_store_with_tables`;
  - `s ⪯ s'` via `Extend_store_of_parts`, using `table_grow_table_extension` for the tables and reflexivity for the other components;
  - `⊢ s' : OK` via `Store_ok_of_parts`, with the table types updated at `a`. For the tables it uses `construct_tableinsts_grow`, which needs `s ⊢ ref : rt` and `|r'*| + n ≤ j`; the other components use `Extend_store_*insts`.

**Current proof sketch.** The proof takes the extra premise `htab : fun_table (s; f) x var_1`. `fun_table_inv htab` gives `var_1 = s.TABLES[f.MODULE.TABLES[x]!]!`. Its two index bounds are discarded with `_`, because the proof still gets them from validation as above. `subst` then turns `fun_growtable var_1 …` into `fun_growtable s.TABLES[f.MODULE.TABLES[x]!]! …`, which is what the old `fun_growtable (fun_table (s; f) x) …` unfolds to. The rest is the old proof, unchanged.

#### `with_mem_store_ok` (TypePreservation; theorem) - restated and re-proved

*Statement (Wasm 2.0 terms):* the four memory-store cases of store extension (`store-num-val`, `store-pack-val`, `vstore-val`, `vstore_lane-val`). Assume:
- `$with_mem((s; f), 0, off, len, b*) = (s'; f')`;
- `⊢ s : OK`, `s ⊢ f.MODULE : C` and `inst_match C C'`;
- `C'` has a memory (`0 < |C'.MEMS|`);
- `b*` are well-formed bytes.

Then `s ⪯ s'` and `⊢ s' : OK`. Only the first premise of the statement changed:
- old: `with_mem (state.mk_state s f) (uN.mk_uN 0) off len b_lst = state.mk_state s' f' → …`
- new: `fun_with_mem (state.mk_state s f) (uN.mk_uN 0) off len b_lst (state.mk_state s' f') → …`

**What broke and why.** The statement no longer elaborated, so the cascade deleted it, in both settings. `with_mem` is unknown: auto-bound implicits turn it into a variable, hence "Function expected". The proof's `simp only [with_mem, …]` failed too.
- The spec function `$with_mem((s; f), x, i, j, b*) = s[.MEMS[f.MODULE.MEMS[x]].BYTES[i : j] = b*]; f` became the relation `fun_with_mem`, with premise `x < |f.MODULE.MEMS|`.
- The four store rules carry this relation as a premise.

**Original proof sketch.**
1. Unfold `with_mem` in the equation.
2. Rewrite `splice`, the Lean rendering of `BYTES[i : j] = b*`, to `list_slice_update … |b*| b*` (`splice_eq_list_slice_update`).
3. `injection` gives `s' = s` with `MEMS` updated at `f.MODULE.MEMS[0]`.
4. Apply `mem_store_extension` with `len := |b*|`: storing well-formed bytes into memory 0 extends the store and keeps it OK.

**Current proof sketch.** `cases` on the `fun_with_mem` premise. The relation has one constructor, and its bound `0 < |f.MODULE.MEMS|` is not used. The inversion instantiates `s'` with the updated store and `f'` with `f`. Then `simp only [splice_eq_list_slice_update]` rewrites the goal, and `mem_store_extension` applies exactly as before.

#### `memory_grow_store_ok` (TypePreservation; theorem) - restated and re-proved

*Statement (Wasm 2.0 terms):* the `memory.grow-succeed` case of store extension. Assume:
- `⊢ s : OK`, `s ⊢ f.MODULE : C` and `inst_match C C'`;
- `s; C' ⊢ a memory.grow : t1* → t2*`;
- growing memory 0, i.e. `$mem((s; f), 0)`, by `n` pages gives `mi` (`$growmemory(…) = mi`).

Then `s ⪯ s[.MEMS[f.MODULE.MEMS[0]] = mi]`, and that store is valid. The statement changed:
- old: `(var_0 : Option meminst) … → fun_growmemory (fun_mem (state.mk_state s f) (uN.mk_uN 0)) v_n var_0 → var_0 ≠ none → Option.get! var_0 = mi → …`
- new: `(var_2 : Option meminst) (var_1 : meminst) … → fun_growmemory var_1 v_n var_2 → fun_mem (state.mk_state s f) (uN.mk_uN 0) var_1 → var_2 ≠ none → Option.get! var_2 = mi → …`

**What broke and why.** The statement no longer elaborated, so the cascade deleted it, in both settings. `fun_mem (state.mk_state s f) (uN.mk_uN 0)` has type `meminst → Prop`, but `fun_growmemory` expects a `meminst`.
- `$mem(z, 0)` became the relation `fun_mem z 0 mi`, with premises `f.MODULE.MEMS[0] < |s.MEMS|` and `0 < |f.MODULE.MEMS|`.
- `Step/memory.grow-succeed` now takes `var_1` with `fun_mem z 0 var_1` and `fun_growmemory var_1 n var_2`.

**Original proof sketch.**
- Case-split `$growmemory`. Failure contradicts `var_0 ≠ none`. Success gives:
  - the old memory `{TYPE [i .. j?] PAGE, BYTES b*} = $mem((s; f), 0)` (`hold`);
  - `i' = |b*|/(64 Ki) + n` as a rational, with `i' ≤ j` and `i' ≤ 2^16`;
  - `mi = {TYPE [i' .. j?] PAGE, BYTES b* 0^(n·64Ki)}` and its well-formedness.
- `ais_memory_grow_inv` gives `0 < |C'.MEMS|`. With `Moduleinst_ok_lengths`, `inst_match`, `minst_invert_mems` and `Forall2_nth_of_length` at 0, the address `f.MODULE.MEMS[0]` is `< |s.MEMS|`.
- `Store_ok_parts` decomposes the store. The stored memory's `Meminst_ok` (`meminst_ok_raw`) shows it is `{TYPE [vn0 .. m?] PAGE, BYTES bs0}` with `|bs0| = vn0·64Ki`. `hold.trans` identifies it with `$growmemory`'s input.
- From this:
  - `i' = vn0 + n` (`push_cast; ring`);
  - `rat_to_nat i' = vn0 + n` (`rat_to_nat_natCast`);
  - the bounds `vn0 + n ≤ 2^16` and `vn0 + n ≤ m`;
  - `vn0 = |b*|/(64Ki)`.
- Build the new memory list `ms'`:
  - well-formedness via `wf_store_with_mems`;
  - `s ⪯ s'` via `Extend_store_of_parts` and `memory_grow_mem_extension`;
  - `⊢ s' : OK` via `Store_ok_of_parts`, with the memory types updated at the address. The memories use `construct_meminsts_grow`; the other components use `Extend_store_*insts`.

**Current proof sketch.** The proof takes the extra premise `hmem : fun_mem (s; f) 0 var_1`. `fun_mem_inv hmem` gives `var_1 = s.MEMS[f.MODULE.MEMS[0]!]!` and its bounds are discarded. `subst` follows, and the rest is the old proof, unchanged.

#### `reduce_inst_unchanged_aux` (TypePreservation; private theorem) - re-proved

*Statement (Wasm 2.0 terms):* a step never changes the frame's module instance. This is the generalized form of `reduce_inst_unchanged`: if `(s; f); ais ↪ (s'; f'); ais'`, then `f.MODULE = f'.MODULE`. The statement is unchanged.

**What broke and why.** In both settings, the identifiers `with_global`, `with_table` and `with_tableinst` are unknown in the `simp_all [with_global, with_table, with_tableinst, with_elem, with_mem, with_meminst, with_data]` of the final `all_goals` block (these are the three recorded errors; the other four names are gone too). These functions are now the relations `fun_with_*`, and the store-writing rules' post-state is the variable `var_0` constrained by such a premise.

**Original proof sketch.** `induction h`:
- `ctxt-label` and `ctxt-instrs`: the inner step goes between the same states `z` and `z'` as the outer one, so the IH applies.
- `local.set`: unfold `with_local` (`f' = f[.LOCALS[x] = v]`), `injection`, then `rfl`.
- All other rules: `simp_all` with the `with_*` definitions closes the goal from the configuration equations. In each case `f' = f`, for one of three reasons:
  - the state is unchanged;
  - the post-state is `(s with …; f)`, a store-only update;
  - the rule is `ctxt-frame`, which keeps the outer frame.

**Current proof sketch.** Same, with one addition in the `all_goals` block. Before `simp_all`, `try casesm fun_with_global _ _ _ _, fun_with_table _ _ _ _ _, fun_with_tableinst _ _ _ _, fun_with_elem _ _ _ _, fun_with_mem _ _ _ _ _ _, fun_with_meminst _ _ _ _, fun_with_data _ _ _ _` inverts the rule's `fun_with_*` premise. This sets the rule's `z := (s0; f0)` and `var_0 := (s0 with …; f0)`. Plain `simp_all` then closes the goal from the configuration equations as before. The doc comment was updated: `with_local` is still a function, and the `fun_with_*` updates are relations that get inverted. It also says that `ctxt_frame` needs no induction hypothesis either, since it changes only the store and the inner frame. The proof is sorry-free.

#### `num_default_is_well_formed` (TypePreservation; theorem) - re-proved

*Statement (Wasm 2.0 terms):* for every number type `nt`, the default number `num_default nt` is well-formed at type `nt` (`wf_num_`). The default is `0` for `i32`/`i64` and `+0 = $fzero(N)` for `f32`/`f64`, as in `$default_`. The statement is unchanged.

**What broke and why.**
- *Without the function views:* `Unknown identifier fzero` in the F32 and F64 cases. `$fzero(N)` became the relation `fun_fzero N z`, with premise `wf_fN N (POS (SUBNORM 0))`. In that setting `num_default` itself also failed, for the same reason.
- *With the function views,* where HelperLemmas makes `fzero` a function again, the error is an application type mismatch: `rfl` is given where `fun_sizenn (numtype_Fnn Fnn.F32) ?m` is expected. The constructor `wf_num_.num__case_1` changed shape because `$sizenn` became a relation:
  - old premise: `wf_fN (sizenn (numtype_Fnn Fnn)) x`;
  - new: an explicit width `var_0 : N` with `fun_sizenn (numtype_Fnn Fnn) var_0` and `wf_fN var_0 x`.
  
  So the old `refine … (fzero 32) ?_ rfl` filled the width with `?_` and the `fun_sizenn` slot with `rfl`.

The old inner proof would have failed as well. It used the removed function `E` and the old `wf_fNmag.fNmag_case_1`, which now takes `fun_E`/`fun_M` witnesses because `$E` and `$M` are relations now.

**Original proof sketch.** `cases nt`.
- `I32`: `wf_num_.num__case_0` with `$size(I32) ≠ none` (`simp [size, valtype_Inn]`) and, after unfolding `size`, `wf_uN 32 0` (`by decide`). `I64` is the same with 64.
- `F32`: `wf_num_.num__case_1 … (fzero 32)`. Unfold `fzero`, `sizenn` and `sizenn1`, then prove `wf_fN 32 (POS (SUBNORM 0))` by `wf_fN.fN_case_0` and `wf_fNmag.fNmag_case_1`: `0 < 2^M(32)` holds `by decide`, and the exponent is given explicitly as `2 - 2^(E(32)-1)`, so its equation is `rfl`. `F64` is the same with 64.

**Current proof sketch.** `I32` and `I64` are unchanged. `F32` is a single term, `wf_num_.num__case_1 numtype.F32 Fnn.F32 (fzero 32) 32 (fun_sizenn_sizenn _) wf_fzero_32 rfl`:
- the width is 32;
- the `fun_sizenn` witness comes from the function-view lemma `fun_sizenn_sizenn` (`sizenn F32` reduces to 32);
- `wf_fN 32 (fzero 32)` comes from the HelperLemmas lemma `wf_fzero_32`, which builds the subnormal-zero magnitude with the witnesses `fun_E.fun_E_case_0 32` (E = 8) and `fun_M.fun_M_case_0 32` (M = 23).

`F64` is the same with 64 and `wf_fzero_64`. Per the repair note, the only axiom used is `propext`.

### 7.5 Q1, `TypeProgress`: numeric operators and canonical forms (14 constructs)

#### `invert_typeof_I32` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* canonical form for `i32`: a well-formed value `v` (`wf_val v`) with `typeof v = i32` is `i32.const i` for some `i : Nat` (`admininstr_val v = CONST I32 (mk_num__0 I32 (mk_uN i))`). The progress cases with an `i32` operand use it: the condition or index of `select`, `if`, `br_if`, `br_table` and `call_indirect`; the index, size or address operands of the `table.*` and `memory.*` instructions and of loads and stores (vector loads and stores included); and the `i32` value of `i32.store8/16`.

**What broke and why.** The error: unsolved goals `CONST.I32.val_case_0.num__case_1.F32.fun_sizenn_case_0` (and `…F64…`), where the hypothesis `numtype.I32 = numtype_Fnn Fnn.F32` is left unused. The cause: `$sizenn(nt) = $size(nt)` is built on the partial `$size` (Lean: `Option.get! (size …)`), and it became the relation `fun_sizenn nt n`. So `wf_num_.num__case_1`, the well-formedness clause for float payloads (`num_(Fnn) = fN($sizenn(Fnn))`), gained a field `var_0 : N` and a premise `fun_sizenn (numtype_Fnn F) var_0`. Its payload premise changed from `wf_fN (sizenn (numtype_Fnn F)) x` to `wf_fN var_0 x`. The positional pattern `num__case_1 vFnn x _ hnt` therefore names the `fun_sizenn` premise `hnt`. `cases hnt` then only unfolds `fun_sizenn_case_0` and no longer refutes the numtype equation. The error is the same with and without the function views.

**Original proof sketch.**
- Case on the shape of `v`: `t.const`, `v128.const`, `ref.null`, `ref.func_addr a`, `ref.host_addr a`. Every shape except `CONST I32 n` is refuted by computing `typeof` (`cases Ht`).
- For `CONST I32 n`: invert `wf_val` (`val_case_0`) to get `wf_num_ I32 n`, then invert `wf_num_`:
  - integer payload `mk_num__0 Inn x` (`num__case_0`): if `Inn = I32`, destructure `x = mk_uN i` and return `i` by `rfl`. If `Inn = I64`, the premise `I32 = numtype_Inn I64` is refuted by `cases hnt`.
  - float payload `mk_num__1 Fnn x` (`num__case_1`): `cases vFnn <;> cases hnt` refutes `I32 = numtype_Fnn F32/F64`.

**Current proof sketch.** The proof is unchanged except for the float-payload pattern, which is now `num__case_1 vFnn x _ _ _ hnt`. It skips `var_0`, the `fun_sizenn` premise and `wf_fN var_0 x`, so `hnt` is again the equation `I32 = numtype_Fnn F` and `cases vFnn <;> cases hnt` refutes it. No size relation is built or inverted: an `i32` value never carries a float payload.

#### `invert_typeof_I64` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* canonical form for `i64`: a well-formed value with `typeof v = i64` is `i64.const i` for some `i : Nat`. It is used for the `i64` operand of `i64.store8/16/32` (`t_progress_be_store_pack`).

**What broke and why.** The cause is the same as for `invert_typeof_I32`. There are unsolved goals `CONST.I64.val_case_0.num__case_1.F32.fun_sizenn_case_0`/`…F64…`, because `num__case_1 vFnn x _ hnt` binds `hnt` to the new premise `fun_sizenn (numtype_Fnn F) var_0` instead of `I64 = numtype_Fnn F`. The error is the same in both settings.

**Original proof sketch.** As for `invert_typeof_I32`, with I32 and I64 swapped:
- refute the non-`CONST I64` shapes via `typeof`;
- invert `wf_val`, then `wf_num_`;
- an integer payload with `Inn = I64` gives `mk_uN i`, and `Inn = I32` is refuted by `cases hnt`;
- a float payload is refuted by `cases vFnn <;> cases hnt`.

**Current proof sketch.** The same proof; only the pattern changed, to `num__case_1 vFnn x _ _ _ hnt`.

#### `invert_typeof_I32_wf` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* a well-formed `v` with `typeof v = i32` is `i32.const k` with `k` in range: `admininstr_val v = CONST I32 (mk_num__0 I32 (mk_uN k)) ∧ wf_uN 32 (mk_uN k)`, that is, k < 2^32. `t_progress_be_vshiftop` uses it for the `i32` shift count.

**What broke and why.** The cause is the same as for `invert_typeof_I32`. In `cases Hwfn with … | num__case_1 F x Hx Hnt`, `Hx` now binds `var_0 : N` and `Hnt` binds the `fun_sizenn` premise. So `cases F <;> cases Hnt` leaves the goals `num__case_1.F32.fun_sizenn_case_0`/`…F64…` unsolved. The error is the same in both settings.

**Original proof sketch.**
- `invert_typeof_numtype_wf v I32` gives `n` with `admininstr_val v = CONST I32 n` and `wf_num_ I32 n`.
- Invert `wf_num_`:
  - integer payload `mk_num__0 I x` with `Hx : wf_uN |I| x`: for `I = I32`, destructure `x = mk_uN k` and return `⟨k, Heqv, Hx⟩` (`wf_uN (get! (size (valtype_Inn I32)))` computes to `wf_uN 32`). `I = I64` is refuted by `cases Hnt`.
  - float payload: refuted by `cases F <;> cases Hnt`.

**Current proof sketch.** The same; the float pattern is now `num__case_1 F x _ _ _ Hnt`.

#### `wf_fN_num_` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* suppose every float `x` in a list `l` is a well-formed `fN(|F|)` (`wf_fN (sizenn (numtype_Fnn F)) x`, with |F| = 32 or 64). Then every number `mk_num__1 F x` (the payload of `F.const x`) is a well-formed `num_(F)`. This is the step from the `fN*` results of `$fadd_` … `$fcopysign_` to the `wf_num_` premises of `fun_binop_`. The statement text is unchanged. Its `sizenn` is now the HelperLemmas function view of `fun_sizenn`, which has the old model's body `Option.get! (size (valtype_numtype nt))`.

**What broke and why.**
- Without the function views, the statement no longer elaborates: `sizenn` is unknown, because the old model's `def sizenn` became the relation `fun_sizenn`. The declaration is dropped.
- With the views, the statement elaborates but the proof term `wf_num_.num__case_1 _ _ _ (Hl x hx) rfl` is ill-typed. `num__case_1` now has an extra explicit field `var_0 : N` before its premises (`fun_sizenn (numtype_Fnn F) var_0`, `wf_fN var_0 x`, the numtype equation). `Hl x hx` lands in the `var_0 : N` slot ("is expected to have type N").

**Original proof sketch.** Pointwise: for `x ∈ l`, apply `wf_num_.num__case_1` to the payload premise `Hl x hx` and the numtype equation `rfl`.

**Current proof sketch.** Pointwise, `wf_num_.num__case_1 _ _ _ _ (fun_sizenn_sizenn _) (Hl x hx) rfl`. The HelperLemmas witness `fun_sizenn_sizenn (numtype_Fnn F) : fun_sizenn (numtype_Fnn F) (sizenn (numtype_Fnn F))` sets the size field to `sizenn (numtype_Fnn F)`. Then `Hl x hx : wf_fN (sizenn (numtype_Fnn F)) x` fits the `wf_fN var_0 x` premise.

#### `binop_total` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* for well-formed operands `c_1, c_2 : num_(t)` and a well-formed `binop` of type `t`, the relation for `$binop_(t, binop, c_1, c_2)` has an output: `∃ lst, fun_binop_ t binop c_1 c_2 lst`, with `lst : Option (List num_)`. The statement alone allows `lst = none` (the catch-all case 38, "`$binop_` undefined"); `binop_not_none` rules that out. `t_progress_be_binop` uses the two lemmas to step `(t.const c_1) (t.const c_2) (t.binop)` by Step_pure/binop-val or Step_pure/binop-trap.

**What broke and why.** The reported errors (items 1 and 2) are the same with and without the function views:
1. `numIF _ _ h1` (and `h2`) is ill-typed: `h1 : fun_sizenn (numtype_Fnn F1) var_0`. The pattern `⟨F1, x1, _, h1⟩` for the impossible float payload of an integer operand meets the new shape of `wf_num_.num__case_1` (see `invert_typeof_I32`). It now names the `fun_sizenn` premise instead of the numtype equation.
2. `fun_binop__case_6 sx x1 x2 r …` puts `r : Option iN` where `N` is expected. `fun_binop_` was already a relation in the old model, but now every clause except the catch-all case 38 has an explicit size argument (`var_0 : N`, or `var_1 : N` in the DIV/REM clauses 6-9) with a premise `fun_sizenn (numtype t) var_0`. Each clause computes at that size (`iadd_ var_0 iN_1 iN_2`, `fun_idiv_ var_1 …`, `fadd_ var_0 …`) instead of at `sizenn (numtype t)`.
3. Further consequences, not among the first reported errors: the float branch's pattern `⟨F1, x1, hw1, h1⟩` is shifted in the same way (`hw1` binds `var_0` and `h1` the `fun_sizenn` premise, so `numF _ _ h1` is ill-typed), and `constructor` in the generic integer branch and in the float branch leaves an extra `fun_sizenn` goal.

**Original proof sketch.**
- Local facts `numI`, `numF`, `numIF`: `numtype_Inn` and `numtype_Fnn` are injective and have disjoint images.
- Invert `wf_binop_`: the operator is either an integer operator `mk_binop__0 I bI` (t = I) or a float operator `mk_binop__1 F bF` (t = F).
- Integer operator: invert both `wf_num_`. A float payload is impossible (`numIF` on its numtype equation), and `numI` gives the same `I` for both operands, with `hw1, hw2 : wf_uN |I| x_i`. Then, by operator:
  - `div_sx`, for i32/i64: `idiv_total` gives `r : Option iN` with `fun_idiv_ |I| sx x1 x2 r` (`r = none` on division by zero or signed overflow). `idiv_wf` and `wf_opt_num_` give the well-formedness premises, and `fun_binop__case_6`/`7` closes the goal (`size ≠ none` by `decide`).
  - `rem_sx`: the same with `irem_total`, the model's `irem__is_wf`, and `fun_binop__case_8`/`9`.
  - `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `shr_sx`, `rotl`, `rotr`: `constructor` picks the clause. Its premise `wf_num_ I (mk_num__0 I (iop_ |I| x1 x2))` is `wf_num_.num__case_0` plus the model's `iadd__is_wf` … `ishr__is_wf` (theorems for add, sub and mul; axioms for the other seven) applied to `hw1 hw2`.
- Float operator: invert both `wf_num_` (an integer payload is impossible), giving `hw1, hw2 : wf_fN (sizenn F) x_i`. For each `F ∈ {F32, F64}` and `bF ∈ {add, sub, mul, div, min, max, copysign}`, apply `constructor` and discharge the two `Forall` premises with `wf_fN_num_` and the model axioms `fadd__is_wf` … `fcopysign__is_wf`.

**Current proof sketch.** The skeleton is the same. What is new:
- The patterns follow the new `wf_num_.num__case_1`: `⟨F1, x1, _, _, _, h1⟩` for the impossible float payload, and in the float branch `⟨F1, x1, _, hs1, hw1, h1⟩`, with `hs1 : fun_sizenn (numtype_Fnn F) var_0` and `hw1 : wf_fN var_0 x1`.
- DIV/REM: `fun_binop__case_6..9 sx x1 x2 _ r (fun_sizenn_sizenn _) Hr Ho2 (by decide) Hw Ho1`. The witness `fun_sizenn_sizenn` fixes the size argument to `sizenn (numtype_Inn I)`. `Hr` comes from `idiv_total`/`irem_total` at width `get! (size (valtype_Inn I))` and still fits, because both widths compute to 32/64.
- Other integer operators: after `constructor`, `try exact fun_sizenn_sizenn _` closes the new premise (fixing `var_0 := sizenn (numtype_Inn I)`), and the rest is as before.
- Float operators: first `rw [fun_sizenn_eq hs1] at hw1` (and `hs2`/`hw2`) turns `wf_fN var_0 x_i` into `wf_fN (sizenn (numtype_Fnn F)) x_i`. Then `constructor`, `try exact fun_sizenn_sizenn _`, `try apply wf_fN_num_`, and the same `f…__is_wf` axioms.

#### `relop_total` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* for well-formed `c_1, c_2 : num_(t)` and a well-formed `relop` of type `t`, the relation for `$relop_(t, relop, c_1, c_2)` has an output: `∃ c, fun_relop_ t relop c_1 c_2 c`, with `c : Option num_`. As for `binop_total`, `c = none` is not excluded here; `relop_not_none` excludes it. `t_progress_be_relop` uses both for Step_pure/relop (`(t.const c_1) (t.const c_2) (t.relop) ~> (i32.const c)`).

**What broke and why.** The errors are the same with and without the function views:
1. `numIF _ _ h1`/`h2` is ill-typed: `h1` is now the `fun_sizenn` premise of `wf_num_.num__case_1`, as in `binop_total`.
2. `fun_relop__case_4 sx x1 x2 c Hc` puts `c : u32` where `N` is expected. All `fun_relop_` clauses except the catch-all case 24 gained a size argument (`var_0 : N`, or `var_1 : N` in the `lt/gt/le/ge` clauses 4-11) with a premise `fun_sizenn (numtype t) var_0`, replacing `sizenn (numtype t)`.
3. Further consequences, not among the first reported errors: the float branch's `numF _ _ h1` is ill-typed for the same reason, and the `eq`/`ne` clauses and the float clauses, which had no premises before, now leave a `fun_sizenn` goal after `constructor`.

**Original proof sketch.**
- The helper facts and the `wf_relop_`/`wf_num_` inversions are as in `binop_total`.
- Integer operator:
  - `lt_sx`, `gt_sx`, `le_sx`, `ge_sx`: `ilt_total` … `ige_total` give the result bit `c` with `fun_ilt_ |I| sx x1 x2 c` (etc.), and `fun_relop__case_4..11` closes the goal.
  - `eq`, `ne`: closed by `constructor` (clauses 0-3, no premises).
- Float operator (`eq`, `ne`, `lt`, `gt`, `le`, `ge` for f32/f64): `constructor` (clauses 12-23, no premises; `feq_` etc. are opaque total functions).

**Current proof sketch.** The structure is the same, with the patterns updated as in `binop_total`.
- `lt`/`gt`/`le`/`ge`: `fun_relop__case_k sx x1 x2 _ c (fun_sizenn_sizenn _) Hc`. The size is fixed to `sizenn (numtype_Inn I)`, and `Hc` comes from `i…_total` at the definitionally equal width `get! (size (valtype_Inn I))`.
- `eq`/`ne` and all float cases: `constructor <;> exact fun_sizenn_sizenn _`.

#### `cvtop_total` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* for a well-formed `c_1 : num_(t_1)` and a well-formed conversion `cvtop` from `t_1` to `t_2`, the relation for `$cvtop__(t_1, t_2, cvtop, c_1)` has an output: `∃ c2, fun_cvtop__ t_1 t_2 cvtop c_1 c2`, with `c2 : Option (List num_)`. `c2 = none` is not excluded here; `cvtop_not_none` excludes it. `t_progress_be_cvtop` uses both to step `(t_1.const c_1) (t_2.cvtop_t_1)` (Lean `CVTOP t_2 t_1 cvtop`) by Step_pure/cvtop-val or Step_pure/cvtop-trap.

**What broke and why.** The errors are the same in both settings:
1. `numIF _ _ h1` is ill-typed, because of the `wf_num_.num__case_1` pattern shift (as in `binop_total`; the float-source branches' `numF _ _ h1` fails the same way, outside the first reported errors).
2. After `constructor` in the first integer-to-integer case (EXTEND, I32 to I32), the goal `fun_sizenn2 (numtype_Inn Inn.I32) ?var_1` is unsolved. `$sizenn1` and `$sizenn2` became relations, so `fun_cvtop__` clauses 0-27 (extend, wrap, trunc, trunc_sat, convert, promote, demote) gained fields `var_1 : N` and `var_0 : M`, premises `fun_sizenn2 (numtype t_2) var_1` and `fun_sizenn1 (numtype t_1) var_0`, and now compute at those widths.

The REINTERPRET clauses 28-35 are unchanged; they compare `$size` directly. Separately (not among the first reported errors), the REINTERPRET case of `wf_cvtop__Inn_1_Fnn_2`/`wf_cvtop__Fnn_1_Inn_2` now reads `fun_sizenn2 … var_1 → fun_sizenn1 … var_0 → var_0 = var_1` instead of `sizenn1 … = sizenn2 …`. So the old pattern `cvtop__Inn_1_Fnn_2_case_1 hsz` no longer names the width equation.

**Original proof sketch.**
- The helper facts are as in `binop_total`. Invert `wf_cvtop__` into its four shapes (int to int, int to float, float to int, float to float), substitute the numtype equations, and invert `wf_num_`; a payload of the wrong kind is refuted by `numIF`.
- int to int (`extend_sx`, `wrap`), all i32/i64 combinations: `constructor` (clauses 0-7, no premises).
- int to float:
  - `convert_sx`: `constructor` (clauses 16-19).
  - `reinterpret`: invert the operator's well-formedness to get `hsz : sizenn1 I1 = sizenn2 F2`. For mismatched widths (i32/f64, i64/f32), `decide` refutes `hsz`. For i32 to f32 and i64 to f64, `constructor <;> decide` uses clause 28 or 31, whose premises are two `size ≠ none` facts and the size equality.
- float to int: `trunc_sx` and `trunc_sat_sx` by `constructor` (clauses 8-15); `reinterpret` as above, with clauses 32/35.
- float to float (`promote`, `demote`): `constructor` (clauses 20-27).

**Current proof sketch.** The case structure is the same, with the patterns updated (`⟨F1', y, _, _, _, h1⟩` / `⟨F1', y, _, _, hw, h1⟩`). What is new:
- Non-reinterpret clauses: `apply Exists.intro <;> constructor <;> constructor <;> decide`. The second `constructor` builds the two size witnesses `fun_sizenn2_case_0` and `fun_sizenn1_case_0`, which fixes `var_1` and `var_0` to `get! (size (valtype_numtype t))`. `decide` proves their premise `size … ≠ none`.
- `reinterpret`: `cases hx with | cvtop__Inn_1_Fnn_2_case_1 _ _ hs2 hs1 hsz`, then `cases I1 <;> cases F2 <;> cases hs1 <;> cases hs2`. The float-to-int branch is the same with `cvtop__Fnn_1_Inn_2_case_2` and `cases F1 <;> cases I2 <;> …`. This makes both widths concrete numbers. For mismatched widths, `decide` refutes `hsz : var_0 = var_1`. For matching widths, `apply Exists.intro; constructor <;> decide` uses the unchanged clause 28 or 31 (int to float) or 32 or 35 (float to int).

#### `binop_before` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* on well-formed operands and operator, `fun_binop__before_fun_binop__case_38 t binop c_1 c_2` holds. That is, one of the 38 explicit clauses of `$binop_` matches, so the generated catch-all clause `fun_binop__case_38` (`¬ before → fun_binop_ … none`, meaning "`$binop_` is undefined") cannot apply. `binop_not_none` uses it.

**What broke and why.** The errors are the same as for `binop_total`, with and without the function views:
- `numIF _ _ h1`/`h2` is ill-typed (the `wf_num_.num__case_1` pattern shift).
- `fun_binop__before_fun_binop__case_38.fun_binop__case_6 sx x1 x2 r` puts `r : Option iN` where `N` is expected.

The before-predicate's constructors mirror the `fun_binop_` clauses with all their premises, so they gained the same size argument and `fun_sizenn` premise.

**Original proof sketch.** Exactly the case analysis of `binop_total`, building constructors of the before-predicate instead of `fun_binop_`'s:
- DIV/REM via `idiv_total`/`irem_total`, `idiv_wf`/`irem__is_wf` and `wf_opt_num_`;
- the other integer operators via `constructor`, `wf_num_.num__case_0` and `i…__is_wf`;
- float operators via `constructor`, `wf_fN_num_` and `f…__is_wf`.

**Current proof sketch.** The same adaptation as `binop_total`:
- updated `wf_num_` patterns;
- the DIV/REM constructors take `_ r (fun_sizenn_sizenn _)`;
- `try exact fun_sizenn_sizenn _` after `constructor`;
- in the float branch, `rw [fun_sizenn_eq hs1] at hw1` (and `hs2`) comes first.

#### `relop_before` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* on well-formed operands and operator, `fun_relop__before_fun_relop__case_24 t relop c_1 c_2` holds: an explicit clause of `$relop_` matches, so the catch-all `fun_relop__case_24` (result `none`) cannot apply. `relop_not_none` uses it.

**What broke and why.** The errors are the same with and without the function views: `numIF _ _ h1`/`h2` is ill-typed (pattern shift), and `exact uN.mk_uN 0` has type `uN` where `N` is expected. The before-predicate keeps the binders of the `fun_relop_` clauses but not all of their premises:
- Old: only the `lt/gt/le/ge` clauses 4-11 had a binder besides the pattern variables: `var_0 : uN` (the result bit, with its `fun_ilt_` premise dropped). No clause had a premise.
- New: the `eq`/`ne` clauses 0-3 and all float clauses 12-23 have an unconstrained `var_0 : N`. The `lt`..`ge` clauses have `var_1 : N` with a premise `fun_sizenn (numtype_Inn I) var_1`, plus the unconstrained `var_0 : uN`.

**Original proof sketch.** The inversions are as in `relop_total`. Then `cases rI <;> cases I <;> constructor <;> exact uN.mk_uN 0` fills the unconstrained result bit. For floats, `cases F <;> cases rF <;> constructor`.

**Current proof sketch.** The same. Integer goals are closed by `first | exact fun_sizenn_sizenn _ | exact uN.mk_uN 0 | exact 0` (the size premise, the dummy result bit, the dummy size). Float goals are closed by `constructor <;> exact 0`.

#### `cvtop_before` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* on a well-formed operand and conversion operator, `fun_cvtop___before_fun_cvtop___case_36 t_1 t_2 cvtop c_1` holds: an explicit clause of `$cvtop__` matches, so the catch-all `fun_cvtop___case_36` (result `none`) cannot apply. `cvtop_not_none` uses it.

**What broke and why.** The errors are the same in both settings: `numIF _ _ h1` is ill-typed (pattern shift), and after `constructor` (EXTEND, I32 to I32) a goal `⊢ N` is unsolved. The before-predicate's clauses 0-27 gained the binders `var_1 : N` and `var_0 : M` of the `fun_cvtop__` clauses, but not their `fun_sizenn1`/`fun_sizenn2` premises, so these binders are unconstrained. The REINTERPRET clauses 28-35 are unchanged, but the REINTERPRET well-formedness premise changed shape, as described for `cvtop_total`.

**Original proof sketch.** The same case analysis as `cvtop_total`, using the before-predicate's constructors:
- `constructor` for the non-reinterpret operators;
- for `reinterpret`, `hsz : sizenn1 … = sizenn2 …` is refuted by `decide` for mismatched widths; otherwise `constructor <;> decide`.

**Current proof sketch.** The same. The dummy binders are filled by `constructor <;> exact 0`. `reinterpret` is handled as in `cvtop_total`: `cases hs1 <;> cases hs2` makes the widths concrete, then either `decide` on `hsz : var_0 = var_1` or `constructor <;> decide`.

#### `unop_not_none` (TypeProgress; theorem) - restated and re-proved

*Statement (Wasm 2.0 terms):* for a well-formed `c_1 : num_(t)` and a well-formed `unop` of type `t`, `$unop_(t, unop, c_1)` is defined: it yields a result list `cs` (the empty list means a trap, Step_pure/unop-trap). The changed part:
- old: `fun_unop_ nt u n1 ≠ none`
- new: `∃ cs, fun_unop_ nt u n1 (some cs)`

**What broke and why.** `$unop_` uses `$sizenn`, so `fun_unop_` changed from a Lean function `numtype → unop_ → num_ → Option (List num_)` (a `match` that returns `none` for ill-typed combinations) to a relation `numtype → unop_ → num_ → Option (List num_) → Prop`. The relation has one clause per operator and width, each with `var_0 : N` and `fun_sizenn (numtype t) var_0`, plus a catch-all clause 22 with result `none`. The old statement no longer elaborates (`none` "is expected to have type `Option (List num_) → Prop`"), so the declaration is dropped in both settings.

**Original proof sketch.**
- Assume `fun_unop_ … = none`.
- Invert `wf_num_` (integer or float payload) and `wf_unop_` (integer or float operator), and substitute the numtype equation.
- Mixed integer/float combinations are refuted by `simp` on the numtype equation.
- For matching combinations, case on the width and the operator (`clz`, `ctz`, `popcnt`, `extendM_s`; `abs`, `neg`, `sqrt`, `ceil`, `floor`, `trunc`, `nearest`). `simp [fun_unop_]` evaluates the function to `some […]`, which contradicts the assumption.

**Current proof sketch.** The inversions and the case split are the same; the float-payload pattern is now `num__case_1 vF vx _ _ _ h3`. Each matching combination is closed by `exact ⟨_, by constructor; exact fun_sizenn_sizenn _⟩`. `constructor` selects the `fun_unop_` clause of that operator and width, and `fun_sizenn_sizenn` discharges the new size premise (size = `sizenn (numtype t)`).

#### `testop_not_none` (TypeProgress; theorem) - restated and re-proved

*Statement (Wasm 2.0 terms):* for a well-formed `c_1 : num_(t)` and a well-formed `testop` (only `eqz`, for i32/i64), `$testop_(t, testop, c_1)` is defined. The changed part:
- old: `fun_testop_ nt t n1 ≠ none`
- new: `∃ c, fun_testop_ nt t n1 (some c)`

**What broke and why.** `$testop_(Inn, EQZ, iN) = $ieqz_($sizenn(Inn), iN)`, so `fun_testop_` became a relation `numtype → testop_ → num_ → Option num_ → Prop`. It has clauses for `i32.eqz`/`i64.eqz` with a `fun_sizenn` premise, and a catch-all clause 2 with result `none`. The old statement no longer elaborates (`none` is expected to be `Option num_ → Prop`). The second reported error (`wf_testop_.casesOn` can only eliminate into `Prop`) follows from that. The declaration is dropped in both settings.

**Original proof sketch.**
- Invert `wf_testop_` (`t = numtype_Inn I`, operator `mk_testop__0 I tI`) and substitute.
- Invert `wf_num_`: a float payload is refuted with `numIF`, and `numI` identifies the widths.
- `cases tI` (only `EQZ`), then `cases I <;> simp [fun_testop_, numtype_Inn]` evaluates the function to `some …`.

**Current proof sketch.** The same steps up to `cases tI`, with the float pattern now `⟨F1, x1, _, _, _, h1⟩`. Then `cases I <;> exact ⟨_, by constructor; exact fun_sizenn_sizenn _⟩` builds `fun_testop__case_0`/`_1` (`i32.eqz`/`i64.eqz`), with the size witness from `fun_sizenn_sizenn`.

#### `t_progress_be_unop` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `t.unop`. This is the `Instr_ok.unop` case (Instr_ok/unop: `C ⊢ t.unop : [t] → [t]`) of the `Instrs_ok.rec` proof of `t_progress_be`. Take a well-formed configuration `(S; F; vcs ++ [t.unop])` whose well-formed values `vcs` have types `[t]`. Here `C` is `C'` with its locals set to the types of `F`'s locals and its labels and return set to arbitrary `lab` and `ret` (`upd_local_label_return`); also `Moduleinst_ok S F.module C'` and `Store_ok S` hold, and `[t.unop]` is not a `br` or `return` (`not_lf_br`, `not_lf_return`). The motive concludes "`[t.unop]` is all constants, or the configuration steps", and the proof shows that it steps: `(t.const c_1) (t.unop)` reduces to `t.const c` or `trap`.

**What broke and why.** The error: `cases Eunop : fun_unop_ t unop n` fails ("major premise type is not an inductive type `Option (List num_) → Prop`"), because `fun_unop_` is now a relation, not a value to case on. Two other things changed as well:
- `Step_pure.unop_val`/`unop_trap` changed shape. The old premises were stated on `fun_unop_ nt unop c_1` itself (`≠ none`, `Option.get! … = []`, length, `contains`). The new rules take `var_0 : Option (List num_)`, a witness `fun_unop_ nt unop c_1 var_0`, `var_0 ≠ none`, and the `get!` premises on `var_0`.
- The lemma it uses, `unop_not_none`, was restated.

The errors are the same in both settings.

**Original proof sketch.**
- Unfold the motive `t_progress_be_P`, introduce the configuration and the hypotheses, and choose the "steps" disjunct (`right`).
- From the function type `[t] → [t] = ts1 → ts2`, get `map typeof vcs = [t]`. `vcs` cannot be empty or have two or more elements, so `vcs = [v1]` with `typeof v1 = t`.
- `invert_typeof_numtype` gives `v1 = t.const n`.
- Case on the value `fun_unop_ t unop n` (Rocq `case Eunop`):
  - `some []`: step to `[trap]` by `Step.pure` and `Step_pure.unop_trap` (Step_pure/unop-trap; premises by rewriting with `Eunop`).
  - `some (c' :: l)`: step to `[t.const c']` by `Step_pure.unop_val` (Step_pure/unop-val).
  - `none`: a contradiction. `wf_val v1` gives `wf_num_ t n` (invert `v1 = CONST t n`, then `val_case_0`). `wf_instr (UNOP t unop)` gives `wf_unop_ t unop` (`instr_case_14`). `unop_not_none` then rules out `none`.

**Current proof sketch.** The same up to `vcs = [v1]`. Then:
- `invert_typeof_numtype_wf v1 t Hts HP1` gives `n` together with `wf_num_ t n` up front. `wf_unop_ t unop` comes from `cases HWfinstr; assumption`.
- `unop_not_none t unop n Hwf1 Hwfu` gives `c` and `Eunop : fun_unop_ t unop n (some c)`. There is no `none` branch.
- `c = []`: `Step_pure.unop_trap t n unop _ Eunop (by simp) rfl`, with `var_0 = some []`, `some [] ≠ none` and `get! (some []) = []`.
- `c = c' :: l`: `Step_pure.unop_val t n unop c' _ Eunop (by simp) (by simp) (by simp)`, for `≠ none`, length > 0 and `contains c'`.

#### `t_progress_be_testop` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `t.testop`. This is the `Instr_ok.testop` case (Instr_ok/testop: `C ⊢ t.testop : [t] → [i32]`), under the same hypotheses as `t_progress_be_unop`: with a single operand `v1 : t` on the stack, `(t.const c_1) (t.testop)` steps to `i32.const c` (Step_pure/testop).

**What broke and why.** The error: `cases ENone : fun_testop_ nt testop_nt n1` fails (`Option num_ → Prop` is not an inductive type), because `fun_testop_` is now a relation. Three other things changed as well:
- `Step_pure.testop` now takes `var_0 : Option num_` with a witness `fun_testop_ nt testop c_1 var_0`, `var_0 ≠ none`, `c = get! var_0` and `wf_num_ I32 c`. The old premises were `fun_testop_ … ≠ none`, `c = get! (fun_testop_ …)` and `wf_num_ I32 c`.
- The model's `testop__is_wf` now also takes the relation witness.
- `testop_not_none` was restated.

The errors are the same in both settings.

**Original proof sketch.**
- As in `t_progress_be_unop` up to `vcs = [v1]`.
- `invert_typeof_numtype_wf` gives `n1` with `v1 = t.const n1` and `wf_num_ t n1`; `wf_testop_` comes from `wf_instr`.
- Case on `fun_testop_ nt testop_nt n1`:
  - `some c'`: derive `Hne` and `Hc` by rewriting, then step to `[i32.const c']` with `Step_pure.testop`. Its premise `wf_num_ I32 c'` comes from `testop__is_wf`.
  - `none`: absurd by `testop_not_none`.

**Current proof sketch.** The same setup. `testop_not_none` gives `c'` and `Etestop : fun_testop_ nt testop_nt n1 (some c')`. `Hne : some c' ≠ none` and `Hc : c' = get! (some c')` hold by `simp`. The step is `Step_pure.testop nt n1 testop_nt c' (some c') Etestop Hne Hc (testop__is_wf nt testop_nt n1 c' (some c') Etestop Hwft Hwf1 Hne Hc)`.

### 7.6 Q2, `TypeProgress`: lane and vector-operator totality lemmas (13 constructs)

#### `wf_lane_Jnn_inv` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* inversion for integer lanes: a lane `l` that is well formed at the integer lane type `Jnn` (`wf_lane_ (lanetype_Jnn J) l`) and projects as an integer lane (`proj_lane__0 l ≠ none`) is `mk_lane__0 J x` with `x ∈ iN($lsize(Jnn))` (`wf_uN (lsize (lanetype_Jnn J)) x`; spec `syntax lane_(Jnn) = iN($lsize(Jnn))`). The statement is unchanged. `lsize` is now the HelperLemmas function view of `fun_lsize`, defined exactly like the old model's `lsize`.

**What broke and why.** `$lsize` is defined through the partial `$size` (`Option.get!`), so `sideconditions_on_defs` turned it into the relation `fun_lsize lt n`. As a result `wf_lane_.lane__case_0` changed from `wf_uN (lsize (lanetype_Jnn J)) x → lt = lanetype_Jnn J → …` to `(n : N) … fun_lsize (lanetype_Jnn J) n → wf_uN n x → lt = lanetype_Jnn J → …`. `lane__case_1` changed the same way, with `fun_sizenn (numtype_Fnn F) n → wf_fN n x`.
- Without the function views the statement no longer elaborates. `lsize` is unknown, and autoImplicit reports "Function expected at lsize", so the theorem is lost.
- With the views the statement elaborates, but the old pattern `lane__case_0 J' c Hc Heq` now binds `Hc` to the size `n : N` and `Heq` to the `fun_lsize` premise. This causes three failures:
  - `simp [lanetype_Jnn] at Heq` leaves `False` unsolved in the `J ≠ J'` subgoals.
  - `exact ⟨c, rfl, Hc⟩` is ill-typed, because `Hc : N`.
  - In the float branch, `simp … at Heq` makes no progress.

**Original proof sketch.**
- `cases` on the lane's well-formedness. The projection hypothesis is not used.
- Integer lane `mk_lane__0 J' c` with `Hc : wf_uN (lsize (lanetype_Jnn J')) c` and `Heq : lanetype_Jnn J = lanetype_Jnn J'`:
  - show `J' = J` by `cases J <;> cases J'`; `simp [lanetype_Jnn] at Heq` refutes the off-diagonal cases;
  - substitute and return `⟨c, rfl, Hc⟩`.
- Float lane `mk_lane__1 F c`: the equation `lanetype_Jnn J = lanetype_Fnn F` is impossible (`cases F <;> cases J <;> simp … at Heq`).

**Current proof sketch.** The case analysis is the same, but the patterns bind the two new fields: `lane__case_0 J' c n Hn Hc Heq` and `lane__case_1 F c n Hn Hc Heq`. So `Hc` is again the range fact `wf_uN n c` and `Heq` the lane-type equation. After `J' = J` is substituted, `fun_lsize_eq Hn` (HelperLemmas) turns the width witness `Hn : fun_lsize (lanetype_Jnn J) n` into `n = lsize (lanetype_Jnn J)`. Rewriting this into `Hc` gives the old conclusion `wf_uN (lsize (lanetype_Jnn J)) c`. The float branch is refuted as before.

#### `wf_lane_Jnn_some` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* every lane that is well formed at an integer lane type `Jnn` projects as an integer lane: `wf_lane_ (lanetype_Jnn J) l → proj_lane__0 l ≠ none`. This holds because the union `lane_` has separate integer (`mk_lane__0`) and float (`mk_lane__1`) constructors. `lanes_Jnn_form` uses it, and so do `vunop_total` and `vunop_not_none`, which need it to supply the side premise of `vunop_real`. The statement is unchanged.

**What broke and why.** The statement mentions no size function, so it elaborates in both settings, but the proof broke in both. `wf_lane_.lane__case_1` (spec `lane_(Fnn) = fN($sizenn(Fnn))`) gained a size field `n` and the premise `fun_sizenn (numtype_Fnn F) n`, because `$sizenn` became the relation `fun_sizenn`. In the old pattern `lane__case_1 F c Hc Heq`, the name `Heq` therefore lands on the `fun_sizenn` premise instead of the lane-type equation, and `simp [lanetype_Jnn, lanetype_Fnn] at Heq` fails with "`simp` made no progress".

**Original proof sketch.** `cases` on the lane's well-formedness.
- Integer lane `mk_lane__0 J' c`: `proj_lane__0` returns `some c`, which `simp [proj_lane__0]` closes.
- Float lane `mk_lane__1 F c`: the lane-type equation `lanetype_Jnn J = lanetype_Fnn F` is contradictory (`exfalso; cases F <;> cases J <;> simp … at Heq`).

**Current proof sketch.** The argument is identical. Only the patterns bind the new fields (`lane__case_0 J' c n Hn Hc Heq`, `lane__case_1 F c n Hn Hc Heq`), so `Heq` again names the lane-type equation. No size fact is used.

#### `wf_lane_Fnn_inv` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* inversion for float lanes: a lane that is well formed at the float lane type `Fnn` is `mk_lane__1 F x` with `x ∈ fN($sizenn(Fnn))` (`wf_fN (sizenn (numtype_Fnn F)) x`; spec `syntax lane_(Fnn) = fN($sizenn(Fnn))`). The statement is unchanged. `sizenn` is now the HelperLemmas function view of `fun_sizenn`.

**What broke and why.** The model change is the same as for `wf_lane_Jnn_inv`: `$lsize` and `$sizenn` became `fun_lsize` and `fun_sizenn`, and both `wf_lane_` constructors gained a size field and a relation premise.
- Without the views the statement fails, because `sizenn` is unknown.
- With the views, in the old pattern `lane__case_0 J c Hc Heq` the name `Heq` is the premise `fun_lsize lanetype.I32 Hc`. The integer-lane refutation therefore leaves `False` unsolved. In the float branch, `simp [lanetype_Fnn] at Heq` makes no progress, and `Hc` is the size rather than the `wf_fN` fact.

**Original proof sketch.** `cases` on the lane's well-formedness.
- Integer lane: `lanetype_Fnn F = lanetype_Jnn J` is impossible (`cases F <;> cases J <;> simp`).
- Float lane `mk_lane__1 F' c` with `Hc : wf_fN (sizenn (numtype_Fnn F')) c`:
  - show `F' = F` by `cases F <;> cases F'`; `simp [lanetype_Fnn] at Heq` refutes the off-diagonal cases;
  - substitute and return `⟨c, rfl, Hc⟩`.

**Current proof sketch.** The proof is the same, with the patterns `lane__case_0 J c n Hn Hc Heq` and `lane__case_1 F' c n Hn Hc Heq`. After `subst HF`, `rw [fun_sizenn_eq Hn] at Hc` turns `wf_fN n c` into `wf_fN (sizenn (numtype_Fnn F)) c`.

#### `Forall_lane_map_wf` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* lane-wise unary integer operations preserve lane well-formedness. Suppose `f : iN → iN` maps `iN($lsize(Jnn))` into itself and every lane of `ls` is `mk_lane__0 J x` with `x` in range. Then every `mk_lane__0 J (f (proj_lane__0 l).get!)` is a well-formed `Jnn` lane. `vunop_real` uses it for `$ineg_` and `$ipopcnt_`, i.e. `iNxM.neg` and `i8x16.popcnt` (spec `$vunop_(Jnn X M, NEG, v128_1) = $inv_lanes_(Jnn X M, $ineg_($lsizenn(Jnn), lane_1)*)`). The statement is unchanged; `lsize` is the function view.

**What broke and why.**
- Without the views the statement fails, because `lsize` is unknown.
- With the views only the final constructor application `wf_lane_.lane__case_0 _ _ _ (Hf x hwx) rfl` broke. The fourth explicit argument of `lane__case_0` is now the size field `n : N`, which comes with the new premise `fun_lsize (lanetype_Jnn J) n`. So `Hf x hwx` is rejected ("Application type mismatch … expected to have type N").

**Original proof sketch.** For `l ∈ ls`:
- destruct the hypothesis into `l = mk_lane__0 J x` with `hwx : wf_uN (lsize (lanetype_Jnn J)) x`;
- substitute, so the projected value is definitionally `x`;
- build the lane with `wf_lane_.lane__case_0` from `Hf x hwx` and `rfl` for the lane-type equation.

**Current proof sketch.** The proof is the same, except the lane is built as `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) (Hf x hwx) rfl`. The size field is instantiated with the view value `lsize (lanetype_Jnn J)`, and `fun_lsize_lsize` (HelperLemmas) discharges its `fun_lsize` premise. `Hf x hwx` then fits the `wf_uN` premise unchanged.

#### `Forall_lane_fop_wf` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* lane-wise float operations preserve lane well-formedness. Consider a float lane operation `fop : N → fN → List fN`. Spec float operators are set-valued, e.g. `$fabs_(N, fN(N)) : fN(N)*`. Suppose `fop` maps `fN($sizenn(Fnn))` arguments to lists of `fN($sizenn(Fnn))` results. Then for every well-formed `Fnn` lane `l` and every result `it ∈ fop (sizenn (numtype_Fnn F)) (proj_lane__1 l).get!`, the lane `mk_lane__1 F it` is well formed. `vunop_real` uses it for `$fabs_`, `$fneg_`, `$fsqrt_`, `$fceil_`, `$ffloor_`, `$ftrunc_` and `$fnearest_` (spec `$vunop_(Fnn X M, ABS, v128_1)` with `lane** = $setproduct_(lane_(Fnn), $fabs_($sizenn(Fnn), lane_1)*)`). The statement is unchanged; `sizenn` is the function view.

**What broke and why.**
- Without the views the statement fails, because `sizenn` is unknown.
- With the views, `wf_lane_.lane__case_1 _ _ _ (Hf x hwx r hr) rfl` has the wrong arity ("expected to have type N"). `lane__case_1` gained the size field `n` and the premise `fun_sizenn (numtype_Fnn F) n`.

**Original proof sketch.**
- For `l ∈ ls`, invert with `wf_lane_Fnn_inv` to get `l = mk_lane__1 F x` and `hwx : wf_fN (sizenn (numtype_Fnn F)) x`.
- For each `r ∈ fop (sizenn …) x`, build `wf_lane_.lane__case_1` from `Hf x hwx r hr`.

**Current proof sketch.** The proof is the same, with `wf_lane_.lane__case_1 _ _ _ _ (fun_sizenn_sizenn _) (Hf x hwx r hr) rfl`: the size field is `sizenn (numtype_Fnn F)`, witnessed by `fun_sizenn_sizenn`. It relies on the repaired `wf_lane_Fnn_inv`, whose conclusion is unchanged.

#### `iabs_lane_total` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* `$iabs_` is total on an in-range integer lane and yields a well-formed lane. For `x ∈ iN($lsize(Jnn))` there is a `v` with `fun_iabs_ (lsizenn (lanetype_Jnn J)) x v` such that `mk_lane__0 J v` is a well-formed `Jnn` lane. This is the per-lane step of `iNxM.abs` (spec `$vunop_(Jnn X M, ABS, v128_1) = $inv_lanes_(Jnn X M, $iabs_($lsizenn(Jnn), lane_1)*)`). The statement is unchanged; `lsize` and `lsizenn` are the function views.

**What broke and why.**
- Without the views the statement fails, because `lsize` and `lsizenn` are unknown.
- With the views, `fun_iabs_` itself is unchanged: it was already a relation, with a `fun_signed_` premise. Only the final `wf_lane_.lane__case_0 _ _ _ (iabs__is_wf …) rfl` broke, because of the new size field of `lane__case_0` ("expected to have type N").

**Original proof sketch.**
- `iswf_uN_proj_lt Hx` gives `proj_uN_0 x < 2^N`.
- `signed_total` provides `z` with `fun_signed_ N (proj_uN_0 x) z`.
- `fun_iabs__case_0` yields `fun_iabs_ N x (if z ≥ 0 then x else ineg_ N x)`. This matches the spec `$iabs_(N, i) = i` if `$signed_(N, i) >= 0`, otherwise `$ineg_(N, i)`.
- The model's `iabs__is_wf` keeps the result in range, and `lane__case_0` builds the lane.

**Current proof sketch.** The proof is the same; only the lane construction changed, to `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) (iabs__is_wf _ _ _ _ Ha Hx rfl) rfl`. The size field is `lsize (lanetype_Jnn J)`, witnessed by `fun_lsize_lsize`. The range proof from `iabs__is_wf` is at width `lsizenn (lanetype_Jnn J)`, which is definitionally `lsize (lanetype_Jnn J)`, so it fits the `wf_uN` premise.

#### `vunop_real` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress helper for `VUNOP sh vunop` (`Instr_ok/vunop: C ⊢ VUNOP sh vunop : V128 → V128`; e.g. `i32x4.abs`, `i8x16.popcnt`, `f64x2.sqrt`). Assume:
- the shape and operator are well formed (`wf_shape sh`, `wf_vunop_ sh vunop`);
- the `v128` constant `val` is well formed;
- for an integer shape `Jnn X M`, every lane of `$lanes_(sh, val)` projects as an integer lane.

Then some real (non-catch-all) case of `$vunop_` applies, `∃ vs, fun_vunop_ sh vunop val (some vs)`, and, as a second conjunct proved separately, the "before" predicate `fun_vunop__before_fun_vunop__case_26` holds; its negation is the premise of the catch-all case 26 (`… none`). From this, `vunop_total` and `vunop_not_none` obtain the premise that `t_progress_be_vunop` needs to step with `Step_pure/vunop` or `Step_pure/vunop-trap`. The statement is unchanged.

**What broke and why.**
- Without the views, the proof broke at `Forall_lane_Jnn J _ Hl' Hsome`. That lemma's statement mentions the removed `lsize`, which autoImplicit turned into an implicit argument that Lean cannot synthesize here. So the break came from the lane lemmas it uses (`Forall_lane_Jnn`, `Forall_iabs_total`, `Forall_lane_map_wf`, …), which no longer elaborate.
- With the views, the break comes from the size relations in `fun_vunop_`:
  - Every real case of `fun_vunop_` and of its before-predicate gained a size field. Integer cases 0–11 (`ABS`, `NEG`, `POPCNT` × `I32`, `I64`, `I8`, `I16`) carry the premise `fun_lsizenn (lanetype_Jnn J) var`; float cases 12–25 carry `fun_sizenn (numtype_Fnn F) var`.
  - The lane operations are applied at that field (`fun_iabs_ var_1 …`, `ineg_ var_0 …`, `fabs_ var_0 …`) instead of the old `lsizenn (lanetype_Jnn J)` and `sizenn (numtype_Fnn F)`.
  - No alternative of the old `first | exact H2b | … | exact Hpop | rfl` lists proves the new premise. The last alternative, `rfl`, fails on it ("lanetype_Jnn Jnn.I32 is not definitionally equal to lsizenn (lanetype_Jnn Jnn.I32)").

**Original proof sketch.**
- `Hl := lanes__is_wf …`: every lane of `val` at shape `sh` is well formed.
- `cases` on `wf_vunop_`:
  - Integer shape `Jnn X M` (`vunop__case_0 J M o Ho Hs`). The proof first prepares lane facts:
    - `Hsome`: every lane projects as an integer lane (from the side hypothesis, via `all_Forall`);
    - `Hlx := Forall_lane_Jnn`: every lane is `mk_lane__0 J x` with `x` in range;
    - `Forall_iabs_total`: the `$iabs_` lane results `vs`, with the `Forall₂` relation and length (`H2a`, `H2b`) and well-formed result lanes (`Hvw`);
    - `Hneg`, `Hpop`: `Forall_lane_map_wf` with `ineg__is_wf` and `ipopcnt__is_wf`.

    Then `cases J <;> cases o`. `POPCNT` at `J ≠ I8` is refuted by inverting `Ho : wf_vunop_Jnn_N` (spec `POPCNT -- if Jnn = I8`).
  - Float shape `Fnn X M`: one `Forall_lane_fop_wf` fact per float operator (from `fabs__is_wf` … `fnearest__is_wf`), then `cases F <;> cases o`.
- In every remaining goal:
  - `refine ⟨?_, ?_⟩`;
  - `apply Exists.intro; constructor` for the `fun_vunop_` part, and `constructor` for the before-predicate. In both, `constructor` picks the case that matches the shape and operator.
  - Each premise is then closed by `first` over the prepared facts and `Hsh`. `rfl` comes last, for the defining equations `lane_1* = $lanes_(…)`, `v128 = $inv_lanes_(…)` and `v_M = M_0`.

**Current proof sketch.** The structure and automation are the same. The only addition is a size witness `Hsz`, introduced before the case split:
- integer branch: `Hsz := fun_lsizenn_lsizenn (lanetype_Jnn J)`;
- float branch: `Hsz := fun_sizenn_sizenn (numtype_Fnn F)`.

`exact Hsz` is offered before `rfl` in all four `first` lists. It discharges the new size premise of every real case of `fun_vunop_` and of the before-predicate. In the NEG, POPCNT and float cases that premise comes first, so `exact Hsz` sets the size field to the view value, `lsizenn (lanetype_Jnn J)` or `sizenn (numtype_Fnn F)`. In the ABS cases (0–3) it follows the `Forall₂ fun_iabs_` premise, so `exact H2a` has already fixed the field to `lsizenn (lanetype_Jnn J)` and `Hsz` only matches it. That is the width at which the width-dependent lane facts (`H2a`, `Hneg`, `Hpop`, `Habs`, …) are stated, so the remaining premises are closed exactly as before.

#### `zip_lane_wf` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* lane-wise binary integer operations preserve lane well-formedness. Suppose `f` maps in-range `Jnn` arguments to an in-range result, and `L1`, `L2` are equally long lists of `jlane J` lanes (`mk_lane__0 J x` with `x ∈ iN($lsize(Jnn))`). Then `Forall₂` over `L1`, `L2` holds for `wf_lane_ lt (mk_lane__0 J (f l1 l2))`, where `lt = lanetype_Jnn J`. `vbinop_some` uses it for the `Map₂`-shaped operators `$iadd_`, `$isub_`, `$imul_`, `$iavgr_` and `$iq15mulr_sat_` (`iNxM.add`, `.sub`, `.mul`, `.avgr_u`, `i16x8.q15mulr_sat_s`). The statement is unchanged; `lsize` is the function view, and `jlane` is unchanged.

**What broke and why.**
- Without the views the statement fails, because `lsize` is unknown.
- With the views, the final `wf_lane_.lane__case_0 _ _ _ (Hf _ _ Hx1 Hx2) rfl` has the wrong arity, because `lane__case_0` has a new size field.

**Original proof sketch.**
- Substitute `lt`.
- For a pair `(l1, l2)` in `zip L1 L2`, `List.of_mem_zip` gives membership in each list.
- Destruct `jlane J` for both lanes: `l1 = mk_lane__0 J x1` and `l2 = mk_lane__0 J x2`, both in range.
- Build `lane__case_0` from `Hf _ _ Hx1 Hx2`.

**Current proof sketch.** The proof is the same, with `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) (Hf _ _ Hx1 Hx2) rfl`.

#### `zip_flane_wf` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* the float analogue of `zip_lane_wf`. Suppose the set-valued `fop : N → fN → fN → List fN` maps `fN($sizenn(Fnn))` arguments to lists of in-range results, and `L1`, `L2` are equally long lists of `flane F` lanes. Then every result `it` of `fop (sizenn (numtype_Fnn F)) l1 l2` gives a well-formed lane `mk_lane__1 F it`. `vbinop_some` uses it for `$fadd_` … `$fpmax_` (`fNxM.add/sub/mul/div/min/max/pmin/pmax`; spec `lane** = $setproduct_(lane_(Fnn), $fadd_($sizenn(Fnn), lane_1, lane_2)*)`). The statement is unchanged; `sizenn` is the function view.

**What broke and why.**
- Without the views the statement fails, because `sizenn` is unknown.
- With the views, `wf_lane_.lane__case_1 _ _ _ (Hf _ _ Hx1 Hx2 r hr) rfl` has the wrong arity, because of the new size field and its `fun_sizenn` premise.

**Original proof sketch.**
- For a zipped pair, destruct `flane F` for both lanes.
- For each result `r`, build `lane__case_1` from `Hf _ _ Hx1 Hx2 r hr`.

**Current proof sketch.** The proof is the same, with `wf_lane_.lane__case_1 _ _ _ _ (fun_sizenn_sizenn _) (Hf _ _ Hx1 Hx2 r hr) rfl`.

#### `zip_lane_wf2` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* the width-changing variant of `zip_lane_wf`. Suppose `f` maps in-range `Ji`-width arguments to an in-range `Jo`-width result. Then, lane-wise over equally long lists of `jlane Ji` lanes, `mk_lane__0 Jo (f l1 l2)` is a well-formed lane of type `lt = lanetype_Jnn Jo`. `t_progress_be_vextbinop` uses it for `EXTMUL half sx` (e.g. `i16x8.extmul_low_i8x16_s`). There, `f` is `$imul_($lsizenn2(Jnn_2), $extend__(…, ci_1), $extend__(…, ci_2))`. The statement is unchanged; `lsize` is the function view.

**What broke and why.**
- Without the views the statement fails, because `lsize` is unknown.
- With the views, `wf_lane_.lane__case_0 lt Jo _ (Hf x1 x2 Hx1 Hx2) hlt` has the wrong arity, because of the new size field.

**Original proof sketch.**
- Take the zipped pair; `List.of_mem_zip` gives membership in each list.
- Destruct `jlane Ji` for both lanes.
- Build `wf_lane_.lane__case_0 lt Jo _` from `Hf x1 x2 Hx1 Hx2`. The lane-type equation is the hypothesis `hlt` rather than `rfl`.

**Current proof sketch.** The proof is the same, with `wf_lane_.lane__case_0 lt Jo _ _ (fun_lsize_lsize _) (Hf x1 x2 Hx1 Hx2) hlt`. The size field of the output lane is `lsize (lanetype_Jnn Jo)`.

#### `vbinop_some` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress helper for `VBINOP sh vbinop` (`Instr_ok/vbinop: C ⊢ VBINOP sh vbinop : V128 V128 → V128`; e.g. `i8x16.add_sat_s`, `i64x2.mul`, `f32x4.pmin`). Assume a well-formed shape, two well-formed `v128` constants `c1` and `c2`, and a well-formed operator, `wf_vbinop_ sh op`. Operator well-formedness includes the side conditions of `syntax vbinop_(Jnn X N)`:
- `ADD_SAT`, `SUB_SAT` and `AVGR U` only if `$lsizenn(Jnn) <= 16`;
- `MUL` only if `>= 16`;
- `Q15MULR_SAT S` only if `= 16`;
- `MIN` and `MAX` only if `<= 32`.

Then `fun_vbinop_ sh op c1 c2 (some r)` holds for some list `r`, i.e. a real case of `$vbinop_` applies. `t_progress_be_vbinop` then steps with `Step_pure/vbinop-val` when `r = v :: _`, or `Step_pure/vbinop-trap` when `r = []`. The statement is unchanged.

**What broke and why.**
- Without the views: unknown identifier `lsizenn`. It occurs in `have Hle : lsizenn (lanetype_Jnn J) ≤ 16` and in lane-operation lambdas such as `fun a b => iadd_ (lsizenn (lanetype_Jnn J)) a b`.
- With the views, three model changes broke the proof:
  - Every explicit application `fun_vbinop_.fun_vbinop__case_k …` has the wrong arity ("argument `rfl` … expected to have type N"). Each real case of `fun_vbinop_` gained a size field: integer cases 0–35 carry the premise `fun_lsizenn (lanetype_Jnn J) var`, and float cases 36–51 carry `fun_sizenn (numtype_Fnn F) var`. The lane operation is applied at that field instead of at `lsizenn (…)` or `sizenn (…)`.
  - The `Forall₃` cases (`ADD_SAT`, `SUB_SAT`, `MIN` and `MAX`, whose lane operations are relations such as `fun_iadd_sat_`) also gained the restored premise `|lane_1*| = |lane_2*|`.
  - The side conditions in `wf_vbinop_Jnn_N` are now stated on a relation output (`fun_lsizenn (lanetype_Jnn J) n → n ≤ 16 → …`). So `cases Ho; assumption` no longer proves `lsizenn (lanetype_Jnn J) ≤ 16`.

**Original proof sketch.**
- `cases` on `wf_vbinop_`.
- Integer shape `Jnn X M`. First the lane facts:
  - `lanes_Jnn_form`: the lanes of `c1` and `c2` are `jlane J` (`HL1`, `HL2`);
  - `jlane_some`: they project as integer lanes (`HS1`, `HS2`);
  - `lanes_size_eq`: both vectors have the same lane count (`Hsz`).

  Then `cases o`:
  - `ADD`, `SUB`, `MUL`, `AVGR U` and `Q15MULR_SAT S` have the spec form `$inv_lanes_(Jnn X M, $iadd_($lsizenn(Jnn), lane_1, lane_2)*)` (shown for `ADD`), a `Map₂`. `zip_lane_wf` with the operator's `*_is_wf` gives the `Forall₂` well-formedness `hz` of the result lanes. After `cases J`, the explicit case (one of `fun_vbinop__case_0`–`_7` and `_24`–`_35`; cases 8–23 are the `Forall₃` ones) is applied to `rfl` (for `lane_i* = $lanes_(…)`, the result and `v_M = M_0`) and to `HS1`, `HS2`, `Hsh`, `Hsz` and `hz`.
  - `ADD_SAT sx`, `SUB_SAT sx`, `MIN sx` and `MAX sx`: `zip_lane_rel`, with `iadd_sat_total_wf`, `isub_sat_total_wf`, `imin_total_wf` or `imax_total_wf`, gives lane results `vs`. It provides the `Forall₃` relation `H3`, the range fact `Hw` and the length fact `Hsv`. `Hw'` turns `Hw` into well-formed result lanes, and the case is applied with `vs` for both of its result-list fields.
  - The side conditions `Hle`, `Hge` and `Heq` come from `cases Ho; assumption`. After `cases J` the goals come in the order I32, I64, I8, I16, which is the constructor order. The excluded (J, op) pairs, e.g. `ADD_SAT` on `i32x4`/`i64x2`, `MUL` on `i8x16`, `MIN` on `i64x2`, are closed by `absurd H (by decide)`.
- Float shape `Fnn X M`:
  - `lanes_Fnn_form` and `lanes_size_eq`;
  - `cases o`;
  - `zip_flane_wf` with `fadd__is_wf` … `fpmax__is_wf`;
  - `cases F`;
  - apply cases 36–51, with `rfl` for the lane lists, the `$setproduct_` list and the result list.

**Current proof sketch.** The structure is the same. The changes are:
- Every integer constructor application takes the extra size field `_` and the premise `fun_lsizenn_lsizenn _`. This fixes the field to the view value `lsizenn (lanetype_Jnn J)`, so `hz` and `H3`, which are stated at width `lsizenn (lanetype_Jnn J)`, fill the other premises as before (`Hw'` does not depend on the width). Every float application takes `_` and `fun_sizenn_sizenn _`.
- The `Forall₃` applications also pass `Hsz` for the new `|lane_1*| = |lane_2*|` premise. In these cases the size field sits between the two result lists (`vs _ vs`).
- The bounds are read off the new `wf_vbinop_Jnn_N` constructors with `cases Ho; rename_i hn hb; rwa [fun_lsizenn_eq hn] at hb`. This rewrites the bound on the output `n` into a bound on `lsizenn (lanetype_Jnn J)`. The `absurd … (by decide)` exclusions are unchanged, since `decide` evaluates the view.
- `Hw'` uses the new lane constructor: `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) (Hw v hv) rfl`.

#### `vrelop_some` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress helper for `VRELOP sh vrelop` (`Instr_ok/vrelop: C ⊢ VRELOP sh vrelop : V128 V128 → V128`; `iNxM.eq/ne/lt_sx/gt_sx/le_sx/ge_sx`, `fNxM.eq/ne/lt/gt/le/ge`). For a well-formed shape and operator and two well-formed `v128` constants, `fun_vrelop_ sh op c1 c2 (some r)` holds for some `r`. `t_progress_be_vrelop` feeds this to `Step_pure/vrelop`. The statement is unchanged.

**What broke and why.**
- Without the views: unknown identifier `lsizenn`, in the lane relations passed to `zip_lane_rel` (e.g. `fun a b r => fun_ilt_ (lsizenn (lanetype_Jnn J)) sx a b r`).
- With the views: unsolved goals in both branches.
  - Each integer case of `fun_vrelop_` (0–23) gained a size field `var_0` with the premise `fun_lsizenn (lanetype_Jnn J) var_0`. `var_0` is used as the width of `$ieq_` (and the other comparisons) and of `$extend__(1, N, S, …)`.
  - Each float case (24–35) gained `fun_sizenn (numtype_Fnn F) var_0`. The side condition `$isize(Inn) = $size(Fnn)`, which chooses the integer result shape `Inn X M`, is now `fun_isize v_Inn var_1` together with `var_1 = (size (valtype_Fnn F)).get!`. Before, it was `isize v_Inn = (size (valtype_Fnn F)).get!`.
  - No pass of the old automation proves these relation premises.
  - In addition, the `wf_shape.shape_case_0` pattern (two new fields) and the `wf_lane_.lane__case_0` applications have the wrong arity.

**Original proof sketch.**
- `hMap2`: the model's `Map₂` is `List.zipWith`.
- `cases` on `wf_vrelop_`.
- Integer shape `Jnn X M`:
  - lane facts: `HL1`, `HL2` (`lanes_Jnn_form`), `HS1`, `HS2` (`jlane_some`) and `Hsz` (`lanes_size_eq`);
  - `rcases o` into `EQ`, `NE`, `LT sx`, `GT sx`, `LE sx` and `GE sx`;
  - for the four ordered comparisons, whose lane operations are the relations `fun_ilt_` and so on, `zip_lane_rel` with `icmp_total_bit` provides lane results `vs`: the `Forall₃` relation `H3`, the 1-bit results `Hw` and the length `Hvs`;
  - `cases J`, then `apply Exists.intro; constructor` to select the matching case.
  - Then come the passes: `rfl` for the equations that define `lane_1*`, `lane_2*`, `lane_3*` and the result; `exact H3`; and the "vrelop_close" alternatives. These are `HS1`, `HS2`, `Hsz`, `Hsh`, `Hvs`, `Hvs.trans Hsz`, `Hw`, and `Forall2_all` with `ieq_bit`/`ine_bit` (the 1-bit results of `EQ`/`NE`). The result lanes `mk_lane__0 J ($extend__(1, N, S, …))` are shown well formed via `Forall_zipWith` or `Forall_map_P`, with `extend___is_wf` and `wf_lane_.lane__case_0`.
- Float shape `Fnn X M`:
  - lane facts: `lanes_Fnn_form`, `flane_some` and `lanes_size_eq`;
  - `cases F; cases o`, then `apply Exists.intro; constructor`;
  - choose `v_Inn` with `isize v_Inn = size F`, via `(rfl : isize Inn.I32 = _)` or the `Inn.I64` variant;
  - the `rfl` passes;
  - then `HS1`, `HS2`, `Hsz` and `Hsh`;
  - the result shape `Inn X M` is made well formed by repacking `Hsh` (`cases Hsh` … `wf_shape.shape_case_0 _ _ hd hm`). This works because `$lsize(Inn) = $lsize(Fnn)` holds definitionally;
  - `decide` for `size (valtype_Fnn F) ≠ none`;
  - `Forall2_all` with `feq_bit` … `fge_bit`;
  - the result lanes via `Forall_zipWith` and `extend___is_wf`.

**Current proof sketch.** The old passes remain, with these additions:
- Integer branch: right after `constructor`, `all_goals try exact fun_lsizenn_lsizenn _` closes the new `fun_lsizenn (lanetype_Jnn J) var_0` premise and fixes `var_0 := lsizenn (lanetype_Jnn J)`. `H3` and the other alternatives are stated with `lsizenn`, so they then match as before.
- Float branch:
  - The old `(rfl : isize Inn.I32 = _)` pass now closes `var_1 = (size (valtype_Fnn F)).get!`, with `var_1 := isize Inn.I32` or `isize Inn.I64`.
  - A new pass, `first | exact fun_isize_isize _ | exact fun_sizenn_sizenn _`, closes `fun_isize v_Inn var_1` (which fixes `v_Inn`) and `fun_sizenn (numtype_Fnn F) var_0`.
- Result shape: `cases Hsh with | shape_case_0 _ _ n hn hd hm => rw [fun_lsize_eq hn] at hm; exact wf_shape.shape_case_0 _ _ _ (fun_lsize_lsize _) hd hm`. The rewrite turns `n * M = 128` into `lsize (lanetype_Fnn F) * M = 128`, which is definitionally `lsize (lanetype_Inn v_Inn) * M = 128`.
- Result lanes: the three `wf_lane_.lane__case_0` applications take the extra `_ (fun_lsize_lsize _)`.

#### `wf_ishape_inv` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* inversion of `ishape` well-formedness (spec `syntax ishape = shape -- if $lanetype(shape) = Jnn`). A well-formed integer shape is `Jnn X M` with `wf_shape (Jnn X M)` and `M ≤ 16`; the possible dims are `1 | 2 | 4 | 8 | 16`. `t_progress_be_vbitmask` uses it for `VBITMASK (Jnn X N)`. There `Step_pure/vbitmask` requires `$ibits_(32, ci)` to be the N lane bits `$ilt_($lsize(Jnn), S, ci_1, 0)*` padded with `0^(32-N)`, and `M ≤ 16` makes that list 32 bits long. `t_progress_be_vnarrow` uses it as well. The statement is unchanged.

**What broke and why.** The proof broke in both settings. `wf_shape.shape_case_0` (spec `shape = lanetype X dim -- if $lsize(lanetype) * dim = 128`) gained a size field `n` and the premise `fun_lsize lanetype n`, and its side condition became `n * dim = 128`. In the old pattern `shape_case_0 _ _ Hd _`, `Hd` now binds the size `n : ℕ`. So `wf_dim_le16 M Hd` is ill-typed ("Hd has type ℕ but is expected to have type wf_dim (dim.mk_dim M)").

**Original proof sketch.**
- `cases` on `wf_ishape` (`ishape_case_0 J sh' Hs Hlt`).
- Destruct `sh' = shape.X lt (dim.mk_dim M)`.
- `simp only [fun_lanetype] at Hlt` gives `lt = lanetype_Jnn J`; substitute and return `⟨J, M, rfl, Hs, _⟩`.
- For `M ≤ 16`, `cases Hs` gives `Hd : wf_dim (dim.mk_dim M)`, and `wf_dim_le16` concludes.

**Current proof sketch.** The proof is identical; only the pattern binds the two new fields: `shape_case_0 _ _ _ _ Hd _`. The `fun_lsize` premise is not used.

### 7.7 Q3, `TypeProgress`: vector progress cases A (8 constructs)

#### `t_progress_be_vvunop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* progress for `v128.not` (`VVUNOP V128 NOT`; rule Instr_ok/vvunop, `C ⊢ v128.not : [v128] → [v128]`). In a valid configuration S; F whose values vcs have the input types [v128], `vcs v128.not` steps; this is the `Instr_ok.vvunop` minor premise of the `Instrs_ok.rec` induction (motive `t_progress_be_P`) behind `t_progress_be`. The statement is unchanged.

**What broke and why.** The same two errors appear with and without the function views. First, `Unknown identifier vvunop_` in the witness `v128.const (vvunop_ V128 op c1)`. Second, an application type mismatch in `Step_pure.vvunop c1 v_vvunop _ rfl`: `rfl` is passed where a `vec_` is expected.

The cause is a model change. The spec's `$vvunop_(V128, NOT, v128) = $inot_($size(V128), v128)` calls the partial `$size` (`Option.get! (size V128)` in Lean). So it became the relation `fun_vvunop_ : vectype → vvunop → vec_ → vec_ → Prop`. Its only constructor is `fun_vvunop__case_0 v128 : size V128 ≠ none → fun_vvunop_ V128 NOT v128 (inot_ (Option.get! (size V128)) v128)`.

`Step_pure.vvunop` gained an explicit output `var_0` and the premise `fun_vvunop_ V128 op c_1 var_0`, and its premise `c = vvunop_ V128 op c_1` became `c = var_0`. HelperLemmas has no function view of `vvunop_`.

**Original proof sketch.**
- The proof unfolds `t_progress_be_P`, introduces S, F, vcs and the hypotheses, and takes the "steps" disjunct (`right`).
- `Htf` gives ts1 = [v128]. With `Hts : map typeof vcs = ts1`, `simp` refutes vcs = [] and |vcs| ≥ 2.
- For vcs = [v1], the canonical-forms lemma `invert_typeof_V128` gives v1 = `v128.const c1`. It needs `wf_val v1`, which comes from `HWfVals`.
- The witness is S' = S, F' = F, es' = [v128.const (vvunop_ V128 op c1)]. The step is `Step.pure` with `Step_pure.vvunop c1 op _ rfl`. This is spec rule Step_pure/vvunop: `(v128.const c_1) v128.not ~> (v128.const c)` if `c = $vvunop_(V128, NOT, c_1)`.

**Current proof sketch.** The proof is the same up to the canonical form. What is new is that the result vector comes from the relation.
- `∃ c, fun_vvunop_ V128 op c1 c` is proved by `cases v_vvunop` (only `NOT`) and `fun_vvunop__case_0 c1 (by simp [size])`. The side condition `size V128 ≠ none` holds because `size V128 = some 128`.
- The witness is es' = [v128.const c]. The step is `Step.pure _ _ _ (Step_pure.vvunop c1 op _ _ Hc rfl)`: the output is `var_0 := c`, the relation premise is `Hc`, and `c = var_0` holds by `rfl`.

#### `t_progress_be_vvbinop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* progress for `v128.and`, `v128.andnot`, `v128.or` and `v128.xor` (`VVBINOP V128 op`; `C ⊢ … : [v128 v128] → [v128]`). In a valid configuration whose values vcs have types [v128 v128], `vcs vvbinop` steps; this is case `Instr_ok.vvbinop` of `t_progress_be`. The statement is unchanged.

**What broke and why.** The same two errors appear in both settings. First, `Unknown identifier vvbinop_`. Second, `rfl` is passed where a `vec_` is expected in `Step_pure.vvbinop c1 c2 v_vvbinop _ rfl`.

The spec's `$vvbinop_` is `$iand_`, `$iandnot_`, `$ior_` or `$ixor_` applied to `$size(V128)`, so it uses the partial `$size`. It became the relation `fun_vvbinop_`, with constructors `fun_vvbinop__case_0..3` for AND, ANDNOT, OR and XOR. Each constructor has the side condition `size V128 ≠ none`. `Step_pure.vvbinop` gained the output `var_0`, the premise `fun_vvbinop_ V128 op c_1 c_2 var_0`, and `c = var_0`.

**Original proof sketch.** The proof is the same as for `v128.not`, with ts1 = [v128, v128].
- vcs = [v1, v2], and `simp` refutes the other lengths. `invert_typeof_V128` gives the two canonical forms `v128.const c1` and `v128.const c2`.
- The witness is S, F, [v128.const (vvbinop_ V128 op c1 c2)]. The step is `Step.pure` with `Step_pure.vvbinop c1 c2 op _ rfl` (spec Step_pure/vvbinop).

**Current proof sketch.**
- New: `∃ c, fun_vvbinop_ V128 op c1 c2 c` is proved by `cases v_vvbinop` and then, for each operator, `fun_vvbinop__case_k c1 c2 (by simp [size])` with k = 0..3.
- The witness is [v128.const c], and the step is `Step_pure.vvbinop c1 c2 op _ _ Hc rfl`. The rest is unchanged.

#### `t_progress_be_vvternop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* progress for `v128.bitselect` (`VVTERNOP V128 BITSELECT`; `C ⊢ v128.bitselect : [v128 v128 v128] → [v128]`). In a valid configuration whose values vcs have types [v128 v128 v128], `vcs v128.bitselect` steps; this is case `Instr_ok.vvternop` of `t_progress_be`. The statement is unchanged.

**What broke and why.** The same two errors appear in both settings. First, `Unknown identifier vvternop_`. Second, `rfl` is passed where a `vec_` is expected in `Step_pure.vvternop c1 c2 c3 v_vvternop _ rfl`.

The spec's `$vvternop_(V128, BITSELECT, …) = $ibitselect_($size(V128), …)` uses the partial `$size`. It became the relation `fun_vvternop_`, whose one constructor `fun_vvternop__case_0` has the premise `size V128 ≠ none`. `Step_pure.vvternop` gained `var_0`, the premise `fun_vvternop_ V128 op c_1 c_2 c_3 var_0`, and `c = var_0`.

**Original proof sketch.**
- vcs = [v1, v2, v3], and `simp` refutes the other lengths. `invert_typeof_V128` gives three canonical forms, `v128.const c1`, `v128.const c2` and `v128.const c3`.
- The witness is S, F, [v128.const (vvternop_ V128 op c1 c2 c3)]. The step is `Step.pure` with `Step_pure.vvternop c1 c2 c3 op _ rfl` (spec Step_pure/vvternop).

**Current proof sketch.**
- New: `∃ c, fun_vvternop_ V128 op c1 c2 c3 c` is proved by `cases v_vvternop` (only `BITSELECT`) and `fun_vvternop__case_0 c1 c2 c3 (by simp [size])`.
- The witness is [v128.const c], and the step is `Step_pure.vvternop c1 c2 c3 op _ _ Hc rfl`. The rest is unchanged.

#### `t_progress_be_vshiftop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* progress for the lane-wise shifts `sh.shl` and `sh.shr_sx` (`VSHIFTOP sh op`, where sh = Jnn X M is an integer shape such as `i32x4`; rule Instr_ok/vshiftop, `C ⊢ … : [v128 i32] → [v128]`). In a valid configuration whose values vcs have types [v128 i32], `vcs vshiftop` steps; this is case `Instr_ok.vshiftop` of `t_progress_be`. The statement is unchanged.

**What broke and why.**
- *Without the function views:* `Unknown identifier lsize` appears once, in the auxiliary `Hlx` (`wf_uN (lsize (lanetype_Jnn J)) x`). `Unknown identifier lsizenn` appears eight times, in the result lanes (`ishl_ (lsizenn …) … (k % lsizenn …)`, `ishr_` for SHR), both in the witness and in the rule's output-list argument. The eight constructor errors described next also appear (17 errors in all). The old model's functions `lsize` and `lsizenn` (spec `$lsize` and `$lsizenn`) became the relations `fun_lsize` and `fun_lsizenn`. `lsize` became a relation because `$lsize(numtype) = $size(numtype)` uses the partial `$size`. `lsizenn` (`$lsizenn(lt) = $lsize(lt)`) followed, as `fun_lsizenn_case_0 : fun_lsize lt n → fun_lsizenn lt n`.
- *With the function views:* HelperLemmas restores `lsize` and `lsizenn`, so only the eight constructor applications of the per-lane relation `fun_vshiftop_` fail. The error is an application type mismatch in `fun_vshiftop__case_k M x k M rfl`: `rfl` is given where `N` is expected.

  Each of `fun_vshiftop__case_0..7` (SHL, then SHR sx, for I32, I64, I8 and I16) gained an explicit argument `var_0 : N` and a first premise `fun_lsizenn (lanetype_Jnn J) var_0`. Its output now uses `var_0` in place of `lsizenn (lanetype_Jnn J)`, matching the spec's `$vshiftop_(Jnn X M, SHL, lane, n) = $ishl_($lsizenn(Jnn), lane, $(n \ $lsizenn(Jnn)))`. The rule `Step_pure.vshiftop` itself is identical in both models.

**Original proof sketch.**
- The proof takes `right`, so ts1 = [v128, i32] and vcs = [v1, v2]. `invert_typeof_V128` gives v1 = `v128.const c1` with c1 a 128-bit value (`Hwf1`). `invert_typeof_I32_wf` gives v2 = `i32.const k` with `wf_uN 32 k` (`Hwfk`).
- `wf_instr (VSHIFTOP sh op)` gives `wf_ishape sh` and `wf_vshiftop_ sh op`. Inverting the latter gives sh = J X M and op = `mk_vshiftop__0 J M o`, which the proof substitutes. Then `wf_shape (J X M)` follows from `wf_ishape`.
- The model axiom `lanes__is_wf` says that every lane of `lanes_(J X M, c1)` is a well-formed lane (`Hl`). With `wf_lane_Jnn_inv` and `wf_lane_Jnn_some`, each lane is `mk_lane__0 J x` with x ∈ iN(lsize J) (`Hlx`).
- The proof cases on o (SHL or SHR sx). The witness is S, F, [v128.const c] with c = `inv_lanes_(J X M, map (λ l, mk_lane__0 J (ishl_ N (proj l) (k mod N))) lanes)`, where N = `lsizenn (lanetype_Jnn J)`. For SHR it uses `ishr_ N sx` instead.
- The step uses `Step_pure.vshiftop c1 k J M _ _ lanes (map (λ l, some …) lanes)`. This is spec Step_pure/vshiftop: `c'* = $lanes_(J X M, c_1)` and `c = $inv_lanes_(J X M, $vshiftop_(J X M, op, c', n)*)`.
- The rule's premises, in order: equal lengths (`simp`); `Forall₂ fun_vshiftop_` via `Forall2_map_l`, where each lane uses `Hlx`, then `cases J`, then `fun_vshiftop__case_{0..3}` (SHL) or `fun_vshiftop__case_{4..7}` (SHR), with `rfl` for `M = M_0`; `c'* = lanes` (`rfl`); all outputs are `some` (`Option.some_ne_none`); the result equation (`simp only [Map, List.map_map]; rfl`); and finally `Hl`, `Hwsh`, `Hwish` and `Hwfk`.

**Current proof sketch.** The proof is unchanged except for the eight constructor applications, which are now `fun_vshiftop__case_j M x k M _ (fun_lsizenn_lsizenn _) rfl` (`M v_sx x k M …` for SHR).
- The new lane-width argument `var_0` (the spec's `$lsizenn(Jnn)`) is left as `_`. Unification instantiates it with the HelperLemmas function view `lsizenn (lanetype_Jnn J)`, which is what the goal's output lanes are written with.
- The new premise `fun_lsizenn (lanetype_Jnn J) var_0` is HelperLemmas' `fun_lsizenn_lsizenn`: the relation holds of the function view.
- `lsize` in `Hlx` and `lsizenn` in the witness now refer to the HelperLemmas function views, which have the old model's definitions.

#### `t_progress_be_vbitmask` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* progress for `sh.bitmask` (`VBITMASK sh`, where sh is an integer shape such as `i8x16`; rule Instr_ok/vbitmask, `C ⊢ sh.bitmask : [v128] → [i32]`). In a valid configuration, `v128.const c; sh.bitmask` steps; this is case `Instr_ok.vbitmask` of `t_progress_be`. The statement is unchanged.

**What broke and why.**
- *Without the function views:* `Unknown identifier lsize` appears twice: once in `Hz0 : wf_uN (lsize (lanetype_Jnn J)) 0`, and once in the relation `fun_ilt_ (lsize (lanetype_Jnn J)) S …` that is given to `Forall_exists_Forall2`. The error below also appears.
- *With the function views:* only one error remains, in `Step_pure.vbitmask c1 J M (inv_ibits_ 32 bits) lanes vs`: `vs : List uN` is given where `N` is expected.

  The rule `Step_pure.vbitmask` gained an explicit argument `var_1 : N`, placed before `var_0_lst`, and a first premise `fun_lsize (lanetype_Jnn J) var_1`. Its comparison premise is now `Forall₂ (λ v l, fun_ilt_ var_1 S (proj l) 0 v) var_0_lst ci_1*`, where it used to be `fun_ilt_ (lsize (lanetype_Jnn J)) …`. So the spec's `$lsize(Jnn)` in `$ibits_(32, ci) = $ilt_($lsize(Jnn), S, ci_1, 0)* (0)^(32-N)` is now a relation witness.

**Original proof sketch.**
- The proof takes `right`, so vcs = [v1]. `invert_typeof_V128` gives v1 = `v128.const c1` with c1 ∈ iN(128).
- `wf_ishape sh` comes from `wf_instr`. `wf_ishape_inv` then gives sh = J X M, `wf_shape (J X M)` and M ≤ 16.
- `lanes_Jnn_form` says that every lane of `lanes_(J X M, c1)` is `mk_lane__0 J x` with x ∈ iN(lsize J) (`jlane`).
- The per-lane sign tests come from `Forall_exists_Forall2`, with the relation `fun_ilt_ (lsize J) S (proj l) 0 v` and the property `wf_bit (mk_bit v)`. For each lane, `icmp_total_bit` gives an `ilt_` result that is a 1-bit integer, and `bit_of_wf1` makes it a well-formed bit. This yields vs, which is the spec's `$ilt_($lsize(Jnn), S, ci_1, 0)*` (the lane signs). It also yields the `Forall₂` `H2`, |vs| = |lanes| (`Hsvs`), and the bit facts `Hb`.
- bits := (vs as bits) ++ 0^(32−M). All of these bits are well-formed (`Hbw`). The length of bits is 32 (`Hbl`), by `omega` from |lanes| = M (the project axiom `lanes_len`) and M ≤ 16.
- The witness is S, F, [i32.const (irev_ 32 ci)] with ci = `inv_ibits_ 32 bits`.
- The step uses `Step_pure.vbitmask c1 J M ci lanes vs`. Its premises: |vs| = |lanes| (`Hsvs`); every lane projects (`jlane_some`); `H2`; `ci_1* = lanes` (`rfl`); `$ibits_(32, ci) = bits`, from the project axiom `ibits_inv` (ibits_ ∘ inv_ibits_ = id on 32 well-formed bits) and the definition of bits; `wf_uN 32 ci`, from the model axiom `inv_ibits__is_wf`; and `Hwsh`, `Hb` and `wf_bit 0`.

**Current proof sketch.** The proof is unchanged except for the rule application, which is now `Step_pure.vbitmask c1 J M (inv_ibits_ 32 bits) lanes (lsize (lanetype_Jnn J)) vs (fun_lsize_lsize _) Hsvs …`.
- The new lane-width argument `var_1` is the function view `lsize (lanetype_Jnn J)`, and its premise `fun_lsize (lanetype_Jnn J) var_1` is HelperLemmas' `fun_lsize_lsize`.
- With this choice of `var_1`, the existing `H2` (built with `fun_ilt_ (lsize (lanetype_Jnn J))`) is exactly the new premise `Forall₂ (… fun_ilt_ var_1 …)`.

#### `t_progress_be_vswizzle` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* progress for `i8x16.swizzle` (`VSWIZZLE sh`; rule Instr_ok/vswizzle, `C ⊢ … : [v128 v128] → [v128]`, where `wf_instr` forces sh = `I8 X 16`). In a valid configuration, `v128.const c1; v128.const c2; i8x16.swizzle` steps; this is case `Instr_ok.vswizzle` of `t_progress_be`. The statement is unchanged.

**What broke and why.**
- *With the function views:* there are five errors.
  1. An application type mismatch in `wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 …) rfl`: `wf_dim (dim.mk_dim 16)` is given where `ℕ` is expected. The `wf_shape` constructor gained an explicit lane-width argument `var_0` and a premise `fun_lsize lt var_0`, and its size condition is now `var_0 * dim = 128`. This is because the spec's `$lsize` is now the relation `fun_lsize`.
  2. A `rewrite` failure: `cs.length` is not found in `proj_lane__0 (mk_lane__0 I8 x) ≠ none`.
  3. A `rewrite` failure: `(lanes c2)[k]!` is not found in `k < |lanes c2|`.
  4. A `rewrite` failure: the `lanes_len` pattern `|lanes_ …|` is not found in `proj(ci*[k]) < |cs|`.
  5. A type mismatch at `refine wf_lane_.lane__case_0 _ _ _ ?_ ?_` in the last bullet: `wf_lane_.lane__case_0` gained the same pair `var_0` / `fun_lsize (lanetype_Jnn J) var_0`.

  Errors 2, 3 and 4 have one cause: the three per-index `Forall` premises of `Step_pure.vswizzle` were reordered. These are the side conditions of the spec's `c'*[ci*[k]]` (two index bounds and the lane projection). The old order was `proj(ci*[k]) < |c'*|`, `proj_lane__0 (ci*[k]) ≠ none`, `k < |ci*|`. The new order is `proj_lane__0 (ci*[k]) ≠ none`, `k < |ci*|`, `proj(ci*[k]) < |c'*|`, so the inner bound `k < |ci*|` now comes before the outer bound. As a result, each old bullet landed on the wrong goal.
- *Without the function views:* the same five errors appear, plus a type mismatch at `HL2 …` in `Hidx`. `jlane` is a MAIN-group definition that mentions `lsize`. Its body fails to elaborate (`Unknown identifier lsize`), so `jlane Jnn.I8 l` no longer unfolds to `∃ x, … ∧ wf_uN 8 x`.

**Original proof sketch.**
- The proof takes `right`, so vcs = [v1, v2]. `invert_typeof_V128`, used twice, gives `v128.const c1` and `v128.const c2`, both 128-bit.
- `wf_instr` gives sh = I8 X 16, which the proof substitutes. `wf_shape (I8 X 16)` is built directly: `wf_dim` holds for 16, and 8·16 = 128 by `rfl`.
- `lanes_Jnn_form` says that all lanes of c1 and of c2 are i8 lanes (`HL1`, `HL2`).
- cs := (projected lanes of c1) ++ 0^240. This is the spec's `c'* = $lanes_(I8 X 16, c_1) 0^(256-M)`. Every element is in iN(8) (`jlane_proj_wf`, `Hcsw`), and |cs| = 256 (`lanes_len`, `Hcsl`).
- `Hidx`: for k < 16, `(lanes c2)[k]!` = `mk_lane__0 I8 x` with x ∈ iN(8), by `getElem!_pos`, `lanes_len` and `HL2`. `Hx256`: if x ∈ iN(8), then x < 256.
- The step uses `Step_pure.vswizzle c1 c2 I8 16 _ (lanes c2) cs 0`, with c = `$inv_lanes_(I8 X 16, c'*[ci*[k]]^(k<16))`. Its premises: `ci* = lanes c2` (`rfl`); all lanes of c1 project (`jlane_some`); `Hcs`; then, in the old order, the selector bound `ci*[k] < |c'*|` (`Hidx`, `Hcsl`, `Hx256`), `proj_lane__0 (ci*[k]) ≠ none` (`Hidx`, `simp`) and `k < |ci*|` (`lanes_len`); the result equation (`rfl`); `Hwsh`; `wf_uN 8 0`.
- The last premise says each selected lane `mk_lane__0 I8 (cs[ci*[k]]!)` is well-formed. It is proved by `wf_lane_.lane__case_0 _ _ _ ?_ ?_`, with `wf_uN 8 (cs[j]!)` from `getElem!_pos` and `Hcsw`, and the lane-type equation by `rfl`.

**Current proof sketch.** The structure is the same, with three local changes.
1. `Hwsh := wf_shape.shape_case_0 _ _ _ (fun_lsize_lsize _) (wf_dim.dim_case_0 _ (Or.inr rfl)) rfl`. The lane width is the function view `lsize I8`, which equals `psize I8` = 8. Its `fun_lsize` premise comes from `fun_lsize_lsize`, and `8 * 16 = 128` still holds by `rfl`.
2. The three per-index bullets are reordered to the new premise order: `proj_lane__0 (ci*[k]) ≠ none`, then `k < |ci*|`, then `ci*[k] < |c'*|`. The bodies of the bullets are unchanged.
3. The final lane well-formedness uses `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) ?_ ?_`. The `show wf_uN 8 (cs[…]!)` still applies, because `lsize (lanetype_Jnn I8)` reduces to 8.

#### `t_progress_be_vshuffle` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* progress for `i8x16.shuffle i*` (`VSHUFFLE sh i*`; rule Instr_ok/vshuffle, `C ⊢ … : [v128 v128] → [v128]` if `(i < 2·$dim(sh))*`). In a valid configuration, `v128.const c1; v128.const c2; i8x16.shuffle i*` steps; this is case `Instr_ok.vshuffle` of `t_progress_be`. The statement is unchanged.

**What broke and why.** The same five errors appear in both settings.
1. The arity error of `wf_shape.shape_case_0`, as in `t_progress_be_vswizzle`: the constructor gained the lane width `var_0` and a premise `fun_lsize lt var_0`.
2. A `rewrite` failure: `cs.length` is not found in `k < |i*|`.
3. A `rewrite` failure: `i_lst.length` is not found in `proj(i*[k]!) < |cs|`.
4. A type mismatch at the first `refine wf_lane_.lane__case_0 _ _ _ ?_ ?_` (the lanes of cs): the constructor gained `var_0` and its `fun_lsize` premise.
5. The same type mismatch at the second one (the selected lanes).

Errors 2 and 3 occur because the two bound premises of `Step_pure.vshuffle` (the bounds for the spec's `c'*[i*[k]]`) swapped places. The old order was `i*[k] < |c'*|`, then `k < |i*|`. The new order is `k < |i*|`, then `i*[k] < |c'*|`.

**Original proof sketch.**
- The proof takes `right`, so vcs = [v1, v2], with canonical forms c1 and c2.
- `wf_instr` gives sh = I8 X 16 and |i*| = 16. `wf_shape (I8 X 16)` is built directly.
- `lanes_Jnn_form` is applied to c1 and to c2, and the results are combined for `lanes c1 ++ lanes c2` (`HL`).
- cs := the projections of `lanes c1 ++ lanes c2`. This is the spec's `c'* = $lanes_(I8 X 16, c_1) ++ $lanes_(I8 X 16, c_2)`. All elements are in iN(8) (`jlane_proj_wf`), and |cs| = 32 (`lanes_len`, twice).
- `Hi32`: for k < 16, `i*[k]! < 32`. This follows from the validation premise `Hilt : (i < 2·dim(sh))*` (2·16 = 32) and |i*| = 16, via `getElem!_pos`.
- The step uses `Step_pure.vshuffle c1 c2 I8 16 i* _ cs 0`, with c = `$inv_lanes_(I8 X 16, c'*[i*[k]]^(k<16))`. Its premises: `map mk_lane__0 cs = lanes c1 ++ lanes c2` (`jlane_map_proj`); then, in the old order, `i*[k] < |cs|` (`Hcsl`, `Hi32`) and `k < |i*|` (`Hlen`); the result equation (`rfl`); every `mk_lane__0 I8 c'` with c' ∈ cs is well-formed (`wf_lane_.lane__case_0 _ _ _ ?_ ?_`, `Hcsw`, `rfl`); `Hwsh`; and each selected lane `mk_lane__0 I8 (cs[i*[k]]!)` is well-formed (`getElem!_pos`, `Hcsw`).

**Current proof sketch.** The proof is the same, with three changes.
- `Hwsh` is built with the extra lane width `lsize I8` and `fun_lsize_lsize _`.
- The two bound bullets are swapped: `k < |i*|` (from |i*| = 16) now comes first, then `i*[k] < |cs|` (from `Hi32` and `Hcsl`).
- Both lane-well-formedness bullets use `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) ?_ ?_`.

No new facts are needed: both bounds were already proved in the old proof.

#### `t_progress_be_vextract_lane` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* progress for `sh.extract_lane_sx? i` (`VEXTRACT_LANE sh sx? i`, for example `f32x4.extract_lane 2` or `i8x16.extract_lane_s 5`; rule Instr_ok/vextract_lane, `C ⊢ … : [v128] → [$shunpack(sh)]` if `i < $dim(sh)`). In a valid configuration, `v128.const c1; sh.extract_lane_sx? i` steps; this is case `Instr_ok.vextract_lane` of `t_progress_be`. The statement is unchanged.

**What broke and why.** The same six errors appear in both settings, one in each branch that builds a step.
- In the four numeric-lane branches (I32, I64, F32, F64), a type mismatch: the proof's `unpacknum_ … ≠ none` argument now sits where `proj_uN_0 i < |lanes_(nt X M, c_1)|` is expected.
- In the two packed-lane branches (I8, I16), an application type mismatch: `wf_lane_Jnn_some …` (a proof of `proj_lane__0 (lane i) ≠ none`) now sits where the same bound is expected.

`Step_pure.vextract_lane_num` and `Step_pure.vextract_lane_pack` have the same premises as before. The premises were only reordered, so that the lane-index bound comes before the premise that reads lane i (the spec's `$lanes_(sh, c_1)[i]`).
- `vextract_lane_num` now starts with the bound. The old order was `unpacknum_ ≠ none`, then the bound.
- `vextract_lane_pack` now has `proj_num__0 c_2 ≠ none`, then the bound, then `proj_lane__0 (lane i) ≠ none`. The old order was `proj_num__0`, then `proj_lane__0`, then the bound.

**Original proof sketch.**
- The proof takes `right`, so vcs = [v1]. `invert_typeof_V128` gives v1 = `v128.const c1`.
- With sh = lt X M, `wf_instr` gives `wf_shape (lt X M)` and the side condition `Hiff`: lt ∈ {i32, i64, f32, f64} ⇔ sx? = none. The typing premise gives `i < M`.
- `lanes_nth_wf` gives `wf_lane_ lt (lanes_(lt X M, c1)[i]!)` (`Hl`). `Hlen : i < |lanes|` comes from `lanes_len`.
- The proof cases on sx? × lt, which gives 12 cases.
  - sx? = none, lt = i32 or i64: `wf_lane_Jnn_inv` gives the lane `mk_lane__0 J x`. The witness is `i32.const x` or `i64.const x`. The step uses `Step_pure.vextract_lane_num c1 nt M i _` with, in this order, `unpacknum_ … ≠ none`, `Hlen`, `c_2 = Option.get! (unpacknum_ …)` and `Hwsh`. The first and third are proved by rewriting the lane and `simp [unpacknum_]`. This is spec Step_pure/vextract_lane-num: `c_2 = $unpacknum_(nt, $lanes_(nt X N, c_1)[i])`.
  - sx? = none, lt = f32 or f64: the same, with `wf_lane_Fnn_inv` (`mk_lane__1 F x`). The witness is `f32.const x` or `f64.const x`.
  - sx? = none with i8 or i16, and sx? = some with a numeric lane type: these contradict `Hiff` (`decide`, `simp`).
  - sx? = some sx, lt = i8 or i16: `wf_lane_Jnn_inv` gives x ∈ iN(8) or x ∈ iN(16). The witness is `i32.const (extend__ 8 32 sx x)` or `i32.const (extend__ 16 32 sx x)`. This is spec Step_pure/vextract_lane-pack: `c_2 = $extend__($psize(pt), 32, sx, $lanes_(pt X N, c_1)[i])`. The step uses `Step_pure.vextract_lane_pack`, with `proj_num__0 c_2 ≠ none` (`simp`), `wf_lane_Jnn_some`, `Hlen`, the extend equation (rewriting and `simp`), `wf_num_ I32 c_2` (from the model axiom `extend___is_wf`) and `Hwsh`.

**Current proof sketch.** The proof is identical; only argument positions moved.
- In the four `vextract_lane_num` applications, `Hlen` now comes first, before `unpacknum_ … ≠ none`.
- In the two `vextract_lane_pack` applications, `Hlen` now comes second: after `proj_num__0 c_2 ≠ none` and before `wf_lane_Jnn_some …`.

No new witness is needed. The old proof already derived the bound `i < |lanes|` from the validation premise `i < dim(sh)` and `lanes_len`.

### 7.8 Q4, `TypeProgress`: vector progress cases B and `vcvtop` (9 constructs)

#### `t_progress_be_vextunop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* the progress case for `VEXTUNOP sh_1 sh_2 vextunop`, i.e. `i16x8.extadd_pairwise_i8x16_sx` and `i32x4.extadd_pairwise_i16x8_sx` (`Instr_ok.vextunop`, type `[v128] → [v128]`). It is stated through the motive `t_progress_be_P`: take a store S, a frame F and well-formed operand values vcs whose types are the instruction's input types, with `wf_config (S; F; vcs VEXTUNOP …)`, C = C' extended with F's locals, labels and return, `Moduleinst_ok S F.module C'` and `Store_ok S`, and the instruction is not a `br`/`return`. Then the instruction sequence is a constant or the configuration takes a step.

**What broke and why.** The proof broke: the cascade replaced it with `sorry` both with and without the function views. The statement did not change. The cause is in the model. `$lsize` used to be `def lsize`. Its `numtype` clauses apply `!` to the partial `$size`, so it is now the relation `fun_lsize lt n`. `$lsizenn1` and `$lsizenn2` are defined from it, so they became `fun_lsizenn1` and `fun_lsizenn2`. Every use now takes a fresh size variable and a relation premise.
- Without the views, the first errors are `unknown identifier lsize` (in `have H128 : lsize (lanetype_Jnn J1) * M1 = 128`), the failing `assumption` of that `have`, and `unknown identifier lsizenn1` (in the definition of the extended lane list `E`).
- With the views, three constructor shapes no longer match:
  1. `wf_shape.shape_case_0` encodes the `shape` side condition `$lsize(lanetype)·dim = 128`. It now binds `var_0` with the premise `fun_lsize L var_0` and states `var_0 * M = 128`. As a result, `cases Hs1; assumption` finds no hypothesis `lsize J1 * M1 = 128`.
  2. `wf_lane_.lane__case_0` now takes `var_0 : N` and `fun_lsize (lanetype_Jnn J) var_0` before `wf_uN var_0 x`. The `iadd__is_wf …` proof therefore lands where `var_0 : N` is expected.
  3. `fun_vextunop___case_3/_14` are the generated rules of `$vextunop__` for I16→I32 and I8→I16. They gained `var_1 var_0` with the premises `fun_lsizenn2 (Jnn_2) var_1` and `fun_lsizenn1 (Jnn_1) var_0`, and they use `extend__ var_0 var_1 sx` and `iadd_ var_1` where they used `lsizenn1`/`lsizenn2`. The old argument list now puts `rfl` where `var_1 : N` is expected.

  In the same way, `wf_vextunop__Jnn_1_M_1_Jnn_2_M_2` encodes the side condition `16 ≤ 2·$lsizenn1(Jnn_1) = $lsizenn2(Jnn_2) ≤ 32`. It gained `var_1 var_0` and two relation premises, so `obtain ⟨sx, Hsz⟩ := Ho` no longer extracts the size condition (`Hsz` is the Nat `var_1`; the `exact absurd Hsz …` alternative then fails inside `first`, which reports only its last alternative's error).

**Original proof sketch.**
- The proof takes the right disjunct, because `VEXTUNOP` is not a constant. `Htf`/`Hts` force exactly one v128 operand: an empty list, or two or more values, contradict `map typeof vcs = [V128]`. Then `invert_typeof_V128` turns `v1` into `v128.const c1` with c1 a 128-bit value.
- `wf_instr` carries the syntax side conditions. From it, `sh_2 = Jnn_1 X M_1` is the source shape and `sh_1 = Jnn_2 X M_2` the destination, and both are valid shapes (`Hs1`, `Hs2`). Also op = `EXTADD_PAIRWISE sx` with `Hsz : 16 ≤ 2·|J1| ∧ 2·|J1| = |J2| ∧ |J2| ≤ 32`. `H128 : lsize J1 * M1 = 128` comes from `Hs1`.
- The proof then computes `$vextunop__`:
  - The lanes `ci* = $lanes_(J1 X M1, c1)` are in-range integer lanes (`lanes_Jnn_form`, `jlane`).
  - The extended lanes `E = $extend__(|J1|, |J2|, sx, ci)*` are |J2|-bit values (`extend___is_wf`).
  - E has even length (`shape_lanes_even` from `H128`). So `evens E`/`odds E` give `cj_1*`, `cj_2*` with `$concat_((cj_1 cj_2)*) = E` (`evens_odds_size`, `evens_odds_concat`).
  - The sums `$iadd_(|J2|, cj_1, cj_2)` are well-formed J2 lanes (`iadd__is_wf`, `wf_lane_.lane__case_0`, `Forall2_of_Forall`).
- It runs `cases J1 <;> cases J2`. `decide` on `Hsz` refutes the impossible pairs. I8→I16 is `fun_vextunop___case_14` and I16→I32 is `fun_vextunop___case_3`. Both get the facts above and the result `c = $inv_lanes_(J2 X M2, $iadd_(…)*)`.
- The step is `Step.pure` with `Step_pure.vextunop`, i.e. rule Step_pure/vextunop: `(v128.const c_1) (VEXTUNOP sh_2 sh_1 vextunop) ~> (v128.const c)` if `$vextunop__(sh_1, sh_2, vextunop, c_1) = c`. (The rule's `sh_1` is the source shape, i.e. this theorem's `sh_2`.)

**Current proof sketch.** The argument and the step rule are the same as before. Only the size bookkeeping changed:
- `H128` now comes from `cases Hs1 with | shape_case_0 _ _ n hn _ h => rw [← fun_lsize_eq hn]; exact h`. The wf_shape witness `hn : fun_lsize J1 n` gives `n = lsize J1`.
- `obtain ⟨sx, n1, n0, hn1, hn0, Hsz⟩ := Ho` is followed by `obtain rfl := fun_lsizenn2_eq hn1` and `obtain rfl := fun_lsizenn1_eq hn0`. These substitute `n1 := lsizenn2 J2` and `n0 := lsizenn1 J1`, which gives `Hsz` back its old form over the HelperLemmas views. The views are definitionally `lsize`, so `E`, the evens/odds split and the sums are built exactly as before.
- `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) …` supplies the new lane-width witness, with var_0 := `lsize J2`.
- `fun_vextunop___case_14/_3 … _ _ _ _ (fun_lsizenn2_lsizenn2 _) (fun_lsizenn1_lsizenn1 _) …` passes the two new explicit size arguments `var_1`, `var_0` as `_`. The witnesses fix `var_1 := lsizenn2 J2` and `var_0 := lsizenn1 J1`, so the rule's `extend__ var_0 var_1 sx` and `iadd_ var_1` premises are the unchanged facts `HEc` and `HW2` (the result equation is still `rfl`).

#### `t_progress_be_vextbinop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* the progress case for `VEXTBINOP sh_1 sh_2 vextbinop` (`Instr_ok.vextbinop`, type `[v128 v128] → [v128]`). `EXTMUL half sx` covers `i16x8/i32x4/i64x2.extmul_{low,high}_…_sx`, and `DOT S` covers `i32x4.dot_i16x8_s`. The claim is that `v128.const c_1; v128.const c_2; VEXTBINOP …` in a valid configuration steps. It uses the motive `t_progress_be_P`, as for `t_progress_be_vextunop`.

**What broke and why.** The proof broke (sorried in both settings). The model change is the one described for `t_progress_be_vextunop`.
- Without the views: `unknown identifier lsize` (in the statements of `H128` and of the local helper `Hext`) and `unknown identifier lsizenn1` (also in `Hext`).
- With the views:
  1. The inversion `| shape_case_0 _ _ _ h => exact h` now binds `h` to the new premise `fun_lsize (lanetype_Jnn J1) var_0` instead of `lsize J1 * M1 = 128`, which gives a type mismatch.
  2. `fun_vextbinop___case_3/_4/_14/_19` are the rules of `$vextbinop__` that the proof uses. They gained `var_1 : M` and `var_0 : N` with the premises `fun_lsizenn1 (Jnn_1) var_1` and `fun_lsizenn2 (Jnn_2) var_0`. Here the lsizenn1 premise comes first, the reverse of `fun_vextunop__`. The rules now use `extend__ var_1 var_0`, `imul_ var_0` and `iadd_ var_0`, so the old argument lists put `rfl` where `var_1 : M` is expected.
  3. `wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2` encodes the side conditions `2·$lsizenn1(Jnn_1) = $lsizenn2(Jnn_2) ≥ 16` (EXTMUL) and `= 32` (DOT). It gained `var_1 var_0` with the premises `fun_lsizenn2 (Jnn_2) var_1` and `fun_lsizenn1 (Jnn_1) var_0`, so the old `rcases Ho` patterns bind `Hsz` to the Nat `var_1` (the `try exact absurd Hsz …` then fails silently). `wf_lane_.lane__case_0` also gained its `fun_lsize` premise (used in `HW2`; see `t_progress_be_vextunop`). Neither change shows among the three recorded errors.

**Original proof sketch.**
- The proof takes the right disjunct. There are exactly two v128 operands, and `invert_typeof_V128` gives c1 and c2. From `wf_instr`: the source shape is `J1 X M1` and the destination `J2 X M2` (both valid), `Ho : wf_vextbinop__… J1 M1 J2 M2 o`, and `H128 : lsize J1 * M1 = 128`. The lanes of c1 and c2 are `jlane J1` (`lanes_Jnn_form`) and there are equally many of them (`lanes_size_eq`). `Hext` states that the extended lanes are |J2|-bit values.
- `rcases Ho` splits on the operator:
  - `EXTMUL half sx`: the half slices `$lanes_(J1 X M1, c_i)[$half(half, 0, M2) : M2]` keep `jlane` and equal length (`Forall_list_slice`, `list_slice_size_eq`). The lane products `$imul_(|J2|, $extend__(…, ci_1), $extend__(…, ci_2))` are well-formed (`zip_lane_wf2`, `imul__is_wf`, `extend___is_wf`). After `cases J1 <;> cases J2`, `decide` on `Hsz` refutes the impossible pairs. The rest are `fun_vextbinop___case_14` (I8→I16), `_3` (I16→I32) and `_4` (I32→I64).
  - `DOT S`: the products P (a `zipWith` over the two lane lists) are |J2|-bit values (`zip_wf`). P has even length (`size_zipWith_eq`, `shape_lanes_even`), and its evens/odds give `cj_1*` and `cj_2*` (`evens_odds_size`, `evens_odds_concat`). The sums `$iadd_(|J2|, cj_1, cj_2)` are well-formed lanes. Only I16→I32 survives `decide`, which is `fun_vextbinop___case_19`. Its concat premise comes from `HPc.trans HPdef` after `hMap2` rewrites `Map₂` to `zipWith`.
- The step is `Step.pure` with `Step_pure.vextbinop c1 c2 … c (some c) Hc` (rule Step_pure/vextbinop).

**Current proof sketch.** The structure and the step rule are the same. What changed:
- `H128` comes from `| shape_case_0 _ _ n hn _ h => rw [← fun_lsize_eq hn]; exact h`.
- The split is now `rcases Ho with ⟨hf, v_sx, n1, n0, hn1, hn0, Hsz⟩ | ⟨n1, n0, hn1, hn0, Hsz⟩`. In each branch, `obtain rfl := fun_lsizenn2_eq hn1` and `obtain rfl := fun_lsizenn1_eq hn0` restate `Hsz` over `lsizenn1 J1` and `lsizenn2 J2`. The slice, product and evens/odds facts are unchanged.
- Each of `fun_vextbinop___case_3/_4/_14/_19` gets two more `_` (var_1, var_0) and the witnesses `(fun_lsizenn1_lsizenn1 _) (fun_lsizenn2_lsizenn2 _)`. These fix `var_1 := lsizenn1 J1` and `var_0 := lsizenn2 J2`, so the rules' `imul_ var_0 (extend__ var_1 var_0 …)`/`iadd_ var_0` premises are the old `HW`, `HPc` and `HW2`.
- In `HW2`, the lane is built with `wf_lane_.lane__case_0 _ J2 _ _ (fun_lsize_lsize _) …`.

#### `t_progress_be_vnarrow` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* the progress case for `VNARROW sh_1 sh_2 sx`, i.e. `i8x16.narrow_i16x8_sx` and `i16x8.narrow_i32x4_sx` (`Instr_ok.vnarrow`, type `[v128 v128] → [v128]`). The claim is that `v128.const c_1; v128.const c_2; VNARROW …` in a valid configuration steps (motive `t_progress_be_P`).

**What broke and why.** The proof broke (sorried in both settings). The rule Step_pure/vnarrow says `cj_i* = $narrow__($lsize(Jnn_1), $lsize(Jnn_2), sx, ci_i)*`. Because `$lsize` became a relation, `Step_pure.vnarrow` has two new explicit arguments `var_1 : N` and `var_0 : M`, with the premises `fun_lsize (lanetype_Jnn Jnn_2) var_1` and `fun_lsize (lanetype_Jnn Jnn_1) var_0`. It uses `narrow__ var_0 var_1` where it used `narrow__ (lsize J1) (lsize J2)`. Separately, `wf_lane_.lane__case_0` gained `var_0` and a `fun_lsize` premise.
- Without the views: `unknown identifier lsize`, both in the statement of `Hnar` and in the explicit result vector.
- With the views: `lane__case_0 _ J2 _ (narrow___is_wf …)` passes a proof where `var_0 : N` is expected, and the old `Step_pure.vnarrow` argument list passes `rfl` where `var_1 : N` is expected.

**Original proof sketch.**
- The proof takes the right disjunct. There are two v128 operands, c1 and c2 (`invert_typeof_V128`). `wf_ishape_inv` on both shapes gives the destination `sh_1 = J2 X N2` and the source `sh_2 = J1 X N1`, both valid shapes. The lanes of c1 and c2 at `J1 X N1` are `jlane J1` (`lanes_Jnn_form`).
- `Hnar`: narrowing a list of `jlane J1` lanes with `narrow__ (lsize J1) (lsize J2) sx` gives well-formed J2 lanes (`narrow___is_wf`, `wf_lane_.lane__case_0`).
- The result is given explicitly: `c = $inv_lanes_(J2 X N2, cj_1* ++ cj_2*)`. The step is `Step.pure` with `Step_pure.vnarrow`. Its premises are:
  - `rfl` for the lanes, the narrow maps and `inv_lanes_`;
  - `jlane_some` (all lanes are integer lanes);
  - `lanes__is_wf` (the source lanes are well-formed);
  - `Hs1`, `Hs2` (the shapes);
  - `Hnar` (the result lanes are well-formed).

  There is no case split on lane types: `Step_pure.vnarrow` is a single rule, generic in `Jnn_1`/`Jnn_2`, with no size side condition to check.

**Current proof sketch.** The proof is unchanged except for two points:
- `Hnar` uses `wf_lane_.lane__case_0 _ J2 _ _ (fun_lsize_lsize _) (narrow___is_wf …) rfl`.
- The step is `Step_pure.vnarrow … _ _ _ _ (fun_lsize_lsize _) (fun_lsize_lsize _) …`. The two new premises are discharged by the function-view witnesses, which fix `var_1 := lsize J2` and `var_0 := lsize J1`. The rule's `cj_i = Map (narrow__ var_0 var_1 sx …)` premises therefore still hold by `rfl` against the explicit result, which is written with `lsize`.

#### `t_progress_be_vcvtop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* the progress case for `VCVTOP sh_1 sh_2 vcvtop` (`Instr_ok.vcvtop`, type `[v128] → [v128]`). This covers all SIMD conversions: `extend_{low,high}`, `convert`, `convert_low`, `trunc_sat`, `trunc_sat_…_zero`, `demote_…_zero` and `promote_low`. The claim is that `v128.const c_1; VCVTOP …` in a valid configuration steps (motive `t_progress_be_P`).

**What broke and why.** The proof broke (sorried in both settings).
- Without the views, the only recorded error is `unknown identifier vcvtop_full_lsize`. That helper's statement `lsize L1 = lsize L2` no longer elaborated, so the cascade deleted it (see the `vcvtop_full_lsize` entry below).
- With the views, `cases Hs2; assumption` and `cases Hs1; assumption` fail for `lsize L1 * M1 = 128` and `lsize L2 * M2 = 128`. `wf_shape.shape_case_0` now states `var_0 * M = 128` with a `fun_lsize L var_0` premise (see `t_progress_be_vextunop`).

The step rule `Step_pure.vcvtop` itself is unchanged.

**Original proof sketch.**
- The proof takes the right disjunct. There is one v128 operand, c1. From `wf_instr`: the destination is `sh_1 = L2 X M2`, the source is `sh_2 = L1 X M1`, both are valid shapes, and `Hop : wf_vcvtop__ sh_2 sh_1 op`.
- It splits on the three clauses of `$vcvtop__`, using `halfop_of op` and `zeroop_of op`. These are ported from Rocq, and `halfop_total`/`zeroop_total` relate them to the model's `fun_halfop` and `fun_zeroop`.
  - If `halfop = some h` (extend, convert_low, promote_low), it applies `vcvtop_step_half`.
  - Else, if `zeroop = some ZERO` (trunc_sat_zero, demote_zero), `vcvtop_zero_numtype` shows that both lane types are number types, and `vcvtop_step_zero` gives the step.
  - Otherwise (the full-width convert and trunc_sat), `vcvtop_full_lsize` gives `lsize L1 = lsize L2`. With `lsize L1 * M1 = 128 = lsize L2 * M2` from the shapes and `0 < lsize L2`, this gives `M1 = M2`, and `vcvtop_step_full` gives the step.
- Each helper returns a `Step_pure` for `(v128.const c_1) (VCVTOP (L2 X M2) (L1 X M1) op)`, i.e. this theorem's `VCVTOP sh_1 sh_2 op` (rule Step_pure/vcvtop), which is lifted with `Step.pure`.

**Current proof sketch.** The case analysis and the helpers are the same. Only `Hm1` and `Hm2` changed: they are now `cases Hs2 with | shape_case_0 _ _ n hn _ h => rw [← fun_lsize_eq hn]; exact h`, and likewise for `Hs1`. `vcvtop_step_half` and `vcvtop_step_full` compile unchanged. `vcvtop_zero_numtype`, `vcvtop_step_zero` and `vcvtop_full_lsize` keep their statements and were re-proved (entries below).

#### `vcvtop_lane_total` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* take a valid conversion operator `vcvtop__(sh_1, sh_2)` (`wf_vcvtop__ sh_1 sh_2 op`) and a well-formed lane ci of `sh_1`'s lane type. Then the per-lane conversion `$lcvtop__(sh_1, sh_2, vcvtop, ci)` is defined (`fun_lcvtop__ … ci (some r)`) and its result list r is non-empty. `vcvtop_lanes_total` uses it, and through that lemma all three `vcvtop_step_*` lemmas do.

**What broke and why.** The proof broke (sorried in both settings, with the same errors in each):
1. `wf_lane_.lane__case_0/_1` gained `var_0` and a premise `fun_lsize (lanetype_Jnn J) var_0` (case 0) or `fun_sizenn (numtype_Fnn F) var_0` (case 1). The inversions `| lane__case_0 J c _ Heq` (and `lane__case_1`) now bind `Heq` to that premise instead of the lane-type equation, so `inj _ _ Heq` and `absurd Heq (hJF _ _)` are ill-typed.
2. The side-condition relations of the four `vcvtop__` families gained `var_1 var_0`, premises from `fun_lsizenn1`, `fun_lsizenn2`, `fun_sizenn1` and `fun_sizenn2`, and conditions stated over the variables (for example, the spec's `$lsizenn2(Jnn_2) = 2·$lsizenn1(Jnn_1)`). The four relations are `wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2`, `…_Jnn_1_M_1_Fnn_2_M_2`, `…_Fnn_1_M_1_Inn_2_M_2` and `…_Fnn_1_M_1_Fnn_2_M_2`. The old patterns (`… _ _ hs` for EXTEND, CONVERT and TRUNC_SAT, `… _ hs` for DEMOTE, `… hs` for PROMOTE_LOW) now bind `hs` to the Nat `var_1`.
3. Each rule `fun_lcvtop___case_N` gained `var_1 var_0` with the premises `fun_lsizenn2 (dest) var_1` and `fun_lsizenn1 (source) var_0`. This follows the spec's use of sizes, for example `$extend__($lsizenn1(Jnn_1), $lsizenn2(Jnn_2), sx, iN_1)`.

**Original proof sketch.**
- Local facts:
  - `lanetype_Jnn` and `lanetype_Fnn` are injective and disjoint.
  - `lJ`/`lF`: a well-formed lane of an integer lane type is `mk_lane__0 J c`, and one of a float lane type is `mk_lane__1 F c`.
  - `key`/`keyL`: `list_ (OMap f o) ≠ []` when `o ≠ none`, and `Map f l ≠ []` when `l ≠ []`.
- `cases Hop` splits on the four families. In each, `lJ`/`lF` give the lane's form, the side condition is inverted to `hs`, and the proof does `cases` on both lane types. `decide` on `hs` (split into `h1`/`h2` for CONVERT and TRUNC_SAT) refutes the impossible pairs, and each remaining pair is a rule built with `rfl` premises:
  - EXTEND and CONVERT give a singleton result (`List.cons_ne_nil`). The EXTEND cases are I8→I16 `case_14`, I16→I32 `case_3` and I32→I64 `case_4`. The CONVERT cases are I32→F32 `case_16`, I16→F32 `case_19` and I32→F64 `case_20`.
  - TRUNC_SAT (F32→I32 `case_24`, F64→I32 `case_25`) gives `list_ (OMap … (trunc_sat__ …))`, which is non-empty by the axiom `trunc_sat_total`.
  - DEMOTE (F64→F32 `case_29`) and PROMOTE_LOW (F32→F64 `case_34`) give a `Map` over `demote__`/`promote__`, which is non-empty by `demote_nonempty`/`promote_nonempty`.

**Current proof sketch.** The case analysis and the axioms are the same. What changed:
- `lJ`/`lF` use `lane__case_0 J c _ _ _ Heq` and `lane__case_1 F c _ _ _ Heq`. The patterns skip var_0, its size premise and the `wf_uN`/`wf_fN` premise.
- The side conditions are inverted as `… n1 n0 hn1 hn0 hs`. The size premises are then eliminated, so that `hs` is again closed for `decide`:
  - EXTEND: `fun_lsizenn1_eq hn1` and `fun_lsizenn2_eq hn0`.
  - CONVERT: `fun_lsizenn1_eq hn1` and `cases hn0`. `fun_sizenn2` has no function view, and its single rule fixes the output to `Option.get! (size …)`.
  - TRUNC_SAT: `fun_lsizenn2_eq hn1` and `fun_sizenn1_eq hn0`.
  - DEMOTE/PROMOTE_LOW: `cases hn1` (for `fun_sizenn2`) and `fun_sizenn1_eq hn0`.
- Each `fun_lcvtop___case_N` gets two more `_` and the witnesses `(fun_lsizenn2_lsizenn2 _) (fun_lsizenn1_lsizenn1 _)`. The result equation is still `rfl`.

#### `zero_lane_wf` (TypeProgress; theorem) - restated and re-proved
*Statement (Wasm 2.0 terms):* `$zero(nt)` is the zero of a number type nt: `0` for i32/i64 and `+0` (`$fzero`) for f32/f64. It packs into a lane of lane type nt (`$packnum_` is defined) and the packed lane is well-formed. The statement changed:
- old: `packnum_ (lanetype_numtype nt) (fun_zero nt) ≠ none ∧ wf_lane_ … (Option.get! (packnum_ (lanetype_numtype nt) (fun_zero nt)))`
- new: `∃ z, fun_zero nt z ∧ packnum_ (lanetype_numtype nt) z ≠ none ∧ wf_lane_ … (Option.get! (packnum_ (lanetype_numtype nt) z))`

**What broke and why.** The statement no longer elaborates, so the cascade deleted it in both settings; there is no function view for `$zero`.
- The old model had `def fun_zero : numtype → num_`, with I32/I64 ↦ `0` and F32/F64 ↦ `fzero 32/64`.
- The new model has `inductive fun_zero : numtype → num_ → Prop`. The clause `$zero(Fnn) = $fzero($size(Fnn))` applies `!` to the partial `$size`, so the float rules `fun_zero_case_2/_3` require `size (F32/F64) ≠ none` and `fun_fzero (Option.get! (size …)) x`, with output `mk_num__1 Fnn x`. `$fzero` itself became `fun_fzero N x`, whose rule requires `wf_fN N (+0)`.

The errors: `fun_zero nt` has type `num_ → Prop`, but `packnum_` and `wf_num_` expect a `num_`.

**Original proof sketch.** The model's `zero_is_wf` gives `wf_num_ nt (fun_zero nt)`; this runs after `cases nt`, so that `unpack (lanetype_numtype nt)` reduces to nt. `packnum_not_none` shows `$packnum_` is defined, and `packnum__is_wf` shows the lane is well-formed.

**Current proof sketch.** The proof first builds the witness by `cases nt`:
- I32/I64: `fun_zero_case_0/_1`, the integer 0.
- F32/F64: `fun_zero_case_2 _ (by decide) fun_fzero_32` and `fun_zero_case_3 _ (by decide) fun_fzero_64`. `fun_fzero_32 : fun_fzero 32 (fzero 32)` is a HelperLemmas lemma derived from `wf_fzero_32` (`+0` is a well-formed f32); likewise for 64.

The rest is as before. `wf_num_` comes from the new `zero_is_wf _ _ _ Hz rfl`, which now takes the `fun_zero` derivation; then `packnum_not_none` and `packnum__is_wf`. The proof returns `⟨z, Hz, …⟩`. The only user, `vcvtop_step_zero`, needs z for the new premise of `fun_vcvtop___case_2`.

#### `vcvtop_step_zero` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* take a valid `vcvtop` with `$zeroop = ZERO` (`i32x4.trunc_sat_f64x2_sx_zero` or `f32x4.demote_f64x2_zero`) from `nt1 X M1` to `nt2 X M2` (valid shapes, number-type lanes on both sides), and a 128-bit c1. Then `(v128.const c_1) (VCVTOP (nt2 X M2) (nt1 X M1) op)` steps by Step_pure/vcvtop to some `v128.const c`. The step goes through the third clause of `$vcvtop__`, which converts the M1 source lanes and appends M1 zero lanes `$packnum_(Lnn_2, $zero($unpack(Lnn_2)))`. The statement is unchanged.

**What broke and why.** The proof broke (sorried in both settings). Its text uses `fun_zero (unpack (lanetype_numtype nt2))` as a `num_` inside `packnum_` (in `Hpz'`, `Hwz'`, `Hne'` and `Hw'`). `fun_zero` is now a relation (see `zero_lane_wf`), hence the error "`fun_zero (unpack …)` has type `num_ → Prop` but is expected to have type `num_`". Correspondingly, the rule `fun_vcvtop___case_2` gained `var_2 : num_` with the premise `fun_zero (unpack Lnn_2) var_2`, and its `packnum_` premises now mention `var_2`. Its helper `zero_lane_wf` was also deleted by the cascade.

**Original proof sketch.**
- `lanes__is_wf` shows the source lanes are well-formed. `vcvtop_lanes_total` gives the list vs of `$lcvtop__` results: in `Forall₂` with the lanes, of the same length, all defined, all non-empty, and all well-formed nt2 lanes.
- `zero_lane_wf nt2` gives the zero lane. `Hu : unpack (lanetype_numtype nt) = nt` rewrites it into the rule's form `packnum_ (lanetype_numtype nt2) (fun_zero (unpack …))`, giving `Hpz'` and `Hwz'`.
- The list `results ++ replicate M1 [zero lane]` has non-empty, well-formed entries (`Hne'`, `Hw'`). `setproduct_pick` then picks c from `$inv_lanes_(nt2 X M2, ·)` over its `$setproduct_`. `zeroop_total` and `Hz` give `fun_zeroop … (some (some ZERO))`.
- The result is `Step_pure.vcvtop c1 … c (some c) (fun_vcvtop___case_2 …)`.

**Current proof sketch.** The argument is the same. `zero_lane_wf nt2` now returns `⟨z, Hfz, Hpz, Hwz⟩`, and the zero lane is written `Option.get! (packnum_ (lanetype_numtype nt2) z)`. So `Hpz'` and `Hwz'` are gone, and `Hpz` and `Hwz` are used directly. `fun_vcvtop___case_2` gets `var_2 := z`, and its new premise `fun_zero (unpack (lanetype_numtype nt2)) z` is proved by `rw [Hu]; exact Hfz`.

#### `vcvtop_zero_numtype` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* a valid `vcvtop__(L1 X M1, L2 X M2)` with `$zeroop = ZERO` has number-type lanes on both sides: `TRUNC_SAT … ZERO` is f64 → i32 and `DEMOTE ZERO` is f64 → f32. In Lean: `∃ nt1 nt2, L1 = lanetype_numtype nt1 ∧ L2 = lanetype_numtype nt2`. The statement is unchanged.

**What broke and why.** The proof broke (sorried in both settings).
- The side-condition constructors `vcvtop__Fnn_1_M_1_Inn_2_M_2_case_0` and `vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0/_1` gained `var_1 var_0` and two premises each, and their conditions are now stated over the variables. TRUNC_SAT gets `fun_lsizenn2 (Inn_2)` and `fun_sizenn1 (Fnn_1)`; DEMOTE/PROMOTE_LOW get `fun_sizenn2 (Fnn_2)` and `fun_sizenn1 (Fnn_1)`.
- The old patterns `… sx zo hcond` and `… z' hcond` bind `hcond` to the Nat `var_1`. So `revert hcond; decide` no longer refutes the impossible lane pairs, and `first` falls through to `exact ⟨numtype.F64, numtype.I32, rfl, rfl⟩` (`⟨numtype.F64, numtype.F32, rfl, rfl⟩` in the DEMOTE branch), which fails on them. The errors say that `rfl` cannot prove `lanetype_Fnn F32 = lanetype_numtype F64` or `lanetype_Inn I64 = lanetype_numtype I32`.

**Original proof sketch.** `cases Hop` splits on the four families:
- EXTEND and CONVERT have `zeroop_of = none`, which contradicts `Hz`.
- TRUNC_SAT (Fnn→Inn): inject the shape equations and invert the side condition. `zeroop_of` gives `zero? = ZERO`, which forces the alternative `$sizenn1(Fnn_1) = 2·$lsizenn2(Inn_2)`. After `cases F1 <;> cases J2`, `decide` refutes everything except F64→I32, and the answer is `⟨F64, I32⟩`.
- Fnn→Fnn: DEMOTE's condition `|F1| = 2·|F2|` leaves only F64→F32, so the answer is `⟨F64, F32⟩`. PROMOTE_LOW has `zeroop_of = none`.

**Current proof sketch.** The proof is the same, with three changes:
- The patterns become `… sx zo n1 n0 hn1 hn0 hcond`, `… z' n1 n0 hn1 hn0 hcond` and `… n1 n0 hn1 hn0 hcond`.
- TRUNC_SAT: `obtain rfl := fun_lsizenn2_eq hn1` and `obtain rfl := fun_sizenn1_eq hn0`.
- DEMOTE: `cases hn1` (`fun_sizenn2` has no function view) and `obtain rfl := fun_sizenn1_eq hn0`.

After the lane-type split, `hcond` is closed again and `decide` refutes the impossible pairs.

#### `vcvtop_full_lsize` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* a valid `vcvtop__(L1 X M1, L2 X M2)` with neither half nor zero (`$halfop = $zeroop = ε`: `f32x4.convert_i32x4_sx`, `i32x4.trunc_sat_f32x4_sx`) has equal lane widths: `lsize L1 = lsize L2`, i.e. `|L1| = |L2|`. Here `lsize` is now the HelperLemmas function view. The statement text is unchanged.

**What broke and why.**
- Without the views, the statement does not elaborate: `lsize` is unknown, and autoImplicit cannot make it a function. The cascade deleted it, and this is what broke `t_progress_be_vcvtop` in that setting.
- With the views, the statement elaborates but the proof broke (sorried). As in `vcvtop_zero_numtype`, the side-condition patterns `… ho sx hcond` and `… sx zo hcond` bind `hcond` to a Nat (the new `var_1`). So `absurd hcond (by decide)` is ill-typed: `hcond` has type `ℕ` (sort `Type`) where `absurd` expects a proof (sort `Prop`), and `by decide` is left with the goal `¬?m`, which contains a metavariable.

**Original proof sketch.** `cases Hop` splits on the families:
- EXTEND always has a half, PROMOTE_LOW has one too, and DEMOTE has a zero. These contradict `Hh`/`Hz` through `halfop_of`/`zeroop_of`.
- CONVERT (Jnn→Fnn) with `half? = ε` (from `Hh`): after `cases J1 <;> cases F2`, the pairs with equal widths close by `rfl` (`lsize` computes), and the others are refuted by `decide` on the side condition `$sizenn2(Fnn_2) = $lsizenn1(Jnn_1) = 32`.
- TRUNC_SAT (Fnn→Inn) with `zero? = ε`: handled the same way.

**Current proof sketch.** The proof is the same. The patterns gain `n1 n0 hn1 hn0`, and the new premises are eliminated as follows:
- CONVERT: `obtain rfl := fun_lsizenn1_eq hn1` and `cases hn0` (for `fun_sizenn2`).
- TRUNC_SAT: `fun_lsizenn2_eq hn1` and `fun_sizenn1_eq hn0`.
- DEMOTE/PROMOTE_LOW: the patterns only gain the four names, and the contradiction with `Hz`/`Hh` is unchanged.

Because `lsize` in the goal is the HelperLemmas view, which computes, `rfl` still closes the equal-width pairs.

### 7.9 Q5, `TypeProgress`: control, variables and tables (15 constructs)

#### `t_progress_be_block` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* This is the `Instr_ok.block` case of progress for plain instructions (`t_progress_be`, motive `t_progress_be_P`). Suppose `C ⊢ block bt instr* : t_1* → t_2*` (from `Blocktype_ok C bt (t_1* → t_2*)`, the body typing and its IH). Then for every store S, frame F and context C' with `S ⊢ F.module : C'` (`Moduleinst_ok`), `C` = `C'` with its locals replaced by the types of `F.locals` and arbitrary labels and return (`upd_local_label_return C' (map typeof F.locals) lab ret`), `Store_ok S` and well-formed values `val*` of types `t_1*`, the well-formed configuration `S; F; val* (block bt instr*)` is constant or steps. The motive also assumes `not_lf_br`/`not_lf_return`: the instruction list (without `val*`) is not of the form `val'* (br l) …` or `val'* return …`. Here it steps to `label_{|t_2*|}{ε} val* instr*` (execution of `block`: Wasm 2.0 spec §4.4.8, p. 107). All `t_progress_be_*` entries below use this motive, with `val*` typed by the instruction's input types.

**What broke and why.** `have Hfun : fun_blocktype (state.mk_state s f) bt = t_1* → t_2*` no longer elaborates: "`functype.mk_functype …` has type `functype` but is expected to have type `functype → Prop`". The `rfl`s for the `_RESULT` cases then fail on the broken goal. Model change: `$blocktype` (8-reduction.spectec:63-66) used to be `def fun_blocktype : state → blocktype → functype`. It is now `inductive fun_blocktype : state → blocktype → functype → Prop` with three cases:
- `fun_blocktype_case_0`: `_RESULT ε ↦ ε → ε`;
- `case_1`: `_RESULT t ↦ ε → t`;
- `case_2`: `_IDX x ↦ var_0` given `fun_type z x var_0`.

This is because `$type((s; f), x) = f.MODULE.TYPES[x]` became the relation `fun_type` with premise `x < |F.module.types|`. `Step_read.block` (rule `Step_read/block`) now takes a witness `var_0 : functype` with premises `fun_blocktype z bt var_0` and `var_0 = t_1* → t_2*`, instead of the equation `fun_blocktype z bt = t_1* → t_2*`. The errors are the same with the function views, since there is no view for `fun_blocktype`/`fun_type`.

**Original proof sketch.**
- Take the step disjunct, with result `S; F; label_{|t_2*|}{ε} (val* instr*)`.
- From `Htf` (`t_1* → t_2* = mkFunctype ts1 ts2`) get `ts1 = t_1*`, so `Hts : map typeof val* = t_1*`.
- Prove `Hfun` by cases on `Blocktype_ok`:
  - `Blocktype_ok.valtype` (`bt = _RESULT t?`): `rfl`, because the definition computes `ε → t?`.
  - `Blocktype_ok.typeidx` (`C.types[x] = t_1* → t_2*`): unfold the goal to `F.module.types[x]! = …`. Then `rw [← lookup_types … Hmod, ← Hcontext]` (under `Moduleinst_ok`, `C'.types[x] = F.module.types[x]`) turns it into `C.types[x]! = t_1* → t_2*`, which is the typing premise `Hty`. The bound `x < |C.types|` was not used.
- `Hlen : |val*| = |t_1*|` from `Hts` and `List.length_map`.
- Step with `Step.read` and `Step_read.block`, with `k = |val*|`, `n = |t_2*|` and premises `Hfun`, `rfl`, `Hlen`, `rfl`.

**Current proof sketch.** The skeleton and the witness are unchanged. `Hfun` is now a derivation of `fun_blocktype (S;F) bt (t_1* → t_2*)`:
- `_RESULT ε`: `fun_blocktype_case_0`. `_RESULT t`: `fun_blocktype_case_1 _ t`.
- `_IDX x`: this case now uses the validation bound `Hlt : x < |C.types|` from `Blocktype_ok.typeidx`. This is the formal counterpart of the prose step "Assert: due to validation, expand_F(blocktype) is defined".
  - After `subst Hcontext`, `fun_type_typed s f C' x Hmod Hlt` gives `fun_type (S;F) x F.module.types[x]`. Its premise `x < |F.module.types|` comes from `minst_invert_functypes` (`Moduleinst_ok` gives `C'.types = F.module.types`). `C.types` is definitionally `C'.types`, because `upd_local_label_return` only changes locals, labels and return.
  - Rewriting the output with `← lookup_types` and `Hty` gives `fun_type (S;F) x (t_1* → t_2*)`, and `fun_blocktype_case_2 _ x _ Hft` closes the case.
- The step is `Step_read.block … _ Hfun rfl rfl Hlen rfl`. The new witness `var_0` is inferred from `Hfun`, and the new premise `var_0 = t_1* → t_2*` is `rfl`.

#### `t_progress_be_loop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `loop bt instr*` (motive `t_progress_be_P`). If `C ⊢ loop bt instr* : t_1* → t_2*`, then `S; F; val* (loop bt instr*)` with `val* : t_1*` steps to `label_{|t_1*|}{loop bt instr*} val* instr*` (Wasm 2.0 spec §4.4.8, p. 107).

**What broke and why.** The errors are identical to `t_progress_be_block`: `Hfun`'s equation is ill-typed because `fun_blocktype z bt : functype → Prop`, and the `rfl`s fail. `Step_read.loop` (rule `Step_read/loop`) changed in the same way: it gained the witness `var_0 : functype` and the premises `fun_blocktype z bt var_0` and `var_0 = t_1* → t_2*`. The errors are the same with the function views.

**Original proof sketch.** Identical to `block`: the same `Hfun` by cases on `Blocktype_ok` (`rfl`, or `lookup_types` + `Hcontext` + the typing premise) and the same `Hlen`. The step is `Step_read.loop` with `k = |t_1*|` and premises `Hfun`, `Hlen.symm` (`k = |val*|`), `rfl`, `rfl`.

**Current proof sketch.** `Hfun` is built exactly as in the new `block` proof: `fun_blocktype_case_0/1`, or `fun_blocktype_case_2` from `fun_type_typed` with the bound `Hlt` from `Blocktype_ok.typeidx`, `lookup_types` and `Hty`. The step is `Step_read.loop … _ Hfun rfl Hlen.symm rfl rfl`: `var_0` is inferred and the new equation premise is `rfl`.

#### `t_progress_be_br_table` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `br_table l* l'`. If `C ⊢ br_table l* l' : t_1* t* i32 → t_2*` (all labels in range, with `t*` a subtype of each target label type), then `S; F; val* (br_table l* l')` with `val* : t_1* t* i32` steps (Wasm 2.0 spec §4.4.8, p. 108).

**What broke and why.** The only error is "Unknown identifier `iswf_Forall_getElem!`". That lemma was a hand-written helper of the old model (marked "HELPER LEMMA, NOT AUTOGENERATED BY MODEL"): `Forall P l → P default → P l[n]!`, which covers an out-of-range `l[n]!` through the default value. The regenerated model dropped it. In its place the new model provides `iswf_Forall_getElem!_of_lt : Forall P l → n < |l| → P l[n]!`. The rules `Step_pure.br_table_lt/ge` (`Step_pure/br_table-lt`/`-ge`) are unchanged. The error is the same with the function views.

**Original proof sketch.**
- The input types are `(t_1* ++ t*) ++ [i32]`. `typeof_append` splits `val*` into `vs ++ [v1]` with `typeof v1 = i32`, and `invert_typeof_I32` (using `wf_val v1`) gives `v1 = i32.const n`. The configuration is rewritten as `vs ++ [i32.const n, br_table l* l']`.
- Helper `Hctxt` (Rocq's `ctxt_instrs`): a `Step_pure` redex with a well-formed result steps under the value prefix `vs`. This is `Step.pure` when `vs = []`, and otherwise `Step.ctxt_instrs` around `Step.pure`, which needs the configurations before and after to be well formed.
- `wf_instr (br_table l* l')` (`instr_case_9`) gives `wf_uN 32` for every label in `l*` and for `l'`.
- Case `n < |l*|`: `Step_pure.br_table_lt` steps to `br l*[n]`. The well-formedness of the result comes from `iswf_Forall_getElem! _ Hls (iswf_uN_zero _)`, which uses the default label 0. Otherwise `Step_pure.br_table_ge` steps to `br l'`, which is well formed by `wf_uN 32 l'`.

**Current proof sketch.** The proof is unchanged except for the well-formedness of `br l*[n]` in the `br_table-lt` branch. It is now `iswf_Forall_getElem!_of_lt Hls Hv1`, where the bound `Hv1 : n < |l*|` is the branch hypothesis, i.e. the rule's own side condition `i < |l*|`. No default label is read any more. `invert_typeof_I32` is used unchanged; it was itself repaired in cluster Q1.

#### `t_progress_be_local_get` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `local.get x`. If `C.locals[x] = t` (with `x < |C.locals|`), then `S; F; (local.get x)` steps to `F.locals[x]` (Wasm 2.0 spec §4.4.5, p. 91). The input type is `ε`, so there are no values.

**What broke and why.** The error is "`fun_local (state.mk_state s f) x` has type `val → Prop` but is expected to have type `val`", in the result `[fun_local (S;F) x]`. `$local((s; f), x) = f.LOCALS[x]` (5-runtime-aux.spectec:90) became `inductive fun_local z x v` with premise `x < |F.locals|`. `Step_read.local_get` now takes `var_0 : val` and the premise `fun_local z x var_0`, and steps to `var_0`. The error is the same with the function views.

**Original proof sketch.** The input types are `ε`, so `vcs = []`; the cons case is refuted by `simp at Hts`. The result is `S; F; F.locals[x]`, written as `fun_local (S;F) x`. The step is `Step.read` with `Step_read.local_get _ x`, which had no premises.

**Current proof sketch.**
- New `Hx : x < |F.locals|`. After `subst Hcontext`, `C.locals` is `map typeof F.locals`, so the validation bound `x < |C.locals|` becomes `x < |F.locals|` by `List.length_map`. This is the prose's "Assert: due to validation, F.locals[x] exists".
- The result is `[F.locals[x]!]`. The step is `Step_read.local_get _ x _ (fun_local.fun_local_case_0 s f x Hx)`.

#### `t_progress_be_global_get` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `global.get x`. If `C.globals[x] = mut t` (with `x < |C.globals|`), then `S; F; (global.get x)` steps to `S.globals[F.module.globaladdrs[x]].value` (Wasm 2.0 spec §4.4.5, p. 91).

**What broke and why.** The error is "Invalid field `VALUE`" on `fun_global (state.mk_state s f) x : globalinst → Prop`. `$global((s; f), x) = s.GLOBALS[f.MODULE.GLOBALS[x]]` became `inductive fun_global z x gi` with two premises: `F.module.globaladdrs[x] < |S.globals|` and `x < |F.module.globaladdrs|`. `Step_read.global_get` now takes `var_0 : globalinst` and the premise `fun_global z x var_0`, and steps to `var_0.value`. The error is the same with the function views.

**Original proof sketch.** `vcs = []`. The result is `[(fun_global (S;F) x).VALUE]` and the step is `Step_read.global_get _ x`, which had no premises.

**Current proof sketch.**
- `rw [Hcontext] at Hlen` restates the validation bound over `upd_local_label_return C' …`, whose `globals` are definitionally `C'.globals`.
- The result is `[(S.globals[F.module.globaladdrs[x]]).value]` and the step is `Step_read.global_get _ x _ (fun_global_typed s f C' x Hmod Hlen)`.
- `fun_global_typed` builds `fun_global_case_0` from the two halves of `Moduleinst_ok_global_addr`:
  - the module bound: `|F.module.globaladdrs| = |C'.globals|` by `Moduleinst_ok_lengths`;
  - the store bound: every global address of a valid module instance is a valid external address in S, by `minst_invert_globals`.
- These two bounds are the prose's "Assert: due to validation, F.module.globaladdrs[x] exists" and "S.globals[a] exists".

#### `t_progress_be_global_set` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `global.set x`. If `C.globals[x] = var t` (Lean `some r_MUT.MUT`), then `S; F; val (global.set x)` with `val : t` steps to `S'; F; ε`, where `S'` has `globals[F.module.globaladdrs[x]].value := val` (Wasm 2.0 spec §4.4.5, p. 92).

**What broke and why.** The error is "Unknown identifier `with_global`", so `cases Estate : with_global (S;F) x v1` fails. `$with_global((s; f), x, v) = s[.GLOBALS[f.MODULE.GLOBALS[x]].VALUE = v]; f` became `inductive fun_with_global z x v z'` with the single premise `x < |F.module.globaladdrs|`; the store update itself is a total `List.modify`. `Step.global_set` now takes the output state `var_0` and the premise `fun_with_global z x v var_0`, and steps to `var_0; ε`. The error is the same with the function views.

**Original proof sketch.** `vcs` must be `[v1]`; the other lengths are refuted by `simp at Hts`. `cases Estate : with_global (S;F) x v1` names the resulting `s', f'`. Then `rw [← Estate]` and `Step.global_set _ v1 x`, which had no premises.

**Current proof sketch.**
- `rw [Hcontext] at Hlen`.
- For `vcs = [v1]` the witness is `⟨_, f, [], Step.global_set _ v1 x _ (fun_with_global_case_0 s f x v1 (Moduleinst_ok_global_addr s f.MODULE C' _ Hmod Hlen).1)⟩`.
- The updated store is read off the constructor's output and the frame is `f`, so the `cases Estate` is gone.
- Only the module-instance bound `x < |F.module.globaladdrs|` (the `.1`) is needed. The mutability premise is still unused.

#### `call_indirect_progress` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* For every S, F, table index x, type index y and integer `i` (`proj_num__0 i ≠ none`), `S; F; (i32.const i) (call_indirect x y)` steps without changing S or F, either to `call_addr a` or to `trap` (Wasm 2.0 spec §4.4.8, p. 109). There are no typing assumptions. This is Rocq `type_progress.v:2727`.

**What broke and why.** The error is an application type mismatch: `Step_read.call_indirect_call (S;F) i x y ?a h1 h2 h3 h4 h5` still expects four premises: `i < |h2.REFS|`, `h2.REFS[i] = ref.func_addr ?a`, `?a < |S.funcs|` and `h1 = S.funcs[?a].type`. The cause is a change to two definitions:
- the guard `Step_read_before_call_indirect_trap`, the generated relation "rule `call_indirect-call` applies". Its negation is the premise that `Step_read/call_indirect-trap`'s `otherwise` became;
- the rule `Step_read.call_indirect_call`.

Both gained two witnesses: `var_1 : functype`, for `$type(z, y)`, and `var_0 : tableinst`, for `$table(z, x)`. They come with the premises `fun_type z y var_1` and `fun_table z x var_0`; the old versions applied the functions `fun_type z y` and `fun_table z x` directly. So the old pattern `call_indirect_call_0 _ _ _ _ a h1 h2 h3 h4 h5` bound the two witnesses as `h1` and `h2`, and the rule application was four premises short. The error is the same with the function views.

**Original proof sketch.** A classical split on the guard `Step_read_before_call_indirect_trap (S;F; [i32.const i, call_indirect x y])`:
- If the guard holds, inverting its only constructor `call_indirect_call_0` gives `a` and five premises: `i < |tab.elem|`, `i ≠ none`, `tab.elem[i] = ref.func_addr a`, `a < |S.funcs|` and `$type(z, y) = S.funcs[a].type`. They are passed to `Step_read.call_indirect_call`, which steps to `call_addr a`.
- Otherwise, `Step_read.call_indirect_trap` with the negated guard steps to `trap`.

**Current proof sketch.** The split is the same. The constructor now yields `a`, `ft`, `ti` and seven premises: `fun_type (S;F) y ft`, `fun_table (S;F) x ti`, `i ≠ none`, `i < |ti.elem|`, `ti.elem[i] = ref.func_addr a`, `a < |S.funcs|` and `ft = S.funcs[a].type`. All of them are passed unchanged to `Step_read.call_indirect_call _ _ _ _ a ft ti h1 … h7`. The trap branch is unchanged. No bound has to be proved: the lookups' bounds are premises inside the guard, so out-of-range indices just make the guard false. Those bounds are the prose's asserts that `F.module.tableaddrs[x]`, `S.tables[ta]` and `F.module.types[y]` exist.

#### `t_progress_e_call_addr` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* This is the `Instr_ok2.call_addr` case of progress for administrative instructions (`t_progress_e`, motive `t_progress_e_P s`). Suppose `S ⊢ func a : func (t_1* → t_2*)` (`Externaddr_ok`). Then for every frame F with `S ⊢ F.module : C'`, `Store_ok S` and values `val* : t_1*`, the configuration `S; F; val* (call_addr a)` steps. `call_addr a` is the prose's `invoke a` (invocation of a function address, Wasm 2.0 spec §4.4.10, p. 111). The step goes to `frame_{|t_2*|}{F'} (label_{|t_2*|}{ε} instr*)` with `F' = {locals val* (default_ t)*, module mm}`.

**What broke and why.**
- Without the function views the errors are "Unknown identifier `default_`" and "Unknown identifier `default_not_none`". `$default_` is now the relation `fun_default_ t v?`. Its F32/F64 cases go through the relation `fun_fzero`, which carries the side condition `wf_fN N (POS (SUBNORM 0))`. Its `none` result is the generated fallback case `fun_default__case_7`, guarded by a negated `_before_` premise. `default_not_none` mentions `default_`, so it did not elaborate either.
- With the views (`default_` restored in HelperLemmas), two errors remain:
  - `default__is_wf` now takes the output `var_0 : Option val` and a premise `fun_default_ t var_0`. The old call passed `HNotNone t ht` where an `Option val` was expected.
  - `Step_read.call_addr` (rule `Step_read/call_addr`) gained `var_0_lst : List (Option val)` with the premises `|var_0_lst| = |t*|` and `Forall₂ (fun var_0 t => fun_default_ t var_0) var_0_lst t*`. Its non-`none` premise and the new frame's locals `val* ++ map Option.get! var_0_lst` now refer to `var_0_lst`. The old argument `HBound` landed where `var_0_lst` was expected.

**Original proof sketch.**
- `Externaddr_invert_funcs` gives `a < |S.funcs|` and `S.funcs[a] = {type, module mm, code}`; `externtype_func_eq` makes the type `t_1* → t_2*`. The code is destructured as `func x (local t)* instr*`.
- `Store_ok_parts` and `Forall2_nth_of_length` give `Funcinst_ok S S.funcs[a] _`, and `wf_store_parts` gives that the instance is well formed.
- `funcinst_ok_parts` gives `Func_ok C0 (func x (local t)* instr*) (t_1* → t_2*)`. Inverting it yields `hbot : t ≠ bot` for every local type, and that the function is well formed.
- `default_not_none` turns `hbot` into `default_ t ≠ none` for all `t*`. The new locals `val* ++ (default_ t).get!*` are well formed by `HWfVals` and `default__is_wf`.
- The step is `Step_read.call_addr` with `k = |val*|`, `n = |t_2*|` and the premises `HBound`, `HLookup`, `rfl` (code shape), `HNotNone`, `rfl` (frame shape), the well-formedness of the funcinst, func and frame (`frame_case_`), then `rfl`, `hlen`, `rfl`.

**Current proof sketch.**
- Everything up to `HNotNone` is unchanged. `default_` now refers to the function view in HelperLemmas, which has the old model's definition. Against it, the TypeProgress lemma `default_not_none` compiles again with its text unchanged and is used as before.
- The new locals are `val* ++ map Option.get! (map default_ t*)`. Their well-formedness uses the new `default__is_wf t _ _ (fun_default_default t) (HNotNone t ht) rfl`; `fun_default_default t : fun_default_ t (default_ t)` (HelperLemmas) links the view to the relation.
- `Step_read.call_addr` gets:
  - `var_0_lst := map default_ t*`;
  - `List.length_map _` for the length premise;
  - `Forall2_map_l … default_ t* (fun t _ => fun_default_default t)` for the `Forall₂ fun_default_` premise;
  - the non-`none` premise over `var_0_lst`, from `HNotNone` via `List.mem_map`;
  - the remaining arguments as before.

#### `t_progress_be_table_get` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `table.get x`. If `C.tables[x] = lim rt`, then `S; F; (i32.const i) (table.get x)` steps, either to `trap` or to the reference `tab.elem[i]`, where `tab = S.tables[F.module.tableaddrs[x]]` (Wasm 2.0 spec §4.4.6, p. 92).

**What broke and why.** The errors are "Invalid field `REFS`" on `fun_table (state.mk_state s f) x : tableinst → Prop` (in the case split and in the result), followed by unsolved goals. `$table((s; f), x) = s.TABLES[f.MODULE.TABLES[x]]` became `inductive fun_table z x ti` with the premises `F.module.tableaddrs[x] < |S.tables|` and `x < |F.module.tableaddrs|`. `Step_read.table_get_trap` and `table_get_val` (`Step_read/table.get-trap`/`-val`) now take `var_0 : tableinst` and the premise `fun_table z x var_0`, and state their bounds on `var_0.REFS`. The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1]` with `typeof v1 = i32`; the other lengths are refuted. `invert_typeof_I32` gives `v1 = i32.const n`.
- Case `n < |tab.elem|` (with `tab = fun_table (S;F) x`): `Step_read.table_get_val` steps to `tab.elem[n]`. Otherwise `Step_read.table_get_trap` steps to `trap`.
- The side conditions `proj_num__0 … ≠ none` and the comparisons are closed by `simp`/`omega`.

**Current proof sketch.**
- `rw [Hcontext] at Hlen`. Then `obtain ⟨ti, Hti⟩` from `fun_table_typed s f C' x Hmod Hlen`: `ti` is `S.tables[F.module.tableaddrs[x]]` and `Hti : fun_table (S;F) x ti`.
- Both bounds of `Hti` come from `Moduleinst_ok_table_addr` applied to the validation bound `x < |C.tables|`:
  - `|F.module.tableaddrs| = |C'.tables|` by `Moduleinst_ok_lengths`;
  - every table address is valid in S, by `minst_invert_tables`.
- These are the prose's "Assert: due to validation, F.module.tableaddrs[x] exists" and "S.tables[a] exists". The table entries below get their `fun_table`/`fun_elem` premises the same way.
- The split is the same, now on `n < |ti.elem|`, using `table_get_val _ _ x ti … Hti` and `table_get_trap _ _ x ti Hti …`.

#### `t_progress_be_table_set` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `table.set x`. If `C.tables[x] = lim rt`, then `S; F; (i32.const i) ref (table.set x)` steps, either to `trap` or to `S'; ε`, where `S'` has `tables[F.module.tableaddrs[x]].elem[i] := ref` (Wasm 2.0 spec §4.4.6, p. 93).

**What broke and why.** The errors are "Invalid field `REFS`" on `fun_table (S;F) x` and "Unknown identifier `with_table`", which makes `cases Estate` fail. Besides the `fun_table` change described under `table.get`, `$with_table` became `inductive fun_with_table z x i r z'` with the premise `x < |F.module.tableaddrs|`. The two rules changed as follows:
- `Step.table_set_val` (`Step/table.set-val`) now takes `var_1 : tableinst` and the output state `var_0`, with the premises `fun_table z x var_1` and `fun_with_table z x i r var_0`.
- `Step.table_set_trap` takes `var_0 : tableinst` with `fun_table z x var_0`.

The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1, v2]`. `invert_typeof_I32` gives `v1 = i32.const n1`, and `invert_typeof_reftype'` gives `v2 = ref r2`.
- Case `n1 < |(fun_table (S;F) x).REFS|`: `cases Estate : with_table (S;F) x n1 r2` names the new `s', f'`, then `Step.table_set_val` applies.
- Otherwise `Step.table_set_trap` applies, with the store unchanged and result `trap`.

**Current proof sketch.**
- `ti` and `Hti` come from `fun_table_typed`, as in `table.get`.
- Case `n1 < |ti.elem|`: `Step.table_set_val _ _ r2 x ti _ Hti (≠ none) (fun_with_table_case_0 s f x _ r2 (Moduleinst_ok_table_addr s f.MODULE C' _ Hmod Hlen).1) (bound)`. The new store is the relation's output, so there is no `cases Estate`.
- Otherwise `Step.table_set_trap _ _ r2 x ti Hti …`.

#### `t_progress_be_table_size` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `table.size x`. If `C.tables[x] = lim rt`, then `S; F; (table.size x)` steps to `i32.const |tab.elem|` (Wasm 2.0 spec §4.4.6, p. 93).

**What broke and why.** The errors are "Invalid field `REFS`" on `fun_table (S;F) x` in the result, and an argument mismatch in `Step_read.table_size _ x _ rfl`, where `rfl` was given in the slot of the new `tableinst` argument. `Step_read.table_size` now takes `var_0 : tableinst`, `fun_table z x var_0` and `|var_0.REFS| = n`. The errors are the same with the function views.

**Original proof sketch.** `vcs = []`. The result is `i32.const |(fun_table (S;F) x).REFS|` and the step is `Step_read.table_size _ x _ rfl`.

**Current proof sketch.** `ti` and `Hti` come from `fun_table_typed` (as in `table.get`). The result is `i32.const |ti.elem|` and the step is `Step_read.table_size _ x _ ti Hti rfl`.

#### `t_progress_be_table_fill` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `table.fill x`. If `C.tables[x] = lim rt`, then `S; F; (i32.const i) val (i32.const n) (table.fill x)` steps (Wasm 2.0 spec §4.4.6, p. 94).

**What broke and why.** The errors are "Invalid field `REFS`" on `fun_table (S;F) x` in the case split, then an application mismatch for `Step_read.table_fill_trap … v2 n3 x ?ti ?h` followed by "`simp` made no progress". The old arguments are shifted by the two new leading arguments, a `tableinst` and its `fun_table` premise. `Step_read.table_fill_trap/zero/succ` (`Step_read/table.fill-*`) each take `var_0 : tableinst` and `fun_table z x var_0` now, and state their bounds on `var_0.REFS`. The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1, v2, v3]` with types `i32 rt i32`. `invert_typeof_I32` gives `v1 = i32.const n1` and `v3 = i32.const n3`; `v2` stays a value.
- Case `n1 + n3 > |tab.elem|`: `table_fill_trap`.
- Otherwise, if `n3 = 0`: `table_fill_zero`, with `n1 + 0 ≤ |tab.elem|` by `omega`.
- Otherwise `n3 = k+1`: `table_fill_succ` steps to `(i32.const n1) val (table.set x) (i32.const n1+1) val (i32.const k) (table.fill x)`, after rewriting `Int.toNat ((k+1) - 1) = k`.

**Current proof sketch.** The proof is the same, with the split stated on `|ti.elem|`. `ti` and `Hti` come from `fun_table_typed` and are passed to each rule: `table_fill_trap _ _ v2 n3 x ti Hti …`, `table_fill_zero _ _ v2 0 x ti Hti …`, `table_fill_succ … x ti (≠ none) Hti …`. As in the old model, the `zero`/`succ` rules carry the explicit complement `n1 + n3 ≤ |tab.elem|` rather than a negated `_before_` guard, so no classical split is needed.

#### `t_progress_be_table_copy` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `table.copy x_1 x_2`. If `C.tables[x_1] = lim_1 rt` and `C.tables[x_2] = lim_2 rt`, then `S; F; (i32.const j) (i32.const i) (i32.const n) (table.copy x_1 x_2)` steps (Wasm 2.0 spec §4.4.6, p. 95).

**What broke and why.** The errors are "Invalid field `REFS`" on `fun_table (S;F) x2` and `fun_table (S;F) x1`, then an application mismatch for `Step_read.table_copy_trap`. All four `table_copy_*` rules (`Step_read/table.copy-trap/-zero/-le/-gt`) now take two `tableinst` witnesses: `var_1` for the destination table x and `var_0` for the source table y. They come with the premises `fun_table z x var_1` and `fun_table z y var_0`. The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1, v2, v3]`, all `i32`: `j = n1` is the destination offset in table x_1, `i = n2` is the source offset in table x_2, and `n = n3`.
- Case `n2 + n3 > |tab_2.elem| ∨ n1 + n3 > |tab_1.elem|`: `table_copy_trap`.
- Otherwise both sums are within bounds (`Hb`, by `omega`), and the cases are:
  - `n3 = 0`: `table_copy_zero`;
  - `n1 ≤ n2`: `table_copy_le`;
  - otherwise `table_copy_gt`, with `j > i` by `omega`.

**Current proof sketch.** `rw [Hcontext] at Hlenx1 Hlenx2`. `ti1`/`Hti1` and `ti2`/`Hti2` come from `fun_table_typed` for x_1 and x_2, using the two bounds of `Instr_ok.table_copy`. The four-way split is the same, stated on `|ti1.elem|` and `|ti2.elem|`, and passes `ti1 ti2 Hti1 Hti2` to `table_copy_trap/zero/le/gt`.

#### `t_progress_be_table_init` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `table.init x_1 x_2`. If `C.tables[x_1] = lim rt` and `C.elems[x_2] = rt`, then `S; F; (i32.const j) (i32.const i) (i32.const n) (table.init x_1 x_2)` steps (Wasm 2.0 spec §4.4.6, p. 96).

**What broke and why.** The errors are "Invalid field `REFS`" on `fun_elem (S;F) x2` and `fun_table (S;F) x1`, then an application mismatch for `Step_read.table_init_trap`. `$elem((s; f), x) = s.ELEMS[f.MODULE.ELEMS[x]]` became `inductive fun_elem` with the premises `F.module.elemaddrs[x] < |S.elems|` and `x < |F.module.elemaddrs|`. `table_init_trap/zero/succ` (`Step_read/table.init-*`) now take `var_1 : tableinst` and `var_0 : eleminst` with the premises `fun_table z x var_1` and `fun_elem z y var_0`. The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1, v2, v3]`, all `i32`: `j = n1` is the offset in table x_1, `i = n2` is the offset in element segment x_2, and `n = n3`.
- Case `n2 + n3 > |elem.elem| ∨ n1 + n3 > |tab.elem|`, stated on `fun_elem (S;F) x2` and `fun_table (S;F) x1`: `table_init_trap`.
- Otherwise, if `n3 = 0`: `table_init_zero`.
- Otherwise `n3 = k+1`: `table_init_succ`, whose extra premise `n2 < |elem.elem|` holds by `omega`.

**Current proof sketch.** `rw [Hcontext] at Hlenx1 Hlenx2`. Two witnesses are obtained:
- `ti`/`Hti` from `fun_table_typed s f C' x1`;
- `ei`/`Hei` from `fun_elem_typed s f C' x2`, using the bound `x_2 < |C.elems|`. That lemma gets both bounds from `Moduleinst_ok_elem_addr` (`Moduleinst_ok_lengths` and `minst_invert_elems`).

The split is the same, stated on `|ei.elem|` and `|ti.elem|`, and passes `ti ei Hti Hei` to `table_init_trap/zero/succ`.

#### `t_progress_be_elem_drop` (TypeProgress; theorem) - re-proved
*Statement (Wasm 2.0 terms):* Progress for `elem.drop x`. If `C.elems[x] = rt`, then `S; F; (elem.drop x)` steps to `S'; ε`, where `S'` has `elems[F.module.elemaddrs[x]].elem := ε` (Wasm 2.0 spec §4.4.6, p. 97).

**What broke and why.** The error is "Unknown identifier `with_elem`", which makes `cases Estate` fail. `$with_elem((s; f), x, r*)` became `inductive fun_with_elem z x r* z'` with the premise `x < |F.module.elemaddrs|`. `Step.elem_drop` (`Step/elem.drop`) now takes the output state `var_0` and the premise `fun_with_elem z x ε var_0`. The error is the same with the function views.

**Original proof sketch.** `vcs = []`. `cases Estate : with_elem (S;F) x []` names `s', f'`. Then `rw [← Estate]` and `Step.elem_drop _ x`, which had no premises.

**Current proof sketch.** `rw [Hcontext] at Hlen`. The witness is `⟨_, f, [], Step.elem_drop _ x _ (fun_with_elem_case_0 s f x [] (Moduleinst_ok_elem_addr s f.MODULE C' _ Hmod Hlen).1)⟩`. The updated store is the relation's output and the frame is unchanged. Only the module-instance bound `x < |F.module.elemaddrs|` is needed, obtained from the validation bound `x < |C.elems|`.

### 7.10 Q6a, `TypeProgress`: memory instructions (9 constructs)

#### `t_progress_be_memory_size` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `memory.size`. This is the `Instr_ok.memory_size` case of `t_progress_be`, i.e. the `Instrs_ok.rec` minor premise for the motive `t_progress_be_P`. Assume `C ⊢ memory.size : [] → [i32]` (validation needs `C.mems[0]`), and take a well-formed configuration `S; F; vcs memory.size` with these side conditions:
- `⊢ S ok`;
- `S ⊢ F.module : C'`, where C is C' with F's locals and some labels/return;
- well-formed operands `vcs` (`Forall wf_val vcs`) of the input type `[]`;
- `not_lf_br` / `not_lf_return` for `[memory.size]` (it is not a `br` or `return` after values). These hold trivially and are not used here.

The motive then says that either `[memory.size]` is a constant list or the configuration steps to some `S'; F'; es'`. The proof always produces the step. Statement unchanged.

**What broke and why.** Lean rejected `Step_read.memory_size (state.mk_state s f) v_n ?_ ?_` with "application type mismatch". After the two holes, the term still had type `v_n * 64 * Ki = |?var_0.BYTES| → wf_uN 32 0 → Step_read …`. The next bullet (`simp only [fun_mem, proj_uN_0]`) then reported "no goals". The cause is the model change for `$mem(z, 0)`:
- It used to be the function `fun_mem z x := s.MEMS[f.MODULE.MEMS[x]!]!`. With `sideconditions_on_defs` it is the relation `fun_mem z x mi`, whose only constructor `fun_mem_case_0` has the premises `F.module.memaddrs[x] < |S.mems|` and `x < |F.module.memaddrs|`.
- `Step_read.memory_size` (rule `Step_read/memory.size`) gained the explicit argument `var_0 : meminst` and the premise `fun_mem z 0 var_0`. Its premise `n·64·Ki = |mem.data|` is now stated on `var_0.BYTES`.
- So the two old holes were used up by the new argument and premise. The "no goals" error follows from that: Lean replaced the mismatched argument by an error term, so `refine` produced no goals for the bullets. Separately, `fun_mem` is no longer a function that `simp` could unfold, so the final proof drops it from the simp set.

The errors are the same with and without the function views, because no view exists for the partial lookup `fun_mem`.

**Original proof sketch.**
- Unfold the motive, choose the "steps" disjunct and read `ts1 = []` off the function type. A non-empty `vcs` contradicts `map typeof vcs = ts1`.
- `C.mems = C'.mems` holds because C is C' with locals/labels/return replaced. `Moduleinst_ok_lengths` gives `|F.module.memaddrs| = |C'.mems|`, hence `0 < |F.module.memaddrs|`.
- `minst_invert_mems` gives, for each memory address of `F.module`, that it is in range of `S.mems` (from the `Externaddr_ok` premises of `S ⊢ F.module : C'`). Applied to the pair `(F.module.memaddrs[0], C'.mems[0])` (through `mem_zip_getElem!`), it gives the address bound `a := F.module.memaddrs[0] < |S.mems|`.
- `Store_ok_parts` (from `⊢ S ok`) gives the memory types `mtl` with `|S.mems| = |mtl|` and pointwise `Meminst_ok`. At index a this is `S ⊢ S.mems[a] : mtl[a]`.
- `meminst_ok_raw` inverts that to `S.mems[a] = {type [n..m?] page, data bs}` with `|bs| = n·(64·Ki)`.
- Step by `Step.read` with `Step_read.memory_size` to `i32.const n`. The premise `n·64·Ki = |$mem(z,0).BYTES|` follows by unfolding `fun_mem`, rewriting with the inversion and `Nat.mul_assoc`. `wf_uN 32 0` is `wf_uN.uN_case_0`.

**Current proof sketch.**
- The skeleton is the same: motive, `ts1 = []`, `vcs = []`, store inversion with `Store_ok_parts`/`meminst_ok_raw`, and a step to `i32.const n`.
- The address bound now comes from the new lemma `Moduleinst_ok_mem_addr s F.module C' 0 Hmod Hlen'` (`.2`), which packages `Moduleinst_ok_lengths`, `minst_invert_mems` and `mem_zip_getElem!`. `Hlen' : 0 < |C'.mems|` is the validation premise `0 < |C.mems|` rewritten with `C.mems = C'.mems`.
- New premise: the meminst argument of `Step_read.memory_size` is left to unification. Its `fun_mem` witness is `fun_mem_typed s f C' 0 Hmod Hlen'`, i.e. `fun_mem (S;F) 0 S.mems[F.module.memaddrs[0]]`, built from the same two `Moduleinst_ok` bounds.
- The length premise is now about that meminst directly. It closes with `simp only [proj_uN_0]` and the same rewrites, with no `fun_mem` unfolding.

#### `t_progress_be_memory_fill` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `memory.fill` (the `Instr_ok.memory_fill` case of `t_progress_be`; same side conditions and conclusion shape as `t_progress_be_memory_size`). If `C ⊢ memory.fill : [i32 i32 i32] → []` (with `C.mems[0]`), then every well-formed configuration `S; F; vcs memory.fill` whose operands have type `[i32 i32 i32]` steps. Such a configuration has the form `(i32.const i) val (i32.const n) memory.fill`. Statement unchanged.

**What broke and why.**
- "Invalid field `BYTES`" in the case split `n1 + n3 > (fun_mem (state.mk_state s f) (uN.mk_uN 0)).BYTES.length`: `fun_mem …` now has type `meminst → Prop`.
- In `Step_read.memory_fill_trap …` the old arguments sit two positions off. `by simp [proj_num__0]` lands on the new `meminst` argument ("simp made no progress"), and `wf_uN.uN_case_0 …` lands on `proj_num__0 i ≠ none`.
- Cause: `fun_mem` became a relation (see `t_progress_be_memory_size`). The three rules `Step_read/memory.fill-trap|zero|succ` each gained `(var_0 : meminst)` and the premise `fun_mem z 0 var_0`, and their bound premises (`i + n > |mem.data|`, resp. `≤`) are now stated on `var_0.BYTES`. The zero/succ applications are out of step as well (in `-succ` the `fun_mem` premise comes second, after `proj_num__0 i ≠ none`).
- The errors are the same with the function views.

**Original proof sketch.**
- Unfold the motive and choose the step disjunct, with `ts1 = [i32 i32 i32]`. `vcs` of any other length contradicts the typing.
- For `vcs = [v1 v2 v3]`: `invert_typeof_I32` (using `wf_val` from `Forall wf_val vcs`) turns v1 and v3 into `i32.const n1` (= i) and `i32.const n3` (= n). v2 stays an arbitrary `val`, since the rule accepts any value.
- If `n1 + n3 > |$mem(z,0).BYTES|` (`fun_mem` was a function): `Step_read.memory_fill_trap` reduces to `trap`.
- Otherwise, if `n3 = 0`: `memory_fill_zero` reduces to `ε`, with the `≤` bound by omega.
- Otherwise: `memory_fill_succ` reduces to `(i32.const i) val (i32.store8 memarg0) (i32.const i+1) val (i32.const n-1) memory.fill`.
- All steps go through `Step.read`, and `proj_num__0 i ≠ none` holds by `simp`. The model encodes the spec's `otherwise` as explicit `≤` premises (plus `n ≠ 0` for `-succ`), so no `Step_read_before_*` reasoning is needed.

**Current proof sketch.**
- The canonical forms and the three-way split are unchanged.
- New: before the split, the proof derives `C.mems = C'.mems` and `Hm := fun_mem_typed s f C' 0 Hmod (0 < |C'.mems|)`, where the index bound is validation's `0 < |C.mems|`. It then generalizes `S.mems[F.module.memaddrs[0]]` to `mi`, so the split is on `n1 + n3 > |mi.BYTES|`.
- Each rule receives `mi` and `Hm` in its new argument position (`memory_fill_succ` takes `proj_num__0 i ≠ none` before `Hm`). The bound arguments are as before.

#### `t_progress_be_memory_copy` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `memory.copy` (the `Instr_ok.memory_copy` case of `t_progress_be`; same side conditions and conclusion shape as `t_progress_be_memory_size`). If `C ⊢ memory.copy : [i32 i32 i32] → []` (with `C.mems[0]`), then every well-formed `S; F; (i32.const j) (i32.const i) (i32.const n) memory.copy` steps. Here j is the destination and i the source. Statement unchanged.

**What broke and why.**
- Two "Invalid field `BYTES`" errors on `fun_mem (state.mk_state s f) (uN.mk_uN 0)`, one per disjunct of the trap condition.
- In `Step_read.memory_copy_trap`, the shifted arguments put `wf_uN.uN_case_0 …` where `proj_num__0 j ≠ none` is expected.
- Cause: `fun_mem` became a relation. `Step_read/memory.copy-trap|zero|le|gt` each gained `(var_0 : meminst)` and `fun_mem z 0 var_0`: the first premise for trap/zero, the third for le/gt. Both bounds are now stated on `var_0.BYTES`.
- The errors are the same with the function views.

**Original proof sketch.**
- Substitute `ts1 = [i32 i32 i32]`. `rcases` on `vcs`, where `simp` closes the wrong lengths.
- `invert_typeof_I32` on all three operands gives n1 = j, n2 = i, n3 = n.
- If `i + n > |$mem(z,0).BYTES| ∨ j + n > |$mem(z,0).BYTES|`: `memory_copy_trap` reduces to `trap`.
- Otherwise both `≤` bounds hold (`HB`, by omega). Then:
  - If `n = 0`: `memory_copy_zero` reduces to `ε`.
  - If `j ≤ i`: `memory_copy_le` copies one byte forward (`i32.load8_u` / `i32.store8` with `memarg0`) and continues with `j+1`, `i+1`, `n-1`.
  - Otherwise: `memory_copy_gt` (with `j > i` by omega) copies the last byte first (`j+n-1`, `i+n-1`) and continues with `n-1`.

**Current proof sketch.**
- Same structure. Before the split, `Hm := fun_mem_typed s f C' 0 Hmod …` (index bound from `0 < |C.mems|` and `C.mems = C'.mems`), and `S.mems[F.module.memaddrs[0]]` is generalized to `mi`.
- The trap condition and `HB` are stated on `|mi.BYTES|`. Each of the four rules receives `mi` and `Hm` in its new position, and the remaining arguments are unchanged.

#### `t_progress_be_memory_init` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `memory.init x` (the `Instr_ok.memory_init` case of `t_progress_be`; same side conditions and conclusion shape as `t_progress_be_memory_size`). If `C ⊢ memory.init x : [i32 i32 i32] → []` (`C.mems[0]` exists, `x < |C.datas|`, `C.datas[x] = ok`), then every well-formed `S; F; (i32.const j) (i32.const i) (i32.const n) (memory.init x)` steps. Here j is the memory offset and i the data offset. Statement unchanged.

**What broke and why.**
- "Invalid field `BYTES`" on both `fun_data (state.mk_state s f) x` (now of type `datainst → Prop`) and `fun_mem …` in the trap condition.
- `Step_read.memory_init_trap` got its arguments four positions off, so `wf_uN.uN_case_0 …` landed on the new `fun_data` premise.
- Cause: `$data(z, x)` (`fun_data`) became a relation in the same way as `fun_mem`. Its constructor `fun_data_case_0` has the premises `F.module.dataaddrs[x] < |S.datas|` and `x < |F.module.dataaddrs|`.
- `Step_read/memory.init-trap|zero|succ` each gained `(var_1 : meminst) (var_0 : datainst)` and the premises `fun_mem z 0 var_1` and `fun_data z x var_0`. The data bounds are now on `var_0.BYTES`, and so are `-succ`'s premise `i < |data.data|` and the byte `data.data[i]` it reads. The memory bounds are on `var_1.BYTES`.
- The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1 v2 v3]`; other lengths contradict the typing. `invert_typeof_I32` on all three gives n1 = j, n2 = i, n3 = n.
- If `i + n > |$data(z,x).BYTES| ∨ j + n > |$mem(z,0).BYTES|`: `memory_init_trap` reduces to `trap`.
- Otherwise, case on n (`rcases n3`):
  - `n = 0`: `memory_init_zero` reduces to `ε`, with the bounds by omega.
  - `n = n3+1`: `memory_init_succ` reduces to `(i32.const j) (i32.const data.data[i]) (i32.store8 memarg0) (i32.const j+1) (i32.const i+1) (i32.const n-1) (memory.init x)`. Its premise `i < |data.data|` follows from `i + n ≤ |data.data|` and `n ≥ 1` by omega, and `n ≠ 0` is `Nat.succ_ne_zero`.

**Current proof sketch.**
- The split structure is unchanged.
- New: from `Hcontext` the proof derives `C.mems = C'.mems ∧ C.datas = C'.datas`. Then:
  - `Hm := fun_mem_typed s f C' 0 Hmod (0 < |C'.mems|)`.
  - `Hd := fun_data_typed s f C' x Hmod (x < |C'.datas|)`, where the index bound is the validation premise `x < |C.datas|` (`HRange`). `fun_data_typed` builds `fun_data_case_0` from `Moduleinst_ok_data_addr`. That lemma combines `|F.module.dataaddrs| = |C'.datas|` (`Moduleinst_ok_lengths`) with `minst_invert_datas`, which reads off the `Moduleinst_ok` premise that every data address is `< |S.datas|`.
- `S.mems[F.module.memaddrs[0]]` and `S.datas[F.module.dataaddrs[x]]` are generalized to `mi` and `di`, and the split is on `|di.BYTES|` and `|mi.BYTES|`.
- All three rules receive `mi di Hm Hd`. In `-succ`, `Hm Hd` come after the `i < |di.BYTES|` premise and the two `≠ none` premises. The omega side goals are unchanged.

#### `t_progress_be_data_drop` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `data.drop x` (the `Instr_ok.data_drop` case of `t_progress_be`; same side conditions and conclusion shape as `t_progress_be_memory_size`). If `C ⊢ data.drop x : [] → []` (`x < |C.datas|`, `C.datas[x] = ok`), then every well-formed `S; F; data.drop x` (with no operands) steps. Statement unchanged.

**What broke and why.**
- "Unknown identifier `with_data`", so `cases Estate : with_data (state.mk_state s f) x []` failed ("major premise type is not an inductive type").
- Cause: the store update `$with_data(z, x, b*)` was the function `with_data` (S with `S.datas[F.module.dataaddrs[x]].data := b*`). It is now the relation `fun_with_data z x b* z'`, whose constructor `fun_with_data_case_0` has the premise `x < |F.module.dataaddrs|`.
- `Step.data_drop` (rule `Step/data.drop`) gained the output state `var_0 : state` and the premise `fun_with_data z x [] var_0`, and now reduces to `config var_0 []`.
- The errors are the same with the function views.

**Original proof sketch.**
- Unfold the motive and choose the step disjunct, with `vcs = []` (a non-empty `vcs` contradicts `ts1 = []`).
- Destruct the state `with_data (S;F) x []` into `S'; F'` (`cases Estate`), take `S'`, `F'`, `[]` as witnesses, rewrite back with `← Estate`, and apply `Step.data_drop`, which had no premises.
- The validation premises were not used.

**Current proof sketch.**
- `vcs = []` as before.
- New: the index bound `Hx : x < |F.module.dataaddrs|` is `(Moduleinst_ok_data_addr s F.module C' x Hmod (HeqC ▸ HRange)).1`. Here `HRange : x < |C.datas|` is the validation premise and `HeqC : C.datas = C'.datas`.
- The step is `Step.data_drop _ x _ (fun_with_data.fun_with_data_case_0 s f x [] Hx)`. The existential `S'`, `F'` are fixed by unification with the constructor's output state: S with `datas[F.module.dataaddrs[x]].data := ε`, and F unchanged. No case split on a state is needed.

#### `t_progress_be_load_val` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for a full-width load `t.load memarg` (the `Instr_ok.load_val` case of `t_progress_be`; same side conditions and conclusion shape as `t_progress_be_memory_size`). If `C ⊢ t.load memarg : [i32] → [t]` (`C.mems[0]` exists, `|t|` is defined, `2^memarg.align ≤ |t|/8`), then every well-formed `S; F; (i32.const i) (t.load memarg)` steps, either to `trap` or to `t.const c`. Statement unchanged.

**What broke and why.**
- "Invalid field `BYTES`" on `fun_mem …` in the bounds split.
- In `Step_read.load_num_trap _ _ _ _ (by simp [proj_num__0]) Hfunsize …`, the `simp` lands on the new meminst argument ("no progress"), and `Hfunsize : size t ≠ none` lands on the new `fun_mem` premise.
- Cause: `fun_mem` became a relation. `Step_read/load-num-trap|val` gained `(var_0 : meminst)` and `fun_mem z 0 var_0` as first premise, with the bound and the byte slice now on `var_0.BYTES`.
- The helper `wf_config_mem_bytes` was stated on `(fun_mem (S;F) x).BYTES`. That statement no longer elaborates and was restated, so the old call `wf_config_mem_bytes _ _ _ _ HWfConfig` is out of date too.
- The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1]`; other lengths contradict the typing. `invert_typeof_I32` gives `i32.const n1`.
- If `n1 + memarg.offset + |t|/8 > |$mem(z,0).BYTES|`: `Step_read.load_num_trap` reduces to `trap`. Its premise `size t ≠ none` is the validation premise `Hfunsize`.
- Otherwise: `Step_read.load_num_val` with `c := inv_nbytes_ t bs`, where `bs = mem.data[i+offset : |t|/8]` (`List.take (|t|/8) (List.drop (i+offset) …)`). The premises are discharged as follows:
  - `nbytes_ t c = bs` by the axiom `nbytes_inv`. It needs `|bs| = |t|/8`, which comes from `list_slice_size` (the slice is in bounds) and `Hsz` (`|t|/8` is integral, by `cases nt <;> decide +kernel`).
  - `wf_num_ t c` by `inv_nbytes__is_wf`, `Forall_list_slice` and the old `wf_config_mem_bytes _ _ _ _ HWfConfig` (all bytes of `$mem(z,x)` are well-formed in a well-formed configuration). That lemma went through `mem_bytes_wf`, whose out-of-range case read the default `meminst`.
  - `wf_uN 32 0`.

**Current proof sketch.**
- The structure is unchanged.
- New: `Hm := fun_mem_typed s f C' 0 Hmod …`, with the index bound from `0 < |C.mems|` and `C.mems = C'.mems`. `S.mems[F.module.memaddrs[0]]` is generalized to `mi`, and both the split and the slice are on `mi.BYTES`.
- The steps are `load_num_trap _ _ _ _ mi Hm …` and `load_num_val _ _ _ _ _ mi Hm …`.
- Byte well-formedness now comes from the restated `wf_config_mem_bytes _ _ _ _ _ HWfConfig Hm`, which takes the meminst and its `fun_mem` witness. Internally it uses `fun_mem_inv` and the bounded `mem_bytes_wf`, so no default value is read.
- `nbytes_inv`, `list_slice_size`, `Hsz` and `inv_nbytes__is_wf` are used as before.

#### `t_progress_be_load_pack` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for a packed load `iN.loadM_sx memarg` (the `Instr_ok.load_pack` case of `t_progress_be`; same side conditions and conclusion shape as `t_progress_be_memory_size`). If `C ⊢ iN.loadM_sx memarg : [i32] → [iN]` (`C.mems[0]` exists, `2^memarg.align ≤ M/8`), then every well-formed `S; F; (i32.const i) (iN.loadM_sx memarg)` steps, either to `trap` or to `iN.const extend^sx_{M,N}(c)`. Statement unchanged.

**What broke and why.**
- "Invalid field `BYTES`" on `fun_mem …` in the bounds split.
- In `Step_read.load_pack_trap` the arguments shift: `by simp [proj_num__0]` lands on the meminst argument, and `wf_uN.uN_case_0 …` lands on `proj_num__0 i ≠ none`.
- Cause: `fun_mem` became a relation. `Step_read/load-pack-trap|val` gained `(var_0 : meminst)` and the `fun_mem` premise: first premise for trap, second (after `size Inn ≠ none`) for val. The bound and the slice are on `var_0.BYTES`.
- The old call `wf_config_mem_bytes _ _ _ _ HWfConfig` is out of date because that lemma was restated (as for load_val).
- The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1]`, and `invert_typeof_I32` gives `i32.const n1`.
- If `n1 + memarg.offset + M/8 > |$mem(z,0).BYTES|`: `load_pack_trap` reduces to `trap`.
- Otherwise: `load_pack_val` with `c := inv_ibytes_ M bs`, where `bs = mem.data[i+offset : M/8]`. The premises are discharged as follows:
  - `size Inn ≠ none` by `cases v_Inn; simp`.
  - `ibytes_ M c = bs` by the axiom `ibytes_inv` and `list_slice_size`.
  - `wf_uN M c` by `inv_ibytes__is_wf`, `Forall_list_slice` and the old `wf_config_mem_bytes`.
- The result is `iN.const (extend__ M |Inn| sx c)`.

**Current proof sketch.**
- Same as before, plus `Hm := fun_mem_typed s f C' 0 Hmod …` and a generalization to `mi`.
- The steps are `load_pack_trap _ _ _ _ _ _ mi Hm …` and `load_pack_val _ _ _ _ _ _ _ mi ?_ Hm …` (the size premise comes first, then `Hm`).
- The slice is taken from `mi.BYTES`. Byte well-formedness comes from the restated `wf_config_mem_bytes _ _ _ _ _ HWfConfig Hm`.
- `ibytes_inv`, `list_slice_size` and `inv_ibytes__is_wf` are used as before.

#### `t_progress_be_store_val` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for a full-width store `t.store memarg` (the `Instr_ok.store_val` case of `t_progress_be`; same side conditions and conclusion shape as `t_progress_be_memory_size`). If `C ⊢ t.store memarg : [i32 t] → []` (`C.mems[0]` exists, `|t|` is defined, alignment bound), then every well-formed `S; F; (i32.const i) (t.const c) (t.store memarg)` steps. It reaches either `S; F; trap` or the updated store with an empty instruction sequence. Statement unchanged.

**What broke and why.**
- "Invalid field `BYTES`" on `fun_mem …` in the bounds split.
- In `Step.store_num_trap`, `simp` lands on the new meminst argument and `Hfunsize` on the new `fun_mem` premise.
- Cause: `fun_mem` became a relation, and `Step/store-num-trap` gained `(var_0 : meminst)` and `fun_mem z 0 var_0`.
- `Step/store-num-val` used to target the function `with_mem z 0 (i+offset) (|t|/8) b*`. That is now the relation `fun_with_mem z 0 (i+offset) (|t|/8) b* z'`, whose constructor `fun_with_mem_case_0` has the single premise `0 < |F.module.memaddrs|`. The rule gained the output state `var_0 : state` and the premise `fun_with_mem z 0 (i+offset) (|t|/8) b* var_0` (third, after `size t ≠ none`), and now reduces to `config var_0 []`. So the old `store_num_val` application is out of step as well.
- The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1 v2]`. `invert_typeof_I32` gives `i32.const n1`, and `invert_typeof_numtype` gives `t.const n2`.
- If `n1 + memarg.offset + |t|/8 > |$mem(z,0).BYTES|`: `Step.store_num_trap` leaves the store unchanged and produces `trap`. Its premises are `proj_num__0 i ≠ none`, `Hfunsize`, the bound, and `wf_uN 32 0`.
- Otherwise: `Step.store_num_val (S;F) …` with `b* = nbytes_ t c` (`rfl`). Its target is the state `with_mem (S;F) 0 (i+offset) (|t|/8) b*`, and the witnesses `S'`, `F'`, `[]` are found by unification.
- The rule (like the spec rule `Step/store-num-val`) has no in-bounds premise, so the negated bound is not used.

**Current proof sketch.**
- The split is the same, now with `Hm := fun_mem_typed s f C' 0 Hmod …` and a generalization to `mi`, so the bound is on `|mi.BYTES|`. The trap step is `store_num_trap _ _ _ _ _ mi Hm …`.
- New value case: `Step.store_num_val (S;F) _ _ _ _ _ _ (proj_num__0 i ≠ none) Hfunsize (fun_with_mem.fun_with_mem_case_0 s f 0 _ _ _ (fun_mem_inv Hm).1) rfl`:
  - The only premise of `fun_with_mem`, `0 < |F.module.memaddrs|`, is the first conjunct of `fun_mem_inv Hm`.
  - The output state comes from the constructor: S with `mems[F.module.memaddrs[0]].data` spliced at `i+offset` with `b*`. `S'` and `F'` are inferred by unification.

#### `t_progress_be_store_pack` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for a packed store `iN.storeM memarg` (the `Instr_ok.store_pack` case of `t_progress_be`; same side conditions and conclusion shape as `t_progress_be_memory_size`). If `C ⊢ iN.storeM memarg : [i32 iN] → []` (`C.mems[0]` exists, `2^memarg.align ≤ M/8`), then every well-formed `S; F; (i32.const i) (iN.const c) (iN.storeM memarg)` steps. Statement unchanged.

**What broke and why.**
- "Invalid field `BYTES`" on `fun_mem …` in the bounds split.
- In `Step.store_pack_trap` the arguments shift: `by simp` lands on the meminst argument, and `wf_uN.uN_case_0 …` lands on `proj_num__0 i ≠ none`.
- Cause (as for store_val): `Step/store-pack-trap` gained `(var_0 : meminst)` and `fun_mem z 0 var_0`. `Step/store-pack-val` now targets the output of `fun_with_mem z 0 (i+offset) (M/8) b* var_0`, taking `var_0 : state` and that premise (second premise) instead of the old function `with_mem`.
- The errors are the same with the function views.

**Original proof sketch.**
- `vcs = [v1 v2]`, and `invert_typeof_I32` on v1 gives `i32.const n1`. Then split on `n1 + memarg.offset + M/8 > |$mem(z,0).BYTES|`.
- Trap case: `cases v_Inn`. For I32, `invert_typeof_I32 v2` gives `i32.const n2`; for I64, `invert_typeof_I64 v2` does the same. Then `Step.store_pack_trap`.
- Otherwise: again `cases v_Inn` and the same inversion of v2. Then `Step.store_pack_val (S;F) _ Inn …` with the premises `proj_num__0 i ≠ none`, `size Inn ≠ none` (by `simp`), `proj_num__0 c ≠ none`, and `b* = ibytes_ M (wrap__ |Inn| M c)` (`rfl`). The target is `with_mem (S;F) 0 (i+offset) (M/8) b*`.

**Current proof sketch.**
- The structure is the same, with `Hm := fun_mem_typed s f C' 0 Hmod …` and a generalization to `mi` before the split.
- Trap case: `store_pack_trap _ _ Inn _ _ _ mi Hm …` for each Inn.
- Value case, for each of I32 and I64: `store_pack_val (S;F) _ Inn _ _ _ _ _ (proj_num__0 i ≠ none) (fun_with_mem.fun_with_mem_case_0 s f 0 _ _ _ (fun_mem_inv Hm).1) (size …) (proj_num__0 c ≠ none) rfl`.
- As in store_val, the only premise of `fun_with_mem_case_0`, `0 < |F.module.memaddrs|`, comes from `fun_mem_inv Hm`, and the output store is the constructor's.

### 7.11 Q6b, `TypeProgress`: vector memory instructions (8 constructs)

#### `t_progress_be_vload_val` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `v128.load memarg`. This is the `Instr_ok.vload_val` case of `t_progress_be`, stated as the minor premise of `Instrs_ok.rec` for the motive `t_progress_be_P`; the typing rule is `Instr_ok/vload-val`: `C ⊢ v128.load memarg : [i32] → [v128]` if `C.mems[0] = mt` and `2^memarg.align ≤ |v128|/8`. Assume `C` is `C'` with its locals set to the types of `F.locals` and some labels/return (`upd_local_label_return`), `S ⊢ F.module : C'`, `⊢ S ok`, and the configuration `S; F; vcs v128.load memarg` is well-formed (`wf_config`) with `vcs : [i32]`. Then that configuration takes a step (the `right` disjunct of the motive). The statement is unchanged.

**What broke and why.** The first errors are the same with and without the function views; the proof broke ("sorried") in both cascades. Below, `(s;f)` abbreviates `state.mk_state s f` and `0` abbreviates `uN.mk_uN 0`.
- `(fun_mem (s;f) 0).BYTES`: invalid field `BYTES`, because the term now has type `meminst → Prop`. In the spec, `$mem((s; f), x) = s.MEMS[f.MODULE.MEMS[x]]` indexes twice. So `sideconditions_on_defs` replaced the total Lean function `fun_mem` (old body: `s.MEMS[f.MODULE.MEMS[x]!]!`) with a relation `fun_mem z x mi`. Its only constructor, `fun_mem_case_0`, requires `x < |F.module.memaddrs|` and `F.module.memaddrs[x] < |S.mems|`. Because the function is partial, it got no function view.
- `Step_read.vload_oob` and `Step_read.vload_val` gained an explicit argument `var_0 : meminst` and a new first premise `fun_mem z 0 var_0`. Their trap condition and byte slice now read `var_0.BYTES`. In the old argument list, `(by simp [proj_num__0])` fills the `var_0` slot ("`simp` made no progress"), and `Hfunsize : size V128 ≠ none` fills the `fun_mem` slot (application type mismatch).
- The proof also called `wf_config_mem_bytes`. That lemma had to be restated over the relation: it now takes the memory `mi` and a `fun_mem` witness.

**Original proof sketch.**
- Intros, then pick the step disjunct. Injectivity of `Htf` gives `ts1 = [i32]`. Of the cases for `vcs`, only `vcs = [v1]` is consistent with `typeof vcs = [i32]`, and `invert_typeof_I32` gives `v1 = i32.const n1`.
- The proof never used the validation bound `Hlen : 0 < |C.mems|` or `Hmod : S ⊢ F.module : C'`. Here `mem = fun_mem (s;f) 0` was always defined, because each out-of-range `!` lookup returned a default: address `0` from the module's list, or, from the store, the default `meminst`, whose byte list is empty. For the same reason `wf_config_mem_bytes` held at every index.
- `by_cases Hs : n1 + memarg.offset + |v128|/8 > |mem.data|`:
  - Out of bounds: `Step.read (Step_read.vload_oob …)` (`Step_read/vload-oob`, result `trap`), using `Hfunsize`, `Hs` and `wf_uN 32 0`.
  - In bounds: `Step.read (Step_read.vload_val …)` (`Step_read/vload-val`) with `c := inv_vbytes_ V128 (mem.data[n1+offset : 16])`.
    - `vbytes_(V128, c) = slice` follows from the axiom `vbytes_inv` and `list_slice_size`: by `¬Hs` the slice has exactly 16 bytes.
    - `wf_uN 128 c` follows from `inv_vbytes__is_wf`, `Forall_list_slice` and `wf_config_mem_bytes`: in a well-formed configuration, the memory's bytes are well-formed.

**Current proof sketch.** The case structure is unchanged. What is new:
- `subst Hcontext` makes `C.mems` definitionally `C'.mems` (`upd_local_label_return` changes only locals, labels and return), so `Hlen` serves as the bound for `C'`. Then `obtain ⟨mi, Hmem⟩ : ∃ mi, fun_mem (s;f) 0 mi := ⟨_, fun_mem_typed s f C' 0 Hmod Hlen⟩` gives `Hmem` for a fresh `mi`. The existential hides that `mi` is `S.mems[F.module.memaddrs[0]]`, so every fact about `mi` comes from `Hmem`.
  - `fun_mem_typed` gets the constructor's two bounds from `Moduleinst_ok_mem_addr`.
  - `0 < |F.module.memaddrs|` follows from `Hlen`, because `Moduleinst_ok_lengths` gives the instance's address list the length of `C'.mems`.
  - `F.module.memaddrs[0] < |S.mems|` comes from `minst_invert_mems`: every memory address of a typed module instance is a valid store address.
- The case split compares against `mi.BYTES.length`. Both rules receive `mi` and `Hmem` (`Step_read.vload_oob _ _ _ _ Hmem …`, `Step_read.vload_val _ _ _ _ _ Hmem …`), and `c` is read from `mi.BYTES`.
- Byte well-formedness uses the restated `wf_config_mem_bytes _ _ _ _ _ HWfConfig Hmem`; the memory `mi` is inferred from `Hmem`.

#### `t_progress_be_vload_pack` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `v128.load{M}x{N}_{sx} memarg` (Lean `VLOAD V128 (SHAPEX_ M N sx)`; case `Instr_ok.vload_pack`). The typing rule is `Instr_ok/vload-pack`: `[i32] → [v128]` if `C.mems[0] = mt` and `2^align ≤ M/8·N`. Under the hypotheses of `t_progress_be_P` (well-formed `S; F; vcs instr` with `vcs : [i32]`, `S ⊢ F.module : C'`, `⊢ S ok`), the configuration steps. The statement is unchanged.

**What broke and why.** The first errors are the same in both settings, and the proof broke in both cascades.
- Invalid field `BYTES` on `fun_mem (s;f) 0`, which is now a relation (see `t_progress_be_vload_val`).
- `Step_read.vload_shape_oob` gained `var_0 : meminst` and the `fun_mem` premise. In the old argument list, `(by simp [proj_num__0])` fills `var_0` (no progress), and `wf_uN.uN_case_0 32 0 …` lands in the `proj_num__0 i ≠ none` slot (type mismatch).
- The in-bounds branch also builds terms whose constructors changed shape:
  - `Step_read.vload_shape_val` gained `var_1 : Nat` with the premise `fun_jsize v_Jnn var_1`. The spec premise `$jsize(Jnn) = M·2` became `var_1 = M·2`, and the lanes became `extend__ M var_1 sx j`. It also gained `var_0 : meminst` with `fun_mem`.
  - `wf_shape.shape_case_0` and `wf_lane_.lane__case_0` gained an explicit lane width and a `fun_lsize` premise, because `$lsize` is now a relation.
  - `jsize`, used in `jsize Jn = M·2`, no longer exists in the model. Only the HelperLemmas function view restores it.

**Original proof sketch.**
- `vcs = [i32.const n1]`, as for `v128.load`.
- `by_cases Hs : n1 + offset + M·N/8 > |mem.data|`. Out of bounds: `Step_read.vload_shape_oob` (`Step_read/vload-shape-oob`, result `trap`).
- In bounds (`Hbnd`):
  - Inverting `wf_instr` gives `wf_vloadop_ V128 (SHAPE M X N sx)`. That gives `wf_sz M`, so `M ∈ {8,16,32,64}`, and the side condition `M·N = 128/2 ∧ N > 1` (`HMN'`: `M·N = 64`).
  - `HJ k`: the k-th chunk `inv_ibytes_ M (mem.data[n1+offset+k·M/8 : M/8])` is a well-formed `uN M`, by `inv_ibytes__is_wf`, `Forall_list_slice` and `wf_config_mem_bytes`.
- `M = 8/16/32` forces `N = 8/4/2` and lanes widened to `J = i16/i32/i64`, with `q = M/8`, `jsize J = 2M` and `wf_shape (J×N)`. `M = 64` forces `N = 1`, which contradicts `N > 1`.
- One shared step, `Step_read.vload_shape_val` (`Step_read/vload-shape-val`), with `j* = [inv_ibytes_ M chunk_k | k < N]`:
  - Per lane, `ibytes_(M, j_k) = chunk_k` by `ibytes_inv` and `list_slice_size`. Chunk `k` is in bounds because `(k+1)·q ≤ N·q` and `Hbnd`, after `HkM`/`HM`/`HMN8` normalize the `rat_to_nat` byte counts.
  - `jsize J = M·2` is `HJn`, and `c = inv_lanes_(J×N, extend__…)` holds by `rfl`.
  - `wf_shape` holds, and every extended lane is well-formed by `wf_lane_.lane__case_0`, `extend___is_wf` and `HJ`.
  - `N = |j*|`.

**Current proof sketch.** Same as before. What is new:
- After `subst Hcontext`, the memory witness `⟨mi, Hmem⟩` comes from `fun_mem_typed s f C' 0 Hmod Hlen`, as in `t_progress_be_vload_val`. `Hs`, `Hbnd`, the chunks and `HJ` use `mi.BYTES`, and `HJ` is proved via `wf_config_mem_bytes … HWfConfig Hmem`.
- `Step_read.vload_shape_oob … Hmem …`.
- `Step_read.vload_shape_val … Jn _ _ (fun_jsize_jsize Jn) Hmem …`. `fun_jsize_jsize` fixes the `fun_jsize` output to the view `jsize Jn`. So the unchanged `HJn : jsize Jn = M·2` discharges `var_1 = M·2`, and the lane terms are as before.
- `wf_shape.shape_case_0 _ _ _ (fun_lsize_lsize _) …` (three cases) and `wf_lane_.lane__case_0 _ _ _ _ (fun_lsize_lsize _) …` supply the lane width `lsize` and its `fun_lsize` witness.
- The `SHAPE 64 X 1` refutation is unchanged.

#### `t_progress_be_vload_splat` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `v128.load{N}_splat memarg` (Lean `VLOAD V128 (SPLAT N)`; case `Instr_ok.vload_splat`). The typing rule is `Instr_ok/vload-splat`: `[i32] → [v128]` if `C.mems[0] = mt` and `2^align ≤ N/8`. Under the hypotheses of `t_progress_be_P` with `vcs : [i32]`, the configuration steps. The statement is unchanged.

**What broke and why.** The first errors are the same in both settings, and the proof broke in both cascades.
- Invalid field `BYTES` on `fun_mem (s;f) 0`.
- `Step_read.vload_splat_oob` gained `var_0 : meminst` and `fun_mem`. `(by simp [proj_num__0])` fills `var_0` (no progress), and `wf_uN.uN_case_0 …` lands in the `proj_num__0 i ≠ none` slot (type mismatch).
- Also changed:
  - `Step_read.vload_splat_val` gained `var_1` with `fun_jsize v_Jnn var_1`; the premise `N = $jsize(Jnn)` became `v_N = var_1`. It also gained `var_0` with `fun_mem`.
  - The `wf_shape` and `wf_lane_` constructors gained `fun_lsize` premises.
  - `wf_config_mem_bytes` was restated, and `jsize` is gone from the model.

**Original proof sketch.**
- `vcs = [i32.const n1]`. `by_cases Hs : n1 + offset + N/8 > |mem.data|`. Out of bounds: `Step_read.vload_splat_oob` (result `trap`).
- In bounds:
  - `Hwfk`: `inv_ibytes_ N (mem.data[n1+offset : N/8])` is a well-formed `uN N`.
  - `wf_sz N`, obtained by inverting `wf_instr` and then `wf_vloadop_`, gives `N ∈ {8,16,32,64}`. So `(J, M) = (i8,16)/(i16,8)/(i32,4)/(i64,2)` with `N = jsize J`, `M = 128/N` and `wf_shape (J×M)`.
- After `subst`, one step `Step_read.vload_splat_val` (`Step_read/vload-splat-val`) with `j := inv_ibytes_ |J| slice`:
  - `ibytes_(N, j) = slice` by `ibytes_inv`, `list_slice_size` and `Hbnd`.
  - `N = jsize J` holds by `rfl`, and `M = 128/N` is `HvM`.
  - `c = inv_lanes_(J×M, j^M)` holds by `rfl`.
  - `wf_shape` holds, and the lane `mk_lane__0 J j` is well-formed by `mk_uN_eta`, `lane__case_0` and `Hwfk`.

**Current proof sketch.** Same as before. What is new:
- The memory witness `⟨mi, Hmem⟩` comes from `fun_mem_typed` (after `subst Hcontext`). The slices read `mi.BYTES`, and `Hwfk` is proved via `wf_config_mem_bytes … HWfConfig Hmem`.
- `Step_read.vload_splat_oob … Hmem …`.
- `Step_read.vload_splat_val … Jn vM _ _ (fun_jsize_jsize Jn) Hmem …`. Here `v_N = var_1` holds by `rfl`, because `N` was substituted by `jsize Jn`.
- `fun_lsize_lsize` witnesses in `wf_shape.shape_case_0` (four cases) and `wf_lane_.lane__case_0`.

#### `t_progress_be_vload_zero` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `v128.load{N}_zero memarg` (Lean `VLOAD V128 (ZERO N)`; case `Instr_ok.vload_zero`). The typing rule is `Instr_ok/vload-zero`: `[i32] → [v128]` if `C.mems[0] = mt` and `2^align ≤ N/8`. Under the hypotheses of `t_progress_be_P` with `vcs : [i32]`, the configuration steps. The statement is unchanged.

**What broke and why.** The errors are the same in both settings, and the proof broke in both cascades.
- Invalid field `BYTES` on `fun_mem (s;f) 0`, both in the trap condition and in `Hbnd`.
- `Step_read.vload_zero_oob` gained `var_0 : meminst` and a `fun_mem` premise, so `(by simp [proj_num__0])` fills `var_0` (no progress).
- `Step_read.vload_zero_val` changed the same way, and `wf_config_mem_bytes` was restated. No lane-size relation is involved.

**Original proof sketch.**
- `Htf` gives `[i32] → [v128]`. `List.map_eq_singleton_iff` and `invert_typeof_I32` give `vcs = [i32.const n1]`.
- `by_cases Hs : n1 + offset + N/8 > |mem.data|`. Out of bounds: `Step_read.vload_zero_oob` (result `trap`).
- In bounds: `Step_read.vload_zero_val` (`Step_read/vload-zero-val`) with `j := inv_ibytes_ N slice`:
  - `ibytes_(N, j) = slice` by `ibytes_inv` and `list_slice_size Hbnd`.
  - `c = extend__(N, 128, U, j)` holds by `rfl`.
  - `wf_uN N j` by `inv_ibytes__is_wf`, `Forall_list_slice` and `wf_config_mem_bytes`; plus `wf_uN 32 0`.

**Current proof sketch.** Same as before. What is new:
- `subst Hcontext`, then `⟨mi, Hmem⟩` from `fun_mem_typed s f C' 0 Hmod Hlen`.
- The case split is on `mi.BYTES.length`.
- The steps are `Step_read.vload_zero_oob _ _ _ _ _ Hmem …` and `Step_read.vload_zero_val _ _ _ _ _ _ _ Hmem …`, with the slice taken from `mi.BYTES`.
- `wf_config_mem_bytes s f _ 0 mi HWfConfig Hmem`.

#### `t_progress_be_vload_lane` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `v128.load{N}_lane memarg laneidx` (case `Instr_ok.vload_lane`). The typing rule is `Instr_ok/vload_lane`: `[i32 v128] → [v128]` if `C.mems[0] = mt`, `2^align ≤ N/8` and `laneidx < 128/N`. Under the hypotheses of `t_progress_be_P` with `vcs : [i32 v128]`, the configuration steps. The statement is unchanged.

**What broke and why.** The first errors are the same in both settings, and the proof broke in both cascades.
- Invalid field `BYTES` on `fun_mem (s;f) 0`, in the trap condition and in `Hbnd`; `Hwfk` reads the same field.
- `Step_read.vload_lane_oob` gained `var_0 : meminst` and a `fun_mem` premise, so `(by simp [proj_num__0])` lands in the `var_0` slot (no progress).
- Also changed:
  - `Step_read.vload_lane_val` gained `var_1` with `fun_jsize v_Jnn var_1`; the premise `v_N = var_1` replaces `v_N = jsize v_Jnn`. It also gained `var_0` with `fun_mem`.
  - The `wf_shape` and `wf_lane_` constructors gained `fun_lsize` premises.
  - `wf_config_mem_bytes` was restated.

**Original proof sketch.**
- `Htf` gives `[i32 v128] → [v128]`. `vcs = [v1, v2]` by `List.map_eq_cons_iff` and `List.map_eq_singleton_iff`. `invert_typeof_I32` gives `v1 = i32.const n1`, and `invert_typeof_V128` gives `v2 = v128.const c1`.
- `by_cases Hs : n1 + offset + N/8 > |mem.data|`. Out of bounds: `Step_read.vload_lane_oob` (result `trap`).
- In bounds:
  - `Hwfk`: the loaded `N`-bit value is well-formed.
  - `wf_sz N` comes from `wf_instr`, so `N ∈ {8,16,32,64}`.
- Each of the four cases makes its own `Step_read.vload_lane_val` step (`Step_read/vload_lane-val`), with `(J, M) = (i8,16)/(i16,8)/(i32,4)/(i64,2)` and `k := inv_ibytes_ N slice`:
  - `ibytes_inv` and `list_slice_size` give the byte premise.
  - `N = jsize J` holds by `rfl`, and `M = 128/N` by `norm_num`.
  - `c = inv_lanes_(J×M, lanes_(J×M, c1)[[laneidx] = k])` holds by `rfl`.
  - `wf_shape` comes from `shape_case_0`, and the new lane is well-formed by `Heta` and `Hwfk`.
- The validation bound `laneidx < 128/N` is never needed, because Lean's lane update (`List.modify`) is total.

**Current proof sketch.** Same as before. What is new:
- The memory witness comes from `fun_mem_typed`, after `subst Hcontext`.
- `Step_read.vload_lane_oob _ _ _ _ _ _ _ Hmem …`.
- Each step is now `Step_read.vload_lane_val … J M _ _ (fun_jsize_jsize _) Hmem …`. `v_N = var_1` still holds by `rfl`, because `jsize i8` computes to `8`, and likewise for the others.
- `fun_lsize_lsize` witnesses in `wf_shape.shape_case_0` and `wf_lane_.lane__case_0`.
- `wf_config_mem_bytes s f _ 0 mi HWfConfig Hmem`.

#### `t_progress_be_vstore` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `v128.store memarg` (case `Instr_ok.vstore`). The typing rule is `Instr_ok/vstore`: `[i32 v128] → []` if `C.mems[0] = mt` and `2^align ≤ |v128|/8`. Under the hypotheses of `t_progress_be_P` with `vcs : [i32 v128]`, the configuration steps. The statement is unchanged.

**What broke and why.** The errors are the same in both settings, and the proof broke in both cascades.
- `Step.vstore_val` implements `Step/vstore-val`, whose result is `$with_mem(z, 0, i+offset, |v128|/8, b*); ε`. It gained an explicit `var_0 : state` and the premise `fun_with_mem z 0 (i+offset) (|v128|/8) b* var_0`, which replaces the total function `with_mem` in its conclusion.
- The reason: the spec's `$with_mem((s; f), x, i, j, b*) = s[.MEMS[f.MODULE.MEMS[x]].BYTES[i : j] = b*]; f` reads `f.MODULE.MEMS[x]`. So it became the relation `fun_with_mem`, whose constructor `fun_with_mem_case_0` requires `x < |F.module.memaddrs|`.
- In the old argument list, `(by simp [proj_num__0])` fills `var_0` (no progress), and `Hfunsize` lands in the `proj_num__0 i ≠ none` slot (type mismatch). Lean also reports an `unsolved goals` error on the proof.

**Original proof sketch.**
- `Htf` gives `[i32 v128] → []`. `vcs = [i32.const n1, v128.const c2]` by `invert_typeof_I32` and `invert_typeof_V128`.
- The proof then steps directly by `Step.vstore_val`, with `b* = vbytes_(V128, c2)` by `rfl` and `Hfunsize`.
- There is no trap case and no memory lookup. Lean's `Step.vstore_val` has no bounds premise, and `with_mem` was total (`List.modify` plus the capped `splice`). So `Step.vstore_val` always applies, even out of bounds (where `Step.vstore_oob` applies too), and steps to `with_mem (s;f) 0 (n1+offset) 16 b*` with an empty instruction sequence. Rocq argues the same way.

**Current proof sketch.** Same as before. What is new:
- `subst Hcontext`, then `Hx : 0 < |F.module.memaddrs|` as `(Moduleinst_ok_mem_addr s f.MODULE C' 0 Hmod Hlen).1`. This is the validation bound `0 < |C.mems|` carried over along `S ⊢ F.module : C'`.
- The step is `Step.vstore_val _ _ _ _ _ _ (by simp [proj_num__0]) Hfunsize (fun_with_mem.fun_with_mem_case_0 s f _ _ _ _ Hx) rfl`. Its post-state is the one the constructor builds: `S` with `S.mems[F.module.memaddrs[0]].data` spliced.
- The store bound `F.module.memaddrs[0] < |S.mems|` is not needed.

#### `t_progress_be_vstore_lane` (TypeProgress; theorem) - re-proved

*Statement (Wasm 2.0 terms):* progress for `v128.store{N}_lane memarg laneidx` (case `Instr_ok.vstore_lane`). The typing rule is `Instr_ok/vstore_lane`: `[i32 v128] → []` if `C.mems[0] = mt`, `2^align ≤ N/8` and `laneidx < 128/N`. Under the hypotheses of `t_progress_be_P` with `vcs : [i32 v128]`, the configuration steps. The statement is unchanged.

**What broke and why.** The first errors are the same in both settings, and the proof broke in both cascades.
- Invalid field `BYTES` on `fun_mem (s;f) 0`, in the trap condition.
- `Step.vstore_lane_oob` gained `var_0 : meminst` and a `fun_mem` premise, so `(by simp [proj_num__0])` lands in the `var_0` slot (no progress).
- `wf_shape.shape_case_0 _ _ (wf_dim.dim_case_0 …) rfl` passes the `wf_dim` proof where the new explicit lane-width `Nat` is expected (type mismatch).
- The proof also calls `vstore_lane_progress`, which broke as well and was restated with a new first premise.

**Original proof sketch.**
- `vcs = [i32.const n1, v128.const c1]`, as for `v128.load{N}_lane`.
- `by_cases Hs : n1 + offset + N > |mem.data|`. The spec's `Step/vstore_lane-oob` compares `i + offset + N`, with `N` in bits, and the Lean split follows it. Out of bounds: `Step.vstore_lane_oob` (result `z; trap`).
- Otherwise: `Hs` itself is not used, because `Step.vstore_lane_val` has no bounds premise. `wf_sz N` comes from `wf_instr`.
- For `(J, M) = (i8,16)/(i16,8)/(i32,4)/(i64,2)`, apply `vstore_lane_progress s f n1 memarg laneidx c1 J M` with:
  - `wf_uN 128 c1`, from `invert_typeof_V128`;
  - `wf_shape (J×M)`;
  - `laneidx < M`, from validation's `laneidx < 128/N` by `norm_num` and `exact_mod_cast` (`omega` for i64);
  - `M = 128/|J|`, by `norm_num`.

**Current proof sketch.** Same as before. What is new:
- `subst Hcontext`, then `⟨mi, Hmem⟩` from `fun_mem_typed`, and `Hx : 0 < |F.module.memaddrs|` from `(fun_mem_inv Hmem).1`.
- The case split is on `mi.BYTES.length`. The trap step is `Step.vstore_lane_oob _ _ _ _ _ _ _ Hmem …`.
- The other branch calls the restated `vstore_lane_progress … J M Hx Hwf128 …`, with `wf_shape.shape_case_0 _ _ _ (fun_lsize_lsize _) …`.

#### `vstore_lane_progress` (TypeProgress; theorem) - restated and re-proved

*Statement (Wasm 2.0 terms):* Assume a frame `F` whose module has a memory (new), a well-formed 128-bit `c1`, a valid shape `J×M` with `M = 128/|J|`, and `laneidx < M`. Then `S; F; (i32.const n1) (v128.const c1) (v128.store{|J|}_lane memarg laneidx)` takes a step. The Lean statement gains a new first premise; the rest is unchanged:

```
old: wf_uN 128 c1 → wf_shape (shape.X (lanetype_Jnn J) (dim.mk_dim M)) → proj_uN_0 laneidx < M →
     (M : Rat) = 128 / (jsize J : Rat) → ∃ s' f' es', Step …
new: 0 < f.MODULE.MEMS.length → wf_uN 128 c1 → … (unchanged)
```

**What broke and why.**
- Without the function views, the statement does not elaborate. It mentions `jsize J`, and the new model has no `jsize`. The spec's `$jsize(Jnn) = $lsize(Jnn)` is now the relation `fun_jsize`, because `$lsize` uses the partial `$size` and became `fun_lsize`. Lean reports "function expected at `jsize`" (unknown identifier), so the cascade dropped the theorem.
- With the views, `jsize` comes from HelperLemmas, so the statement elaborates and only the proof breaks. `Step.vstore_lane_val` has two new explicit arguments:
  - `var_1 : Nat`, for `fun_jsize v_Jnn var_1`; `v_N = var_1` replaces `v_N = jsize v_Jnn`.
  - `var_0 : state`, for `fun_with_mem z 0 (i+offset) (N/8) b* var_0`, which replaces the total `with_mem` in the conclusion.
- The old `?_ rfl` therefore land in the `var_1`/`var_0` slots, and `rfl` is not a `state`. The new rule also lists the lane-index bound before `proj_lane__0 … ≠ none`.
- `fun_with_mem_case_0` needs `0 < |F.module.memaddrs|`, and the old hypotheses say nothing about `F`. That is why the statement had to change.

**Original proof sketch.**
- `lanes_nth_wf` (from `lanes__is_wf` and `lanes_len`) shows that lane `laneidx` of `lanes_(J×M, c1)` is a well-formed lane of type `J`. `wf_lane_Jnn_inv` and `wf_lane_Jnn_some` make it `mk_lane__0 J x` with `wf_uN |J| x`.
- Then one step `Step.vstore_lane_val (s;f) _ c1 (jsize J) memarg laneidx _ J M` (`Step/vstore_lane-val`), with premises:
  - `proj_num__0 ≠ none`, by `simp`;
  - `N = jsize J`, by `rfl`;
  - `M = 128/N`, which is `HM`;
  - `proj_lane__0 lane ≠ none`, via `Hx`;
  - `laneidx < |lanes|`, by `lanes_len` and `Hk`;
  - `b* = ibytes_(N, lanes[laneidx])`, by `rfl`;
  - `wf_uN N` of that lane, by rewriting with `Hx` and then `Hwx`.
- The post-state is `with_mem (s;f) 0 (n1+offset) (N/8) b*`. The rule has no memory-bounds premise and `with_mem` was total, so this step exists even out of bounds, where `Step.vstore_lane_oob` also applies. The lemma therefore needs no trap case.

**Current proof sketch.**
- Same lane facts.
- The step is `Step.vstore_lane_val … J M _ _ (fun_jsize_jsize J) ?_ (fun_with_mem.fun_with_mem_case_0 s f _ _ _ _ Hmems) rfl HM ?_ ?_ rfl ?_`:
  - `fun_jsize_jsize J` sets `var_1 := jsize J`, so `v_N = var_1` holds by `rfl`.
  - The post-state is the one `fun_with_mem_case_0` builds from the new premise `Hmems`.
  - The lane-index bound and the integer-lane premise follow in their new order; the rest is as before.
- The only caller, `t_progress_be_vstore_lane`, supplies `Hmems` from `fun_mem_inv` of its `fun_mem_typed` witness.

## 8. Evidence

In `claude-logging/verbatim_dialogue_log/bundle31/`:
- `evidence/outputs/`: the final build summary (errors, warnings and `sorry` count per module), the axiom
  audit, the default-value audits (starting state, first assembly, final), the cascade report and the
  first errors of the original proofs with and without the function views.
- `evidence/diffs_vs_original/`: `HelperLemmas`, `ExtensionLemmas`, `TypePreservation` and `TypeProgress`,
  unified diffs from the pre-repair files to the installed ones.
- `evidence/tools/`: the scripts (safety check, locked Lean runner, cascade, unit-level merge, final
  build and audits, post-merge patches) and the infrastructure parts as first written.
- `agent_logs/repair/` (the nine repair agents' results and assignments) and `agent_logs/report/` (the
  report writers', checkers', updater's and final checker's results).

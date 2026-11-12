# Progress port: deviations from the Rocq proof (bundle20)

Written for: the user and future sessions. This is the explicit list of deviations you asked for
("Try as far as possible to exactly match the Rocq proof, but you can deviate (and explicitly list
the deviations …)").
Reference: `spectec/test-rocq/theories/type_progress.v` at upstream `rocq-backend-proof-final`
`95c256c2c`. Lean: `spectec/src/test-lean-claude/TypeProgress.lean` (new this bundle).

## 0. How the signatures were made and checked

1. **Definitions (15):** hand-ported by the main thread and sanity-checked by evaluation (for
   example `split_vals`, `evens`, `odds`). They are placed at their Rocq positions.
2. **Lemma statements (190):** six subagents translated them in Rocq order. Each one compiled
   its chunk against the project before returning.
   - Every chunk was then checked by an **independent auditor** against the Rocq statements.
     Result: 0 problems in 5 chunks and 1 problem in chunk 4, which a fixer corrected
     (`Forall2_size_eq`, below).
   - Logs: `bundle20/agent_logs/psig-*.md`, `psig-audit-*.md`, `psig-fix-4.md`; full results in
     `agent_logs/progress_signatures_results.json`.
3. **`t_progress_be` / `t_progress_e` case statements (90):** generated **mechanically** from the
   types Lean prints for the minor premises of the mutual recursors `Instrs_ok.rec` and
   `Instrs_ok2.rec`. They therefore fit the recursors by construction.
   - The only text edits: the context literals got a `: context` ascription and were put on one
     line, and the 13 premises that the generated source writes with `Rat` casts were copied from
     the source verbatim, because the pretty-printer drops the casts.
4. **The motives and the four main statements** (`t_progress_be`, `Instr_ok_Instrs_ok`,
   `t_progress_e`, `t_progress`) were transcribed by hand and compared term by term with Rocq.

## 1. Structural deviations (proof architecture, no change to any Rocq statement)

| # | Rocq | Lean | Why |
|---|---|---|---|
| S1 | `t_progress_be` is one `Instrs_ok_ind'` application with ~70 bullets. Its motives `P`/`P0` are inline lambdas. | The motives are named defs `t_progress_be_P`/`_P0`, which take the unused derivation argument exactly as Rocq's do. There are 78 standalone **case lemmas** `t_progress_be_<rule>`. `t_progress_be` is one `Instrs_ok.rec` application to them. | The cases can be proved, checked and reviewed independently (and in parallel). Each case lemma's doc comment names its Rocq bullet. |
| S2 | `t_progress_e`: one `Admin_instrs_ok_ind'` application with motives `P`/`P0`/`P1`. | Defs `t_progress_e_P`/`_P0`/`_P1`, 12 case lemmas `t_progress_e_<rule>`, and `t_progress_e` as one `Instrs_ok2.rec` application. | Same as S1. The store is a *parameter* of Lean's mutual inductive, so the motives are used as `t_progress_e_P s`. Rocq's motives take `s` as an argument. |
| S3 | `Scheme Instr_ok_ind'`, `Scheme Instr_ok2_ind'` (+ `Admin_instrs_ok_ind'`, `Expr_ok2_ind'`) | Not ported (NOT PORTED comments in place) | Lean generates the mutual recursors itself. |
| S4 | 9 `Ltac`s (`invert_typeof_vcs`, `num_shapes`, `binop_wf`, `vunop_case`, `vlane_close`, `bit_close`, `vrelop_close`, `vcvtop_cases`, `vcvtop_cases_full`) | Not ported (NOT PORTED comments in place) | This is proof automation; the Lean proofs inline it. |
| S5 | `instr_eqb`, `eqinstrP` (bool equality on `instr` and its reflection lemma) | Not ported | Lean derives `DecidableEq instr` in the generated file. |
| S6 | `type_progress.v` does not import the preservation files. | `TypeProgress.lean` imports `TypePreservation`. | This makes Lean-only helpers available (`Moduleinst_ok_lengths`, `getElem?_eq_some_bang`, typing builders). No progress statement depends on a preservation result. |

## 2. Signature deviations (all documented in the Lean doc comments)

### 2.1 Forced by Lean's zip-based `Forall₂`

The generated `Forall₂ R l l'` is `∀ p ∈ l.zip l', R p.1 p.2`. Unlike Rocq's inductive `Forall2`,
it does not imply `|l| = |l'|`. The project precedents are `funcinst_same`, `Vals_ok`,
`wf_tableinsts_preserves` and, this bundle, `s_invert_*`.

| Lemma | Deviation | Effect |
|---|---|---|
| `Forall2_Val_ok_is_same_as_map` (v:795) | premise `hlen : v_t1.length = v_local_vals.length` added after the `Forall₂` | Without it the statement is false (`v_t1 = [t, t']`, `v_local_vals = [v]`). With it, equivalent to Rocq. |
| `Forall_exists_Forall2` (v:1865) | conclusion `Forall2 R la l` rendered as `(Forall₂ R la l ∧ la.length = l.length)` | Without it the conclusion is vacuous (`la := []`). With it, equivalent to Rocq. |
| `Forall_iabs_total` (v:1968) | same treatment of its existential `Forall2` | Same as above. The generated `fun_vunop_` iabs rules need that length. |
| `vcvtop_lanes_total` (v:2849) | conjunct `vs.length = L.length` added to the existential | Same as above. |
| `Forall2_size_eq` (v:1874) | **NOT PORTED** | The literal statement `Forall2 R la lb → |la| = |lb|` is false here. Adding `hlen` would make it return its premise. Callers use the length conjuncts above. This is the same decision as `Forall2_seq_size` (HelperLemmas). |
| `Forall2_size`, `Forall2_size2` (helper_lemmas.v; needed by progress) | ported to `HelperLemmas.lean` with `hlen` | Equivalent to Rocq. |

### 2.2 Type-level and notation differences

| Lemma / item | Deviation |
|---|---|
| `const_es_exists` (v:124) | Rocq returns a `sig` `{vs \| es = map admininstr_val vs}`; Lean states `∃ vs, …` (a theorem must be a `Prop`). The uses are inside proofs, where `∃` suffices. |
| `br_reduce_decidable`, `return_reduce_decidable` (v:666, 692) | Rocq's ssreflect `decidable` is the sumbool `{P} + {~P}`. Lean states `def … : Decidable (br_reduce es)`, the exact Type-level counterpart, so these are `def`s, not `theorem`s. If proved classically they need `noncomputable`, which changes nothing in the statement. |
| `length_size` (v:33) | **NOT PORTED**: a stdlib `length` vs mathcomp `size` bridge. Both are `List.length` in Lean. |
| Rocq bool predicates in `Prop` position (`is_true b`) | `b = true`. Rocq's bool `x != y` becomes `x ≠ y`. |
| Rocq `N`/`nat` | Lean `Nat` (the generated `N := Nat`). |
| Rocq `Q → N` coercion (`Z.to_N ∘ Qfloor`) | `rat_to_nat`, which is exactly that composite. |
| Rocq `eqType` binders (`evens_odds_concat`, `setproduct*_Forall`, `setproduct_nonempty`) | `Type`. The Lean generated defs take a plain `Type`, so the Lean statements are at least as general. |
| Rocq right-associative `++` | Lean's `++` is left-associative, so Rocq's grouping is kept with explicit parentheses (e.g. `vs ++ ([BR l] ++ es')`). |
| `size_list_repeat` (v:2568) | Ported, although it is core `List.length_replicate`, because Rocq proofs use it by name. |

## 3. Supporting changes outside `TypeProgress.lean`

- **`HelperLemmas.lean`:**
  - the 12 progress-only axioms of `axioms.v` (`ibits_inv`, `feq_bit` … `fge_bit`, `ishl_wf`,
    `ishr_wf`, `trunc_sat_total`, `demote_nonempty`, `promote_nonempty`). The statements match
    Rocq, and they constrain only functions that are `opaque` in Lean (`Axiom`s in Rocq). Each has
    an obvious joint model; the comment block gives the consistency argument.
  - `Forall2_size`, `Forall2_size2` (§2.1).
  - the correction of the two inconsistent axioms `ibytes_len'`/`ibytes_len''` and of
    `ibytes_inv`'s premise (preservation report, finding A).
- **`ExtensionLemmas.lean`:** `s_invert_*` now carry the length (preservation report, finding D).
  This matters here because Rocq's progress proof inverts `Store_ok`.
- **`TypePreservation.lean`:** the Lean-only helper `wf_config_frame` was renamed
  `wf_config_wf_frame`, freeing the name for Rocq's progress lemma `wf_config_frame` (v:870),
  which is a different statement.

## 4. Known-false cases (inherited from Rocq)

Rocq's `t_progress_be` is **`Admitted`**. Two of its subcases are false as the spec stands, with
mechanised counterexamples that are ported here as statements (`vload_shape64_wf`,
`vload_shape64_stuck`, `vcvtop_trunc_sat_i16_wf_instr`, `vcvtop_trunc_sat_i16_stuck`):

- **`t_progress_be_vload_pack`, subcase `VLOAD V128 (SHAPE 64 X 1)`:** the instruction is well
  formed, but the `vload-shape-val` rule needs a `Jnn` of size 128, so an in-bounds access has no
  reduction. Rocq's `admit` is at v:5208.
- **`t_progress_be_vcvtop`, subcase `F32 X 4 → I16 X 8 TRUNC_SAT … ZERO`:** the instruction is
  well formed, but `$lcvtop__` defines `TRUNC_SAT` only for `Inn` destinations. Rocq's `admit`
  is at v:4319.

These subcases stay `sorry`, each with a comment naming its Rocq `admit` and counterexample
lemma, and **`t_progress` is therefore false in those two cases in Rocq and Lean alike**. That is
a spec issue for you to decide on, not a porting gap. In addition, `t_progress` inherits the
coverage limits found in the preservation audit (no `$invoke` configuration, no immutable globals).

## 5. Status

See `progress_port_status.md` (written at the end of the proof phase) for which bodies are
proved.

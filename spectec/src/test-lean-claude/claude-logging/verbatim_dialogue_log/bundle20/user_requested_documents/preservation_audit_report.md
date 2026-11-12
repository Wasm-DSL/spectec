# Preservation audit report (bundle20)

Written for: the user (project owner), and anyone checking the Lean preservation proof by hand.
Date: 2026-10-05. References: Rocq `rocq-backend-proof-final` @ `95c256c2c` (checked this turn:
identical to the local `spectec/test-rocq/theories/`) and Isabelle `isabelle-mech-backend` @
`41e27cc54` (`spectec/isabelle_type_safety_proof`).

## 0. Bottom line

**Preservation is meaningfully complete and makes sense.**

- **Same statement everywhere.** `TLC.t_preservation : Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts`
  says the same as Rocq `t_preservation` and Isabelle `preservation`. The `Config_ok` it talks
  about corresponds one-to-one with Rocq's generated `Config_ok`.
- **It is not vacuous.** A witness, machine-checked and with sorry-free hypotheses, shows the
  hypotheses can hold. It is in `preservation_nonvacuity_witness.lean` next to this report, and
  I re-ran it against the final build.
- **Its trust boundary is exactly Rocq's.** The only `sorry`s it rests on are 33 generated
  `*_is_wf` theorems that Rocq also leaves `Admitted`:
  - `Step_read_is_wf` (the known memory.fill/copy/init 2^32 corner case, awaiting your spec fix);
  - 32 well-formedness facts about numeric functions that are `opaque` in the generated Lean and
    `Axiom`s in Rocq.

  It uses no custom `axiom`. The project contains no trust-expanding construct (`native_decide`,
  `implemented_by`, `unsafe`, …).
- **Signatures match Rocq.** No signature on the preservation chain differs from Rocq except
  the documented deviations, which are the length facts made necessary by Lean's zip-based
  `Forall₂`.

**What the audit found** (details in §5):

| # | Finding | Severity | Status |
|---|---|---|---|
| A | Two ported axioms, `ibytes_len'` and `ibytes_len''`, were **inconsistent**: each derived `False`, machine-checked. The cause was a misreading of Rocq's `\|x\| = q` as exact when Rocq floors it. | critical for the project's consistency; **not** used by preservation or by anything else | **fixed** (restated with Rocq's floor semantics; `ibytes_inv`'s premise also corrected) |
| B | Generated `Moduleinst_ok` has a hoisted "address list non-empty" premise that the spec does not have, so **no `$invoke` configuration is ever `Config_ok`**. | major (limits coverage), **shared by Lean, Rocq and Isabelle**; a SpecTec middle-end artifact | reported (yours to fix upstream). Confirmed independently by 2 auditors and 2 verifiers, root cause traced, machine-checked. |
| C | Generated `Globaltype_ok` only admits **mutable** globals (spec: `MUT? t`), so stores with immutable globals are never `Store_ok`. | major (limits coverage), **shared by all three backends** | reported (yours to fix upstream). Confirmed by a verifier, machine-checked. |
| D | `s_invert_funcs/_globals/_mems/_tables` are **vacuous** in Lean: `∃ xs, Forall₂ P s.X xs` holds with `xs := []`. | major as statements (confirmed by a verifier); **unused**, so no effect on preservation | **fixed**: a length conjunct was added inside the existential, proved from `Store_ok`'s length premises, with a deviation note. The proofs are axiom-clean. |
| E | Many small documentation problems: 166 of 278 Rocq line citations point at older checkouts; stale file headers; a few undocumented reshapes. | minor | listed in §5.4 for a cleanup pass |

Note the distinction: B and C make the theorem cover **fewer** configurations than the spec
intends. They make it neither false nor vacuous, and Rocq's and Isabelle's theorems have exactly
the same limitation.

## 1. What was checked, and how

Following your guidance, signatures were checked and proof bodies were not read, except to look
for `sorry`, axioms and trust-expanding constructs (Lean has proof irrelevance and the kernel
re-checks every proof).

| Dimension | Done by | Result |
|---|---|---|
| Lean↔Rocq signatures, `TypePreservation` and `TypePreservationPure` | subagent `sig-tp-tpp` | 0 mismatches. 35/36 and 76/77 matched; the missing two are `Qfloor_add_Z` (a Q-arithmetic bridge) and an Ltac. All 103 Lean-only helpers are labelled and plausible. |
| Lean↔Rocq signatures, `ExtensionLemmas` | `sig-ext` | 77/91 name-matched pairs identical. The rest are documented reshapes and minor items, plus finding D. The 27 unmatched Rocq lemmas are all justified. |
| Lean↔Rocq signatures, `TypingLemmas`, `Subtyping`, `HelperLemmas` (+ `axioms.v`) | `sig-typing-base` | All statements match except 4 unused trivial restatements. Axioms: finding A, plus `ibytes_inv`'s weaker premise (now fixed). |
| Generated model (`wasm2.0.lean` vs `wasm.v`) | `audit-model`, plus my own script | 1:1 correspondence. Constructor names and order are identical for `Instr_ok` (73), `Instrs_ok` (5), `Instr_ok2` (6), `Instrs_ok2` (5), `Expr_ok2` (1), `Step_pure` (54), `Step_read` (47) and `Step` (23). Premise "fingerprints" are identical for all 346 common inductives. The 64 `opaque`s are exactly Rocq's 64 `Axiom`s. |
| Isabelle comparison | `audit-isabelle` | Same statement, same relations. Lean proves nearly everything Isabelle leaves `sorry` (§2.3). |
| Non-vacuity | `audit-nonvacuity` (ran Lean) | Witness compiles with sorry-free hypotheses. It led to findings B and C. |
| Trust and hygiene | main thread | See §3. |
| Adversarial verification | 1–2 verifiers per major finding | All four major findings confirmed: B twice, C once, D once. No finding was refuted. |

All subagents worked read-only. Each ran the safety check at start and end and logged under
`bundle20/agent_logs/`. Every check verified "zero new changes outside
`spectec/src/test-lean-claude`".

## 2. The generated model: does `Config_ok` mean the same thing in Lean as in Rocq?

### 2.1 Zip-based `Forall₂`

The generated `Forall₂ P xs ys := ∀ p ∈ xs.zip ys, P p.1 p.2` does not force equal lengths,
whereas Rocq's inductive `Forall2` and Isabelle's `list_all2` do. The worry is that this makes the
Lean relations weaker. It does not:

- 391 of the 404 `Forall₂`/`Forall₃` uses inside generated constructors come with a
  generator-emitted `List.length xs = List.length ys` premise on exactly the paired lists.
- That covers every use in `Store_ok` (6), `Moduleinst_ok` (6), `Frame_ok`, `Resulttype_sub`,
  `Module_ok` and the `Step` rules.
- Of the other 13, 3 are length-forced by other premises and 10 are in `fun_instantiate`, which
  is off the preservation path. In those 10 the zip encoding *is* weaker than Rocq; this only
  matters if you ever attempt instantiation soundness.
- Lemma-level uses of `Forall₂` that need a length carry an explicit `hlen` or go through
  `Vals_ok`. These are the documented deviations.

### 2.2 Other backend differences, all checked equivalent on the preservation path

- `with_mem` uses your clamped `splice` (length-preserving; `HelperLemmas.splice_eq_list_slice_update`
  proves it equal to Rocq's `list_slice_update`).
- `rat_to_nat` (your definition) equals Rocq's `Z.to_N ∘ Qfloor` coercion on every rational.
- `holds_upto` and `List_Foralli` are rendered via `List.range`.
- `Step_read_is_wf`/`Step_is_wf` carry Rocq's hand-added `Store_ok (fun_store z)` premise.

Isabelle's `step_wf`/`Step_read_is_wf` lack that premise and are **false** as stated (table.size
pushes `|REFS|` unbounded). This independently confirms that Rocq's and Lean's re-signing is
needed.

### 2.3 Isabelle

`preservation` has the same quantifiers, hypotheses and fixed result type `ts` as Lean's
theorem; only the argument order differs. The decomposition maps cleanly:

| Isabelle | Lean |
|---|---|
| `e_preservation` | `t_preservation_type` |
| `e_preservation_locals` | `t_preservation_vs_type` |
| `step_wf` | `Step_is_wf` |
| the `sorry` at Preservation.thy:5989 | `store_extension_reduce` + `Extend_store_moduleinst` |

Isabelle leaves these `sorry` and Lean proves them:
- `Limits_sub` reflexivity and transitivity;
- 20 of the 23 cases of `reduce_store_extension`;
- `store_extension_typing`;
- the memory.copy/init typing cases.

Isabelle hits the same 2^32 memory.fill corner case (Preservation.thy:5197).

## 3. Trust boundary (verified in the main thread)

- `#print axioms TLC.t_preservation` gives `[propext, sorryAx, Classical.choice, Quot.sound]`.
  Same for `store_extension_reduce`, `t_pure_preservation`, `t_read_preservation` and
  `t_preservation_type`.
- The `sorry` dependencies, from the `#sorry_deps` meta-program, are exactly 33:
  - `Step_read_is_wf`;
  - the `*_is_wf` of `convert__`, `demote__`, `extend__`, `fabs_`, `fceil_`, `ffloor_`,
    `fnearest_`, `fneg_`, `fsqrt_`, `ftrunc_`, `iand_`, `iandnot_`, `ibitselect_`, `ibytes_`,
    `iclz_`, `ictz_`, `inot_`, `inv_lanes_`, `ior_`, `ipopcnt_`, `irev_`, `ishl_`, `ishr_`,
    `ixor_`, `lanes_`, `nbytes_`, `promote__`, `reinterpret__`, `trunc__`, `trunc_sat__`,
    `vbytes_`, `wrap__`.
- The 63 `sorry` theorems in `wasm2.0.lean` are exactly the 63 `Admitted` theorems in `wasm.v`
  (set comparison by script). No `opaque` body contains `sorry`.
- None of `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, `partial def`,
  `ofReduceBool`, `debug.skipKernelTC`, custom `macro`/`syntax`/`elab` appears in any of the 8
  Lean files or the lakefile. There is one harmless `set_option maxHeartbeats`.
  `ExtendedDeriveDecEq.lean` generates kernel-checked `DecidableEq` instances, without unsafe
  bridges.
- The 16 unused `sorry` lemmas are marked `-- TODO FROM USER: MARKED FOR DELETION BECAUSE
  UNUSED`, as you asked (15 in `HelperLemmas`, `Val_ok_store` in `ExtensionLemmas`). Nothing
  references them. Several are false under the zip-based `Forall₂`, so deleting them is right.

## 4. How to check the preservation proof by hand

You do not need to read proof bodies. The review has three jobs: confirm that the top-level
statement says what you think it says, that everything it rests on is proved or an accepted gap,
and that the intermediate statements are the right ones.

### 4.1 Overall shape (top-down)

```
t_preservation  (TypePreservation.lean:2699)          Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts
│  Unpacks Config_ok → State_ok → Store_ok + Frame_ok (Moduleinst_ok, locals typed) + Expr_ok2 (Instrs_ok2),
│  then re-packs the same structure for c2 from:
├─ store_extension_reduce   (TP:1611)   Step ⇒ Extend_store s s' ∧ Store_ok s'
│   └─ store_extension_reduce_aux (TP:1438): induction on the Step derivation
│        (equational premises c1 = …, c2 = … encode Rocq's `dependent induction`)
│        ├─ congruence rules (label/frame/instrs context): the IH
│        ├─ store-writing rules → one lemma each: global_set_store_ok, table_set_store_ok,
│        │   table_grow_store_ok, elem_drop_store_ok, data_drop_store_ok,
│        │   with_mem_store_ok (TP:1341, the 4 store rules), memory_grow_store_ok (TP:1355)
│        └─ every other rule: store unchanged ⇒ Extend_store_refl
├─ reduce_inst_unchanged    (TP:536)    a step never changes the frame's MODULE
├─ Extend_store_moduleinst  (ExtensionLemmas.lean:1724)  Moduleinst_ok survives store extension
├─ t_preservation_vs_type   (TP:227)    the locals stay well-typed (Vals_ok) across a step
└─ t_preservation_type      (TP:2679)   the instruction sequence keeps its type
    └─ t_preservation_type_aux (TP:2422): induction on Step
         ├─ Step.pure  → t_pure_preservation (TypePreservationPure.lean:1858): case split over the
         │               54 Step_pure rules, one Step_pure__*_preserves lemma per rule
         ├─ Step.read  → t_read_preservation (TP:2028): case split over the 47 Step_read rules
         ├─ congruence rules (ctxt_label / ctxt_frame / ctxt_instrs): IH + typing decomposition
         └─ store-writing rules: the reduct is [] or a constant, typed directly
```

The well-formedness of the post-state (`wf_config c2`, part of `Config_ok`) comes from the
generated `Step_is_wf` (`wasm2.0.lean`:16045, proved). Its `read` case calls the generated
`Step_read_is_wf` (16034), which is the known `sorry`.

### 4.2 Recommended reading order (about a day)

1. **The definitions behind the statement** (`wasm2.0.lean`):
   - `Forall`/`Forall₂`/`Forall₃` (lines 17-25). Read these first: they are unusual (§2.1).
   - `Config_ok` (16325), `State_ok` (16315), `Frame_ok` (15743), `Store_ok` (15992),
     `Moduleinst_ok` (15671). Note the line-15690 premise of finding B.
   - `Val_ok`, `Ref_ok`, `Externaddr_ok` (15547-15610); `Instr_ok2`, `Instrs_ok2`, `Expr_ok2`
     (15785-15915); `Extend_store` (16289).

   Compare each with `wasm.v` (Config_ok 18230, State_ok 18221, Frame_ok 17186, Store_ok 17330,
   Moduleinst_ok 17155, Instr_ok2 17198, Extend_store 18196).
2. **`t_preservation` itself** (TP:2699-2751). It is a short composition, and reading it shows
   exactly which fact flows where.
3. **The five main lemma statements** it calls (TP:1611, 536, 227, 2679; ExtensionLemmas.lean:1724).
   They match Rocq; the documented deviations are in §4.4.
4. **The trust boundary.** Run `#print axioms TLC.t_preservation`; you should see what §3 lists.
   To list the `sorry`s, use the `#sorry_deps` program in
   `bundle18/user_requested_documents/insights_for_next_turn.md` §6.
5. **Non-vacuity.** Run `lake env lean <path>/preservation_nonvacuity_witness.lean` from
   `spectec/src/test-lean-claude`. It is about 280 lines and readable top to bottom.
6. Optional: one representative case per family, for example:
   - `Step_pure__select_preserves_helper` (pure);
   - the `table_get_val` case of `t_read_preservation` (read);
   - `table_grow_store_ok` (store).

### 4.3 Custom infrastructure and design patterns to recognise

| Pattern | Where | Why it exists |
|---|---|---|
| **Zip-based `Forall₂`** with explicit lengths | wasm2.0.lean:20; `Vals_ok` (TypingLemmas.lean:1775); `Moduleinst_ok_lengths` (TP:408); `hlen` premises | This is how the backend renders spec iterations. It is sound only together with the generator's length premises (§2.1). |
| **`_aux` lemmas with equational premises** | `store_extension_reduce_aux`, `t_preservation_type_aux`, `reduce_inst_unchanged_aux`, `t_preservation_vs_type'_aux`, `Externaddr_invert_*_aux` | Lean's `induction` cannot handle an indexed hypothesis like `Step (mk_config (mk_state s f) ais) …`. The `_aux` lemma generalises the indices and adds `c1 = …` premises, which is the Lean form of Rocq's `dependent induction`. The public lemma instantiates it at `rfl`. |
| **Auto-generated mutual recursors** | `Extend_store_ais` (ExtensionLemmas.lean:1842) via `Instrs_ok2.rec` | Rocq needs a hand-written `Scheme`; Lean generates the recursor itself, with the store as a parameter. |
| **Bare-variable inversion helpers** (`*_ok_invert`, `wf_*_parts`, `limits_ok_invert`) | ExtensionLemmas.lean ~130-300 | Lean's `cases` fails when an inductive index is an opaque term such as `l[i]!`. Each inversion is done once over plain variables. This is a proof technique only. |
| **Templates A/B/C** | HelperLemmas.lean:42-110 (`getElem!_modify_eq_or_ne`, `mem_zip_modify*`); ExtensionLemmas.lean:533 (`Externaddr_invert_*`, a Rocq port) | These bridge list updates and zips for every "update one store component" lemma, and invert external-address typing. |
| **Store plumbing** | TP:298-420 (`Store_ok_parts`, `Store_ok_of_parts`, `Extend_store_of_parts`, `wf_store_with_*`) | They split `Store_ok`/`Extend_store` into per-component facts and reassemble them, so each store case is about 30 lines. |
| **Principal typing + subtyping** | TypingLemmas.lean (`ai_principal_typing` :311, `ais_composition_typing` :1254, `ais_single_typing_inversion` :1344, `construct_ais_*`); Subtyping.lean (`instrtype_sub` :46, `instrtype_sub_compose_ge` :424) | This is Rocq's method, ported: invert the redex's typing to its principal type, rebuild the reduct's typing, and close the gap with `instrtype_sub`. |
| **`ais_*` / `pt_*` / `inv_*` builders** | TP:687-900, 1635-2020 (Lean-only sections) | Small typing constructors and principal-type readers that keep the 47 `t_read_preservation` cases short. |
| **Hand-written blocks inside the generated file** | wasm2.0.lean, five blocks headed "Hand-written helper lemmas … (bundle19; not generated)", plus the re-signed `Step_*_is_wf` | Regenerating the file erases them; `bundle19/…/wasm2.0_hand_edits.patch` restores them. |

### 4.4 Documented signature deviations from Rocq (all intended)

- `t_read_preservation` takes `Vals_ok` (length + `Forall₂`) instead of Rocq's bare `Forall2`.
- `wf_tableinsts_preserves`, `wf_memoryinsts_preserves` and `funcinst_same` take `hlen`.
- `mem_store_extension` uses a `Nat` length where Rocq has `Q`; this is equivalent.
- `store_extension_reduce` is proved without `Step_is_wf`. This is a proof route, not a
  signature change.
- `Step_is_wf`/`Step_read_is_wf` take `Store_ok (fun_store z)`, as in Rocq's hand edit.
- `construct_meminsts_grow` takes `Option uN`, as in Rocq.

### 4.5 Ten things worth checking by hand

1. `Forall₂` is zip-based. Check that the length premises in §2.1 really are there in
   `Store_ok`, `Moduleinst_ok` and `Frame_ok`.
2. The `Config_ok`/`State_ok`/`Frame_ok`/`Expr_ok2` chain: `ts` is fixed across the step, and
   `Frame_ok` ties the frame's locals to the context's `LOCALS`.
3. `Step` has 23 rules. The congruence rules carry `wf_config` premises (as Rocq's do), and
   `with_mem` is length-preserving.
4. The re-signed `Step_is_wf`/`Step_read_is_wf` (wasm2.0.lean:16034-16060).
5. `#print axioms TLC.t_preservation` shows no project axiom.
6. The `t_read_preservation` deviation (`Vals_ok`).
7. `store_extension_reduce`'s statement: `Extend_store s s' ∧ Store_ok s'`.
8. `rat_to_nat` (wasm2.0.lean:9), which `memory_grow_store_ok` relies on.
9. The 63 `sorry`s in `wasm2.0.lean` are exactly Rocq's `Admitted`, and 33 of them are on this
   path.
10. The coverage limits of findings B and C: what the theorem does **not** talk about.

## 5. Findings in detail

### 5.1 A: inconsistent axioms (fixed)

`HelperLemmas.ibytes_len'` and `ibytes_len''` stated `((ibytes_ v_n …).length : Rat) = (v_n : Rat) / 8`.
At `v_n = 1` that equates a natural number with `1/8`, which gives `False`; this was
machine-checked in a scratch file.

In Rocq, `|x| = (v_n / 8)%Q` compares an `N` with a `Q` coerced through `Qfloor` and `Z.to_N`
(wasm.v:194-200, 309), so it is a floored equation, and consistent.

- **Fix:** both axioms are now `(ibytes_ v_n …).length = rat_to_nat ((v_n : Rat) / 8)`.
  `rat_to_nat` is exactly `Z.to_N ∘ Qfloor`. The same correction was applied to `ibytes_inv`'s
  premise, which was consistent but strictly weaker than Rocq's.
- **Checks:** the old `False` derivation no longer type-checks, and the rebuild was clean.
- **Effect on proofs:** none. No proof ever used these axioms, and `t_preservation`'s axioms are
  unchanged.
- **Consistency of the others:** the remaining axioms, including the 12 progress-only axioms added
  this bundle (§6), each have an obvious model consistent with one another. For example, byte
  encodings are mutually inverse bijections, comparisons return 0 or 1, and saturating
  truncation returns `some 0`.

### 5.2 B: `Moduleinst_ok` non-emptiness (upstream, all backends)

The generated `Moduleinst_ok` (wasm2.0.lean:15690; Rocq wasm.v:17174; Isabelle thy:13634) has

`List.length (GLOBAL addrs ++ MEM addrs ++ TABLE addrs ++ FUNC addrs) > 0`.

The spec rule (B-soundness.spectec:230) only has the per-export membership premise
`(if exportinst.ADDR <- (GLOBAL globaladdr)* …)*`. That premise is vacuous when there are no
exports.

- **Cause:** `middlend/sideconditions.ml:62-63` emits `|xs| > 0` for every membership `x <- xs`.
  The `iterPr` smart constructor (l.21-28) then drops the unused iteration variable and, because
  `List <= List1`, returns the bare premise. This hoists it out of a `*` iteration that may have
  zero elements. The pass is shared by the Rocq and Lean backends (main.ml:317-319).
- **Consequence:** a frame whose module has no globals, memories, tables or functions is never
  `Config_ok`. `fun_invoke` (wasm2.0.lean:15452-15484) builds exactly such a frame. So
  `t_preservation`, and any progress theorem, **never applies to the initial configuration of an
  invocation**; it applies from the callee's frame onward. This is machine-checked
  (`invoke_config_not_ok` in the witness file).
- **Status:** confirmed by `audit-isabelle`, `audit-nonvacuity` and two verifiers.
- **Suggestion:** fix `iterPr`/`flatten_empty_iter` upstream. No Lean-side change, to stay in
  correspondence with Rocq.

### 5.3 C: `Globaltype_ok` only admits mutable globals (upstream, all backends)

The spec says `|- MUT? t : OK`. Every backend generates a single constructor with `Some MUT`
(wasm2.0.lean:12688; wasm.v:14686; Isabelle thy:11394).

- `Store_ok` requires `Globalinst_ok`, which requires `Globaltype_ok`. So any store with an
  immutable global is not `Store_ok`, and no configuration over it is `Config_ok`. This is
  machine-checked (`immutable_globaltype_not_ok`, `s_imm_not_ok`).
- `Global_ok` itself leaves mutability free, so this is clearly an artifact. Probably `MUT?` with
  no iteration variable is rendered as the constant `Some MUT`; the root cause was not traced.
- The hand-written proofs never mention `Globaltype_ok`, so an upstream fix should be cheap for
  them.

### 5.4 D and E (Lean-side, minor or unused)

**D: `s_invert_*` are vacuous.** `s_invert_funcs/_globals/_mems/_tables` (ExtensionLemmas) state
`∃ xs, Forall₂ P s.X xs`, which `xs := []` satisfies for any store. Rocq's inductive `Forall2`
makes the Rocq versions meaningful.

- They are unused, so preservation is unaffected.
- **Fixed:** the statements are now `∃ xs, s.X.length = xs.length ∧ Forall₂ …`, proved from
  `Store_ok`'s own length premises, with a "Deviation" doc note. The proofs use only standard
  axioms.
- A related, non-vacuous point: `minst_invert_*` also drop Rocq's implicit length. Their callers
  get it from `Moduleinst_ok_lengths`; doc notes saying so were added.

**E: documentation cleanup**, suggested for a later pass:
- 166 of 278 `<file>.v:<line>` citations carry line numbers from older Rocq checkouts. None
  names the wrong lemma.
- 6 live lemmas cite Rocq lemmas that were removed upstream; they should be relabelled
  "Lean-only".
- File headers in all six files still say "Phase 1 … proofs `sorry`".
- `num_default`'s doc claims a use that does not exist.
- `proj_identity` is specialised to `valtype`, which is harmless but undocumented.
- The four unused `upd_*_is_same_as_append` lemmas restate the record update rather than Rocq's
  context-append equation.
- The datas cluster hard-codes `datatype.OK`. This was known; it is equivalent but needlessly
  un-Rocq-like.
- `memory_grow_mem_extension` uses `Nat` for Rocq's `Q` without saying so.
- The packed-LOAD arms of `ai_principal_typing` are stronger than Rocq's, but only in uninhabited
  cases.

**Also reported:** a spec typo transcribed faithfully by all backends. `vstore_lane-oob` adds `N`
bits where it should add `N/8` bytes. It does not affect preservation.

## 6. What changed in the Lean files this turn (preservation side)

- `HelperLemmas.lean`:
  - the 15 deletion markers;
  - axioms `ibytes_len'`, `ibytes_len''` and `ibytes_inv` corrected (finding A), and the axiom-block
    header corrected;
  - added `Forall2_size`/`Forall2_size2` (with `hlen`; Rocq ports needed by progress) and a
    NOT-PORTED note for `Forall2_seq_size`;
  - added the 12 progress-only axioms of `axioms.v` (`ibits_inv`, `feq/fne/flt/fgt/fle/fge_bit`,
    `ishl_wf`, `ishr_wf`, `trunc_sat_total`, `demote_nonempty`, `promote_nonempty`).
- `ExtensionLemmas.lean`: 1 deletion marker; finding D fixed (`s_invert_*`); doc notes on `minst_invert_*`.
- `TypePreservation.lean`: the Lean-only helper `wf_config_frame` was renamed to
  `wf_config_wf_frame`, freeing the Rocq name for the progress lemma of that name.
- `lakefile.lean`: added the new `TypeProgress` module.

After each change `lake build` was clean, `#print axioms TLC.t_preservation` was unchanged, and
the safety check verified nothing changed outside `spectec/src/test-lean-claude`.

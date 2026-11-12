# Insights for the next turn (written at the end of bundle16)

Written for: **whoever picks this up next — very possibly a different session,
a smaller model, or both.** Assume you have the Lean files and the logs but
none of my working memory. Everything below is hard-won and is *not* visible
from reading the Lean code alone. Read §1-§3 before writing a single tactic;
they are where almost all of my wasted iterations went.

---

## 0. Where things stand (one paragraph)

`lake build` is clean. 27 `sorry`s remain project-wide, down from 83 at this
bundle's start. **Only 5 are genuine remaining work**, all in
`TypePreservationPure.lean` (`Step_pure__br_zero_preserves`,
`Step_pure__br_succ_preserves`, `Step_pure__br_table_lt_preserves`,
`Step_pure__br_table_ge_preserves`, `Step_pure__return_label_preserves`).
`ExtensionLemmas.lean` went 76 → 2 and `TypePreservation.lean` 12 → 3, and both
remainders are non-targets (deliberate Rocq-`Admitted` mirrors, or signatures
upstream has dropped). **The top-level theorem `t_preservation` is proved.** See
`proof_dependencies_v5.md` and `proof_prioritization_v6.md` (same folder).

---

## 1. STANDING INSTRUCTIONS — do not skip these

These are the user's, carried across every bundle. Violating them is worse than
proving nothing.

1. **Never modify anything outside `spectec/src/test-lean-claude`.** Run
   `bash spectec/src/test-lean-claude/claude-logging/safety-checks/check.sh`
   after every batch of edits; it auto-writes a timestamped log into
   `claude-logging/safety-checks/`. **Verify the output, don't just run it.**
   Recipe for verifying:
   ```bash
   cd .../claude-logging/safety-checks
   diff <(grep -E "^( M | D |A )" <FIRST-check-of-your-turn>.txt | grep -v "src/test-lean-claude") \
        <(grep -E "^( M | D |A )" <LATEST-check>.txt         | grep -v "src/test-lean-claude")
   ```
   Identical output ⇒ you introduced no out-of-target changes. **Known
   pre-existing (NOT yours, do not "fix"):** `M spectec/test-lean/todaywasm2.0.lean`
   and `D spectec/test-lean/todaywasm3.0.lean`, plus a large set of untracked
   `??` scratch files at the repo root. These were already present before
   bundle16 began.
2. **If you spawn any subagent / other LLM, you MUST brief it on #1** and
   require it to run its own `check.sh` and log the result.
3. **Log every exchange verbatim.** New folder per exchange:
   `claude-logging/verbatim_dialogue_log/bundleN/` containing `prompt_N.md`,
   `response_N.md`, `response_N_modelinfo.md`. Mid-turn user messages and
   subagent hand-backs get appended to `prompt_N.md` in chronological order,
   verbatim, clearly labelled. **Never edit a previous bundle's files.**
   One-off deliverables go in `bundleN/user_requested_documents/`.
4. **Proof fidelity:** signatures must match Rocq's **exactly**. Proof
   *method*/tactics may diverge freely (Lean has proof irrelevance). When you
   add a non-Rocq helper lemma, say so in its doc comment and say what Rocq does
   inline instead.
5. **When a proof fights back: first check the signature and its dependencies
   are right; if the issue persists, SKIP IT and FLAG IT** (revert to `sorry`
   with a doc comment saying exactly where it got stuck). Do not spin. Report
   significant issues immediately rather than burning the turn.
6. Ignore any `TODO FROM USER` comments — those are the user's notes to self.
7. `lake build` after every lemma or small batch. The build is fast enough
   (~30-60s warm) that there is no reason to batch more than a few lemmas.

---

## 2. THE BIG ONE: Lean cannot invert a hypothesis whose inductive index is an
## opaque term — and the fix is always the same

This single issue accounted for every lemma bundle15 flagged as stuck, and for
most of my own early iterations. **Understand it and you will not get stuck.**

### The problem

`cases h` / `obtain ⟨…⟩ := h` / `rcases h` on `h : SomeInductive a b c` works by
*dependent elimination*: Lean must unify each index of `h`'s type against the
corresponding index in each constructor's conclusion. That unification succeeds
cheaply when the index is a **bare free variable** (it just gets assigned), and
fails with

```
Dependent elimination failed: Failed to solve equation
  v_S.ELEMS.get!Internal p.1 = { TYPE := …, REFS := … }
```

when the index is an **opaque application** — in this codebase that means
`l[i]!` (`getElem!`), `p.1`/`p.2` (`Prod` projections), `x.TYPE` (structure
projections on a variable), or anything built with `OMap`/`Option.map` over a
variable (which unfolds to a `match` on that variable, and Lean will not invert
a `match`).

### The fix (use this, always)

**Do the inversion once, in a separate lemma whose arguments are bare
variables, and apply that lemma at the opaque site.** Mechanically:

```lean
-- helper: every argument is a plain variable, so `cases` is trivial
theorem eleminst_ok_invert (s : store) (e : eleminst) (t : elemtype) :
    Eleminst_ok s e t →
    ∃ ref_lst, Forall (fun r => Ref_ok s r t) ref_lst ∧ e = eleminst.MKeleminst t ref_lst := by
  intro h
  cases h with
  | mk_Eleminst_ok _ ref_lst hrefs _ _ => exact ⟨ref_lst, hrefs, rfl⟩

-- use site: the subject is `v_S.ELEMS[p.1]!`, which `cases` could never touch
obtain ⟨ref_lst, hrefs, heq⟩ := eleminst_ok_invert v_S _ p.2 (h16 p hp)
```

`ExtensionLemmas.lean` now has a whole labelled section of these
(`funcinst_ok_invert`, `globalinst_ok_invert`, `meminst_ok_invert`,
`meminst_ok_raw`, `tableinst_ok_invert`, `eleminst_ok_invert`,
`limits_ok_invert`, `wf_tableinst_parts`, `wf_meminst_parts`,
`Ref_ok_wf_store`, `Val_ok_wf_val`, `Store_ok_globalinst`). **Look there first
before writing a new one.** Also note the *transport* variants, which bundle an
inversion with a reconstruction so the caller never has to invert at all:
`Extend_store_eleminst_ext`, `Extend_store_datainst_ext`,
`Extend_store_frame`, `Extend_store_externaddr`, plus the `construct_*` rebuild
steps `eleminst_ok_drop`, `datainst_ok_drop`, `globalinst_ok_set`,
`tableinst_ok_set`, `meminst_ok_store`, `extend_meminst_bytes`.

### Special sub-case: `OMap` in an index

`Limits_ok`'s index contains `OMap (fun e => uN.mk_uN e) m_opt`, which unfolds to
`Option.map`, i.e. a `match` on `m_opt`. `cases` on a `Limits_ok` whose limits
argument is a *compound* term therefore always fails. The fix in the repo is
`limits_ok_invert`, which takes the limits as a bare variable plus an equational
premise:

```lean
theorem limits_ok_invert (lim : limits) (k : Nat) (h : Limits_ok lim k) :
    ∀ (v_n : Nat) (m_opt : Option Nat),
      lim = limits.mk_limits (uN.mk_uN v_n) (m_opt.map uN.mk_uN) →
      v_n ≤ k ∧ Forall (fun m' => v_n ≤ m' ∧ m' ≤ k) (Option.toList m_opt)
```
and recovers `m_opt` by an explicit `rcases m_opt <;> rcases m_opt' <;> simp_all [OMap]`
injectivity step. Call it as `limits_ok_invert _ _ h v_n m_opt rfl`.

---

## 3. THE OTHER BIG ONE: how many binder names does `cases … with | Ctor …` take?

I lost a lot of iterations to this and never found a rule I fully trust. What I
*do* trust:

- The count is **not** "constructor args + hypotheses". Some args occupy no slot
  at all; some occupy a slot whose *name is silently discarded*.
- **Giving too few names is always safe** (the rest get inaccessible names).
  Giving too many is a hard error that tells you the exact expected count:
  `Too many variable names provided at alternative 'mk_Frame_ok': 12 provided,
  but 11 expected`.
- **A name can be accepted and still not exist.** If a constructor arg is
  unified away (assigned to an existing free variable), its slot is kept but
  your name for it is dropped — you then get `Unknown identifier 'rt'` at the
  *use site*, with **no** error on the `cases` line. bundle15 misread this as a
  mysterious "`obtain` loses identifiers" bug; it is just this.

**Practical recipe — do this instead of reasoning:**

1. Write the pattern with a deliberately **too large** count of `_`s.
2. Build. Read `N expected` from the error.
3. Rewrite with exactly `N` entries, naming only the ones you need, and put
   `_` everywhere else.
4. Build again. If you now get `Unknown identifier 'foo'`, that slot's name was
   discarded by unification — find what it was unified *with* (usually one of
   your own lemma's variables) and use that name instead.

Worked examples now in the repo, for calibration:

| Inductive / constructor | slots | note |
|---|---:|---|
| `Extend_store.mk_Extend_store` | 20 | the 2 store args take no slot; hyp positions: globals 1-3, mems 4-6, tables 7-9, funcs 10-12, datas 13-15, elems 16-18, `wf_store s` 19, `wf_store s'` 20 |
| `Store_ok.mk_Store_ok` | 25+ | 12 list args, then hyps; `s = {…}` is hyp 13 ⇒ slot 25 |
| `Moduleinst_ok.mk_Moduleinst_ok` | 40 | 14 list args + 26 hyps; hyp *k* is slot 14+*k* |
| `Frame_ok.mk_Frame_ok` | 11 | `s` takes no slot; `val_lst v_minst t_lst C` + 7 hyps |
| `Expr_ok2.mk_Expr_ok2` | 7 | `s` takes no slot |
| `Config_ok.mk_Config_ok` | 10 | all 5 args keep slots (they sit inside compound indices) |
| `State_ok.mk_State_ok` | 7 | |
| `wf_uN.uN_case_0` | 2 | `v_N` takes no slot (it unifies with the literal `32`) |
| `wf_limits.limits_case_0` | 4 | |
| `wf_tabletype.tabletype_case_0` | 3 | |
| `wf_meminst.meminst_case_` | 4 | |
| `Meminst_ok.mk_Meminst_ok` | 8 | `v_n m_opt b_lst` + 5 hyps |
| `Tableinst_ok.mk_Tableinst_ok` | 10 | 4 args + 6 hyps |
| `Globalinst_ok.mk_Globalinst_ok` | 7 | 3 args + 4 hyps |
| `Eleminst_ok.mk_Eleminst_ok` | 5 | `rt`'s *name* is discarded (it unifies with your `t`) |
| `Extend_eleminst.mk_Extend_eleminst` | 4 | first two names discarded |
| `Extend_datainst.mk_Extend_datainst` | 5 | first name discarded |
| `Blocktype_ok.valtype` / `.typeidx` | 3 / 7 | |

**One more trap:** `induction h` and `cases h` do **not** agree on slot counts.
`induction` has to form a single motive covering every constructor, so it
generalizes indices that `cases` could have unified away — which means
`induction` generally gives you *more* slots. (`Externaddr_ok`'s `sub` case:
9 slots under `induction`, fewer under `cases`.) Don't reuse a `cases` pattern
inside an `induction` or vice versa.

---

## 4. Encoding Rocq's `dependent induction` in Lean

Rocq writes `dependent induction H` (or `remember … as c1; generalize dependent …;
induction H`) when the inductive's indices are not variables. Lean's `induction`
refuses non-variable indices outright. The repo's uniform encoding:

```lean
private theorem foo_aux (c1 c2 : config) (h : Step c1 c2) :
    ∀ (s : store) (f : frame) … ,
      c1 = config.mk_config (state.mk_state s f) ais →
      c2 = config.mk_config (state.mk_state s' f') ais' →
      … → <conclusion> := by
  induction h
  case ctxt_label … => …          -- the cases that need the IH
  case ctxt_frame  => …
  case local_set z v x => …
  all_goals (                      -- everything else, uniformly
    intro s f ais s' f' ais' … h1 h2 …
    injection h1 with hz1 _
    injection h2 with hz2 _
    subst hz1
    try simp only [with_global, with_table, with_tableinst, with_elem,
      with_mem, with_meminst, with_data] at hz2
    injection hz2 with _ hf
    subst hf
    exact hvals)

theorem foo … := fun … => foo_aux _ _ h s f ais s' f' ais' … rfl rfl …
```

Live instances: `reduce_inst_unchanged_aux` and `t_preservation_vs_type'_aux`
(both in `TypePreservation.lean`), and the four
`Externaddr_invert_*_aux` (in `ExtensionLemmas.lean`). The `try` on the
`simp only` matters: on the cases where the state is unchanged the simp set has
nothing to do and would otherwise fail with "simp made no progress".

**Useful fact about `Step` specifically:** of its 23 constructors, only
`local_set` touches the frame at all (`with_local` rewrites `LOCALS`, every
other `with_*` touches only the store), `ctxt_frame` changes only the *inner*
frame, and only `ctxt_label` and `ctxt_instrs` need the induction hypothesis.
That is why both `Step` inductions in the repo are short.

---

## 5. Mutual inductives: `Instr_ok2` / `Instrs_ok2` / `Expr_ok2`

Rocq needs a hand-written `Scheme ais_ok_ind'` for these. **Lean already
generates exactly what you need.** Two crucial facts:

- `@Instrs_ok2.rec` takes `{a : store}` as a **parameter**, not an index. So the
  store is *fixed* across the whole induction and you do **not** have to
  generalize it into the motive the way Rocq does.
- It takes **three** motives (`motive_1` for `Instr_ok2`, `motive_2` for
  `Instrs_ok2`, `motive_3` for `Expr_ok2`) and **12** minor premises, in
  declaration order: `Instr_ok2`'s 6 (`plain`, `label`, `Instr_ok2_frame`,
  `call_addr`, `ref`, `trap`), then `Instrs_ok2`'s 5 (`empty`, `instr`, `seq`,
  `sub`, `Instrs_ok2_frame`), then `Expr_ok2`'s 1 (`mk_Expr_ok2`). In each minor
  premise the induction hypotheses come **after** all args and all hypotheses.

`Extend_store_ais` is proved by applying it directly as a term:

```lean
exact Instrs_ok2.rec
  (motive_1 := fun C ai ft' _ => Instr_ok2 s' C ai ft')
  (motive_2 := fun C ais' ft' _ => Instrs_ok2 s' C ais' ft')
  (motive_3 := fun C ae ts _ => Expr_ok2 s' C ae ts)
  (fun C vi t1 t2 hok _ hwfC hwfi => Instr_ok2.plain s' C vi t1 t2 hok hwfS' hwfC hwfi)
  … 12 lambdas total …
  h
```

If you need to see the exact shape again, drop
`set_option pp.explicit false in #check @Instrs_ok2.rec` just before `end TLC`,
run `lake build`, read the `info:` line, then delete it. (I did exactly that.
Remember to delete it — it produces a huge info message.)

There is also a precedent for using `induction h using Instrs_ok2.rec
(motive_1 := …) (motive_3 := …) with | …` in `TypingLemmas.lean`'s
`ais_single_typing_inversion'_gen`, when you want tactic-mode cases and only
care about one motive.

---

## 6. The zip-based `Forall₂` — what is free and what is not

`wasm2.0.lean:18`: `Forall₂ P xs ys := ∀ p ∈ xs.zip ys, P p.1 p.2`, and
`Forall P xs := ∀ x ∈ xs, P x`. Consequences, all of which bite:

- **Pointwise lifts are free.** `Forall₂ P l1 l2 → Forall₂ Q l1 l2` given
  `∀ a b, P a b → Q a b` is literally `fun h p hp => … (h p hp)`. Every
  `Extend_store_*s` plural lemma in the repo is a one-liner of this shape. Don't
  write an induction.
- **Length is NOT implied.** `Forall₂ P [a] []` holds vacuously. This is why
  `HelperLemmas.Forall2_nth`, `Forall2_lookup`, `Forall2_forall2` and friends are
  permanently `sorry` — their Rocq statements *derive* the length equality. Their
  usable replacement is **`HelperLemmas.Forall2_nth_of_length`**, which takes the
  length as a hypothesis. Same for `funcinst_same`.
- **To get the element at a specific index you must exhibit the zip pair.**
  Use `HelperLemmas.mem_zip_getElem! l l' i hi hi' : (l[i]!, l'[i]!) ∈ l.zip l'`.
- **To get `p.1 ∈ l1` from `p ∈ l1.zip l2`**: `(List.of_mem_zip hp).1`. This
  works even though `p` is not syntactically `(a, b)`, thanks to structure eta.
- **"Template B" — the `List.modify` bridge** (all in `HelperLemmas.lean`, added
  this bundle). Use these whenever a lemma's conclusion is a `Forall`/`Forall₂`
  over `list_update_func l i f` (= `l.modify i f`):
  - `mem_modify f l : ∀ idx x, x ∈ l.modify idx f → x ∈ l ∨ (x = f (l[idx]!) ∧ l[idx]! ∈ l)`
  - `mem_zip_modify f l : … p ∈ (l.modify idx f).zip ts → p ∈ l.zip ts ∨ (p.1 = f (l[idx]!) ∧ (l[idx]!, p.2) ∈ l.zip ts)`
  - `mem_zip_modify_right g l : … p ∈ l.zip (ts.modify idx g) → p ∈ l.zip ts ∨ (p.1 = l[idx]! ∧ p.2 = g (ts[idx]!) ∧ (l[idx]!, ts[idx]!) ∈ l.zip ts)`
  - `mem_zip_modify₂ f g l : … both lists modified at the same index`
  Each one hands you membership of the *original* element, so you can feed it the
  `Forall`/`Forall₂` you already have. The usage pattern is always:
  ```lean
  intro p hp
  rcases mem_zip_modify _ l ts idx p hp with hp' | ⟨h1, h2⟩
  · exact h p hp'                       -- untouched position
  · rw [h1]; exact <rebuild> (h _ h2)   -- the updated position
  ```
  All 7 `construct_*` lemmas and `t_preservation_vs_type'`'s `local_set` case use
  exactly this.
- `Vals_ok v_S v_vals v_ts := v_ts.length = v_vals.length ∧ Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals`
  — note **types first, values second**, and the length is baked in (a deliberate
  bundle9 strengthening). `obtain ⟨hlen, hall⟩ := hvals` works; `refine ⟨?_, ?_⟩`
  constructs.

---

## 7. Syntax / elaboration gotchas that cost me real time

- **Multi-line structure-instance literals are indentation-sensitive.** This
  fails to *parse* with `unexpected identifier; expected '}'`:
  ```lean
      inst_match C (({ TYPES := [], FUNCS := [], …, MEMS := [],
        ELEMS := [], … } : context) ++ C)        -- ELEMS is LEFT of TYPES's column
  ```
  because continuation fields must be indented at least to the column of the
  first field. Put the first field on its own line instead:
  ```lean
      inst_match C (({
          TYPES := [], FUNCS := [], …, MEMS := [],
          ELEMS := [], … } : context) ++ C)
  ```
  `TypePreservation.lean`'s `inst_match_locals_append` / `locals_append_eq` show
  the working layout. The error position Lean reports is *not* where the problem
  is — don't chase it.
- **`rw` is syntactic; `lookup_total` vs `[i]!` will not match.**
  `lookup_total l i` is a plain `def` for `l[i]!`. Lemma statements use
  `lookup_total`; `getElem!`-based helpers produce `[i]!`. Normalise first with
  `simp only [lookup_total] at h ⊢` before any `rw`, or bridge with
  `rw [show (l[i]! : α) = lookup_total l i from rfl]`.
- **`simp` "made no progress" often means the goal is already `rfl`-true.** Both
  `inst_match_locals_append` and `locals_append_eq` needed plain `rfl` / `show …;
  rw [h]` rather than `simp [append_context]`, because `simp` could not see
  through the `HAppend`/`Append` instance while `rfl` could.
- **`OMap f o` and `o.map f` are defeq** (`OMap` is literally `o |>.map f`), and
  `(fun e => uN.mk_uN e)` is eta-equal to `uN.mk_uN`. `exact`/`refine` cope;
  `rw`/`simp only` do not. When a constructor wants `OMap f m_opt` and you have
  `j_opt`, you must first *derive* `j_opt = m_opt.map uN.mk_uN` and `subst` it —
  unification cannot invent `m_opt`.
- **`congrArg f h` elaborates `h`'s expected type from the goal**, so
  `exact congrArg frame.MODULE hf` can fail with a type mismatch where
  `subst hf; rfl` succeeds. Prefer `subst`/`rw` for this.
- **`rcases … with rfl` can delete the variable you wanted to keep.** In
  `hx : x = tv1 ∨ …`, `rcases hx with rfl | …` may eliminate `tv1` rather than
  `x`, after which `tv1` is an unknown identifier. Use
  `rcases hx with hx | …` then `rw [hx]`.
- **`injection h with …` only works on constructor-headed equations**; for
  `uN.mk_uN a = uN.mk_uN b` it is fine, for `some (uN.mk_uN a) = Option.map f o`
  you must `rcases o` first (or use `have : a = b := by simpa using h`).
- `Int.toNat ((2 ^ 32 : Int) - 1)` is the *same expression* in `wf_uN 32`'s bound
  and in `Tabletype_ok`'s `Limits_ok _ k`. That is not a coincidence and it is
  how `construct_tableinsts_grow` gets its `|v_r| + v_n ≤ 2^32-1` obligation: from
  the `Forall wf_tableinst tbinsts` premise, via `wf_tableinst_parts`. Rocq does
  the same thing (`inv_Forall HWftbinsts`).

---

## 8. How to iterate fast

- `timeout 1800 lake build 2>&1 | grep -E "error:" -A 20 | head -60` — the only
  build command you need. The raw output is dominated by `wasm2.0.lean` linter
  warnings; always filter.
- The IDE diagnostics hook (shown automatically after `Edit`) is often *more*
  informative than the CLI for binder-count and unknown-identifier errors, and
  often *less* informative for goal states. Use both.
- To see a full local context, provoke an **"Application type mismatch"** (e.g.
  apply a hypothesis to a wrongly-typed argument). That error class prints the
  whole context; a bare `exact trivial` usually prints only the goal.
- `grep -c 'sorry$'` per file is the progress metric. To list *which* ones:
  ```bash
  grep -n "sorry$" F.lean | awk -F: '{print $1}' | while read ln; do \
    awk -v L=$ln 'NR<=L && (/^theorem /||/^def /||/^private theorem /){t=$0} END{print t}' F.lean \
    | sed 's/ (.*//;s/ {.*//;s/^theorem //;s/^private theorem //;s/^def //'; done
  ```
- I did all edits this bundle through `python3 - <<'PYEOF'` scripts doing exact
  string replacement with `assert old in s`. That is much more reliable than
  `sed` for multi-line Lean and it fails loudly if the anchor drifted.
- The Rocq source is at `spectec/test-rocq/theories/*.v`. **Line numbers in the
  Lean doc comments are from an older revision and do not match the local
  checkout** — always `grep -n "^Lemma <name>"` instead.

---

## 9. Dead ends — things I tried that do NOT work

- `cases`/`obtain`/`rcases` on a hypothesis with an opaque index, in any
  combination, including `set x := … with hx; clear_value x; obtain …`. Use §2.
- `simp [Option.toList]` to unfold `Option.toList (some a)` into `[a]` — it does
  not fire reliably. `rcases o with _ | a <;> simp_all` does.
- `omega` on goals mentioning `Ki` (a `def`, not a literal) — it will not unfold.
  Use `Nat.add_mul`/`Nat.mul_div_cancel` explicitly. Also: a stray `omega`
  failure with "No usable constraints found" on an obviously-true goal usually
  means an earlier metavariable leaked into it; fix the earlier step rather than
  the `omega`.
- Reusing bundle15's note that `cases h with | Ctor … =>` "fixes" the
  `obtain`-loses-names problem. It does not — it has the same slot semantics.
  The real fix is §2 (move the inversion to a bare-variable lemma); the real
  explanation of the symptom is §3 (discarded names).

---

## 10. Per-lemma routes for the 5 remaining genuine proofs

See `proof_prioritization_v6.md` in this folder for the recommended order and a
step-by-step route for each. Summary of the machinery they all need, all of which
**already exists and is proved**:

- Splitting a sequence: `ais_seq_typing_inversion` (head + tail),
  `ais_composition_typing` (arbitrary prefix).
- One instruction's principal type: `ais_single_typing_inversion` +
  `unfold ai_principal_typing` (the big `match` at `TypingLemmas.lean` ~line 311
  — read the entry for your instruction there first; it tells you exactly what
  existential you will get).
- Values: `ais_single_val_typing_inversion`, `Val_ok_non_bot`,
  `valtype_sub_non_bot`, `resulttype_sub_non_bot`.
- Composing subtyping steps: `instrtype_sub_compose_le/_ge/_eq/1/2`
  (`Subtyping.lean` ~line 375 onward). The `_eq` form additionally hands back
  the `ResulttypeSub` between the two middle types — that is how you learn
  "the value's type *is* the expected type" once you know it is not `BOT`.
- Rebuilding: `construct_ai_val`, `construct_ai_const_I32`, `construct_ai_ref`,
  `construct_ai_maybe` (for an arbitrary plain instr),
  `construct_ais_typing_single`, `construct_ais_subtyping`,
  `construct_ais_compose`, `construct_ais_vals'`, `ais_empty_typing`.
- Context plumbing: `prepend_label` (`HelperLemmas` ~479),
  `construct_inst_prepend_label`, `construct_inst_match_label`,
  `lookup_label_0`, `lookup_label_1`, `proj_identity`.
- Wf side conditions: `ainstrs_ok_context_store_wf` (returns
  `wf_context ∧ wf_store ∧ Forall wf_admininstr`, in that order).

**The already-proved `Step_pure__select_preserves_helper` (this bundle) and
`Step_pure__if_preserves_helper`, `Step_pure__br_if_preserves`,
`Step_pure__label_vals_preserves`, `Step_pure__frame_vals_preserves` are your
templates.** The select helper in particular shows the full four-instruction
pattern: peel with three `ais_seq_typing_inversion`s, pin `CONST`'s principal
type, case-split the `SELECT` annotation (`some [t]` / `none` give the type,
`some []` and `some (_::_::_)` are `False`), compose with
`instrtype_sub_compose_ge` twice then `instrtype_sub_compose_eq`, then use
`resulttype_sub_non_bot` to turn the resulting `ResulttypeSub` into actual type
equalities.

---

## 11. Things worth double-checking if you have budget

- **`Extend_store_datainsts'`'s signature diverges from Rocq.** Rocq's is
  `Forall2 (λ a t, Datainst_ok …) aa ts`; the Lean statement is a `Forall` with
  `datatype.OK` hard-coded, dropping the `ts` list entirely. Since `datatype` has
  exactly one constructor these are equivalent in content, but it *is* a
  signature divergence against the standing fidelity rule, and it is not
  documented in the lemma's own comment. I left it alone (changing it risks
  breaking `Extend_store_moduleinst`, which currently does the `Forall₂` version
  inline instead of calling this lemma). Worth raising with the user.
- **`construct_meminsts_grow`'s signature** hard-codes the declared page-count
  max as present (`some (uN.mk_uN v_j)`) where Rocq's `v_j_opt` is a genuine
  `Option`. Pre-existing; flagged in its doc comment since bundle13. It is now
  *proved* at the narrower signature, so generalising it later is real work, not
  a rename.
- **`table_grow_table_extension` takes `j : Option uN`** while
  `memory_grow_mem_extension` takes `v_j : Option Nat` + `.map uN.mk_uN`. The
  former matches Rocq more literally. Harmless, but the inconsistency will
  confuse someone eventually.
- `Step_is_wf` in `wasm2.0.lean` is `sorry` (generated file, out of bounds).
  `t_preservation` depends on it. Nothing to do about it here, but it means
  `t_preservation` is not yet axiom-free even ignoring the Rocq gaps. Verified
  with a temporary `#print axioms TLC.t_preservation` at the end of
  `TypePreservation.lean` (probe since removed):
  `depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]` — i.e.
  the only non-standard dependency is `sorryAx`, contributed by the 3 Rocq-
  `Admitted` mirrors plus `Step_is_wf`. Re-run that probe after closing the
  remaining 5 to see the gap shrink; it will not reach "no sorryAx" until the
  SIMD gaps and `Step_is_wf` are addressed upstream.

# 3. `reduce_inst_unchanged`

*(Previous: [02-store-extension-reduce.md](02-store-extension-reduce.md). Next: [04-extend-store-moduleinst.md](04-extend-store-moduleinst.md).)*

**Plain-English summary.** *A single step never changes which module a frame belongs to.* The frame's `LOCALS` can change (that's what `local.set` does); its `MODULE` field — the addresses this code's indices resolve through — never does. This matters because a function call pushes a brand-new `FRAME_` with the *callee's* module instance, but that's a nested/different frame, not a mutation of the current one.

**Code** — [TypePreservation.lean:492-540](../../../../../src/test-lean-claude/TypePreservation.lean#L492-L540):
```lean
/-- Generalized form of `reduce_inst_unchanged` below. Rocq does the same
    thing with `remember ... as c1`/`remember ... as c2` plus `generalize
    dependent` before `induction HReduce`; Lean's `induction` needs the
    indices to be variables, so the two `config`s are generalized and the
    shapes recovered from equational premises instead. Every `Step`
    constructor either leaves the state alone, rewrites it with one of the
    `with_*` functions (all of which preserve `frame.MODULE` — `with_local`
    touches only `LOCALS`, the rest only the store), or is one of the two
    congruence rules that need the induction hypothesis; `ctxt_frame` is in
    the first group, since it changes only the *inner* frame. -/
private theorem reduce_inst_unchanged_aux (c1 c2 : config) (h : Step c1 c2) :
    ∀ (s : store) (f : frame) (ais : List admininstr) (s' : store) (f' : frame)
      (ais' : List admininstr),
      c1 = config.mk_config (state.mk_state s f) ais →
      c2 = config.mk_config (state.mk_state s' f') ais' → f.MODULE = f'.MODULE := by
  induction h
  case ctxt_label z v_n i0 L z' L' _ _ _ ih =>
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    injection h2 with hz' _
    exact ih s f L s' f' L' (by rw [hz]) (by rw [hz'])
  case ctxt_instrs z vl L L1 z' L' _ _ _ _ ih =>
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    injection h2 with hz' _
    exact ih s f L s' f' L' (by rw [hz]) (by rw [hz'])
  case local_set z v_val x =>
    -- the only rule that touches the frame at all: `with_local` rewrites
    -- `LOCALS` and leaves `MODULE` alone.
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    subst hz
    injection h2 with hz' _
    simp only [with_local] at hz'
    injection hz' with _ hf
    subst hf
    rfl
  all_goals (
    intro s f ais s' f' ais' h1 h2
    simp_all [with_global, with_table, with_tableinst, with_elem, with_mem,
      with_meminst, with_data])

/-- Rocq `type_preservation.v:997` `reduce_inst_unchanged`. The module-instance component
    of the frame is invariant under `Step`. -/
theorem reduce_inst_unchanged (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    f.MODULE = f'.MODULE :=
  fun h => reduce_inst_unchanged_aux _ _ h s f ais s' f' ais' rfl rfl
```

**Signature.** Simplicity itself: from one `Step` between two `(store, frame, instrs)` triples, conclude the *old* frame's `MODULE` equals the *new* frame's `MODULE` — no other hypotheses needed at all (this fact doesn't depend on typing, only on which operational rule fired).

**Proof sketch.** Induct over all 23 `Step` constructors (primer §0.8's `_aux` pattern again). `ctxt_frame` is interesting *by its absence from the explicit cases*: it changes only the frame *wrapped inside* a `FRAME_` marker, not the ambient `(s,f,...)` triple the lemma is stated about, so it falls into the `all_goals` catch-all along with every store-writing rule (none of which touch `frame.MODULE`, only `store` fields — confirmed by `simp_all` unfolding every `with_*` updater and finding nothing to do). `ctxt_label`/`ctxt_instrs` recurse via `ih` since they wrap a *further* step at the same frame. `local_set` is the one genuinely interesting case: `with_local` only overwrites the indexed slot of `LOCALS`, so `MODULE` survives by `rfl` once that's unfolded.

---
*Next: [04-extend-store-moduleinst.md](04-extend-store-moduleinst.md).*

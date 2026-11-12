import «wasm2.0»

/-!
# Byte-serialization length axioms, and the `store_pack_val`/`store_num_val`
  cases of `store_extension_reduce`

`PROGRESS.md`/`logs/DECISIONS.md` (session of 2026-09-23) record that the
`store_num_val`/`store_pack_val`/`vstore_val`/`vstore_lane_val` cases of
`StoreExtension.lean`'s `store_extension_reduce` were left `sorry` because
`nbytes_`/`ibytes_`/`vbytes_` (`wasm2.0.lean:3626-3681`) are `hint(builtin)`
opaque axioms with no stated length property.

**This is not a gap unique to the Lean backend.** Rocq's own development hits
the exact same wall and resolves it the same way: `spectec/test-rocq/theories/
axioms.v` (branch `rocq-backend-proof`) introduces `nbytes_len`/`ibytes_len`
(and primed rational-division variants `nbytes_len'`/`ibytes_len'`) as *bare
Coq `Axiom`s*, not derived from anything — i.e. Rocq's trusted base already
includes exactly this fact. This file adds the Lean equivalents for `ibytes_`
(closing `store_pack_val`) and `nbytes_` (closing `store_num_val`), matching
Rocq's axioms name-for-name and shape-for-shape (adapted to the Lean model's
`rat_to_nat`-based rational-division encoding, which Rocq's primed variants
already use directly via `Q`).

**No Rocq precedent exists for `vbytes_`** (`vstore_val`/`vstore_lane_val`) —
Rocq's `axioms.v` has nothing for it, so introducing an analogous axiom here
would be a genuinely new addition beyond translating Rocq, not just
replicating its trusted base. Left `sorry`, not attempted.

**[REVIEW]** Introducing new axioms is a more consequential step than
anything else in this folder — everywhere else, this session only proved
consequences of what `wasm2.0.lean` already states. These two axioms *are*
already part of the accepted Rocq trusted base for the same purpose, so
replicating them is a faithful translation, not an invention — but you
should decide whether you want them carried into any eventual release
artifact, the same way `rat_to_nat`'s opacity was flagged in the Task 1
report as the one Lean-backend-specific gap worth a second look.

**These axioms alone turned out NOT to be enough to actually close
`store_pack_val`/`store_num_val`** (attempted after writing them — see
`logs/DECISIONS.md`, `2026-09-23 ~01:20`). `Extend_meminst`'s constructor
needs `wf_meminst` of the *new* `meminst`, which needs
`Forall wf_byte newBYTES`; splitting that over the splice needs
`Forall wf_byte b_lst` (the newly-written bytes) — and unlike the *length*
fact, **Rocq's `axioms.v` has no axiom for this at all**. The generated
file's own `ibytes__is_wf`/`nbytes__is_wf` (`wasm2.0.lean:3633-3666`) assert
exactly this, but are `sorry`, and even invoking them needs a `wf_uN`
precondition this file has no derivation for either. Adding a *third*
axiom, beyond what Rocq's trusted base covers, to paper over this felt like
a step too far past "translate Rocq's proof" into "invent what's needed" —
so `store_pack_val`/`store_num_val` are left `sorry` in `StoreExtension.lean`
still. `splice_length_ge` below (the length-side reasoning, which *does* go
through cleanly) is kept since it's real, reusable progress, and the two
`Axiom`-precedented facts (`ibytes_len`/`nbytes_len`) are kept since they're
independently useful and faithful to Rocq — but this file does not, in the
end, unlock any additional `Step` case on its own.
-/

namespace TestLeanClaude

/-- Rocq: `axioms.v`, `ibytes_len'` (the rational-division form; the plain
    `ibytes_len` uses `Nat.divmod` directly, `rat_to_nat` is this backend's
    bridge to that same quantity — see the Task 1 report). Stated over any
    `iN`, not just `wrap__`'s output, since Rocq's version doesn't depend on
    how the `iN` argument was produced either. -/
axiom ibytes_len (v_N : N) (x : iN) :
    (ibytes_ v_N x).length = rat_to_nat ((v_N : Rat) / (8 : Rat))

/-- Rocq: `axioms.v`, `nbytes_len'`. `nbytes_` is `Option`-wrapped in this
    backend (unlike Rocq's, which is presumably partial via a different
    mechanism), so this only makes a length claim on the `some` branch. -/
axiom nbytes_len (v_numtype : numtype) (v_num_ : num_) (bs : List byte) :
    nbytes_ v_numtype v_num_ = some bs →
    bs.length = rat_to_nat (((Option.get! (size (valtype_numtype v_numtype))) : Rat) / (8 : Rat))

/-- A splice-write `(l.take nat ++ new) ++ l.drop (nat + nat_0)` never
    *shrinks* the list, as long as the inserted block is at least as long as
    the claimed removed span (`new.length ≥ nat_0`) — regardless of whether
    `nat`/`nat_0` are actually in bounds for `l` (`List.take`/`List.drop`
    clamp gracefully either way). This is the one piece of genuinely new
    (Wasm-independent) list-algebra this file needed; no direct Rocq/Isabelle
    counterpart (their `store_pack_val`-equivalent cases go through
    different, index-carrying bookkeeping). -/
theorem splice_length_ge {α : Type} (l new : List α) (nat0 nat_0 : Nat) (h : nat_0 ≤ new.length) :
    l.length ≤ ((l.take nat0 ++ new) ++ l.drop (nat0 + nat_0)).length := by
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

end TestLeanClaude

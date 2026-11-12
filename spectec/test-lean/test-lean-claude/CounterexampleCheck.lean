import «wasm2.0»
import custom_notation

/-!
Standalone empirical check of a suspected counterexample to
`typing_lemmas.lean`'s `instrs_seq_typing_inversion` (lines 2002-2011):

  Instrs_ok c (i :: is) (ts1 f-> ts3)
  → ∃ ts2, Instr_ok c i (ts1 f-> ts2) ∧ Instrs_ok c is (ts2 f-> ts3)

Claim: this is FALSE in general. Witness: `i := CONST I32 c`, `is := []`,
`ts1 := [I32]`, `ts3 := [I32, I32]`. `Instrs_ok C [CONST I32 c] ([I32] f->
[I32,I32])` is derivable via `Instrs_ok.frame` (prepending `[I32]` to the
plain `Instrs_ok.instr` derivation of `[] f-> [I32]`), but no `ts2` can
satisfy `Instr_ok C (CONST I32 c) ([I32] f-> ts2)`, because `Instr_ok`'s
`const` rule fixes the input type to `[]` unconditionally
(`wasm2.0.lean:9676-9679`) — it has no `frame`/subsumption flexibility of its
own (only `Instrs_ok`, the *sequence*-level judgment, has `frame`/`sub`).

See `logs/DECISIONS.md` for the write-up if this compiles as expected.
-/

namespace TestLeanClaude

example (C : context) (c : num_) (hC : wf_context C) (hi : wf_instr (instr.CONST numtype.I32 c)) :
    Instrs_ok C [instr.CONST numtype.I32 c]
      (mkFunctype [valtype.I32] [valtype.I32, valtype.I32]) := by
  have h0 : Instrs_ok C [instr.CONST numtype.I32 c] (mkFunctype [] [valtype.I32]) :=
    Instrs_ok.instr C (instr.CONST numtype.I32 c) [] [valtype.I32]
      (Instr_ok.const C numtype.I32 c hC hi) hC hi
  have h1 := Instrs_ok.frame C [instr.CONST numtype.I32 c] [valtype.I32] [] [valtype.I32]
    h0 hC (by intro x hx; simp at hx; subst hx; exact hi)
  simpa [mkFunctype] using h1

/-- The claimed-impossible half: no `ts2` makes `Instr_ok C (CONST I32 c)
    ([I32] f-> ts2)` true, because `const`'s rule forces the input to `[]`. -/
example (C : context) (c : num_) (ts2 : List valtype) :
    ¬ Instr_ok C (instr.CONST numtype.I32 c) (mkFunctype [valtype.I32] ts2) := by
  intro h
  unfold mkFunctype at h
  cases h

end TestLeanClaude

;; ============================================================================
;; Companion to specification/wasm-2.0/3-numerics.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs, despite this being the
;; single biggest file in the directory (612 lines / ~90 top-level defs).
;;
;; This file's *entire* content is `def $foo(...)` -- functions computing
;; what a numeric/vector operator actually returns: $iadd_, $isub_, $idiv_,
;; $ishl_, $fsqrt_, $fnearest_, $sat_u_, $sat_s_, $signed_, $wrap__,
;; $extend__, $trunc_sat__, $convert__, $ibytes_/$fbytes_ (value <-> bytes
;; for memory load/store), $lanes_/$inv_lanes_ (SIMD vector <-> per-lane
;; values), and so on for every unop/binop/testop/relop/cvtop this
;; directory's spec knows about.
;;
;; The crucial distinction: the *existence* and *name* of an operator --
;; that `i32` has an `ADD` and a `CLZ` and a `DIV_S`, that a `binop_(Inn)`
;; grammar production even has a `DIV sx` case -- is declared as category-A
;; syntax in 1-syntax.spectec. This file only says what happens when the
;; interpreter executes one: `$iadd_(32, 2, 3) = 5`. You cannot write
;; "$iadd_" in a .wat file; you write `i32.add`, and 01-syntax.wat in this
;; directory exercises literally every one of ~130 scalar numeric
;; instructions and ~80 vector instructions that this file gives meaning
;; to -- go there to see (and run, via wasmdebug) the actual instructions.
;; This file is the reference you'd check to know what result to *expect*.
;;
;; A few defs are worth calling out by name, since they're the ones with
;; the least obvious 1-syntax.spectec counterpart:
;;   - $signed_ / $inv_signed_: WASM integers have no separate signed type
;;     -- i32 is just 32 bits. $signed_ is how the spec reinterprets those
;;     bits as a signed value for e.g. i32.lt_s. Purely a math function.
;;   - $sat_u_ / $sat_s_: clamps an out-of-range integer into [0, 2^N-1] or
;;     [-2^(N-1), 2^(N-1)-1]. Used to define the *_sat_ conversion
;;     instructions (category A: `i32.trunc_sat_f64_s` etc., see
;;     01-syntax.wat) but is itself just clamping arithmetic.
;;   - $packnum_ / $unpacknum_: convert between a full numtype value and a
;;     packed SIMD lane (i8/i16) value -- the semantics behind why
;;     `i8x16.add` truncates each lane to 8 bits.
;;
;; hint(builtin) tags (e.g. `def $fsqrt_ hint(builtin)`) mark defs whose
;; actual computation is supplied by spectec's backend (e.g. real
;; IEEE-754 sqrt) rather than spelled out equationally in this file -- an
;; implementation detail of the spec tooling, not a WASM concept either
;; way.

(module)

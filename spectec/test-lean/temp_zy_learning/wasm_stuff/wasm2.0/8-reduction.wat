;; ============================================================================
;; Companion to specification/wasm-2.0/8-reduction.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs. This is the small-step
;; operational semantics: ~100 `rule`s of the form "this instruction (plus
;; whatever's underneath it on the stack) steps to that", e.g.
;;
;;   rule Step_pure/binop-val:
;;     (CONST nt c_1) (CONST nt c_2) (BINOP nt binop)  ~>  (CONST nt c)
;;     -- if c <- $binop_(nt, binop, c_1, c_2)
;;
;; which literally says: two const values followed by a binop instruction
;; step to the single const result of applying that binop (defined in
;; 3-numerics.spectec). Every rule here is *about* some category-A
;; instruction from 1-syntax.spectec, but the rule itself -- the ~> arrow,
;; the "Step" judgment -- has no WAT representation. This is, in a very
;; concrete sense, the file that defines what "stepping" means -- which
;; makes it worth pointing out explicitly, given this whole directory
;; exists to be stepped through with wasmdebug (see ~/wasmdebug in this
;; project):
;;
;;   - Every click of wasmdebug's "Call" button, and every time you press
;;     Chrome DevTools' Step Over / Step Into, you are watching one
;;     instance of the `Step` / `Step_pure` / `Step_read` relation fire.
;;   - The "context" rules (Step/ctxt-label, Step/ctxt-frame,
;;     Step/ctxt-instrs) are why stepping "into" a block or a call works
;;     the way it does -- they say a step deep inside a LABEL_/FRAME_
;;     (see admininstr in 4-runtime.spectec) counts as a step of the whole
;;     configuration. That's the formal justification for DevTools letting
;;     you step into `call_indirect` in sandbox1.wat and land inside `$sq`.
;;   - Step_pure/trap-vals and friends are why a trap (e.g. an
;;     out-of-bounds memory.init, or i32.div_s by zero) immediately
;;     unwinds past any surrounding values/labels/frames -- which is
;;     exactly what you'd see in wasmdebug if you call an export that
;;     traps: DevTools reports an uncaught (wasm) exception rather than a
;;     return value.
;;   - $blocktype here (not in 1-syntax.spectec) computes a block/loop/if's
;;     actual functype from its `blocktype` (either an inline result or a
;;     type-section reference, both category A) -- a small helper local to
;;     this file, still category B.
;;
;; See 01-syntax.wat for every instruction whose stepping behavior is
;; defined here, and try setting a breakpoint with wasmdebug on any of
;; them -- what you're single-stepping through *is* this file, rendered as
;; disassembled bytecode instead of these inference rules.

(module)

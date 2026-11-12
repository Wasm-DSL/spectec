;; ============================================================================
;; Companion to specification/wasm-2.0/6-typing.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs. This file is pure
;; validation logic: ~50 `relation`/`rule` judgments (Instr_ok, Module_ok,
;; Valtype_sub, Externtype_sub, ...) plus one `syntax context` record.
;;
;;   syntax context = { TYPES ..., FUNCS ..., GLOBALS ..., TABLES ...,
;;                       MEMS ..., ELEMS ..., DATAS ..., LOCALS ...,
;;                       LABELS ..., RETURN ... }
;;     -- the "typing context": everything the type checker needs to know
;;        about the enclosing module/function/block while checking one
;;        instruction (what type is local 3? what does a `br 1` target?
;;        what must this function return?). It's an accumulator the
;;        *checker* builds and threads through recursion -- nothing you
;;        write, and it doesn't exist once your module is instantiated
;;        (compare to `moduleinst` in 4-runtime.spectec, which is a
;;        *runtime* record and does persist).
;;
;;   relation Instr_ok / Instrs_ok / Expr_ok, and one `rule ... :` per
;;   instruction (Instr_ok/const, Instr_ok/call_indirect, Instr_ok/br, ...)
;;     -- "an instruction I, in context C, has stack type t1* -> t2*".
;;        These are the rules a validator (and wat2wasm, when it typechecks
;;        your module before emitting bytes) applies. Every single rule
;;        here corresponds one-to-one to an instruction that's category A
;;        in 1-syntax.spectec -- Instr_ok/call_indirect exists *because*
;;        CALL_INDIRECT exists -- but the *rule* (the judgment that it
;;        type-checks) isn't itself writable or observable as WASM syntax.
;;        You don't ever see "Instr_ok" in a .wat file or in DevTools.
;;
;;   Valtype_sub / Resulttype_sub / Limits_sub / Functype_sub / ... _sub
;;     -- subtyping rules (e.g. any type is a subtype of BOT; a table type
;;        with a smaller minimum is a subtype of one with a larger
;;        minimum). Used when checking e.g. that an imported table is at
;;        least as large as what the module declares it needs.
;;
;;   Module_ok
;;     -- the top-level judgment: strings every other rule together to
;;        decide whether a whole module is well-formed. This is precisely
;;        what `wat2wasm` is checking on every file in this directory
;;        before it will emit a .wasm binary -- and what wasmdebug's
;;        server-side `wat2wasm --enable-all --debug-names` invocation
;;        (see ~/wasmdebug/wasmdebug in this project) runs on every page
;;        load. Every file in this directory that compiles cleanly is a
;;        (very large, mechanically-checked) witness that Module_ok holds
;;        for it.
;;
;; See 01-syntax.wat for the module fields, types and instructions these
;; rules classify; see B-soundness.wat for how typing (this file) is later
;; connected to execution (8-reduction.wat) via the soundness theorem.

(module)

;; ============================================================================
;; Companion to specification/wasm-2.0/9-module.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs, despite the name.
;; The `module` syntax itself (type/import/func/global/table/mem/elem/
;; data/start/export -- everything you actually write) is declared in
;; 1-syntax.spectec; this file is entirely the *algorithm* that turns a
;; module into a running instance -- allocation, instantiation, invocation.
;;
;;   def $allocfunc(s), $allocglobal(s), $alloctable(s), $allocmem(s),
;;   $allocelem(s), $allocdata(s)
;;     -- for each declaration in your module, append one fresh instance to
;;        the store and hand back its address. E.g. $alloctable allocates a
;;        `tableinst` whose REFS is `n` copies of `REF.NULL rt` -- which is
;;        precisely why a fresh `(table 2 funcref)` reads as two nulls
;;        before any `(elem ...)` segment runs.
;;
;;   def $instexport
;;     -- turns one `export` declaration (category A) into a runtime
;;        `exportinst` (category B, 4-runtime.spectec) by resolving its
;;        index to the address just allocated above. This is why an
;;        exported function shows up in JS as `instance.exports.name` --
;;        wasmdebug's Scope-pane walkthrough of `run(i32)` earlier in this
;;        project was you looking at the product of this function.
;;
;;   def $allocmodule
;;     -- runs all of the above in the right order and assembles the
;;        resulting `moduleinst` (4-runtime.spectec). This is the formal
;;        version of "what happens between calling
;;        WebAssembly.instantiate(bytes) and getting an `instance` back".
;;
;;   def $runelem, $rundata, def $instantiate
;;     -- $instantiate is the top-level entry point: allocate the module,
;;        then run each active element/data segment's initializer (that's
;;        $runelem/$rundata) via a synthesized sequence like
;;        `(TABLE.INIT x i) (ELEM.DROP i)`, then call the start function if
;;        one was declared. Every one of those synthesized instructions is
;;        itself category A (1-syntax.spectec) -- $instantiate's job is
;;        just deciding *which* instructions to run and in what order.
;;
;;   def $invoke
;;     -- given a function address and arguments, pushes the arguments and
;;        a CALL_ADDR administrative instruction (4-runtime.spectec) onto a
;;        fresh configuration. This is exactly what wasmdebug's "Call"
;;        button does on your behalf: `instance.exports.run(3)` from the
;;        DevTools Console, or clicking Call in the page, both bottom out
;;        in one $invoke.
;;
;; See 01-syntax.wat for the module you write; 04-runtime.wat for the
;; moduleinst/store/exportinst records this file builds; 06-typing.wat for
;; Module_ok, the validity check that must hold before $instantiate may
;; run at all.

(module)

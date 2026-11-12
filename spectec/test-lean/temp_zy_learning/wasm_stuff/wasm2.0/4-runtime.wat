;; ============================================================================
;; Companion to specification/wasm-2.0/4-runtime.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs. Every top-level
;; `syntax` here describes the *abstract machine's* internal state -- never
;; something written in, or directly visible from, a .wat source file.
;;
;;   syntax addr, funcaddr, globaladdr, tableaddr, memaddr, elemaddr,
;;   dataaddr, hostaddr, externaddr
;;     -- runtime "addresses": plain numbers the abstract machine uses to
;;        identify one specific instance living in the store. Not the same
;;        thing as the funcidx/globalidx/etc. index spaces from
;;        1-syntax.spectec (category A) -- an *index* is module-relative
;;        and is what you write (`call 3`, `global.get $count`); an
;;        *address* is store-global and only exists once a module has been
;;        instantiated. You never write an address in WAT text.
;;
;;   syntax num, vec, ref, val, result
;;     -- runtime *values* flowing on the operand stack during execution.
;;        Note `ref` here is REF.NULL / REF.FUNC_ADDR / REF.HOST_ADDR --
;;        the latter two carry a resolved runtime address, unlike the
;;        source-level `ref.null` / `ref.func $x` instructions (category A,
;;        1-syntax.spectec) which name a type or an index. `result` adds
;;        TRAP as a possible outcome of running code -- again a runtime
;;        classification, not something you write.
;;
;;   syntax funcinst, globalinst, tableinst, meminst, eleminst, datainst,
;;   exportinst, moduleinst, store, frame, state, config
;;     -- THIS is the good part to know about if you've used wasmdebug:
;;        these records are *exactly* what Chrome DevTools shows you when
;;        you expand the "Module" entry in the Scope pane while paused --
;;        `functions: {$sq: f, $run: f}`, `globals: {$count: i32}`,
;;        `memories: {$memory0: Memory(1)}` is a `moduleinst`; the
;;        DevTools "Module" object as a whole is showing you a live
;;        `moduleinst` plus pieces of the enclosing `store`. You can watch
;;        one being built in real time by breakpointing anywhere and
;;        expanding Module -- but you can't write a moduleinst in source
;;        text; it's what your module *becomes* after 9-module.spectec's
;;        $allocmodule runs (see 09-module.wat in this directory).
;;
;;   syntax admininstr
;;     -- "administrative instructions": LABEL_, FRAME_, CALL_ADDR, TRAP,
;;        plus REF.FUNC_ADDR/REF.HOST_ADDR. These extend the real
;;        instruction set (`instr`, category A) with bookkeeping forms that
;;        only ever appear *during* execution, to let 8-reduction.spectec
;;        state small-step rules (e.g. "a LOOP turns into a LABEL_ wrapping
;;        its body"). No text encoding exists for LABEL_/FRAME_/CALL_ADDR;
;;        you can't write one, wat2wasm has no opcode for one. They're pure
;;        semantics scaffolding.
;;
;; See 01-syntax.wat for the module you actually author (func/table/
;; memory/global/elem/data/start/import/export -- everything a moduleinst
;; gets built *from*), and 09-module.wat's companion notes for the
;; allocation algorithm that turns one into the other.

(module)

;; ============================================================================
;; Companion to specification/wasm-2.0/2-syntax-aux.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs. All auxiliary functions
;; over the syntax defined in 1-syntax.spectec -- convenience, not syntax.
;;
;;   def $concat_bytes((byte*)*) : byte*
;;     -- flattens a list of byte-lists into one byte-list. Used later by
;;        A-binary.spectec's $utf8 to build up an encoded name byte by byte.
;;
;;   def $unpack(lanetype) : numtype
;;     -- packed SIMD lane types (I8/I16, see packtype in 1-syntax.spectec,
;;        category A) don't have their own arithmetic; when you e.g. add
;;        two i8x16 lanes, the spec first "unpacks" each lane to i32, does
;;        i32 arithmetic, then re-packs (see $packnum_/$unpacknum_ in
;;        3-numerics.spectec). $unpack just says which numtype a lanetype
;;        unpacks to. There's no WAT instruction called "unpack" -- this
;;        function is invoked implicitly, inside the *definition* of what
;;        e.g. i8x16.add means.
;;
;;   def $lanetype(shape), def $dim(shape), def $shsize(shape),
;;   def $shunpack(shape)
;;     -- accessors that pull the lane type / lane count / bit size /
;;        unpacked numtype out of a `shape` (like `I8 X 16`). `shape`
;;        itself is category A (it's literally the "i8x16" in an
;;        instruction mnemonic, declared in 1-syntax.spectec) -- but these
;;        four functions are just field projections used by typing and
;;        execution rules, not something you write.
;;
;;   def $funcsxt, def $globalsxt, def $tablesxt, def $memsxt
;;     -- given a list of externtype (the type of an import/export), filter
;;        out just the function types / global types / table types / mem
;;        types, preserving order. Used by 6-typing.spectec's Module_ok to
;;        split a module's imports into per-kind lists before building the
;;        typing context. This is a filter-and-project helper, not syntax.
;;
;;   def $dataidx_instr, def $dataidx_instrs, def $dataidx_expr,
;;   def $dataidx_func, def $dataidx_funcs
;;     -- walk an instruction / expression / function body and collect
;;        every `dataidx` mentioned (by memory.init or data.drop). This is
;;        how the spec states a *validation* side-condition ("a module's
;;        data-count section must be consistent with the data indices
;;        actually used") -- it's a free-variable-collection pass, not
;;        something you invoke from WAT.
;;
;;   def $memarg0 = {ALIGN 0, OFFSET 0}
;;     -- the default memarg (what you get when you write e.g. `i32.load`
;;        with no `offset=`/`align=` immediates). It's used inside
;;        8-reduction.spectec's rules for memory.fill/copy/init, which are
;;        *defined* in terms of a loop of implicit byte-at-a-time
;;        loads/stores using this default. You can and do write the
;;        *effect* of $memarg0 constantly (any bare `i32.load8_u` in
;;        1-syntax.wat uses it implicitly) -- but $memarg0 the named
;;        constant is spec shorthand, not a WAT construct of its own.
;;
;; See 1-syntax.wat for `memarg`, `shape`, and packed SIMD lane types
;; (`packtype`) themselves, which *are* category A.

(module)

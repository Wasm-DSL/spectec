;; ============================================================================
;; Companion to specification/wasm-2.0/5-runtime-aux.spectec
;; ============================================================================
;;
;; CATEGORIZATION RESULT: no category-A constructs. Accessor/update helpers
;; over the runtime state defined in 4-runtime.spectec.
;;
;;   def $default_(valtype) : val
;;     -- the zero value for a type: 0 for i32/i64, +0.0 for f32/f64, an
;;        all-zero v128, REF.NULL for funcref/externref. This is *observed*
;;        constantly (every local you declare without an initializer --
;;        `(local $y i32)` in sandbox1.wat from earlier in this project --
;;        starts at exactly this value, per Step_read/call_addr in
;;        8-reduction.spectec) but "$default_" itself is never written;
;;        `(local $y i32)` is the category-A syntax (1-syntax.spectec) that
;;        triggers it.
;;
;;   def $funcsxa, $globalsxa, $tablesxa, $memsxa
;;     -- same filter-by-kind idea as 2-syntax-aux.spectec's $funcsxt/etc.,
;;        just over runtime `externaddr` instead of static `externtype`.
;;        Used when instantiation splits the externaddr* argument (the
;;        resolved imports) into per-kind lists.
;;
;;   def $store, $frame, $funcaddr, $funcinst, $globalinst, $tableinst,
;;   $meminst, $eleminst, $datainst, $moduleinst, $type, $func, $global,
;;   $table, $mem, $elem, $data, $local
;;     -- a long list of field-projection shorthands, e.g. $func(state, x)
;;        follows state -> frame -> moduleinst.FUNCS[x] -> store.FUNCS[that
;;        address] to get the funcinst for local function index x. This is
;;        exactly the address-indirection you'd trace by hand if asked
;;        "how does `call 3` find the function to run" -- but it's spelled
;;        out here purely so 8-reduction.spectec's rules can write
;;        `$func(z, x)` instead of repeating that chain every time.
;;
;;   def $with_local, $with_global, $with_table, $with_tableinst,
;;   $with_mem, $with_meminst, $with_elem, $with_data
;;     -- "functional update" helpers: produce a *new* state that's like
;;        the old one except e.g. one local slot changed. This is how a
;;        purely-functional formal semantics expresses "local.set mutates
;;        a local" without actual mutation. It's the mathematical model of
;;        an effect, not something with its own WAT syntax.
;;
;;   def $growtable, $growmemory
;;     -- the actual growth algorithm behind `table.grow` / `memory.grow`
;;        (category A, in 1-syntax.spectec / exercised in 01-syntax.wat):
;;        append n new default elements, or fail if that would exceed the
;;        declared maximum. You call table.grow / memory.grow; this def is
;;        what decides whether that call succeeds.
;;
;; Nothing here has independent WAT syntax; see 01-syntax.wat for the
;; instructions (local.get/set/tee, global.get/set, table.grow,
;; memory.grow, ...) whose *behavior* these functions define.

(module)

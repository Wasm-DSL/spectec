;; ============================================================================
;; sandbox4.wat -- every field of `moduleinst` (specification/wasm-2.0/
;; 4-runtime.spectec), and the module-level construct that populates it.
;;
;;   syntax moduleinst = { TYPES functype*, FUNCS funcaddr*, GLOBALS
;;     globaladdr*, TABLES tableaddr*, MEMS memaddr*, ELEMS elemaddr*,
;;     DATAS dataaddr*, EXPORTS exportinst* }
;;
;; moduleinst is what your module *becomes* once instantiated -- it's
;; exactly the "Module" object Chrome DevTools shows in the Scope pane
;; while paused (see wasmdebug). $allocmodule (specification/wasm-2.0/
;; 9-module.spectec) is the function that builds one; every comment below
;; points at the piece of *this* file responsible for one of its fields.
;; ============================================================================

(module
  ;; ---------------------------------------------------------------
  ;; moduleinst.TYPES = every (type ...) declaration, verbatim, in order.
  ;; The ONE field with no "imported half": types are descriptions, not
  ;; instances, so there's nothing to import -- every module just states
  ;; its own. ($allocmodule: `TYPES ft*` -- copied straight from the
  ;; module's type* field, no allocation needed.)
  ;; ---------------------------------------------------------------
  (type $unary_i32 (func (param i32) (result i32)))

  ;; ---------------------------------------------------------------
  ;; moduleinst.FUNCS = [addresses of every imported func] followed by
  ;; [addresses of every locally-defined func], in that order.
  ;; ($allocmodule: `FUNCS fa_ex* fa*` -- fa_ex* from the externaddr*
  ;; you instantiate with, fa* freshly allocated by $allocfuncs.)
  ;; This import makes $double function index 0 in THIS module; $sq
  ;; below becomes index 1 -- imports always take the lowest indices.
  ;; ---------------------------------------------------------------
  (import "env" "double" (func $double (param i32) (result i32)))

  ;; ---------------------------------------------------------------
  ;; moduleinst.GLOBALS: same imported-then-local pattern as FUNCS.
  ;; No imported global here (kept to one import so this file stays
  ;; verifiable end-to-end with a plain `wasm-interp --dummy-import-func`,
  ;; which can only stub *function* imports) -- but the mechanism is
  ;; identical; this local global would simply follow any imported ones.
  ;; ---------------------------------------------------------------
  (global $count (export "count") (mut i32) (i32.const 0))  ;; bumped by $start_fn, below

  ;; ---------------------------------------------------------------
  ;; moduleinst.TABLES: same imported-then-local pattern again. WASM
  ;; 2.0's reference-types feature allows any number of tables.
  ;; ---------------------------------------------------------------
  (table $tbl (export "tbl") 2 funcref)

  ;; ---------------------------------------------------------------
  ;; moduleinst.MEMS: same pattern -- but WASM 2.0 caps the *combined*
  ;; import+local memory count at exactly one (try adding a second
  ;; `memory` here: wat2wasm rejects it with "only one memory block
  ;; allowed". Multiple memories are a later, post-2.0 proposal.) So
  ;; this is necessarily either one import OR one local declaration,
  ;; never both, never more.
  ;; ---------------------------------------------------------------
  (memory $mem (export "mem") 1)

  ;; ---------------------------------------------------------------
  ;; moduleinst.FUNCS, local half. Deliberately pure and simple so its
  ;; result is trivial to verify: sq(x) = x*x.
  ;; ---------------------------------------------------------------
  (func $sq (export "sq") (type $unary_i32)
    (i32.mul (local.get 0) (local.get 0)))

  ;; A second local function, whose only job is to prove $double (the
  ;; import, above) is a real, callable address in FUNCS -- not just a
  ;; placeholder. Verify with:
  ;;   wasm-interp sandbox4.wasm --dummy-import-func --run-all-exports
  ;; wasm-interp's dummy stub always returns 0 regardless of the input,
  ;; so this demo returns 0 *on this tool* -- a real host providing an
  ;; actual "double" function would make it return 42. wasmdebug's stub
  ;; behaves the same way (logs the call, returns zero) for the same
  ;; reason: neither tool knows what a real host's `env.double` should
  ;; compute.
  (func $call_the_import (export "call_the_import") (result i32)
    (call $double (i32.const 21)))

  ;; ---------------------------------------------------------------
  ;; moduleinst.ELEMS: one eleminst address per (elem ...) segment.
  ;; Unlike FUNCS/GLOBALS/TABLES/MEMS, this is NEVER "imported ++
  ;; local" -- there is no such thing as importing an elem segment, so
  ;; ELEMS is always 100% local. ($allocmodule: `ELEMS ea*` -- no
  ;; ea_ex* prefix, contrast with FUNCS/GLOBALS/TABLES/MEMS above.)
  ;; This one is ACTIVE, so per $runelem (9-module.spectec) it writes
  ;; $sq into $tbl[0] automatically, once, during instantiation --
  ;; before any of your code runs.
  ;; ---------------------------------------------------------------
  (elem $e (table $tbl) (i32.const 0) funcref (ref.func $sq))

  ;; ---------------------------------------------------------------
  ;; moduleinst.DATAS: same story as ELEMS -- always 100% local, one
  ;; datainst address per (data ...) segment. ACTIVE, so per $rundata
  ;; it writes "hi" into $mem at address 0 automatically, during
  ;; instantiation.
  ;; ---------------------------------------------------------------
  (data $d (memory $mem) (i32.const 0) "hi")

  ;; Two more tiny local functions, purely to make the ACTIVE elem/data
  ;; segments' effects observable (not new moduleinst fields -- just
  ;; verification of the two above).
  (func $check_elem_ran (export "check_elem_ran") (result i32)
    (call_indirect (type $unary_i32) (i32.const 5) (i32.const 0)))  ;; sq(5) via $tbl[0] -- expect 25
  (func $check_data_ran (export "check_data_ran") (result i32)
    (i32.load8_u (i32.const 0)))                                    ;; 'h' -- expect 104

  ;; ---------------------------------------------------------------
  ;; start: NOT a moduleinst field! There is no START slot in the
  ;; record at all -- go back and check 4-runtime.spectec's syntax
  ;; moduleinst above; it isn't there. $instantiate (9-module.spectec)
  ;; consumes `start?` directly: after allocation and after the elem/
  ;; data segments run, it appends one extra `(CALL x)` to the
  ;; instantiation config -- and that's the last anyone ever asks
  ;; about `start` again. Its only lasting trace in the moduleinst is
  ;; whatever side effect it had. Here: bumping $count from 0 to 1,
  ;; observable via the "count" export or $read_count below.
  ;; ---------------------------------------------------------------
  (start $start_fn)
  (func $start_fn
    (global.set $count (i32.add (global.get $count) (i32.const 1))))

  (func $read_count (export "read_count") (result i32)
    (global.get $count))                                            ;; expect 1

  ;; ---------------------------------------------------------------
  ;; moduleinst.EXPORTS: one exportinst per (export ...), regardless of
  ;; what kind of thing it names -- func/global/table/mem all end up in
  ;; the same flat EXPORTS list ($instexport, 9-module.spectec, has one
  ;; case per externidx kind but they all produce the same exportinst
  ;; shape: { NAME name, ADDR externaddr }). Every export above was
  ;; written inline, e.g. (func (export "sq") ...) -- that's pure
  ;; syntax sugar for a standalone (export "sq" (func $sq)) clause
  ;; placed here instead; same moduleinst either way. This file's
  ;; EXPORTS ends up with 8 entries: 5 func, 1 global, 1 table, 1 mem.
  ;; ---------------------------------------------------------------
)

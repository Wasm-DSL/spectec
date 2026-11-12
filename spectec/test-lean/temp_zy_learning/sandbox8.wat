;; ============================================================================
;; sandbox8.wat -- two REAL uses of reference types, not just null-checks.
;;
;;   1. externref as a held host handle: the host hands us an opaque
;;      "logger" reference ONCE (init), and we hold onto it across many
;;      later calls (report), passing it back each time -- exactly the
;;      "canvas context" / "file handle" pattern from the reference-types
;;      proposal's own motivation (avoiding a hand-rolled integer handle
;;      table on the host side).
;;
;;   2. funcref as a caller-supplied operation: the CALLER decides which
;;      binary operation to fold an array with (add, or max) and passes
;;      THAT as a funcref parameter -- the same shape as a C comparator
;;      function pointer (qsort-style), just typed and validated.
;; ============================================================================

(module
  ;; ---------------------------------------------------------------
  ;; Part 1: externref as a held host handle
  ;; ---------------------------------------------------------------

  ;; The host provides this: given OUR remembered handle to its logger,
  ;; and a value, do whatever host-side logging that handle refers to.
  ;; We never learn or care what's actually behind the handle.
  (import "host" "log" (func $host_log (param externref) (param i32)))

  (global $logger (mut externref) (ref.null extern))

  ;; Called ONCE: the host hands us a reference and we hold onto it.
  (func (export "init") (param $ctx externref)
    (global.set $logger (local.get $ctx)))

  ;; Called MANY times afterward: reuse the SAME remembered handle every
  ;; time, without the host needing to pass it again on each call.
  (func (export "report") (param $value i32)
    (call $host_log (global.get $logger) (local.get $value)))

  ;; ---------------------------------------------------------------
  ;; Part 2: funcref as a caller-supplied operation
  ;; ---------------------------------------------------------------

  (type $binop_t (func (param i32 i32) (result i32)))

  (func $add (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1)))
  (func $max (param i32 i32) (result i32)
    (select (local.get 0) (local.get 1)
      (i32.gt_s (local.get 0) (local.get 1))))
  ;; Both are legal targets of `ref.func` from outside their own body
  ;; (satisfies the "declared references" rule from a few turns back).
  (elem declare func $add $max)

  ;; A table exists purely as the mechanism REQUIRED to call a held
  ;; funcref in 2.0 (no direct call_ref yet -- see a couple turns back).
  ;; One slot: "whichever operation is currently selected."
  (table $op 1 funcref)

  ;; The CALLER decides which operation to use, and hands it to us as an
  ;; ordinary funcref parameter -- we never hard-code $add or $max here.
  (func $set_op (export "set_op") (param $f funcref)
    (table.set $op (i32.const 0) (local.get $f)))

  ;; TEST-ONLY convenience wrappers: a real host (e.g. JS) can pass
  ;; `instance.exports.add` straight into `set_op` as an ordinary funcref
  ;; argument, but the reference interpreter's script format has no way
  ;; to construct "the export of another module" as a script-level
  ;; constant. These two just call the SAME general set_op internally,
  ;; so `reduce` below is exercised through the real mechanism either way.
  (func (export "use_add") (call $set_op (ref.func $add)))
  (func (export "use_max") (call $set_op (ref.func $max)))

  ;; Folds an array in linear memory using WHATEVER operation was most
  ;; recently selected via set_op -- the same shape as C's
  ;; `int reduce(int *arr, int n, int init, int (*op)(int,int))`.
  (memory (export "mem") 1)
  ;; sample data for exercising `reduce`: [1,2,3,4] at offset 0, [3,9,2,7] at offset 16
  (data (i32.const 0)
    "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00"
    "\03\00\00\00\09\00\00\00\02\00\00\00\07\00\00\00")

  (func (export "reduce") (param $ptr i32) (param $len i32) (param $init i32) (result i32)
    (local $i i32)
    (local $acc i32)
    (local.set $acc (local.get $init))
    (local.set $i (i32.const 0))
    (block $done
      (loop $loop
        (br_if $done (i32.ge_u (local.get $i) (local.get $len)))
        (local.set $acc
          (call_indirect (type $binop_t)
            (local.get $acc)
            (i32.load (i32.add (local.get $ptr) (i32.mul (local.get $i) (i32.const 4))))
            (i32.const 0)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $loop)))
    (local.get $acc))
)

(module
  ;; type* -- a shared function type, used both to declare $double's own
  ;; signature and to validate the indirect call inside $run.
  (type $binop_t (func (param i32) (result i32)))

  ;; import* -- a host logging hook, called both from `start` and from $run.
  (import "env" "log" (func $log (param i32)))

  ;; global* -- a call counter: read AND written on every call to $run.
  (global $calls (export "calls") (mut i32) (i32.const 0))

  ;; table* + elem* -- $double is reachable indirectly through table[0].
  (table 1 funcref)
  (elem (i32.const 0) $double)

  ;; mem* + data* -- memory seeded with a real i32 value (1000, little-endian)
  ;; at byte 0, read back at runtime by $run.
  (memory (export "mem") 1)
  (data (i32.const 0) "\e8\03\00\00")

  ;; func* -- $double is the indirect-call target; $init runs once at
  ;; instantiation via `start`; $run is the externally-callable entry point.
  (func $double (type $binop_t)
    local.get 0
    i32.const 2
    i32.mul)

  (func $init
    i32.const 0
    i32.load
    call $log)

  (func $run (export "run") (param $x i32) (result i32)
    (local $call_no i32)
    (local $seed i32)
    (local $doubled i32)

    ;; bump the call counter; remember the value from BEFORE incrementing
    global.get $calls
    local.set $call_no
    global.get $calls
    i32.const 1
    i32.add
    global.set $calls

    ;; re-read the data-segment-seeded value out of memory
    i32.const 0
    i32.load
    local.set $seed

    ;; call $double indirectly through the table; $binop_t validates the
    ;; callee found there actually has this signature
    local.get $x
    i32.const 0
    call_indirect (type $binop_t)
    local.set $doubled

    local.get $doubled
    call $log

    local.get $doubled
    local.get $seed
    i32.add
    local.get $call_no
    i32.add
  )

  ;; start? -- runs $init automatically at instantiation, before any export
  ;; is ever called, proving the memory/data/import wiring works up front.
  (start $init)
)

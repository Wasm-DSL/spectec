;; Test globals

(module
  (global (import "spectest" "global_i32") i32)
  (global (import "spectest" "global_i64") i64)
  
  (global $z3 i32 (i32.add (i32.sub (i32.mul (i32.const 20) (i32.const 2)) (i32.const 2)) (i32.const 4)))
  (global $z4 i64 (i64.add (i64.sub (i64.mul (i64.const 20) (i64.const 2)) (i64.const 2)) (i64.const 5)))
  (global $z5 i32 (i32.add (global.get 0) (i32.const 42)))
  (global $z6 i64 (i64.add (global.get 1) (i64.const 42)))
  
  (func (export "get-z3") (result i32) (global.get $z3))
  (func (export "get-z4") (result i64) (global.get $z4))
  (func (export "get-z5") (result i32) (global.get $z5))
  (func (export "get-z6") (result i64) (global.get $z6))
)

(assert_return (invoke "get-z3") (i32.const 42))
(assert_return (invoke "get-z4") (i64.const 43))
(assert_return (invoke "get-z5") (i32.const 708))
(assert_return (invoke "get-z6") (i64.const 708))

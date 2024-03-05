
(module
  (memory 1)
  (data (i32.const 0) "ABC\a7D") (data (i32.const 20) "WASM")
  (func (export "foo") (result i32) (i32.const 42))
)

(assert_return (invoke "foo") (i32.const 42))

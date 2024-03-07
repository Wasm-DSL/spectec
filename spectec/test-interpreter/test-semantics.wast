
(module
  (memory 1)
  (data (i32.const 0) "ABC\a7D") (data (i32.const 20) "WASM")
  (func (export "data") (result i32) (i32.const 1))
)

(assert_return (invoke "data") (i32.const 1))

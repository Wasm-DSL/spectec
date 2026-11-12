(module
  (table 2 funcref)
  (func $f1 (param $p1 i32) (result i32)
    i32.const 42
  )
  (func $f2 (param $p1 i32) (result i32)
    i32.const 13
  )
  (elem (i32.const 0) $f1 $f2)
  (type $return_i32 (func (param i32) (result i32)))
  (func (export "callByIndex") (param $i i32) (result i32)
    local.get $i
    call_indirect (type $return_i32)
  )
)
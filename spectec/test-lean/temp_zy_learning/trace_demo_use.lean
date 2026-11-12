import trace_demo_lib

set_option trace.kitchen.log true in
#eval show Lean.Meta.MetaM Unit from do
  let r ← totalCost 3 4
  IO.println s!"{r}"

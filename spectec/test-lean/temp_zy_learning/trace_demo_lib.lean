import Lean
open Lean

initialize registerTraceClass `kitchen.log

def totalCost (apples bananas : Nat) : Meta.MetaM Nat := do
  trace[kitchen.log] "adding up the basket"
  return apples + bananas

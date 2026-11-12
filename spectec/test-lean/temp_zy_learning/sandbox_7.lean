/-
  Testing whether a type that merely REFERENCES a self-nested type (rather
  than being self-nested itself) can get DecidableEq via Lean's ordinary
  stock `deriving` clause, once the self-nested type has a real DecidableEq
  instance from ExtendedDeriveDecEq's `derive_deceq` -- or whether it too
  needs `derive_deceq`. This determines how many of wasm2.0.lean's 13
  SelfNestedDataCategory members actually need the custom mechanism versus
  how many would just start working on their own.
-/
import ExtendedDeriveDecEq

/- Self-nested root, mirroring `instr` -/
inductive Instr where
  | nop
  | block (body : List Instr)
deriving Inhabited, BEq

derive_deceq Instr

#check (inferInstance : DecidableEq Instr)


/- Ordinary type that merely references Instr in a field -- NOT self-nested
   itself, mirroring `func`/`elemmode`/etc. Uses Lean's plain stock
   `deriving`, not `derive_deceq`. -/
structure Func where
  body : List Instr
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

#check (inferInstance : DecidableEq Func)


/- Second-order: a type referencing Func (which itself only got DecidableEq
   via the previous step's ordinary stock derive) -- mirrors funcinst
   referencing func. -/
structure FuncInst where
  code : Func
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

#check (inferInstance : DecidableEq FuncInst)

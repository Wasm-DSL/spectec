-- generalize h : e = x uses TWO names: h (the new equation hypothesis)
-- and x (the new generalized variable). What happens if you give BOTH
-- of them the exact same name, as in `generalize ft : e = ft`?

example (a b : Nat) (hab : a = b + 1) : a > 0 := by
  generalize ft : a = ft
  trace_state
  sorry

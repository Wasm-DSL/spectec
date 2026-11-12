def part (b : Bool) : Nat :=
  match b with
  | true => 1

#eval! part false

partial def collatzSteps (n : Nat) : Nat :=
  if n = 1 then 0
  else if n % 2 = 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

#eval collatzSteps 27   -- 111

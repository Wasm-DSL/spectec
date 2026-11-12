def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Inductive Type Definition at: test-lean/temp_zy_learning/scratch_minus_recs_pipeline_repro.spectec:16.1-16.32 -/
inductive tag : Type where
  | LEFT : tag
  | RIGHT (_ : Nat) : tag
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/- Auxiliary Definition at: test-lean/temp_zy_learning/scratch_minus_recs_pipeline_repro.spectec:18.1-18.66 -/
def minus (var_0_lst : List tag) (var_1_lst : List Nat) : Option (List tag × List Nat) :=
  match var_0_lst, var_1_lst with
  | [], [] => some (([], []))
  | tag.LEFT :: t_lst, n_1 :: n'_lst => minus t_lst n'_lst
  | (tag.RIGHT x) :: t_lst, n_1 :: n'_lst => let (t''_lst, n''_lst) := Option.get! (minus t_lst n'_lst)
  some (([tag.RIGHT x] ++ t''_lst, [n_1] ++ n''_lst))
  | _, _ => none

def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Inductive Type Definition at: ./test-lean/temp_zy_learning/scratch_minus_recs_pipeline_repro.spectec:16.1-16.32 -/
inductive tag : Type where
  | LEFT : tag
  | RIGHT (_ : Nat) : tag
deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

mutual
/- Inductive Relations Definition at: ./test-lean/temp_zy_learning/scratch_minus_recs_pipeline_repro.spectec:18.6-18.12 -/
inductive fun_minus_before_fun_minus_case_3 : List tag → List Nat → Prop where
  | fun_minus_before_fun_minus_case_3_fun_minus_case_2 (x : Nat) (t_lst : List tag) (n_1 : Nat) (n'_lst : List Nat) (t''_lst : List tag) (n''_lst : List Nat) (var_0 : Option (List tag × List Nat)) :
    fun_minus t_lst n'_lst var_0 →
    var_0 ≠ none →
    ((t''_lst, n''_lst)) = (Option.get! var_0) →
    fun_minus_before_fun_minus_case_3 ([tag.RIGHT x] ++ t_lst) ([n_1] ++ n'_lst)
  | fun_minus_before_fun_minus_case_3_fun_minus_case_1 (t_lst : List tag) (n_1 : Nat) (n'_lst : List Nat) (var_0 : Option (List tag × List Nat)) : fun_minus_before_fun_minus_case_3 ([tag.LEFT] ++ t_lst) ([n_1] ++ n'_lst)
  | fun_minus_before_fun_minus_case_3_fun_minus_case_0 : fun_minus_before_fun_minus_case_3 [] []

/- Inductive Relations Definition at: ./test-lean/temp_zy_learning/scratch_minus_recs_pipeline_repro.spectec:18.6-18.12 -/
inductive fun_minus : List tag → List Nat → Option (List tag × List Nat) → Prop where
  | fun_minus_fun_minus_case_0 : fun_minus [] [] (some (([], [])))
  | fun_minus_fun_minus_case_1 (t_lst : List tag) (n_1 : Nat) (n'_lst : List Nat) (var_0 : Option (List tag × List Nat)) :
    fun_minus t_lst n'_lst var_0 →
    fun_minus ([tag.LEFT] ++ t_lst) ([n_1] ++ n'_lst) var_0
  | fun_minus_fun_minus_case_2 (x : Nat) (t_lst : List tag) (n_1 : Nat) (n'_lst : List Nat) (t''_lst : List tag) (n''_lst : List Nat) (var_0 : Option (List tag × List Nat)) :
    fun_minus t_lst n'_lst var_0 →
    var_0 ≠ none →
    ((t''_lst, n''_lst)) = (Option.get! var_0) →
    fun_minus ([tag.RIGHT x] ++ t_lst) ([n_1] ++ n'_lst) (some (([tag.RIGHT x] ++ t''_lst, [n_1] ++ n''_lst)))
  | fun_minus_case_3 (x0 : List tag) (x1 : List Nat) :
    ¬ fun_minus_before_fun_minus_case_3 x0 x1 →
    fun_minus x0 x1 none


end

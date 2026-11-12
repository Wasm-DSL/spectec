def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Inductive Relations Definition at: test_beq.spectec:16.6-16.13 -/
inductive fun_count_ (X : Type) : List X → Nat → Prop where
  | fun_count__case_0 : fun_count_ X [] 0
  | fun_count__case_1 (w : X) (w'_lst : List X) (var_0 : Nat) :
    fun_count_ X w'_lst var_0 →
    fun_count_ X ([w] ++ w'_lst) (1 + var_0)


/- Inductive Relations Definition at: test_beq.spectec:20.6-20.15 -/
inductive fun_reverse_ (X : Type) : List X → List X → Prop where
  | fun_reverse__case_0 : fun_reverse_ X [] []
  | fun_reverse__case_1 (w : X) (w'_lst : List X) (var_0 : List X) :
    fun_reverse_ X w'_lst var_0 →
    fun_reverse_ X ([w] ++ w'_lst) (var_0 ++ [w])


/- Auxiliary Definition at: test_beq.spectec:30.1-30.35 -/
def elem_ (X : Type) [BEq X] (X_0 : X) (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => false
  | _ => List.contains var_0_lst X_0

/- Inductive Relations Definition at: test_beq.spectec:34.6-34.15 -/
inductive fun_remove1_ (X : Type) [BEq X] : X → List X → List X → Prop where
  | fun_remove1__case_0 (w : X) : fun_remove1_ X w [] []
  | fun_remove1__case_1 (w : X) (w_1 : X) (w'_lst : List X) (var_0 : List X) :
    fun_remove1_ X w w'_lst var_0 →
    fun_remove1_ X w ([w_1] ++ w'_lst) (if
      w == w_1
    then
      w'_lst
    else
      [w_1] ++ var_0)


/- Inductive Relations Definition at: test_beq.spectec:44.6-44.14 -/
inductive fun_subset_ (X : Type) [BEq X] : List X → List X → Bool → Prop where
  | fun_subset__case_0 (w'_lst : List X) : fun_subset_ X [] w'_lst true
  | fun_subset__case_1 (w_1 : X) (w_lst : List X) (w'_lst : List X) (var_0 : Bool) :
    fun_subset_ X w_lst w'_lst var_0 →
    fun_subset_ X ([w_1] ++ w_lst) w'_lst ((elem_ X w_1 w'_lst) && var_0)


/- Inductive Relations Definition at: test_beq.spectec:53.6-53.18 -/
inductive fun_equal_sets_ (X : Type) [BEq X] : List X → List X → Bool → Prop where
  | fun_equal_sets__case_0 (w_lst : List X) (w'_lst : List X) (var_1 : Bool) (var_0 : Bool) :
    fun_subset_ X w'_lst w_lst var_1 →
    fun_subset_ X w_lst w'_lst var_0 →
    fun_equal_sets_ X w_lst w'_lst (var_0 && var_1)


mutual
/- Inductive Relations Definition at: test_beq.spectec:61.6-61.16 -/
inductive fun_even_len_ (X : Type) : List X → Bool → Prop where
  | fun_even_len__case_0 : fun_even_len_ X [] true
  | fun_even_len__case_1 (w : X) (w'_lst : List X) (var_0 : Bool) :
    fun_odd_len_ X w'_lst var_0 →
    fun_even_len_ X ([w] ++ w'_lst) var_0

/- Inductive Relations Definition at: test_beq.spectec:62.6-62.15 -/
inductive fun_odd_len_ (X : Type) : List X → Bool → Prop where
  | fun_odd_len__case_0 : fun_odd_len_ X [] false
  | fun_odd_len__case_1 (w : X) (w'_lst : List X) (var_0 : Bool) :
    fun_even_len_ X w'_lst var_0 →
    fun_odd_len_ X ([w] ++ w'_lst) var_0


end

/- Inductive Relations Definition at: test_beq.spectec:77.6-77.18 -/
inductive fun_has_dup_tl_ (X : Type) [BEq X] : X → List X → Bool → Prop where
  | fun_has_dup_tl__case_0 (w : X) : fun_has_dup_tl_ X w [] false
  | fun_has_dup_tl__case_1 (w : X) (w_1 : X) (w'_lst : List X) (var_0 : Bool) :
    fun_has_dup_tl_ X w w'_lst var_0 →
    fun_has_dup_tl_ X w ([w_1] ++ w'_lst) (if
      w == w_1
    then
      true
    else
      var_0)


/- Inductive Relations Definition at: test_beq.spectec:76.6-76.15 -/
inductive fun_has_dup_ (X : Type) [BEq X] : List X → Bool → Prop where
  | fun_has_dup__case_0 : fun_has_dup_ X [] false
  | fun_has_dup__case_1 (w : X) (w'_lst : List X) (var_1 : Bool) (var_0 : Bool) :
    fun_has_dup_ X w'_lst var_1 →
    fun_has_dup_tl_ X w w'_lst var_0 →
    fun_has_dup_ X ([w] ++ w'_lst) (var_0 || var_1)


/- Inductive Relations Definition at: test_beq.spectec:91.6-91.14 -/
inductive fun_lookup_ (K : Type) [BEq K] (V : Type) : List K → List V → K → Option V → Prop where
  | fun_lookup__case_0 (k : K) : fun_lookup_ K V [] [] k none
  | fun_lookup__case_1 (k_1 : K) (k'_lst : List K) (v_1 : V) (v'_lst : List V) (k : K) (var_0 : Option V) :
    fun_lookup_ K V k'_lst v'_lst k var_0 →
    fun_lookup_ K V ([k_1] ++ k'_lst) ([v_1] ++ v'_lst) k (if
      k == k_1
    then
      some v_1
    else
      var_0)


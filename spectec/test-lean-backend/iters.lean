/- Preamble -/
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

instance : Append (Option a) where
  append := fun o1 o2 => match o1 with | none => o2 | _ => o1
    
def Forall (R : α → Prop) (xs : List α) : Prop :=
  ∀ x ∈ xs, R x
def Forall₂ (R : α → β → Prop) (xs : List α) (ys : List β) : Prop :=
  ∀ x y, (x,y) ∈ List.zip xs ys → R x y
def Forall₃ (R : α → β → γ → Prop) (xs : List α) (ys : List β) (zs : List γ) : Prop :=
  ∀ x y z, (x,y,z) ∈ List.zip xs (List.zip ys zs) → R x y z
    
macro "opaqueDef" : term => `(by first | exact Inhabited.default | intros; assumption)

/- written manually due to `BEq` constraint -/
def disjoint_ (X : Type) [BEq X] : ∀ (var_0 : (List X)), Bool
  | [] => true
  | (w :: w'_lst) => ((!(List.contains w'_lst w)) && (disjoint_ X w'_lst))

/- written manually due to `BEq` constraint -/
def setminus_ (X : Type) [BEq X] (l1 l2 : List X) : List X :=
  l1.filter (fun x => !(List.contains l2 x))
/- Generated Code -/

/- Auxiliary Definition at: /home/zhengyew/spectec/spectec/test-lean-backend/test.spectec:5.1-5.23 -/
def zeros : ∀  (nat : Nat) , (List Nat)
  | n =>
    (List.replicate n 0)


/- Inductive Relations Definition at: /home/zhengyew/spectec/spectec/test-lean-backend/test.spectec:8.6-8.20 -/
inductive fun_range_shifted : Nat -> Nat -> (List Nat) -> Prop where
  | fun_range_shifted_case_0 : forall (b : Nat) (n : Nat) (i_lst : (List Nat)), fun_range_shifted b n (List.map (fun (i : Nat) => (b + i)) i_lst)

/- Auxiliary Definition at: /home/zhengyew/spectec/spectec/test-lean-backend/test.spectec:11.1-11.22 -/
def inc : ∀  (var_0 : (List Nat)) , (List Nat)
  | x_lst =>
    (List.map (fun (x : Nat) => (x + 1)) x_lst)


/- Auxiliary Definition at: /home/zhengyew/spectec/spectec/test-lean-backend/test.spectec:14.1-14.34 -/
def add_pairs : ∀  (var_0 : (List Nat)) (var_1 : (List Nat)) , (List Nat)
  | x_lst, y_lst =>
    (List.zipWith (fun (x : Nat) (y : Nat) => (x + y)) x_lst y_lst)


/- Auxiliary Definition at: /home/zhengyew/spectec/spectec/test-lean-backend/test.spectec:17.1-17.26 -/
def inc_opt : ∀  (var_0 : (Option Nat)) , (Option Nat)
  | x_opt =>
    (Option.map (fun (x : Nat) => (x + 1)) x_opt)


/- Inductive Relations Definition at: /home/zhengyew/spectec/spectec/test-lean-backend/test.spectec:20.6-20.15 -/
inductive fun_double_n : Nat -> (List Nat) -> (List Nat) -> Prop where
  | fun_double_n_case_0 : forall (n : Nat) (x_lst : (List Nat)), fun_double_n n x_lst (List.map (fun (x : Nat) => (x + x)) x_lst)

/- Inductive Relations Definition at: /home/zhengyew/spectec/spectec/test-lean-backend/test.spectec:23.6-23.18 -/
inductive fun_indexed_add : Nat -> (List Nat) -> (List Nat) -> Prop where
  | fun_indexed_add_case_0 : forall (n : Nat) (x_lst : (List Nat)) (i_lst : (List Nat)), fun_indexed_add n x_lst (List.zipWith (fun (i : Nat) (x : Nat) => (x + i)) i_lst x_lst)

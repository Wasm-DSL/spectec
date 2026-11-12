def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

def zeros (nat : Nat) : List Nat :=
  match nat with
  | n => List.replicate n 0

def range_shifted (nat : Nat) (nat_0 : Nat) : List Nat :=
  match nat, nat_0 with
  | b, n => List.range n |>.map (fun i => b + i)

def inc (var_0 : List Nat) : List Nat :=
  match var_0 with
  | x_lst => x_lst |>.map (fun x_elem => x_elem + 1)

def add_pairs (var_0 : List Nat) (var_1 : List Nat) : List Nat :=
  match var_0, var_1 with
  | x_lst, y_lst => x_lst |>.map (fun x_elem y_elem => x_elem + y_elem) |>.ap y_lst

def inc_opt (var_0 : Option Nat) : Option Nat :=
  match var_0 with
  | x_opt => x_opt |>.map (fun x_elem => x_elem + 1)

inductive fun_double_n : Nat → List Nat → List Nat → Prop where
  | fun_double_n_case_0 (n : Nat) (x_lst : List Nat) : n == (List.length x_lst) → fun_double_n n x_lst (x_lst |>.map (fun x_elem => x_elem + x_elem))


inductive fun_indexed_add : Nat → List Nat → List Nat → Prop where
  | fun_indexed_add_case_0 (n : Nat) (x_lst : List Nat) : n == (List.length x_lst) → fun_indexed_add n x_lst (List.range n |>.map (fun i x_elem => x_elem + i) |>.ap x_lst)


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

/- Type Alias Definition at: ../../../../specification/wasm-3.0/0.1-aux.vars.spectec:5.1-5.32 -/
abbrev N : Type := Nat

/- Type Alias Definition at: ../../../../specification/wasm-3.0/0.1-aux.vars.spectec:6.1-6.32 -/
abbrev M : Type := Nat

/- Type Alias Definition at: ../../../../specification/wasm-3.0/0.1-aux.vars.spectec:7.1-7.32 -/
abbrev K : Type := Nat

/- Type Alias Definition at: ../../../../specification/wasm-3.0/0.1-aux.vars.spectec:8.1-8.32 -/
abbrev n : Type := Nat

/- Type Alias Definition at: ../../../../specification/wasm-3.0/0.1-aux.vars.spectec:9.1-9.32 -/
abbrev m : Type := Nat

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:5.1-5.25 -/
def min : ∀  (nat : Nat) (nat_0 : Nat) , Nat
  | i, j =>
    (if (i <= j) then i else j)


/- Recursive Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:9.1-9.56 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:9.6-9.10 -/
inductive fun_sum : (List Nat) -> Nat -> Prop where
  | fun_sum_case_0 : fun_sum [] 0
  | fun_sum_case_1 : forall (v_n : Nat) (n'_lst : (List n)) (var_0 : Nat), 
    (fun_sum n'_lst var_0) ->
    fun_sum ([v_n] ++ n'_lst) (v_n + var_0)

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:13.1-13.57 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/0.2-aux.num.spectec:13.6-13.11 -/
inductive fun_prod : (List Nat) -> Nat -> Prop where
  | fun_prod_case_0 : fun_prod [] 1
  | fun_prod_case_1 : forall (v_n : Nat) (n'_lst : (List n)) (var_0 : Nat), 
    (fun_prod n'_lst var_0) ->
    fun_prod ([v_n] ++ n'_lst) (v_n * var_0)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:7.1-7.44 -/
def opt_ : ∀  (X : Type) (var_0 : (List X)) , (Option X)
  | X, [] =>
    none
  | X, [w] =>
    (some w)


/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:14.1-14.82 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:14.1-14.82 -/
def concat_ : ∀  (X : Type) (var_0 : (List (List X))) , (List X)
  | X, [] =>
    []
  | X, (w_lst :: w'_lst_lst) =>
    (w_lst ++ (concat_ X w'_lst_lst))


/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:18.1-18.89 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:18.1-18.89 -/
def concatn_ : ∀  (X : Type) (var_0 : (List (List X))) (nat : Nat) , (List X)
  | X, [], v_n =>
    []
  | X, (w_lst :: w'_lst_lst), v_n =>
    (w_lst ++ (concatn_ X w'_lst_lst v_n))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:22.1-22.58 -/
def concatopt_ : ∀  (X : Type) (var_0 : (List (Option X))) , (List X)
  | X, [] =>
    []
  | X, (w_opt :: w'_opt_lst) =>
    ((Option.toList w_opt) ++ (concat_ X (List.map (fun (w'_opt : (Option X)) => (Option.toList w'_opt)) w'_opt_lst)))


/- Axiom Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:26.1-26.39 -/
opaque inv_concat_ : forall (X : Type) (var_0 : (List X)), (List (List X)) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:29.1-29.45 -/
opaque inv_concatn_ : forall (X : Type) (nat : Nat) (var_0 : (List X)), (List (List X)) := opaqueDef

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:35.1-35.78 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:35.1-35.78 -/
/- elided, builtin -/

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:40.1-40.38 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:40.1-40.38 -/
/- elided, builtin -/

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:39.1-39.56 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:39.1-39.56 -/
/- elided, builtin -/

/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:51.1-51.46 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:51.1-51.46 -/
def setproduct2_ : ∀  (X : Type) (X_0 : X) (var_0 : (List (List X))) , (List (List X))
  | X, w_1, [] =>
    []
  | X, w_1, (w'_lst :: w_lst_lst) =>
    ([([w_1] ++ w'_lst)] ++ (setproduct2_ X w_1 w_lst_lst))


/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:50.1-50.47 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:50.1-50.47 -/
def setproduct1_ : ∀  (X : Type) (var_0 : (List X)) (var_1 : (List (List X))) , (List (List X))
  | X, [], w_lst_lst =>
    []
  | X, (w_1 :: w'_lst), w_lst_lst =>
    ((setproduct2_ X w_1 w_lst_lst) ++ (setproduct1_ X w'_lst w_lst_lst))


/- Recursive Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:49.1-49.84 -/
/- Auxiliary Definition at: ../../../../specification/wasm-3.0/0.3-aux.seq.spectec:49.1-49.84 -/
def setproduct_ : ∀  (X : Type) (var_0 : (List (List X))) , (List (List X))
  | X, [] =>
    [[]]
  | X, (w_1_lst :: w_lst_lst) =>
    (setproduct1_ X w_1_lst (setproduct_ X w_lst_lst))


/- Axiom Definition at: ../../../../specification/wasm-3.0/1.0-syntax.profiles.spectec:5.1-5.29 -/
opaque ND : Bool := opaqueDef

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:7.1-7.37 -/
inductive bit : Type where
  | mk_bit (i : Nat) : bit
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:7.8-7.11 -/
inductive wf_bit : bit -> Prop where
  | bit_case_0 : forall (i : Nat), 
    ((i == 0) || (i == 1)) ->
    wf_bit (.mk_bit i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:8.1-8.50 -/
inductive byte : Type where
  | mk_byte (i : Nat) : byte
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:8.1-8.50 -/
def proj_byte_0 : ∀  (x : byte) , Nat
  | (.mk_byte v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:8.8-8.12 -/
inductive wf_byte : byte -> Prop where
  | byte_case_0 : forall (i : Nat), 
    ((i >= 0) && (i <= 255)) ->
    wf_byte (.mk_byte i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:10.1-11.25 -/
inductive uN : Type where
  | mk_uN (i : Nat) : uN
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:10.1-11.25 -/
def proj_uN_0 : ∀  (x : uN) , Nat
  | (.mk_uN v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:10.8-10.11 -/
inductive wf_uN : N -> uN -> Prop where
  | uN_case_0 : forall (v_N : N) (i : Nat), 
    ((i >= 0) && (i <= ((((2 ^ v_N) : Nat) - (1 : Nat)) : Nat))) ->
    wf_uN v_N (.mk_uN i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:12.1-13.50 -/
inductive sN : Type where
  | mk_sN (i : Nat) : sN
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:12.1-13.50 -/
def proj_sN_0 : ∀  (x : sN) , Nat
  | (.mk_sN v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:12.8-12.11 -/
inductive wf_sN : N -> sN -> Prop where
  | sN_case_0 : forall (v_N : N) (i : Nat), 
    ((((i >= (0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat))) && (i <= (0 - (1 : Nat)))) || (i == (0 : Nat))) || ((i >= ((1 : Nat))) && (i <= ((((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat)) - (1 : Nat))))) ->
    wf_sN v_N (.mk_sN i)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:14.1-15.8 -/
abbrev iN : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:17.1-17.20 -/
abbrev u8 : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:18.1-18.21 -/
abbrev u16 : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:19.1-19.21 -/
abbrev u31 : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:20.1-20.21 -/
abbrev u32 : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:21.1-21.21 -/
abbrev u64 : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:22.1-22.21 -/
abbrev s33 : Type := sN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:23.1-23.21 -/
abbrev i32 : Type := iN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:24.1-24.21 -/
abbrev i64 : Type := iN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:25.1-25.23 -/
abbrev i128 : Type := iN

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:32.1-32.21 -/
def signif : ∀  (v_N : N) , Nat
  | 32 =>
    23
  | 64 =>
    52


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:36.1-36.20 -/
def expon : ∀  (v_N : N) , Nat
  | 32 =>
    8
  | 64 =>
    11


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:40.1-40.47 -/
def fun_M : ∀  (v_N : N) , Nat
  | v_N =>
    (signif v_N)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:43.1-43.47 -/
def E : ∀  (v_N : N) , Nat
  | v_N =>
    (expon v_N)


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:50.1-50.47 -/
abbrev exp : Type := Nat

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:51.1-55.84 -/
inductive fNmag : Type where
  | NORM (v_m : m) (v_exp : exp) : fNmag
  | SUBNORM (v_m : m) : fNmag
  | INF : fNmag
  | NAN (v_m : m) : fNmag
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:51.8-51.14 -/
inductive wf_fNmag : N -> fNmag -> Prop where
  | fNmag_case_0 : forall (v_N : N) (v_m : m) (v_exp : exp), 
    ((v_m < (2 ^ (fun_M v_N))) && ((((2 : Nat) - ((2 ^ ((((E v_N) : Nat) - (1 : Nat)) : Nat)) : Nat)) <= v_exp) && (v_exp <= (((2 ^ ((((E v_N) : Nat) - (1 : Nat)) : Nat)) : Nat) - (1 : Nat))))) ->
    wf_fNmag v_N (.NORM v_m v_exp)
  | fNmag_case_1 : forall (v_N : N) (v_m : m) (v_exp : exp), 
    ((v_m < (2 ^ (fun_M v_N))) && (((2 : Nat) - ((2 ^ ((((E v_N) : Nat) - (1 : Nat)) : Nat)) : Nat)) == v_exp)) ->
    wf_fNmag v_N (.SUBNORM v_m)
  | fNmag_case_2 : forall (v_N : N), wf_fNmag v_N .INF
  | fNmag_case_3 : forall (v_N : N) (v_m : m), 
    ((1 <= v_m) && (v_m < (2 ^ (fun_M v_N)))) ->
    wf_fNmag v_N (.NAN v_m)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:46.1-48.35 -/
inductive fN : Type where
  | POS (v_fNmag : fNmag) : fN
  | NEG (v_fNmag : fNmag) : fN
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:46.8-46.11 -/
inductive wf_fN : N -> fN -> Prop where
  | fN_case_0 : forall (v_N : N) (v_fNmag : fNmag), 
    (wf_fNmag v_N v_fNmag) ->
    wf_fN v_N (.POS v_fNmag)
  | fN_case_1 : forall (v_N : N) (v_fNmag : fNmag), 
    (wf_fNmag v_N v_fNmag) ->
    wf_fN v_N (.NEG v_fNmag)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:57.1-57.21 -/
abbrev f32 : Type := fN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:58.1-58.21 -/
abbrev f64 : Type := fN

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:60.1-60.39 -/
def fzero : ∀  (v_N : N) , fN
  | v_N =>
    (.POS (.SUBNORM 0))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:63.1-63.44 -/
def fnat : ∀  (v_N : N) (nat : Nat) , fN
  | v_N, v_n =>
    (.POS (.NORM v_n (0 : Nat)))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:66.1-66.39 -/
def fone : ∀  (v_N : N) , fN
  | v_N =>
    (.POS (.NORM 1 (0 : Nat)))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:69.1-69.21 -/
def canon_ : ∀  (v_N : N) , Nat
  | v_N =>
    (2 ^ ((((signif v_N) : Nat) - (1 : Nat)) : Nat))


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:75.1-76.8 -/
abbrev vN : Type := uN

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:78.1-78.23 -/
abbrev v128 : Type := vN

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:84.1-84.49 -/
inductive list (X : Type 0) : Type where
  | mk_list (X_lst : (List X)) : list X
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:84.1-84.49 -/
def proj_list_0 : ∀  (X : Type) (x : (list X)) , (List X)
  | X, (.mk_list v_X_list_0) =>
    (v_X_list_0)


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:89.1-89.85 -/
inductive char : Type where
  | mk_char (i : Nat) : char
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:89.1-89.85 -/
def proj_char_0 : ∀  (x : char) , Nat
  | (.mk_char v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:89.8-89.12 -/
inductive wf_char : char -> Prop where
  | char_case_0 : forall (i : Nat), 
    (((i >= 0) && (i <= 55295)) || ((i >= 57344) && (i <= 1114111))) ->
    wf_char (.mk_char i)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/5.1-binary.values.spectec:48.6-48.11 -/
inductive fun_cont : byte -> Nat -> Prop where
  | fun_cont_case_0 : forall (b : byte), 
    ((128 < (proj_byte_0 b)) && ((proj_byte_0 b) < 192)) ->
    fun_cont b ((((proj_byte_0 b) : Nat) - (128 : Nat)) : Nat)

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:91.1-91.25 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:91.6-91.11 -/
inductive fun_utf8 : (List char) -> (List byte) -> Prop where
  | fun_utf8_case_0 : forall (ch_lst : (List char)) (var_0_lst : (List (List byte))), 
    ((List.length var_0_lst) == (List.length ch_lst)) ->
    Forall₂ (fun (var_0 : (List byte)) (ch : char) => (fun_utf8 [ch] var_0)) var_0_lst ch_lst ->
    fun_utf8 ch_lst (concat_ byte var_0_lst)
  | fun_utf8_case_1 : forall (ch : char) (b : byte), 
    ((proj_char_0 ch) < 128) ->
    ((.mk_byte (proj_char_0 ch)) == b) ->
    fun_utf8 [ch] [b]
  | fun_utf8_case_2 : forall (ch : char) (b_1 : byte) (b_2 : byte) (var_0 : Nat), 
    (fun_cont b_2 var_0) ->
    ((128 <= (proj_char_0 ch)) && ((proj_char_0 ch) < 2048)) ->
    ((proj_char_0 ch) == (((2 ^ 6) * ((((proj_byte_0 b_1) : Nat) - (192 : Nat)) : Nat)) + var_0)) ->
    fun_utf8 [ch] [b_1, b_2]
  | fun_utf8_case_3 : forall (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) (var_1 : Nat) (var_0 : Nat), 
    (fun_cont b_3 var_1) ->
    (fun_cont b_2 var_0) ->
    (((2048 <= (proj_char_0 ch)) && ((proj_char_0 ch) < 55296)) || ((57344 <= (proj_char_0 ch)) && ((proj_char_0 ch) < 65536))) ->
    ((proj_char_0 ch) == ((((2 ^ 12) * ((((proj_byte_0 b_1) : Nat) - (224 : Nat)) : Nat)) + ((2 ^ 6) * var_0)) + var_1)) ->
    fun_utf8 [ch] [b_1, b_2, b_3]
  | fun_utf8_case_4 : forall (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) (b_4 : byte) (var_2 : Nat) (var_1 : Nat) (var_0 : Nat), 
    (fun_cont b_4 var_2) ->
    (fun_cont b_3 var_1) ->
    (fun_cont b_2 var_0) ->
    ((65536 <= (proj_char_0 ch)) && ((proj_char_0 ch) < 69632)) ->
    ((proj_char_0 ch) == (((((2 ^ 18) * ((((proj_byte_0 b_1) : Nat) - (240 : Nat)) : Nat)) + ((2 ^ 12) * var_0)) + ((2 ^ 6) * var_1)) + var_2)) ->
    fun_utf8 [ch] [b_1, b_2, b_3, b_4]

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:93.1-93.70 -/
inductive name : Type where
  | mk_name (char_lst : (List char)) : name
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:93.1-93.70 -/
def proj_name_0 : ∀  (x : name) , (List char)
  | (.mk_name v_char_list_0) =>
    (v_char_list_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:93.8-93.12 -/
inductive wf_name : name -> Prop where
  | name_case_0 : forall (char_lst : (List char)) (var_0 : (List byte)), 
    (fun_utf8 char_lst var_0) ->
    Forall (fun (v_char : char) => (wf_char v_char)) char_lst ->
    ((List.length var_0) < (2 ^ 32)) ->
    wf_name (.mk_name char_lst)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:100.1-100.36 -/
abbrev idx : Type := u32

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:101.1-101.44 -/
abbrev laneidx : Type := u8

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:103.1-103.45 -/
abbrev typeidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:104.1-104.49 -/
abbrev funcidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:105.1-105.49 -/
abbrev globalidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:106.1-106.47 -/
abbrev tableidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:107.1-107.46 -/
abbrev memidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:108.1-108.43 -/
abbrev tagidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:109.1-109.45 -/
abbrev elemidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:110.1-110.45 -/
abbrev dataidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:111.1-111.47 -/
abbrev labelidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:112.1-112.47 -/
abbrev localidx : Type := idx

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:113.1-113.47 -/
abbrev fieldidx : Type := idx

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:115.1-116.79 -/
inductive externidx : Type where
  | FUNC (v_funcidx : funcidx) : externidx
  | GLOBAL (v_globalidx : globalidx) : externidx
  | TABLE (v_tableidx : tableidx) : externidx
  | MEM (v_memidx : memidx) : externidx
  | TAG (v_tagidx : tagidx) : externidx
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:115.8-115.17 -/
inductive wf_externidx : externidx -> Prop where
  | externidx_case_0 : forall (v_funcidx : funcidx), 
    (wf_uN 32 v_funcidx) ->
    wf_externidx (.FUNC v_funcidx)
  | externidx_case_1 : forall (v_globalidx : globalidx), 
    (wf_uN 32 v_globalidx) ->
    wf_externidx (.GLOBAL v_globalidx)
  | externidx_case_2 : forall (v_tableidx : tableidx), 
    (wf_uN 32 v_tableidx) ->
    wf_externidx (.TABLE v_tableidx)
  | externidx_case_3 : forall (v_memidx : memidx), 
    (wf_uN 32 v_memidx) ->
    wf_externidx (.MEM v_memidx)
  | externidx_case_4 : forall (v_tagidx : tagidx), 
    (wf_uN 32 v_tagidx) ->
    wf_externidx (.TAG v_tagidx)

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:129.1-129.86 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:129.6-129.14 -/
inductive fun_funcsxx : (List externidx) -> (List typeidx) -> Prop where
  | fun_funcsxx_case_0 : fun_funcsxx [] []
  | fun_funcsxx_case_1 : forall (x : uN) (xx_lst : (List externidx)) (var_0 : (List typeidx)), 
    (fun_funcsxx xx_lst var_0) ->
    fun_funcsxx ([(.FUNC x)] ++ xx_lst) ([x] ++ var_0)
  | fun_funcsxx_case_2 : forall (v_externidx : externidx) (xx_lst : (List externidx)) (var_0 : (List typeidx)), 
    (fun_funcsxx xx_lst var_0) ->
    fun_funcsxx ([v_externidx] ++ xx_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:130.1-130.88 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:130.6-130.16 -/
inductive fun_globalsxx : (List externidx) -> (List globalidx) -> Prop where
  | fun_globalsxx_case_0 : fun_globalsxx [] []
  | fun_globalsxx_case_1 : forall (x : uN) (xx_lst : (List externidx)) (var_0 : (List globalidx)), 
    (fun_globalsxx xx_lst var_0) ->
    fun_globalsxx ([(.GLOBAL x)] ++ xx_lst) ([x] ++ var_0)
  | fun_globalsxx_case_2 : forall (v_externidx : externidx) (xx_lst : (List externidx)) (var_0 : (List globalidx)), 
    (fun_globalsxx xx_lst var_0) ->
    fun_globalsxx ([v_externidx] ++ xx_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:131.1-131.87 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:131.6-131.15 -/
inductive fun_tablesxx : (List externidx) -> (List tableidx) -> Prop where
  | fun_tablesxx_case_0 : fun_tablesxx [] []
  | fun_tablesxx_case_1 : forall (x : uN) (xx_lst : (List externidx)) (var_0 : (List tableidx)), 
    (fun_tablesxx xx_lst var_0) ->
    fun_tablesxx ([(.TABLE x)] ++ xx_lst) ([x] ++ var_0)
  | fun_tablesxx_case_2 : forall (v_externidx : externidx) (xx_lst : (List externidx)) (var_0 : (List tableidx)), 
    (fun_tablesxx xx_lst var_0) ->
    fun_tablesxx ([v_externidx] ++ xx_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:132.1-132.85 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:132.6-132.13 -/
inductive fun_memsxx : (List externidx) -> (List memidx) -> Prop where
  | fun_memsxx_case_0 : fun_memsxx [] []
  | fun_memsxx_case_1 : forall (x : uN) (xx_lst : (List externidx)) (var_0 : (List memidx)), 
    (fun_memsxx xx_lst var_0) ->
    fun_memsxx ([(.MEM x)] ++ xx_lst) ([x] ++ var_0)
  | fun_memsxx_case_2 : forall (v_externidx : externidx) (xx_lst : (List externidx)) (var_0 : (List memidx)), 
    (fun_memsxx xx_lst var_0) ->
    fun_memsxx ([v_externidx] ++ xx_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:133.1-133.85 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:133.6-133.13 -/
inductive fun_tagsxx : (List externidx) -> (List tagidx) -> Prop where
  | fun_tagsxx_case_0 : fun_tagsxx [] []
  | fun_tagsxx_case_1 : forall (x : uN) (xx_lst : (List externidx)) (var_0 : (List tagidx)), 
    (fun_tagsxx xx_lst var_0) ->
    fun_tagsxx ([(.TAG x)] ++ xx_lst) ([x] ++ var_0)
  | fun_tagsxx_case_2 : forall (v_externidx : externidx) (xx_lst : (List externidx)) (var_0 : (List tagidx)), 
    (fun_tagsxx xx_lst var_0) ->
    fun_tagsxx ([v_externidx] ++ xx_lst) var_0

/- Record Creation Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:158.1-168.4 -/
structure free where MKfree ::
  TYPES : (List typeidx)
  FUNCS : (List funcidx)
  GLOBALS : (List globalidx)
  TABLES : (List tableidx)
  MEMS : (List memidx)
  ELEMS : (List elemidx)
  DATAS : (List dataidx)
  LOCALS : (List localidx)
  LABELS : (List labelidx)
deriving Inhabited, BEq

def _append_free (arg1 arg2 : (free)) : free where
  TYPES := arg1.TYPES ++ arg2.TYPES
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  TABLES := arg1.TABLES ++ arg2.TABLES
  MEMS := arg1.MEMS ++ arg2.MEMS
  ELEMS := arg1.ELEMS ++ arg2.ELEMS
  DATAS := arg1.DATAS ++ arg2.DATAS
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
  LABELS := arg1.LABELS ++ arg2.LABELS
instance : Append free where
  append arg1 arg2 := _append_free arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:158.8-158.12 -/
inductive wf_free : free -> Prop where
  | free_case_ : forall (var_0 : (List typeidx)) (var_1 : (List funcidx)) (var_2 : (List globalidx)) (var_3 : (List tableidx)) (var_4 : (List memidx)) (var_5 : (List elemidx)) (var_6 : (List dataidx)) (var_7 : (List localidx)) (var_8 : (List labelidx)), 
    Forall (fun (var_0 : typeidx) => (wf_uN 32 var_0)) var_0 ->
    Forall (fun (var_1 : funcidx) => (wf_uN 32 var_1)) var_1 ->
    Forall (fun (var_2 : globalidx) => (wf_uN 32 var_2)) var_2 ->
    Forall (fun (var_3 : tableidx) => (wf_uN 32 var_3)) var_3 ->
    Forall (fun (var_4 : memidx) => (wf_uN 32 var_4)) var_4 ->
    Forall (fun (var_5 : elemidx) => (wf_uN 32 var_5)) var_5 ->
    Forall (fun (var_6 : dataidx) => (wf_uN 32 var_6)) var_6 ->
    Forall (fun (var_7 : localidx) => (wf_uN 32 var_7)) var_7 ->
    Forall (fun (var_8 : labelidx) => (wf_uN 32 var_8)) var_8 ->
    wf_free { TYPES := var_0, FUNCS := var_1, GLOBALS := var_2, TABLES := var_3, MEMS := var_4, ELEMS := var_5, DATAS := var_6, LOCALS := var_7, LABELS := var_8 }

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:171.1-171.28 -/
def free_opt : ∀  (var_0 : (Option free)) , free
  | none =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | (some v_free) =>
    v_free


/- Recursive Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:172.1-172.29 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:172.6-172.16 -/
inductive fun_free_list : (List free) -> free -> Prop where
  | fun_free_list_case_0 : fun_free_list [] { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_list_case_1 : forall (v_free : free) (free'_lst : (List free)) (var_0 : free), 
    (fun_free_list free'_lst var_0) ->
    fun_free_list ([v_free] ++ free'_lst) (v_free ++ var_0)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:181.1-181.34 -/
def free_typeidx : ∀  (v_typeidx : typeidx) , free
  | v_typeidx =>
    { TYPES := [v_typeidx], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:182.1-182.34 -/
def free_funcidx : ∀  (v_funcidx : funcidx) , free
  | v_funcidx =>
    { TYPES := [], FUNCS := [v_funcidx], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:183.1-183.38 -/
def free_globalidx : ∀  (v_globalidx : globalidx) , free
  | v_globalidx =>
    { TYPES := [], FUNCS := [], GLOBALS := [v_globalidx], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:184.1-184.36 -/
def free_tableidx : ∀  (v_tableidx : tableidx) , free
  | v_tableidx =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [v_tableidx], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:185.1-185.32 -/
def free_memidx : ∀  (v_memidx : memidx) , free
  | v_memidx =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [v_memidx], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:186.1-186.34 -/
def free_elemidx : ∀  (v_elemidx : elemidx) , free
  | v_elemidx =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [v_elemidx], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:187.1-187.34 -/
def free_dataidx : ∀  (v_dataidx : dataidx) , free
  | v_dataidx =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [v_dataidx], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:188.1-188.36 -/
def free_localidx : ∀  (v_localidx : localidx) , free
  | v_localidx =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [v_localidx], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:189.1-189.36 -/
def free_labelidx : ∀  (v_labelidx : labelidx) , free
  | v_labelidx =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [v_labelidx] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.1-syntax.values.spectec:190.1-190.38 -/
def free_externidx : ∀  (v_externidx : externidx) , free
  | (.FUNC v_funcidx) =>
    (free_funcidx v_funcidx)
  | (.GLOBAL v_globalidx) =>
    (free_globalidx v_globalidx)
  | (.TABLE v_tableidx) =>
    (free_tableidx v_tableidx)
  | (.MEM v_memidx) =>
    (free_memidx v_memidx)


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:8.1-8.55 -/
inductive null : Type where
  | NULL : null
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:10.1-11.14 -/
inductive addrtype : Type where
  | I32 : addrtype
  | I64 : addrtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:13.1-14.26 -/
inductive numtype : Type where
  | I32 : numtype
  | I64 : numtype
  | F32 : numtype
  | F64 : numtype
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def numtype_addrtype : ∀  (var_0 : addrtype) , numtype
  | .I32 =>
    .I32
  | .I64 =>
    .I64


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:16.1-17.9 -/
inductive vectype : Type where
  | V128 : vectype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:19.1-20.22 -/
inductive consttype : Type where
  | I32 : consttype
  | I64 : consttype
  | F32 : consttype
  | F64 : consttype
  | V128 : consttype
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def consttype_numtype : ∀  (var_0 : numtype) , consttype
  | .I32 =>
    .I32
  | .I64 =>
    .I64
  | .F32 =>
    .F32
  | .F64 =>
    .F64


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:28.1-29.14 -/
inductive absheaptype : Type where
  | ANY : absheaptype
  | EQ : absheaptype
  | I31 : absheaptype
  | STRUCT : absheaptype
  | ARRAY : absheaptype
  | NONE : absheaptype
  | FUNC : absheaptype
  | NOFUNC : absheaptype
  | EXN : absheaptype
  | NOEXN : absheaptype
  | EXTERN : absheaptype
  | NOEXTERN : absheaptype
  | BOT : absheaptype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:109.1-109.54 -/
inductive «mut» : Type where
  | MUT : «mut»
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:110.1-110.60 -/
inductive final : Type where
  | FINAL : final
deriving Inhabited, BEq


/- Recursive Definitions at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:37.1-123.22 -/
mutual
/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:37.1-38.43 -/
inductive typeuse : Type where
  | _IDX (v_typeidx : typeidx) : typeuse
  | _DEF (v_rectype : rectype) (v_n : n) : typeuse
  | REC (v_n : n) : typeuse
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:43.1-44.26 -/
inductive heaptype : Type where
  | ANY : heaptype
  | EQ : heaptype
  | I31 : heaptype
  | STRUCT : heaptype
  | ARRAY : heaptype
  | NONE : heaptype
  | FUNC : heaptype
  | NOFUNC : heaptype
  | EXN : heaptype
  | NOEXN : heaptype
  | EXTERN : heaptype
  | NOEXTERN : heaptype
  | BOT : heaptype
  | _IDX (v_typeidx : typeidx) : heaptype
  | REC (v_n : n) : heaptype
  | _DEF (v_rectype : rectype) (v_n : n) : heaptype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:51.1-52.14 -/
inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
  | V128 : valtype
  | REF (null_opt : (Option null)) (v_heaptype : heaptype) : valtype
  | BOT : valtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:92.1-92.66 -/
inductive storagetype : Type where
  | BOT : storagetype
  | I32 : storagetype
  | I64 : storagetype
  | F32 : storagetype
  | F64 : storagetype
  | V128 : storagetype
  | REF (null_opt : (Option null)) (v_heaptype : heaptype) : storagetype
  | I8 : storagetype
  | I16 : storagetype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:112.1-112.61 -/
inductive fieldtype : Type where
  | mk_fieldtype (mut_opt : (Option «mut»)) (v_storagetype : storagetype) : fieldtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:114.1-117.34 -/
inductive comptype : Type where
  | STRUCT (v_list : (list fieldtype)) : comptype
  | ARRAY (v_fieldtype : fieldtype) : comptype
  | FUNC (v_resulttype : (list valtype)) (_ : (list valtype)) : comptype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:119.1-120.33 -/
inductive subtype : Type where
  | SUB (final_opt : (Option final)) (typeuse_lst : (List typeuse)) (v_comptype : comptype) : subtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:122.1-123.22 -/
inductive rectype : Type where
  | REC (v_list : (list subtype)) : rectype
deriving Inhabited, BEq


end

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:102.1-103.16 -/
abbrev resulttype : Type := (list valtype)

/- Auxiliary Definition at:  -/
def heaptype_absheaptype : ∀  (var_0 : absheaptype) , heaptype
  | .ANY =>
    .ANY
  | .EQ =>
    .EQ
  | .I31 =>
    .I31
  | .STRUCT =>
    .STRUCT
  | .ARRAY =>
    .ARRAY
  | .NONE =>
    .NONE
  | .FUNC =>
    .FUNC
  | .NOFUNC =>
    .NOFUNC
  | .EXN =>
    .EXN
  | .NOEXN =>
    .NOEXN
  | .EXTERN =>
    .EXTERN
  | .NOEXTERN =>
    .NOEXTERN
  | .BOT =>
    .BOT


/- Auxiliary Definition at:  -/
def valtype_addrtype : ∀  (var_0 : addrtype) , valtype
  | .I32 =>
    .I32
  | .I64 =>
    .I64


/- Auxiliary Definition at:  -/
def storagetype_consttype : ∀  (var_0 : consttype) , storagetype
  | .I32 =>
    .I32
  | .I64 =>
    .I64
  | .F32 =>
    .F32
  | .F64 =>
    .F64
  | .V128 =>
    .V128


/- Auxiliary Definition at:  -/
def storagetype_numtype : ∀  (var_0 : numtype) , storagetype
  | .I32 =>
    .I32
  | .I64 =>
    .I64
  | .F32 =>
    .F32
  | .F64 =>
    .F64


/- Auxiliary Definition at:  -/
def valtype_numtype : ∀  (var_0 : numtype) , valtype
  | .I32 =>
    .I32
  | .I64 =>
    .I64
  | .F32 =>
    .F32
  | .F64 =>
    .F64


/- Auxiliary Definition at:  -/
def heaptype_typeuse : ∀  (var_0 : typeuse) , heaptype
  | (._IDX x0) =>
    (._IDX x0)
  | (._DEF x0 x1) =>
    (._DEF x0 x1)
  | (.REC x0) =>
    (.REC x0)


/- Auxiliary Definition at:  -/
def storagetype_valtype : ∀  (var_0 : valtype) , storagetype
  | .I32 =>
    .I32
  | .I64 =>
    .I64
  | .F32 =>
    .F32
  | .F64 =>
    .F64
  | .V128 =>
    .V128
  | (.REF x0 x1) =>
    (.REF x0 x1)
  | .BOT =>
    .BOT


/- Auxiliary Definition at:  -/
def storagetype_vectype : ∀  (var_0 : vectype) , storagetype
  | .V128 =>
    .V128


/- Auxiliary Definition at:  -/
def valtype_vectype : ∀  (var_0 : vectype) , valtype
  | .V128 =>
    .V128


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:32.1-33.34 -/
inductive deftype : Type where
  | _DEF (v_rectype : rectype) (v_n : n) : deftype
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def heaptype_deftype : ∀  (var_0 : deftype) , heaptype
  | (._DEF x0 x1) =>
    (._DEF x0 x1)


/- Auxiliary Definition at:  -/
def typeuse_deftype : ∀  (var_0 : deftype) , typeuse
  | (._DEF x0 x1) =>
    (._DEF x0 x1)


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:40.1-41.42 -/
inductive typevar : Type where
  | _IDX (v_typeidx : typeidx) : typevar
  | REC (v_n : n) : typevar
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def typeuse_typevar : ∀  (var_0 : typevar) , typeuse
  | (._IDX x0) =>
    (._IDX x0)
  | (.REC x0) =>
    (.REC x0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:40.8-40.15 -/
inductive wf_typevar : typevar -> Prop where
  | typevar_case_0 : forall (v_typeidx : typeidx), 
    (wf_uN 32 v_typeidx) ->
    wf_typevar (._IDX v_typeidx)
  | typevar_case_1 : forall (v_n : n), wf_typevar (.REC v_n)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:46.1-47.23 -/
inductive reftype : Type where
  | REF (null_opt : (Option null)) (v_heaptype : heaptype) : reftype
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def storagetype_reftype : ∀  (var_0 : reftype) , storagetype
  | (.REF x0 x1) =>
    (.REF x0 x1)


/- Auxiliary Definition at:  -/
def valtype_reftype : ∀  (var_0 : reftype) , valtype
  | (.REF x0 x1) =>
    (.REF x0 x1)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:46.8-46.15 -/
inductive wf_reftype : reftype -> Prop where
  | reftype_case_0 : forall (null_opt : (Option null)) (v_heaptype : heaptype), 
    (wf_heaptype v_heaptype) ->
    wf_reftype (.REF null_opt v_heaptype)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:55.1-55.55 -/
abbrev Inn : Type := addrtype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:56.1-56.56 -/
inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def numtype_Fnn : ∀  (var_0 : Fnn) , numtype
  | .F32 =>
    .F32
  | .F64 =>
    .F64


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:57.1-57.54 -/
abbrev Vnn : Type := vectype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:58.1-58.42 -/
inductive Cnn : Type where
  | I32 : Cnn
  | I64 : Cnn
  | F32 : Cnn
  | F64 : Cnn
  | V128 : Cnn
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:61.1-61.43 -/
def ANYREF : reftype := (.REF (some .NULL) .ANY)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:62.1-62.42 -/
def EQREF : reftype := (.REF (some .NULL) .EQ)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:63.1-63.43 -/
def I31REF : reftype := (.REF (some .NULL) .I31)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:64.1-64.46 -/
def STRUCTREF : reftype := (.REF (some .NULL) .STRUCT)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:65.1-65.45 -/
def ARRAYREF : reftype := (.REF (some .NULL) .ARRAY)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:66.1-66.44 -/
def FUNCREF : reftype := (.REF (some .NULL) .FUNC)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:67.1-67.43 -/
def EXNREF : reftype := (.REF (some .NULL) .EXN)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:68.1-68.46 -/
def EXTERNREF : reftype := (.REF (some .NULL) .EXTERN)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:69.1-69.44 -/
def NULLREF : reftype := (.REF (some .NULL) .NONE)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:70.1-70.50 -/
def NULLFUNCREF : reftype := (.REF (some .NULL) .NOFUNC)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:71.1-71.49 -/
def NULLEXNREF : reftype := (.REF (some .NULL) .NOEXN)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:72.1-72.54 -/
def NULLEXTERNREF : reftype := (.REF (some .NULL) .NOEXTERN)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:90.1-90.52 -/
inductive packtype : Type where
  | I8 : packtype
  | I16 : packtype
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def storagetype_packtype : ∀  (var_0 : packtype) , storagetype
  | .I8 =>
    .I8
  | .I16 =>
    .I16


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:91.1-91.60 -/
inductive lanetype : Type where
  | I32 : lanetype
  | I64 : lanetype
  | F32 : lanetype
  | F64 : lanetype
  | I8 : lanetype
  | I16 : lanetype
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def lanetype_Fnn : ∀  (var_0 : Fnn) , lanetype
  | .F32 =>
    .F32
  | .F64 =>
    .F64


/- Auxiliary Definition at:  -/
def lanetype_addrtype : ∀  (var_0 : addrtype) , lanetype
  | .I32 =>
    .I32
  | .I64 =>
    .I64


/- Auxiliary Definition at:  -/
def lanetype_numtype : ∀  (var_0 : numtype) , lanetype
  | .I32 =>
    .I32
  | .I64 =>
    .I64
  | .F32 =>
    .F32
  | .F64 =>
    .F64


/- Auxiliary Definition at:  -/
def lanetype_packtype : ∀  (var_0 : packtype) , lanetype
  | .I8 =>
    .I8
  | .I16 =>
    .I16


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:95.1-95.55 -/
abbrev Pnn : Type := packtype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:96.1-96.56 -/
inductive Jnn : Type where
  | I32 : Jnn
  | I64 : Jnn
  | I8 : Jnn
  | I16 : Jnn
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def lanetype_Jnn : ∀  (var_0 : Jnn) , lanetype
  | .I32 =>
    .I32
  | .I64 =>
    .I64
  | .I8 =>
    .I8
  | .I16 =>
    .I16


/- Auxiliary Definition at:  -/
def Jnn_addrtype : ∀  (var_0 : addrtype) , Jnn
  | .I32 =>
    .I32
  | .I64 =>
    .I64


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:97.1-97.55 -/
abbrev Lnn : Type := lanetype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:128.1-128.74 -/
inductive limits : Type where
  | mk_limits (v_u64 : u64) (_ : (Option u64)) : limits
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:128.8-128.14 -/
inductive wf_limits : limits -> Prop where
  | limits_case_0 : forall (v_u64 : u64) (var_0 : (Option u64)), 
    (wf_uN 64 v_u64) ->
    Forall (fun (var_0 : u64) => (wf_uN 64 var_0)) (Option.toList var_0) ->
    wf_limits (.mk_limits v_u64 var_0)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:130.1-130.47 -/
abbrev tagtype : Type := typeuse

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:131.1-131.58 -/
inductive globaltype : Type where
  | mk_globaltype (mut_opt : (Option «mut»)) (v_valtype : valtype) : globaltype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:131.8-131.18 -/
inductive wf_globaltype : globaltype -> Prop where
  | globaltype_case_0 : forall (mut_opt : (Option «mut»)) (v_valtype : valtype), 
    (wf_valtype v_valtype) ->
    wf_globaltype (.mk_globaltype mut_opt v_valtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:132.1-132.63 -/
inductive memtype : Type where
  | PAGE (v_addrtype : addrtype) (v_limits : limits) : memtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:132.8-132.15 -/
inductive wf_memtype : memtype -> Prop where
  | memtype_case_0 : forall (v_addrtype : addrtype) (v_limits : limits), 
    (wf_limits v_limits) ->
    wf_memtype (.PAGE v_addrtype v_limits)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:133.1-133.67 -/
inductive tabletype : Type where
  | mk_tabletype (v_addrtype : addrtype) (v_limits : limits) (v_reftype : reftype) : tabletype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:133.8-133.17 -/
inductive wf_tabletype : tabletype -> Prop where
  | tabletype_case_0 : forall (v_addrtype : addrtype) (v_limits : limits) (v_reftype : reftype), 
    (wf_limits v_limits) ->
    (wf_reftype v_reftype) ->
    wf_tabletype (.mk_tabletype v_addrtype v_limits v_reftype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:134.1-134.64 -/
inductive datatype : Type where
  | OK : datatype
deriving Inhabited, BEq


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:135.1-135.52 -/
abbrev elemtype : Type := reftype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:137.1-138.83 -/
inductive externtype : Type where
  | TAG (v_tagtype : tagtype) : externtype
  | GLOBAL (v_globaltype : globaltype) : externtype
  | MEM (v_memtype : memtype) : externtype
  | TABLE (v_tabletype : tabletype) : externtype
  | FUNC (v_typeuse : typeuse) : externtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:137.8-137.18 -/
inductive wf_externtype : externtype -> Prop where
  | externtype_case_0 : forall (v_tagtype : tagtype), 
    (wf_typeuse v_tagtype) ->
    wf_externtype (.TAG v_tagtype)
  | externtype_case_1 : forall (v_globaltype : globaltype), 
    (wf_globaltype v_globaltype) ->
    wf_externtype (.GLOBAL v_globaltype)
  | externtype_case_2 : forall (v_memtype : memtype), 
    (wf_memtype v_memtype) ->
    wf_externtype (.MEM v_memtype)
  | externtype_case_3 : forall (v_tabletype : tabletype), 
    (wf_tabletype v_tabletype) ->
    wf_externtype (.TABLE v_tabletype)
  | externtype_case_4 : forall (v_typeuse : typeuse), 
    (wf_typeuse v_typeuse) ->
    wf_externtype (.FUNC v_typeuse)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:140.1-141.47 -/
inductive moduletype : Type where
  | mk_moduletype (externtype_lst : (List externtype)) (_ : (List externtype)) : moduletype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:140.8-140.18 -/
inductive wf_moduletype : moduletype -> Prop where
  | moduletype_case_0 : forall (externtype_lst : (List externtype)) (var_0 : (List externtype)), 
    Forall (fun (v_externtype : externtype) => (wf_externtype v_externtype)) externtype_lst ->
    Forall (fun (var_0 : externtype) => (wf_externtype var_0)) var_0 ->
    wf_moduletype (.mk_moduletype externtype_lst var_0)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:179.1-179.51 -/
def IN : ∀  (v_N : N) , Inn
  | 32 =>
    .I32
  | 64 =>
    .I64


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:183.1-183.51 -/
def FN : ∀  (v_N : N) , Fnn
  | 32 =>
    .F32
  | 64 =>
    .F64


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:187.1-187.51 -/
def JN : ∀  (v_N : N) , Jnn
  | 8 =>
    .I8
  | 16 =>
    .I16
  | 32 =>
    .I32
  | 64 =>
    .I64


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:196.1-196.46 -/
def size : ∀  (v_numtype : numtype) , Nat
  | .I32 =>
    32
  | .I64 =>
    64
  | .F32 =>
    32
  | .F64 =>
    64


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:197.1-197.46 -/
def vsize : ∀  (v_vectype : vectype) , Nat
  | .V128 =>
    128


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:198.1-198.46 -/
def psize : ∀  (v_packtype : packtype) , Nat
  | .I8 =>
    8
  | .I16 =>
    16


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:199.1-199.46 -/
def lsize : ∀  (v_lanetype : lanetype) , Nat
  | .I32 =>
    (size .I32)
  | .I64 =>
    (size .I64)
  | .F32 =>
    (size .F32)
  | .F64 =>
    (size .F64)
  | .I8 =>
    (psize .I8)
  | .I16 =>
    (psize .I16)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:200.1-200.46 -/
def zsize : ∀  (v_storagetype : storagetype) , Nat
  | .I32 =>
    (size .I32)
  | .I64 =>
    (size .I64)
  | .F32 =>
    (size .F32)
  | .F64 =>
    (size .F64)
  | .V128 =>
    (vsize .V128)
  | .I8 =>
    (psize .I8)
  | .I16 =>
    (psize .I16)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:201.1-201.71 -/
def isize : ∀  (v_Inn : Inn) , Nat
  | v_Inn =>
    (size (numtype_addrtype v_Inn))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:202.1-202.71 -/
def jsize : ∀  (v_Jnn : Jnn) , Nat
  | v_Jnn =>
    (lsize (lanetype_Jnn v_Jnn))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:203.1-203.71 -/
def fsize : ∀  (v_Fnn : Fnn) , Nat
  | v_Fnn =>
    (size (numtype_Fnn v_Fnn))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:226.1-226.40 -/
def inv_isize : ∀  (nat : Nat) , (Option Inn)
  | 32 =>
    (some .I32)
  | 64 =>
    (some .I64)
  | x0 =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:227.1-227.40 -/
def inv_jsize : ∀  (nat : Nat) , (Option Jnn)
  | 8 =>
    (some .I8)
  | 16 =>
    (some .I16)
  | v_n =>
    (some (Jnn_addrtype (Option.get! (inv_isize v_n))))
  | x0 =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:228.1-228.40 -/
def inv_fsize : ∀  (nat : Nat) , (Option Fnn)
  | 32 =>
    (some .F32)
  | 64 =>
    (some .F64)
  | x0 =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:239.1-239.63 -/
def sizenn : ∀  (v_numtype : numtype) , Nat
  | nt =>
    (size nt)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:240.1-240.63 -/
def sizenn1 : ∀  (v_numtype : numtype) , Nat
  | nt =>
    (size nt)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:241.1-241.63 -/
def sizenn2 : ∀  (v_numtype : numtype) , Nat
  | nt =>
    (size nt)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:246.1-246.63 -/
def vsizenn : ∀  (v_vectype : vectype) , Nat
  | vt =>
    (vsize vt)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:249.1-249.63 -/
def psizenn : ∀  (v_packtype : packtype) , Nat
  | pt =>
    (psize pt)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:252.1-252.63 -/
def lsizenn : ∀  (v_lanetype : lanetype) , Nat
  | lt =>
    (lsize lt)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:253.1-253.63 -/
def lsizenn1 : ∀  (v_lanetype : lanetype) , Nat
  | lt =>
    (lsize lt)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:254.1-254.63 -/
def lsizenn2 : ∀  (v_lanetype : lanetype) , Nat
  | lt =>
    (lsize lt)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:259.1-259.83 -/
def jsizenn : ∀  (v_Jnn : Jnn) , Nat
  | v_Jnn =>
    (lsize (lanetype_Jnn v_Jnn))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:262.1-262.42 -/
def inv_jsizenn : ∀  (nat : Nat) , (Option Jnn)
  | v_n =>
    (some (Option.get! (inv_jsize v_n)))
  | x0 =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:268.1-268.56 -/
def lunpack : ∀  (v_lanetype : lanetype) , numtype
  | .I32 =>
    .I32
  | .I64 =>
    .I64
  | .F32 =>
    .F32
  | .F64 =>
    .F64
  | .I8 =>
    .I32
  | .I16 =>
    .I32


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:272.1-272.35 -/
def unpack : ∀  (v_storagetype : storagetype) , valtype
  | .BOT =>
    .BOT
  | (.REF null_opt v_heaptype) =>
    (.REF null_opt v_heaptype)
  | .V128 =>
    .V128
  | .F64 =>
    .F64
  | .F32 =>
    .F32
  | .I64 =>
    .I64
  | .I32 =>
    .I32
  | .I8 =>
    .I32
  | .I16 =>
    .I32


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:276.1-276.73 -/
def nunpack : ∀  (v_storagetype : storagetype) , (Option numtype)
  | .I32 =>
    (some .I32)
  | .I64 =>
    (some .I64)
  | .F32 =>
    (some .F32)
  | .F64 =>
    (some .F64)
  | .I8 =>
    (some .I32)
  | .I16 =>
    (some .I32)
  | x0 =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:280.1-280.73 -/
def vunpack : ∀  (v_storagetype : storagetype) , (Option vectype)
  | .V128 =>
    (some .V128)
  | x0 =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:283.1-283.74 -/
def cunpack : ∀  (v_storagetype : storagetype) , (Option consttype)
  | .I32 =>
    (some .I32)
  | .I64 =>
    (some .I64)
  | .F32 =>
    (some .F32)
  | .F64 =>
    (some .F64)
  | .V128 =>
    (some .V128)
  | .I8 =>
    (some .I32)
  | .I16 =>
    (some .I32)
  | .I32 =>
    (some (consttype_numtype (lunpack .I32)))
  | .I64 =>
    (some (consttype_numtype (lunpack .I64)))
  | .F32 =>
    (some (consttype_numtype (lunpack .F32)))
  | .F64 =>
    (some (consttype_numtype (lunpack .F64)))
  | .I8 =>
    (some (consttype_numtype (lunpack .I8)))
  | .I16 =>
    (some (consttype_numtype (lunpack .I16)))
  | x0 =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:291.1-291.90 -/
def minat : ∀  (v_addrtype : addrtype) (v_addrtype_0 : addrtype) , addrtype
  | at_1, at_2 =>
    (if ((size (numtype_addrtype at_1)) <= (size (numtype_addrtype at_2))) then at_1 else at_2)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:295.1-295.82 -/
def diffrt : ∀  (v_reftype : reftype) (v_reftype_0 : reftype) , reftype
  | (.REF null_1_opt ht_1), (.REF (some .NULL) ht_2) =>
    (.REF none ht_1)
  | (.REF null_1_opt ht_1), (.REF none ht_2) =>
    (.REF null_1_opt ht_1)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:300.1-300.49 -/
def as_deftype : ∀  (v_typeuse : typeuse) , deftype
  | (._DEF v_rectype v_n) =>
    (._DEF v_rectype v_n)


/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:308.1-308.87 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:308.6-308.13 -/
inductive fun_tagsxt : (List externtype) -> (List tagtype) -> Prop where
  | fun_tagsxt_case_0 : fun_tagsxt [] []
  | fun_tagsxt_case_1 : forall (jt : typeuse) (xt_lst : (List externtype)) (var_0 : (List tagtype)), 
    (fun_tagsxt xt_lst var_0) ->
    fun_tagsxt ([(.TAG jt)] ++ xt_lst) ([jt] ++ var_0)
  | fun_tagsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List tagtype)), 
    (fun_tagsxt xt_lst var_0) ->
    fun_tagsxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:309.1-309.90 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:309.6-309.16 -/
inductive fun_globalsxt : (List externtype) -> (List globaltype) -> Prop where
  | fun_globalsxt_case_0 : fun_globalsxt [] []
  | fun_globalsxt_case_1 : forall (gt : globaltype) (xt_lst : (List externtype)) (var_0 : (List globaltype)), 
    (fun_globalsxt xt_lst var_0) ->
    fun_globalsxt ([(.GLOBAL gt)] ++ xt_lst) ([gt] ++ var_0)
  | fun_globalsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List globaltype)), 
    (fun_globalsxt xt_lst var_0) ->
    fun_globalsxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:310.1-310.87 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:310.6-310.13 -/
inductive fun_memsxt : (List externtype) -> (List memtype) -> Prop where
  | fun_memsxt_case_0 : fun_memsxt [] []
  | fun_memsxt_case_1 : forall (mt : memtype) (xt_lst : (List externtype)) (var_0 : (List memtype)), 
    (fun_memsxt xt_lst var_0) ->
    fun_memsxt ([(.MEM mt)] ++ xt_lst) ([mt] ++ var_0)
  | fun_memsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List memtype)), 
    (fun_memsxt xt_lst var_0) ->
    fun_memsxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:311.1-311.89 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:311.6-311.15 -/
inductive fun_tablesxt : (List externtype) -> (List tabletype) -> Prop where
  | fun_tablesxt_case_0 : fun_tablesxt [] []
  | fun_tablesxt_case_1 : forall (tt : tabletype) (xt_lst : (List externtype)) (var_0 : (List tabletype)), 
    (fun_tablesxt xt_lst var_0) ->
    fun_tablesxt ([(.TABLE tt)] ++ xt_lst) ([tt] ++ var_0)
  | fun_tablesxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List tabletype)), 
    (fun_tablesxt xt_lst var_0) ->
    fun_tablesxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:312.1-312.88 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:312.6-312.14 -/
inductive fun_funcsxt : (List externtype) -> (List deftype) -> Prop where
  | fun_funcsxt_case_0 : fun_funcsxt [] []
  | fun_funcsxt_case_1 : forall (v_rectype : rectype) (v_n : n) (xt_lst : (List externtype)) (var_0 : (List deftype)), 
    (fun_funcsxt xt_lst var_0) ->
    fun_funcsxt ([(.FUNC (._DEF v_rectype v_n))] ++ xt_lst) ([(._DEF v_rectype v_n)] ++ var_0)
  | fun_funcsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List deftype)), 
    (fun_funcsxt xt_lst var_0) ->
    fun_funcsxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:337.1-337.112 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:337.6-337.20 -/
inductive fun_subst_typevar : typevar -> (List typevar) -> (List typeuse) -> typeuse -> Prop where
  | fun_subst_typevar_case_0 : forall (tv : typevar), fun_subst_typevar tv [] [] (typeuse_typevar tv)
  | fun_subst_typevar_case_1 : forall (tv : typevar) (tv_1 : typevar) (tv'_lst : (List typevar)) (tu_1 : typeuse) (tu'_lst : (List typeuse)) (var_0 : typeuse), 
    (fun_subst_typevar tv tv'_lst tu'_lst var_0) ->
    fun_subst_typevar tv ([tv_1] ++ tv'_lst) ([tu_1] ++ tu'_lst) (if (tv == tv_1) then tu_1 else var_0)

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:401.1-401.59 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:401.6-401.17 -/
inductive fun_minus_recs : (List typevar) -> (List typeuse) -> (List typevar) × (List typeuse) -> Prop where
  | fun_minus_recs_case_0 : fun_minus_recs [] [] ([], [])
  | fun_minus_recs_case_1 : forall (v_n : Nat) (tv_lst : (List typevar)) (tu_1 : typeuse) (tu_lst : (List typeuse)) (var_0 : (List typevar) × (List typeuse)), 
    (fun_minus_recs tv_lst tu_lst var_0) ->
    fun_minus_recs ([(.REC v_n)] ++ tv_lst) ([tu_1] ++ tu_lst) var_0
  | fun_minus_recs_case_2 : forall (x : uN) (tv_lst : (List typevar)) (tu_1 : typeuse) (tu_lst : (List typeuse)) (tv'_lst : (List typevar)) (tu'_lst : (List typeuse)) (var_0 : (List typevar) × (List typeuse)), 
    (fun_minus_recs tv_lst tu_lst var_0) ->
    ((tv'_lst, tu'_lst) == var_0) ->
    fun_minus_recs ([(._IDX x)] ++ tv_lst) ([tu_1] ++ tu_lst) (([(._IDX x)] ++ tv'_lst), ([tu_1] ++ tu'_lst))

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:347.1-347.112 -/
def subst_packtype : ∀  (v_packtype : packtype) (var_0 : (List typevar)) (var_1 : (List typeuse)) , packtype
  | pt, tv_lst, tu_lst =>
    pt


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:341.1-341.112 -/
def subst_numtype : ∀  (v_numtype : numtype) (var_0 : (List typevar)) (var_1 : (List typeuse)) , numtype
  | nt, tv_lst, tu_lst =>
    nt


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:342.1-342.112 -/
def subst_vectype : ∀  (v_vectype : vectype) (var_0 : (List typevar)) (var_1 : (List typeuse)) , vectype
  | vt, tv_lst, tu_lst =>
    vt


/- Recursive Definitions at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:338.1-354.112 -/
mutual
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:338.6-338.20 -/
inductive fun_subst_typeuse : typeuse -> (List typevar) -> (List typeuse) -> typeuse -> Prop where
  | fun_subst_typeuse_case_0 : forall (v_n : n) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : typeuse), 
    (fun_subst_typevar (.REC v_n) tv_lst tu_lst var_0) ->
    fun_subst_typeuse (.REC v_n) tv_lst tu_lst var_0
  | fun_subst_typeuse_case_1 : forall (v_typeidx : typeidx) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : typeuse), 
    (fun_subst_typevar (._IDX v_typeidx) tv_lst tu_lst var_0) ->
    fun_subst_typeuse (._IDX v_typeidx) tv_lst tu_lst var_0
  | fun_subst_typeuse_case_2 : forall (v_rectype : rectype) (v_n : n) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : deftype), 
    (fun_subst_deftype (._DEF v_rectype v_n) tv_lst tu_lst var_0) ->
    fun_subst_typeuse (._DEF v_rectype v_n) tv_lst tu_lst (typeuse_deftype var_0)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:343.6-343.21 -/
inductive fun_subst_heaptype : heaptype -> (List typevar) -> (List typeuse) -> heaptype -> Prop where
  | fun_subst_heaptype_case_0 : forall (v_n : n) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : typeuse), 
    (fun_subst_typevar (.REC v_n) tv_lst tu_lst var_0) ->
    fun_subst_heaptype (.REC v_n) tv_lst tu_lst (heaptype_typeuse var_0)
  | fun_subst_heaptype_case_1 : forall (v_typeidx : typeidx) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : typeuse), 
    (fun_subst_typevar (._IDX v_typeidx) tv_lst tu_lst var_0) ->
    fun_subst_heaptype (._IDX v_typeidx) tv_lst tu_lst (heaptype_typeuse var_0)
  | fun_subst_heaptype_case_2 : forall (v_rectype : rectype) (v_n : n) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : deftype), 
    (fun_subst_deftype (._DEF v_rectype v_n) tv_lst tu_lst var_0) ->
    fun_subst_heaptype (._DEF v_rectype v_n) tv_lst tu_lst (heaptype_deftype var_0)
  | fun_subst_heaptype_case_3 : forall (ht : heaptype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_heaptype ht tv_lst tu_lst ht

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:344.6-344.20 -/
inductive fun_subst_reftype : reftype -> (List typevar) -> (List typeuse) -> reftype -> Prop where
  | fun_subst_reftype_case_0 : forall (null_opt : (Option null)) (ht : heaptype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : heaptype), 
    (fun_subst_heaptype ht tv_lst tu_lst var_0) ->
    fun_subst_reftype (.REF null_opt ht) tv_lst tu_lst (.REF null_opt var_0)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:345.6-345.20 -/
inductive fun_subst_valtype : valtype -> (List typevar) -> (List typeuse) -> valtype -> Prop where
  | fun_subst_valtype_case_0 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_valtype .I32 tv_lst tu_lst (valtype_numtype (subst_numtype .I32 tv_lst tu_lst))
  | fun_subst_valtype_case_1 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_valtype .I64 tv_lst tu_lst (valtype_numtype (subst_numtype .I64 tv_lst tu_lst))
  | fun_subst_valtype_case_2 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_valtype .F32 tv_lst tu_lst (valtype_numtype (subst_numtype .F32 tv_lst tu_lst))
  | fun_subst_valtype_case_3 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_valtype .F64 tv_lst tu_lst (valtype_numtype (subst_numtype .F64 tv_lst tu_lst))
  | fun_subst_valtype_case_4 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_valtype .V128 tv_lst tu_lst (valtype_vectype (subst_vectype .V128 tv_lst tu_lst))
  | fun_subst_valtype_case_5 : forall (null_opt : (Option null)) (v_heaptype : heaptype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : reftype), 
    (fun_subst_reftype (.REF null_opt v_heaptype) tv_lst tu_lst var_0) ->
    fun_subst_valtype (.REF null_opt v_heaptype) tv_lst tu_lst (valtype_reftype var_0)
  | fun_subst_valtype_case_6 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_valtype .BOT tv_lst tu_lst .BOT

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:348.6-348.24 -/
inductive fun_subst_storagetype : storagetype -> (List typevar) -> (List typeuse) -> storagetype -> Prop where
  | fun_subst_storagetype_case_0 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : valtype), 
    (fun_subst_valtype .BOT tv_lst tu_lst var_0) ->
    fun_subst_storagetype .BOT tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_1 : forall (null_opt : (Option null)) (v_heaptype : heaptype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : valtype), 
    (fun_subst_valtype (.REF null_opt v_heaptype) tv_lst tu_lst var_0) ->
    fun_subst_storagetype (.REF null_opt v_heaptype) tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_2 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : valtype), 
    (fun_subst_valtype .V128 tv_lst tu_lst var_0) ->
    fun_subst_storagetype .V128 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_3 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : valtype), 
    (fun_subst_valtype .F64 tv_lst tu_lst var_0) ->
    fun_subst_storagetype .F64 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_4 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : valtype), 
    (fun_subst_valtype .F32 tv_lst tu_lst var_0) ->
    fun_subst_storagetype .F32 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_5 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : valtype), 
    (fun_subst_valtype .I64 tv_lst tu_lst var_0) ->
    fun_subst_storagetype .I64 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_6 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : valtype), 
    (fun_subst_valtype .I32 tv_lst tu_lst var_0) ->
    fun_subst_storagetype .I32 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_7 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_storagetype .I8 tv_lst tu_lst (storagetype_packtype (subst_packtype .I8 tv_lst tu_lst))
  | fun_subst_storagetype_case_8 : forall (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_storagetype .I16 tv_lst tu_lst (storagetype_packtype (subst_packtype .I16 tv_lst tu_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:349.6-349.22 -/
inductive fun_subst_fieldtype : fieldtype -> (List typevar) -> (List typeuse) -> fieldtype -> Prop where
  | fun_subst_fieldtype_case_0 : forall (mut_opt : (Option «mut»)) (zt : storagetype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : storagetype), 
    (fun_subst_storagetype zt tv_lst tu_lst var_0) ->
    fun_subst_fieldtype (.mk_fieldtype mut_opt zt) tv_lst tu_lst (.mk_fieldtype mut_opt var_0)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:351.6-351.21 -/
inductive fun_subst_comptype : comptype -> (List typevar) -> (List typeuse) -> comptype -> Prop where
  | fun_subst_comptype_case_0 : forall (ft_lst : (List fieldtype)) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0_lst : (List fieldtype)), 
    ((List.length var_0_lst) == (List.length ft_lst)) ->
    Forall₂ (fun (var_0 : fieldtype) (ft : fieldtype) => (fun_subst_fieldtype ft tv_lst tu_lst var_0)) var_0_lst ft_lst ->
    fun_subst_comptype (.STRUCT (.mk_list ft_lst)) tv_lst tu_lst (.STRUCT (.mk_list var_0_lst))
  | fun_subst_comptype_case_1 : forall (ft : fieldtype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : fieldtype), 
    (fun_subst_fieldtype ft tv_lst tu_lst var_0) ->
    fun_subst_comptype (.ARRAY ft) tv_lst tu_lst (.ARRAY var_0)
  | fun_subst_comptype_case_2 : forall (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_1_lst : (List valtype)) (var_0_lst : (List valtype)), 
    ((List.length var_1_lst) == (List.length t_2_lst)) ->
    Forall₂ (fun (var_1 : valtype) (t_2 : valtype) => (fun_subst_valtype t_2 tv_lst tu_lst var_1)) var_1_lst t_2_lst ->
    ((List.length var_0_lst) == (List.length t_1_lst)) ->
    Forall₂ (fun (var_0 : valtype) (t_1 : valtype) => (fun_subst_valtype t_1 tv_lst tu_lst var_0)) var_0_lst t_1_lst ->
    fun_subst_comptype (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) tv_lst tu_lst (.FUNC (.mk_list var_0_lst) (.mk_list var_1_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:352.6-352.20 -/
inductive fun_subst_subtype : subtype -> (List typevar) -> (List typeuse) -> subtype -> Prop where
  | fun_subst_subtype_case_0 : forall (final_opt : (Option final)) (tu'_lst : (List typeuse)) (ct : comptype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_1 : comptype) (var_0_lst : (List typeuse)), 
    (fun_subst_comptype ct tv_lst tu_lst var_1) ->
    ((List.length var_0_lst) == (List.length tu'_lst)) ->
    Forall₂ (fun (var_0 : typeuse) (tu' : typeuse) => (fun_subst_typeuse tu' tv_lst tu_lst var_0)) var_0_lst tu'_lst ->
    fun_subst_subtype (.SUB final_opt tu'_lst ct) tv_lst tu_lst (.SUB final_opt var_0_lst var_1)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:353.6-353.20 -/
inductive fun_subst_rectype : rectype -> (List typevar) -> (List typeuse) -> rectype -> Prop where
  | fun_subst_rectype_case_0 : forall (st_lst : (List subtype)) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (tv'_lst : (List typevar)) (tu'_lst : (List typeuse)) (var_1 : (List typevar) × (List typeuse)) (var_0_lst : (List subtype)), 
    (fun_minus_recs tv_lst tu_lst var_1) ->
    ((List.length var_0_lst) == (List.length st_lst)) ->
    Forall₂ (fun (var_0 : subtype) (st : subtype) => (fun_subst_subtype st tv'_lst tu'_lst var_0)) var_0_lst st_lst ->
    ((tv'_lst, tu'_lst) == var_1) ->
    fun_subst_rectype (.REC (.mk_list st_lst)) tv_lst tu_lst (.REC (.mk_list var_0_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:354.6-354.20 -/
inductive fun_subst_deftype : deftype -> (List typevar) -> (List typeuse) -> deftype -> Prop where
  | fun_subst_deftype_case_0 : forall (qt : rectype) (i : Nat) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : rectype), 
    (fun_subst_rectype qt tv_lst tu_lst var_0) ->
    fun_subst_deftype (._DEF qt i) tv_lst tu_lst (._DEF var_0 i)

end

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:340.1-340.112 -/
def subst_addrtype : ∀  (v_addrtype : addrtype) (var_0 : (List typevar)) (var_1 : (List typeuse)) , addrtype
  | «at», tv_lst, tu_lst =>
    «at»


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:356.6-356.20 -/
inductive fun_subst_tagtype : tagtype -> (List typevar) -> (List typeuse) -> tagtype -> Prop where
  | fun_subst_tagtype_case_0 : forall (tu' : typeuse) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : tagtype), 
    (fun_subst_typeuse tu' tv_lst tu_lst var_0) ->
    fun_subst_tagtype tu' tv_lst tu_lst var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:357.6-357.23 -/
inductive fun_subst_globaltype : globaltype -> (List typevar) -> (List typeuse) -> globaltype -> Prop where
  | fun_subst_globaltype_case_0 : forall (mut_opt : (Option «mut»)) (t : valtype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : valtype), 
    (fun_subst_valtype t tv_lst tu_lst var_0) ->
    fun_subst_globaltype (.mk_globaltype mut_opt t) tv_lst tu_lst (.mk_globaltype mut_opt var_0)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:358.1-358.112 -/
def subst_memtype : ∀  (v_memtype : memtype) (var_0 : (List typevar)) (var_1 : (List typeuse)) , memtype
  | (.PAGE «at» lim), tv_lst, tu_lst =>
    (.PAGE «at» lim)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:359.6-359.22 -/
inductive fun_subst_tabletype : tabletype -> (List typevar) -> (List typeuse) -> tabletype -> Prop where
  | fun_subst_tabletype_case_0 : forall («at» : addrtype) (lim : limits) (rt : reftype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : reftype), 
    (fun_subst_reftype rt tv_lst tu_lst var_0) ->
    fun_subst_tabletype (.mk_tabletype «at» lim rt) tv_lst tu_lst (.mk_tabletype «at» lim var_0)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:361.6-361.23 -/
inductive fun_subst_externtype : externtype -> (List typevar) -> (List typeuse) -> externtype -> Prop where
  | fun_subst_externtype_case_0 : forall (jt : typeuse) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : tagtype), 
    (fun_subst_tagtype jt tv_lst tu_lst var_0) ->
    fun_subst_externtype (.TAG jt) tv_lst tu_lst (.TAG var_0)
  | fun_subst_externtype_case_1 : forall (gt : globaltype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : globaltype), 
    (fun_subst_globaltype gt tv_lst tu_lst var_0) ->
    fun_subst_externtype (.GLOBAL gt) tv_lst tu_lst (.GLOBAL var_0)
  | fun_subst_externtype_case_2 : forall (tt : tabletype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : tabletype), 
    (fun_subst_tabletype tt tv_lst tu_lst var_0) ->
    fun_subst_externtype (.TABLE tt) tv_lst tu_lst (.TABLE var_0)
  | fun_subst_externtype_case_3 : forall (mt : memtype) (tv_lst : (List typevar)) (tu_lst : (List typeuse)), fun_subst_externtype (.MEM mt) tv_lst tu_lst (.MEM (subst_memtype mt tv_lst tu_lst))
  | fun_subst_externtype_case_4 : forall (v_rectype : rectype) (v_n : n) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_0 : deftype), 
    (fun_subst_deftype (._DEF v_rectype v_n) tv_lst tu_lst var_0) ->
    fun_subst_externtype (.FUNC (._DEF v_rectype v_n)) tv_lst tu_lst (.FUNC (typeuse_deftype var_0))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:362.6-362.23 -/
inductive fun_subst_moduletype : moduletype -> (List typevar) -> (List typeuse) -> moduletype -> Prop where
  | fun_subst_moduletype_case_0 : forall (xt_1_lst : (List externtype)) (xt_2_lst : (List externtype)) (tv_lst : (List typevar)) (tu_lst : (List typeuse)) (var_1_lst : (List externtype)) (var_0_lst : (List externtype)), 
    ((List.length var_1_lst) == (List.length xt_2_lst)) ->
    Forall₂ (fun (var_1 : externtype) (xt_2 : externtype) => (fun_subst_externtype xt_2 tv_lst tu_lst var_1)) var_1_lst xt_2_lst ->
    ((List.length var_0_lst) == (List.length xt_1_lst)) ->
    Forall₂ (fun (var_0 : externtype) (xt_1 : externtype) => (fun_subst_externtype xt_1 tv_lst tu_lst var_0)) var_0_lst xt_1_lst ->
    fun_subst_moduletype (.mk_moduletype xt_1_lst xt_2_lst) tv_lst tu_lst (.mk_moduletype var_0_lst var_1_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:431.6-431.24 -/
inductive fun_subst_all_valtype : valtype -> (List typeuse) -> valtype -> Prop where
  | fun_subst_all_valtype_case_0 : forall (t : valtype) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : valtype), 
    (fun_subst_valtype t (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst var_0) ->
    fun_subst_all_valtype t tu_lst var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:432.6-432.24 -/
inductive fun_subst_all_reftype : reftype -> (List typeuse) -> reftype -> Prop where
  | fun_subst_all_reftype_case_0 : forall (rt : reftype) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : reftype), 
    (fun_subst_reftype rt (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst var_0) ->
    fun_subst_all_reftype rt tu_lst var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:433.6-433.24 -/
inductive fun_subst_all_deftype : deftype -> (List typeuse) -> deftype -> Prop where
  | fun_subst_all_deftype_case_0 : forall (dt : deftype) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : deftype), 
    (fun_subst_deftype dt (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst var_0) ->
    fun_subst_all_deftype dt tu_lst var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:434.6-434.24 -/
inductive fun_subst_all_tagtype : tagtype -> (List typeuse) -> tagtype -> Prop where
  | fun_subst_all_tagtype_case_0 : forall (jt : typeuse) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : tagtype), 
    (fun_subst_tagtype jt (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst var_0) ->
    fun_subst_all_tagtype jt tu_lst var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:435.6-435.27 -/
inductive fun_subst_all_globaltype : globaltype -> (List typeuse) -> globaltype -> Prop where
  | fun_subst_all_globaltype_case_0 : forall (gt : globaltype) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : globaltype), 
    (fun_subst_globaltype gt (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst var_0) ->
    fun_subst_all_globaltype gt tu_lst var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:436.6-436.24 -/
inductive fun_subst_all_memtype : memtype -> (List typeuse) -> memtype -> Prop where
  | fun_subst_all_memtype_case_0 : forall (mt : memtype) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)), fun_subst_all_memtype mt tu_lst (subst_memtype mt (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:437.6-437.26 -/
inductive fun_subst_all_tabletype : tabletype -> (List typeuse) -> tabletype -> Prop where
  | fun_subst_all_tabletype_case_0 : forall (tt : tabletype) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : tabletype), 
    (fun_subst_tabletype tt (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst var_0) ->
    fun_subst_all_tabletype tt tu_lst var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:438.6-438.27 -/
inductive fun_subst_all_externtype : externtype -> (List typeuse) -> externtype -> Prop where
  | fun_subst_all_externtype_case_0 : forall (xt : externtype) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : externtype), 
    (fun_subst_externtype xt (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst var_0) ->
    fun_subst_all_externtype xt tu_lst var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:439.6-439.27 -/
inductive fun_subst_all_moduletype : moduletype -> (List typeuse) -> moduletype -> Prop where
  | fun_subst_all_moduletype_case_0 : forall (mmt : moduletype) (tu_lst : (List typeuse)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : moduletype), 
    (fun_subst_moduletype mmt (List.map (fun (i : Nat) => (._IDX (.mk_uN i))) i_lst) tu_lst var_0) ->
    fun_subst_all_moduletype mmt tu_lst var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:451.1-451.97 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:451.6-451.25 -/
inductive fun_subst_all_deftypes : (List deftype) -> (List typeuse) -> (List deftype) -> Prop where
  | fun_subst_all_deftypes_case_0 : forall (tu_lst : (List typeuse)), fun_subst_all_deftypes [] tu_lst []
  | fun_subst_all_deftypes_case_1 : forall (dt_1 : deftype) (dt_lst : (List deftype)) (tu_lst : (List typeuse)) (var_1 : (List deftype)) (var_0 : deftype), 
    (fun_subst_all_deftypes dt_lst tu_lst var_1) ->
    (fun_subst_all_deftype dt_1 tu_lst var_0) ->
    fun_subst_all_deftypes ([dt_1] ++ dt_lst) tu_lst ([var_0] ++ var_1)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:458.6-458.13 -/
inductive fun_rollrt : typeidx -> rectype -> rectype -> Prop where
  | fun_rollrt_case_0 : forall (x : uN) (v_rectype : rectype) (subtype_lst : (List subtype)) (i_lst : (List Nat)) (v_n : Nat) (var_0_lst : (List subtype)), 
    Forall₂ (fun (var_0 : subtype) (v_subtype : subtype) => (fun_subst_subtype v_subtype (List.map (fun (i : Nat) => (._IDX (.mk_uN ((proj_uN_0 x) + i)))) i_lst) (List.map (fun (i : Nat) => (.REC i)) i_lst) var_0)) var_0_lst subtype_lst ->
    (v_rectype == (.REC (.mk_list subtype_lst))) ->
    fun_rollrt x v_rectype (.REC (.mk_list var_0_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:459.6-459.15 -/
inductive fun_unrollrt : rectype -> rectype -> Prop where
  | fun_unrollrt_case_0 : forall (v_rectype : rectype) (subtype_lst : (List subtype)) (i_lst : (List Nat)) (v_n : Nat) (var_0_lst : (List subtype)), 
    Forall₂ (fun (var_0 : subtype) (v_subtype : subtype) => (fun_subst_subtype v_subtype (List.map (fun (i : Nat) => (.REC i)) i_lst) (List.map (fun (i : Nat) => (._DEF v_rectype i)) i_lst) var_0)) var_0_lst subtype_lst ->
    (v_rectype == (.REC (.mk_list subtype_lst))) ->
    fun_unrollrt v_rectype (.REC (.mk_list var_0_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:460.6-460.13 -/
inductive fun_rolldt : typeidx -> rectype -> (List deftype) -> Prop where
  | fun_rolldt_case_0 : forall (x : uN) (v_rectype : rectype) (subtype_lst : (List subtype)) (v_n : Nat) (i_lst : (List Nat)) (var_0 : rectype), 
    (fun_rollrt x v_rectype var_0) ->
    (var_0 == (.REC (.mk_list subtype_lst))) ->
    fun_rolldt x v_rectype (List.map (fun (i : Nat) => (._DEF (.REC (.mk_list subtype_lst)) i)) i_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:461.6-461.15 -/
inductive fun_unrolldt : deftype -> subtype -> Prop where
  | fun_unrolldt_case_0 : forall (v_rectype : rectype) (i : Nat) (subtype_lst : (List subtype)) (var_0 : rectype), 
    (i < (List.length subtype_lst)) ->
    (fun_unrollrt v_rectype var_0) ->
    (var_0 == (.REC (.mk_list subtype_lst))) ->
    fun_unrolldt (._DEF v_rectype i) (subtype_lst[i]!)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:462.6-462.15 -/
inductive fun_expanddt : deftype -> comptype -> Prop where
  | fun_expanddt_case_0 : forall (v_deftype : deftype) (v_comptype : comptype) (final_opt : (Option final)) (typeuse_lst : (List typeuse)) (var_0 : subtype), 
    (fun_unrolldt v_deftype var_0) ->
    (var_0 == (.SUB final_opt typeuse_lst v_comptype)) ->
    fun_expanddt v_deftype v_comptype

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:477.1-477.35 -/
def free_addrtype : ∀  (v_numtype : numtype) , free
  | .I32 =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | .I64 =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:478.1-478.34 -/
def free_numtype : ∀  (v_numtype : numtype) , free
  | v_numtype =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:479.1-479.36 -/
def free_packtype : ∀  (v_packtype : packtype) , free
  | v_packtype =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:480.1-480.36 -/
def free_lanetype : ∀  (v_lanetype : lanetype) , free
  | .I32 =>
    (free_numtype .I32)
  | .I64 =>
    (free_numtype .I64)
  | .F32 =>
    (free_numtype .F32)
  | .F64 =>
    (free_numtype .F64)
  | .I8 =>
    (free_packtype .I8)
  | .I16 =>
    (free_packtype .I16)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:481.1-481.34 -/
def free_vectype : ∀  (v_vectype : vectype) , free
  | v_vectype =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:482.1-482.38 -/
def free_consttype : ∀  (v_consttype : consttype) , free
  | .I32 =>
    (free_numtype .I32)
  | .I64 =>
    (free_numtype .I64)
  | .F32 =>
    (free_numtype .F32)
  | .F64 =>
    (free_numtype .F64)
  | .V128 =>
    (free_vectype .V128)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:483.1-483.42 -/
def free_absheaptype : ∀  (v_absheaptype : absheaptype) , free
  | v_absheaptype =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:486.1-486.34 -/
def free_typevar : ∀  (v_typevar : typevar) , free
  | (._IDX v_typeidx) =>
    (free_typeidx v_typeidx)
  | (.REC v_n) =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Recursive Definitions at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:484.1-523.34 -/
mutual
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:484.6-484.20 -/
inductive fun_free_heaptype : heaptype -> free -> Prop where
  | fun_free_heaptype_case_0 : fun_free_heaptype .ANY (free_absheaptype .ANY)
  | fun_free_heaptype_case_1 : fun_free_heaptype .EQ (free_absheaptype .EQ)
  | fun_free_heaptype_case_2 : fun_free_heaptype .I31 (free_absheaptype .I31)
  | fun_free_heaptype_case_3 : fun_free_heaptype .STRUCT (free_absheaptype .STRUCT)
  | fun_free_heaptype_case_4 : fun_free_heaptype .ARRAY (free_absheaptype .ARRAY)
  | fun_free_heaptype_case_5 : fun_free_heaptype .NONE (free_absheaptype .NONE)
  | fun_free_heaptype_case_6 : fun_free_heaptype .FUNC (free_absheaptype .FUNC)
  | fun_free_heaptype_case_7 : fun_free_heaptype .NOFUNC (free_absheaptype .NOFUNC)
  | fun_free_heaptype_case_8 : fun_free_heaptype .EXN (free_absheaptype .EXN)
  | fun_free_heaptype_case_9 : fun_free_heaptype .NOEXN (free_absheaptype .NOEXN)
  | fun_free_heaptype_case_10 : fun_free_heaptype .EXTERN (free_absheaptype .EXTERN)
  | fun_free_heaptype_case_11 : fun_free_heaptype .NOEXTERN (free_absheaptype .NOEXTERN)
  | fun_free_heaptype_case_12 : fun_free_heaptype .BOT (free_absheaptype .BOT)
  | fun_free_heaptype_case_13 : forall (n_0 : n) (var_0 : free), 
    (fun_free_typeuse (.REC n_0) var_0) ->
    fun_free_heaptype (.REC n_0) var_0
  | fun_free_heaptype_case_14 : forall (v_rectype : rectype) (v_n : n) (var_0 : free), 
    (fun_free_typeuse (._DEF v_rectype v_n) var_0) ->
    fun_free_heaptype (._DEF v_rectype v_n) var_0
  | fun_free_heaptype_case_15 : forall (v_typeidx : typeidx) (var_0 : free), 
    (fun_free_typeuse (._IDX v_typeidx) var_0) ->
    fun_free_heaptype (._IDX v_typeidx) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:485.6-485.19 -/
inductive fun_free_reftype : reftype -> free -> Prop where
  | fun_free_reftype_case_0 : forall (null_opt : (Option null)) (v_heaptype : heaptype) (var_0 : free), 
    (fun_free_heaptype v_heaptype var_0) ->
    fun_free_reftype (.REF null_opt v_heaptype) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:487.6-487.19 -/
inductive fun_free_typeuse : typeuse -> free -> Prop where
  | fun_free_typeuse_case_0 : forall (v_n : n), fun_free_typeuse (.REC v_n) (free_typevar (.REC v_n))
  | fun_free_typeuse_case_1 : forall (v_typeidx : typeidx), fun_free_typeuse (._IDX v_typeidx) (free_typevar (._IDX v_typeidx))
  | fun_free_typeuse_case_2 : forall (v_rectype : rectype) (v_n : n) (var_0 : free), 
    (fun_free_deftype (._DEF v_rectype v_n) var_0) ->
    fun_free_typeuse (._DEF v_rectype v_n) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:488.6-488.19 -/
inductive fun_free_valtype : valtype -> free -> Prop where
  | fun_free_valtype_case_0 : fun_free_valtype .I32 (free_numtype .I32)
  | fun_free_valtype_case_1 : fun_free_valtype .I64 (free_numtype .I64)
  | fun_free_valtype_case_2 : fun_free_valtype .F32 (free_numtype .F32)
  | fun_free_valtype_case_3 : fun_free_valtype .F64 (free_numtype .F64)
  | fun_free_valtype_case_4 : fun_free_valtype .V128 (free_vectype .V128)
  | fun_free_valtype_case_5 : forall (null_opt : (Option null)) (v_heaptype : heaptype) (var_0 : free), 
    (fun_free_reftype (.REF null_opt v_heaptype) var_0) ->
    fun_free_valtype (.REF null_opt v_heaptype) var_0
  | fun_free_valtype_case_6 : fun_free_valtype .BOT { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:490.6-490.22 -/
inductive fun_free_resulttype : resulttype -> free -> Prop where
  | fun_free_resulttype_case_0 : forall (valtype_lst : (List valtype)) (var_1_lst : (List free)) (var_0 : free), 
    ((List.length var_1_lst) == (List.length valtype_lst)) ->
    Forall₂ (fun (var_1 : free) (v_valtype : valtype) => (fun_free_valtype v_valtype var_1)) var_1_lst valtype_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_free_resulttype (.mk_list valtype_lst) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:491.6-491.23 -/
inductive fun_free_storagetype : storagetype -> free -> Prop where
  | fun_free_storagetype_case_0 : forall (var_0 : free), 
    (fun_free_valtype .BOT var_0) ->
    fun_free_storagetype .BOT var_0
  | fun_free_storagetype_case_1 : forall (null_opt : (Option null)) (v_heaptype : heaptype) (var_0 : free), 
    (fun_free_valtype (.REF null_opt v_heaptype) var_0) ->
    fun_free_storagetype (.REF null_opt v_heaptype) var_0
  | fun_free_storagetype_case_2 : forall (var_0 : free), 
    (fun_free_valtype .V128 var_0) ->
    fun_free_storagetype .V128 var_0
  | fun_free_storagetype_case_3 : forall (var_0 : free), 
    (fun_free_valtype .F64 var_0) ->
    fun_free_storagetype .F64 var_0
  | fun_free_storagetype_case_4 : forall (var_0 : free), 
    (fun_free_valtype .F32 var_0) ->
    fun_free_storagetype .F32 var_0
  | fun_free_storagetype_case_5 : forall (var_0 : free), 
    (fun_free_valtype .I64 var_0) ->
    fun_free_storagetype .I64 var_0
  | fun_free_storagetype_case_6 : forall (var_0 : free), 
    (fun_free_valtype .I32 var_0) ->
    fun_free_storagetype .I32 var_0
  | fun_free_storagetype_case_7 : fun_free_storagetype .I8 (free_packtype .I8)
  | fun_free_storagetype_case_8 : fun_free_storagetype .I16 (free_packtype .I16)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:492.6-492.21 -/
inductive fun_free_fieldtype : fieldtype -> free -> Prop where
  | fun_free_fieldtype_case_0 : forall (mut_opt : (Option «mut»)) (v_storagetype : storagetype) (var_0 : free), 
    (fun_free_storagetype v_storagetype var_0) ->
    fun_free_fieldtype (.mk_fieldtype mut_opt v_storagetype) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:493.6-493.20 -/
inductive fun_free_comptype : comptype -> free -> Prop where
  | fun_free_comptype_case_0 : forall (fieldtype_lst : (List fieldtype)) (var_1_lst : (List free)) (var_0 : free), 
    ((List.length var_1_lst) == (List.length fieldtype_lst)) ->
    Forall₂ (fun (var_1 : free) (v_fieldtype : fieldtype) => (fun_free_fieldtype v_fieldtype var_1)) var_1_lst fieldtype_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_free_comptype (.STRUCT (.mk_list fieldtype_lst)) var_0
  | fun_free_comptype_case_1 : forall (v_fieldtype : fieldtype) (var_0 : free), 
    (fun_free_fieldtype v_fieldtype var_0) ->
    fun_free_comptype (.ARRAY v_fieldtype) var_0
  | fun_free_comptype_case_2 : forall (resulttype_1 : (list valtype)) (resulttype_2 : (list valtype)) (var_1 : free) (var_0 : free), 
    (fun_free_resulttype resulttype_2 var_1) ->
    (fun_free_resulttype resulttype_1 var_0) ->
    fun_free_comptype (.FUNC resulttype_1 resulttype_2) (var_0 ++ var_1)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:494.6-494.19 -/
inductive fun_free_subtype : subtype -> free -> Prop where
  | fun_free_subtype_case_0 : forall (final_opt : (Option final)) (typeuse_lst : (List typeuse)) (v_comptype : comptype) (var_2 : free) (var_1_lst : (List free)) (var_0 : free), 
    (fun_free_comptype v_comptype var_2) ->
    ((List.length var_1_lst) == (List.length typeuse_lst)) ->
    Forall₂ (fun (var_1 : free) (v_typeuse : typeuse) => (fun_free_typeuse v_typeuse var_1)) var_1_lst typeuse_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_free_subtype (.SUB final_opt typeuse_lst v_comptype) (var_0 ++ var_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:495.6-495.19 -/
inductive fun_free_rectype : rectype -> free -> Prop where
  | fun_free_rectype_case_0 : forall (subtype_lst : (List subtype)) (var_1_lst : (List free)) (var_0 : free), 
    ((List.length var_1_lst) == (List.length subtype_lst)) ->
    Forall₂ (fun (var_1 : free) (v_subtype : subtype) => (fun_free_subtype v_subtype var_1)) var_1_lst subtype_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_free_rectype (.REC (.mk_list subtype_lst)) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:523.6-523.19 -/
inductive fun_free_deftype : deftype -> free -> Prop where
  | fun_free_deftype_case_0 : forall (v_rectype : rectype) (v_n : Nat) (var_0 : free), 
    (fun_free_rectype v_rectype var_0) ->
    fun_free_deftype (._DEF v_rectype v_n) var_0

end

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:497.6-497.19 -/
inductive fun_free_tagtype : tagtype -> free -> Prop where
  | fun_free_tagtype_case_0 : forall (v_rectype : rectype) (v_n : n) (var_0 : free), 
    (fun_free_deftype (._DEF v_rectype v_n) var_0) ->
    fun_free_tagtype (._DEF v_rectype v_n) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:498.6-498.22 -/
inductive fun_free_globaltype : globaltype -> free -> Prop where
  | fun_free_globaltype_case_0 : forall (mut_opt : (Option «mut»)) (v_valtype : valtype) (var_0 : free), 
    (fun_free_valtype v_valtype var_0) ->
    fun_free_globaltype (.mk_globaltype mut_opt v_valtype) var_0

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:499.1-499.34 -/
def free_memtype : ∀  (v_memtype : memtype) , free
  | (.PAGE v_addrtype v_limits) =>
    (free_addrtype (numtype_addrtype v_addrtype))


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:500.6-500.21 -/
inductive fun_free_tabletype : tabletype -> free -> Prop where
  | fun_free_tabletype_case_0 : forall (v_addrtype : addrtype) (v_limits : limits) (v_reftype : reftype) (var_0 : free), 
    (fun_free_reftype v_reftype var_0) ->
    fun_free_tabletype (.mk_tabletype v_addrtype v_limits v_reftype) ((free_addrtype (numtype_addrtype v_addrtype)) ++ var_0)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:501.1-501.36 -/
def free_datatype : ∀  (v_datatype : datatype) , free
  | .OK =>
    { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:502.6-502.20 -/
inductive fun_free_elemtype : elemtype -> free -> Prop where
  | fun_free_elemtype_case_0 : forall (v_reftype : reftype) (var_0 : free), 
    (fun_free_reftype v_reftype var_0) ->
    fun_free_elemtype v_reftype var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:503.6-503.22 -/
inductive fun_free_externtype : externtype -> free -> Prop where
  | fun_free_externtype_case_0 : forall (v_tagtype : typeuse) (var_0 : free), 
    (fun_free_tagtype v_tagtype var_0) ->
    fun_free_externtype (.TAG v_tagtype) var_0
  | fun_free_externtype_case_1 : forall (v_globaltype : globaltype) (var_0 : free), 
    (fun_free_globaltype v_globaltype var_0) ->
    fun_free_externtype (.GLOBAL v_globaltype) var_0
  | fun_free_externtype_case_2 : forall (v_memtype : memtype), fun_free_externtype (.MEM v_memtype) (free_memtype v_memtype)
  | fun_free_externtype_case_3 : forall (v_tabletype : tabletype) (var_0 : free), 
    (fun_free_tabletype v_tabletype var_0) ->
    fun_free_externtype (.TABLE v_tabletype) var_0
  | fun_free_externtype_case_4 : forall (v_typeuse : typeuse) (var_0 : free), 
    (fun_free_typeuse v_typeuse var_0) ->
    fun_free_externtype (.FUNC v_typeuse) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.2-syntax.types.spectec:504.6-504.22 -/
inductive fun_free_moduletype : moduletype -> free -> Prop where
  | fun_free_moduletype_case_0 : forall (externtype_1_lst : (List externtype)) (externtype_2_lst : (List externtype)) (var_3_lst : (List free)) (var_2 : free) (var_1_lst : (List free)) (var_0 : free), 
    ((List.length var_3_lst) == (List.length externtype_2_lst)) ->
    Forall₂ (fun (var_3 : free) (externtype_2 : externtype) => (fun_free_externtype externtype_2 var_3)) var_3_lst externtype_2_lst ->
    (fun_free_list var_3_lst var_2) ->
    ((List.length var_1_lst) == (List.length externtype_1_lst)) ->
    Forall₂ (fun (var_1 : free) (externtype_1 : externtype) => (fun_free_externtype externtype_1 var_1)) var_1_lst externtype_1_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_free_moduletype (.mk_moduletype externtype_1_lst externtype_2_lst) (var_0 ++ var_2)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 -/
inductive num_ : Type where
  | mk_num__0 (v_Inn : Inn) (var_x : iN) : num_
  | mk_num__1 (v_Fnn : Fnn) (var_x : fN) : num_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.8-7.13 -/
inductive wf_num_ : numtype -> num_ -> Prop where
  | num__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : iN), 
    (wf_uN (size (numtype_addrtype v_Inn)) var_x) ->
    (v_numtype == (numtype_addrtype v_Inn)) ->
    wf_num_ v_numtype (.mk_num__0 v_Inn var_x)
  | num__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : fN), 
    (wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x) ->
    (v_numtype == (numtype_Fnn v_Fnn)) ->
    wf_num_ v_numtype (.mk_num__1 v_Fnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 -/
def proj_num__0 : ∀  (var_x : num_) , (Option iN)
  | (.mk_num__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:7.1-7.21 -/
def proj_num__1 : ∀  (var_x : num_) , (Option fN)
  | (.mk_num__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:11.1-11.38 -/
abbrev pack_ : Type := iN

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -/
inductive lane_ : Type where
  | mk_lane__0 (v_numtype : numtype) (var_x : num_) : lane_
  | mk_lane__1 (v_packtype : packtype) (var_x : pack_) : lane_
  | mk_lane__2 (v_Jnn : Jnn) (var_x : iN) : lane_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.8-13.14 -/
inductive wf_lane_ : lanetype -> lane_ -> Prop where
  | lane__case_0 : forall (v_lanetype : lanetype) (v_numtype : numtype) (var_x : num_), 
    (wf_num_ v_numtype var_x) ->
    (v_lanetype == (lanetype_numtype v_numtype)) ->
    wf_lane_ v_lanetype (.mk_lane__0 v_numtype var_x)
  | lane__case_1 : forall (v_lanetype : lanetype) (v_packtype : packtype) (var_x : pack_), 
    (wf_uN (psize v_packtype) var_x) ->
    (v_lanetype == (lanetype_packtype v_packtype)) ->
    wf_lane_ v_lanetype (.mk_lane__1 v_packtype var_x)
  | lane__case_2 : forall (v_lanetype : lanetype) (v_Jnn : Jnn) (var_x : iN), 
    (wf_uN (lsize (lanetype_Jnn v_Jnn)) var_x) ->
    (v_lanetype == (lanetype_Jnn v_Jnn)) ->
    wf_lane_ v_lanetype (.mk_lane__2 v_Jnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -/
def proj_lane__0 : ∀  (var_x : lane_) , (Option num_)
  | (.mk_lane__0 v_numtype var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -/
def proj_lane__1 : ∀  (var_x : lane_) , (Option pack_)
  | (.mk_lane__1 v_packtype var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:13.1-13.23 -/
def proj_lane__2 : ∀  (var_x : lane_) , (Option iN)
  | (.mk_lane__2 v_Jnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:18.1-18.35 -/
abbrev vec_ : Type := vN

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -/
inductive lit_ : Type where
  | mk_lit__0 (v_numtype : numtype) (var_x : num_) : lit_
  | mk_lit__1 (v_vectype : vectype) (var_x : vec_) : lit_
  | mk_lit__2 (v_packtype : packtype) (var_x : pack_) : lit_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.8-20.13 -/
inductive wf_lit_ : storagetype -> lit_ -> Prop where
  | lit__case_0 : forall (v_storagetype : storagetype) (v_numtype : numtype) (var_x : num_), 
    (wf_num_ v_numtype var_x) ->
    (v_storagetype == (storagetype_numtype v_numtype)) ->
    wf_lit_ v_storagetype (.mk_lit__0 v_numtype var_x)
  | lit__case_1 : forall (v_storagetype : storagetype) (v_vectype : vectype) (var_x : vec_), 
    (wf_uN (vsize v_vectype) var_x) ->
    (v_storagetype == (storagetype_vectype v_vectype)) ->
    wf_lit_ v_storagetype (.mk_lit__1 v_vectype var_x)
  | lit__case_2 : forall (v_storagetype : storagetype) (v_packtype : packtype) (var_x : pack_), 
    (wf_uN (psize v_packtype) var_x) ->
    (v_storagetype == (storagetype_packtype v_packtype)) ->
    wf_lit_ v_storagetype (.mk_lit__2 v_packtype var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -/
def proj_lit__0 : ∀  (var_x : lit_) , (Option num_)
  | (.mk_lit__0 v_numtype var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -/
def proj_lit__1 : ∀  (var_x : lit_) , (Option vec_)
  | (.mk_lit__1 v_vectype var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:20.1-20.25 -/
def proj_lit__2 : ∀  (var_x : lit_) , (Option pack_)
  | (.mk_lit__2 v_packtype var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.1-28.56 -/
inductive sz : Type where
  | mk_sz (i : Nat) : sz
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.1-28.56 -/
def proj_sz_0 : ∀  (x : sz) , Nat
  | (.mk_sz v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:28.8-28.10 -/
inductive wf_sz : sz -> Prop where
  | sz_case_0 : forall (i : Nat), 
    ((((i == 8) || (i == 16)) || (i == 32)) || (i == 64)) ->
    wf_sz (.mk_sz i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:29.1-29.42 -/
inductive sx : Type where
  | U : sx
  | S : sx
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 -/
inductive unop_Inn : Type where
  | CLZ : unop_Inn
  | CTZ : unop_Inn
  | POPCNT : unop_Inn
  | EXTEND (v_sz : sz) : unop_Inn
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.8-31.14 -/
inductive wf_unop_Inn : Inn -> unop_Inn -> Prop where
  | unop_Inn_case_0 : forall (v_Inn : Inn), wf_unop_Inn v_Inn .CLZ
  | unop_Inn_case_1 : forall (v_Inn : Inn), wf_unop_Inn v_Inn .CTZ
  | unop_Inn_case_2 : forall (v_Inn : Inn), wf_unop_Inn v_Inn .POPCNT
  | unop_Inn_case_3 : forall (v_Inn : Inn) (v_sz : sz), 
    (wf_sz v_sz) ->
    ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) ->
    wf_unop_Inn v_Inn (.EXTEND v_sz)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 -/
inductive unop_Fnn : Type where
  | ABS : unop_Fnn
  | NEG : unop_Fnn
  | SQRT : unop_Fnn
  | CEIL : unop_Fnn
  | FLOOR : unop_Fnn
  | TRUNC : unop_Fnn
  | NEAREST : unop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 -/
inductive unop_ : Type where
  | mk_unop__0 (v_Inn : Inn) (var_x : unop_Inn) : unop_
  | mk_unop__1 (v_Fnn : Fnn) (var_x : unop_Fnn) : unop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.8-31.14 -/
inductive wf_unop_ : numtype -> unop_ -> Prop where
  | unop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : unop_Inn), 
    (wf_unop_Inn v_Inn var_x) ->
    (v_numtype == (numtype_addrtype v_Inn)) ->
    wf_unop_ v_numtype (.mk_unop__0 v_Inn var_x)
  | unop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : unop_Fnn), 
    (v_numtype == (numtype_Fnn v_Fnn)) ->
    wf_unop_ v_numtype (.mk_unop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 -/
def proj_unop__0 : ∀  (var_x : unop_) , (Option unop_Inn)
  | (.mk_unop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:31.1-31.22 -/
def proj_unop__1 : ∀  (var_x : unop_) , (Option unop_Fnn)
  | (.mk_unop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -/
inductive binop_Inn : Type where
  | ADD : binop_Inn
  | SUB : binop_Inn
  | MUL : binop_Inn
  | DIV (v_sx : sx) : binop_Inn
  | REM (v_sx : sx) : binop_Inn
  | AND : binop_Inn
  | OR : binop_Inn
  | XOR : binop_Inn
  | SHL : binop_Inn
  | SHR (v_sx : sx) : binop_Inn
  | ROTL : binop_Inn
  | ROTR : binop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -/
inductive binop_Fnn : Type where
  | ADD : binop_Fnn
  | SUB : binop_Fnn
  | MUL : binop_Fnn
  | DIV : binop_Fnn
  | MIN : binop_Fnn
  | MAX : binop_Fnn
  | COPYSIGN : binop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -/
inductive binop_ : Type where
  | mk_binop__0 (v_Inn : Inn) (var_x : binop_Inn) : binop_
  | mk_binop__1 (v_Fnn : Fnn) (var_x : binop_Fnn) : binop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.8-35.15 -/
inductive wf_binop_ : numtype -> binop_ -> Prop where
  | binop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : binop_Inn), 
    (v_numtype == (numtype_addrtype v_Inn)) ->
    wf_binop_ v_numtype (.mk_binop__0 v_Inn var_x)
  | binop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : binop_Fnn), 
    (v_numtype == (numtype_Fnn v_Fnn)) ->
    wf_binop_ v_numtype (.mk_binop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -/
def proj_binop__0 : ∀  (var_x : binop_) , (Option binop_Inn)
  | (.mk_binop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:35.1-35.23 -/
def proj_binop__1 : ∀  (var_x : binop_) , (Option binop_Fnn)
  | (.mk_binop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 -/
inductive testop_Inn : Type where
  | EQZ : testop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 -/
inductive testop_ : Type where
  | mk_testop__0 (v_Inn : Inn) (var_x : testop_Inn) : testop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.8-42.16 -/
inductive wf_testop_ : numtype -> testop_ -> Prop where
  | testop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : testop_Inn), 
    (v_numtype == (numtype_addrtype v_Inn)) ->
    wf_testop_ v_numtype (.mk_testop__0 v_Inn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:42.1-42.24 -/
def proj_testop__0 : ∀  (var_x : testop_) , testop_Inn
  | (.mk_testop__0 v_Inn var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -/
inductive relop_Inn : Type where
  | EQ : relop_Inn
  | NE : relop_Inn
  | LT (v_sx : sx) : relop_Inn
  | GT (v_sx : sx) : relop_Inn
  | LE (v_sx : sx) : relop_Inn
  | GE (v_sx : sx) : relop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -/
inductive relop_Fnn : Type where
  | EQ : relop_Fnn
  | NE : relop_Fnn
  | LT : relop_Fnn
  | GT : relop_Fnn
  | LE : relop_Fnn
  | GE : relop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -/
inductive relop_ : Type where
  | mk_relop__0 (v_Inn : Inn) (var_x : relop_Inn) : relop_
  | mk_relop__1 (v_Fnn : Fnn) (var_x : relop_Fnn) : relop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.8-46.15 -/
inductive wf_relop_ : numtype -> relop_ -> Prop where
  | relop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : relop_Inn), 
    (v_numtype == (numtype_addrtype v_Inn)) ->
    wf_relop_ v_numtype (.mk_relop__0 v_Inn var_x)
  | relop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : relop_Fnn), 
    (v_numtype == (numtype_Fnn v_Fnn)) ->
    wf_relop_ v_numtype (.mk_relop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -/
def proj_relop__0 : ∀  (var_x : relop_) , (Option relop_Inn)
  | (.mk_relop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:46.1-46.23 -/
def proj_relop__1 : ∀  (var_x : relop_) , (Option relop_Fnn)
  | (.mk_relop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
inductive cvtop__Inn_1_Inn_2 : Type where
  | EXTEND (v_sx : sx) : cvtop__Inn_1_Inn_2
  | WRAP : cvtop__Inn_1_Inn_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 -/
inductive wf_cvtop__Inn_1_Inn_2 : Inn -> Inn -> cvtop__Inn_1_Inn_2 -> Prop where
  | cvtop__Inn_1_Inn_2_case_0 : forall (Inn_1 : Inn) (Inn_2 : Inn) (v_sx : sx), 
    ((sizenn1 (numtype_addrtype Inn_1)) < (sizenn2 (numtype_addrtype Inn_2))) ->
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 (.EXTEND v_sx)
  | cvtop__Inn_1_Inn_2_case_1 : forall (Inn_1 : Inn) (Inn_2 : Inn), 
    ((sizenn1 (numtype_addrtype Inn_1)) > (sizenn2 (numtype_addrtype Inn_2))) ->
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 .WRAP

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
inductive cvtop__Inn_1_Fnn_2 : Type where
  | CONVERT (v_sx : sx) : cvtop__Inn_1_Fnn_2
  | REINTERPRET : cvtop__Inn_1_Fnn_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 -/
inductive wf_cvtop__Inn_1_Fnn_2 : Inn -> Fnn -> cvtop__Inn_1_Fnn_2 -> Prop where
  | cvtop__Inn_1_Fnn_2_case_0 : forall (Inn_1 : Inn) (Fnn_2 : Fnn) (v_sx : sx), wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 (.CONVERT v_sx)
  | cvtop__Inn_1_Fnn_2_case_1 : forall (Inn_1 : Inn) (Fnn_2 : Fnn), 
    ((sizenn1 (numtype_addrtype Inn_1)) == (sizenn2 (numtype_Fnn Fnn_2))) ->
    wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 .REINTERPRET

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
inductive cvtop__Fnn_1_Inn_2 : Type where
  | TRUNC (v_sx : sx) : cvtop__Fnn_1_Inn_2
  | TRUNC_SAT (v_sx : sx) : cvtop__Fnn_1_Inn_2
  | REINTERPRET : cvtop__Fnn_1_Inn_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 -/
inductive wf_cvtop__Fnn_1_Inn_2 : Fnn -> Inn -> cvtop__Fnn_1_Inn_2 -> Prop where
  | cvtop__Fnn_1_Inn_2_case_0 : forall (Fnn_1 : Fnn) (Inn_2 : Inn) (v_sx : sx), wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (.TRUNC v_sx)
  | cvtop__Fnn_1_Inn_2_case_1 : forall (Fnn_1 : Fnn) (Inn_2 : Inn) (v_sx : sx), wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (.TRUNC_SAT v_sx)
  | cvtop__Fnn_1_Inn_2_case_2 : forall (Fnn_1 : Fnn) (Inn_2 : Inn), 
    ((sizenn1 (numtype_Fnn Fnn_1)) == (sizenn2 (numtype_addrtype Inn_2))) ->
    wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 .REINTERPRET

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
inductive cvtop__Fnn_1_Fnn_2 : Type where
  | PROMOTE : cvtop__Fnn_1_Fnn_2
  | DEMOTE : cvtop__Fnn_1_Fnn_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 -/
inductive wf_cvtop__Fnn_1_Fnn_2 : Fnn -> Fnn -> cvtop__Fnn_1_Fnn_2 -> Prop where
  | cvtop__Fnn_1_Fnn_2_case_0 : forall (Fnn_1 : Fnn) (Fnn_2 : Fnn), 
    ((sizenn1 (numtype_Fnn Fnn_1)) < (sizenn2 (numtype_Fnn Fnn_2))) ->
    wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 .PROMOTE
  | cvtop__Fnn_1_Fnn_2_case_1 : forall (Fnn_1 : Fnn) (Fnn_2 : Fnn), 
    ((sizenn1 (numtype_Fnn Fnn_1)) > (sizenn2 (numtype_Fnn Fnn_2))) ->
    wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 .DEMOTE

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
inductive cvtop__ : Type where
  | mk_cvtop___0 (Inn_1 : Inn) (Inn_2 : Inn) (var_x : cvtop__Inn_1_Inn_2) : cvtop__
  | mk_cvtop___1 (Inn_1 : Inn) (Fnn_2 : Fnn) (var_x : cvtop__Inn_1_Fnn_2) : cvtop__
  | mk_cvtop___2 (Fnn_1 : Fnn) (Inn_2 : Inn) (var_x : cvtop__Fnn_1_Inn_2) : cvtop__
  | mk_cvtop___3 (Fnn_1 : Fnn) (Fnn_2 : Fnn) (var_x : cvtop__Fnn_1_Fnn_2) : cvtop__
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.8-55.16 -/
inductive wf_cvtop__ : numtype -> numtype -> cvtop__ -> Prop where
  | cvtop___case_0 : forall (numtype_1 : numtype) (numtype_2 : numtype) (Inn_1 : Inn) (Inn_2 : Inn) (var_x : cvtop__Inn_1_Inn_2), 
    (wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 var_x) ->
    (numtype_1 == (numtype_addrtype Inn_1)) ->
    (numtype_2 == (numtype_addrtype Inn_2)) ->
    wf_cvtop__ numtype_1 numtype_2 (.mk_cvtop___0 Inn_1 Inn_2 var_x)
  | cvtop___case_1 : forall (numtype_1 : numtype) (numtype_2 : numtype) (Inn_1 : Inn) (Fnn_2 : Fnn) (var_x : cvtop__Inn_1_Fnn_2), 
    (wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 var_x) ->
    (numtype_1 == (numtype_addrtype Inn_1)) ->
    (numtype_2 == (numtype_Fnn Fnn_2)) ->
    wf_cvtop__ numtype_1 numtype_2 (.mk_cvtop___1 Inn_1 Fnn_2 var_x)
  | cvtop___case_2 : forall (numtype_1 : numtype) (numtype_2 : numtype) (Fnn_1 : Fnn) (Inn_2 : Inn) (var_x : cvtop__Fnn_1_Inn_2), 
    (wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 var_x) ->
    (numtype_1 == (numtype_Fnn Fnn_1)) ->
    (numtype_2 == (numtype_addrtype Inn_2)) ->
    wf_cvtop__ numtype_1 numtype_2 (.mk_cvtop___2 Fnn_1 Inn_2 var_x)
  | cvtop___case_3 : forall (numtype_1 : numtype) (numtype_2 : numtype) (Fnn_1 : Fnn) (Fnn_2 : Fnn) (var_x : cvtop__Fnn_1_Fnn_2), 
    (wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 var_x) ->
    (numtype_1 == (numtype_Fnn Fnn_1)) ->
    (numtype_2 == (numtype_Fnn Fnn_2)) ->
    wf_cvtop__ numtype_1 numtype_2 (.mk_cvtop___3 Fnn_1 Fnn_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
def proj_cvtop___0 : ∀  (var_x : cvtop__) , (Option cvtop__Inn_1_Inn_2)
  | (.mk_cvtop___0 Inn_1 Inn_2 var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
def proj_cvtop___1 : ∀  (var_x : cvtop__) , (Option cvtop__Inn_1_Fnn_2)
  | (.mk_cvtop___1 Inn_1 Fnn_2 var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
def proj_cvtop___2 : ∀  (var_x : cvtop__) , (Option cvtop__Fnn_1_Inn_2)
  | (.mk_cvtop___2 Fnn_1 Inn_2 var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:55.1-55.37 -/
def proj_cvtop___3 : ∀  (var_x : cvtop__) , (Option cvtop__Fnn_1_Fnn_2)
  | (.mk_cvtop___3 Fnn_1 Fnn_2 var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.1-73.60 -/
inductive dim : Type where
  | mk_dim (i : Nat) : dim
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.1-73.60 -/
def proj_dim_0 : ∀  (x : dim) , Nat
  | (.mk_dim v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:73.8-73.11 -/
inductive wf_dim : dim -> Prop where
  | dim_case_0 : forall (i : Nat), 
    (((((i == 1) || (i == 2)) || (i == 4)) || (i == 8)) || (i == 16)) ->
    wf_dim (.mk_dim i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:74.1-75.40 -/
inductive shape : Type where
  | X (v_lanetype : lanetype) (v_dim : dim) : shape
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:74.8-74.13 -/
inductive wf_shape : shape -> Prop where
  | shape_case_0 : forall (v_lanetype : lanetype) (v_dim : dim), 
    (wf_dim v_dim) ->
    (((lsize v_lanetype) * (proj_dim_0 v_dim)) == 128) ->
    wf_shape (.X v_lanetype v_dim)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:78.1-78.43 -/
def fun_dim : ∀  (v_shape : shape) , dim
  | (.X v_Lnn (.mk_dim v_N)) =>
    (.mk_dim v_N)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:81.1-81.58 -/
def fun_lanetype : ∀  (v_shape : shape) , lanetype
  | (.X v_Lnn (.mk_dim v_N)) =>
    v_Lnn


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:84.1-84.57 -/
def unpackshape : ∀  (v_shape : shape) , numtype
  | (.X v_Lnn (.mk_dim v_N)) =>
    (lunpack v_Lnn)


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.1-88.78 -/
inductive ishape : Type where
  | mk_ishape (v_shape : shape) : ishape
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.1-88.78 -/
def proj_ishape_0 : ∀  (x : ishape) , shape
  | (.mk_ishape v_shape_0) =>
    (v_shape_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:88.8-88.14 -/
inductive wf_ishape : ishape -> Prop where
  | ishape_case_0 : forall (v_shape : shape) (v_Jnn : Jnn), 
    (wf_shape v_shape) ->
    ((fun_lanetype v_shape) == (lanetype_Jnn v_Jnn)) ->
    wf_ishape (.mk_ishape v_shape)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.1-89.77 -/
inductive bshape : Type where
  | mk_bshape (v_shape : shape) : bshape
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.1-89.77 -/
def proj_bshape_0 : ∀  (x : bshape) , shape
  | (.mk_bshape v_shape_0) =>
    (v_shape_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:89.8-89.14 -/
inductive wf_bshape : bshape -> Prop where
  | bshape_case_0 : forall (v_shape : shape), 
    (wf_shape v_shape) ->
    ((fun_lanetype v_shape) == .I8) ->
    wf_bshape (.mk_bshape v_shape)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:94.1-94.19 -/
inductive zero : Type where
  | ZERO : zero
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:95.1-95.25 -/
inductive half : Type where
  | LOW : half
  | HIGH : half
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:97.1-97.41 -/
inductive vvunop : Type where
  | NOT : vvunop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:98.1-98.62 -/
inductive vvbinop : Type where
  | AND : vvbinop
  | ANDNOT : vvbinop
  | OR : vvbinop
  | XOR : vvbinop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:99.1-99.49 -/
inductive vvternop : Type where
  | BITSELECT : vvternop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:100.1-100.48 -/
inductive vvtestop : Type where
  | ANY_TRUE : vvtestop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 -/
inductive vunop_Jnn_M : Type where
  | ABS : vunop_Jnn_M
  | NEG : vunop_Jnn_M
  | POPCNT : vunop_Jnn_M
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.8-102.15 -/
inductive wf_vunop_Jnn_M : Jnn -> M -> vunop_Jnn_M -> Prop where
  | vunop_Jnn_M_case_0 : forall (v_Jnn : Jnn) (v_M : M), wf_vunop_Jnn_M v_Jnn v_M .ABS
  | vunop_Jnn_M_case_1 : forall (v_Jnn : Jnn) (v_M : M), wf_vunop_Jnn_M v_Jnn v_M .NEG
  | vunop_Jnn_M_case_2 : forall (v_Jnn : Jnn) (v_M : M), 
    ((lsizenn (lanetype_Jnn v_Jnn)) == 8) ->
    wf_vunop_Jnn_M v_Jnn v_M .POPCNT

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 -/
inductive vunop_Fnn_M : Type where
  | ABS : vunop_Fnn_M
  | NEG : vunop_Fnn_M
  | SQRT : vunop_Fnn_M
  | CEIL : vunop_Fnn_M
  | FLOOR : vunop_Fnn_M
  | TRUNC : vunop_Fnn_M
  | NEAREST : vunop_Fnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 -/
inductive vunop_ : Type where
  | mk_vunop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vunop_Jnn_M) : vunop_
  | mk_vunop__1 (v_Fnn : Fnn) (v_M : M) (var_x : vunop_Fnn_M) : vunop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.8-102.15 -/
inductive wf_vunop_ : shape -> vunop_ -> Prop where
  | vunop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vunop_Jnn_M), 
    (wf_vunop_Jnn_M v_Jnn v_M var_x) ->
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) ->
    wf_vunop_ v_shape (.mk_vunop__0 v_Jnn v_M var_x)
  | vunop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_M : M) (var_x : vunop_Fnn_M), 
    (v_shape == (.X (lanetype_Fnn v_Fnn) (.mk_dim v_M))) ->
    wf_vunop_ v_shape (.mk_vunop__1 v_Fnn v_M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 -/
def proj_vunop__0 : ∀  (var_x : vunop_) , (Option vunop_Jnn_M)
  | (.mk_vunop__0 v_Jnn v_M var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:102.1-102.42 -/
def proj_vunop__1 : ∀  (var_x : vunop_) , (Option vunop_Fnn_M)
  | (.mk_vunop__1 v_Fnn v_M var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.1-107.43 -/
inductive vbinop_Jnn_M : Type where
  | ADD : vbinop_Jnn_M
  | SUB : vbinop_Jnn_M
  | ADD_SAT (v_sx : sx) : vbinop_Jnn_M
  | SUB_SAT (v_sx : sx) : vbinop_Jnn_M
  | MUL : vbinop_Jnn_M
  | AVGRU : vbinop_Jnn_M
  | Q15MULR_SATS : vbinop_Jnn_M
  | RELAXED_Q15MULRS : vbinop_Jnn_M
  | MIN (v_sx : sx) : vbinop_Jnn_M
  | MAX (v_sx : sx) : vbinop_Jnn_M
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.8-107.16 -/
inductive wf_vbinop_Jnn_M : Jnn -> M -> vbinop_Jnn_M -> Prop where
  | vbinop_Jnn_M_case_0 : forall (v_Jnn : Jnn) (v_M : M), wf_vbinop_Jnn_M v_Jnn v_M .ADD
  | vbinop_Jnn_M_case_1 : forall (v_Jnn : Jnn) (v_M : M), wf_vbinop_Jnn_M v_Jnn v_M .SUB
  | vbinop_Jnn_M_case_2 : forall (v_Jnn : Jnn) (v_M : M) (v_sx : sx), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
    wf_vbinop_Jnn_M v_Jnn v_M (.ADD_SAT v_sx)
  | vbinop_Jnn_M_case_3 : forall (v_Jnn : Jnn) (v_M : M) (v_sx : sx), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
    wf_vbinop_Jnn_M v_Jnn v_M (.SUB_SAT v_sx)
  | vbinop_Jnn_M_case_4 : forall (v_Jnn : Jnn) (v_M : M), 
    ((lsizenn (lanetype_Jnn v_Jnn)) >= 16) ->
    wf_vbinop_Jnn_M v_Jnn v_M .MUL
  | vbinop_Jnn_M_case_5 : forall (v_Jnn : Jnn) (v_M : M), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
    wf_vbinop_Jnn_M v_Jnn v_M .AVGRU
  | vbinop_Jnn_M_case_6 : forall (v_Jnn : Jnn) (v_M : M), 
    ((lsizenn (lanetype_Jnn v_Jnn)) == 16) ->
    wf_vbinop_Jnn_M v_Jnn v_M .Q15MULR_SATS
  | vbinop_Jnn_M_case_7 : forall (v_Jnn : Jnn) (v_M : M), 
    ((lsizenn (lanetype_Jnn v_Jnn)) == 16) ->
    wf_vbinop_Jnn_M v_Jnn v_M .RELAXED_Q15MULRS
  | vbinop_Jnn_M_case_8 : forall (v_Jnn : Jnn) (v_M : M) (v_sx : sx), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 32) ->
    wf_vbinop_Jnn_M v_Jnn v_M (.MIN v_sx)
  | vbinop_Jnn_M_case_9 : forall (v_Jnn : Jnn) (v_M : M) (v_sx : sx), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 32) ->
    wf_vbinop_Jnn_M v_Jnn v_M (.MAX v_sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.1-107.43 -/
inductive vbinop_Fnn_M : Type where
  | ADD : vbinop_Fnn_M
  | SUB : vbinop_Fnn_M
  | MUL : vbinop_Fnn_M
  | DIV : vbinop_Fnn_M
  | MIN : vbinop_Fnn_M
  | MAX : vbinop_Fnn_M
  | PMIN : vbinop_Fnn_M
  | PMAX : vbinop_Fnn_M
  | RELAXED_MIN : vbinop_Fnn_M
  | RELAXED_MAX : vbinop_Fnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.1-107.43 -/
inductive vbinop_ : Type where
  | mk_vbinop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vbinop_Jnn_M) : vbinop_
  | mk_vbinop__1 (v_Fnn : Fnn) (v_M : M) (var_x : vbinop_Fnn_M) : vbinop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.8-107.16 -/
inductive wf_vbinop_ : shape -> vbinop_ -> Prop where
  | vbinop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vbinop_Jnn_M), 
    (wf_vbinop_Jnn_M v_Jnn v_M var_x) ->
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) ->
    wf_vbinop_ v_shape (.mk_vbinop__0 v_Jnn v_M var_x)
  | vbinop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_M : M) (var_x : vbinop_Fnn_M), 
    (v_shape == (.X (lanetype_Fnn v_Fnn) (.mk_dim v_M))) ->
    wf_vbinop_ v_shape (.mk_vbinop__1 v_Fnn v_M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.1-107.43 -/
def proj_vbinop__0 : ∀  (var_x : vbinop_) , (Option vbinop_Jnn_M)
  | (.mk_vbinop__0 v_Jnn v_M var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:107.1-107.43 -/
def proj_vbinop__1 : ∀  (var_x : vbinop_) , (Option vbinop_Fnn_M)
  | (.mk_vbinop__1 v_Fnn v_M var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.1-122.44 -/
inductive vternop_Jnn_M : Type where
  | RELAXED_LANESELECT : vternop_Jnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.1-122.44 -/
inductive vternop_Fnn_M : Type where
  | RELAXED_MADD : vternop_Fnn_M
  | RELAXED_NMADD : vternop_Fnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.1-122.44 -/
inductive vternop_ : Type where
  | mk_vternop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vternop_Jnn_M) : vternop_
  | mk_vternop__1 (v_Fnn : Fnn) (v_M : M) (var_x : vternop_Fnn_M) : vternop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.8-122.17 -/
inductive wf_vternop_ : shape -> vternop_ -> Prop where
  | vternop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vternop_Jnn_M), 
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) ->
    wf_vternop_ v_shape (.mk_vternop__0 v_Jnn v_M var_x)
  | vternop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_M : M) (var_x : vternop_Fnn_M), 
    (v_shape == (.X (lanetype_Fnn v_Fnn) (.mk_dim v_M))) ->
    wf_vternop_ v_shape (.mk_vternop__1 v_Fnn v_M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.1-122.44 -/
def proj_vternop__0 : ∀  (var_x : vternop_) , (Option vternop_Jnn_M)
  | (.mk_vternop__0 v_Jnn v_M var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:122.1-122.44 -/
def proj_vternop__1 : ∀  (var_x : vternop_) , (Option vternop_Fnn_M)
  | (.mk_vternop__1 v_Fnn v_M var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:126.1-126.44 -/
inductive vtestop_Jnn_M : Type where
  | ALL_TRUE : vtestop_Jnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:126.1-126.44 -/
inductive vtestop_ : Type where
  | mk_vtestop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vtestop_Jnn_M) : vtestop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:126.8-126.17 -/
inductive wf_vtestop_ : shape -> vtestop_ -> Prop where
  | vtestop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vtestop_Jnn_M), 
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) ->
    wf_vtestop_ v_shape (.mk_vtestop__0 v_Jnn v_M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:126.1-126.44 -/
def proj_vtestop__0 : ∀  (var_x : vtestop_) , vtestop_Jnn_M
  | (.mk_vtestop__0 v_Jnn v_M var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.1-130.43 -/
inductive vrelop_Jnn_M : Type where
  | EQ : vrelop_Jnn_M
  | NE : vrelop_Jnn_M
  | LT (v_sx : sx) : vrelop_Jnn_M
  | GT (v_sx : sx) : vrelop_Jnn_M
  | LE (v_sx : sx) : vrelop_Jnn_M
  | GE (v_sx : sx) : vrelop_Jnn_M
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.8-130.16 -/
inductive wf_vrelop_Jnn_M : Jnn -> M -> vrelop_Jnn_M -> Prop where
  | vrelop_Jnn_M_case_0 : forall (v_Jnn : Jnn) (v_M : M), wf_vrelop_Jnn_M v_Jnn v_M .EQ
  | vrelop_Jnn_M_case_1 : forall (v_Jnn : Jnn) (v_M : M), wf_vrelop_Jnn_M v_Jnn v_M .NE
  | vrelop_Jnn_M_case_2 : forall (v_Jnn : Jnn) (v_M : M) (v_sx : sx), 
    (((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == .S)) ->
    wf_vrelop_Jnn_M v_Jnn v_M (.LT v_sx)
  | vrelop_Jnn_M_case_3 : forall (v_Jnn : Jnn) (v_M : M) (v_sx : sx), 
    (((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == .S)) ->
    wf_vrelop_Jnn_M v_Jnn v_M (.GT v_sx)
  | vrelop_Jnn_M_case_4 : forall (v_Jnn : Jnn) (v_M : M) (v_sx : sx), 
    (((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == .S)) ->
    wf_vrelop_Jnn_M v_Jnn v_M (.LE v_sx)
  | vrelop_Jnn_M_case_5 : forall (v_Jnn : Jnn) (v_M : M) (v_sx : sx), 
    (((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == .S)) ->
    wf_vrelop_Jnn_M v_Jnn v_M (.GE v_sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.1-130.43 -/
inductive vrelop_Fnn_M : Type where
  | EQ : vrelop_Fnn_M
  | NE : vrelop_Fnn_M
  | LT : vrelop_Fnn_M
  | GT : vrelop_Fnn_M
  | LE : vrelop_Fnn_M
  | GE : vrelop_Fnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.1-130.43 -/
inductive vrelop_ : Type where
  | mk_vrelop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vrelop_Jnn_M) : vrelop_
  | mk_vrelop__1 (v_Fnn : Fnn) (v_M : M) (var_x : vrelop_Fnn_M) : vrelop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.8-130.16 -/
inductive wf_vrelop_ : shape -> vrelop_ -> Prop where
  | vrelop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vrelop_Jnn_M), 
    (wf_vrelop_Jnn_M v_Jnn v_M var_x) ->
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) ->
    wf_vrelop_ v_shape (.mk_vrelop__0 v_Jnn v_M var_x)
  | vrelop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_M : M) (var_x : vrelop_Fnn_M), 
    (v_shape == (.X (lanetype_Fnn v_Fnn) (.mk_dim v_M))) ->
    wf_vrelop_ v_shape (.mk_vrelop__1 v_Fnn v_M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.1-130.43 -/
def proj_vrelop__0 : ∀  (var_x : vrelop_) , (Option vrelop_Jnn_M)
  | (.mk_vrelop__0 v_Jnn v_M var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:130.1-130.43 -/
def proj_vrelop__1 : ∀  (var_x : vrelop_) , (Option vrelop_Fnn_M)
  | (.mk_vrelop__1 v_Fnn v_M var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:138.1-138.46 -/
inductive vshiftop_Jnn_M : Type where
  | SHL : vshiftop_Jnn_M
  | SHR (v_sx : sx) : vshiftop_Jnn_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:138.1-138.46 -/
inductive vshiftop_ : Type where
  | mk_vshiftop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vshiftop_Jnn_M) : vshiftop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:138.8-138.18 -/
inductive wf_vshiftop_ : ishape -> vshiftop_ -> Prop where
  | vshiftop__case_0 : forall (v_ishape : ishape) (v_Jnn : Jnn) (v_M : M) (var_x : vshiftop_Jnn_M), 
    (v_ishape == (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)))) ->
    wf_vshiftop_ v_ishape (.mk_vshiftop__0 v_Jnn v_M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:138.1-138.46 -/
def proj_vshiftop__0 : ∀  (var_x : vshiftop_) , vshiftop_Jnn_M
  | (.mk_vshiftop__0 v_Jnn v_M var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:141.1-141.47 -/
inductive vswizzlop_M : Type where
  | SWIZZLE : vswizzlop_M
  | RELAXED_SWIZZLE : vswizzlop_M
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:141.1-141.47 -/
inductive vswizzlop_ : Type where
  | mk_vswizzlop__0 (v_M : M) (var_x : vswizzlop_M) : vswizzlop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:141.8-141.19 -/
inductive wf_vswizzlop_ : bshape -> vswizzlop_ -> Prop where
  | vswizzlop__case_0 : forall (v_bshape : bshape) (v_M : M) (var_x : vswizzlop_M), 
    (v_bshape == (.mk_bshape (.X .I8 (.mk_dim v_M)))) ->
    wf_vswizzlop_ v_bshape (.mk_vswizzlop__0 v_M var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:141.1-141.47 -/
def proj_vswizzlop__0 : ∀  (var_x : vswizzlop_) , vswizzlop_M
  | (.mk_vswizzlop__0 v_M var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.1-144.59 -/
inductive vextunop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTADD_PAIRWISE (v_sx : sx) : vextunop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.8-144.19 -/
inductive wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 : Jnn -> M -> Jnn -> M -> vextunop__Jnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_sx : sx), 
    ((16 <= (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) && (((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) <= 32))) ->
    wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (.EXTADD_PAIRWISE v_sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.1-144.59 -/
inductive vextunop__ : Type where
  | mk_vextunop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2) : vextunop__
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.8-144.19 -/
inductive wf_vextunop__ : ishape -> ishape -> vextunop__ -> Prop where
  | vextunop___case_0 : forall (ishape_1 : ishape) (ishape_2 : ishape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2), 
    (wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ->
    (ishape_1 == (.mk_ishape (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1)))) ->
    (ishape_2 == (.mk_ishape (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2)))) ->
    wf_vextunop__ ishape_1 ishape_2 (.mk_vextunop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:144.1-144.59 -/
def proj_vextunop___0 : ∀  (var_x : vextunop__) , vextunop__Jnn_1_M_1_Jnn_2_M_2
  | (.mk_vextunop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:149.1-149.60 -/
inductive vextbinop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTMUL (v_half : half) (v_sx : sx) : vextbinop__Jnn_1_M_1_Jnn_2_M_2
  | DOTS : vextbinop__Jnn_1_M_1_Jnn_2_M_2
  | RELAXED_DOTS : vextbinop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:149.8-149.20 -/
inductive wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 : Jnn -> M -> Jnn -> M -> vextbinop__Jnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_half : half) (v_sx : sx), 
    (((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) >= 16)) ->
    wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (.EXTMUL v_half v_sx)
  | vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M), 
    (((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) == 32)) ->
    wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 .DOTS
  | vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M), 
    (((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) == 16)) ->
    wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 .RELAXED_DOTS

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:149.1-149.60 -/
inductive vextbinop__ : Type where
  | mk_vextbinop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextbinop__Jnn_1_M_1_Jnn_2_M_2) : vextbinop__
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:149.8-149.20 -/
inductive wf_vextbinop__ : ishape -> ishape -> vextbinop__ -> Prop where
  | vextbinop___case_0 : forall (ishape_1 : ishape) (ishape_2 : ishape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextbinop__Jnn_1_M_1_Jnn_2_M_2), 
    (wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ->
    (ishape_1 == (.mk_ishape (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1)))) ->
    (ishape_2 == (.mk_ishape (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2)))) ->
    wf_vextbinop__ ishape_1 ishape_2 (.mk_vextbinop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:149.1-149.60 -/
def proj_vextbinop___0 : ∀  (var_x : vextbinop__) , vextbinop__Jnn_1_M_1_Jnn_2_M_2
  | (.mk_vextbinop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:158.1-158.61 -/
inductive vextternop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | RELAXED_DOT_ADDS : vextternop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:158.8-158.21 -/
inductive wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 : Jnn -> M -> Jnn -> M -> vextternop__Jnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M), 
    (((4 * (lsizenn1 (lanetype_Jnn Jnn_1))) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) == 32)) ->
    wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 .RELAXED_DOT_ADDS

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:158.1-158.61 -/
inductive vextternop__ : Type where
  | mk_vextternop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextternop__Jnn_1_M_1_Jnn_2_M_2) : vextternop__
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:158.8-158.21 -/
inductive wf_vextternop__ : ishape -> ishape -> vextternop__ -> Prop where
  | vextternop___case_0 : forall (ishape_1 : ishape) (ishape_2 : ishape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextternop__Jnn_1_M_1_Jnn_2_M_2), 
    (wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ->
    (ishape_1 == (.mk_ishape (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1)))) ->
    (ishape_2 == (.mk_ishape (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2)))) ->
    wf_vextternop__ ishape_1 ishape_2 (.mk_vextternop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:158.1-158.61 -/
def proj_vextternop___0 : ∀  (var_x : vextternop__) , vextternop__Jnn_1_M_1_Jnn_2_M_2
  | (.mk_vextternop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTEND (v_half : half) (v_sx : sx) : vcvtop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 : Jnn -> M -> Jnn -> M -> vcvtop__Jnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_half : half) (v_sx : sx), 
    ((lsizenn2 (lanetype_Jnn Jnn_2)) == (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) ->
    wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (.EXTEND v_half v_sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__Jnn_1_M_1_Fnn_2_M_2 : Type where
  | CONVERT (half_opt : (Option half)) (v_sx : sx) : vcvtop__Jnn_1_M_1_Fnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 : Jnn -> M -> Fnn -> M -> vcvtop__Jnn_1_M_1_Fnn_2_M_2 -> Prop where
  | vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 : forall (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (half_opt : (Option half)) (v_sx : sx), 
    (((((sizenn2 (numtype_Fnn Fnn_2)) == (lsizenn1 (lanetype_Jnn Jnn_1))) && ((lsizenn1 (lanetype_Jnn Jnn_1)) == 32)) && (half_opt == none)) || (((sizenn2 (numtype_Fnn Fnn_2)) == (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) && (half_opt == (some .LOW)))) ->
    wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 Jnn_1 M_1 Fnn_2 M_2 (.CONVERT half_opt v_sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__Fnn_1_M_1_Jnn_2_M_2 : Type where
  | TRUNC_SAT (v_sx : sx) (zero_opt : (Option zero)) : vcvtop__Fnn_1_M_1_Jnn_2_M_2
  | RELAXED_TRUNC (v_sx : sx) (zero_opt : (Option zero)) : vcvtop__Fnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 : Fnn -> M -> Jnn -> M -> vcvtop__Fnn_1_M_1_Jnn_2_M_2 -> Prop where
  | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 : forall (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_sx : sx) (zero_opt : (Option zero)), 
    (((((sizenn1 (numtype_Fnn Fnn_1)) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) == 32)) && (zero_opt == none)) || (((sizenn1 (numtype_Fnn Fnn_1)) == (2 * (lsizenn2 (lanetype_Jnn Jnn_2)))) && (zero_opt == (some .ZERO)))) ->
    wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 (.TRUNC_SAT v_sx zero_opt)
  | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_1 : forall (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_sx : sx) (zero_opt : (Option zero)), 
    (((((sizenn1 (numtype_Fnn Fnn_1)) == (lsizenn2 (lanetype_Jnn Jnn_2))) && ((lsizenn2 (lanetype_Jnn Jnn_2)) == 32)) && (zero_opt == none)) || (((sizenn1 (numtype_Fnn Fnn_1)) == (2 * (lsizenn2 (lanetype_Jnn Jnn_2)))) && (zero_opt == (some .ZERO)))) ->
    wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 (.RELAXED_TRUNC v_sx zero_opt)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__Fnn_1_M_1_Fnn_2_M_2 : Type where
  | DEMOTE (v_zero : zero) : vcvtop__Fnn_1_M_1_Fnn_2_M_2
  | PROMOTELOW : vcvtop__Fnn_1_M_1_Fnn_2_M_2
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 : Fnn -> M -> Fnn -> M -> vcvtop__Fnn_1_M_1_Fnn_2_M_2 -> Prop where
  | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 : forall (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (v_zero : zero), 
    ((sizenn1 (numtype_Fnn Fnn_1)) == (2 * (sizenn2 (numtype_Fnn Fnn_2)))) ->
    wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 (.DEMOTE v_zero)
  | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 : forall (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M), 
    ((2 * (sizenn1 (numtype_Fnn Fnn_1))) == (sizenn2 (numtype_Fnn Fnn_2))) ->
    wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 .PROMOTELOW

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
inductive vcvtop__ : Type where
  | mk_vcvtop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Jnn_2_M_2) : vcvtop__
  | mk_vcvtop___1 (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Fnn_2_M_2) : vcvtop__
  | mk_vcvtop___2 (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Jnn_2_M_2) : vcvtop__
  | mk_vcvtop___3 (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Fnn_2_M_2) : vcvtop__
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.8-163.17 -/
inductive wf_vcvtop__ : shape -> shape -> vcvtop__ -> Prop where
  | vcvtop___case_0 : forall (shape_1 : shape) (shape_2 : shape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Jnn_2_M_2), 
    (wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x) ->
    (shape_1 == (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1))) ->
    (shape_2 == (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2))) ->
    wf_vcvtop__ shape_1 shape_2 (.mk_vcvtop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)
  | vcvtop___case_1 : forall (shape_1 : shape) (shape_2 : shape) (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Fnn_2_M_2), 
    (wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 Jnn_1 M_1 Fnn_2 M_2 var_x) ->
    (shape_1 == (.X (lanetype_Jnn Jnn_1) (.mk_dim M_1))) ->
    (shape_2 == (.X (lanetype_Fnn Fnn_2) (.mk_dim M_2))) ->
    wf_vcvtop__ shape_1 shape_2 (.mk_vcvtop___1 Jnn_1 M_1 Fnn_2 M_2 var_x)
  | vcvtop___case_2 : forall (shape_1 : shape) (shape_2 : shape) (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Jnn_2_M_2), 
    (wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 var_x) ->
    (shape_1 == (.X (lanetype_Fnn Fnn_1) (.mk_dim M_1))) ->
    (shape_2 == (.X (lanetype_Jnn Jnn_2) (.mk_dim M_2))) ->
    wf_vcvtop__ shape_1 shape_2 (.mk_vcvtop___2 Fnn_1 M_1 Jnn_2 M_2 var_x)
  | vcvtop___case_3 : forall (shape_1 : shape) (shape_2 : shape) (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Fnn_2_M_2), 
    (wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 var_x) ->
    (shape_1 == (.X (lanetype_Fnn Fnn_1) (.mk_dim M_1))) ->
    (shape_2 == (.X (lanetype_Fnn Fnn_2) (.mk_dim M_2))) ->
    wf_vcvtop__ shape_1 shape_2 (.mk_vcvtop___3 Fnn_1 M_1 Fnn_2 M_2 var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
def proj_vcvtop___0 : ∀  (var_x : vcvtop__) , (Option vcvtop__Jnn_1_M_1_Jnn_2_M_2)
  | (.mk_vcvtop___0 Jnn_1 M_1 Jnn_2 M_2 var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
def proj_vcvtop___1 : ∀  (var_x : vcvtop__) , (Option vcvtop__Jnn_1_M_1_Fnn_2_M_2)
  | (.mk_vcvtop___1 Jnn_1 M_1 Fnn_2 M_2 var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
def proj_vcvtop___2 : ∀  (var_x : vcvtop__) , (Option vcvtop__Fnn_1_M_1_Jnn_2_M_2)
  | (.mk_vcvtop___2 Fnn_1 M_1 Jnn_2 M_2 var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:163.1-163.55 -/
def proj_vcvtop___3 : ∀  (var_x : vcvtop__) , (Option vcvtop__Fnn_1_M_1_Fnn_2_M_2)
  | (.mk_vcvtop___3 Fnn_1 M_1 Fnn_2 M_2 var_x) =>
    (some var_x)
  | var_x =>
    none


/- Record Creation Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:187.1-187.69 -/
structure memarg where MKmemarg ::
  ALIGN : u32
  OFFSET : u64
deriving Inhabited, BEq

def _append_memarg (arg1 arg2 : (memarg)) : memarg where
  ALIGN := arg1.ALIGN /- FIXME - Non-trivial append -/
  OFFSET := arg1.OFFSET /- FIXME - Non-trivial append -/
instance : Append memarg where
  append arg1 arg2 := _append_memarg arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:187.8-187.14 -/
inductive wf_memarg : memarg -> Prop where
  | memarg_case_ : forall (var_0 : u32) (var_1 : u64), 
    (wf_uN 32 var_0) ->
    (wf_uN 64 var_1) ->
    wf_memarg { ALIGN := var_0, OFFSET := var_1 }

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.1-191.24 -/
inductive loadop_Inn : Type where
  | mk_loadop_Inn (v_sz : sz) (v_sx : sx) : loadop_Inn
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.8-191.16 -/
inductive wf_loadop_Inn : Inn -> loadop_Inn -> Prop where
  | loadop_Inn_case_0 : forall (v_Inn : Inn) (v_sz : sz) (v_sx : sx), 
    (wf_sz v_sz) ->
    ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) ->
    wf_loadop_Inn v_Inn (.mk_loadop_Inn v_sz v_sx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.1-191.24 -/
inductive loadop_ : Type where
  | mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.8-191.16 -/
inductive wf_loadop_ : numtype -> loadop_ -> Prop where
  | loadop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : loadop_Inn), 
    (wf_loadop_Inn v_Inn var_x) ->
    (v_numtype == (numtype_addrtype v_Inn)) ->
    wf_loadop_ v_numtype (.mk_loadop__0 v_Inn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:191.1-191.24 -/
def proj_loadop__0 : ∀  (var_x : loadop_) , loadop_Inn
  | (.mk_loadop__0 v_Inn var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.1-194.25 -/
inductive storeop_Inn : Type where
  | mk_storeop_Inn (v_sz : sz) : storeop_Inn
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.8-194.17 -/
inductive wf_storeop_Inn : Inn -> storeop_Inn -> Prop where
  | storeop_Inn_case_0 : forall (v_Inn : Inn) (v_sz : sz), 
    (wf_sz v_sz) ->
    ((proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn))) ->
    wf_storeop_Inn v_Inn (.mk_storeop_Inn v_sz)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.1-194.25 -/
inductive storeop_ : Type where
  | mk_storeop__0 (v_Inn : Inn) (var_x : storeop_Inn) : storeop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.8-194.17 -/
inductive wf_storeop_ : numtype -> storeop_ -> Prop where
  | storeop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : storeop_Inn), 
    (wf_storeop_Inn v_Inn var_x) ->
    (v_numtype == (numtype_addrtype v_Inn)) ->
    wf_storeop_ v_numtype (.mk_storeop__0 v_Inn var_x)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:194.1-194.25 -/
def proj_storeop__0 : ∀  (var_x : storeop_) , storeop_Inn
  | (.mk_storeop__0 v_Inn var_x) =>
    var_x


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:197.1-200.59 -/
inductive vloadop_ : Type where
  | SHAPEX_ (v_sz : sz) (v_M : M) (v_sx : sx) : vloadop_
  | SPLAT (v_sz : sz) : vloadop_
  | ZERO (v_sz : sz) : vloadop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:197.8-197.17 -/
inductive wf_vloadop_ : vectype -> vloadop_ -> Prop where
  | vloadop__case_0 : forall (v_vectype : vectype) (v_sz : sz) (v_M : M) (v_sx : sx), 
    (wf_sz v_sz) ->
    ((((proj_sz_0 v_sz) * v_M) : Nat) == (((vsize v_vectype) : Nat) / (2 : Nat))) ->
    wf_vloadop_ v_vectype (.SHAPEX_ v_sz v_M v_sx)
  | vloadop__case_1 : forall (v_vectype : vectype) (v_sz : sz), 
    (wf_sz v_sz) ->
    wf_vloadop_ v_vectype (.SPLAT v_sz)
  | vloadop__case_2 : forall (v_vectype : vectype) (v_sz : sz), 
    (wf_sz v_sz) ->
    ((proj_sz_0 v_sz) >= 32) ->
    wf_vloadop_ v_vectype (.ZERO v_sz)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:205.1-207.17 -/
inductive blocktype : Type where
  | _RESULT (valtype_opt : (Option valtype)) : blocktype
  | _IDX (v_typeidx : typeidx) : blocktype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:205.8-205.17 -/
inductive wf_blocktype : blocktype -> Prop where
  | blocktype_case_0 : forall (valtype_opt : (Option valtype)), 
    Forall (fun (v_valtype : valtype) => (wf_valtype v_valtype)) (Option.toList valtype_opt) ->
    wf_blocktype (._RESULT valtype_opt)
  | blocktype_case_1 : forall (v_typeidx : typeidx), 
    (wf_uN 32 v_typeidx) ->
    wf_blocktype (._IDX v_typeidx)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:7.1-7.39 -/
abbrev addr : Type := Nat

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:16.1-16.51 -/
abbrev arrayaddr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:17.1-17.53 -/
abbrev exnaddr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:12.1-12.53 -/
abbrev funcaddr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:18.1-18.49 -/
abbrev hostaddr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:15.1-15.56 -/
abbrev structaddr : Type := addr

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:35.1-42.23 -/
/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:35.1-42.23 -/
inductive addrref : Type where
  | REF_I31_NUM (v_u31 : u31) : addrref
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : addrref
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : addrref
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : addrref
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : addrref
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : addrref
  | REF_EXTERN (v_addrref : addrref) : addrref
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:255.1-259.27 -/
inductive «catch» : Type where
  | CATCH (v_tagidx : tagidx) (v_labelidx : labelidx) : «catch»
  | CATCH_REF (v_tagidx : tagidx) (v_labelidx : labelidx) : «catch»
  | CATCH_ALL (v_labelidx : labelidx) : «catch»
  | CATCH_ALL_REF (v_labelidx : labelidx) : «catch»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:255.8-255.13 -/
inductive wf_catch : «catch» -> Prop where
  | catch_case_0 : forall (v_tagidx : tagidx) (v_labelidx : labelidx), 
    (wf_uN 32 v_tagidx) ->
    (wf_uN 32 v_labelidx) ->
    wf_catch (.CATCH v_tagidx v_labelidx)
  | catch_case_1 : forall (v_tagidx : tagidx) (v_labelidx : labelidx), 
    (wf_uN 32 v_tagidx) ->
    (wf_uN 32 v_labelidx) ->
    wf_catch (.CATCH_REF v_tagidx v_labelidx)
  | catch_case_2 : forall (v_labelidx : labelidx), 
    (wf_uN 32 v_labelidx) ->
    wf_catch (.CATCH_ALL v_labelidx)
  | catch_case_3 : forall (v_labelidx : labelidx), 
    (wf_uN 32 v_labelidx) ->
    wf_catch (.CATCH_ALL_REF v_labelidx)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:13.1-13.49 -/
abbrev dataaddr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:14.1-14.49 -/
abbrev elemaddr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:9.1-9.53 -/
abbrev globaladdr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:10.1-10.50 -/
abbrev memaddr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:11.1-11.51 -/
abbrev tableaddr : Type := addr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:8.1-8.47 -/
abbrev tagaddr : Type := addr

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:20.1-21.84 -/
inductive externaddr : Type where
  | TAG (v_tagaddr : tagaddr) : externaddr
  | GLOBAL (v_globaladdr : globaladdr) : externaddr
  | MEM (v_memaddr : memaddr) : externaddr
  | TABLE (v_tableaddr : tableaddr) : externaddr
  | FUNC (v_funcaddr : funcaddr) : externaddr
deriving Inhabited, BEq


/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:84.1-85.33 -/
structure exportinst where MKexportinst ::
  NAME : name
  ADDR : externaddr
deriving Inhabited, BEq

def _append_exportinst (arg1 arg2 : (exportinst)) : exportinst where
  NAME := arg1.NAME /- FIXME - Non-trivial append -/
  ADDR := arg1.ADDR /- FIXME - Non-trivial append -/
instance : Append exportinst where
  append arg1 arg2 := _append_exportinst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:84.8-84.18 -/
inductive wf_exportinst : exportinst -> Prop where
  | exportinst_case_ : forall (var_0 : name) (var_1 : externaddr), 
    (wf_name var_0) ->
    wf_exportinst { NAME := var_0, ADDR := var_1 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:104.1-113.26 -/
structure moduleinst where MKmoduleinst ::
  TYPES : (List deftype)
  TAGS : (List tagaddr)
  GLOBALS : (List globaladdr)
  MEMS : (List memaddr)
  TABLES : (List tableaddr)
  FUNCS : (List funcaddr)
  DATAS : (List dataaddr)
  ELEMS : (List elemaddr)
  EXPORTS : (List exportinst)
deriving Inhabited, BEq

def _append_moduleinst (arg1 arg2 : (moduleinst)) : moduleinst where
  TYPES := arg1.TYPES ++ arg2.TYPES
  TAGS := arg1.TAGS ++ arg2.TAGS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  MEMS := arg1.MEMS ++ arg2.MEMS
  TABLES := arg1.TABLES ++ arg2.TABLES
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  DATAS := arg1.DATAS ++ arg2.DATAS
  ELEMS := arg1.ELEMS ++ arg2.ELEMS
  EXPORTS := arg1.EXPORTS ++ arg2.EXPORTS
instance : Append moduleinst where
  append arg1 arg2 := _append_moduleinst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:104.8-104.18 -/
inductive wf_moduleinst : moduleinst -> Prop where
  | moduleinst_case_ : forall (var_0 : (List deftype)) (var_1 : (List tagaddr)) (var_2 : (List globaladdr)) (var_3 : (List memaddr)) (var_4 : (List tableaddr)) (var_5 : (List funcaddr)) (var_6 : (List dataaddr)) (var_7 : (List elemaddr)) (var_8 : (List exportinst)), 
    Forall (fun (var_8 : exportinst) => (wf_exportinst var_8)) var_8 ->
    wf_moduleinst { TYPES := var_0, TAGS := var_1, GLOBALS := var_2, MEMS := var_3, TABLES := var_4, FUNCS := var_5, DATAS := var_6, ELEMS := var_7, EXPORTS := var_8 }

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:48.1-49.20 -/
inductive val : Type where
  | CONST (v_numtype : numtype) (v_num_ : num_) : val
  | VCONST (v_vectype : vectype) (v_vec_ : vec_) : val
  | REF_NULL (v_heaptype : heaptype) : val
  | REF_I31_NUM (v_u31 : u31) : val
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : val
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : val
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : val
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : val
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : val
  | REF_EXTERN (v_addrref : addrref) : val
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:48.8-48.11 -/
inductive wf_val : val -> Prop where
  | val_case_0 : forall (v_numtype : numtype) (v_num_ : num_), 
    (wf_num_ v_numtype v_num_) ->
    wf_val (.CONST v_numtype v_num_)
  | val_case_1 : forall (v_vectype : vectype) (v_vec_ : vec_), 
    (wf_uN (vsize v_vectype) v_vec_) ->
    wf_val (.VCONST v_vectype v_vec_)
  | val_case_2 : forall (v_heaptype : heaptype), 
    (wf_heaptype v_heaptype) ->
    wf_val (.REF_NULL v_heaptype)
  | val_case_3 : forall (v_u31 : u31), 
    (wf_uN 31 v_u31) ->
    wf_val (.REF_I31_NUM v_u31)
  | val_case_4 : forall (v_structaddr : structaddr), wf_val (.REF_STRUCT_ADDR v_structaddr)
  | val_case_5 : forall (v_arrayaddr : arrayaddr), wf_val (.REF_ARRAY_ADDR v_arrayaddr)
  | val_case_6 : forall (v_funcaddr : funcaddr), wf_val (.REF_FUNC_ADDR v_funcaddr)
  | val_case_7 : forall (v_exnaddr : exnaddr), wf_val (.REF_EXN_ADDR v_exnaddr)
  | val_case_8 : forall (v_hostaddr : hostaddr), wf_val (.REF_HOST_ADDR v_hostaddr)
  | val_case_9 : forall (v_addrref : addrref), 
    (wf_addrref v_addrref) ->
    wf_val (.REF_EXTERN v_addrref)

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:130.1-131.40 -/
structure frame where MKframe ::
  LOCALS : (List (Option val))
  MODULE : moduleinst
deriving Inhabited, BEq

def _append_frame (arg1 arg2 : (frame)) : frame where
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
  MODULE := arg1.MODULE ++ arg2.MODULE
instance : Append frame where
  append arg1 arg2 := _append_frame arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:130.8-130.13 -/
inductive wf_frame : frame -> Prop where
  | frame_case_ : forall (var_0 : (List (Option val))) (var_1 : moduleinst), 
    Forall (fun (var_0 : (Option val)) => Forall (fun (var_0 : val) => (wf_val var_0)) (Option.toList var_0)) var_0 ->
    (wf_moduleinst var_1) ->
    wf_frame { LOCALS := var_0, MODULE := var_1 }

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 -/
/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:136.1-142.9 -/
inductive instr : Type where
  | NOP : instr
  | UNREACHABLE : instr
  | DROP : instr
  | SELECT (valtype_lst_opt : (Option (List valtype))) : instr
  | BLOCK (v_blocktype : blocktype) (instr_lst : (List instr)) : instr
  | LOOP (v_blocktype : blocktype) (instr_lst : (List instr)) : instr
  | IFELSE (v_blocktype : blocktype) (instr_lst : (List instr)) (_ : (List instr)) : instr
  | BR (v_labelidx : labelidx) : instr
  | BR_IF (v_labelidx : labelidx) : instr
  | BR_TABLE (labelidx_lst : (List labelidx)) (_ : labelidx) : instr
  | BR_ON_NULL (v_labelidx : labelidx) : instr
  | BR_ON_NON_NULL (v_labelidx : labelidx) : instr
  | BR_ON_CAST (v_labelidx : labelidx) (v_reftype : reftype) (_ : reftype) : instr
  | BR_ON_CAST_FAIL (v_labelidx : labelidx) (v_reftype : reftype) (_ : reftype) : instr
  | CALL (v_funcidx : funcidx) : instr
  | CALL_REF (v_typeuse : typeuse) : instr
  | CALL_INDIRECT (v_tableidx : tableidx) (v_typeuse : typeuse) : instr
  | RETURN : instr
  | RETURN_CALL (v_funcidx : funcidx) : instr
  | RETURN_CALL_REF (v_typeuse : typeuse) : instr
  | RETURN_CALL_INDIRECT (v_tableidx : tableidx) (v_typeuse : typeuse) : instr
  | THROW (v_tagidx : tagidx) : instr
  | THROW_REF : instr
  | TRY_TABLE (v_blocktype : blocktype) (v_list : (list «catch»)) (instr_lst : (List instr)) : instr
  | LOCAL_GET (v_localidx : localidx) : instr
  | LOCAL_SET (v_localidx : localidx) : instr
  | LOCAL_TEE (v_localidx : localidx) : instr
  | GLOBAL_GET (v_globalidx : globalidx) : instr
  | GLOBAL_SET (v_globalidx : globalidx) : instr
  | TABLE_GET (v_tableidx : tableidx) : instr
  | TABLE_SET (v_tableidx : tableidx) : instr
  | TABLE_SIZE (v_tableidx : tableidx) : instr
  | TABLE_GROW (v_tableidx : tableidx) : instr
  | TABLE_FILL (v_tableidx : tableidx) : instr
  | TABLE_COPY (v_tableidx : tableidx) (_ : tableidx) : instr
  | TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : instr
  | ELEM_DROP (v_elemidx : elemidx) : instr
  | LOAD (v_numtype : numtype) (loadop__opt : (Option loadop_)) (v_memidx : memidx) (v_memarg : memarg) : instr
  | STORE (v_numtype : numtype) (storeop__opt : (Option storeop_)) (v_memidx : memidx) (v_memarg : memarg) : instr
  | VLOAD (v_vectype : vectype) (vloadop__opt : (Option vloadop_)) (v_memidx : memidx) (v_memarg : memarg) : instr
  | VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memidx : memidx) (v_memarg : memarg) (v_laneidx : laneidx) : instr
  | VSTORE (v_vectype : vectype) (v_memidx : memidx) (v_memarg : memarg) : instr
  | VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memidx : memidx) (v_memarg : memarg) (v_laneidx : laneidx) : instr
  | MEMORY_SIZE (v_memidx : memidx) : instr
  | MEMORY_GROW (v_memidx : memidx) : instr
  | MEMORY_FILL (v_memidx : memidx) : instr
  | MEMORY_COPY (v_memidx : memidx) (_ : memidx) : instr
  | MEMORY_INIT (v_memidx : memidx) (v_dataidx : dataidx) : instr
  | DATA_DROP (v_dataidx : dataidx) : instr
  | REF_NULL (v_heaptype : heaptype) : instr
  | REF_IS_NULL : instr
  | REF_AS_NON_NULL : instr
  | REF_EQ : instr
  | REF_TEST (v_reftype : reftype) : instr
  | REF_CAST (v_reftype : reftype) : instr
  | REF_FUNC (v_funcidx : funcidx) : instr
  | REF_I31 : instr
  | I31_GET (v_sx : sx) : instr
  | STRUCT_NEW (v_typeidx : typeidx) : instr
  | STRUCT_NEW_DEFAULT (v_typeidx : typeidx) : instr
  | STRUCT_GET (sx_opt : (Option sx)) (v_typeidx : typeidx) (v_u32 : u32) : instr
  | STRUCT_SET (v_typeidx : typeidx) (v_u32 : u32) : instr
  | ARRAY_NEW (v_typeidx : typeidx) : instr
  | ARRAY_NEW_DEFAULT (v_typeidx : typeidx) : instr
  | ARRAY_NEW_FIXED (v_typeidx : typeidx) (v_u32 : u32) : instr
  | ARRAY_NEW_DATA (v_typeidx : typeidx) (v_dataidx : dataidx) : instr
  | ARRAY_NEW_ELEM (v_typeidx : typeidx) (v_elemidx : elemidx) : instr
  | ARRAY_GET (sx_opt : (Option sx)) (v_typeidx : typeidx) : instr
  | ARRAY_SET (v_typeidx : typeidx) : instr
  | ARRAY_LEN : instr
  | ARRAY_FILL (v_typeidx : typeidx) : instr
  | ARRAY_COPY (v_typeidx : typeidx) (_ : typeidx) : instr
  | ARRAY_INIT_DATA (v_typeidx : typeidx) (v_dataidx : dataidx) : instr
  | ARRAY_INIT_ELEM (v_typeidx : typeidx) (v_elemidx : elemidx) : instr
  | EXTERN_CONVERT_ANY : instr
  | ANY_CONVERT_EXTERN : instr
  | CONST (v_numtype : numtype) (v_num_ : num_) : instr
  | UNOP (v_numtype : numtype) (v_unop_ : unop_) : instr
  | BINOP (v_numtype : numtype) (v_binop_ : binop_) : instr
  | TESTOP (v_numtype : numtype) (v_testop_ : testop_) : instr
  | RELOP (v_numtype : numtype) (v_relop_ : relop_) : instr
  | CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop__ : cvtop__) : instr
  | VCONST (v_vectype : vectype) (v_vec_ : vec_) : instr
  | VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : instr
  | VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : instr
  | VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : instr
  | VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : instr
  | VUNOP (v_shape : shape) (v_vunop_ : vunop_) : instr
  | VBINOP (v_shape : shape) (v_vbinop_ : vbinop_) : instr
  | VTERNOP (v_shape : shape) (v_vternop_ : vternop_) : instr
  | VTESTOP (v_shape : shape) (v_vtestop_ : vtestop_) : instr
  | VRELOP (v_shape : shape) (v_vrelop_ : vrelop_) : instr
  | VSHIFTOP (v_ishape : ishape) (v_vshiftop_ : vshiftop_) : instr
  | VBITMASK (v_ishape : ishape) : instr
  | VSWIZZLOP (v_bshape : bshape) (v_vswizzlop_ : vswizzlop_) : instr
  | VSHUFFLE (v_bshape : bshape) (laneidx_lst : (List laneidx)) : instr
  | VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop__ : vextunop__) : instr
  | VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop__ : vextbinop__) : instr
  | VEXTTERNOP (ishape_1 : ishape) (ishape_2 : ishape) (v_vextternop__ : vextternop__) : instr
  | VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : instr
  | VCVTOP (shape_1 : shape) (shape_2 : shape) (v_vcvtop__ : vcvtop__) : instr
  | VSPLAT (v_shape : shape) : instr
  | VEXTRACT_LANE (v_shape : shape) (sx_opt : (Option sx)) (v_laneidx : laneidx) : instr
  | VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : instr
  | REF_I31_NUM (v_u31 : u31) : instr
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : instr
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : instr
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : instr
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : instr
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : instr
  | REF_EXTERN (v_addrref : addrref) : instr
  | LABEL_ (v_n : n) (instr_lst : (List instr)) (_ : (List instr)) : instr
  | FRAME_ (v_n : n) (v_frame : frame) (instr_lst : (List instr)) : instr
  | HANDLER_ (v_n : n) (catch_lst : (List «catch»)) (instr_lst : (List instr)) : instr
  | TRAP : instr
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def instr_addrref : ∀  (var_0 : addrref) , instr
  | (.REF_I31_NUM x0) =>
    (.REF_I31_NUM x0)
  | (.REF_STRUCT_ADDR x0) =>
    (.REF_STRUCT_ADDR x0)
  | (.REF_ARRAY_ADDR x0) =>
    (.REF_ARRAY_ADDR x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_EXN_ADDR x0) =>
    (.REF_EXN_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)
  | (.REF_EXTERN x0) =>
    (.REF_EXTERN x0)


/- Auxiliary Definition at:  -/
def instr_val : ∀  (var_0 : val) , instr
  | (.CONST x0 x1) =>
    (.CONST x0 x1)
  | (.VCONST x0 x1) =>
    (.VCONST x0 x1)
  | (.REF_NULL x0) =>
    (.REF_NULL x0)
  | (.REF_I31_NUM x0) =>
    (.REF_I31_NUM x0)
  | (.REF_STRUCT_ADDR x0) =>
    (.REF_STRUCT_ADDR x0)
  | (.REF_ARRAY_ADDR x0) =>
    (.REF_ARRAY_ADDR x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_EXN_ADDR x0) =>
    (.REF_EXN_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)
  | (.REF_EXTERN x0) =>
    (.REF_EXTERN x0)


/- Type Alias Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:392.1-393.9 -/
abbrev expr : Type := (List instr)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:404.1-404.35 -/
def memarg0 : memarg := { ALIGN := (.mk_uN 0), OFFSET := (.mk_uN 0) }

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:407.1-407.69 -/
def const : ∀  (v_consttype : consttype) (v_lit_ : lit_) , instr
  | .I32, (.mk_lit__0 .I32 c) =>
    (.CONST .I32 c)
  | .I64, (.mk_lit__0 .I64 c) =>
    (.CONST .I64 c)
  | .F32, (.mk_lit__0 .F32 c) =>
    (.CONST .F32 c)
  | .F64, (.mk_lit__0 .F64 c) =>
    (.CONST .F64 c)
  | .V128, (.mk_lit__1 .V128 c) =>
    (.VCONST .V128 c)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:414.1-414.30 -/
def free_shape : ∀  (v_shape : shape) , free
  | (.X v_lanetype v_dim) =>
    (free_lanetype v_lanetype)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:415.6-415.21 -/
inductive fun_free_blocktype : blocktype -> free -> Prop where
  | fun_free_blocktype_case_0 : forall (valtype_opt : (Option valtype)) (var_0_opt : (Option free)), 
    ((var_0_opt == none) <-> (valtype_opt == none)) ->
    Forall₂ (fun (var_0 : free) (v_valtype : valtype) => (fun_free_valtype v_valtype var_0)) (Option.toList var_0_opt) (Option.toList valtype_opt) ->
    fun_free_blocktype (._RESULT valtype_opt) (free_opt var_0_opt)
  | fun_free_blocktype_case_1 : forall (v_typeidx : uN), fun_free_blocktype (._IDX v_typeidx) (free_typeidx v_typeidx)

/- Recursive Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:572.1-572.44 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:572.6-572.22 -/
inductive fun_shift_labelidxs : (List labelidx) -> (List labelidx) -> Prop where
  | fun_shift_labelidxs_case_0 : fun_shift_labelidxs [] []
  | fun_shift_labelidxs_case_1 : forall (labelidx'_lst : (List labelidx)) (var_0 : (List labelidx)), 
    (fun_shift_labelidxs labelidx'_lst var_0) ->
    fun_shift_labelidxs ([(.mk_uN 0)] ++ labelidx'_lst) var_0
  | fun_shift_labelidxs_case_2 : forall (v_labelidx : uN) (labelidx'_lst : (List labelidx)) (var_0 : (List labelidx)), 
    (fun_shift_labelidxs labelidx'_lst var_0) ->
    fun_shift_labelidxs ([v_labelidx] ++ labelidx'_lst) ([(.mk_uN ((((proj_uN_0 v_labelidx) : Nat) - (1 : Nat)) : Nat))] ++ var_0)

/- Recursive Definitions at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:417.1-418.31 -/
mutual
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:417.6-417.17 -/
inductive fun_free_instr : instr -> free -> Prop where
  | fun_free_instr_case_0 : fun_free_instr .NOP { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_1 : fun_free_instr .UNREACHABLE { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_2 : fun_free_instr .DROP { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_3 : forall (valtype_lst_opt : (Option (List valtype))) (var_1_lst_opt : (Option (List free))) (var_0_opt : (Option free)), 
    ((var_1_lst_opt == none) <-> (valtype_lst_opt == none)) ->
    Forall₂ (fun (var_1_lst : (List free)) (valtype_lst : (List valtype)) => ((List.length var_1_lst) == (List.length valtype_lst))) (Option.toList var_1_lst_opt) (Option.toList valtype_lst_opt) ->
    Forall₂ (fun (var_1_lst : (List free)) (valtype_lst : (List valtype)) => Forall₂ (fun (var_1 : free) (v_valtype : valtype) => (fun_free_valtype v_valtype var_1)) var_1_lst valtype_lst) (Option.toList var_1_lst_opt) (Option.toList valtype_lst_opt) ->
    ((var_1_lst_opt == none) <-> (var_0_opt == none)) ->
    Forall₂ (fun (var_1_lst : (List free)) (var_0 : free) => (fun_free_list var_1_lst var_0)) (Option.toList var_1_lst_opt) (Option.toList var_0_opt) ->
    fun_free_instr (.SELECT valtype_lst_opt) (free_opt var_0_opt)
  | fun_free_instr_case_4 : forall (v_blocktype : blocktype) (instr_lst : (List instr)) (var_1 : free) (var_0 : free), 
    (fun_free_block instr_lst var_1) ->
    (fun_free_blocktype v_blocktype var_0) ->
    fun_free_instr (.BLOCK v_blocktype instr_lst) (var_0 ++ var_1)
  | fun_free_instr_case_5 : forall (v_blocktype : blocktype) (instr_lst : (List instr)) (var_1 : free) (var_0 : free), 
    (fun_free_block instr_lst var_1) ->
    (fun_free_blocktype v_blocktype var_0) ->
    fun_free_instr (.LOOP v_blocktype instr_lst) (var_0 ++ var_1)
  | fun_free_instr_case_6 : forall (v_blocktype : blocktype) (instr_1_lst : (List instr)) (instr_2_lst : (List instr)) (var_2 : free) (var_1 : free) (var_0 : free), 
    (fun_free_block instr_2_lst var_2) ->
    (fun_free_block instr_1_lst var_1) ->
    (fun_free_blocktype v_blocktype var_0) ->
    fun_free_instr (.IFELSE v_blocktype instr_1_lst instr_2_lst) ((var_0 ++ var_1) ++ var_2)
  | fun_free_instr_case_7 : forall (v_labelidx : uN), fun_free_instr (.BR v_labelidx) (free_labelidx v_labelidx)
  | fun_free_instr_case_8 : forall (v_labelidx : uN), fun_free_instr (.BR_IF v_labelidx) (free_labelidx v_labelidx)
  | fun_free_instr_case_9 : forall (labelidx_lst : (List labelidx)) (labelidx' : uN) (var_0 : free), 
    (fun_free_list (List.map (fun (v_labelidx : labelidx) => (free_labelidx v_labelidx)) labelidx_lst) var_0) ->
    fun_free_instr (.BR_TABLE labelidx_lst labelidx') (var_0 ++ (free_labelidx labelidx'))
  | fun_free_instr_case_10 : forall (v_labelidx : uN), fun_free_instr (.BR_ON_NULL v_labelidx) (free_labelidx v_labelidx)
  | fun_free_instr_case_11 : forall (v_labelidx : uN), fun_free_instr (.BR_ON_NON_NULL v_labelidx) (free_labelidx v_labelidx)
  | fun_free_instr_case_12 : forall (v_labelidx : uN) (reftype_1 : reftype) (reftype_2 : reftype) (var_1 : free) (var_0 : free), 
    (fun_free_reftype reftype_2 var_1) ->
    (fun_free_reftype reftype_1 var_0) ->
    fun_free_instr (.BR_ON_CAST v_labelidx reftype_1 reftype_2) (((free_labelidx v_labelidx) ++ var_0) ++ var_1)
  | fun_free_instr_case_13 : forall (v_labelidx : uN) (reftype_1 : reftype) (reftype_2 : reftype) (var_1 : free) (var_0 : free), 
    (fun_free_reftype reftype_2 var_1) ->
    (fun_free_reftype reftype_1 var_0) ->
    fun_free_instr (.BR_ON_CAST_FAIL v_labelidx reftype_1 reftype_2) (((free_labelidx v_labelidx) ++ var_0) ++ var_1)
  | fun_free_instr_case_14 : forall (v_funcidx : uN), fun_free_instr (.CALL v_funcidx) (free_funcidx v_funcidx)
  | fun_free_instr_case_15 : forall (v_typeuse : typeuse) (var_0 : free), 
    (fun_free_typeuse v_typeuse var_0) ->
    fun_free_instr (.CALL_REF v_typeuse) var_0
  | fun_free_instr_case_16 : forall (v_tableidx : uN) (v_typeuse : typeuse) (var_0 : free), 
    (fun_free_typeuse v_typeuse var_0) ->
    fun_free_instr (.CALL_INDIRECT v_tableidx v_typeuse) ((free_tableidx v_tableidx) ++ var_0)
  | fun_free_instr_case_17 : fun_free_instr .RETURN { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_18 : forall (v_funcidx : uN), fun_free_instr (.RETURN_CALL v_funcidx) (free_funcidx v_funcidx)
  | fun_free_instr_case_19 : forall (v_typeuse : typeuse) (var_0 : free), 
    (fun_free_typeuse v_typeuse var_0) ->
    fun_free_instr (.RETURN_CALL_REF v_typeuse) var_0
  | fun_free_instr_case_20 : forall (v_tableidx : uN) (v_typeuse : typeuse) (var_0 : free), 
    (fun_free_typeuse v_typeuse var_0) ->
    fun_free_instr (.RETURN_CALL_INDIRECT v_tableidx v_typeuse) ((free_tableidx v_tableidx) ++ var_0)
  | fun_free_instr_case_21 : forall (v_numtype : numtype) (numlit : num_), fun_free_instr (.CONST v_numtype numlit) (free_numtype v_numtype)
  | fun_free_instr_case_22 : forall (v_numtype : numtype) (unop : unop_), fun_free_instr (.UNOP v_numtype unop) (free_numtype v_numtype)
  | fun_free_instr_case_23 : forall (v_numtype : numtype) (binop : binop_), fun_free_instr (.BINOP v_numtype binop) (free_numtype v_numtype)
  | fun_free_instr_case_24 : forall (v_numtype : numtype) (testop : testop_), fun_free_instr (.TESTOP v_numtype testop) (free_numtype v_numtype)
  | fun_free_instr_case_25 : forall (v_numtype : numtype) (relop : relop_), fun_free_instr (.RELOP v_numtype relop) (free_numtype v_numtype)
  | fun_free_instr_case_26 : forall (numtype_1 : numtype) (numtype_2 : numtype) (cvtop : cvtop__), fun_free_instr (.CVTOP numtype_1 numtype_2 cvtop) ((free_numtype numtype_1) ++ (free_numtype numtype_2))
  | fun_free_instr_case_27 : forall (v_vectype : vectype) (veclit : uN), fun_free_instr (.VCONST v_vectype veclit) (free_vectype v_vectype)
  | fun_free_instr_case_28 : forall (v_vectype : vectype) (v_vvunop : vvunop), fun_free_instr (.VVUNOP v_vectype v_vvunop) (free_vectype v_vectype)
  | fun_free_instr_case_29 : forall (v_vectype : vectype) (v_vvbinop : vvbinop), fun_free_instr (.VVBINOP v_vectype v_vvbinop) (free_vectype v_vectype)
  | fun_free_instr_case_30 : forall (v_vectype : vectype) (v_vvternop : vvternop), fun_free_instr (.VVTERNOP v_vectype v_vvternop) (free_vectype v_vectype)
  | fun_free_instr_case_31 : forall (v_vectype : vectype) (v_vvtestop : vvtestop), fun_free_instr (.VVTESTOP v_vectype v_vvtestop) (free_vectype v_vectype)
  | fun_free_instr_case_32 : forall (v_shape : shape) (vunop : vunop_), fun_free_instr (.VUNOP v_shape vunop) (free_shape v_shape)
  | fun_free_instr_case_33 : forall (v_shape : shape) (vbinop : vbinop_), fun_free_instr (.VBINOP v_shape vbinop) (free_shape v_shape)
  | fun_free_instr_case_34 : forall (v_shape : shape) (vternop : vternop_), fun_free_instr (.VTERNOP v_shape vternop) (free_shape v_shape)
  | fun_free_instr_case_35 : forall (v_shape : shape) (vtestop : vtestop_), fun_free_instr (.VTESTOP v_shape vtestop) (free_shape v_shape)
  | fun_free_instr_case_36 : forall (v_shape : shape) (vrelop : vrelop_), fun_free_instr (.VRELOP v_shape vrelop) (free_shape v_shape)
  | fun_free_instr_case_37 : forall (v_ishape : ishape) (vshiftop : vshiftop_), fun_free_instr (.VSHIFTOP v_ishape vshiftop) (free_shape (proj_ishape_0 v_ishape))
  | fun_free_instr_case_38 : forall (v_ishape : ishape), fun_free_instr (.VBITMASK v_ishape) (free_shape (proj_ishape_0 v_ishape))
  | fun_free_instr_case_39 : forall (v_bshape : bshape) (vswizzlop : vswizzlop_), fun_free_instr (.VSWIZZLOP v_bshape vswizzlop) (free_shape (proj_bshape_0 v_bshape))
  | fun_free_instr_case_40 : forall (v_bshape : bshape) (laneidx_lst : (List laneidx)), fun_free_instr (.VSHUFFLE v_bshape laneidx_lst) (free_shape (proj_bshape_0 v_bshape))
  | fun_free_instr_case_41 : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextunop : vextunop__), fun_free_instr (.VEXTUNOP ishape_1 ishape_2 vextunop) ((free_shape (proj_ishape_0 ishape_1)) ++ (free_shape (proj_ishape_0 ishape_2)))
  | fun_free_instr_case_42 : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextbinop : vextbinop__), fun_free_instr (.VEXTBINOP ishape_1 ishape_2 vextbinop) ((free_shape (proj_ishape_0 ishape_1)) ++ (free_shape (proj_ishape_0 ishape_2)))
  | fun_free_instr_case_43 : forall (ishape_1 : ishape) (ishape_2 : ishape) (vextternop : vextternop__), fun_free_instr (.VEXTTERNOP ishape_1 ishape_2 vextternop) ((free_shape (proj_ishape_0 ishape_1)) ++ (free_shape (proj_ishape_0 ishape_2)))
  | fun_free_instr_case_44 : forall (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx), fun_free_instr (.VNARROW ishape_1 ishape_2 v_sx) ((free_shape (proj_ishape_0 ishape_1)) ++ (free_shape (proj_ishape_0 ishape_2)))
  | fun_free_instr_case_45 : forall (shape_1 : shape) (shape_2 : shape) (vcvtop : vcvtop__), fun_free_instr (.VCVTOP shape_1 shape_2 vcvtop) ((free_shape shape_1) ++ (free_shape shape_2))
  | fun_free_instr_case_46 : forall (v_shape : shape), fun_free_instr (.VSPLAT v_shape) (free_shape v_shape)
  | fun_free_instr_case_47 : forall (v_shape : shape) (sx_opt : (Option sx)) (v_laneidx : uN), fun_free_instr (.VEXTRACT_LANE v_shape sx_opt v_laneidx) (free_shape v_shape)
  | fun_free_instr_case_48 : forall (v_shape : shape) (v_laneidx : uN), fun_free_instr (.VREPLACE_LANE v_shape v_laneidx) (free_shape v_shape)
  | fun_free_instr_case_49 : forall (v_heaptype : heaptype) (var_0 : free), 
    (fun_free_heaptype v_heaptype var_0) ->
    fun_free_instr (.REF_NULL v_heaptype) var_0
  | fun_free_instr_case_50 : fun_free_instr .REF_IS_NULL { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_51 : fun_free_instr .REF_AS_NON_NULL { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_52 : fun_free_instr .REF_EQ { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_53 : forall (v_reftype : reftype) (var_0 : free), 
    (fun_free_reftype v_reftype var_0) ->
    fun_free_instr (.REF_TEST v_reftype) var_0
  | fun_free_instr_case_54 : forall (v_reftype : reftype) (var_0 : free), 
    (fun_free_reftype v_reftype var_0) ->
    fun_free_instr (.REF_CAST v_reftype) var_0
  | fun_free_instr_case_55 : forall (v_funcidx : uN), fun_free_instr (.REF_FUNC v_funcidx) (free_funcidx v_funcidx)
  | fun_free_instr_case_56 : fun_free_instr .REF_I31 { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_57 : forall (v_sx : sx), fun_free_instr (.I31_GET v_sx) { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_58 : forall (v_typeidx : uN), fun_free_instr (.STRUCT_NEW v_typeidx) { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_59 : forall (v_typeidx : uN), fun_free_instr (.STRUCT_NEW_DEFAULT v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_60 : forall (sx_opt : (Option sx)) (v_typeidx : uN) (v_u32 : uN), fun_free_instr (.STRUCT_GET sx_opt v_typeidx v_u32) (free_typeidx v_typeidx)
  | fun_free_instr_case_61 : forall (v_typeidx : uN) (v_u32 : uN), fun_free_instr (.STRUCT_SET v_typeidx v_u32) (free_typeidx v_typeidx)
  | fun_free_instr_case_62 : forall (v_typeidx : uN), fun_free_instr (.ARRAY_NEW v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_63 : forall (v_typeidx : uN), fun_free_instr (.ARRAY_NEW_DEFAULT v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_64 : forall (v_typeidx : uN) (v_u32 : uN), fun_free_instr (.ARRAY_NEW_FIXED v_typeidx v_u32) (free_typeidx v_typeidx)
  | fun_free_instr_case_65 : forall (v_typeidx : uN) (v_dataidx : uN), fun_free_instr (.ARRAY_NEW_DATA v_typeidx v_dataidx) ((free_typeidx v_typeidx) ++ (free_dataidx v_dataidx))
  | fun_free_instr_case_66 : forall (v_typeidx : uN) (v_elemidx : uN), fun_free_instr (.ARRAY_NEW_ELEM v_typeidx v_elemidx) ((free_typeidx v_typeidx) ++ (free_elemidx v_elemidx))
  | fun_free_instr_case_67 : forall (sx_opt : (Option sx)) (v_typeidx : uN), fun_free_instr (.ARRAY_GET sx_opt v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_68 : forall (v_typeidx : uN), fun_free_instr (.ARRAY_SET v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_69 : fun_free_instr .ARRAY_LEN { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_70 : forall (v_typeidx : uN), fun_free_instr (.ARRAY_FILL v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_71 : forall (typeidx_1 : uN) (typeidx_2 : uN), fun_free_instr (.ARRAY_COPY typeidx_1 typeidx_2) ((free_typeidx typeidx_1) ++ (free_typeidx typeidx_2))
  | fun_free_instr_case_72 : forall (v_typeidx : uN) (v_dataidx : uN), fun_free_instr (.ARRAY_INIT_DATA v_typeidx v_dataidx) ((free_typeidx v_typeidx) ++ (free_dataidx v_dataidx))
  | fun_free_instr_case_73 : forall (v_typeidx : uN) (v_elemidx : uN), fun_free_instr (.ARRAY_INIT_ELEM v_typeidx v_elemidx) ((free_typeidx v_typeidx) ++ (free_elemidx v_elemidx))
  | fun_free_instr_case_74 : fun_free_instr .EXTERN_CONVERT_ANY { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_75 : fun_free_instr .ANY_CONVERT_EXTERN { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_instr_case_76 : forall (v_localidx : uN), fun_free_instr (.LOCAL_GET v_localidx) (free_localidx v_localidx)
  | fun_free_instr_case_77 : forall (v_localidx : uN), fun_free_instr (.LOCAL_SET v_localidx) (free_localidx v_localidx)
  | fun_free_instr_case_78 : forall (v_localidx : uN), fun_free_instr (.LOCAL_TEE v_localidx) (free_localidx v_localidx)
  | fun_free_instr_case_79 : forall (v_globalidx : uN), fun_free_instr (.GLOBAL_GET v_globalidx) (free_globalidx v_globalidx)
  | fun_free_instr_case_80 : forall (v_globalidx : uN), fun_free_instr (.GLOBAL_SET v_globalidx) (free_globalidx v_globalidx)
  | fun_free_instr_case_81 : forall (v_tableidx : uN), fun_free_instr (.TABLE_GET v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_82 : forall (v_tableidx : uN), fun_free_instr (.TABLE_SET v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_83 : forall (v_tableidx : uN), fun_free_instr (.TABLE_SIZE v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_84 : forall (v_tableidx : uN), fun_free_instr (.TABLE_GROW v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_85 : forall (v_tableidx : uN), fun_free_instr (.TABLE_FILL v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_86 : forall (tableidx_1 : uN) (tableidx_2 : uN), fun_free_instr (.TABLE_COPY tableidx_1 tableidx_2) ((free_tableidx tableidx_1) ++ (free_tableidx tableidx_2))
  | fun_free_instr_case_87 : forall (v_tableidx : uN) (v_elemidx : uN), fun_free_instr (.TABLE_INIT v_tableidx v_elemidx) ((free_tableidx v_tableidx) ++ (free_elemidx v_elemidx))
  | fun_free_instr_case_88 : forall (v_elemidx : uN), fun_free_instr (.ELEM_DROP v_elemidx) (free_elemidx v_elemidx)
  | fun_free_instr_case_89 : forall (v_numtype : numtype) (loadop_opt : (Option loadop_)) (v_memidx : uN) (v_memarg : memarg), fun_free_instr (.LOAD v_numtype loadop_opt v_memidx v_memarg) ((free_numtype v_numtype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_90 : forall (v_numtype : numtype) (storeop_opt : (Option storeop_)) (v_memidx : uN) (v_memarg : memarg), fun_free_instr (.STORE v_numtype storeop_opt v_memidx v_memarg) ((free_numtype v_numtype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_91 : forall (v_vectype : vectype) (vloadop_opt : (Option vloadop_)) (v_memidx : uN) (v_memarg : memarg), fun_free_instr (.VLOAD v_vectype vloadop_opt v_memidx v_memarg) ((free_vectype v_vectype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_92 : forall (v_vectype : vectype) (v_sz : sz) (v_memidx : uN) (v_memarg : memarg) (v_laneidx : uN), fun_free_instr (.VLOAD_LANE v_vectype v_sz v_memidx v_memarg v_laneidx) ((free_vectype v_vectype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_93 : forall (v_vectype : vectype) (v_memidx : uN) (v_memarg : memarg), fun_free_instr (.VSTORE v_vectype v_memidx v_memarg) ((free_vectype v_vectype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_94 : forall (v_vectype : vectype) (v_sz : sz) (v_memidx : uN) (v_memarg : memarg) (v_laneidx : uN), fun_free_instr (.VSTORE_LANE v_vectype v_sz v_memidx v_memarg v_laneidx) ((free_vectype v_vectype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_95 : forall (v_memidx : uN), fun_free_instr (.MEMORY_SIZE v_memidx) (free_memidx v_memidx)
  | fun_free_instr_case_96 : forall (v_memidx : uN), fun_free_instr (.MEMORY_GROW v_memidx) (free_memidx v_memidx)
  | fun_free_instr_case_97 : forall (v_memidx : uN), fun_free_instr (.MEMORY_FILL v_memidx) (free_memidx v_memidx)
  | fun_free_instr_case_98 : forall (memidx_1 : uN) (memidx_2 : uN), fun_free_instr (.MEMORY_COPY memidx_1 memidx_2) ((free_memidx memidx_1) ++ (free_memidx memidx_2))
  | fun_free_instr_case_99 : forall (v_memidx : uN) (v_dataidx : uN), fun_free_instr (.MEMORY_INIT v_memidx v_dataidx) ((free_memidx v_memidx) ++ (free_dataidx v_dataidx))
  | fun_free_instr_case_100 : forall (v_dataidx : uN), fun_free_instr (.DATA_DROP v_dataidx) (free_dataidx v_dataidx)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:418.6-418.17 -/
inductive fun_free_block : (List instr) -> free -> Prop where
  | fun_free_block_case_0 : forall (instr_lst : (List instr)) (v_free : free) (var_2_lst : (List free)) (var_1 : free) (var_0 : (List labelidx)), 
    ((List.length var_2_lst) == (List.length instr_lst)) ->
    Forall₂ (fun (var_2 : free) (v_instr : instr) => (fun_free_instr v_instr var_2)) var_2_lst instr_lst ->
    (fun_free_list var_2_lst var_1) ->
    (fun_shift_labelidxs (v_free.LABELS) var_0) ->
    (v_free == var_1) ->
    fun_free_block instr_lst (v_free <| LABELS := var_0 |>)

end

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.3-syntax.instructions.spectec:419.6-419.16 -/
inductive fun_free_expr : expr -> free -> Prop where
  | fun_free_expr_case_0 : forall (instr_lst : (List instr)) (var_1_lst : (List free)) (var_0 : free), 
    ((List.length var_1_lst) == (List.length instr_lst)) ->
    Forall₂ (fun (var_1 : free) (v_instr : instr) => (fun_free_instr v_instr var_1)) var_1_lst instr_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_free_expr instr_lst var_0

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:5.1-6.43 -/
inductive elemmode : Type where
  | ACTIVE (v_tableidx : tableidx) (v_expr : expr) : elemmode
  | PASSIVE : elemmode
  | DECLARE : elemmode
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:5.8-5.16 -/
inductive wf_elemmode : elemmode -> Prop where
  | elemmode_case_0 : forall (v_tableidx : tableidx) (v_expr : expr), 
    (wf_uN 32 v_tableidx) ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_elemmode (.ACTIVE v_tableidx v_expr)
  | elemmode_case_1 : wf_elemmode .PASSIVE
  | elemmode_case_2 : wf_elemmode .DECLARE

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:7.1-8.31 -/
inductive datamode : Type where
  | ACTIVE (v_memidx : memidx) (v_expr : expr) : datamode
  | PASSIVE : datamode
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:7.8-7.16 -/
inductive wf_datamode : datamode -> Prop where
  | datamode_case_0 : forall (v_memidx : memidx) (v_expr : expr), 
    (wf_uN 32 v_memidx) ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_datamode (.ACTIVE v_memidx v_expr)
  | datamode_case_1 : wf_datamode .PASSIVE

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:10.1-11.15 -/
inductive type : Type where
  | TYPE (v_rectype : rectype) : type
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:13.1-14.14 -/
inductive tag : Type where
  | TAG (v_tagtype : tagtype) : tag
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:13.8-13.11 -/
inductive wf_tag : tag -> Prop where
  | tag_case_0 : forall (v_tagtype : tagtype), 
    (wf_typeuse v_tagtype) ->
    wf_tag (.TAG v_tagtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:16.1-17.25 -/
inductive global : Type where
  | GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:16.8-16.14 -/
inductive wf_global : global -> Prop where
  | global_case_0 : forall (v_globaltype : globaltype) (v_expr : expr), 
    (wf_globaltype v_globaltype) ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_global (.GLOBAL v_globaltype v_expr)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:19.1-20.17 -/
inductive mem : Type where
  | MEMORY (v_memtype : memtype) : mem
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:19.8-19.11 -/
inductive wf_mem : mem -> Prop where
  | mem_case_0 : forall (v_memtype : memtype), 
    (wf_memtype v_memtype) ->
    wf_mem (.MEMORY v_memtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:22.1-23.23 -/
inductive table : Type where
  | TABLE (v_tabletype : tabletype) (v_expr : expr) : table
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:22.8-22.13 -/
inductive wf_table : table -> Prop where
  | table_case_0 : forall (v_tabletype : tabletype) (v_expr : expr), 
    (wf_tabletype v_tabletype) ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_table (.TABLE v_tabletype v_expr)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:25.1-26.22 -/
inductive data : Type where
  | DATA (byte_lst : (List byte)) (v_datamode : datamode) : data
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:25.8-25.12 -/
inductive wf_data : data -> Prop where
  | data_case_0 : forall (byte_lst : (List byte)) (v_datamode : datamode), 
    Forall (fun (v_byte : byte) => (wf_byte v_byte)) byte_lst ->
    (wf_datamode v_datamode) ->
    wf_data (.DATA byte_lst v_datamode)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:28.1-29.16 -/
inductive «local» : Type where
  | LOCAL (v_valtype : valtype) : «local»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:28.8-28.13 -/
inductive wf_local : «local» -> Prop where
  | local_case_0 : forall (v_valtype : valtype), 
    (wf_valtype v_valtype) ->
    wf_local (.LOCAL v_valtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:31.1-32.27 -/
inductive func : Type where
  | FUNC (v_typeidx : typeidx) (local_lst : (List «local»)) (v_expr : expr) : func
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:31.8-31.12 -/
inductive wf_func : func -> Prop where
  | func_case_0 : forall (v_typeidx : typeidx) (local_lst : (List «local»)) (v_expr : expr), 
    (wf_uN 32 v_typeidx) ->
    Forall (fun (v_local : «local») => (wf_local v_local)) local_lst ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_func (.FUNC v_typeidx local_lst v_expr)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:34.1-35.30 -/
inductive elem : Type where
  | ELEM (v_reftype : reftype) (expr_lst : (List expr)) (v_elemmode : elemmode) : elem
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:34.8-34.12 -/
inductive wf_elem : elem -> Prop where
  | elem_case_0 : forall (v_reftype : reftype) (expr_lst : (List expr)) (v_elemmode : elemmode), 
    (wf_reftype v_reftype) ->
    Forall (fun (v_expr : expr) => Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr) expr_lst ->
    (wf_elemmode v_elemmode) ->
    wf_elem (.ELEM v_reftype expr_lst v_elemmode)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:37.1-38.16 -/
inductive start : Type where
  | START (v_funcidx : funcidx) : start
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:37.8-37.13 -/
inductive wf_start : start -> Prop where
  | start_case_0 : forall (v_funcidx : funcidx), 
    (wf_uN 32 v_funcidx) ->
    wf_start (.START v_funcidx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:40.1-41.30 -/
inductive «import» : Type where
  | IMPORT (v_name : name) (_ : name) (v_externtype : externtype) : «import»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:40.8-40.14 -/
inductive wf_import : «import» -> Prop where
  | import_case_0 : forall (v_name : name) (v_externtype : externtype) (var_0 : name), 
    (wf_name v_name) ->
    (wf_externtype v_externtype) ->
    (wf_name var_0) ->
    wf_import (.IMPORT v_name var_0 v_externtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:43.1-44.24 -/
inductive «export» : Type where
  | EXPORT (v_name : name) (v_externidx : externidx) : «export»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:43.8-43.14 -/
inductive wf_export : «export» -> Prop where
  | export_case_0 : forall (v_name : name) (v_externidx : externidx), 
    (wf_name v_name) ->
    (wf_externidx v_externidx) ->
    wf_export (.EXPORT v_name v_externidx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:46.1-47.81 -/
inductive module : Type where
  | MODULE (type_lst : (List type)) (import_lst : (List «import»)) (tag_lst : (List tag)) (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (func_lst : (List func)) (data_lst : (List data)) (elem_lst : (List elem)) (start_opt : (Option start)) (export_lst : (List «export»)) : module
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:46.8-46.14 -/
inductive wf_module : module -> Prop where
  | module_case_0 : forall (type_lst : (List type)) (import_lst : (List «import»)) (tag_lst : (List tag)) (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (func_lst : (List func)) (data_lst : (List data)) (elem_lst : (List elem)) (start_opt : (Option start)) (export_lst : (List «export»)), 
    Forall (fun (v_import : «import») => (wf_import v_import)) import_lst ->
    Forall (fun (v_tag : tag) => (wf_tag v_tag)) tag_lst ->
    Forall (fun (v_global : global) => (wf_global v_global)) global_lst ->
    Forall (fun (v_mem : mem) => (wf_mem v_mem)) mem_lst ->
    Forall (fun (v_table : table) => (wf_table v_table)) table_lst ->
    Forall (fun (v_func : func) => (wf_func v_func)) func_lst ->
    Forall (fun (v_data : data) => (wf_data v_data)) data_lst ->
    Forall (fun (v_elem : elem) => (wf_elem v_elem)) elem_lst ->
    Forall (fun (v_start : start) => (wf_start v_start)) (Option.toList start_opt) ->
    Forall (fun (v_export : «export») => (wf_export v_export)) export_lst ->
    wf_module (.MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:62.6-62.16 -/
inductive fun_free_type : type -> free -> Prop where
  | fun_free_type_case_0 : forall (v_rectype : rectype) (var_0 : free), 
    (fun_free_rectype v_rectype var_0) ->
    fun_free_type (.TYPE v_rectype) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:63.6-63.15 -/
inductive fun_free_tag : tag -> free -> Prop where
  | fun_free_tag_case_0 : forall (v_tagtype : typeuse) (var_0 : free), 
    (fun_free_tagtype v_tagtype var_0) ->
    fun_free_tag (.TAG v_tagtype) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:64.6-64.18 -/
inductive fun_free_global : global -> free -> Prop where
  | fun_free_global_case_0 : forall (v_globaltype : globaltype) (v_expr : (List instr)) (var_1 : free) (var_0 : free), 
    (fun_free_expr v_expr var_1) ->
    (fun_free_globaltype v_globaltype var_0) ->
    fun_free_global (.GLOBAL v_globaltype v_expr) (var_0 ++ var_1)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:65.1-65.26 -/
def free_mem : ∀  (v_mem : mem) , free
  | (.MEMORY v_memtype) =>
    (free_memtype v_memtype)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:66.6-66.17 -/
inductive fun_free_table : table -> free -> Prop where
  | fun_free_table_case_0 : forall (v_tabletype : tabletype) (v_expr : (List instr)) (var_1 : free) (var_0 : free), 
    (fun_free_expr v_expr var_1) ->
    (fun_free_tabletype v_tabletype var_0) ->
    fun_free_table (.TABLE v_tabletype v_expr) (var_0 ++ var_1)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:67.6-67.17 -/
inductive fun_free_local : «local» -> free -> Prop where
  | fun_free_local_case_0 : forall (t : valtype) (var_0 : free), 
    (fun_free_valtype t var_0) ->
    fun_free_local (.LOCAL t) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:68.6-68.16 -/
inductive fun_free_func : func -> free -> Prop where
  | fun_free_func_case_0 : forall (v_typeidx : uN) (local_lst : (List «local»)) (v_expr : (List instr)) (var_2 : free) (var_1_lst : (List free)) (var_0 : free), 
    (fun_free_block v_expr var_2) ->
    ((List.length var_1_lst) == (List.length local_lst)) ->
    Forall₂ (fun (var_1 : free) (v_local : «local») => (fun_free_local v_local var_1)) var_1_lst local_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_free_func (.FUNC v_typeidx local_lst v_expr) (((free_typeidx v_typeidx) ++ var_0) ++ (var_2 <| LOCALS := [] |>))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:71.6-71.20 -/
inductive fun_free_datamode : datamode -> free -> Prop where
  | fun_free_datamode_case_0 : forall (v_memidx : uN) (v_expr : (List instr)) (var_0 : free), 
    (fun_free_expr v_expr var_0) ->
    fun_free_datamode (.ACTIVE v_memidx v_expr) ((free_memidx v_memidx) ++ var_0)
  | fun_free_datamode_case_1 : fun_free_datamode .PASSIVE { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:69.6-69.16 -/
inductive fun_free_data : data -> free -> Prop where
  | fun_free_data_case_0 : forall (byte_lst : (List byte)) (v_datamode : datamode) (var_0 : free), 
    (fun_free_datamode v_datamode var_0) ->
    fun_free_data (.DATA byte_lst v_datamode) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:72.6-72.20 -/
inductive fun_free_elemmode : elemmode -> free -> Prop where
  | fun_free_elemmode_case_0 : forall (v_tableidx : uN) (v_expr : (List instr)) (var_0 : free), 
    (fun_free_expr v_expr var_0) ->
    fun_free_elemmode (.ACTIVE v_tableidx v_expr) ((free_tableidx v_tableidx) ++ var_0)
  | fun_free_elemmode_case_1 : fun_free_elemmode .PASSIVE { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }
  | fun_free_elemmode_case_2 : fun_free_elemmode .DECLARE { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [] }

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:70.6-70.16 -/
inductive fun_free_elem : elem -> free -> Prop where
  | fun_free_elem_case_0 : forall (v_reftype : reftype) (expr_lst : (List expr)) (v_elemmode : elemmode) (var_3 : free) (var_2_lst : (List free)) (var_1 : free) (var_0 : free), 
    (fun_free_elemmode v_elemmode var_3) ->
    ((List.length var_2_lst) == (List.length expr_lst)) ->
    Forall₂ (fun (var_2 : free) (v_expr : expr) => (fun_free_expr v_expr var_2)) var_2_lst expr_lst ->
    (fun_free_list var_2_lst var_1) ->
    (fun_free_reftype v_reftype var_0) ->
    fun_free_elem (.ELEM v_reftype expr_lst v_elemmode) ((var_0 ++ var_1) ++ var_3)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:73.1-73.30 -/
def free_start : ∀  (v_start : start) , free
  | (.START v_funcidx) =>
    (free_funcidx v_funcidx)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:74.6-74.18 -/
inductive fun_free_import : «import» -> free -> Prop where
  | fun_free_import_case_0 : forall (name_1 : name) (name_2 : name) (v_externtype : externtype) (var_0 : free), 
    (fun_free_externtype v_externtype var_0) ->
    fun_free_import (.IMPORT name_1 name_2 v_externtype) var_0

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:75.1-75.32 -/
def free_export : ∀  (v_export : «export») , free
  | (.EXPORT v_name v_externidx) =>
    (free_externidx v_externidx)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:76.6-76.18 -/
inductive fun_free_module : module -> free -> Prop where
  | fun_free_module_case_0 : forall (type_lst : (List type)) (import_lst : (List «import»)) (tag_lst : (List tag)) (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (func_lst : (List func)) (data_lst : (List data)) (elem_lst : (List elem)) (start_opt : (Option start)) (export_lst : (List «export»)) (var_17 : free) (var_16_lst : (List free)) (var_15 : free) (var_14_lst : (List free)) (var_13 : free) (var_12_lst : (List free)) (var_11 : free) (var_10_lst : (List free)) (var_9 : free) (var_8_lst : (List free)) (var_7 : free) (var_6 : free) (var_5_lst : (List free)) (var_4 : free) (var_3_lst : (List free)) (var_2 : free) (var_1_lst : (List free)) (var_0 : free), 
    (fun_free_list (List.map (fun (v_export : «export») => (free_export v_export)) export_lst) var_17) ->
    ((List.length var_16_lst) == (List.length import_lst)) ->
    Forall₂ (fun (var_16 : free) (v_import : «import») => (fun_free_import v_import var_16)) var_16_lst import_lst ->
    (fun_free_list var_16_lst var_15) ->
    ((List.length var_14_lst) == (List.length elem_lst)) ->
    Forall₂ (fun (var_14 : free) (v_elem : elem) => (fun_free_elem v_elem var_14)) var_14_lst elem_lst ->
    (fun_free_list var_14_lst var_13) ->
    ((List.length var_12_lst) == (List.length data_lst)) ->
    Forall₂ (fun (var_12 : free) (v_data : data) => (fun_free_data v_data var_12)) var_12_lst data_lst ->
    (fun_free_list var_12_lst var_11) ->
    ((List.length var_10_lst) == (List.length func_lst)) ->
    Forall₂ (fun (var_10 : free) (v_func : func) => (fun_free_func v_func var_10)) var_10_lst func_lst ->
    (fun_free_list var_10_lst var_9) ->
    ((List.length var_8_lst) == (List.length table_lst)) ->
    Forall₂ (fun (var_8 : free) (v_table : table) => (fun_free_table v_table var_8)) var_8_lst table_lst ->
    (fun_free_list var_8_lst var_7) ->
    (fun_free_list (List.map (fun (v_mem : mem) => (free_mem v_mem)) mem_lst) var_6) ->
    ((List.length var_5_lst) == (List.length global_lst)) ->
    Forall₂ (fun (var_5 : free) (v_global : global) => (fun_free_global v_global var_5)) var_5_lst global_lst ->
    (fun_free_list var_5_lst var_4) ->
    ((List.length var_3_lst) == (List.length tag_lst)) ->
    Forall₂ (fun (var_3 : free) (v_tag : tag) => (fun_free_tag v_tag var_3)) var_3_lst tag_lst ->
    (fun_free_list var_3_lst var_2) ->
    ((List.length var_1_lst) == (List.length type_lst)) ->
    Forall₂ (fun (var_1 : free) (v_type : type) => (fun_free_type v_type var_1)) var_1_lst type_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_free_module (.MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst) ((((((((((var_0 ++ var_2) ++ var_4) ++ var_6) ++ var_7) ++ var_9) ++ var_11) ++ var_13) ++ (free_opt (Option.map (fun (v_start : start) => (free_start v_start)) start_opt))) ++ var_15) ++ var_17)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:130.6-130.21 -/
inductive fun_funcidx_module : module -> (List funcidx) -> Prop where
  | fun_funcidx_module_case_0 : forall (v_module : module) (var_0 : free), 
    (fun_free_module v_module var_0) ->
    fun_funcidx_module v_module (var_0.FUNCS)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/1.4-syntax.modules.spectec:133.6-133.20 -/
inductive fun_dataidx_funcs : (List func) -> (List dataidx) -> Prop where
  | fun_dataidx_funcs_case_0 : forall (func_lst : (List func)) (var_1_lst : (List free)) (var_0 : free), 
    ((List.length var_1_lst) == (List.length func_lst)) ->
    Forall₂ (fun (var_1 : free) (v_func : func) => (fun_free_func v_func var_1)) var_1_lst func_lst ->
    (fun_free_list var_1_lst var_0) ->
    fun_dataidx_funcs func_lst (var_0.DATAS)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:8.1-9.16 -/
inductive init : Type where
  | SET : init
  | UNSET : init
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:11.1-12.15 -/
inductive localtype : Type where
  | mk_localtype (v_init : init) (v_valtype : valtype) : localtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:11.8-11.17 -/
inductive wf_localtype : localtype -> Prop where
  | localtype_case_0 : forall (v_init : init) (v_valtype : valtype), 
    (wf_valtype v_valtype) ->
    wf_localtype (.mk_localtype v_init v_valtype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:14.1-15.56 -/
inductive instrtype : Type where
  | mk_instrtype (v_resulttype : resulttype) (localidx_lst : (List localidx)) (_ : resulttype) : instrtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:14.8-14.17 -/
inductive wf_instrtype : instrtype -> Prop where
  | instrtype_case_0 : forall (v_resulttype : resulttype) (localidx_lst : (List localidx)) (var_0 : resulttype), 
    Forall (fun (v_localidx : localidx) => (wf_uN 32 v_localidx)) localidx_lst ->
    wf_instrtype (.mk_instrtype v_resulttype localidx_lst var_0)

/- Record Creation Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:24.1-38.4 -/
structure context where MKcontext ::
  TYPES : (List deftype)
  RECS : (List subtype)
  TAGS : (List tagtype)
  GLOBALS : (List globaltype)
  MEMS : (List memtype)
  TABLES : (List tabletype)
  FUNCS : (List deftype)
  DATAS : (List datatype)
  ELEMS : (List elemtype)
  LOCALS : (List localtype)
  LABELS : (List resulttype)
  RETURN : (Option resulttype)
  REFS : (List funcidx)
deriving Inhabited, BEq

def _append_context (arg1 arg2 : (context)) : context where
  TYPES := arg1.TYPES ++ arg2.TYPES
  RECS := arg1.RECS ++ arg2.RECS
  TAGS := arg1.TAGS ++ arg2.TAGS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  MEMS := arg1.MEMS ++ arg2.MEMS
  TABLES := arg1.TABLES ++ arg2.TABLES
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  DATAS := arg1.DATAS ++ arg2.DATAS
  ELEMS := arg1.ELEMS ++ arg2.ELEMS
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
  LABELS := arg1.LABELS ++ arg2.LABELS
  RETURN := arg1.RETURN ++ arg2.RETURN
  REFS := arg1.REFS ++ arg2.REFS
instance : Append context where
  append arg1 arg2 := _append_context arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:24.8-24.15 -/
inductive wf_context : context -> Prop where
  | context_case_ : forall (var_0 : (List deftype)) (var_1 : (List subtype)) (var_2 : (List tagtype)) (var_3 : (List globaltype)) (var_4 : (List memtype)) (var_5 : (List tabletype)) (var_6 : (List deftype)) (var_7 : (List datatype)) (var_8 : (List elemtype)) (var_9 : (List localtype)) (var_10 : (List resulttype)) (var_11 : (Option resulttype)) (var_12 : (List funcidx)), 
    Forall (fun (var_1 : subtype) => (wf_subtype var_1)) var_1 ->
    Forall (fun (var_2 : tagtype) => (wf_typeuse var_2)) var_2 ->
    Forall (fun (var_3 : globaltype) => (wf_globaltype var_3)) var_3 ->
    Forall (fun (var_4 : memtype) => (wf_memtype var_4)) var_4 ->
    Forall (fun (var_5 : tabletype) => (wf_tabletype var_5)) var_5 ->
    Forall (fun (var_8 : elemtype) => (wf_reftype var_8)) var_8 ->
    Forall (fun (var_9 : localtype) => (wf_localtype var_9)) var_9 ->
    Forall (fun (var_12 : funcidx) => (wf_uN 32 var_12)) var_12 ->
    wf_context { TYPES := var_0, RECS := var_1, TAGS := var_2, GLOBALS := var_3, MEMS := var_4, TABLES := var_5, FUNCS := var_6, DATAS := var_7, ELEMS := var_8, LOCALS := var_9, LABELS := var_10, RETURN := var_11, REFS := var_12 }

/- Recursive Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:46.1-46.144 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:46.6-46.18 -/
inductive fun_with_locals : context -> (List localidx) -> (List localtype) -> context -> Prop where
  | fun_with_locals_case_0 : forall (C : context), fun_with_locals C [] [] C
  | fun_with_locals_case_1 : forall (C : context) (x_1 : uN) (x_lst : (List idx)) (lct_1 : localtype) (lct_lst : (List localtype)) (var_0 : context), 
    (fun_with_locals (C <| LOCALS := (List.modify (C.LOCALS) (proj_uN_0 x_1) (fun (_ : localtype) => lct_1)) |>) x_lst lct_lst var_0) ->
    fun_with_locals C ([x_1] ++ x_lst) ([lct_1] ++ lct_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:59.1-59.94 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:59.6-59.20 -/
inductive fun_clos_deftypes : (List deftype) -> (List deftype) -> Prop where
  | fun_clos_deftypes_case_0 : fun_clos_deftypes [] []
  | fun_clos_deftypes_case_1 : forall (dt_lst : (List deftype)) (dt_n : deftype) (dt'_lst : (List deftype)) (var_1 : (List deftype)) (var_0 : deftype), 
    (fun_clos_deftypes dt_lst var_1) ->
    (fun_subst_all_deftype dt_n (List.map (fun (dt' : deftype) => (typeuse_deftype dt')) dt'_lst) var_0) ->
    (dt'_lst == var_1) ->
    fun_clos_deftypes (dt_lst ++ [dt_n]) (dt'_lst ++ [var_0])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:54.6-54.19 -/
inductive fun_clos_valtype : context -> valtype -> valtype -> Prop where
  | fun_clos_valtype_case_0 : forall (C : context) (t : valtype) (dt_lst : (List deftype)) (var_1 : (List deftype)) (var_0 : valtype), 
    (fun_clos_deftypes (C.TYPES) var_1) ->
    (fun_subst_all_valtype t (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == var_1) ->
    fun_clos_valtype C t var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:55.6-55.19 -/
inductive fun_clos_deftype : context -> deftype -> deftype -> Prop where
  | fun_clos_deftype_case_0 : forall (C : context) (dt : deftype) (dt'_lst : (List deftype)) (var_1 : (List deftype)) (var_0 : deftype), 
    (fun_clos_deftypes (C.TYPES) var_1) ->
    (fun_subst_all_deftype dt (List.map (fun (dt' : deftype) => (typeuse_deftype dt')) dt'_lst) var_0) ->
    (dt'_lst == var_1) ->
    fun_clos_deftype C dt var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:56.6-56.19 -/
inductive fun_clos_tagtype : context -> tagtype -> tagtype -> Prop where
  | fun_clos_tagtype_case_0 : forall (C : context) (jt : typeuse) (dt_lst : (List deftype)) (var_1 : (List deftype)) (var_0 : tagtype), 
    (fun_clos_deftypes (C.TYPES) var_1) ->
    (fun_subst_all_tagtype jt (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == var_1) ->
    fun_clos_tagtype C jt var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:57.6-57.22 -/
inductive fun_clos_externtype : context -> externtype -> externtype -> Prop where
  | fun_clos_externtype_case_0 : forall (C : context) (xt : externtype) (dt_lst : (List deftype)) (var_1 : (List deftype)) (var_0 : externtype), 
    (fun_clos_deftypes (C.TYPES) var_1) ->
    (fun_subst_all_externtype xt (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == var_1) ->
    fun_clos_externtype C xt var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.0-validation.contexts.spectec:58.6-58.22 -/
inductive fun_clos_moduletype : context -> moduletype -> moduletype -> Prop where
  | fun_clos_moduletype_case_0 : forall (C : context) (mmt : moduletype) (dt_lst : (List deftype)) (var_1 : (List deftype)) (var_0 : moduletype), 
    (fun_clos_deftypes (C.TYPES) var_1) ->
    (fun_subst_all_moduletype mmt (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == var_1) ->
    fun_clos_moduletype C mmt var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:7.1-7.91 -/
inductive Numtype_ok : context -> numtype -> Prop where
  | mk_Numtype_ok : forall (C : context) (v_numtype : numtype), Numtype_ok C v_numtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:8.1-8.91 -/
inductive Vectype_ok : context -> vectype -> Prop where
  | mk_Vectype_ok : forall (C : context) (v_vectype : vectype), Vectype_ok C v_vectype

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:79.1-80.85 -/
inductive oktypeidx : Type where
  | OK (v_typeidx : typeidx) : oktypeidx
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:79.8-79.17 -/
inductive wf_oktypeidx : oktypeidx -> Prop where
  | oktypeidx_case_0 : forall (v_typeidx : typeidx), 
    (wf_uN 32 v_typeidx) ->
    wf_oktypeidx (.OK v_typeidx)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:81.1-82.68 -/
inductive oktypeidxnat : Type where
  | OK (v_typeidx : typeidx) (nat : Nat) : oktypeidxnat
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:81.8-81.20 -/
inductive wf_oktypeidxnat : oktypeidxnat -> Prop where
  | oktypeidxnat_case_0 : forall (v_typeidx : typeidx) (nat : Nat), 
    (wf_uN 32 v_typeidx) ->
    wf_oktypeidxnat (.OK v_typeidx nat)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:84.1-84.103 -/
inductive Packtype_ok : context -> packtype -> Prop where
  | mk_Packtype_ok : forall (C : context) (v_packtype : packtype), Packtype_ok C v_packtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:133.1-133.116 -/
inductive Packtype_sub : context -> packtype -> packtype -> Prop where
  | mk_Packtype_sub : forall (C : context) (v_packtype : packtype), Packtype_sub C v_packtype v_packtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:7.1-7.103 -/
inductive Numtype_sub : context -> numtype -> numtype -> Prop where
  | mk_Numtype_sub : forall (C : context) (v_numtype : numtype), Numtype_sub C v_numtype v_numtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:65.1-66.70 -/
inductive Expand : deftype -> comptype -> Prop where
  | mk_Expand : forall (v_deftype : deftype) (v_comptype : comptype) (var_0 : comptype), 
    (fun_expanddt v_deftype var_0) ->
    (var_0 == v_comptype) ->
    Expand v_deftype v_comptype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:8.1-8.103 -/
inductive Vectype_sub : context -> vectype -> vectype -> Prop where
  | mk_Vectype_sub : forall (C : context) (v_vectype : vectype), Vectype_sub C v_vectype v_vectype

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:151.1-151.85 -/
def before : ∀  (v_typeuse : typeuse) (v_typeidx : typeidx) (nat : Nat) , Bool
  | (._DEF v_rectype v_n), x, i =>
    true
  | (._IDX v_typeidx), x, i =>
    ((proj_uN_0 v_typeidx) < (proj_uN_0 x))
  | (.REC j), x, i =>
    (j < i)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:156.6-156.15 -/
inductive fun_unrollht : context -> heaptype -> subtype -> Prop where
  | fun_unrollht_case_0 : forall (v_rectype : rectype) (v_n : n) (C : context) (var_0 : subtype), 
    (fun_unrolldt (._DEF v_rectype v_n) var_0) ->
    fun_unrollht C (._DEF v_rectype v_n) var_0
  | fun_unrollht_case_1 : forall (C : context) (v_typeidx : uN) (var_0 : subtype), 
    ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) ->
    (fun_unrolldt ((C.TYPES)[(proj_uN_0 v_typeidx)]!) var_0) ->
    fun_unrollht C (._IDX v_typeidx) var_0
  | fun_unrollht_case_2 : forall (C : context) (i : Nat), 
    (i < (List.length (C.RECS))) ->
    fun_unrollht C (.REC i) ((C.RECS)[i]!)

/- Recursive Definitions at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:9.1-135.117 -/
mutual
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:9.1-9.92 -/
inductive Heaptype_ok : context -> heaptype -> Prop where
  | abs : forall (C : context) (v_absheaptype : absheaptype), Heaptype_ok C (heaptype_absheaptype v_absheaptype)
  | typeuse : forall (C : context) (v_typeuse : typeuse), 
    (Typeuse_ok C v_typeuse) ->
    Heaptype_ok C (heaptype_typeuse v_typeuse)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:10.1-10.91 -/
inductive Reftype_ok : context -> reftype -> Prop where
  | mk_Reftype_ok : forall (C : context) (v_heaptype : heaptype), 
    (Heaptype_ok C v_heaptype) ->
    Reftype_ok C (.REF (some .NULL) v_heaptype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:11.1-11.91 -/
inductive Valtype_ok : context -> valtype -> Prop where
  | num : forall (C : context) (v_numtype : numtype), 
    (Numtype_ok C v_numtype) ->
    Valtype_ok C (valtype_numtype v_numtype)
  | vec : forall (C : context) (v_vectype : vectype), 
    (Vectype_ok C v_vectype) ->
    Valtype_ok C (valtype_vectype v_vectype)
  | ref : forall (C : context) (v_reftype : reftype), 
    (Reftype_ok C v_reftype) ->
    Valtype_ok C (valtype_reftype v_reftype)
  | bot : forall (C : context), Valtype_ok C .BOT

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:12.1-12.94 -/
inductive Typeuse_ok : context -> typeuse -> Prop where
  | typeidx : forall (C : context) (v_typeidx : typeidx) (dt : deftype), 
    ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) ->
    (((C.TYPES)[(proj_uN_0 v_typeidx)]!) == dt) ->
    Typeuse_ok C (._IDX v_typeidx)
  | rec_ : forall (C : context) (i : n) (st : subtype), 
    (i < (List.length (C.RECS))) ->
    (((C.RECS)[i]!) == st) ->
    Typeuse_ok C (.REC i)
  | deftype : forall (C : context) (v_deftype : deftype), 
    (Deftype_ok C v_deftype) ->
    Typeuse_ok C (typeuse_deftype v_deftype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:49.1-49.100 -/
inductive Resulttype_ok : context -> resulttype -> Prop where
  | mk_Resulttype_ok : forall (C : context) (t_lst : (List valtype)), 
    Forall (fun (t : valtype) => (Valtype_ok C t)) t_lst ->
    Resulttype_ok C (.mk_list t_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:85.1-85.104 -/
inductive Fieldtype_ok : context -> fieldtype -> Prop where
  | mk_Fieldtype_ok : forall (C : context) (v_storagetype : storagetype), 
    (Storagetype_ok C v_storagetype) ->
    Fieldtype_ok C (.mk_fieldtype (some .MUT) v_storagetype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:86.1-86.106 -/
inductive Storagetype_ok : context -> storagetype -> Prop where
  | val : forall (C : context) (v_valtype : valtype), 
    (Valtype_ok C v_valtype) ->
    Storagetype_ok C (storagetype_valtype v_valtype)
  | pack : forall (C : context) (v_packtype : packtype), 
    (Packtype_ok C v_packtype) ->
    Storagetype_ok C (storagetype_packtype v_packtype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:87.1-87.103 -/
inductive Comptype_ok : context -> comptype -> Prop where
  | struct : forall (C : context) (fieldtype_lst : (List fieldtype)), 
    Forall (fun (v_fieldtype : fieldtype) => (Fieldtype_ok C v_fieldtype)) fieldtype_lst ->
    Comptype_ok C (.STRUCT (.mk_list fieldtype_lst))
  | array : forall (C : context) (v_fieldtype : fieldtype), 
    (Fieldtype_ok C v_fieldtype) ->
    Comptype_ok C (.ARRAY v_fieldtype)
  | func : forall (C : context) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Resulttype_ok C (.mk_list t_1_lst)) ->
    (Resulttype_ok C (.mk_list t_2_lst)) ->
    Comptype_ok C (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:88.1-88.126 -/
inductive Subtype_ok : context -> subtype -> oktypeidx -> Prop where
  | mk_Subtype_ok : forall (C : context) (x_lst : (List idx)) (v_comptype : comptype) (x_0 : idx) (x'_lst_lst : (List (List idx))) (comptype'_lst : (List comptype)) (var_0_lst : (List subtype)), 
    ((List.length var_0_lst) == (List.length x_lst)) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length (C.TYPES)))) x_lst ->
    Forall₂ (fun (var_0 : subtype) (x : idx) => (fun_unrolldt ((C.TYPES)[(proj_uN_0 x)]!) var_0)) var_0_lst x_lst ->
    ((List.length x_lst) <= 1) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (proj_uN_0 x_0))) x_lst ->
    ((List.length var_0_lst) == (List.length comptype'_lst)) ->
    ((List.length var_0_lst) == (List.length x'_lst_lst)) ->
    Forall₃ (fun (var_0 : subtype) (comptype' : comptype) (x'_lst : (List typeidx)) => (var_0 == (.SUB none (List.map (fun (x' : idx) => (._IDX x')) x'_lst) comptype'))) var_0_lst comptype'_lst x'_lst_lst ->
    (Comptype_ok C v_comptype) ->
    Forall (fun (comptype' : comptype) => (Comptype_sub C v_comptype comptype')) comptype'_lst ->
    Subtype_ok C (.SUB (some .FINAL) (List.map (fun (x : idx) => (._IDX x)) x_lst) v_comptype) (.OK x_0)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:89.1-89.126 -/
inductive Rectype_ok : context -> rectype -> oktypeidx -> Prop where
  | empty : forall (C : context) (x : idx), Rectype_ok C (.REC (.mk_list [])) (.OK x)
  | cons : forall (C : context) (subtype_1 : subtype) (subtype_lst : (List subtype)) (x : idx), 
    (Subtype_ok C subtype_1 (.OK x)) ->
    (Rectype_ok C (.REC (.mk_list subtype_lst)) (.OK (.mk_uN ((proj_uN_0 x) + 1)))) ->
    Rectype_ok C (.REC (.mk_list ([subtype_1] ++ subtype_lst))) (.OK x)
  | _rec2 : forall (C : context) (subtype_lst : (List subtype)) (x : idx), 
    (Rectype_ok2 ({ TYPES := [], RECS := subtype_lst, TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } ++ C) (.REC (.mk_list subtype_lst)) (.OK x 0)) ->
    Rectype_ok C (.REC (.mk_list subtype_lst)) (.OK x)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:90.1-90.126 -/
inductive Subtype_ok2 : context -> subtype -> oktypeidxnat -> Prop where
  | mk_Subtype_ok2 : forall (C : context) (typeuse_lst : (List typeuse)) (compttype : comptype) (x : idx) (i : Nat) (typeuse'_lst_lst : (List (List typeuse))) (comptype'_lst : (List comptype)) (v_comptype : comptype) (var_0_lst : (List subtype)), 
    ((List.length var_0_lst) == (List.length typeuse_lst)) ->
    Forall₂ (fun (var_0 : subtype) (v_typeuse : typeuse) => (fun_unrollht C (heaptype_typeuse v_typeuse) var_0)) var_0_lst typeuse_lst ->
    ((List.length typeuse_lst) <= 1) ->
    Forall (fun (v_typeuse : typeuse) => (before v_typeuse x i)) typeuse_lst ->
    ((List.length var_0_lst) == (List.length comptype'_lst)) ->
    ((List.length var_0_lst) == (List.length typeuse'_lst_lst)) ->
    Forall₃ (fun (var_0 : subtype) (comptype' : comptype) (typeuse'_lst : (List typeuse)) => (var_0 == (.SUB none typeuse'_lst comptype'))) var_0_lst comptype'_lst typeuse'_lst_lst ->
    (Comptype_ok C v_comptype) ->
    Forall (fun (comptype' : comptype) => (Comptype_sub C v_comptype comptype')) comptype'_lst ->
    Subtype_ok2 C (.SUB (some .FINAL) typeuse_lst compttype) (.OK x i)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:91.1-91.126 -/
inductive Rectype_ok2 : context -> rectype -> oktypeidxnat -> Prop where
  | empty : forall (C : context) (x : idx) (i : Nat), Rectype_ok2 C (.REC (.mk_list [])) (.OK x i)
  | cons : forall (C : context) (subtype_1 : subtype) (subtype_lst : (List subtype)) (x : idx) (i : Nat), 
    (Subtype_ok2 C subtype_1 (.OK x i)) ->
    (Rectype_ok2 C (.REC (.mk_list subtype_lst)) (.OK (.mk_uN ((proj_uN_0 x) + 1)) (i + 1))) ->
    Rectype_ok2 C (.REC (.mk_list ([subtype_1] ++ subtype_lst))) (.OK x i)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:92.1-92.102 -/
inductive Deftype_ok : context -> deftype -> Prop where
  | mk_Deftype_ok : forall (C : context) (v_rectype : rectype) (i : n) (x : idx) (subtype_lst : (List subtype)) (v_n : n), 
    (Rectype_ok C v_rectype (.OK x)) ->
    (v_rectype == (.REC (.mk_list subtype_lst))) ->
    (i < v_n) ->
    Deftype_ok C (._DEF v_rectype i)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:95.1-95.108 -/
inductive Comptype_sub : context -> comptype -> comptype -> Prop where
  | struct : forall (C : context) (ft_1_lst : (List fieldtype)) (ft'_1_lst : (List fieldtype)) (ft_2_lst : (List fieldtype)), 
    ((List.length ft_1_lst) == (List.length ft_2_lst)) ->
    Forall₂ (fun (ft_1 : fieldtype) (ft_2 : fieldtype) => (Fieldtype_sub C ft_1 ft_2)) ft_1_lst ft_2_lst ->
    Comptype_sub C (.STRUCT (.mk_list (ft_1_lst ++ ft'_1_lst))) (.STRUCT (.mk_list ft_2_lst))
  | array : forall (C : context) (ft_1 : fieldtype) (ft_2 : fieldtype), 
    (Fieldtype_sub C ft_1 ft_2) ->
    Comptype_sub C (.ARRAY ft_1) (.ARRAY ft_2)
  | func : forall (C : context) (t_11_lst : (List valtype)) (t_12_lst : (List valtype)) (t_21_lst : (List valtype)) (t_22_lst : (List valtype)), 
    (Resulttype_sub C (.mk_list t_21_lst) (.mk_list t_11_lst)) ->
    (Resulttype_sub C (.mk_list t_12_lst) (.mk_list t_22_lst)) ->
    Comptype_sub C (.FUNC (.mk_list t_11_lst) (.mk_list t_12_lst)) (.FUNC (.mk_list t_21_lst) (.mk_list t_22_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:96.1-96.107 -/
inductive Deftype_sub : context -> deftype -> deftype -> Prop where
  | refl : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype) (var_1 : deftype) (var_0 : deftype), 
    (fun_clos_deftype C deftype_2 var_1) ->
    (fun_clos_deftype C deftype_1 var_0) ->
    (var_0 == var_1) ->
    Deftype_sub C deftype_1 deftype_2
  | super : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype) (final_opt : (Option final)) (typeuse_lst : (List typeuse)) (ct : comptype) (i : Nat) (var_0 : subtype), 
    (fun_unrolldt deftype_1 var_0) ->
    (var_0 == (.SUB final_opt typeuse_lst ct)) ->
    (i < (List.length typeuse_lst)) ->
    (Heaptype_sub C (heaptype_typeuse (typeuse_lst[i]!)) (heaptype_deftype deftype_2)) ->
    Deftype_sub C deftype_1 deftype_2

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:9.1-9.104 -/
inductive Heaptype_sub : context -> heaptype -> heaptype -> Prop where
  | refl : forall (C : context) (v_heaptype : heaptype), Heaptype_sub C v_heaptype v_heaptype
  | trans : forall (C : context) (heaptype_1 : heaptype) (heaptype_2 : heaptype) (heaptype' : heaptype), 
    (Heaptype_ok C heaptype') ->
    (Heaptype_sub C heaptype_1 heaptype') ->
    (Heaptype_sub C heaptype' heaptype_2) ->
    Heaptype_sub C heaptype_1 heaptype_2
  | eq_any : forall (C : context), Heaptype_sub C .EQ .ANY
  | i31_eq : forall (C : context), Heaptype_sub C .I31 .EQ
  | struct_eq : forall (C : context), Heaptype_sub C .STRUCT .EQ
  | array_eq : forall (C : context), Heaptype_sub C .ARRAY .EQ
  | struct : forall (C : context) (v_deftype : deftype) (fieldtype_lst : (List fieldtype)), 
    (Expand v_deftype (.STRUCT (.mk_list fieldtype_lst))) ->
    Heaptype_sub C (heaptype_deftype v_deftype) .STRUCT
  | array : forall (C : context) (v_deftype : deftype) (v_fieldtype : fieldtype), 
    (Expand v_deftype (.ARRAY v_fieldtype)) ->
    Heaptype_sub C (heaptype_deftype v_deftype) .ARRAY
  | func : forall (C : context) (v_deftype : deftype) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Expand v_deftype (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Heaptype_sub C (heaptype_deftype v_deftype) .FUNC
  | def : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype), 
    (Deftype_sub C deftype_1 deftype_2) ->
    Heaptype_sub C (heaptype_deftype deftype_1) (heaptype_deftype deftype_2)
  | typeidx_l : forall (C : context) (v_typeidx : typeidx) (v_heaptype : heaptype), 
    ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) ->
    (Heaptype_sub C (heaptype_deftype ((C.TYPES)[(proj_uN_0 v_typeidx)]!)) v_heaptype) ->
    Heaptype_sub C (._IDX v_typeidx) v_heaptype
  | typeidx_r : forall (C : context) (v_heaptype : heaptype) (v_typeidx : typeidx), 
    ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) ->
    (Heaptype_sub C v_heaptype (heaptype_deftype ((C.TYPES)[(proj_uN_0 v_typeidx)]!))) ->
    Heaptype_sub C v_heaptype (._IDX v_typeidx)
  | rec_ : forall (C : context) (i : n) (typeuse_lst : (List typeuse)) (j : Nat) (final_opt : (Option final)) (ct : comptype), 
    (j < (List.length typeuse_lst)) ->
    (i < (List.length (C.RECS))) ->
    (((C.RECS)[i]!) == (.SUB final_opt typeuse_lst ct)) ->
    Heaptype_sub C (.REC i) (heaptype_typeuse (typeuse_lst[j]!))
  | none : forall (C : context) (v_heaptype : heaptype), 
    (Heaptype_sub C v_heaptype .ANY) ->
    Heaptype_sub C .NONE v_heaptype
  | nofunc : forall (C : context) (v_heaptype : heaptype), 
    (Heaptype_sub C v_heaptype .FUNC) ->
    Heaptype_sub C .NOFUNC v_heaptype
  | noexn : forall (C : context) (v_heaptype : heaptype), 
    (Heaptype_sub C v_heaptype .EXN) ->
    Heaptype_sub C .NOEXN v_heaptype
  | noextern : forall (C : context) (v_heaptype : heaptype), 
    (Heaptype_sub C v_heaptype .EXTERN) ->
    Heaptype_sub C .NOEXTERN v_heaptype
  | bot : forall (C : context) (v_heaptype : heaptype), Heaptype_sub C .BOT v_heaptype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:10.1-10.103 -/
inductive Reftype_sub : context -> reftype -> reftype -> Prop where
  | nonnull : forall (C : context) (ht_1 : heaptype) (ht_2 : heaptype), 
    (Heaptype_sub C ht_1 ht_2) ->
    Reftype_sub C (.REF none ht_1) (.REF none ht_2)
  | null : forall (C : context) (ht_1 : heaptype) (ht_2 : heaptype), 
    (Heaptype_sub C ht_1 ht_2) ->
    Reftype_sub C (.REF (some .NULL) ht_1) (.REF (some .NULL) ht_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:11.1-11.103 -/
inductive Valtype_sub : context -> valtype -> valtype -> Prop where
  | num : forall (C : context) (numtype_1 : numtype) (numtype_2 : numtype), 
    (Numtype_sub C numtype_1 numtype_2) ->
    Valtype_sub C (valtype_numtype numtype_1) (valtype_numtype numtype_2)
  | vec : forall (C : context) (vectype_1 : vectype) (vectype_2 : vectype), 
    (Vectype_sub C vectype_1 vectype_2) ->
    Valtype_sub C (valtype_vectype vectype_1) (valtype_vectype vectype_2)
  | ref : forall (C : context) (reftype_1 : reftype) (reftype_2 : reftype), 
    (Reftype_sub C reftype_1 reftype_2) ->
    Valtype_sub C (valtype_reftype reftype_1) (valtype_reftype reftype_2)
  | bot : forall (C : context) (v_valtype : valtype), Valtype_sub C .BOT v_valtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:116.1-116.115 -/
inductive Resulttype_sub : context -> resulttype -> resulttype -> Prop where
  | mk_Resulttype_sub : forall (C : context) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((List.length t_1_lst) == (List.length t_2_lst)) ->
    Forall₂ (fun (t_1 : valtype) (t_2 : valtype) => (Valtype_sub C t_1 t_2)) t_1_lst t_2_lst ->
    Resulttype_sub C (.mk_list t_1_lst) (.mk_list t_2_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:134.1-134.119 -/
inductive Storagetype_sub : context -> storagetype -> storagetype -> Prop where
  | val : forall (C : context) (valtype_1 : valtype) (valtype_2 : valtype), 
    (Valtype_sub C valtype_1 valtype_2) ->
    Storagetype_sub C (storagetype_valtype valtype_1) (storagetype_valtype valtype_2)
  | pack : forall (C : context) (packtype_1 : packtype) (packtype_2 : packtype), 
    (Packtype_sub C packtype_1 packtype_2) ->
    Storagetype_sub C (storagetype_packtype packtype_1) (storagetype_packtype packtype_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:135.1-135.117 -/
inductive Fieldtype_sub : context -> fieldtype -> fieldtype -> Prop where
  | const : forall (C : context) (zt_1 : storagetype) (zt_2 : storagetype), 
    (Storagetype_sub C zt_1 zt_2) ->
    Fieldtype_sub C (.mk_fieldtype none zt_1) (.mk_fieldtype none zt_2)
  | var : forall (C : context) (zt_1 : storagetype) (zt_2 : storagetype), 
    (Storagetype_sub C zt_1 zt_2) ->
    (Storagetype_sub C zt_2 zt_1) ->
    Fieldtype_sub C (.mk_fieldtype (some .MUT) zt_1) (.mk_fieldtype (some .MUT) zt_2)

end

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:50.1-50.99 -/
inductive Instrtype_ok : context -> instrtype -> Prop where
  | mk_Instrtype_ok : forall (C : context) (t_1_lst : (List valtype)) (x_lst : (List idx)) (t_2_lst : (List valtype)) (lct_lst : (List localtype)), 
    (Resulttype_ok C (.mk_list t_1_lst)) ->
    (Resulttype_ok C (.mk_list t_2_lst)) ->
    ((List.length lct_lst) == (List.length x_lst)) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length (C.LOCALS)))) x_lst ->
    Forall₂ (fun (lct : localtype) (x : idx) => (((C.LOCALS)[(proj_uN_0 x)]!) == lct)) lct_lst x_lst ->
    Instrtype_ok C (.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:68.1-69.70 -/
inductive Expand_use : typeuse -> context -> comptype -> Prop where
  | deftype : forall (v_deftype : deftype) (C : context) (v_comptype : comptype), 
    (Expand v_deftype v_comptype) ->
    Expand_use (typeuse_deftype v_deftype) C v_comptype
  | typeidx : forall (v_typeidx : typeidx) (C : context) (v_comptype : comptype), 
    ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 v_typeidx)]!) v_comptype) ->
    Expand_use (._IDX v_typeidx) C v_comptype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:201.1-201.120 -/
inductive Limits_ok : context -> limits -> Nat -> Prop where
  | mk_Limits_ok : forall (C : context) (v_n : n) (m_opt : (Option m)) (k : Nat), 
    (v_n <= k) ->
    Forall (fun (v_m : Nat) => ((v_n <= v_m) && (v_m <= k))) (Option.toList m_opt) ->
    Limits_ok C (.mk_limits (.mk_uN v_n) (Option.map (fun (v_m : m) => (.mk_uN v_m)) m_opt)) k

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:202.1-202.97 -/
inductive Tagtype_ok : context -> tagtype -> Prop where
  | mk_Tagtype_ok : forall (C : context) (v_typeuse : typeuse) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Typeuse_ok C v_typeuse) ->
    (Expand_use v_typeuse C (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Tagtype_ok C v_typeuse

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:203.1-203.100 -/
inductive Globaltype_ok : context -> globaltype -> Prop where
  | mk_Globaltype_ok : forall (C : context) (t : valtype), 
    (Valtype_ok C t) ->
    Globaltype_ok C (.mk_globaltype (some .MUT) t)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:204.1-204.97 -/
inductive Memtype_ok : context -> memtype -> Prop where
  | mk_Memtype_ok : forall (C : context) (v_addrtype : addrtype) (v_limits : limits), 
    (Limits_ok C v_limits (2 ^ 16)) ->
    Memtype_ok C (.PAGE v_addrtype v_limits)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:205.1-205.99 -/
inductive Tabletype_ok : context -> tabletype -> Prop where
  | mk_Tabletype_ok : forall (C : context) (v_addrtype : addrtype) (v_limits : limits) (v_reftype : reftype), 
    (Limits_ok C v_limits ((((2 ^ 32) : Nat) - (1 : Nat)) : Nat)) ->
    (Reftype_ok C v_reftype) ->
    Tabletype_ok C (.mk_tabletype v_addrtype v_limits v_reftype)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.1-validation.types.spectec:206.1-206.100 -/
inductive Externtype_ok : context -> externtype -> Prop where
  | tag : forall (C : context) (v_tagtype : tagtype), 
    (Tagtype_ok C v_tagtype) ->
    Externtype_ok C (.TAG v_tagtype)
  | global : forall (C : context) (v_globaltype : globaltype), 
    (Globaltype_ok C v_globaltype) ->
    Externtype_ok C (.GLOBAL v_globaltype)
  | mem : forall (C : context) (v_memtype : memtype), 
    (Memtype_ok C v_memtype) ->
    Externtype_ok C (.MEM v_memtype)
  | table : forall (C : context) (v_tabletype : tabletype), 
    (Tabletype_ok C v_tabletype) ->
    Externtype_ok C (.TABLE v_tabletype)
  | func : forall (C : context) (v_typeuse : typeuse) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Typeuse_ok C v_typeuse) ->
    (Expand_use v_typeuse C (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Externtype_ok C (.FUNC v_typeuse)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:117.1-117.114 -/
inductive Instrtype_sub : context -> instrtype -> instrtype -> Prop where
  | mk_Instrtype_sub : forall (C : context) (t_11_lst : (List valtype)) (x_1_lst : (List idx)) (t_12_lst : (List valtype)) (t_21_lst : (List valtype)) (x_2_lst : (List idx)) (t_22_lst : (List valtype)) (x_lst : (List idx)) (t_lst : (List valtype)), 
    (Resulttype_sub C (.mk_list t_21_lst) (.mk_list t_11_lst)) ->
    (Resulttype_sub C (.mk_list t_12_lst) (.mk_list t_22_lst)) ->
    (x_lst == (setminus_ localidx x_2_lst x_1_lst)) ->
    ((List.length t_lst) == (List.length x_lst)) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length (C.LOCALS)))) x_lst ->
    Forall₂ (fun (t : valtype) (x : idx) => (((C.LOCALS)[(proj_uN_0 x)]!) == (.mk_localtype .SET t))) t_lst x_lst ->
    Instrtype_sub C (.mk_instrtype (.mk_list t_11_lst) x_1_lst (.mk_list t_12_lst)) (.mk_instrtype (.mk_list t_21_lst) x_2_lst (.mk_list t_22_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:191.1-191.110 -/
inductive Limits_sub : context -> limits -> limits -> Prop where
  | max : forall (C : context) (n_1 : n) (m_1 : m) (n_2 : n) (m_2_opt : (Option m)), 
    (n_1 >= n_2) ->
    Forall (fun (m_2 : Nat) => (m_1 <= m_2)) (Option.toList m_2_opt) ->
    Limits_sub C (.mk_limits (.mk_uN n_1) (some (.mk_uN m_1))) (.mk_limits (.mk_uN n_2) (Option.map (fun (m_2 : m) => (.mk_uN m_2)) m_2_opt))
  | eps : forall (C : context) (n_1 : n) (n_2 : n), 
    (n_1 >= n_2) ->
    Limits_sub C (.mk_limits (.mk_uN n_1) none) (.mk_limits (.mk_uN n_2) none)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:192.1-192.111 -/
inductive Tagtype_sub : context -> tagtype -> tagtype -> Prop where
  | mk_Tagtype_sub : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype), 
    (Deftype_sub C deftype_1 deftype_2) ->
    (Deftype_sub C deftype_2 deftype_1) ->
    Tagtype_sub C (typeuse_deftype deftype_1) (typeuse_deftype deftype_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:193.1-193.114 -/
inductive Globaltype_sub : context -> globaltype -> globaltype -> Prop where
  | const : forall (C : context) (valtype_1 : valtype) (valtype_2 : valtype), 
    (Valtype_sub C valtype_1 valtype_2) ->
    Globaltype_sub C (.mk_globaltype none valtype_1) (.mk_globaltype none valtype_2)
  | var : forall (C : context) (valtype_1 : valtype) (valtype_2 : valtype), 
    (Valtype_sub C valtype_1 valtype_2) ->
    (Valtype_sub C valtype_2 valtype_1) ->
    Globaltype_sub C (.mk_globaltype (some .MUT) valtype_1) (.mk_globaltype (some .MUT) valtype_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:194.1-194.111 -/
inductive Memtype_sub : context -> memtype -> memtype -> Prop where
  | mk_Memtype_sub : forall (C : context) (v_addrtype : addrtype) (limits_1 : limits) (limits_2 : limits), 
    (Limits_sub C limits_1 limits_2) ->
    Memtype_sub C (.PAGE v_addrtype limits_1) (.PAGE v_addrtype limits_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:195.1-195.113 -/
inductive Tabletype_sub : context -> tabletype -> tabletype -> Prop where
  | mk_Tabletype_sub : forall (C : context) (v_addrtype : addrtype) (limits_1 : limits) (reftype_1 : reftype) (limits_2 : limits) (reftype_2 : reftype), 
    (Limits_sub C limits_1 limits_2) ->
    (Reftype_sub C reftype_1 reftype_2) ->
    (Reftype_sub C reftype_2 reftype_1) ->
    Tabletype_sub C (.mk_tabletype v_addrtype limits_1 reftype_1) (.mk_tabletype v_addrtype limits_2 reftype_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.2-validation.subtyping.spectec:196.1-196.114 -/
inductive Externtype_sub : context -> externtype -> externtype -> Prop where
  | tag : forall (C : context) (tagtype_1 : tagtype) (tagtype_2 : tagtype), 
    (Tagtype_sub C tagtype_1 tagtype_2) ->
    Externtype_sub C (.TAG tagtype_1) (.TAG tagtype_2)
  | global : forall (C : context) (globaltype_1 : globaltype) (globaltype_2 : globaltype), 
    (Globaltype_sub C globaltype_1 globaltype_2) ->
    Externtype_sub C (.GLOBAL globaltype_1) (.GLOBAL globaltype_2)
  | mem : forall (C : context) (memtype_1 : memtype) (memtype_2 : memtype), 
    (Memtype_sub C memtype_1 memtype_2) ->
    Externtype_sub C (.MEM memtype_1) (.MEM memtype_2)
  | table : forall (C : context) (tabletype_1 : tabletype) (tabletype_2 : tabletype), 
    (Tabletype_sub C tabletype_1 tabletype_2) ->
    Externtype_sub C (.TABLE tabletype_1) (.TABLE tabletype_2)
  | func : forall (C : context) (deftype_1 : deftype) (deftype_2 : deftype), 
    (Deftype_sub C deftype_1 deftype_2) ->
    Externtype_sub C (.FUNC (typeuse_deftype deftype_1)) (.FUNC (typeuse_deftype deftype_2))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:42.1-42.121 -/
inductive Blocktype_ok : context -> blocktype -> instrtype -> Prop where
  | valtype : forall (C : context) (valtype_opt : (Option valtype)), 
    Forall (fun (v_valtype : valtype) => (Valtype_ok C v_valtype)) (Option.toList valtype_opt) ->
    Blocktype_ok C (._RESULT valtype_opt) (.mk_instrtype (.mk_list []) [] (.mk_list (Option.toList valtype_opt)))
  | typeidx : forall (C : context) (v_typeidx : typeidx) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 v_typeidx)]!) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Blocktype_ok C (._IDX v_typeidx) (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:164.1-164.77 -/
inductive Catch_ok : context -> «catch» -> Prop where
  | «catch» : forall (C : context) (x : idx) (l : labelidx) (t_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.TAGS))) ->
    (Expand (as_deftype ((C.TAGS)[(proj_uN_0 x)]!)) (.FUNC (.mk_list t_lst) (.mk_list []))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (Resulttype_sub C (.mk_list t_lst) ((C.LABELS)[(proj_uN_0 l)]!)) ->
    Catch_ok C (.CATCH x l)
  | catch_ref : forall (C : context) (x : idx) (l : labelidx) (t_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.TAGS))) ->
    (Expand (as_deftype ((C.TAGS)[(proj_uN_0 x)]!)) (.FUNC (.mk_list t_lst) (.mk_list []))) ->
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (Resulttype_sub C (.mk_list (t_lst ++ [(.REF none .EXN)])) ((C.LABELS)[(proj_uN_0 l)]!)) ->
    Catch_ok C (.CATCH_REF x l)
  | catch_all : forall (C : context) (l : labelidx), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (Resulttype_sub C (.mk_list []) ((C.LABELS)[(proj_uN_0 l)]!)) ->
    Catch_ok C (.CATCH_ALL l)
  | catch_all_ref : forall (C : context) (l : labelidx), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (Resulttype_sub C (.mk_list [(.REF none .EXN)]) ((C.LABELS)[(proj_uN_0 l)]!)) ->
    Catch_ok C (.CATCH_ALL_REF l)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:7.1-7.30 -/
def default_ : ∀  (v_valtype : valtype) , (Option val)
  | .I32 =>
    (some (.CONST (numtype_addrtype .I32) (.mk_num__0 .I32 (.mk_uN 0))))
  | .I64 =>
    (some (.CONST (numtype_addrtype .I64) (.mk_num__0 .I64 (.mk_uN 0))))
  | .F32 =>
    (some (.CONST (numtype_Fnn .F32) (.mk_num__1 .F32 (fzero (size (numtype_Fnn .F32))))))
  | .F64 =>
    (some (.CONST (numtype_Fnn .F64) (.mk_num__1 .F64 (fzero (size (numtype_Fnn .F64))))))
  | .V128 =>
    (some (.VCONST .V128 (.mk_uN 0)))
  | (.REF (some .NULL) ht) =>
    (some (.REF_NULL ht))
  | (.REF none ht) =>
    none


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:9.1-10.71 -/
inductive Defaultable : valtype -> Prop where
  | mk_Defaultable : forall (t : valtype), 
    ((default_ t) != none) ->
    Defaultable t

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:408.1-408.131 -/
inductive Memarg_ok : memarg -> addrtype -> N -> Prop where
  | mk_Memarg_ok : forall (v_n : n) (v_m : m) («at» : addrtype) (v_N : N), 
    (((2 ^ v_n) : Nat) <= ((v_N : Nat) / (8 : Nat))) ->
    (v_m < (2 ^ (size (numtype_addrtype «at»)))) ->
    Memarg_ok { ALIGN := (.mk_uN v_n), OFFSET := (.mk_uN v_m) } «at» v_N

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:255.1-255.111 -/
def is_packtype : ∀  (v_storagetype : storagetype) , Bool
  | zt =>
    (zt == (storagetype_valtype (unpack zt)))


/- Recursive Definitions at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:5.1-6.96 -/
mutual
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:5.1-5.95 -/
inductive Instr_ok : context -> instr -> instrtype -> Prop where
  | nop : forall (C : context), Instr_ok C .NOP (.mk_instrtype (.mk_list []) [] (.mk_list []))
  | unreachable : forall (C : context) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Instrtype_ok C (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    Instr_ok C .UNREACHABLE (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | drop : forall (C : context) (t : valtype), 
    (Valtype_ok C t) ->
    Instr_ok C .DROP (.mk_instrtype (.mk_list [t]) [] (.mk_list []))
  | select_expl : forall (C : context) (t : valtype), 
    (Valtype_ok C t) ->
    Instr_ok C (.SELECT (some [t])) (.mk_instrtype (.mk_list [t, t, .I32]) [] (.mk_list [t]))
  | select_impl : forall (C : context) (t : valtype) (t' : valtype) (v_numtype : numtype) (v_vectype : vectype), 
    (Valtype_ok C t) ->
    (Valtype_sub C t t') ->
    ((t' == (valtype_numtype v_numtype)) || (t' == (valtype_vectype v_vectype))) ->
    Instr_ok C (.SELECT none) (.mk_instrtype (.mk_list [t, t, .I32]) [] (.mk_list [t]))
  | block : forall (C : context) (bt : blocktype) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (x_lst : (List idx)), 
    (Blocktype_ok C bt (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(.mk_list t_2_lst)], RETURN := none, REFS := [] } ++ C) instr_lst (.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst))) ->
    Instr_ok C (.BLOCK bt instr_lst) (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | loop : forall (C : context) (bt : blocktype) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (x_lst : (List idx)), 
    (Blocktype_ok C bt (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(.mk_list t_1_lst)], RETURN := none, REFS := [] } ++ C) instr_lst (.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst))) ->
    Instr_ok C (.LOOP bt instr_lst) (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | if : forall (C : context) (bt : blocktype) (instr_1_lst : (List instr)) (instr_2_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (x_1_lst : (List idx)) (x_2_lst : (List idx)), 
    (Blocktype_ok C bt (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(.mk_list t_2_lst)], RETURN := none, REFS := [] } ++ C) instr_1_lst (.mk_instrtype (.mk_list t_1_lst) x_1_lst (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(.mk_list t_2_lst)], RETURN := none, REFS := [] } ++ C) instr_2_lst (.mk_instrtype (.mk_list t_1_lst) x_2_lst (.mk_list t_2_lst))) ->
    Instr_ok C (.IFELSE bt instr_1_lst instr_2_lst) (.mk_instrtype (.mk_list (t_1_lst ++ [.I32])) [] (.mk_list t_2_lst))
  | br : forall (C : context) (l : labelidx) (t_1_lst : (List valtype)) (t_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    ((proj_list_0 valtype ((C.LABELS)[(proj_uN_0 l)]!)) == t_lst) ->
    (Instrtype_ok C (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    Instr_ok C (.BR l) (.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst))
  | br_if : forall (C : context) (l : labelidx) (t_lst : (List valtype)), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    ((proj_list_0 valtype ((C.LABELS)[(proj_uN_0 l)]!)) == t_lst) ->
    Instr_ok C (.BR_IF l) (.mk_instrtype (.mk_list (t_lst ++ [.I32])) [] (.mk_list t_lst))
  | br_table : forall (C : context) (l_lst : (List labelidx)) (l' : labelidx) (t_1_lst : (List valtype)) (t_lst : (List valtype)) (t_2_lst : (List valtype)), 
    Forall (fun (l : labelidx) => ((proj_uN_0 l) < (List.length (C.LABELS)))) l_lst ->
    Forall (fun (l : labelidx) => (Resulttype_sub C (.mk_list t_lst) ((C.LABELS)[(proj_uN_0 l)]!))) l_lst ->
    ((proj_uN_0 l') < (List.length (C.LABELS))) ->
    (Resulttype_sub C (.mk_list t_lst) ((C.LABELS)[(proj_uN_0 l')]!)) ->
    (Instrtype_ok C (.mk_instrtype (.mk_list (t_1_lst ++ (t_lst ++ [.I32]))) [] (.mk_list t_2_lst))) ->
    Instr_ok C (.BR_TABLE l_lst l') (.mk_instrtype (.mk_list (t_1_lst ++ (t_lst ++ [.I32]))) [] (.mk_list t_2_lst))
  | br_on_null : forall (C : context) (l : labelidx) (t_lst : (List valtype)) (ht : heaptype), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    ((proj_list_0 valtype ((C.LABELS)[(proj_uN_0 l)]!)) == t_lst) ->
    (Heaptype_ok C ht) ->
    Instr_ok C (.BR_ON_NULL l) (.mk_instrtype (.mk_list (t_lst ++ [(.REF (some .NULL) ht)])) [] (.mk_list (t_lst ++ [(.REF none ht)])))
  | br_on_non_null : forall (C : context) (l : labelidx) (t_lst : (List valtype)) (ht : heaptype), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (((C.LABELS)[(proj_uN_0 l)]!) == (.mk_list (t_lst ++ [(.REF (some .NULL) ht)]))) ->
    Instr_ok C (.BR_ON_NON_NULL l) (.mk_instrtype (.mk_list (t_lst ++ [(.REF (some .NULL) ht)])) [] (.mk_list t_lst))
  | br_on_cast : forall (C : context) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (t_lst : (List valtype)) (rt : reftype), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (((C.LABELS)[(proj_uN_0 l)]!) == (.mk_list (t_lst ++ [(valtype_reftype rt)]))) ->
    (Reftype_ok C rt_1) ->
    (Reftype_ok C rt_2) ->
    (Reftype_sub C rt_2 rt_1) ->
    (Reftype_sub C rt_2 rt) ->
    Instr_ok C (.BR_ON_CAST l rt_1 rt_2) (.mk_instrtype (.mk_list (t_lst ++ [(valtype_reftype rt_1)])) [] (.mk_list (t_lst ++ [(valtype_reftype (diffrt rt_1 rt_2))])))
  | br_on_cast_fail : forall (C : context) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (t_lst : (List valtype)) (rt : reftype), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (((C.LABELS)[(proj_uN_0 l)]!) == (.mk_list (t_lst ++ [(valtype_reftype rt)]))) ->
    (Reftype_ok C rt_1) ->
    (Reftype_ok C rt_2) ->
    (Reftype_sub C rt_2 rt_1) ->
    (Reftype_sub C (diffrt rt_1 rt_2) rt) ->
    Instr_ok C (.BR_ON_CAST_FAIL l rt_1 rt_2) (.mk_instrtype (.mk_list (t_lst ++ [(valtype_reftype rt_1)])) [] (.mk_list (t_lst ++ [(valtype_reftype rt_2)])))
  | call : forall (C : context) (x : idx) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (Expand ((C.FUNCS)[(proj_uN_0 x)]!) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instr_ok C (.CALL x) (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | call_ref : forall (C : context) (x : idx) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instr_ok C (.CALL_REF (._IDX x)) (.mk_instrtype (.mk_list (t_1_lst ++ [(.REF (some .NULL) (._IDX x))])) [] (.mk_list t_2_lst))
  | call_indirect : forall (C : context) (x : idx) (y : idx) (t_1_lst : (List valtype)) («at» : addrtype) (t_2_lst : (List valtype)) (lim : limits) (rt : reftype), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt)) ->
    (Reftype_sub C rt (.REF (some .NULL) .FUNC)) ->
    ((proj_uN_0 y) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 y)]!) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instr_ok C (.CALL_INDIRECT x (._IDX y)) (.mk_instrtype (.mk_list (t_1_lst ++ [(valtype_addrtype «at»)])) [] (.mk_list t_2_lst))
  | return : forall (C : context) (t_1_lst : (List valtype)) (t_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((C.RETURN) == (some (.mk_list t_lst))) ->
    (Instrtype_ok C (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    Instr_ok C .RETURN (.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst))
  | return_call : forall (C : context) (x : idx) (t_3_lst : (List valtype)) (t_1_lst : (List valtype)) (t_4_lst : (List valtype)) (t_2_lst : (List valtype)) (t'_2_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (Expand ((C.FUNCS)[(proj_uN_0 x)]!) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    ((C.RETURN) == (some (.mk_list t'_2_lst))) ->
    (Resulttype_sub C (.mk_list t_2_lst) (.mk_list t'_2_lst)) ->
    (Instrtype_ok C (.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst))) ->
    Instr_ok C (.RETURN_CALL x) (.mk_instrtype (.mk_list (t_3_lst ++ t_1_lst)) [] (.mk_list t_4_lst))
  | return_call_ref : forall (C : context) (x : idx) (t_3_lst : (List valtype)) (t_1_lst : (List valtype)) (t_4_lst : (List valtype)) (t_2_lst : (List valtype)) (t'_2_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    ((C.RETURN) == (some (.mk_list t'_2_lst))) ->
    (Resulttype_sub C (.mk_list t_2_lst) (.mk_list t'_2_lst)) ->
    (Instrtype_ok C (.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst))) ->
    Instr_ok C (.RETURN_CALL_REF (._IDX x)) (.mk_instrtype (.mk_list (t_3_lst ++ (t_1_lst ++ [(.REF (some .NULL) (._IDX x))]))) [] (.mk_list t_4_lst))
  | return_call_indirect : forall (C : context) (x : idx) (y : idx) (t_3_lst : (List valtype)) (t_1_lst : (List valtype)) («at» : addrtype) (t_4_lst : (List valtype)) (lim : limits) (rt : reftype) (t_2_lst : (List valtype)) (t'_2_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt)) ->
    (Reftype_sub C rt (.REF (some .NULL) .FUNC)) ->
    ((proj_uN_0 y) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 y)]!) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    ((C.RETURN) == (some (.mk_list t'_2_lst))) ->
    (Resulttype_sub C (.mk_list t_2_lst) (.mk_list t'_2_lst)) ->
    (Instrtype_ok C (.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst))) ->
    Instr_ok C (.RETURN_CALL_INDIRECT x (._IDX y)) (.mk_instrtype (.mk_list (t_3_lst ++ (t_1_lst ++ [(valtype_addrtype «at»)]))) [] (.mk_list t_4_lst))
  | throw : forall (C : context) (x : idx) (t_1_lst : (List valtype)) (t_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.TAGS))) ->
    (Expand (as_deftype ((C.TAGS)[(proj_uN_0 x)]!)) (.FUNC (.mk_list t_lst) (.mk_list []))) ->
    (Instrtype_ok C (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    Instr_ok C (.THROW x) (.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst))
  | throw_ref : forall (C : context) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Instrtype_ok C (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    Instr_ok C .THROW_REF (.mk_instrtype (.mk_list (t_1_lst ++ [(.REF (some .NULL) .EXN)])) [] (.mk_list t_2_lst))
  | try_table : forall (C : context) (bt : blocktype) (catch_lst : (List «catch»)) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (x_lst : (List idx)), 
    (Blocktype_ok C bt (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [(.mk_list t_2_lst)], RETURN := none, REFS := [] } ++ C) instr_lst (.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst))) ->
    Forall (fun (v_catch : «catch») => (Catch_ok C v_catch)) catch_lst ->
    Instr_ok C (.TRY_TABLE bt (.mk_list catch_lst) instr_lst) (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | ref_null : forall (C : context) (ht : heaptype), 
    (Heaptype_ok C ht) ->
    Instr_ok C (.REF_NULL ht) (.mk_instrtype (.mk_list []) [] (.mk_list [(.REF (some .NULL) ht)]))
  | ref_func : forall (C : context) (x : idx) (dt : deftype), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == dt) ->
    ((List.length (C.REFS)) > 0) ->
    (List.contains (C.REFS) x) ->
    Instr_ok C (.REF_FUNC x) (.mk_instrtype (.mk_list []) [] (.mk_list [(.REF none (heaptype_deftype dt))]))
  | ref_i31 : forall (C : context), Instr_ok C .REF_I31 (.mk_instrtype (.mk_list [.I32]) [] (.mk_list [(.REF none .I31)]))
  | ref_is_null : forall (C : context) (ht : heaptype), 
    (Heaptype_ok C ht) ->
    Instr_ok C .REF_IS_NULL (.mk_instrtype (.mk_list [(.REF (some .NULL) ht)]) [] (.mk_list [.I32]))
  | ref_as_non_null : forall (C : context) (ht : heaptype), 
    (Heaptype_ok C ht) ->
    Instr_ok C .REF_AS_NON_NULL (.mk_instrtype (.mk_list [(.REF (some .NULL) ht)]) [] (.mk_list [(.REF none ht)]))
  | ref_eq : forall (C : context), Instr_ok C .REF_EQ (.mk_instrtype (.mk_list [(.REF (some .NULL) .EQ), (.REF (some .NULL) .EQ)]) [] (.mk_list [.I32]))
  | ref_test : forall (C : context) (rt : reftype) (rt' : reftype), 
    (Reftype_ok C rt) ->
    (Reftype_ok C rt') ->
    (Reftype_sub C rt rt') ->
    Instr_ok C (.REF_TEST rt) (.mk_instrtype (.mk_list [(valtype_reftype rt')]) [] (.mk_list [.I32]))
  | ref_cast : forall (C : context) (rt : reftype) (rt' : reftype), 
    (Reftype_ok C rt) ->
    (Reftype_ok C rt') ->
    (Reftype_sub C rt rt') ->
    Instr_ok C (.REF_CAST rt) (.mk_instrtype (.mk_list [(valtype_reftype rt')]) [] (.mk_list [(valtype_reftype rt)]))
  | i31_get : forall (C : context) (v_sx : sx), Instr_ok C (.I31_GET v_sx) (.mk_instrtype (.mk_list [(.REF (some .NULL) .I31)]) [] (.mk_list [.I32]))
  | struct_new : forall (C : context) (x : idx) (zt_lst : (List storagetype)) (mut_opt_lst : (List (Option «mut»))), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => (.mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ->
    Instr_ok C (.STRUCT_NEW x) (.mk_instrtype (.mk_list (List.map (fun (zt : storagetype) => (unpack zt)) zt_lst)) [] (.mk_list [(.REF none (._IDX x))]))
  | struct_new_default : forall (C : context) (x : idx) (mut_opt_lst : (List (Option «mut»))) (zt_lst : (List storagetype)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => (.mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ->
    Forall (fun (zt : storagetype) => (Defaultable (unpack zt))) zt_lst ->
    Instr_ok C (.STRUCT_NEW_DEFAULT x) (.mk_instrtype (.mk_list []) [] (.mk_list [(.REF none (._IDX x))]))
  | struct_get : forall (C : context) (sx_opt : (Option sx)) (x : idx) (i : u32) (zt : storagetype) (ft_lst : (List fieldtype)) (mut_opt : (Option «mut»)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.STRUCT (.mk_list ft_lst))) ->
    ((proj_uN_0 i) < (List.length ft_lst)) ->
    ((ft_lst[(proj_uN_0 i)]!) == (.mk_fieldtype mut_opt zt)) ->
    ((sx_opt == none) <-> (is_packtype zt)) ->
    Instr_ok C (.STRUCT_GET sx_opt x i) (.mk_instrtype (.mk_list [(.REF (some .NULL) (._IDX x))]) [] (.mk_list [(unpack zt)]))
  | struct_set : forall (C : context) (x : idx) (i : u32) (zt : storagetype) (ft_lst : (List fieldtype)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.STRUCT (.mk_list ft_lst))) ->
    ((proj_uN_0 i) < (List.length ft_lst)) ->
    ((ft_lst[(proj_uN_0 i)]!) == (.mk_fieldtype (some .MUT) zt)) ->
    Instr_ok C (.STRUCT_SET x i) (.mk_instrtype (.mk_list [(.REF (some .NULL) (._IDX x)), (unpack zt)]) [] (.mk_list []))
  | array_new : forall (C : context) (x : idx) (zt : storagetype) (mut_opt : (Option «mut»)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    Instr_ok C (.ARRAY_NEW x) (.mk_instrtype (.mk_list [(unpack zt), .I32]) [] (.mk_list [(.REF none (._IDX x))]))
  | array_new_default : forall (C : context) (x : idx) (mut_opt : (Option «mut»)) (zt : storagetype), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    (Defaultable (unpack zt)) ->
    Instr_ok C (.ARRAY_NEW_DEFAULT x) (.mk_instrtype (.mk_list [.I32]) [] (.mk_list [(.REF none (._IDX x))]))
  | array_new_fixed : forall (C : context) (x : idx) (v_n : n) (zt : storagetype) (mut_opt : (Option «mut»)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    Instr_ok C (.ARRAY_NEW_FIXED x (.mk_uN v_n)) (.mk_instrtype (.mk_list (List.replicate v_n (unpack zt))) [] (.mk_list [(.REF none (._IDX x))]))
  | array_new_elem : forall (C : context) (x : idx) (y : idx) (mut_opt : (Option «mut»)) (rt : reftype), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype mut_opt (storagetype_reftype rt)))) ->
    ((proj_uN_0 y) < (List.length (C.ELEMS))) ->
    (Reftype_sub C ((C.ELEMS)[(proj_uN_0 y)]!) rt) ->
    Instr_ok C (.ARRAY_NEW_ELEM x y) (.mk_instrtype (.mk_list [.I32, .I32]) [] (.mk_list [(.REF none (._IDX x))]))
  | array_new_data : forall (C : context) (x : idx) (y : idx) (mut_opt : (Option «mut»)) (zt : storagetype) (v_numtype : numtype) (v_vectype : vectype), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    (((unpack zt) == (valtype_numtype v_numtype)) || ((unpack zt) == (valtype_vectype v_vectype))) ->
    ((proj_uN_0 y) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 y)]!) == .OK) ->
    Instr_ok C (.ARRAY_NEW_DATA x y) (.mk_instrtype (.mk_list [.I32, .I32]) [] (.mk_list [(.REF none (._IDX x))]))
  | array_get : forall (C : context) (sx_opt : (Option sx)) (x : idx) (zt : storagetype) (mut_opt : (Option «mut»)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((sx_opt == none) <-> (is_packtype zt)) ->
    Instr_ok C (.ARRAY_GET sx_opt x) (.mk_instrtype (.mk_list [(.REF (some .NULL) (._IDX x)), .I32]) [] (.mk_list [(unpack zt)]))
  | array_set : forall (C : context) (x : idx) (zt : storagetype), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype (some .MUT) zt))) ->
    Instr_ok C (.ARRAY_SET x) (.mk_instrtype (.mk_list [(.REF (some .NULL) (._IDX x)), .I32, (unpack zt)]) [] (.mk_list []))
  | array_len : forall (C : context), Instr_ok C .ARRAY_LEN (.mk_instrtype (.mk_list [(.REF (some .NULL) .ARRAY)]) [] (.mk_list [.I32]))
  | array_fill : forall (C : context) (x : idx) (zt : storagetype), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype (some .MUT) zt))) ->
    Instr_ok C (.ARRAY_FILL x) (.mk_instrtype (.mk_list [(.REF (some .NULL) (._IDX x)), .I32, (unpack zt), .I32]) [] (.mk_list []))
  | array_copy : forall (C : context) (x_1 : idx) (x_2 : idx) (zt_1 : storagetype) (mut_opt : (Option «mut»)) (zt_2 : storagetype), 
    ((proj_uN_0 x_1) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x_1)]!) (.ARRAY (.mk_fieldtype (some .MUT) zt_1))) ->
    ((proj_uN_0 x_2) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x_2)]!) (.ARRAY (.mk_fieldtype mut_opt zt_2))) ->
    (Storagetype_sub C zt_2 zt_1) ->
    Instr_ok C (.ARRAY_COPY x_1 x_2) (.mk_instrtype (.mk_list [(.REF (some .NULL) (._IDX x_1)), .I32, (.REF (some .NULL) (._IDX x_2)), .I32, .I32]) [] (.mk_list []))
  | array_init_elem : forall (C : context) (x : idx) (y : idx) (zt : storagetype), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype (some .MUT) zt))) ->
    ((proj_uN_0 y) < (List.length (C.ELEMS))) ->
    (Storagetype_sub C (storagetype_reftype ((C.ELEMS)[(proj_uN_0 y)]!)) zt) ->
    Instr_ok C (.ARRAY_INIT_ELEM x y) (.mk_instrtype (.mk_list [(.REF (some .NULL) (._IDX x)), .I32, .I32, .I32]) [] (.mk_list []))
  | array_init_data : forall (C : context) (x : idx) (y : idx) (zt : storagetype) (v_numtype : numtype) (v_vectype : vectype), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.ARRAY (.mk_fieldtype (some .MUT) zt))) ->
    (((unpack zt) == (valtype_numtype v_numtype)) || ((unpack zt) == (valtype_vectype v_vectype))) ->
    ((proj_uN_0 y) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 y)]!) == .OK) ->
    Instr_ok C (.ARRAY_INIT_DATA x y) (.mk_instrtype (.mk_list [(.REF (some .NULL) (._IDX x)), .I32, .I32, .I32]) [] (.mk_list []))
  | extern_convert_any : forall (C : context) (null_1_opt : (Option null)) (null_2_opt : (Option null)), 
    (null_1_opt == null_2_opt) ->
    Instr_ok C .EXTERN_CONVERT_ANY (.mk_instrtype (.mk_list [(.REF null_1_opt .ANY)]) [] (.mk_list [(.REF null_2_opt .EXTERN)]))
  | any_convert_extern : forall (C : context) (null_1_opt : (Option null)) (null_2_opt : (Option null)), 
    (null_1_opt == null_2_opt) ->
    Instr_ok C .ANY_CONVERT_EXTERN (.mk_instrtype (.mk_list [(.REF null_1_opt .EXTERN)]) [] (.mk_list [(.REF null_2_opt .ANY)]))
  | local_get : forall (C : context) (x : idx) (t : valtype), 
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == (.mk_localtype .SET t)) ->
    Instr_ok C (.LOCAL_GET x) (.mk_instrtype (.mk_list []) [] (.mk_list [t]))
  | local_set : forall (C : context) (x : idx) (t : valtype) (v_init : init), 
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == (.mk_localtype v_init t)) ->
    Instr_ok C (.LOCAL_SET x) (.mk_instrtype (.mk_list [t]) [x] (.mk_list []))
  | local_tee : forall (C : context) (x : idx) (t : valtype) (v_init : init), 
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == (.mk_localtype v_init t)) ->
    Instr_ok C (.LOCAL_TEE x) (.mk_instrtype (.mk_list [t]) [x] (.mk_list [t]))
  | global_get : forall (C : context) (x : idx) (t : valtype) (mut_opt : (Option «mut»)), 
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype mut_opt t)) ->
    Instr_ok C (.GLOBAL_GET x) (.mk_instrtype (.mk_list []) [] (.mk_list [t]))
  | global_set : forall (C : context) (x : idx) (t : valtype), 
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype (some .MUT) t)) ->
    Instr_ok C (.GLOBAL_SET x) (.mk_instrtype (.mk_list [t]) [] (.mk_list []))
  | table_get : forall (C : context) (x : idx) («at» : addrtype) (rt : reftype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt)) ->
    Instr_ok C (.TABLE_GET x) (.mk_instrtype (.mk_list [(valtype_addrtype «at»)]) [] (.mk_list [(valtype_reftype rt)]))
  | table_set : forall (C : context) (x : idx) («at» : addrtype) (rt : reftype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt)) ->
    Instr_ok C (.TABLE_SET x) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), (valtype_reftype rt)]) [] (.mk_list []))
  | table_size : forall (C : context) (x : idx) («at» : addrtype) (lim : limits) (rt : reftype), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt)) ->
    Instr_ok C (.TABLE_SIZE x) (.mk_instrtype (.mk_list []) [] (.mk_list [(valtype_addrtype «at»)]))
  | table_grow : forall (C : context) (x : idx) (rt : reftype) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt)) ->
    Instr_ok C (.TABLE_GROW x) (.mk_instrtype (.mk_list [(valtype_reftype rt), (valtype_addrtype «at»)]) [] (.mk_list [.I32]))
  | table_fill : forall (C : context) (x : idx) («at» : addrtype) (rt : reftype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt)) ->
    Instr_ok C (.TABLE_FILL x) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), (valtype_reftype rt), (valtype_addrtype «at»)]) [] (.mk_list []))
  | table_copy : forall (C : context) (x_1 : idx) (x_2 : idx) (at_1 : addrtype) (at_2 : addrtype) (lim_1 : limits) (rt_1 : reftype) (lim_2 : limits) (rt_2 : reftype), 
    ((proj_uN_0 x_1) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x_1)]!) == (.mk_tabletype at_1 lim_1 rt_1)) ->
    ((proj_uN_0 x_2) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x_2)]!) == (.mk_tabletype at_2 lim_2 rt_2)) ->
    (Reftype_sub C rt_2 rt_1) ->
    Instr_ok C (.TABLE_COPY x_1 x_2) (.mk_instrtype (.mk_list [(valtype_addrtype at_1), (valtype_addrtype at_2), (valtype_addrtype (minat at_1 at_2))]) [] (.mk_list []))
  | table_init : forall (C : context) (x : idx) (y : idx) («at» : addrtype) (lim : limits) (rt_1 : reftype) (rt_2 : reftype), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt_1)) ->
    ((proj_uN_0 y) < (List.length (C.ELEMS))) ->
    (((C.ELEMS)[(proj_uN_0 y)]!) == rt_2) ->
    (Reftype_sub C rt_2 rt_1) ->
    Instr_ok C (.TABLE_INIT x y) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), .I32, .I32]) [] (.mk_list []))
  | elem_drop : forall (C : context) (x : idx) (rt : reftype), 
    ((proj_uN_0 x) < (List.length (C.ELEMS))) ->
    (((C.ELEMS)[(proj_uN_0 x)]!) == rt) ->
    Instr_ok C (.ELEM_DROP x) (.mk_instrtype (.mk_list []) [] (.mk_list []))
  | memory_size : forall (C : context) (x : idx) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    Instr_ok C (.MEMORY_SIZE x) (.mk_instrtype (.mk_list []) [] (.mk_list [(valtype_addrtype «at»)]))
  | memory_grow : forall (C : context) (x : idx) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    Instr_ok C (.MEMORY_GROW x) (.mk_instrtype (.mk_list [(valtype_addrtype «at»)]) [] (.mk_list [(valtype_addrtype «at»)]))
  | memory_fill : forall (C : context) (x : idx) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    Instr_ok C (.MEMORY_FILL x) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), .I32, (valtype_addrtype «at»)]) [] (.mk_list []))
  | memory_copy : forall (C : context) (x_1 : idx) (x_2 : idx) (at_1 : addrtype) (at_2 : addrtype) (lim_1 : limits) (lim_2 : limits), 
    ((proj_uN_0 x_1) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x_1)]!) == (.PAGE at_1 lim_1)) ->
    ((proj_uN_0 x_2) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x_2)]!) == (.PAGE at_2 lim_2)) ->
    Instr_ok C (.MEMORY_COPY x_1 x_2) (.mk_instrtype (.mk_list [(valtype_addrtype at_1), (valtype_addrtype at_2), (valtype_addrtype (minat at_1 at_2))]) [] (.mk_list []))
  | memory_init : forall (C : context) (x : idx) (y : idx) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    ((proj_uN_0 y) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 y)]!) == .OK) ->
    Instr_ok C (.MEMORY_INIT x y) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), .I32, .I32]) [] (.mk_list []))
  | data_drop : forall (C : context) (x : idx), 
    ((proj_uN_0 x) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 x)]!) == .OK) ->
    Instr_ok C (.DATA_DROP x) (.mk_instrtype (.mk_list []) [] (.mk_list []))
  | load_val : forall (C : context) (nt : numtype) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» (size nt)) ->
    Instr_ok C (.LOAD nt none x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»)]) [] (.mk_list [(valtype_numtype nt)]))
  | load_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» v_M) ->
    Instr_ok C (.LOAD (numtype_addrtype v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_M) v_sx))) x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»)]) [] (.mk_list [(valtype_addrtype v_Inn)]))
  | store_val : forall (C : context) (nt : numtype) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» (size nt)) ->
    Instr_ok C (.STORE nt none x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), (valtype_numtype nt)]) [] (.mk_list []))
  | store_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» v_M) ->
    Instr_ok C (.STORE (numtype_addrtype v_Inn) (some (.mk_storeop__0 v_Inn (.mk_storeop_Inn (.mk_sz v_M)))) x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), (valtype_addrtype v_Inn)]) [] (.mk_list []))
  | vload_val : forall (C : context) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» (vsize .V128)) ->
    Instr_ok C (.VLOAD .V128 none x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»)]) [] (.mk_list [.V128]))
  | vload_pack : forall (C : context) (v_M : M) (v_N : N) (v_sx : sx) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» (v_M * v_N)) ->
    Instr_ok C (.VLOAD .V128 (some (.SHAPEX_ (.mk_sz v_M) v_N v_sx)) x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»)]) [] (.mk_list [.V128]))
  | vload_splat : forall (C : context) (v_N : N) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» v_N) ->
    Instr_ok C (.VLOAD .V128 (some (.SPLAT (.mk_sz v_N))) x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»)]) [] (.mk_list [.V128]))
  | vload_zero : forall (C : context) (v_N : N) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» v_N) ->
    Instr_ok C (.VLOAD .V128 (some (.ZERO (.mk_sz v_N))) x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»)]) [] (.mk_list [.V128]))
  | vload_lane : forall (C : context) (v_N : N) (x : idx) (v_memarg : memarg) (i : laneidx) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» v_N) ->
    (((proj_uN_0 i) : Nat) < ((128 : Nat) / (v_N : Nat))) ->
    Instr_ok C (.VLOAD_LANE .V128 (.mk_sz v_N) x v_memarg i) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), .V128]) [] (.mk_list [.V128]))
  | vstore : forall (C : context) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» (vsize .V128)) ->
    Instr_ok C (.VSTORE .V128 x v_memarg) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), .V128]) [] (.mk_list []))
  | vstore_lane : forall (C : context) (v_N : N) (x : idx) (v_memarg : memarg) (i : laneidx) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Memarg_ok v_memarg «at» v_N) ->
    (((proj_uN_0 i) : Nat) < ((128 : Nat) / (v_N : Nat))) ->
    Instr_ok C (.VSTORE_LANE .V128 (.mk_sz v_N) x v_memarg i) (.mk_instrtype (.mk_list [(valtype_addrtype «at»), .V128]) [] (.mk_list []))
  | const : forall (C : context) (nt : numtype) (c_nt : num_), 
    (wf_num_ nt c_nt) ->
    Instr_ok C (.CONST nt c_nt) (.mk_instrtype (.mk_list []) [] (.mk_list [(valtype_numtype nt)]))
  | unop : forall (C : context) (nt : numtype) (unop_nt : unop_), 
    (wf_unop_ nt unop_nt) ->
    Instr_ok C (.UNOP nt unop_nt) (.mk_instrtype (.mk_list [(valtype_numtype nt)]) [] (.mk_list [(valtype_numtype nt)]))
  | binop : forall (C : context) (nt : numtype) (binop_nt : binop_), 
    (wf_binop_ nt binop_nt) ->
    Instr_ok C (.BINOP nt binop_nt) (.mk_instrtype (.mk_list [(valtype_numtype nt), (valtype_numtype nt)]) [] (.mk_list [(valtype_numtype nt)]))
  | testop : forall (C : context) (nt : numtype) (testop_nt : testop_), 
    (wf_testop_ nt testop_nt) ->
    Instr_ok C (.TESTOP nt testop_nt) (.mk_instrtype (.mk_list [(valtype_numtype nt)]) [] (.mk_list [.I32]))
  | relop : forall (C : context) (nt : numtype) (relop_nt : relop_), 
    (wf_relop_ nt relop_nt) ->
    Instr_ok C (.RELOP nt relop_nt) (.mk_instrtype (.mk_list [(valtype_numtype nt), (valtype_numtype nt)]) [] (.mk_list [.I32]))
  | cvtop : forall (C : context) (nt_1 : numtype) (nt_2 : numtype) (cvtop : cvtop__), 
    (wf_cvtop__ nt_2 nt_1 cvtop) ->
    Instr_ok C (.CVTOP nt_1 nt_2 cvtop) (.mk_instrtype (.mk_list [(valtype_numtype nt_2)]) [] (.mk_list [(valtype_numtype nt_1)]))
  | vconst : forall (C : context) (c : vec_), Instr_ok C (.VCONST .V128 c) (.mk_instrtype (.mk_list []) [] (.mk_list [.V128]))
  | vvunop : forall (C : context) (v_vvunop : vvunop), Instr_ok C (.VVUNOP .V128 v_vvunop) (.mk_instrtype (.mk_list [.V128]) [] (.mk_list [.V128]))
  | vvbinop : forall (C : context) (v_vvbinop : vvbinop), Instr_ok C (.VVBINOP .V128 v_vvbinop) (.mk_instrtype (.mk_list [.V128, .V128]) [] (.mk_list [.V128]))
  | vvternop : forall (C : context) (v_vvternop : vvternop), Instr_ok C (.VVTERNOP .V128 v_vvternop) (.mk_instrtype (.mk_list [.V128, .V128, .V128]) [] (.mk_list [.V128]))
  | vvtestop : forall (C : context) (v_vvtestop : vvtestop), Instr_ok C (.VVTESTOP .V128 v_vvtestop) (.mk_instrtype (.mk_list [.V128]) [] (.mk_list [.I32]))
  | vunop : forall (C : context) (sh : shape) (vunop : vunop_), 
    (wf_vunop_ sh vunop) ->
    Instr_ok C (.VUNOP sh vunop) (.mk_instrtype (.mk_list [.V128]) [] (.mk_list [.V128]))
  | vbinop : forall (C : context) (sh : shape) (vbinop : vbinop_), 
    (wf_vbinop_ sh vbinop) ->
    Instr_ok C (.VBINOP sh vbinop) (.mk_instrtype (.mk_list [.V128, .V128]) [] (.mk_list [.V128]))
  | vternop : forall (C : context) (sh : shape) (vternop : vternop_), 
    (wf_vternop_ sh vternop) ->
    Instr_ok C (.VTERNOP sh vternop) (.mk_instrtype (.mk_list [.V128, .V128, .V128]) [] (.mk_list [.V128]))
  | vtestop : forall (C : context) (sh : shape) (vtestop : vtestop_), 
    (wf_vtestop_ sh vtestop) ->
    Instr_ok C (.VTESTOP sh vtestop) (.mk_instrtype (.mk_list [.V128]) [] (.mk_list [.I32]))
  | vrelop : forall (C : context) (sh : shape) (vrelop : vrelop_), 
    (wf_vrelop_ sh vrelop) ->
    Instr_ok C (.VRELOP sh vrelop) (.mk_instrtype (.mk_list [.V128, .V128]) [] (.mk_list [.V128]))
  | vshiftop : forall (C : context) (sh : ishape) (vshiftop : vshiftop_), 
    (wf_vshiftop_ sh vshiftop) ->
    Instr_ok C (.VSHIFTOP sh vshiftop) (.mk_instrtype (.mk_list [.V128, .I32]) [] (.mk_list [.V128]))
  | vbitmask : forall (C : context) (sh : ishape), Instr_ok C (.VBITMASK sh) (.mk_instrtype (.mk_list [.V128]) [] (.mk_list [.I32]))
  | vswizzlop : forall (C : context) (sh : bshape) (vswizzlop : vswizzlop_), 
    (wf_vswizzlop_ sh vswizzlop) ->
    Instr_ok C (.VSWIZZLOP sh vswizzlop) (.mk_instrtype (.mk_list [.V128, .V128]) [] (.mk_list [.V128]))
  | vshuffle : forall (C : context) (sh : bshape) (i_lst : (List laneidx)), 
    Forall (fun (i : laneidx) => ((proj_uN_0 i) < (2 * (proj_dim_0 (fun_dim (proj_bshape_0 sh)))))) i_lst ->
    Instr_ok C (.VSHUFFLE sh i_lst) (.mk_instrtype (.mk_list [.V128, .V128]) [] (.mk_list [.V128]))
  | vsplat : forall (C : context) (sh : shape), Instr_ok C (.VSPLAT sh) (.mk_instrtype (.mk_list [(valtype_numtype (unpackshape sh))]) [] (.mk_list [.V128]))
  | vextract_lane : forall (C : context) (sh : shape) (sx_opt : (Option sx)) (i : laneidx), 
    ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) ->
    Instr_ok C (.VEXTRACT_LANE sh sx_opt i) (.mk_instrtype (.mk_list [.V128]) [] (.mk_list [(valtype_numtype (unpackshape sh))]))
  | vreplace_lane : forall (C : context) (sh : shape) (i : laneidx), 
    ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) ->
    Instr_ok C (.VREPLACE_LANE sh i) (.mk_instrtype (.mk_list [.V128, (valtype_numtype (unpackshape sh))]) [] (.mk_list [.V128]))
  | vextunop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop__), 
    (wf_vextunop__ sh_2 sh_1 vextunop) ->
    Instr_ok C (.VEXTUNOP sh_1 sh_2 vextunop) (.mk_instrtype (.mk_list [.V128]) [] (.mk_list [.V128]))
  | vextbinop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop__), 
    (wf_vextbinop__ sh_2 sh_1 vextbinop) ->
    Instr_ok C (.VEXTBINOP sh_1 sh_2 vextbinop) (.mk_instrtype (.mk_list [.V128, .V128]) [] (.mk_list [.V128]))
  | vextternop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextternop : vextternop__), 
    (wf_vextternop__ sh_2 sh_1 vextternop) ->
    Instr_ok C (.VEXTTERNOP sh_1 sh_2 vextternop) (.mk_instrtype (.mk_list [.V128, .V128, .V128]) [] (.mk_list [.V128]))
  | vnarrow : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (v_sx : sx), Instr_ok C (.VNARROW sh_1 sh_2 v_sx) (.mk_instrtype (.mk_list [.V128, .V128]) [] (.mk_list [.V128]))
  | vcvtop : forall (C : context) (sh_1 : shape) (sh_2 : shape) (vcvtop : vcvtop__), 
    (wf_vcvtop__ sh_2 sh_1 vcvtop) ->
    Instr_ok C (.VCVTOP sh_1 sh_2 vcvtop) (.mk_instrtype (.mk_list [.V128]) [] (.mk_list [.V128]))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:6.1-6.96 -/
inductive Instrs_ok : context -> (List instr) -> instrtype -> Prop where
  | empty : forall (C : context), Instrs_ok C [] (.mk_instrtype (.mk_list []) [] (.mk_list []))
  | seq : forall (C : context) (instr_1 : instr) (instr_2_lst : (List instr)) (t_1_lst : (List valtype)) (x_1_lst : (List idx)) (x_2_lst : (List idx)) (t_3_lst : (List valtype)) (t_2_lst : (List valtype)) (init_lst : (List init)) (t_lst : (List valtype)) (var_0 : context), 
    (fun_with_locals C x_1_lst (List.map (fun (t : valtype) => (.mk_localtype .SET t)) t_lst) var_0) ->
    (Instr_ok C instr_1 (.mk_instrtype (.mk_list t_1_lst) x_1_lst (.mk_list t_2_lst))) ->
    ((List.length init_lst) == (List.length t_lst)) ->
    ((List.length init_lst) == (List.length x_1_lst)) ->
    Forall (fun (x_1 : idx) => ((proj_uN_0 x_1) < (List.length (C.LOCALS)))) x_1_lst ->
    Forall₃ (fun (v_init : init) (t : valtype) (x_1 : idx) => (((C.LOCALS)[(proj_uN_0 x_1)]!) == (.mk_localtype v_init t))) init_lst t_lst x_1_lst ->
    (Instrs_ok var_0 instr_2_lst (.mk_instrtype (.mk_list t_2_lst) x_2_lst (.mk_list t_3_lst))) ->
    Instrs_ok C ([instr_1] ++ instr_2_lst) (.mk_instrtype (.mk_list t_1_lst) (x_1_lst ++ x_2_lst) (.mk_list t_3_lst))
  | sub : forall (C : context) (instr_lst : (List instr)) (it' : instrtype) (it : instrtype), 
    (Instrs_ok C instr_lst it) ->
    (Instrtype_sub C it it') ->
    (Instrtype_ok C it') ->
    Instrs_ok C instr_lst it'
  | frame : forall (C : context) (instr_lst : (List instr)) (t_lst : (List valtype)) (t_1_lst : (List valtype)) (x_lst : (List idx)) (t_2_lst : (List valtype)), 
    (Instrs_ok C instr_lst (.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst))) ->
    (Resulttype_ok C (.mk_list t_lst)) ->
    Instrs_ok C instr_lst (.mk_instrtype (.mk_list (t_lst ++ t_1_lst)) x_lst (.mk_list (t_lst ++ t_2_lst)))

end

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:7.1-7.94 -/
inductive Expr_ok : context -> expr -> resulttype -> Prop where
  | mk_Expr_ok : forall (C : context) (instr_lst : (List instr)) (t_lst : (List valtype)), 
    (Instrs_ok C instr_lst (.mk_instrtype (.mk_list []) [] (.mk_list t_lst))) ->
    Expr_ok C instr_lst (.mk_list t_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:12.1-13.75 -/
inductive Nondefaultable : valtype -> Prop where
  | mk_Nondefaultable : forall (t : valtype), 
    ((default_ t) == none) ->
    Nondefaultable t

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:645.1-645.104 -/
inductive Instr_const : context -> instr -> Prop where
  | const : forall (C : context) (nt : numtype) (c_nt : num_), 
    (wf_num_ nt c_nt) ->
    Instr_const C (.CONST nt c_nt)
  | vconst : forall (C : context) (vt : vectype) (c_vt : vec_), Instr_const C (.VCONST vt c_vt)
  | ref_null : forall (C : context) (ht : heaptype), Instr_const C (.REF_NULL ht)
  | ref_i31 : forall (C : context), Instr_const C .REF_I31
  | ref_func : forall (C : context) (x : idx), Instr_const C (.REF_FUNC x)
  | struct_new : forall (C : context) (x : idx), Instr_const C (.STRUCT_NEW x)
  | struct_new_default : forall (C : context) (x : idx), Instr_const C (.STRUCT_NEW_DEFAULT x)
  | array_new : forall (C : context) (x : idx), Instr_const C (.ARRAY_NEW x)
  | array_new_default : forall (C : context) (x : idx), Instr_const C (.ARRAY_NEW_DEFAULT x)
  | array_new_fixed : forall (C : context) (x : idx) (v_n : n), Instr_const C (.ARRAY_NEW_FIXED x (.mk_uN v_n))
  | any_convert_extern : forall (C : context), Instr_const C .ANY_CONVERT_EXTERN
  | extern_convert_any : forall (C : context), Instr_const C .EXTERN_CONVERT_ANY
  | global_get : forall (C : context) (x : idx) (t : valtype), 
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype none t)) ->
    Instr_const C (.GLOBAL_GET x)
  | binop : forall (C : context) (v_Inn : Inn) (binop : binop_), 
    (wf_binop_ (numtype_addrtype v_Inn) binop) ->
    (wf_binop_ (numtype_addrtype v_Inn) (.mk_binop__0 v_Inn .ADD)) ->
    (wf_binop_ (numtype_addrtype v_Inn) (.mk_binop__0 v_Inn .SUB)) ->
    (wf_binop_ (numtype_addrtype v_Inn) (.mk_binop__0 v_Inn .MUL)) ->
    (List.contains [.I32, .I64] v_Inn) ->
    (List.contains [(.mk_binop__0 v_Inn .ADD), (.mk_binop__0 v_Inn .SUB), (.mk_binop__0 v_Inn .MUL)] binop) ->
    Instr_const C (.BINOP (numtype_addrtype v_Inn) binop)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:646.1-646.103 -/
inductive Expr_const : context -> expr -> Prop where
  | mk_Expr_const : forall (C : context) (instr_lst : (List instr)), 
    Forall (fun (v_instr : instr) => (Instr_const C v_instr)) instr_lst ->
    Expr_const C instr_lst

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.3-validation.instructions.spectec:647.1-647.105 -/
inductive Expr_ok_const : context -> expr -> valtype -> Prop where
  | mk_Expr_ok_const : forall (C : context) (v_expr : expr) (t : valtype), 
    (Expr_ok C v_expr (.mk_list [t])) ->
    (Expr_const C v_expr) ->
    Expr_ok_const C v_expr t

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:7.1-7.97 -/
inductive Type_ok : context -> type -> (List deftype) -> Prop where
  | mk_Type_ok : forall (C : context) (v_rectype : rectype) (dt_lst : (List deftype)) (x : idx) (var_0 : (List deftype)), 
    (fun_rolldt x v_rectype var_0) ->
    ((proj_uN_0 x) == (List.length (C.TYPES))) ->
    (dt_lst == var_0) ->
    (Rectype_ok (C ++ { TYPES := dt_lst, RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) v_rectype (.OK x)) ->
    Type_ok C (.TYPE v_rectype) dt_lst

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:8.1-8.96 -/
inductive Tag_ok : context -> tag -> tagtype -> Prop where
  | mk_Tag_ok : forall (C : context) (v_tagtype : tagtype) (var_0 : tagtype), 
    (fun_clos_tagtype C v_tagtype var_0) ->
    (Tagtype_ok C v_tagtype) ->
    Tag_ok C (.TAG v_tagtype) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:9.1-9.99 -/
inductive Global_ok : context -> global -> globaltype -> Prop where
  | mk_Global_ok : forall (C : context) (v_globaltype : globaltype) (v_expr : expr) (t : valtype), 
    (Globaltype_ok C v_globaltype) ->
    (v_globaltype == (.mk_globaltype (some .MUT) t)) ->
    (Expr_ok_const C v_expr t) ->
    Global_ok C (.GLOBAL v_globaltype v_expr) v_globaltype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:10.1-10.96 -/
inductive Mem_ok : context -> mem -> memtype -> Prop where
  | mk_Mem_ok : forall (C : context) (v_memtype : memtype), 
    (Memtype_ok C v_memtype) ->
    Mem_ok C (.MEMORY v_memtype) v_memtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:11.1-11.98 -/
inductive Table_ok : context -> table -> tabletype -> Prop where
  | mk_Table_ok : forall (C : context) (v_tabletype : tabletype) (v_expr : expr) («at» : addrtype) (lim : limits) (rt : reftype), 
    (Tabletype_ok C v_tabletype) ->
    (v_tabletype == (.mk_tabletype «at» lim rt)) ->
    (Expr_ok_const C v_expr (valtype_reftype rt)) ->
    Table_ok C (.TABLE v_tabletype v_expr) v_tabletype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:18.1-18.98 -/
inductive Local_ok : context -> «local» -> localtype -> Prop where
  | set : forall (C : context) (t : valtype), 
    (Defaultable t) ->
    Local_ok C (.LOCAL t) (.mk_localtype .SET t)
  | unset : forall (C : context) (t : valtype), 
    (Nondefaultable t) ->
    Local_ok C (.LOCAL t) (.mk_localtype .UNSET t)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:12.1-12.97 -/
inductive Func_ok : context -> func -> deftype -> Prop where
  | mk_Func_ok : forall (C : context) (x : idx) (local_lst : (List «local»)) (v_expr : expr) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (lct_lst : (List localtype)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (Expand ((C.TYPES)[(proj_uN_0 x)]!) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    ((List.length lct_lst) == (List.length local_lst)) ->
    Forall₂ (fun (lct : localtype) (v_local : «local») => (Local_ok C v_local lct)) lct_lst local_lst ->
    (Expr_ok (C ++ { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := ((List.map (fun (t_1 : valtype) => (.mk_localtype .SET t_1)) t_1_lst) ++ lct_lst), LABELS := [(.mk_list t_2_lst)], RETURN := (some (.mk_list t_2_lst)), REFS := [] }) v_expr (.mk_list t_2_lst)) ->
    Func_ok C (.FUNC x local_lst v_expr) ((C.TYPES)[(proj_uN_0 x)]!)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:15.1-15.118 -/
inductive Datamode_ok : context -> datamode -> datatype -> Prop where
  | passive : forall (C : context), Datamode_ok C .PASSIVE .OK
  | active : forall (C : context) (x : idx) (v_expr : expr) («at» : addrtype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == (.PAGE «at» lim)) ->
    (Expr_ok_const C v_expr (valtype_addrtype «at»)) ->
    Datamode_ok C (.ACTIVE x v_expr) .OK

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:13.1-13.115 -/
inductive Data_ok : context -> data -> datatype -> Prop where
  | mk_Data_ok : forall (C : context) (b_lst : (List byte)) (v_datamode : datamode), 
    (Datamode_ok C v_datamode .OK) ->
    Data_ok C (.DATA b_lst v_datamode) .OK

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:16.1-16.101 -/
inductive Elemmode_ok : context -> elemmode -> elemtype -> Prop where
  | passive : forall (C : context) (rt : reftype), Elemmode_ok C .PASSIVE rt
  | declare : forall (C : context) (rt : reftype), Elemmode_ok C .DECLARE rt
  | active : forall (C : context) (x : idx) (v_expr : expr) (rt : reftype) («at» : addrtype) (lim : limits) (rt' : reftype), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype «at» lim rt')) ->
    (Reftype_sub C rt rt') ->
    (Expr_ok_const C v_expr (valtype_addrtype «at»)) ->
    Elemmode_ok C (.ACTIVE x v_expr) rt

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:14.1-14.97 -/
inductive Elem_ok : context -> elem -> elemtype -> Prop where
  | mk_Elem_ok : forall (C : context) (v_elemtype : elemtype) (expr_lst : (List expr)) (v_elemmode : elemmode), 
    (Reftype_ok C v_elemtype) ->
    Forall (fun (v_expr : expr) => (Expr_ok_const C v_expr (valtype_reftype v_elemtype))) expr_lst ->
    (Elemmode_ok C v_elemmode v_elemtype) ->
    Elem_ok C (.ELEM v_elemtype expr_lst v_elemmode) v_elemtype

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:17.1-17.98 -/
inductive Start_ok : context -> start -> Prop where
  | mk_Start_ok : forall (C : context) (x : idx), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (Expand ((C.FUNCS)[(proj_uN_0 x)]!) (.FUNC (.mk_list []) (.mk_list []))) ->
    Start_ok C (.START x)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:98.1-98.105 -/
inductive Import_ok : context -> «import» -> externtype -> Prop where
  | mk_Import_ok : forall (C : context) (name_1 : name) (name_2 : name) (xt : externtype) (var_0 : externtype), 
    (fun_clos_externtype C xt var_0) ->
    (Externtype_ok C xt) ->
    Import_ok C (.IMPORT name_1 name_2 xt) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:100.1-100.108 -/
inductive Externidx_ok : context -> externidx -> externtype -> Prop where
  | tag : forall (C : context) (x : idx) (jt : tagtype), 
    ((proj_uN_0 x) < (List.length (C.TAGS))) ->
    (((C.TAGS)[(proj_uN_0 x)]!) == jt) ->
    Externidx_ok C (.TAG x) (.TAG jt)
  | global : forall (C : context) (x : idx) (gt : globaltype), 
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == gt) ->
    Externidx_ok C (.GLOBAL x) (.GLOBAL gt)
  | mem : forall (C : context) (x : idx) (mt : memtype), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == mt) ->
    Externidx_ok C (.MEM x) (.MEM mt)
  | table : forall (C : context) (x : idx) (tt : tabletype), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == tt) ->
    Externidx_ok C (.TABLE x) (.TABLE tt)
  | func : forall (C : context) (x : idx) (dt : deftype), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == dt) ->
    Externidx_ok C (.FUNC x) (.FUNC (typeuse_deftype dt))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:99.1-99.105 -/
inductive Export_ok : context -> «export» -> name -> externtype -> Prop where
  | mk_Export_ok : forall (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype), 
    (Externidx_ok C v_externidx xt) ->
    Export_ok C (.EXPORT v_name v_externidx) v_name xt

/- Recursive Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:136.1-136.100 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:136.1-136.100 -/
inductive Globals_ok : context -> (List global) -> (List globaltype) -> Prop where
  | empty : forall (C : context), Globals_ok C [] []
  | cons : forall (C : context) (global_1 : global) (global_lst : (List global)) (gt_1 : globaltype) (gt_lst : (List globaltype)), 
    (Global_ok C global_1 gt_1) ->
    (Globals_ok (C ++ { TYPES := [], RECS := [], TAGS := [], GLOBALS := [gt_1], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) global_lst gt_lst) ->
    Globals_ok C ([global_1] ++ global_lst) ([gt_1] ++ gt_lst)

/- Recursive Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:135.1-135.98 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:135.1-135.98 -/
inductive Types_ok : context -> (List type) -> (List deftype) -> Prop where
  | empty : forall (C : context), Types_ok C [] []
  | cons : forall (C : context) (type_1 : type) (type_lst : (List type)) (dt_1_lst : (List deftype)) (dt_lst : (List deftype)), 
    (Type_ok C type_1 dt_1_lst) ->
    (Types_ok (C ++ { TYPES := dt_1_lst, RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] }) type_lst dt_lst) ->
    Types_ok C ([type_1] ++ type_lst) (dt_1_lst ++ dt_lst)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:139.1-139.44 -/
inductive nonfuncs : Type where
  | mk_nonfuncs (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (elem_lst : (List elem)) : nonfuncs
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:139.8-139.16 -/
inductive wf_nonfuncs : nonfuncs -> Prop where
  | nonfuncs_case_0 : forall (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (elem_lst : (List elem)), 
    Forall (fun (v_global : global) => (wf_global v_global)) global_lst ->
    Forall (fun (v_mem : mem) => (wf_mem v_mem)) mem_lst ->
    Forall (fun (v_table : table) => (wf_table v_table)) table_lst ->
    Forall (fun (v_elem : elem) => (wf_elem v_elem)) elem_lst ->
    wf_nonfuncs (.mk_nonfuncs global_lst mem_lst table_lst elem_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:140.6-140.23 -/
inductive fun_funcidx_nonfuncs : nonfuncs -> (List funcidx) -> Prop where
  | fun_funcidx_nonfuncs_case_0 : forall (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (elem_lst : (List elem)) (var_0 : (List funcidx)), 
    (fun_funcidx_module (.MODULE [] [] [] global_lst mem_lst table_lst [] [] elem_lst none []) var_0) ->
    fun_funcidx_nonfuncs (.mk_nonfuncs global_lst mem_lst table_lst elem_lst) var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/2.4-validation.modules.spectec:134.1-134.99 -/
inductive Module_ok : module -> moduletype -> Prop where
  | mk_Module_ok : forall (type_lst : (List type)) (import_lst : (List «import»)) (tag_lst : (List tag)) (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (func_lst : (List func)) (data_lst : (List data)) (elem_lst : (List elem)) (start_opt : (Option start)) (export_lst : (List «export»)) (C : context) (xt_I_lst : (List externtype)) (xt_E_lst : (List externtype)) (dt'_lst : (List deftype)) (C' : context) (jt_lst : (List tagtype)) (gt_lst : (List globaltype)) (mt_lst : (List memtype)) (tt_lst : (List tabletype)) (dt_lst : (List deftype)) (ok_lst : (List datatype)) (rt_lst : (List reftype)) (nm_lst : (List name)) (jt_I_lst : (List tagtype)) (mt_I_lst : (List memtype)) (tt_I_lst : (List tabletype)) (gt_I_lst : (List globaltype)) (dt_I_lst : (List deftype)) (x_lst : (List idx)) (var_6 : (List deftype)) (var_5 : (List tabletype)) (var_4 : (List memtype)) (var_3 : (List globaltype)) (var_2 : (List tagtype)) (var_1 : (List funcidx)) (var_0 : moduletype), 
    (fun_funcsxt xt_I_lst var_6) ->
    (fun_tablesxt xt_I_lst var_5) ->
    (fun_memsxt xt_I_lst var_4) ->
    (fun_globalsxt xt_I_lst var_3) ->
    (fun_tagsxt xt_I_lst var_2) ->
    (fun_funcidx_nonfuncs (.mk_nonfuncs global_lst mem_lst table_lst elem_lst) var_1) ->
    (fun_clos_moduletype C (.mk_moduletype xt_I_lst xt_E_lst) var_0) ->
    (Types_ok { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } type_lst dt'_lst) ->
    ((List.length import_lst) == (List.length xt_I_lst)) ->
    Forall₂ (fun (v_import : «import») (xt_I : externtype) => (Import_ok { TYPES := dt'_lst, RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } v_import xt_I)) import_lst xt_I_lst ->
    ((List.length jt_lst) == (List.length tag_lst)) ->
    Forall₂ (fun (jt : tagtype) (v_tag : tag) => (Tag_ok C' v_tag jt)) jt_lst tag_lst ->
    (Globals_ok C' global_lst gt_lst) ->
    ((List.length mem_lst) == (List.length mt_lst)) ->
    Forall₂ (fun (v_mem : mem) (mt : memtype) => (Mem_ok C' v_mem mt)) mem_lst mt_lst ->
    ((List.length table_lst) == (List.length tt_lst)) ->
    Forall₂ (fun (v_table : table) (tt : tabletype) => (Table_ok C' v_table tt)) table_lst tt_lst ->
    ((List.length dt_lst) == (List.length func_lst)) ->
    Forall₂ (fun (dt : deftype) (v_func : func) => (Func_ok C v_func dt)) dt_lst func_lst ->
    ((List.length data_lst) == (List.length ok_lst)) ->
    Forall₂ (fun (v_data : data) (ok : datatype) => (Data_ok C v_data ok)) data_lst ok_lst ->
    ((List.length elem_lst) == (List.length rt_lst)) ->
    Forall₂ (fun (v_elem : elem) (rt : elemtype) => (Elem_ok C v_elem rt)) elem_lst rt_lst ->
    Forall (fun (v_start : start) => (Start_ok C v_start)) (Option.toList start_opt) ->
    ((List.length export_lst) == (List.length nm_lst)) ->
    ((List.length export_lst) == (List.length xt_E_lst)) ->
    Forall₃ (fun (v_export : «export») (nm : name) (xt_E : externtype) => (Export_ok C v_export nm xt_E)) export_lst nm_lst xt_E_lst ->
    (disjoint_ name nm_lst) ->
    (C == (C' ++ { TYPES := [], RECS := [], TAGS := (jt_I_lst ++ jt_lst), GLOBALS := gt_lst, MEMS := (mt_I_lst ++ mt_lst), TABLES := (tt_I_lst ++ tt_lst), FUNCS := [], DATAS := ok_lst, ELEMS := rt_lst, LOCALS := [], LABELS := [], RETURN := none, REFS := [] })) ->
    (C' == { TYPES := dt'_lst, RECS := [], TAGS := [], GLOBALS := gt_I_lst, MEMS := [], TABLES := [], FUNCS := (dt_I_lst ++ dt_lst), DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := x_lst }) ->
    (x_lst == var_1) ->
    (jt_I_lst == var_2) ->
    (gt_I_lst == var_3) ->
    (mt_I_lst == var_4) ->
    (tt_I_lst == var_5) ->
    (dt_I_lst == var_6) ->
    Module_ok (.MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst) var_0

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.1-5.24 -/
inductive relaxed2 : Type where
  | mk_relaxed2 (i : Nat) : relaxed2
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.1-5.24 -/
def proj_relaxed2_0 : ∀  (x : relaxed2) , Nat
  | (.mk_relaxed2 v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:5.8-5.16 -/
inductive wf_relaxed2 : relaxed2 -> Prop where
  | relaxed2_case_0 : forall (i : Nat), 
    ((i == 0) || (i == 1)) ->
    wf_relaxed2 (.mk_relaxed2 i)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.1-6.32 -/
inductive relaxed4 : Type where
  | mk_relaxed4 (i : Nat) : relaxed4
deriving Inhabited, BEq


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.1-6.32 -/
def proj_relaxed4_0 : ∀  (x : relaxed4) , Nat
  | (.mk_relaxed4 v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:6.8-6.16 -/
inductive wf_relaxed4 : relaxed4 -> Prop where
  | relaxed4_case_0 : forall (i : Nat), 
    ((((i == 0) || (i == 1)) || (i == 2)) || (i == 3)) ->
    wf_relaxed4 (.mk_relaxed4 i)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:8.1-8.83 -/
def fun_relaxed2 : ∀  (v_relaxed2 : relaxed2) (v_X : Type) (v_X_0 : v_X) (v_X_1 : v_X) , v_X
  | i, v_X, X_1, X_2 =>
    (if (ND ) then ([X_1, X_2][(proj_relaxed2_0 i)]!) else ([X_1, X_2][0]!))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:9.1-9.89 -/
def fun_relaxed4 : ∀  (v_relaxed4 : relaxed4) (v_X : Type) (v_X_0 : v_X) (v_X_1 : v_X) (v_X_2 : v_X) (v_X_3 : v_X) , v_X
  | i, v_X, X_1, X_2, X_3, X_4 =>
    (if (ND ) then ([X_1, X_2, X_3, X_4][(proj_relaxed4_0 i)]!) else ([X_1, X_2, X_3, X_4][0]!))


/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:18.1-18.43 -/
opaque R_fmadd : relaxed2 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:19.1-19.43 -/
opaque R_fmin : relaxed4 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:20.1-20.43 -/
opaque R_fmax : relaxed4 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:21.1-21.43 -/
opaque R_idot : relaxed2 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:22.1-22.43 -/
opaque R_iq15mulr : relaxed2 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:23.1-23.43 -/
opaque R_trunc_u : relaxed4 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:24.1-24.43 -/
opaque R_trunc_s : relaxed2 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:25.1-25.43 -/
opaque R_swizzle : relaxed2 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.0-numerics.relaxed.spectec:26.1-26.43 -/
opaque R_laneselect : relaxed2 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:7.1-7.41 -/
opaque s33_to_u32 : forall (v_s33 : s33), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:12.1-12.107 -/
opaque ibits_ : forall (v_N : N) (v_iN : iN), (List bit) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:13.1-13.107 -/
opaque fbits_ : forall (v_N : N) (v_fN : fN), (List bit) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:14.1-14.109 -/
opaque ibytes_ : forall (v_N : N) (v_iN : iN), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:15.1-15.109 -/
opaque fbytes_ : forall (v_N : N) (v_fN : fN), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:16.1-16.104 -/
opaque nbytes_ : forall (v_numtype : numtype) (v_num_ : num_), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:17.1-17.104 -/
opaque vbytes_ : forall (v_vectype : vectype) (v_vec_ : vec_), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:18.1-18.104 -/
opaque zbytes_ : forall (v_storagetype : storagetype) (v_lit_ : lit_), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:19.1-19.104 -/
opaque cbytes_ : forall (v_Cnn : Cnn) (v_lit_ : lit_), (List byte) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:21.1-21.91 -/
opaque inv_ibits_ : forall (v_N : N) (var_0 : (List bit)), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:22.1-22.91 -/
opaque inv_fbits_ : forall (v_N : N) (var_0 : (List bit)), fN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:23.1-23.92 -/
opaque inv_ibytes_ : forall (v_N : N) (var_0 : (List byte)), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:24.1-24.92 -/
opaque inv_fbytes_ : forall (v_N : N) (var_0 : (List byte)), fN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:25.1-25.87 -/
opaque inv_nbytes_ : forall (v_numtype : numtype) (var_0 : (List byte)), num_ := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:26.1-26.87 -/
opaque inv_vbytes_ : forall (v_vectype : vectype) (var_0 : (List byte)), vec_ := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:27.1-27.92 -/
opaque inv_zbytes_ : forall (v_storagetype : storagetype) (var_0 : (List byte)), lit_ := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:28.1-28.87 -/
opaque inv_cbytes_ : forall (v_Cnn : Cnn) (var_0 : (List byte)), lit_ := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:52.6-52.14 -/
inductive fun_signed_ : N -> Nat -> Nat -> Prop where
  | fun_signed__case_0 : forall (v_N : Nat) (i : Nat), 
    (i < (2 ^ (((v_N : Nat) - (1 : Nat)) : Nat))) ->
    fun_signed_ v_N i (i : Nat)
  | fun_signed__case_1 : forall (v_N : Nat) (i : Nat), 
    (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) <= i) && (i < (2 ^ v_N))) ->
    fun_signed_ v_N i ((i : Nat) - ((2 ^ v_N) : Nat))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:56.6-56.18 -/
inductive fun_inv_signed_ : N -> Nat -> Nat -> Prop where
  | fun_inv_signed__case_0 : forall (v_N : Nat) (i : Nat), 
    (((0 : Nat) <= i) && (i < ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat))) ->
    fun_inv_signed_ v_N i (i : Nat)
  | fun_inv_signed__case_1 : forall (v_N : Nat) (i : Nat), 
    (((0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat)) <= i) && (i < (0 : Nat))) ->
    fun_inv_signed_ v_N i ((i + ((2 ^ v_N) : Nat)) : Nat)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:61.1-61.46 -/
def fun_sx : ∀  (v_storagetype : storagetype) , (Option sx)
  | .I32 =>
    none
  | .I64 =>
    none
  | .F32 =>
    none
  | .F64 =>
    none
  | .V128 =>
    none
  | .I8 =>
    (some .S)
  | .I16 =>
    (some .S)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:68.6-68.11 -/
inductive fun_zero : lanetype -> lane_ -> Prop where
  | fun_zero_case_0 : 
    (wf_lane_ (lanetype_Jnn .I32) (.mk_lane__2 .I32 (.mk_uN 0))) ->
    fun_zero .I32 (.mk_lane__2 .I32 (.mk_uN 0))
  | fun_zero_case_1 : 
    (wf_lane_ (lanetype_Jnn .I64) (.mk_lane__2 .I64 (.mk_uN 0))) ->
    fun_zero .I64 (.mk_lane__2 .I64 (.mk_uN 0))
  | fun_zero_case_2 : 
    (wf_lane_ (lanetype_Jnn .I8) (.mk_lane__2 .I8 (.mk_uN 0))) ->
    fun_zero .I8 (.mk_lane__2 .I8 (.mk_uN 0))
  | fun_zero_case_3 : 
    (wf_lane_ (lanetype_Jnn .I16) (.mk_lane__2 .I16 (.mk_uN 0))) ->
    fun_zero .I16 (.mk_lane__2 .I16 (.mk_uN 0))
  | fun_zero_case_4 : 
    (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 (fzero (size (numtype_Fnn .F32)))))) ->
    fun_zero .F32 (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 (fzero (size (numtype_Fnn .F32)))))
  | fun_zero_case_5 : 
    (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 (fzero (size (numtype_Fnn .F64)))))) ->
    fun_zero .F64 (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 (fzero (size (numtype_Fnn .F64)))))

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:72.1-72.22 -/
def nat_of_bool : ∀  (v_bool : Bool) , Nat
  | false =>
    0
  | true =>
    1


/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:76.1-76.23 -/
opaque truncz : forall (rat : Nat), Nat := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:80.1-80.59 -/
opaque ceilz : forall (rat : Nat), Nat := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:87.1-87.61 -/
def sat_u_ : ∀  (v_N : N) (int : Nat) , Nat
  | v_N, i =>
    (if (i < (0 : Nat)) then 0 else (if (i > (((2 ^ v_N) : Nat) - (1 : Nat))) then ((((2 ^ v_N) : Nat) - (1 : Nat)) : Nat) else (i : Nat)))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:92.1-92.61 -/
def sat_s_ : ∀  (v_N : N) (int : Nat) , Nat
  | v_N, i =>
    (if (i < (0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat))) then (0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat)) else (if (i > (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat) - (1 : Nat))) then (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat) - (1 : Nat)) else i))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:100.1-100.29 -/
def ineg_ : ∀  (v_N : N) (v_iN : iN) , iN
  | v_N, i_1 =>
    (.mk_uN (((((2 ^ v_N) : Nat) - ((proj_uN_0 i_1) : Nat)) mod ((2 ^ v_N) : Nat)) : Nat))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:101.1-101.29 -/
opaque iabs_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:102.1-102.29 -/
opaque iclz_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:103.1-103.29 -/
opaque ictz_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:104.1-104.32 -/
opaque ipopcnt_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:105.6-105.15 -/
inductive fun_iextend_ : N -> M -> sx -> iN -> iN -> Prop where
  | fun_iextend__case_0 : forall (v_N : Nat) (v_M : Nat) (i : uN), fun_iextend_ v_N v_M .U i (.mk_uN ((proj_uN_0 i) mod (2 ^ v_M)))
  | fun_iextend__case_1 : forall (v_N : Nat) (v_M : Nat) (i : uN) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_M ((proj_uN_0 i) mod (2 ^ v_M)) var_1) ->
    (fun_inv_signed_ v_N var_1 var_0) ->
    fun_iextend_ v_N v_M .S i (.mk_uN var_0)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:107.1-107.36 -/
def iadd_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN (((proj_uN_0 i_1) + (proj_uN_0 i_2)) mod (2 ^ v_N)))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:108.1-108.36 -/
def isub_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN ((((((2 ^ v_N) + (proj_uN_0 i_1)) : Nat) - ((proj_uN_0 i_2) : Nat)) mod ((2 ^ v_N) : Nat)) : Nat))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:109.1-109.36 -/
def imul_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN (((proj_uN_0 i_1) * (proj_uN_0 i_2)) mod (2 ^ v_N)))


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:110.6-110.12 -/
inductive fun_idiv_ : N -> sx -> iN -> iN -> (Option iN) -> Prop where
  | fun_idiv__case_0 : forall (v_N : Nat) (i_1 : uN), fun_idiv_ v_N .U i_1 (.mk_uN 0) none
  | fun_idiv__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_idiv_ v_N .U i_1 i_2 (some (.mk_uN ((truncz (((proj_uN_0 i_1) : Nat) / ((proj_uN_0 i_2) : Nat))) : Nat)))
  | fun_idiv__case_2 : forall (v_N : Nat) (i_1 : uN), fun_idiv_ v_N .S i_1 (.mk_uN 0) none
  | fun_idiv__case_3 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    (((var_0 : Nat) / (var_1 : Nat)) == ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat)) ->
    fun_idiv_ v_N .S i_1 i_2 none
  | fun_idiv__case_4 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Nat) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_2) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_1) ->
    (fun_inv_signed_ v_N (truncz ((var_1 : Nat) / (var_2 : Nat))) var_0) ->
    fun_idiv_ v_N .S i_1 i_2 (some (.mk_uN var_0))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:111.6-111.12 -/
inductive fun_irem_ : N -> sx -> iN -> iN -> (Option iN) -> Prop where
  | fun_irem__case_0 : forall (v_N : Nat) (i_1 : uN), fun_irem_ v_N .U i_1 (.mk_uN 0) none
  | fun_irem__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_irem_ v_N .U i_1 i_2 (some (.mk_uN ((((proj_uN_0 i_1) : Nat) - (((proj_uN_0 i_2) * ((truncz (((proj_uN_0 i_1) : Nat) / ((proj_uN_0 i_2) : Nat))) : Nat)) : Nat)) : Nat)))
  | fun_irem__case_2 : forall (v_N : Nat) (i_1 : uN), fun_irem_ v_N .S i_1 (.mk_uN 0) none
  | fun_irem__case_3 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (j_1 : Nat) (j_2 : Nat) (var_2 : Nat) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_2) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_1) ->
    (fun_inv_signed_ v_N (j_1 - (j_2 * (truncz ((j_1 : Nat) / (j_2 : Nat))))) var_0) ->
    ((j_1 == var_1) && (j_2 == var_2)) ->
    fun_irem_ v_N .S i_1 i_2 (some (.mk_uN var_0))

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:112.1-112.83 -/
opaque imin_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:113.1-113.83 -/
opaque imax_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:114.1-114.88 -/
opaque iadd_sat_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:115.1-115.88 -/
opaque isub_sat_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:116.1-116.92 -/
opaque iq15mulr_sat_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:117.1-117.101 -/
opaque irelaxed_q15mulr_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), (List iN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:118.1-118.84 -/
opaque iavgr_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:120.1-120.29 -/
opaque inot_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:121.1-121.29 -/
opaque irev_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:122.1-122.36 -/
opaque iand_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:123.1-123.39 -/
opaque iandnot_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:124.1-124.35 -/
opaque ior_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:125.1-125.36 -/
opaque ixor_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:126.1-126.34 -/
opaque ishl_ : forall (v_N : N) (v_iN : iN) (v_u32 : u32), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:127.1-127.76 -/
opaque ishr_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:128.1-128.37 -/
opaque irotl_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:129.1-129.37 -/
opaque irotr_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:131.1-131.49 -/
opaque ibitselect_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN) (v_iN_1 : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:132.1-132.59 -/
opaque irelaxed_laneselect_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN) (v_iN_1 : iN), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:134.1-134.27 -/
def ieqz_ : ∀  (v_N : N) (v_iN : iN) , u32
  | v_N, i_1 =>
    (.mk_uN (nat_of_bool ((proj_uN_0 i_1) == 0)))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:135.1-135.27 -/
def inez_ : ∀  (v_N : N) (v_iN : iN) , u32
  | v_N, i_1 =>
    (.mk_uN (nat_of_bool ((proj_uN_0 i_1) != 0)))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:137.1-137.33 -/
def ieq_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , u32
  | v_N, i_1, i_2 =>
    (.mk_uN (nat_of_bool (i_1 == i_2)))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:138.1-138.33 -/
def ine_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , u32
  | v_N, i_1, i_2 =>
    (.mk_uN (nat_of_bool (i_1 != i_2)))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:139.1-139.75 -/
opaque ilt_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:140.1-140.75 -/
opaque igt_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:141.1-141.75 -/
opaque ile_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), u32 := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:142.1-142.75 -/
opaque ige_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:242.1-242.30 -/
opaque fabs_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:243.1-243.30 -/
opaque fneg_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:244.1-244.31 -/
opaque fsqrt_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:245.1-245.31 -/
opaque fceil_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:246.1-246.32 -/
opaque ffloor_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:247.1-247.32 -/
opaque ftrunc_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:248.1-248.34 -/
opaque fnearest_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:250.1-250.37 -/
opaque fadd_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:251.1-251.37 -/
opaque fsub_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:252.1-252.37 -/
opaque fmul_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:253.1-253.37 -/
opaque fdiv_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:254.1-254.37 -/
opaque fmin_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:255.1-255.37 -/
opaque fmax_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:256.1-256.38 -/
opaque fpmin_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:257.1-257.38 -/
opaque fpmax_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:258.1-258.82 -/
opaque frelaxed_min_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:259.1-259.82 -/
opaque frelaxed_max_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:260.1-260.42 -/
opaque fcopysign_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:262.1-262.33 -/
opaque feq_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:263.1-263.33 -/
opaque fne_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:264.1-264.33 -/
opaque flt_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:265.1-265.33 -/
opaque fgt_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:266.1-266.33 -/
opaque fle_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:267.1-267.33 -/
opaque fge_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:269.1-269.91 -/
opaque frelaxed_madd_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN) (v_fN_1 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:270.1-270.92 -/
opaque frelaxed_nmadd_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN) (v_fN_1 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:308.1-308.33 -/
opaque wrap__ : forall (v_M : M) (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:309.1-309.90 -/
opaque extend__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:310.1-310.89 -/
opaque trunc__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN), (Option iN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:311.1-311.94 -/
opaque trunc_sat__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN), (Option iN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:312.1-312.98 -/
opaque relaxed_trunc__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN), (Option iN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:313.1-313.36 -/
opaque demote__ : forall (v_M : M) (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:314.1-314.37 -/
opaque promote__ : forall (v_M : M) (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:315.1-315.91 -/
opaque convert__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN), fN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:316.1-316.88 -/
opaque narrow__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:318.1-318.76 -/
opaque reinterpret__ : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_), num_ := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:338.6-338.16 -/
inductive fun_lpacknum_ : lanetype -> num_ -> lane_ -> Prop where
  | fun_lpacknum__case_0 : forall (c : num_), 
    (wf_lane_ (lanetype_numtype .I32) (.mk_lane__0 .I32 c)) ->
    fun_lpacknum_ .I32 c (.mk_lane__0 .I32 c)
  | fun_lpacknum__case_1 : forall (c : num_), 
    (wf_lane_ (lanetype_numtype .I64) (.mk_lane__0 .I64 c)) ->
    fun_lpacknum_ .I64 c (.mk_lane__0 .I64 c)
  | fun_lpacknum__case_2 : forall (c : num_), 
    (wf_lane_ (lanetype_numtype .F32) (.mk_lane__0 .F32 c)) ->
    fun_lpacknum_ .F32 c (.mk_lane__0 .F32 c)
  | fun_lpacknum__case_3 : forall (c : num_), 
    (wf_lane_ (lanetype_numtype .F64) (.mk_lane__0 .F64 c)) ->
    fun_lpacknum_ .F64 c (.mk_lane__0 .F64 c)
  | fun_lpacknum__case_4 : forall (c : uN), 
    (wf_lane_ (lanetype_packtype .I8) (.mk_lane__1 .I8 (wrap__ (size (lunpack (lanetype_packtype .I8))) (psize .I8) c))) ->
    fun_lpacknum_ .I8 (.mk_num__0 .I32 c) (.mk_lane__1 .I8 (wrap__ (size (lunpack (lanetype_packtype .I8))) (psize .I8) c))
  | fun_lpacknum__case_5 : forall (c : uN), 
    (wf_lane_ (lanetype_packtype .I16) (.mk_lane__1 .I16 (wrap__ (size (lunpack (lanetype_packtype .I16))) (psize .I16) c))) ->
    fun_lpacknum_ .I16 (.mk_num__0 .I32 c) (.mk_lane__1 .I16 (wrap__ (size (lunpack (lanetype_packtype .I16))) (psize .I16) c))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:340.6-340.16 -/
inductive fun_cpacknum_ : storagetype -> lit_ -> lit_ -> Prop where
  | fun_cpacknum__case_0 : forall (c : lit_), fun_cpacknum_ .I32 c c
  | fun_cpacknum__case_1 : forall (c : lit_), fun_cpacknum_ .I64 c c
  | fun_cpacknum__case_2 : forall (c : lit_), fun_cpacknum_ .F32 c c
  | fun_cpacknum__case_3 : forall (c : lit_), fun_cpacknum_ .F64 c c
  | fun_cpacknum__case_4 : forall (c : lit_), fun_cpacknum_ .V128 c c
  | fun_cpacknum__case_5 : forall (c : uN), 
    (wf_lit_ (storagetype_packtype .I8) (.mk_lit__2 .I8 (wrap__ (size (lunpack (lanetype_packtype .I8))) (psize .I8) c))) ->
    fun_cpacknum_ .I8 (.mk_lit__0 .I32 (.mk_num__0 .I32 c)) (.mk_lit__2 .I8 (wrap__ (size (lunpack (lanetype_packtype .I8))) (psize .I8) c))
  | fun_cpacknum__case_6 : forall (c : uN), 
    (wf_lit_ (storagetype_packtype .I16) (.mk_lit__2 .I16 (wrap__ (size (lunpack (lanetype_packtype .I16))) (psize .I16) c))) ->
    fun_cpacknum_ .I16 (.mk_lit__0 .I32 (.mk_num__0 .I32 c)) (.mk_lit__2 .I16 (wrap__ (size (lunpack (lanetype_packtype .I16))) (psize .I16) c))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:350.6-350.18 -/
inductive fun_lunpacknum_ : lanetype -> lane_ -> num_ -> Prop where
  | fun_lunpacknum__case_0 : forall (c : num_), fun_lunpacknum_ .I32 (.mk_lane__0 .I32 c) c
  | fun_lunpacknum__case_1 : forall (c : num_), fun_lunpacknum_ .I64 (.mk_lane__0 .I64 c) c
  | fun_lunpacknum__case_2 : forall (c : num_), fun_lunpacknum_ .F32 (.mk_lane__0 .F32 c) c
  | fun_lunpacknum__case_3 : forall (c : num_), fun_lunpacknum_ .F64 (.mk_lane__0 .F64 c) c
  | fun_lunpacknum__case_4 : forall (c : uN), 
    (wf_num_ (lunpack (lanetype_packtype .I8)) (.mk_num__0 .I32 (extend__ (psize .I8) (size (lunpack (lanetype_packtype .I8))) .U c))) ->
    fun_lunpacknum_ .I8 (.mk_lane__1 .I8 c) (.mk_num__0 .I32 (extend__ (psize .I8) (size (lunpack (lanetype_packtype .I8))) .U c))
  | fun_lunpacknum__case_5 : forall (c : uN), 
    (wf_num_ (lunpack (lanetype_packtype .I16)) (.mk_num__0 .I32 (extend__ (psize .I16) (size (lunpack (lanetype_packtype .I16))) .U c))) ->
    fun_lunpacknum_ .I16 (.mk_lane__1 .I16 c) (.mk_num__0 .I32 (extend__ (psize .I16) (size (lunpack (lanetype_packtype .I16))) .U c))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:352.6-352.18 -/
inductive fun_cunpacknum_ : storagetype -> lit_ -> lit_ -> Prop where
  | fun_cunpacknum__case_0 : forall (c : lit_), fun_cunpacknum_ .I32 c c
  | fun_cunpacknum__case_1 : forall (c : lit_), fun_cunpacknum_ .I64 c c
  | fun_cunpacknum__case_2 : forall (c : lit_), fun_cunpacknum_ .F32 c c
  | fun_cunpacknum__case_3 : forall (c : lit_), fun_cunpacknum_ .F64 c c
  | fun_cunpacknum__case_4 : forall (c : lit_), fun_cunpacknum_ .V128 c c
  | fun_cunpacknum__case_5 : forall (c : uN), 
    ((cunpack (storagetype_packtype .I8)) != none) ->
    (wf_lit_ (storagetype_consttype (Option.get! (cunpack (storagetype_packtype .I8)))) (.mk_lit__0 .I32 (.mk_num__0 .I32 (extend__ (psize .I8) (size (lunpack (lanetype_packtype .I8))) .U c)))) ->
    fun_cunpacknum_ .I8 (.mk_lit__2 .I8 c) (.mk_lit__0 .I32 (.mk_num__0 .I32 (extend__ (psize .I8) (size (lunpack (lanetype_packtype .I8))) .U c)))
  | fun_cunpacknum__case_6 : forall (c : uN), 
    ((cunpack (storagetype_packtype .I16)) != none) ->
    (wf_lit_ (storagetype_consttype (Option.get! (cunpack (storagetype_packtype .I16)))) (.mk_lit__0 .I32 (.mk_num__0 .I32 (extend__ (psize .I16) (size (lunpack (lanetype_packtype .I16))) .U c)))) ->
    fun_cunpacknum_ .I16 (.mk_lit__2 .I16 c) (.mk_lit__0 .I32 (.mk_num__0 .I32 (extend__ (psize .I16) (size (lunpack (lanetype_packtype .I16))) .U c)))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:364.6-364.12 -/
inductive fun_unop_ : numtype -> unop_ -> num_ -> (List num_) -> Prop where
  | fun_unop__case_0 : forall (i : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (iclz_ (sizenn (numtype_addrtype .I32)) i))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .CLZ) (.mk_num__0 .I32 i) [(.mk_num__0 .I32 (iclz_ (sizenn (numtype_addrtype .I32)) i))]
  | fun_unop__case_1 : forall (i : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (iclz_ (sizenn (numtype_addrtype .I64)) i))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .CLZ) (.mk_num__0 .I64 i) [(.mk_num__0 .I64 (iclz_ (sizenn (numtype_addrtype .I64)) i))]
  | fun_unop__case_2 : forall (i : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (ictz_ (sizenn (numtype_addrtype .I32)) i))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .CTZ) (.mk_num__0 .I32 i) [(.mk_num__0 .I32 (ictz_ (sizenn (numtype_addrtype .I32)) i))]
  | fun_unop__case_3 : forall (i : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (ictz_ (sizenn (numtype_addrtype .I64)) i))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .CTZ) (.mk_num__0 .I64 i) [(.mk_num__0 .I64 (ictz_ (sizenn (numtype_addrtype .I64)) i))]
  | fun_unop__case_4 : forall (i : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (ipopcnt_ (sizenn (numtype_addrtype .I32)) i))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .POPCNT) (.mk_num__0 .I32 i) [(.mk_num__0 .I32 (ipopcnt_ (sizenn (numtype_addrtype .I32)) i))]
  | fun_unop__case_5 : forall (i : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (ipopcnt_ (sizenn (numtype_addrtype .I64)) i))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .POPCNT) (.mk_num__0 .I64 i) [(.mk_num__0 .I64 (ipopcnt_ (sizenn (numtype_addrtype .I64)) i))]
  | fun_unop__case_6 : forall (v_M : Nat) (i : uN) (var_0 : uN), 
    (fun_iextend_ (sizenn (numtype_addrtype .I32)) v_M .S i var_0) ->
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 var_0)) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 (.EXTEND (.mk_sz v_M))) (.mk_num__0 .I32 i) [(.mk_num__0 .I32 var_0)]
  | fun_unop__case_7 : forall (v_M : Nat) (i : uN) (var_0 : uN), 
    (fun_iextend_ (sizenn (numtype_addrtype .I64)) v_M .S i var_0) ->
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 var_0)) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 (.EXTEND (.mk_sz v_M))) (.mk_num__0 .I64 i) [(.mk_num__0 .I64 var_0)]
  | fun_unop__case_8 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fabs_ (sizenn (numtype_Fnn .F32)) f) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .ABS) (.mk_num__1 .F32 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fabs_ (sizenn (numtype_Fnn .F32)) f))
  | fun_unop__case_9 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fabs_ (sizenn (numtype_Fnn .F64)) f) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .ABS) (.mk_num__1 .F64 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fabs_ (sizenn (numtype_Fnn .F64)) f))
  | fun_unop__case_10 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fneg_ (sizenn (numtype_Fnn .F32)) f) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEG) (.mk_num__1 .F32 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fneg_ (sizenn (numtype_Fnn .F32)) f))
  | fun_unop__case_11 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fneg_ (sizenn (numtype_Fnn .F64)) f) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEG) (.mk_num__1 .F64 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fneg_ (sizenn (numtype_Fnn .F64)) f))
  | fun_unop__case_12 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fsqrt_ (sizenn (numtype_Fnn .F32)) f) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .SQRT) (.mk_num__1 .F32 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fsqrt_ (sizenn (numtype_Fnn .F32)) f))
  | fun_unop__case_13 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fsqrt_ (sizenn (numtype_Fnn .F64)) f) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .SQRT) (.mk_num__1 .F64 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fsqrt_ (sizenn (numtype_Fnn .F64)) f))
  | fun_unop__case_14 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fceil_ (sizenn (numtype_Fnn .F32)) f) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .CEIL) (.mk_num__1 .F32 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fceil_ (sizenn (numtype_Fnn .F32)) f))
  | fun_unop__case_15 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fceil_ (sizenn (numtype_Fnn .F64)) f) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .CEIL) (.mk_num__1 .F64 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fceil_ (sizenn (numtype_Fnn .F64)) f))
  | fun_unop__case_16 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (ffloor_ (sizenn (numtype_Fnn .F32)) f) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .FLOOR) (.mk_num__1 .F32 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (ffloor_ (sizenn (numtype_Fnn .F32)) f))
  | fun_unop__case_17 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (ffloor_ (sizenn (numtype_Fnn .F64)) f) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .FLOOR) (.mk_num__1 .F64 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (ffloor_ (sizenn (numtype_Fnn .F64)) f))
  | fun_unop__case_18 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (ftrunc_ (sizenn (numtype_Fnn .F32)) f) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .TRUNC) (.mk_num__1 .F32 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (ftrunc_ (sizenn (numtype_Fnn .F32)) f))
  | fun_unop__case_19 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (ftrunc_ (sizenn (numtype_Fnn .F64)) f) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .TRUNC) (.mk_num__1 .F64 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (ftrunc_ (sizenn (numtype_Fnn .F64)) f))
  | fun_unop__case_20 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fnearest_ (sizenn (numtype_Fnn .F32)) f) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEAREST) (.mk_num__1 .F32 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fnearest_ (sizenn (numtype_Fnn .F32)) f))
  | fun_unop__case_21 : forall (f : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fnearest_ (sizenn (numtype_Fnn .F64)) f) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEAREST) (.mk_num__1 .F64 f) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fnearest_ (sizenn (numtype_Fnn .F64)) f))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:366.6-366.13 -/
inductive fun_binop_ : numtype -> binop_ -> num_ -> num_ -> (List num_) -> Prop where
  | fun_binop__case_0 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (iadd_ (sizenn (numtype_addrtype .I32)) i_1 i_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ADD) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (iadd_ (sizenn (numtype_addrtype .I32)) i_1 i_2))]
  | fun_binop__case_1 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (iadd_ (sizenn (numtype_addrtype .I64)) i_1 i_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ADD) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (iadd_ (sizenn (numtype_addrtype .I64)) i_1 i_2))]
  | fun_binop__case_2 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (isub_ (sizenn (numtype_addrtype .I32)) i_1 i_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .SUB) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (isub_ (sizenn (numtype_addrtype .I32)) i_1 i_2))]
  | fun_binop__case_3 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (isub_ (sizenn (numtype_addrtype .I64)) i_1 i_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .SUB) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (isub_ (sizenn (numtype_addrtype .I64)) i_1 i_2))]
  | fun_binop__case_4 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (imul_ (sizenn (numtype_addrtype .I32)) i_1 i_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .MUL) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (imul_ (sizenn (numtype_addrtype .I32)) i_1 i_2))]
  | fun_binop__case_5 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (imul_ (sizenn (numtype_addrtype .I64)) i_1 i_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .MUL) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (imul_ (sizenn (numtype_addrtype .I64)) i_1 i_2))]
  | fun_binop__case_6 : forall (v_sx : sx) (i_1 : uN) (i_2 : uN) (var_0 : (Option iN)), 
    (fun_idiv_ (sizenn (numtype_addrtype .I32)) v_sx i_1 i_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV v_sx)) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (Option.toList var_0))
  | fun_binop__case_7 : forall (v_sx : sx) (i_1 : uN) (i_2 : uN) (var_0 : (Option iN)), 
    (fun_idiv_ (sizenn (numtype_addrtype .I64)) v_sx i_1 i_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.DIV v_sx)) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (Option.toList var_0))
  | fun_binop__case_8 : forall (v_sx : sx) (i_1 : uN) (i_2 : uN) (var_0 : (Option iN)), 
    (fun_irem_ (sizenn (numtype_addrtype .I32)) v_sx i_1 i_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.REM v_sx)) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (Option.toList var_0))
  | fun_binop__case_9 : forall (v_sx : sx) (i_1 : uN) (i_2 : uN) (var_0 : (Option iN)), 
    (fun_irem_ (sizenn (numtype_addrtype .I64)) v_sx i_1 i_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.REM v_sx)) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (Option.toList var_0))
  | fun_binop__case_10 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (iand_ (sizenn (numtype_addrtype .I32)) i_1 i_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .AND) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (iand_ (sizenn (numtype_addrtype .I32)) i_1 i_2))]
  | fun_binop__case_11 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (iand_ (sizenn (numtype_addrtype .I64)) i_1 i_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .AND) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (iand_ (sizenn (numtype_addrtype .I64)) i_1 i_2))]
  | fun_binop__case_12 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (ior_ (sizenn (numtype_addrtype .I32)) i_1 i_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .OR) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (ior_ (sizenn (numtype_addrtype .I32)) i_1 i_2))]
  | fun_binop__case_13 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (ior_ (sizenn (numtype_addrtype .I64)) i_1 i_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .OR) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (ior_ (sizenn (numtype_addrtype .I64)) i_1 i_2))]
  | fun_binop__case_14 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (ixor_ (sizenn (numtype_addrtype .I32)) i_1 i_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .XOR) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (ixor_ (sizenn (numtype_addrtype .I32)) i_1 i_2))]
  | fun_binop__case_15 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (ixor_ (sizenn (numtype_addrtype .I64)) i_1 i_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .XOR) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (ixor_ (sizenn (numtype_addrtype .I64)) i_1 i_2))]
  | fun_binop__case_16 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (ishl_ (sizenn (numtype_addrtype .I32)) i_1 (.mk_uN (proj_uN_0 i_2))))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .SHL) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (ishl_ (sizenn (numtype_addrtype .I32)) i_1 (.mk_uN (proj_uN_0 i_2))))]
  | fun_binop__case_17 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (ishl_ (sizenn (numtype_addrtype .I64)) i_1 (.mk_uN (proj_uN_0 i_2))))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .SHL) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (ishl_ (sizenn (numtype_addrtype .I64)) i_1 (.mk_uN (proj_uN_0 i_2))))]
  | fun_binop__case_18 : forall (v_sx : sx) (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (ishr_ (sizenn (numtype_addrtype .I32)) v_sx i_1 (.mk_uN (proj_uN_0 i_2))))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.SHR v_sx)) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (ishr_ (sizenn (numtype_addrtype .I32)) v_sx i_1 (.mk_uN (proj_uN_0 i_2))))]
  | fun_binop__case_19 : forall (v_sx : sx) (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (ishr_ (sizenn (numtype_addrtype .I64)) v_sx i_1 (.mk_uN (proj_uN_0 i_2))))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.SHR v_sx)) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (ishr_ (sizenn (numtype_addrtype .I64)) v_sx i_1 (.mk_uN (proj_uN_0 i_2))))]
  | fun_binop__case_20 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (irotl_ (sizenn (numtype_addrtype .I32)) i_1 i_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ROTL) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (irotl_ (sizenn (numtype_addrtype .I32)) i_1 i_2))]
  | fun_binop__case_21 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (irotl_ (sizenn (numtype_addrtype .I64)) i_1 i_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ROTL) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (irotl_ (sizenn (numtype_addrtype .I64)) i_1 i_2))]
  | fun_binop__case_22 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (irotr_ (sizenn (numtype_addrtype .I32)) i_1 i_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ROTR) (.mk_num__0 .I32 i_1) (.mk_num__0 .I32 i_2) [(.mk_num__0 .I32 (irotr_ (sizenn (numtype_addrtype .I32)) i_1 i_2))]
  | fun_binop__case_23 : forall (i_1 : uN) (i_2 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (irotr_ (sizenn (numtype_addrtype .I64)) i_1 i_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ROTR) (.mk_num__0 .I64 i_1) (.mk_num__0 .I64 i_2) [(.mk_num__0 .I64 (irotr_ (sizenn (numtype_addrtype .I64)) i_1 i_2))]
  | fun_binop__case_24 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fadd_ (sizenn (numtype_Fnn .F32)) f_1 f_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .ADD) (.mk_num__1 .F32 f_1) (.mk_num__1 .F32 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fadd_ (sizenn (numtype_Fnn .F32)) f_1 f_2))
  | fun_binop__case_25 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fadd_ (sizenn (numtype_Fnn .F64)) f_1 f_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .ADD) (.mk_num__1 .F64 f_1) (.mk_num__1 .F64 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fadd_ (sizenn (numtype_Fnn .F64)) f_1 f_2))
  | fun_binop__case_26 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fsub_ (sizenn (numtype_Fnn .F32)) f_1 f_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .SUB) (.mk_num__1 .F32 f_1) (.mk_num__1 .F32 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fsub_ (sizenn (numtype_Fnn .F32)) f_1 f_2))
  | fun_binop__case_27 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fsub_ (sizenn (numtype_Fnn .F64)) f_1 f_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .SUB) (.mk_num__1 .F64 f_1) (.mk_num__1 .F64 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fsub_ (sizenn (numtype_Fnn .F64)) f_1 f_2))
  | fun_binop__case_28 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmul_ (sizenn (numtype_Fnn .F32)) f_1 f_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MUL) (.mk_num__1 .F32 f_1) (.mk_num__1 .F32 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fmul_ (sizenn (numtype_Fnn .F32)) f_1 f_2))
  | fun_binop__case_29 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmul_ (sizenn (numtype_Fnn .F64)) f_1 f_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MUL) (.mk_num__1 .F64 f_1) (.mk_num__1 .F64 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fmul_ (sizenn (numtype_Fnn .F64)) f_1 f_2))
  | fun_binop__case_30 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fdiv_ (sizenn (numtype_Fnn .F32)) f_1 f_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .DIV) (.mk_num__1 .F32 f_1) (.mk_num__1 .F32 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fdiv_ (sizenn (numtype_Fnn .F32)) f_1 f_2))
  | fun_binop__case_31 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fdiv_ (sizenn (numtype_Fnn .F64)) f_1 f_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .DIV) (.mk_num__1 .F64 f_1) (.mk_num__1 .F64 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fdiv_ (sizenn (numtype_Fnn .F64)) f_1 f_2))
  | fun_binop__case_32 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmin_ (sizenn (numtype_Fnn .F32)) f_1 f_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MIN) (.mk_num__1 .F32 f_1) (.mk_num__1 .F32 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fmin_ (sizenn (numtype_Fnn .F32)) f_1 f_2))
  | fun_binop__case_33 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmin_ (sizenn (numtype_Fnn .F64)) f_1 f_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MIN) (.mk_num__1 .F64 f_1) (.mk_num__1 .F64 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fmin_ (sizenn (numtype_Fnn .F64)) f_1 f_2))
  | fun_binop__case_34 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmax_ (sizenn (numtype_Fnn .F32)) f_1 f_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MAX) (.mk_num__1 .F32 f_1) (.mk_num__1 .F32 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fmax_ (sizenn (numtype_Fnn .F32)) f_1 f_2))
  | fun_binop__case_35 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmax_ (sizenn (numtype_Fnn .F64)) f_1 f_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MAX) (.mk_num__1 .F64 f_1) (.mk_num__1 .F64 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fmax_ (sizenn (numtype_Fnn .F64)) f_1 f_2))
  | fun_binop__case_36 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fcopysign_ (sizenn (numtype_Fnn .F32)) f_1 f_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .COPYSIGN) (.mk_num__1 .F32 f_1) (.mk_num__1 .F32 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fcopysign_ (sizenn (numtype_Fnn .F32)) f_1 f_2))
  | fun_binop__case_37 : forall (f_1 : fN) (f_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fcopysign_ (sizenn (numtype_Fnn .F64)) f_1 f_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .COPYSIGN) (.mk_num__1 .F64 f_1) (.mk_num__1 .F64 f_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fcopysign_ (sizenn (numtype_Fnn .F64)) f_1 f_2))

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:368.1-369.28 -/
def fun_testop_ : ∀  (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) , u32
  | .I32, (.mk_testop__0 .I32 .EQZ), (.mk_num__0 .I32 i) =>
    (ieqz_ (sizenn (numtype_addrtype .I32)) i)
  | .I64, (.mk_testop__0 .I64 .EQZ), (.mk_num__0 .I64 i) =>
    (ieqz_ (sizenn (numtype_addrtype .I64)) i)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:370.1-371.32 -/
def fun_relop_ : ∀  (v_numtype : numtype) (v_relop_ : relop_) (v_num_ : num_) (v_num__0 : num_) , u32
  | .I32, (.mk_relop__0 .I32 .EQ), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) =>
    (ieq_ (sizenn (numtype_addrtype .I32)) i_1 i_2)
  | .I64, (.mk_relop__0 .I64 .EQ), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) =>
    (ieq_ (sizenn (numtype_addrtype .I64)) i_1 i_2)
  | .I32, (.mk_relop__0 .I32 .NE), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) =>
    (ine_ (sizenn (numtype_addrtype .I32)) i_1 i_2)
  | .I64, (.mk_relop__0 .I64 .NE), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) =>
    (ine_ (sizenn (numtype_addrtype .I64)) i_1 i_2)
  | .I32, (.mk_relop__0 .I32 (.LT v_sx)), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) =>
    (ilt_ (sizenn (numtype_addrtype .I32)) v_sx i_1 i_2)
  | .I64, (.mk_relop__0 .I64 (.LT v_sx)), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) =>
    (ilt_ (sizenn (numtype_addrtype .I64)) v_sx i_1 i_2)
  | .I32, (.mk_relop__0 .I32 (.GT v_sx)), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) =>
    (igt_ (sizenn (numtype_addrtype .I32)) v_sx i_1 i_2)
  | .I64, (.mk_relop__0 .I64 (.GT v_sx)), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) =>
    (igt_ (sizenn (numtype_addrtype .I64)) v_sx i_1 i_2)
  | .I32, (.mk_relop__0 .I32 (.LE v_sx)), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) =>
    (ile_ (sizenn (numtype_addrtype .I32)) v_sx i_1 i_2)
  | .I64, (.mk_relop__0 .I64 (.LE v_sx)), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) =>
    (ile_ (sizenn (numtype_addrtype .I64)) v_sx i_1 i_2)
  | .I32, (.mk_relop__0 .I32 (.GE v_sx)), (.mk_num__0 .I32 i_1), (.mk_num__0 .I32 i_2) =>
    (ige_ (sizenn (numtype_addrtype .I32)) v_sx i_1 i_2)
  | .I64, (.mk_relop__0 .I64 (.GE v_sx)), (.mk_num__0 .I64 i_1), (.mk_num__0 .I64 i_2) =>
    (ige_ (sizenn (numtype_addrtype .I64)) v_sx i_1 i_2)
  | .F32, (.mk_relop__1 .F32 .EQ), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) =>
    (feq_ (sizenn (numtype_Fnn .F32)) f_1 f_2)
  | .F64, (.mk_relop__1 .F64 .EQ), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) =>
    (feq_ (sizenn (numtype_Fnn .F64)) f_1 f_2)
  | .F32, (.mk_relop__1 .F32 .NE), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) =>
    (fne_ (sizenn (numtype_Fnn .F32)) f_1 f_2)
  | .F64, (.mk_relop__1 .F64 .NE), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) =>
    (fne_ (sizenn (numtype_Fnn .F64)) f_1 f_2)
  | .F32, (.mk_relop__1 .F32 .LT), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) =>
    (flt_ (sizenn (numtype_Fnn .F32)) f_1 f_2)
  | .F64, (.mk_relop__1 .F64 .LT), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) =>
    (flt_ (sizenn (numtype_Fnn .F64)) f_1 f_2)
  | .F32, (.mk_relop__1 .F32 .GT), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) =>
    (fgt_ (sizenn (numtype_Fnn .F32)) f_1 f_2)
  | .F64, (.mk_relop__1 .F64 .GT), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) =>
    (fgt_ (sizenn (numtype_Fnn .F64)) f_1 f_2)
  | .F32, (.mk_relop__1 .F32 .LE), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) =>
    (fle_ (sizenn (numtype_Fnn .F32)) f_1 f_2)
  | .F64, (.mk_relop__1 .F64 .LE), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) =>
    (fle_ (sizenn (numtype_Fnn .F64)) f_1 f_2)
  | .F32, (.mk_relop__1 .F32 .GE), (.mk_num__1 .F32 f_1), (.mk_num__1 .F32 f_2) =>
    (fge_ (sizenn (numtype_Fnn .F32)) f_1 f_2)
  | .F64, (.mk_relop__1 .F64 .GE), (.mk_num__1 .F64 f_1), (.mk_num__1 .F64 f_2) =>
    (fge_ (sizenn (numtype_Fnn .F64)) f_1 f_2)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.1-numerics.scalar.spectec:372.6-372.14 -/
inductive fun_cvtop__ : numtype -> numtype -> cvtop__ -> num_ -> (List num_) -> Prop where
  | fun_cvtop___case_0 : forall (v_sx : sx) (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (extend__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I32)) v_sx i_1))) ->
    fun_cvtop__ .I32 .I32 (.mk_cvtop___0 .I32 .I32 (.EXTEND v_sx)) (.mk_num__0 .I32 i_1) [(.mk_num__0 .I32 (extend__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I32)) v_sx i_1))]
  | fun_cvtop___case_1 : forall (v_sx : sx) (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (extend__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I32)) v_sx i_1))) ->
    fun_cvtop__ .I64 .I32 (.mk_cvtop___0 .I64 .I32 (.EXTEND v_sx)) (.mk_num__0 .I64 i_1) [(.mk_num__0 .I32 (extend__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I32)) v_sx i_1))]
  | fun_cvtop___case_2 : forall (v_sx : sx) (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (extend__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I64)) v_sx i_1))) ->
    fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND v_sx)) (.mk_num__0 .I32 i_1) [(.mk_num__0 .I64 (extend__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I64)) v_sx i_1))]
  | fun_cvtop___case_3 : forall (v_sx : sx) (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (extend__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I64)) v_sx i_1))) ->
    fun_cvtop__ .I64 .I64 (.mk_cvtop___0 .I64 .I64 (.EXTEND v_sx)) (.mk_num__0 .I64 i_1) [(.mk_num__0 .I64 (extend__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I64)) v_sx i_1))]
  | fun_cvtop___case_4 : forall (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I32)) i_1))) ->
    fun_cvtop__ .I32 .I32 (.mk_cvtop___0 .I32 .I32 .WRAP) (.mk_num__0 .I32 i_1) [(.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I32)) i_1))]
  | fun_cvtop___case_5 : forall (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I32)) i_1))) ->
    fun_cvtop__ .I64 .I32 (.mk_cvtop___0 .I64 .I32 .WRAP) (.mk_num__0 .I64 i_1) [(.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I32)) i_1))]
  | fun_cvtop___case_6 : forall (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I64)) i_1))) ->
    fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 .WRAP) (.mk_num__0 .I32 i_1) [(.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_addrtype .I64)) i_1))]
  | fun_cvtop___case_7 : forall (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I64)) i_1))) ->
    fun_cvtop__ .I64 .I64 (.mk_cvtop___0 .I64 .I64 .WRAP) (.mk_num__0 .I64 i_1) [(.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_addrtype .I64)) i_1))]
  | fun_cvtop___case_8 : forall (v_sx : sx) (f_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 iter_0))) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)) ->
    fun_cvtop__ .F32 .I32 (.mk_cvtop___2 .F32 .I32 (.TRUNC v_sx)) (.mk_num__1 .F32 f_1) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)))
  | fun_cvtop___case_9 : forall (v_sx : sx) (f_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 iter_0))) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)) ->
    fun_cvtop__ .F64 .I32 (.mk_cvtop___2 .F64 .I32 (.TRUNC v_sx)) (.mk_num__1 .F64 f_1) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)))
  | fun_cvtop___case_10 : forall (v_sx : sx) (f_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 iter_0))) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)) ->
    fun_cvtop__ .F32 .I64 (.mk_cvtop___2 .F32 .I64 (.TRUNC v_sx)) (.mk_num__1 .F32 f_1) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)))
  | fun_cvtop___case_11 : forall (v_sx : sx) (f_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 iter_0))) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)) ->
    fun_cvtop__ .F64 .I64 (.mk_cvtop___2 .F64 .I64 (.TRUNC v_sx)) (.mk_num__1 .F64 f_1) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)))
  | fun_cvtop___case_12 : forall (v_sx : sx) (f_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 iter_0))) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)) ->
    fun_cvtop__ .F32 .I32 (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT v_sx)) (.mk_num__1 .F32 f_1) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)))
  | fun_cvtop___case_13 : forall (v_sx : sx) (f_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 iter_0))) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)) ->
    fun_cvtop__ .F64 .I32 (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT v_sx)) (.mk_num__1 .F64 f_1) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I32)) v_sx f_1)))
  | fun_cvtop___case_14 : forall (v_sx : sx) (f_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 iter_0))) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)) ->
    fun_cvtop__ .F32 .I64 (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT v_sx)) (.mk_num__1 .F32 f_1) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)))
  | fun_cvtop___case_15 : forall (v_sx : sx) (f_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 iter_0))) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)) ->
    fun_cvtop__ .F64 .I64 (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT v_sx)) (.mk_num__1 .F64 f_1) (List.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_addrtype .I64)) v_sx f_1)))
  | fun_cvtop___case_16 : forall (v_sx : sx) (i_1 : uN), 
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 (convert__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_Fnn .F32)) v_sx i_1))) ->
    fun_cvtop__ .I32 .F32 (.mk_cvtop___1 .I32 .F32 (.CONVERT v_sx)) (.mk_num__0 .I32 i_1) [(.mk_num__1 .F32 (convert__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_Fnn .F32)) v_sx i_1))]
  | fun_cvtop___case_17 : forall (v_sx : sx) (i_1 : uN), 
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 (convert__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_Fnn .F32)) v_sx i_1))) ->
    fun_cvtop__ .I64 .F32 (.mk_cvtop___1 .I64 .F32 (.CONVERT v_sx)) (.mk_num__0 .I64 i_1) [(.mk_num__1 .F32 (convert__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_Fnn .F32)) v_sx i_1))]
  | fun_cvtop___case_18 : forall (v_sx : sx) (i_1 : uN), 
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 (convert__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_Fnn .F64)) v_sx i_1))) ->
    fun_cvtop__ .I32 .F64 (.mk_cvtop___1 .I32 .F64 (.CONVERT v_sx)) (.mk_num__0 .I32 i_1) [(.mk_num__1 .F64 (convert__ (sizenn1 (numtype_addrtype .I32)) (sizenn2 (numtype_Fnn .F64)) v_sx i_1))]
  | fun_cvtop___case_19 : forall (v_sx : sx) (i_1 : uN), 
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 (convert__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_Fnn .F64)) v_sx i_1))) ->
    fun_cvtop__ .I64 .F64 (.mk_cvtop___1 .I64 .F64 (.CONVERT v_sx)) (.mk_num__0 .I64 i_1) [(.mk_num__1 .F64 (convert__ (sizenn1 (numtype_addrtype .I64)) (sizenn2 (numtype_Fnn .F64)) v_sx i_1))]
  | fun_cvtop___case_20 : forall (f_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) f_1) ->
    fun_cvtop__ .F32 .F32 (.mk_cvtop___3 .F32 .F32 .PROMOTE) (.mk_num__1 .F32 f_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) f_1))
  | fun_cvtop___case_21 : forall (f_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) f_1) ->
    fun_cvtop__ .F64 .F32 (.mk_cvtop___3 .F64 .F32 .PROMOTE) (.mk_num__1 .F64 f_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) f_1))
  | fun_cvtop___case_22 : forall (f_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) f_1) ->
    fun_cvtop__ .F32 .F64 (.mk_cvtop___3 .F32 .F64 .PROMOTE) (.mk_num__1 .F32 f_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) f_1))
  | fun_cvtop___case_23 : forall (f_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) f_1) ->
    fun_cvtop__ .F64 .F64 (.mk_cvtop___3 .F64 .F64 .PROMOTE) (.mk_num__1 .F64 f_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) f_1))
  | fun_cvtop___case_24 : forall (f_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) f_1) ->
    fun_cvtop__ .F32 .F32 (.mk_cvtop___3 .F32 .F32 .DEMOTE) (.mk_num__1 .F32 f_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) f_1))
  | fun_cvtop___case_25 : forall (f_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) f_1) ->
    fun_cvtop__ .F64 .F32 (.mk_cvtop___3 .F64 .F32 .DEMOTE) (.mk_num__1 .F64 f_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) f_1))
  | fun_cvtop___case_26 : forall (f_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) f_1) ->
    fun_cvtop__ .F32 .F64 (.mk_cvtop___3 .F32 .F64 .DEMOTE) (.mk_num__1 .F32 f_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) f_1))
  | fun_cvtop___case_27 : forall (f_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) f_1) ->
    fun_cvtop__ .F64 .F64 (.mk_cvtop___3 .F64 .F64 .DEMOTE) (.mk_num__1 .F64 f_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) f_1))
  | fun_cvtop___case_28 : forall (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 i_1)) ->
    ((size (numtype_addrtype .I32)) == (size (numtype_Fnn .F32))) ->
    fun_cvtop__ .I32 .F32 (.mk_cvtop___1 .I32 .F32 .REINTERPRET) (.mk_num__0 .I32 i_1) [(reinterpret__ (numtype_addrtype .I32) (numtype_Fnn .F32) (.mk_num__0 .I32 i_1))]
  | fun_cvtop___case_29 : forall (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 i_1)) ->
    ((size (numtype_addrtype .I64)) == (size (numtype_Fnn .F32))) ->
    fun_cvtop__ .I64 .F32 (.mk_cvtop___1 .I64 .F32 .REINTERPRET) (.mk_num__0 .I64 i_1) [(reinterpret__ (numtype_addrtype .I64) (numtype_Fnn .F32) (.mk_num__0 .I64 i_1))]
  | fun_cvtop___case_30 : forall (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I32) (.mk_num__0 .I32 i_1)) ->
    ((size (numtype_addrtype .I32)) == (size (numtype_Fnn .F64))) ->
    fun_cvtop__ .I32 .F64 (.mk_cvtop___1 .I32 .F64 .REINTERPRET) (.mk_num__0 .I32 i_1) [(reinterpret__ (numtype_addrtype .I32) (numtype_Fnn .F64) (.mk_num__0 .I32 i_1))]
  | fun_cvtop___case_31 : forall (i_1 : uN), 
    (wf_num_ (numtype_addrtype .I64) (.mk_num__0 .I64 i_1)) ->
    ((size (numtype_addrtype .I64)) == (size (numtype_Fnn .F64))) ->
    fun_cvtop__ .I64 .F64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET) (.mk_num__0 .I64 i_1) [(reinterpret__ (numtype_addrtype .I64) (numtype_Fnn .F64) (.mk_num__0 .I64 i_1))]
  | fun_cvtop___case_32 : forall (f_1 : fN), 
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 f_1)) ->
    ((size (numtype_Fnn .F32)) == (size (numtype_addrtype .I32))) ->
    fun_cvtop__ .F32 .I32 (.mk_cvtop___2 .F32 .I32 .REINTERPRET) (.mk_num__1 .F32 f_1) [(reinterpret__ (numtype_Fnn .F32) (numtype_addrtype .I32) (.mk_num__1 .F32 f_1))]
  | fun_cvtop___case_33 : forall (f_1 : fN), 
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 f_1)) ->
    ((size (numtype_Fnn .F64)) == (size (numtype_addrtype .I32))) ->
    fun_cvtop__ .F64 .I32 (.mk_cvtop___2 .F64 .I32 .REINTERPRET) (.mk_num__1 .F64 f_1) [(reinterpret__ (numtype_Fnn .F64) (numtype_addrtype .I32) (.mk_num__1 .F64 f_1))]
  | fun_cvtop___case_34 : forall (f_1 : fN), 
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 f_1)) ->
    ((size (numtype_Fnn .F32)) == (size (numtype_addrtype .I64))) ->
    fun_cvtop__ .F32 .I64 (.mk_cvtop___2 .F32 .I64 .REINTERPRET) (.mk_num__1 .F32 f_1) [(reinterpret__ (numtype_Fnn .F32) (numtype_addrtype .I64) (.mk_num__1 .F32 f_1))]
  | fun_cvtop___case_35 : forall (f_1 : fN), 
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 f_1)) ->
    ((size (numtype_Fnn .F64)) == (size (numtype_addrtype .I64))) ->
    fun_cvtop__ .F64 .I64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET) (.mk_num__1 .F64 f_1) [(reinterpret__ (numtype_Fnn .F64) (numtype_addrtype .I64) (.mk_num__1 .F64 f_1))]

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:10.1-10.84 -/
opaque lanes_ : forall (v_shape : shape) (v_vec_ : vec_), (List lane_) := opaqueDef

/- Axiom Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:12.1-13.37 -/
opaque inv_lanes_ : forall (v_shape : shape) (var_0 : (List lane_)), vec_ := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:19.6-19.13 -/
inductive fun_zeroop : shape -> shape -> vcvtop__ -> (Option zero) -> Prop where
  | fun_zeroop_case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I32 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I32 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I8 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I32 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I16 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I32 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I64 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I64 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I8 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I64 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I16 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I64 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_8 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I8 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_9 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I8 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_10 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I8 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I8 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_11 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I16 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I8 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_12 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I16 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_13 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I16 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_14 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I8 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I16 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_15 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_zeroop (.X .I16 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I16 M_2 (.EXTEND v_half v_sx)) none
  | fun_zeroop_case_16 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_zeroop (.X .I32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I32 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_17 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_zeroop (.X .I64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I64 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_18 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_zeroop (.X .I8 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I8 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_19 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_zeroop (.X .I16 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I16 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_20 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_zeroop (.X .I32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I32 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_21 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_zeroop (.X .I64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I64 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_22 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_zeroop (.X .I8 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I8 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_23 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_zeroop (.X .I16 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I16 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_24 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_25 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_26 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_27 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_28 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I8 M_2 (.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_29 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I8 M_2 (.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_30 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I16 M_2 (.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_31 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I16 M_2 (.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_32 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_33 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_34 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_35 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_36 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I8 M_2 (.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_37 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I8 M_2 (.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_38 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I16 M_2 (.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_39 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I16 M_2 (.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_40 : forall (M_1 : Nat) (M_2 : Nat) (v_zero : zero), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F32 M_2 (.DEMOTE v_zero)) (some v_zero)
  | fun_zeroop_case_41 : forall (M_1 : Nat) (M_2 : Nat) (v_zero : zero), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F32 M_2 (.DEMOTE v_zero)) (some v_zero)
  | fun_zeroop_case_42 : forall (M_1 : Nat) (M_2 : Nat) (v_zero : zero), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F64 M_2 (.DEMOTE v_zero)) (some v_zero)
  | fun_zeroop_case_43 : forall (M_1 : Nat) (M_2 : Nat) (v_zero : zero), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F64 M_2 (.DEMOTE v_zero)) (some v_zero)
  | fun_zeroop_case_44 : forall (M_1 : Nat) (M_2 : Nat), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F32 M_2 .PROMOTELOW) none
  | fun_zeroop_case_45 : forall (M_1 : Nat) (M_2 : Nat), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F32 M_2 .PROMOTELOW) none
  | fun_zeroop_case_46 : forall (M_1 : Nat) (M_2 : Nat), fun_zeroop (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F64 M_2 .PROMOTELOW) none
  | fun_zeroop_case_47 : forall (M_1 : Nat) (M_2 : Nat), fun_zeroop (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F64 M_2 .PROMOTELOW) none

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:27.6-27.13 -/
inductive fun_halfop : shape -> shape -> vcvtop__ -> (Option half) -> Prop where
  | fun_halfop_case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I32 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I32 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I8 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I32 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I16 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I32 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I64 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I64 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I8 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I64 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I16 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I64 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_8 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I8 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_9 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I8 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_10 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I8 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I8 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_11 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I16 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I8 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_12 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I16 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_13 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I16 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_14 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I8 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I16 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_15 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx), fun_halfop (.X .I16 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I16 M_2 (.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_16 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_halfop (.X .I32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I32 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_17 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_halfop (.X .I64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I64 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_18 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_halfop (.X .I8 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I8 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_19 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_halfop (.X .I16 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I16 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_20 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_halfop (.X .I32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I32 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_21 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_halfop (.X .I64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I64 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_22 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_halfop (.X .I8 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I8 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_23 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx), fun_halfop (.X .I16 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I16 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_24 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_25 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_26 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_27 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_28 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I8 M_2 (.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_29 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I8 M_2 (.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_30 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I16 M_2 (.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_31 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I16 M_2 (.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_32 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_33 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_34 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_35 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_36 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I8 M_2 (.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_37 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I8 M_2 (.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_38 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I16 M_2 (.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_39 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I16 M_2 (.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_40 : forall (M_1 : Nat) (M_2 : Nat) (v_zero : zero), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F32 M_2 (.DEMOTE v_zero)) none
  | fun_halfop_case_41 : forall (M_1 : Nat) (M_2 : Nat) (v_zero : zero), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F32 M_2 (.DEMOTE v_zero)) none
  | fun_halfop_case_42 : forall (M_1 : Nat) (M_2 : Nat) (v_zero : zero), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F64 M_2 (.DEMOTE v_zero)) none
  | fun_halfop_case_43 : forall (M_1 : Nat) (M_2 : Nat) (v_zero : zero), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F64 M_2 (.DEMOTE v_zero)) none
  | fun_halfop_case_44 : forall (M_1 : Nat) (M_2 : Nat), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F32 M_2 .PROMOTELOW) (some .LOW)
  | fun_halfop_case_45 : forall (M_1 : Nat) (M_2 : Nat), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F32 M_2 .PROMOTELOW) (some .LOW)
  | fun_halfop_case_46 : forall (M_1 : Nat) (M_2 : Nat), fun_halfop (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F64 M_2 .PROMOTELOW) (some .LOW)
  | fun_halfop_case_47 : forall (M_1 : Nat) (M_2 : Nat), fun_halfop (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F64 M_2 .PROMOTELOW) (some .LOW)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:35.1-35.32 -/
def fun_half : ∀  (v_half : half) (nat : Nat) (nat_0 : Nat) , Nat
  | .LOW, i, j =>
    i
  | .HIGH, i, j =>
    j


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:40.1-40.46 -/
def iswizzle_lane_ : ∀  (v_N : N) (var_0 : (List iN)) (v_iN : iN) , iN
  | v_N, c_lst, i =>
    (if ((proj_uN_0 i) < (List.length c_lst)) then (c_lst[(proj_uN_0 i)]!) else (.mk_uN 0))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:41.1-41.54 -/
opaque irelaxed_swizzle_lane_ : forall (v_N : N) (var_0 : (List iN)) (v_iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:54.1-54.73 -/
opaque ivunop_ : forall (v_shape : shape) (f_ : N -> iN -> iN) (v_vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:55.1-55.74 -/
opaque fvunop_ : forall (v_shape : shape) (f_ : N -> fN -> (List fN)) (v_vec_ : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:57.1-57.93 -/
opaque ivbinop_ : forall (v_shape : shape) (f_ : N -> iN -> iN -> iN) (v_vec_ : vec_) (v_vec__0 : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:58.1-58.103 -/
opaque ivbinopsx_ : forall (v_shape : shape) (f_ : N -> sx -> iN -> iN -> iN) (v_sx : sx) (v_vec_ : vec_) (v_vec__0 : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:59.1-59.106 -/
opaque ivbinopsxnd_ : forall (v_shape : shape) (f_ : N -> sx -> iN -> iN -> (List iN)) (v_sx : sx) (v_vec_ : vec_) (v_vec__0 : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:60.1-60.94 -/
opaque fvbinop_ : forall (v_shape : shape) (f_ : N -> fN -> fN -> (List fN)) (v_vec_ : vec_) (v_vec__0 : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:62.1-62.116 -/
opaque ivternopnd_ : forall (v_shape : shape) (f_ : N -> iN -> iN -> iN -> (List iN)) (v_vec_ : vec_) (v_vec__0 : vec_) (v_vec__1 : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:63.1-63.114 -/
opaque fvternop_ : forall (v_shape : shape) (f_ : N -> fN -> fN -> fN -> (List fN)) (v_vec_ : vec_) (v_vec__0 : vec_) (v_vec__1 : vec_), (List vec_) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:65.1-65.90 -/
opaque ivrelop_ : forall (v_shape : shape) (f_ : N -> iN -> iN -> u32) (v_vec_ : vec_) (v_vec__0 : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:66.1-66.100 -/
opaque ivrelopsx_ : forall (v_shape : shape) (f_ : N -> sx -> iN -> iN -> u32) (v_sx : sx) (v_vec_ : vec_) (v_vec__0 : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:67.1-67.90 -/
opaque fvrelop_ : forall (v_shape : shape) (f_ : N -> fN -> fN -> u32) (v_vec_ : vec_) (v_vec__0 : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:69.1-69.85 -/
opaque ivshiftop_ : forall (v_shape : shape) (f_ : N -> iN -> u32 -> iN) (v_vec_ : vec_) (v_u32 : u32), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:70.1-70.95 -/
opaque ivshiftopsx_ : forall (v_shape : shape) (f_ : N -> sx -> iN -> u32 -> iN) (v_sx : sx) (v_vec_ : vec_) (v_u32 : u32), vec_ := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:72.6-72.19 -/
inductive fun_ivbitmaskop_ : shape -> vec_ -> u32 -> Prop where
  | fun_ivbitmaskop__case_0 : forall (v_M : Nat) (v_1 : uN) (c : uN) (c_1_lst : (List lane_)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) c_1)) c_1_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v_1)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    ((ibits_ 32 c) == ((List.map (fun (c_1 : lane_) => (.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn .I32)) .S (Option.get! (proj_lane__2 c_1)) (.mk_uN 0))))) c_1_lst) ++ (List.replicate (((32 : Nat) - (v_M : Nat)) : Nat) (.mk_bit 0)))) ->
    fun_ivbitmaskop_ (.X .I32 (.mk_dim v_M)) v_1 (irev_ 32 c)
  | fun_ivbitmaskop__case_1 : forall (v_M : Nat) (v_1 : uN) (c : uN) (c_1_lst : (List lane_)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) c_1)) c_1_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v_1)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    ((ibits_ 32 c) == ((List.map (fun (c_1 : lane_) => (.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn .I64)) .S (Option.get! (proj_lane__2 c_1)) (.mk_uN 0))))) c_1_lst) ++ (List.replicate (((32 : Nat) - (v_M : Nat)) : Nat) (.mk_bit 0)))) ->
    fun_ivbitmaskop_ (.X .I64 (.mk_dim v_M)) v_1 (irev_ 32 c)
  | fun_ivbitmaskop__case_2 : forall (v_M : Nat) (v_1 : uN) (c : uN) (c_1_lst : (List lane_)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) c_1)) c_1_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v_1)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    ((ibits_ 32 c) == ((List.map (fun (c_1 : lane_) => (.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn .I8)) .S (Option.get! (proj_lane__2 c_1)) (.mk_uN 0))))) c_1_lst) ++ (List.replicate (((32 : Nat) - (v_M : Nat)) : Nat) (.mk_bit 0)))) ->
    fun_ivbitmaskop_ (.X .I8 (.mk_dim v_M)) v_1 (irev_ 32 c)
  | fun_ivbitmaskop__case_3 : forall (v_M : Nat) (v_1 : uN) (c : uN) (c_1_lst : (List lane_)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) c_1)) c_1_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v_1)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    ((ibits_ 32 c) == ((List.map (fun (c_1 : lane_) => (.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn .I16)) .S (Option.get! (proj_lane__2 c_1)) (.mk_uN 0))))) c_1_lst) ++ (List.replicate (((32 : Nat) - (v_M : Nat)) : Nat) (.mk_bit 0)))) ->
    fun_ivbitmaskop_ (.X .I16 (.mk_dim v_M)) v_1 (irev_ 32 c)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:73.1-73.96 -/
opaque ivswizzlop_ : forall (v_shape : shape) (f_ : N -> (List iN) -> iN -> iN) (v_vec_ : vec_) (v_vec__0 : vec_), vec_ := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:74.6-74.18 -/
inductive fun_ivshufflop_ : shape -> (List laneidx) -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_ivshufflop__case_0 : forall (v_M : Nat) (i_lst : (List laneidx)) (v_1 : uN) (v_2 : uN) (c_lst : (List lane_)) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)), 
    Forall (fun (c : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) c)) c_lst ->
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) c_2)) c_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v_2)) ->
    Forall (fun (i : laneidx) => ((proj_uN_0 i) < (List.length (c_1_lst ++ c_2_lst)))) i_lst ->
    (c_lst == (List.map (fun (i : laneidx) => ((c_1_lst ++ c_2_lst)[(proj_uN_0 i)]!)) i_lst)) ->
    fun_ivshufflop_ (.X .I32 (.mk_dim v_M)) i_lst v_1 v_2 (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) c_lst)
  | fun_ivshufflop__case_1 : forall (v_M : Nat) (i_lst : (List laneidx)) (v_1 : uN) (v_2 : uN) (c_lst : (List lane_)) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)), 
    Forall (fun (c : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) c)) c_lst ->
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) c_2)) c_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v_2)) ->
    Forall (fun (i : laneidx) => ((proj_uN_0 i) < (List.length (c_1_lst ++ c_2_lst)))) i_lst ->
    (c_lst == (List.map (fun (i : laneidx) => ((c_1_lst ++ c_2_lst)[(proj_uN_0 i)]!)) i_lst)) ->
    fun_ivshufflop_ (.X .I64 (.mk_dim v_M)) i_lst v_1 v_2 (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) c_lst)
  | fun_ivshufflop__case_2 : forall (v_M : Nat) (i_lst : (List laneidx)) (v_1 : uN) (v_2 : uN) (c_lst : (List lane_)) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)), 
    Forall (fun (c : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) c)) c_lst ->
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) c_2)) c_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v_2)) ->
    Forall (fun (i : laneidx) => ((proj_uN_0 i) < (List.length (c_1_lst ++ c_2_lst)))) i_lst ->
    (c_lst == (List.map (fun (i : laneidx) => ((c_1_lst ++ c_2_lst)[(proj_uN_0 i)]!)) i_lst)) ->
    fun_ivshufflop_ (.X .I8 (.mk_dim v_M)) i_lst v_1 v_2 (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) c_lst)
  | fun_ivshufflop__case_3 : forall (v_M : Nat) (i_lst : (List laneidx)) (v_1 : uN) (v_2 : uN) (c_lst : (List lane_)) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)), 
    Forall (fun (c : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) c)) c_lst ->
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) c_2)) c_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v_2)) ->
    Forall (fun (i : laneidx) => ((proj_uN_0 i) < (List.length (c_1_lst ++ c_2_lst)))) i_lst ->
    (c_lst == (List.map (fun (i : laneidx) => ((c_1_lst ++ c_2_lst)[(proj_uN_0 i)]!)) i_lst)) ->
    fun_ivshufflop_ (.X .I16 (.mk_dim v_M)) i_lst v_1 v_2 (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) c_lst)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:165.1-166.28 -/
def vvunop_ : ∀  (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) , (List vec_)
  | v_Vnn, .NOT, v =>
    [(inot_ (vsizenn v_Vnn) v)]


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:167.1-168.31 -/
def vvbinop_ : ∀  (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (v_vec__0 : vec_) , (List vec_)
  | v_Vnn, .AND, v_1, v_2 =>
    [(iand_ (vsizenn v_Vnn) v_1 v_2)]
  | v_Vnn, .ANDNOT, v_1, v_2 =>
    [(iandnot_ (vsizenn v_Vnn) v_1 v_2)]
  | v_Vnn, .OR, v_1, v_2 =>
    [(ior_ (vsizenn v_Vnn) v_1 v_2)]
  | v_Vnn, .XOR, v_1, v_2 =>
    [(ixor_ (vsizenn v_Vnn) v_1 v_2)]


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:169.1-170.34 -/
def vvternop_ : ∀  (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (v_vec__0 : vec_) (v_vec__1 : vec_) , (List vec_)
  | v_Vnn, .BITSELECT, v_1, v_2, v_3 =>
    [(ibitselect_ (vsizenn v_Vnn) v_1 v_2 v_3)]


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:172.6-172.13 -/
inductive fun_vunop_ : shape -> vunop_ -> vec_ -> (List vec_) -> Prop where
  | fun_vunop__case_0 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .ABS) v (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fabs_ v)
  | fun_vunop__case_1 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .ABS) v (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fabs_ v)
  | fun_vunop__case_2 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .NEG) v (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fneg_ v)
  | fun_vunop__case_3 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .NEG) v (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fneg_ v)
  | fun_vunop__case_4 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .SQRT) v (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fsqrt_ v)
  | fun_vunop__case_5 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .SQRT) v (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fsqrt_ v)
  | fun_vunop__case_6 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .CEIL) v (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fceil_ v)
  | fun_vunop__case_7 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .CEIL) v (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fceil_ v)
  | fun_vunop__case_8 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .FLOOR) v (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) ffloor_ v)
  | fun_vunop__case_9 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .FLOOR) v (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) ffloor_ v)
  | fun_vunop__case_10 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .TRUNC) v (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) ftrunc_ v)
  | fun_vunop__case_11 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .TRUNC) v (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) ftrunc_ v)
  | fun_vunop__case_12 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .NEAREST) v (fvunop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fnearest_ v)
  | fun_vunop__case_13 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .NEAREST) v (fvunop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fnearest_ v)
  | fun_vunop__case_14 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I32 (.mk_dim v_M)) (.mk_vunop__0 .I32 v_M .ABS) v (ivunop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iabs_ v)
  | fun_vunop__case_15 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I64 (.mk_dim v_M)) (.mk_vunop__0 .I64 v_M .ABS) v (ivunop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iabs_ v)
  | fun_vunop__case_16 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I8 (.mk_dim v_M)) (.mk_vunop__0 .I8 v_M .ABS) v (ivunop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iabs_ v)
  | fun_vunop__case_17 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I16 (.mk_dim v_M)) (.mk_vunop__0 .I16 v_M .ABS) v (ivunop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iabs_ v)
  | fun_vunop__case_18 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I32 (.mk_dim v_M)) (.mk_vunop__0 .I32 v_M .NEG) v (ivunop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ineg_ v)
  | fun_vunop__case_19 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I64 (.mk_dim v_M)) (.mk_vunop__0 .I64 v_M .NEG) v (ivunop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ineg_ v)
  | fun_vunop__case_20 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I8 (.mk_dim v_M)) (.mk_vunop__0 .I8 v_M .NEG) v (ivunop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ineg_ v)
  | fun_vunop__case_21 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I16 (.mk_dim v_M)) (.mk_vunop__0 .I16 v_M .NEG) v (ivunop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ineg_ v)
  | fun_vunop__case_22 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I32 (.mk_dim v_M)) (.mk_vunop__0 .I32 v_M .POPCNT) v (ivunop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ipopcnt_ v)
  | fun_vunop__case_23 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I64 (.mk_dim v_M)) (.mk_vunop__0 .I64 v_M .POPCNT) v (ivunop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ipopcnt_ v)
  | fun_vunop__case_24 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I8 (.mk_dim v_M)) (.mk_vunop__0 .I8 v_M .POPCNT) v (ivunop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ipopcnt_ v)
  | fun_vunop__case_25 : forall (v_M : Nat) (v : uN), fun_vunop_ (.X .I16 (.mk_dim v_M)) (.mk_vunop__0 .I16 v_M .POPCNT) v (ivunop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ipopcnt_ v)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:174.6-174.14 -/
inductive fun_vbinop_ : shape -> vbinop_ -> vec_ -> vec_ -> (List vec_) -> Prop where
  | fun_vbinop__case_0 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .ADD) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iadd_ v_1 v_2)
  | fun_vbinop__case_1 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .ADD) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iadd_ v_1 v_2)
  | fun_vbinop__case_2 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .ADD) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iadd_ v_1 v_2)
  | fun_vbinop__case_3 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .ADD) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iadd_ v_1 v_2)
  | fun_vbinop__case_4 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .SUB) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) isub_ v_1 v_2)
  | fun_vbinop__case_5 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .SUB) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) isub_ v_1 v_2)
  | fun_vbinop__case_6 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .SUB) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) isub_ v_1 v_2)
  | fun_vbinop__case_7 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .SUB) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) isub_ v_1 v_2)
  | fun_vbinop__case_8 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .MUL) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) imul_ v_1 v_2)
  | fun_vbinop__case_9 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .MUL) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) imul_ v_1 v_2)
  | fun_vbinop__case_10 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .MUL) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) imul_ v_1 v_2)
  | fun_vbinop__case_11 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .MUL) v_1 v_2 (ivbinop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) imul_ v_1 v_2)
  | fun_vbinop__case_12 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M (.ADD_SAT v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2)
  | fun_vbinop__case_13 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M (.ADD_SAT v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2)
  | fun_vbinop__case_14 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M (.ADD_SAT v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2)
  | fun_vbinop__case_15 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M (.ADD_SAT v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2)
  | fun_vbinop__case_16 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M (.SUB_SAT v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) isub_sat_ v_sx v_1 v_2)
  | fun_vbinop__case_17 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M (.SUB_SAT v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) isub_sat_ v_sx v_1 v_2)
  | fun_vbinop__case_18 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M (.SUB_SAT v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) isub_sat_ v_sx v_1 v_2)
  | fun_vbinop__case_19 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M (.SUB_SAT v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) isub_sat_ v_sx v_1 v_2)
  | fun_vbinop__case_20 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M (.MIN v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) imin_ v_sx v_1 v_2)
  | fun_vbinop__case_21 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M (.MIN v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) imin_ v_sx v_1 v_2)
  | fun_vbinop__case_22 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M (.MIN v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) imin_ v_sx v_1 v_2)
  | fun_vbinop__case_23 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M (.MIN v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) imin_ v_sx v_1 v_2)
  | fun_vbinop__case_24 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M (.MAX v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) imax_ v_sx v_1 v_2)
  | fun_vbinop__case_25 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M (.MAX v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) imax_ v_sx v_1 v_2)
  | fun_vbinop__case_26 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M (.MAX v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) imax_ v_sx v_1 v_2)
  | fun_vbinop__case_27 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M (.MAX v_sx)) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) imax_ v_sx v_1 v_2)
  | fun_vbinop__case_28 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .AVGRU) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iavgr_ .U v_1 v_2)
  | fun_vbinop__case_29 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .AVGRU) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iavgr_ .U v_1 v_2)
  | fun_vbinop__case_30 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .AVGRU) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iavgr_ .U v_1 v_2)
  | fun_vbinop__case_31 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .AVGRU) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iavgr_ .U v_1 v_2)
  | fun_vbinop__case_32 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .Q15MULR_SATS) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) iq15mulr_sat_ .S v_1 v_2)
  | fun_vbinop__case_33 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .Q15MULR_SATS) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) iq15mulr_sat_ .S v_1 v_2)
  | fun_vbinop__case_34 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .Q15MULR_SATS) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) iq15mulr_sat_ .S v_1 v_2)
  | fun_vbinop__case_35 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .Q15MULR_SATS) v_1 v_2 (ivbinopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) iq15mulr_sat_ .S v_1 v_2)
  | fun_vbinop__case_36 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .RELAXED_Q15MULRS) v_1 v_2 (ivbinopsxnd_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) irelaxed_q15mulr_ .S v_1 v_2)
  | fun_vbinop__case_37 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .RELAXED_Q15MULRS) v_1 v_2 (ivbinopsxnd_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) irelaxed_q15mulr_ .S v_1 v_2)
  | fun_vbinop__case_38 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .RELAXED_Q15MULRS) v_1 v_2 (ivbinopsxnd_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) irelaxed_q15mulr_ .S v_1 v_2)
  | fun_vbinop__case_39 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .RELAXED_Q15MULRS) v_1 v_2 (ivbinopsxnd_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) irelaxed_q15mulr_ .S v_1 v_2)
  | fun_vbinop__case_40 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .ADD) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fadd_ v_1 v_2)
  | fun_vbinop__case_41 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .ADD) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fadd_ v_1 v_2)
  | fun_vbinop__case_42 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .SUB) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fsub_ v_1 v_2)
  | fun_vbinop__case_43 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .SUB) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fsub_ v_1 v_2)
  | fun_vbinop__case_44 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .MUL) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fmul_ v_1 v_2)
  | fun_vbinop__case_45 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .MUL) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fmul_ v_1 v_2)
  | fun_vbinop__case_46 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .DIV) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fdiv_ v_1 v_2)
  | fun_vbinop__case_47 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .DIV) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fdiv_ v_1 v_2)
  | fun_vbinop__case_48 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .MIN) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fmin_ v_1 v_2)
  | fun_vbinop__case_49 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .MIN) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fmin_ v_1 v_2)
  | fun_vbinop__case_50 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .MAX) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fmax_ v_1 v_2)
  | fun_vbinop__case_51 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .MAX) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fmax_ v_1 v_2)
  | fun_vbinop__case_52 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .PMIN) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fpmin_ v_1 v_2)
  | fun_vbinop__case_53 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .PMIN) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fpmin_ v_1 v_2)
  | fun_vbinop__case_54 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .PMAX) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fpmax_ v_1 v_2)
  | fun_vbinop__case_55 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .PMAX) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fpmax_ v_1 v_2)
  | fun_vbinop__case_56 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .RELAXED_MIN) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) frelaxed_min_ v_1 v_2)
  | fun_vbinop__case_57 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .RELAXED_MIN) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) frelaxed_min_ v_1 v_2)
  | fun_vbinop__case_58 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .RELAXED_MAX) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) frelaxed_max_ v_1 v_2)
  | fun_vbinop__case_59 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .RELAXED_MAX) v_1 v_2 (fvbinop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) frelaxed_max_ v_1 v_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:176.6-176.15 -/
inductive fun_vternop_ : shape -> vternop_ -> vec_ -> vec_ -> vec_ -> (List vec_) -> Prop where
  | fun_vternop__case_0 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN), fun_vternop_ (.X .I32 (.mk_dim v_M)) (.mk_vternop__0 .I32 v_M .RELAXED_LANESELECT) v_1 v_2 v_3 (ivternopnd_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3)
  | fun_vternop__case_1 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN), fun_vternop_ (.X .I64 (.mk_dim v_M)) (.mk_vternop__0 .I64 v_M .RELAXED_LANESELECT) v_1 v_2 v_3 (ivternopnd_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3)
  | fun_vternop__case_2 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN), fun_vternop_ (.X .I8 (.mk_dim v_M)) (.mk_vternop__0 .I8 v_M .RELAXED_LANESELECT) v_1 v_2 v_3 (ivternopnd_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3)
  | fun_vternop__case_3 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN), fun_vternop_ (.X .I16 (.mk_dim v_M)) (.mk_vternop__0 .I16 v_M .RELAXED_LANESELECT) v_1 v_2 v_3 (ivternopnd_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3)
  | fun_vternop__case_4 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN), fun_vternop_ (.X .F32 (.mk_dim v_M)) (.mk_vternop__1 .F32 v_M .RELAXED_MADD) v_1 v_2 v_3 (fvternop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) frelaxed_madd_ v_1 v_2 v_3)
  | fun_vternop__case_5 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN), fun_vternop_ (.X .F64 (.mk_dim v_M)) (.mk_vternop__1 .F64 v_M .RELAXED_MADD) v_1 v_2 v_3 (fvternop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) frelaxed_madd_ v_1 v_2 v_3)
  | fun_vternop__case_6 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN), fun_vternop_ (.X .F32 (.mk_dim v_M)) (.mk_vternop__1 .F32 v_M .RELAXED_NMADD) v_1 v_2 v_3 (fvternop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) frelaxed_nmadd_ v_1 v_2 v_3)
  | fun_vternop__case_7 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN), fun_vternop_ (.X .F64 (.mk_dim v_M)) (.mk_vternop__1 .F64 v_M .RELAXED_NMADD) v_1 v_2 v_3 (fvternop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) frelaxed_nmadd_ v_1 v_2 v_3)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:178.6-178.14 -/
inductive fun_vrelop_ : shape -> vrelop_ -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_vrelop__case_0 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M .EQ) v_1 v_2 (ivrelop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ieq_ v_1 v_2)
  | fun_vrelop__case_1 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M .EQ) v_1 v_2 (ivrelop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ieq_ v_1 v_2)
  | fun_vrelop__case_2 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M .EQ) v_1 v_2 (ivrelop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ieq_ v_1 v_2)
  | fun_vrelop__case_3 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M .EQ) v_1 v_2 (ivrelop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ieq_ v_1 v_2)
  | fun_vrelop__case_4 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M .NE) v_1 v_2 (ivrelop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ine_ v_1 v_2)
  | fun_vrelop__case_5 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M .NE) v_1 v_2 (ivrelop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ine_ v_1 v_2)
  | fun_vrelop__case_6 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M .NE) v_1 v_2 (ivrelop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ine_ v_1 v_2)
  | fun_vrelop__case_7 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M .NE) v_1 v_2 (ivrelop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ine_ v_1 v_2)
  | fun_vrelop__case_8 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M (.LT v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ilt_ v_sx v_1 v_2)
  | fun_vrelop__case_9 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M (.LT v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ilt_ v_sx v_1 v_2)
  | fun_vrelop__case_10 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M (.LT v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ilt_ v_sx v_1 v_2)
  | fun_vrelop__case_11 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M (.LT v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ilt_ v_sx v_1 v_2)
  | fun_vrelop__case_12 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M (.GT v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) igt_ v_sx v_1 v_2)
  | fun_vrelop__case_13 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M (.GT v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) igt_ v_sx v_1 v_2)
  | fun_vrelop__case_14 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M (.GT v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) igt_ v_sx v_1 v_2)
  | fun_vrelop__case_15 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M (.GT v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) igt_ v_sx v_1 v_2)
  | fun_vrelop__case_16 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M (.LE v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ile_ v_sx v_1 v_2)
  | fun_vrelop__case_17 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M (.LE v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ile_ v_sx v_1 v_2)
  | fun_vrelop__case_18 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M (.LE v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ile_ v_sx v_1 v_2)
  | fun_vrelop__case_19 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M (.LE v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ile_ v_sx v_1 v_2)
  | fun_vrelop__case_20 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M (.GE v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ige_ v_sx v_1 v_2)
  | fun_vrelop__case_21 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M (.GE v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ige_ v_sx v_1 v_2)
  | fun_vrelop__case_22 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M (.GE v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ige_ v_sx v_1 v_2)
  | fun_vrelop__case_23 : forall (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M (.GE v_sx)) v_1 v_2 (ivrelopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ige_ v_sx v_1 v_2)
  | fun_vrelop__case_24 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .EQ) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) feq_ v_1 v_2)
  | fun_vrelop__case_25 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .EQ) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) feq_ v_1 v_2)
  | fun_vrelop__case_26 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .NE) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fne_ v_1 v_2)
  | fun_vrelop__case_27 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .NE) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fne_ v_1 v_2)
  | fun_vrelop__case_28 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .LT) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) flt_ v_1 v_2)
  | fun_vrelop__case_29 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .LT) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) flt_ v_1 v_2)
  | fun_vrelop__case_30 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .GT) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fgt_ v_1 v_2)
  | fun_vrelop__case_31 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .GT) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fgt_ v_1 v_2)
  | fun_vrelop__case_32 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .LE) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fle_ v_1 v_2)
  | fun_vrelop__case_33 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .LE) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fle_ v_1 v_2)
  | fun_vrelop__case_34 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .GE) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) fge_ v_1 v_2)
  | fun_vrelop__case_35 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .GE) v_1 v_2 (fvrelop_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) fge_ v_1 v_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:181.6-181.15 -/
inductive fun_lcvtop__ : shape -> shape -> vcvtop__ -> lane_ -> (List lane_) -> Prop where
  | fun_lcvtop___case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Jnn .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I32 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I32 c_1) [(.mk_lane__2 .I32 c)]
  | fun_lcvtop___case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Jnn .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I32 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I64 c_1) [(.mk_lane__2 .I32 c)]
  | fun_lcvtop___case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Jnn .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I8 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I32 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I8 c_1) [(.mk_lane__2 .I32 c)]
  | fun_lcvtop___case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Jnn .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I16 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I32 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I16 c_1) [(.mk_lane__2 .I32 c)]
  | fun_lcvtop___case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Jnn .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I64 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I32 c_1) [(.mk_lane__2 .I64 c)]
  | fun_lcvtop___case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Jnn .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I64 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I64 c_1) [(.mk_lane__2 .I64 c)]
  | fun_lcvtop___case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Jnn .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I8 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I64 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I8 c_1) [(.mk_lane__2 .I64 c)]
  | fun_lcvtop___case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Jnn .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I16 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I64 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I16 c_1) [(.mk_lane__2 .I64 c)]
  | fun_lcvtop___case_8 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Jnn .I8)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I8 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I32 c_1) [(.mk_lane__2 .I8 c)]
  | fun_lcvtop___case_9 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Jnn .I8)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I8 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I64 c_1) [(.mk_lane__2 .I8 c)]
  | fun_lcvtop___case_10 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Jnn .I8)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I8 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I8 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I8 c_1) [(.mk_lane__2 .I8 c)]
  | fun_lcvtop___case_11 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Jnn .I8)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I16 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I8 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I16 c_1) [(.mk_lane__2 .I8 c)]
  | fun_lcvtop___case_12 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Jnn .I16)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I32 M_1 .I16 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I32 c_1) [(.mk_lane__2 .I16 c)]
  | fun_lcvtop___case_13 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Jnn .I16)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I64 M_1 .I16 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I64 c_1) [(.mk_lane__2 .I16 c)]
  | fun_lcvtop___case_14 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Jnn .I16)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I8 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I8 M_1 .I16 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I8 c_1) [(.mk_lane__2 .I16 c)]
  | fun_lcvtop___case_15 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c)) ->
    (c == (extend__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Jnn .I16)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I16 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.mk_vcvtop___0 .I16 M_1 .I16 M_2 (.EXTEND v_half v_sx)) (.mk_lane__2 .I16 c_1) [(.mk_lane__2 .I16 c)]
  | fun_lcvtop___case_16 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (c_1 : uN) (c : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) ->
    (c == (convert__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Fnn .F32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I32 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) (.mk_lane__2 .I32 c_1) [(.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))]
  | fun_lcvtop___case_17 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (c_1 : uN) (c : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) ->
    (c == (convert__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Fnn .F32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I64 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) (.mk_lane__2 .I64 c_1) [(.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))]
  | fun_lcvtop___case_18 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (c_1 : uN) (c : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) ->
    (c == (convert__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Fnn .F32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I8 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I8 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) (.mk_lane__2 .I8 c_1) [(.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))]
  | fun_lcvtop___case_19 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (c_1 : uN) (c : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) ->
    (c == (convert__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Fnn .F32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I16 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___1 .I16 M_1 .F32 M_2 (.CONVERT half_opt v_sx)) (.mk_lane__2 .I16 c_1) [(.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))]
  | fun_lcvtop___case_20 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (c_1 : uN) (c : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) ->
    (c == (convert__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Fnn .F64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I32 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) (.mk_lane__2 .I32 c_1) [(.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))]
  | fun_lcvtop___case_21 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (c_1 : uN) (c : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) ->
    (c == (convert__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Fnn .F64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I64 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) (.mk_lane__2 .I64 c_1) [(.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))]
  | fun_lcvtop___case_22 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (c_1 : uN) (c : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) ->
    (c == (convert__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Fnn .F64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I8 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I8 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) (.mk_lane__2 .I8 c_1) [(.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))]
  | fun_lcvtop___case_23 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (c_1 : uN) (c : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) ->
    (c == (convert__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Fnn .F64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .I16 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___1 .I16 M_1 .F64 M_2 (.CONVERT half_opt v_sx)) (.mk_lane__2 .I16 c_1) [(.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))]
  | fun_lcvtop___case_24 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_25 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_26 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_27 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_28 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_29 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_30 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_31 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_32 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_33 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_34 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_35 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_36 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_37 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_38 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_39 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.TRUNC_SAT v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_40 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_41 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_42 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_43 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_44 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_45 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_46 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_47 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F32 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_48 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_49 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_50 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_51 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I32) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I32)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I32 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I32) (.mk_num__0 .I32 c))) c_opt))
  | fun_lcvtop___case_52 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_53 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_54 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_55 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (c_1 : fN) (c_opt : (Option iN)), 
    Forall (fun (c : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_addrtype .I64) (.mk_dim M_2))) (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c)))) (Option.toList c_opt) ->
    (c_opt == (relaxed_trunc__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_addrtype .I64)) v_sx c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vcvtop___2 .F64 M_1 .I64 M_2 (.RELAXED_TRUNC v_sx zero_opt)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (Option.toList (Option.map (fun (c : iN) => (.mk_lane__0 (numtype_addrtype .I64) (.mk_num__0 .I64 c))) c_opt))
  | fun_lcvtop___case_56 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c)))) c_lst ->
    (c_lst == (demote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F32)) c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F32 M_2 (.DEMOTE .ZERO)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) c_lst)
  | fun_lcvtop___case_57 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c)))) c_lst ->
    (c_lst == (demote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F32)) c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F32 M_2 (.DEMOTE .ZERO)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) c_lst)
  | fun_lcvtop___case_58 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c)))) c_lst ->
    (c_lst == (demote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F64)) c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F64 M_2 (.DEMOTE .ZERO)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) c_lst)
  | fun_lcvtop___case_59 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c)))) c_lst ->
    (c_lst == (demote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F64)) c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F64 M_2 (.DEMOTE .ZERO)) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) c_lst)
  | fun_lcvtop___case_60 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c)))) c_lst ->
    (c_lst == (demote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F32)) c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F32 M_2 (.DEMOTE .ZERO)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) c_lst)
  | fun_lcvtop___case_61 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c)))) c_lst ->
    (c_lst == (demote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F32)) c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F32 M_2 (.DEMOTE .ZERO)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) c_lst)
  | fun_lcvtop___case_62 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c)))) c_lst ->
    (c_lst == (demote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F64)) c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F64 M_2 (.DEMOTE .ZERO)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) c_lst)
  | fun_lcvtop___case_63 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c)))) c_lst ->
    (c_lst == (demote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F64)) c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F64 M_2 (.DEMOTE .ZERO)) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) c_lst)
  | fun_lcvtop___case_64 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c)))) c_lst ->
    (c_lst == (promote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F32)) c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F32 M_2 .PROMOTELOW) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) c_lst)
  | fun_lcvtop___case_65 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c)))) c_lst ->
    (c_lst == (promote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F32)) c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F32 M_2 .PROMOTELOW) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) c_lst)
  | fun_lcvtop___case_66 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c)))) c_lst ->
    (c_lst == (promote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F64)) c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F64 M_2 .PROMOTELOW) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) c_lst)
  | fun_lcvtop___case_67 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c)))) c_lst ->
    (c_lst == (promote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F64)) c_1)) ->
    fun_lcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F32 M_1 .F64 M_2 .PROMOTELOW) (.mk_lane__0 .F32 (.mk_num__1 .F32 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) c_lst)
  | fun_lcvtop___case_68 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c)))) c_lst ->
    (c_lst == (promote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F32)) c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F32 M_2 .PROMOTELOW) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) c_lst)
  | fun_lcvtop___case_69 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c)))) c_lst ->
    (c_lst == (promote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F32)) c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F32 M_2 .PROMOTELOW) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 c))) c_lst)
  | fun_lcvtop___case_70 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c)))) c_lst ->
    (c_lst == (promote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F64)) c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F64 M_2 .PROMOTELOW) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) c_lst)
  | fun_lcvtop___case_71 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (c_lst : (List fN)), 
    Forall (fun (c : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c)))) c_lst ->
    (c_lst == (promote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F64)) c_1)) ->
    fun_lcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.mk_vcvtop___3 .F64 M_1 .F64 M_2 .PROMOTELOW) (.mk_lane__0 .F64 (.mk_num__1 .F64 c_1)) (List.map (fun (c : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 c))) c_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:183.6-183.15 -/
inductive fun_vcvtop__ : shape -> shape -> vcvtop__ -> vec_ -> vec_ -> Prop where
  | fun_vcvtop___case_0 : forall (Lnn_1 : lanetype) (v_M : Nat) (Lnn_2 : lanetype) (vcvtop : vcvtop__) (v_1 : uN) (v : uN) (c_1_lst : (List lane_)) (c_lst_lst : (List (List lane_))) (var_2_lst : (List (List lane_))) (var_1 : (Option zero)) (var_0 : (Option half)), 
    ((List.length var_2_lst) == (List.length c_1_lst)) ->
    Forall₂ (fun (var_2 : (List lane_)) (c_1 : lane_) => (fun_lcvtop__ (.X Lnn_1 (.mk_dim v_M)) (.X Lnn_2 (.mk_dim v_M)) vcvtop c_1 var_2)) var_2_lst c_1_lst ->
    (fun_zeroop (.X Lnn_1 (.mk_dim v_M)) (.X Lnn_2 (.mk_dim v_M)) vcvtop var_1) ->
    (fun_halfop (.X Lnn_1 (.mk_dim v_M)) (.X Lnn_2 (.mk_dim v_M)) vcvtop var_0) ->
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X Lnn_1 (.mk_dim v_M))) c_1)) c_1_lst ->
    Forall (fun (c_lst : (List lane_)) => Forall (fun (c : lane_) => (wf_lane_ Lnn_2 c)) c_lst) c_lst_lst ->
    ((var_0 == none) && (var_1 == none)) ->
    (c_1_lst == (lanes_ (.X Lnn_1 (.mk_dim v_M)) v_1)) ->
    (c_lst_lst == (setproduct_ lane_ var_2_lst)) ->
    ((List.length (List.map (fun (c_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim v_M)) c_lst)) c_lst_lst)) > 0) ->
    (List.contains (List.map (fun (c_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim v_M)) c_lst)) c_lst_lst) v) ->
    fun_vcvtop__ (.X Lnn_1 (.mk_dim v_M)) (.X Lnn_2 (.mk_dim v_M)) vcvtop v_1 v
  | fun_vcvtop___case_1 : forall (Lnn_1 : lanetype) (M_1 : Nat) (Lnn_2 : lanetype) (M_2 : Nat) (vcvtop : vcvtop__) (v_1 : uN) (v : uN) (v_half : half) (c_1_lst : (List lane_)) (c_lst_lst : (List (List lane_))) (var_1_lst : (List (List lane_))) (var_0 : (Option half)), 
    ((List.length var_1_lst) == (List.length c_1_lst)) ->
    Forall₂ (fun (var_1 : (List lane_)) (c_1 : lane_) => (fun_lcvtop__ (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) vcvtop c_1 var_1)) var_1_lst c_1_lst ->
    (fun_halfop (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) vcvtop var_0) ->
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X Lnn_1 (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_lst : (List lane_)) => Forall (fun (c : lane_) => (wf_lane_ Lnn_2 c)) c_lst) c_lst_lst ->
    (var_0 == (some v_half)) ->
    (c_1_lst == (List.extract (lanes_ (.X Lnn_1 (.mk_dim M_1)) v_1) (fun_half v_half 0 M_2) M_2)) ->
    (c_lst_lst == (setproduct_ lane_ var_1_lst)) ->
    ((List.length (List.map (fun (c_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim M_2)) c_lst)) c_lst_lst)) > 0) ->
    (List.contains (List.map (fun (c_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim M_2)) c_lst)) c_lst_lst) v) ->
    fun_vcvtop__ (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) vcvtop v_1 v
  | fun_vcvtop___case_2 : forall (Lnn_1 : lanetype) (M_1 : Nat) (Lnn_2 : lanetype) (M_2 : Nat) (vcvtop : vcvtop__) (v_1 : uN) (v : uN) (c_1_lst : (List lane_)) (c_lst_lst : (List (List lane_))) (var_2 : lane_) (var_1_lst : (List (List lane_))) (var_0 : (Option zero)), 
    (fun_zero Lnn_2 var_2) ->
    ((List.length var_1_lst) == (List.length c_1_lst)) ->
    Forall₂ (fun (var_1 : (List lane_)) (c_1 : lane_) => (fun_lcvtop__ (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) vcvtop c_1 var_1)) var_1_lst c_1_lst ->
    (fun_zeroop (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) vcvtop var_0) ->
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X Lnn_1 (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_lst : (List lane_)) => Forall (fun (c : lane_) => (wf_lane_ Lnn_2 c)) c_lst) c_lst_lst ->
    (var_0 == (some .ZERO)) ->
    (c_1_lst == (lanes_ (.X Lnn_1 (.mk_dim M_1)) v_1)) ->
    (c_lst_lst == (setproduct_ lane_ (var_1_lst ++ (List.replicate M_1 [var_2])))) ->
    ((List.length (List.map (fun (c_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim M_2)) c_lst)) c_lst_lst)) > 0) ->
    (List.contains (List.map (fun (c_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim M_2)) c_lst)) c_lst_lst) v) ->
    fun_vcvtop__ (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) vcvtop v_1 v

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:186.6-186.16 -/
inductive fun_vshiftop_ : ishape -> vshiftop_ -> vec_ -> u32 -> vec_ -> Prop where
  | fun_vshiftop__case_0 : forall (v_M : Nat) (v : uN) (i : uN), fun_vshiftop_ (.mk_ishape (.X .I32 (.mk_dim v_M))) (.mk_vshiftop__0 .I32 v_M .SHL) v i (ivshiftop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ishl_ v i)
  | fun_vshiftop__case_1 : forall (v_M : Nat) (v : uN) (i : uN), fun_vshiftop_ (.mk_ishape (.X .I64 (.mk_dim v_M))) (.mk_vshiftop__0 .I64 v_M .SHL) v i (ivshiftop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ishl_ v i)
  | fun_vshiftop__case_2 : forall (v_M : Nat) (v : uN) (i : uN), fun_vshiftop_ (.mk_ishape (.X .I8 (.mk_dim v_M))) (.mk_vshiftop__0 .I8 v_M .SHL) v i (ivshiftop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ishl_ v i)
  | fun_vshiftop__case_3 : forall (v_M : Nat) (v : uN) (i : uN), fun_vshiftop_ (.mk_ishape (.X .I16 (.mk_dim v_M))) (.mk_vshiftop__0 .I16 v_M .SHL) v i (ivshiftop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ishl_ v i)
  | fun_vshiftop__case_4 : forall (v_M : Nat) (v_sx : sx) (v : uN) (i : uN), fun_vshiftop_ (.mk_ishape (.X .I32 (.mk_dim v_M))) (.mk_vshiftop__0 .I32 v_M (.SHR v_sx)) v i (ivshiftopsx_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) ishr_ v_sx v i)
  | fun_vshiftop__case_5 : forall (v_M : Nat) (v_sx : sx) (v : uN) (i : uN), fun_vshiftop_ (.mk_ishape (.X .I64 (.mk_dim v_M))) (.mk_vshiftop__0 .I64 v_M (.SHR v_sx)) v i (ivshiftopsx_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) ishr_ v_sx v i)
  | fun_vshiftop__case_6 : forall (v_M : Nat) (v_sx : sx) (v : uN) (i : uN), fun_vshiftop_ (.mk_ishape (.X .I8 (.mk_dim v_M))) (.mk_vshiftop__0 .I8 v_M (.SHR v_sx)) v i (ivshiftopsx_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) ishr_ v_sx v i)
  | fun_vshiftop__case_7 : forall (v_M : Nat) (v_sx : sx) (v : uN) (i : uN), fun_vshiftop_ (.mk_ishape (.X .I16 (.mk_dim v_M))) (.mk_vshiftop__0 .I16 v_M (.SHR v_sx)) v i (ivshiftopsx_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) ishr_ v_sx v i)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:188.6-188.18 -/
inductive fun_vbitmaskop_ : ishape -> vec_ -> u32 -> Prop where
  | fun_vbitmaskop__case_0 : forall (v_M : Nat) (v : uN) (var_0 : u32), 
    (fun_ivbitmaskop_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v var_0) ->
    fun_vbitmaskop_ (.mk_ishape (.X .I32 (.mk_dim v_M))) v var_0
  | fun_vbitmaskop__case_1 : forall (v_M : Nat) (v : uN) (var_0 : u32), 
    (fun_ivbitmaskop_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v var_0) ->
    fun_vbitmaskop_ (.mk_ishape (.X .I64 (.mk_dim v_M))) v var_0
  | fun_vbitmaskop__case_2 : forall (v_M : Nat) (v : uN) (var_0 : u32), 
    (fun_ivbitmaskop_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v var_0) ->
    fun_vbitmaskop_ (.mk_ishape (.X .I8 (.mk_dim v_M))) v var_0
  | fun_vbitmaskop__case_3 : forall (v_M : Nat) (v : uN) (var_0 : u32), 
    (fun_ivbitmaskop_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v var_0) ->
    fun_vbitmaskop_ (.mk_ishape (.X .I16 (.mk_dim v_M))) v var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:190.6-190.17 -/
inductive fun_vswizzlop_ : bshape -> vswizzlop_ -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_vswizzlop__case_0 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vswizzlop_ (.mk_bshape (.X .I8 (.mk_dim v_M))) (.mk_vswizzlop__0 v_M .SWIZZLE) v_1 v_2 (ivswizzlop_ (.X .I8 (.mk_dim v_M)) iswizzle_lane_ v_1 v_2)
  | fun_vswizzlop__case_1 : forall (v_M : Nat) (v_1 : uN) (v_2 : uN), fun_vswizzlop_ (.mk_bshape (.X .I8 (.mk_dim v_M))) (.mk_vswizzlop__0 v_M .RELAXED_SWIZZLE) v_1 v_2 (ivswizzlop_ (.X .I8 (.mk_dim v_M)) irelaxed_swizzle_lane_ v_1 v_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:192.6-192.17 -/
inductive fun_vshufflop_ : bshape -> (List laneidx) -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_vshufflop__case_0 : forall (v_M : Nat) (i_lst : (List laneidx)) (v_1 : uN) (v_2 : uN) (var_0 : vec_), 
    (fun_ivshufflop_ (.X .I8 (.mk_dim v_M)) i_lst v_1 v_2 var_0) ->
    fun_vshufflop_ (.mk_bshape (.X .I8 (.mk_dim v_M))) i_lst v_1 v_2 var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:195.6-195.18 -/
inductive fun_vnarrowop__ : shape -> shape -> sx -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_vnarrowop___case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I32 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I32 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I32 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I32 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I32 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I32 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I8 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I32 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I32 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I16 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I64 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I64 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I64 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I64 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I64 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I64 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I8 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I64 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I64 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I16 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_8 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I8 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I8 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_9 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I8 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I8 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_10 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I8 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I8 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I8 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_11 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I8 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I8 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I16 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_12 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I32)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I16 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I16 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_13 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I64)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I16 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I16 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_14 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I8)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I16 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I16 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I8 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_15 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (v : uN) (c_1_lst : (List lane_)) (c_2_lst : (List lane_)) (c'_1_lst : (List iN)) (c'_2_lst : (List iN)), 
    Forall (fun (c_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_1))) c_1)) c_1_lst ->
    Forall (fun (c_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_1))) c_2)) c_2_lst ->
    Forall (fun (c'_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c'_1))) c'_1_lst ->
    Forall (fun (c'_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 c'_2))) c'_2_lst ->
    (c_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_1)) ->
    (c_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) v_2)) ->
    Forall (fun (c_1 : lane_) => ((proj_lane__2 c_1) != none)) c_1_lst ->
    (c'_1_lst == (List.map (fun (c_1 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 c_1)))) c_1_lst)) ->
    Forall (fun (c_2 : lane_) => ((proj_lane__2 c_2) != none)) c_2_lst ->
    (c'_2_lst == (List.map (fun (c_2 : lane_) => (narrow__ (lsize (lanetype_Jnn .I16)) (lsize (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 c_2)))) c_2_lst)) ->
    (v == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ((List.map (fun (c'_1 : iN) => (.mk_lane__2 .I16 c'_1)) c'_1_lst) ++ (List.map (fun (c'_2 : iN) => (.mk_lane__2 .I16 c'_2)) c'_2_lst)))) ->
    fun_vnarrowop__ (.X .I16 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) v_sx v_1 v_2 v

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:356.1-356.76 -/
opaque ivadd_pairwise_ : forall (v_N : N) (var_0 : (List iN)), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:342.1-342.93 -/
opaque ivextunop__ : forall (shape_1 : shape) (shape_2 : shape) (f_ : N -> (List iN) -> (List iN)) (v_sx : sx) (v_vec_ : vec_), vec_ := opaqueDef

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:198.6-198.17 -/
inductive fun_vextunop__ : ishape -> ishape -> vextunop__ -> vec_ -> vec_ -> Prop where
  | fun_vextunop___case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextunop___0 .I32 M_1 .I32 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextunop___0 .I64 M_1 .I32 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextunop___0 .I8 M_1 .I32 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextunop___0 .I16 M_1 .I32 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextunop___0 .I32 M_1 .I64 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextunop___0 .I64 M_1 .I64 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextunop___0 .I8 M_1 .I64 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextunop___0 .I16 M_1 .I64 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_8 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextunop___0 .I32 M_1 .I8 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_9 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextunop___0 .I64 M_1 .I8 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_10 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextunop___0 .I8 M_1 .I8 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_11 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextunop___0 .I16 M_1 .I8 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_12 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextunop___0 .I32 M_1 .I16 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_13 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextunop___0 .I64 M_1 .I16 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_14 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextunop___0 .I8 M_1 .I16 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)
  | fun_vextunop___case_15 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN), fun_vextunop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextunop___0 .I16 M_1 .I16 M_2 (.EXTADD_PAIRWISE v_sx)) v_1 (ivextunop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivadd_pairwise_ v_sx v_1)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:363.1-363.40 -/
opaque ivdot_ : forall (v_N : N) (var_0 : (List iN)) (var_1 : (List iN)), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:367.1-367.76 -/
opaque ivdot_sat_ : forall (v_N : N) (var_0 : (List iN)) (var_1 : (List iN)), (List iN) := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:348.1-348.136 -/
opaque ivextbinop__ : forall (shape_1 : shape) (shape_2 : shape) (f_ : N -> (List iN) -> (List iN) -> (List iN)) (v_sx : sx) (v_sx_0 : sx) (v_laneidx : laneidx) (v_laneidx_0 : laneidx) (v_vec_ : vec_) (v_vec__0 : vec_), vec_ := opaqueDef

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:360.1-360.40 -/
def ivmul_ : ∀  (v_N : N) (var_0 : (List iN)) (var_1 : (List iN)) , (List iN)
  | v_N, i_1_lst, i_2_lst =>
    (List.zipWith (fun (i_1 : iN) (i_2 : iN) => (imul_ v_N i_1 i_2)) i_1_lst i_2_lst)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:200.6-200.18 -/
inductive fun_vextbinop__ : ishape -> ishape -> vextbinop__ -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_vextbinop___case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I32 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I32 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I32 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I32 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I64 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I64 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I64 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I64 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_8 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I8 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_9 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I8 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_10 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I8 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_11 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I8 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_12 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I16 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_13 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I16 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_14 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I16 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_15 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I16 M_2 (.EXTMUL v_half v_sx)) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivmul_ v_sx v_sx (.mk_uN (fun_half v_half 0 M_2)) (.mk_uN M_2) v_1 v_2)
  | fun_vextbinop___case_16 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I32 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_17 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I32 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_18 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I32 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_19 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I32 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_20 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I64 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_21 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I64 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_22 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I64 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_23 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I64 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_24 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I8 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_25 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I8 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_26 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I8 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_27 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I8 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_28 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I16 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_29 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I16 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_30 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I16 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_31 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I16 M_2 .DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_ .S .S (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_32 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I32 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_33 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I32 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_34 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I32 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_35 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I32 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I32) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_36 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I64 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_37 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I64 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_38 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I64 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_39 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I64 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I64) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_40 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I8 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_41 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I8 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_42 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I8 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_43 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I8 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I8) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_44 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I32 M_1 .I16 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I32) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_45 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I64 M_1 .I16 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I64) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_46 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I8 M_1 .I16 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I8) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)
  | fun_vextbinop___case_47 : forall (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN), fun_vextbinop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextbinop___0 .I16 M_1 .I16 M_2 .RELAXED_DOTS) v_1 v_2 (ivextbinop__ (.X (lanetype_Jnn .I16) (.mk_dim M_1)) (.X (lanetype_Jnn .I16) (.mk_dim M_2)) ivdot_sat_ .S (fun_relaxed2 (R_idot ) sx .S .U) (.mk_uN 0) (.mk_uN M_1) v_1 v_2)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/3.2-numerics.vector.spectec:202.6-202.19 -/
inductive fun_vextternop__ : ishape -> ishape -> vextternop__ -> vec_ -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_vextternop___case_0 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I32)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextternop___0 .I32 M_1 .I32 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_1 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I64)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextternop___0 .I64 M_1 .I32 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_2 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I8)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextternop___0 .I8 M_1 .I32 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_3 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I32 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I32) (.mk_dim M_2)) (.mk_vbinop__0 .I32 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I16)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I32 (.mk_dim M_2))) (.mk_vextternop___0 .I16 M_1 .I32 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_4 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I32)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextternop___0 .I32 M_1 .I64 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_5 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I64)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextternop___0 .I64 M_1 .I64 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_6 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I8)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextternop___0 .I8 M_1 .I64 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_7 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I64 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I64) (.mk_dim M_2)) (.mk_vbinop__0 .I64 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I16)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I64 (.mk_dim M_2))) (.mk_vextternop___0 .I16 M_1 .I64 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_8 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I32)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextternop___0 .I32 M_1 .I8 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_9 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I64)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextternop___0 .I64 M_1 .I8 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_10 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I8)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextternop___0 .I8 M_1 .I8 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_11 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I8 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I8) (.mk_dim M_2)) (.mk_vbinop__0 .I8 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I16)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I8 (.mk_dim M_2))) (.mk_vextternop___0 .I16 M_1 .I8 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_12 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I32) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I32 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I32)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I32 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextternop___0 .I32 M_1 .I16 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_13 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I64) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I64 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I64)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I64 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextternop___0 .I64 M_1 .I16 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_14 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I8) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I8 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I8)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I8 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextternop___0 .I8 M_1 .I16 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_15 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (v_M : Nat) (c' : uN) (c'' : uN) (var_2 : (List vec_)) (var_1 : vec_) (var_0 : vec_), 
    (fun_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD) c'' c_3 var_2) ->
    (fun_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S)) c' var_1) ->
    (fun_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS) c_1 c_2 var_0) ->
    (wf_vextbinop__ (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_1))) (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_vextbinop___0 .I16 M_1 v_Jnn v_M .RELAXED_DOTS)) ->
    (wf_vextunop__ (.mk_ishape (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_ishape (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_vextunop___0 v_Jnn v_M .I16 M_2 (.EXTADD_PAIRWISE .S))) ->
    (wf_vbinop_ (.X (lanetype_Jnn .I16) (.mk_dim M_2)) (.mk_vbinop__0 .I16 M_2 .ADD)) ->
    ((jsizenn v_Jnn) == (2 * (lsizenn1 (lanetype_Jnn .I16)))) ->
    (v_M == (2 * M_2)) ->
    (c' == var_0) ->
    (c'' == var_1) ->
    ((List.length var_2) > 0) ->
    (List.contains var_2 c) ->
    fun_vextternop__ (.mk_ishape (.X .I16 (.mk_dim M_1))) (.mk_ishape (.X .I16 (.mk_dim M_2))) (.mk_vextternop___0 .I16 M_1 .I16 M_2 .RELAXED_DOT_ADDS) c_1 c_2 c_3 c

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:29.1-30.63 -/
inductive num : Type where
  | CONST (v_numtype : numtype) (v_num_ : num_) : num
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def val_num : ∀  (var_0 : num) , val
  | (.CONST x0 x1) =>
    (.CONST x0 x1)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:29.8-29.11 -/
inductive wf_num : num -> Prop where
  | num_case_0 : forall (v_numtype : numtype) (v_num_ : num_), 
    (wf_num_ v_numtype v_num_) ->
    wf_num (.CONST v_numtype v_num_)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:32.1-33.87 -/
inductive vec : Type where
  | VCONST (v_vectype : vectype) (v_vec_ : vec_) : vec
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def val_vec : ∀  (var_0 : vec) , val
  | (.VCONST x0 x1) =>
    (.VCONST x0 x1)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:32.8-32.11 -/
inductive wf_vec : vec -> Prop where
  | vec_case_0 : forall (v_vectype : vectype) (v_vec_ : vec_), 
    (wf_uN (vsize v_vectype) v_vec_) ->
    wf_vec (.VCONST v_vectype v_vec_)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:44.1-46.22 -/
inductive ref : Type where
  | REF_I31_NUM (v_u31 : u31) : ref
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : ref
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : ref
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : ref
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : ref
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : ref
  | REF_EXTERN (v_addrref : addrref) : ref
  | REF_NULL (v_heaptype : heaptype) : ref
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def ref_addrref : ∀  (var_0 : addrref) , ref
  | (.REF_I31_NUM x0) =>
    (.REF_I31_NUM x0)
  | (.REF_STRUCT_ADDR x0) =>
    (.REF_STRUCT_ADDR x0)
  | (.REF_ARRAY_ADDR x0) =>
    (.REF_ARRAY_ADDR x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_EXN_ADDR x0) =>
    (.REF_EXN_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)
  | (.REF_EXTERN x0) =>
    (.REF_EXTERN x0)


/- Auxiliary Definition at:  -/
def instr_ref : ∀  (var_0 : ref) , instr
  | (.REF_I31_NUM x0) =>
    (.REF_I31_NUM x0)
  | (.REF_STRUCT_ADDR x0) =>
    (.REF_STRUCT_ADDR x0)
  | (.REF_ARRAY_ADDR x0) =>
    (.REF_ARRAY_ADDR x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_EXN_ADDR x0) =>
    (.REF_EXN_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)
  | (.REF_EXTERN x0) =>
    (.REF_EXTERN x0)
  | (.REF_NULL x0) =>
    (.REF_NULL x0)


/- Auxiliary Definition at:  -/
def val_ref : ∀  (var_0 : ref) , val
  | (.REF_I31_NUM x0) =>
    (.REF_I31_NUM x0)
  | (.REF_STRUCT_ADDR x0) =>
    (.REF_STRUCT_ADDR x0)
  | (.REF_ARRAY_ADDR x0) =>
    (.REF_ARRAY_ADDR x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_EXN_ADDR x0) =>
    (.REF_EXN_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)
  | (.REF_EXTERN x0) =>
    (.REF_EXTERN x0)
  | (.REF_NULL x0) =>
    (.REF_NULL x0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:44.8-44.11 -/
inductive wf_ref : ref -> Prop where
  | ref_case_0 : forall (v_u31 : u31), 
    (wf_uN 31 v_u31) ->
    wf_ref (.REF_I31_NUM v_u31)
  | ref_case_1 : forall (v_structaddr : structaddr), wf_ref (.REF_STRUCT_ADDR v_structaddr)
  | ref_case_2 : forall (v_arrayaddr : arrayaddr), wf_ref (.REF_ARRAY_ADDR v_arrayaddr)
  | ref_case_3 : forall (v_funcaddr : funcaddr), wf_ref (.REF_FUNC_ADDR v_funcaddr)
  | ref_case_4 : forall (v_exnaddr : exnaddr), wf_ref (.REF_EXN_ADDR v_exnaddr)
  | ref_case_5 : forall (v_hostaddr : hostaddr), wf_ref (.REF_HOST_ADDR v_hostaddr)
  | ref_case_6 : forall (v_addrref : addrref), 
    (wf_addrref v_addrref) ->
    wf_ref (.REF_EXTERN v_addrref)
  | ref_case_7 : forall (v_heaptype : heaptype), 
    (wf_heaptype v_heaptype) ->
    wf_ref (.REF_NULL v_heaptype)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:51.1-52.58 -/
inductive result : Type where
  | _VALS (val_lst : (List val)) : result
  | REF_EXN_ADDRTHROW_REF (v_exnaddr : exnaddr) : result
  | TRAP : result
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:51.8-51.14 -/
inductive wf_result : result -> Prop where
  | result_case_0 : forall (val_lst : (List val)), 
    Forall (fun (v_val : val) => (wf_val v_val)) val_lst ->
    wf_result (._VALS val_lst)
  | result_case_1 : forall (v_exnaddr : exnaddr), wf_result (.REF_EXN_ADDRTHROW_REF v_exnaddr)
  | result_case_2 : wf_result .TRAP

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:60.1-60.72 -/
inductive hostfunc : Type where
  | mk_hostfunc : hostfunc
deriving Inhabited, BEq


/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:61.1-61.73 -/
inductive funccode : Type where
  | FUNC (v_typeidx : typeidx) (local_lst : (List «local»)) (v_expr : expr) : funccode
  | mk_funccode : funccode
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:61.8-61.16 -/
inductive wf_funccode : funccode -> Prop where
  | funccode_case_0 : forall (v_typeidx : typeidx) (local_lst : (List «local»)) (v_expr : expr), 
    (wf_uN 32 v_typeidx) ->
    Forall (fun (v_local : «local») => (wf_local v_local)) local_lst ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_funccode (.FUNC v_typeidx local_lst v_expr)
  | funccode_case_1 : wf_funccode .mk_funccode

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:63.1-64.19 -/
structure taginst where MKtaginst ::
  TYPE : tagtype
deriving Inhabited, BEq

def _append_taginst (arg1 arg2 : (taginst)) : taginst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
instance : Append taginst where
  append arg1 arg2 := _append_taginst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:63.8-63.15 -/
inductive wf_taginst : taginst -> Prop where
  | taginst_case_ : forall (var_0 : tagtype), 
    (wf_typeuse var_0) ->
    wf_taginst { TYPE := var_0 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:66.1-67.33 -/
structure globalinst where MKglobalinst ::
  TYPE : globaltype
  VALUE : val
deriving Inhabited, BEq

def _append_globalinst (arg1 arg2 : (globalinst)) : globalinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  VALUE := arg1.VALUE /- FIXME - Non-trivial append -/
instance : Append globalinst where
  append arg1 arg2 := _append_globalinst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:66.8-66.18 -/
inductive wf_globalinst : globalinst -> Prop where
  | globalinst_case_ : forall (var_0 : globaltype) (var_1 : val), 
    (wf_globaltype var_0) ->
    (wf_val var_1) ->
    wf_globalinst { TYPE := var_0, VALUE := var_1 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:69.1-70.32 -/
structure meminst where MKmeminst ::
  TYPE : memtype
  BYTES : (List byte)
deriving Inhabited, BEq

def _append_meminst (arg1 arg2 : (meminst)) : meminst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  BYTES := arg1.BYTES ++ arg2.BYTES
instance : Append meminst where
  append arg1 arg2 := _append_meminst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:69.8-69.15 -/
inductive wf_meminst : meminst -> Prop where
  | meminst_case_ : forall (var_0 : memtype) (var_1 : (List byte)), 
    (wf_memtype var_0) ->
    Forall (fun (var_1 : byte) => (wf_byte var_1)) var_1 ->
    wf_meminst { TYPE := var_0, BYTES := var_1 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:72.1-73.32 -/
structure tableinst where MKtableinst ::
  TYPE : tabletype
  REFS : (List ref)
deriving Inhabited, BEq

def _append_tableinst (arg1 arg2 : (tableinst)) : tableinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  REFS := arg1.REFS ++ arg2.REFS
instance : Append tableinst where
  append arg1 arg2 := _append_tableinst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:72.8-72.17 -/
inductive wf_tableinst : tableinst -> Prop where
  | tableinst_case_ : forall (var_0 : tabletype) (var_1 : (List ref)), 
    (wf_tabletype var_0) ->
    Forall (fun (var_1 : ref) => (wf_ref var_1)) var_1 ->
    wf_tableinst { TYPE := var_0, REFS := var_1 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:75.1-76.53 -/
structure funcinst where MKfuncinst ::
  TYPE : deftype
  MODULE : moduleinst
  CODE : funccode
deriving Inhabited, BEq

def _append_funcinst (arg1 arg2 : (funcinst)) : funcinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  MODULE := arg1.MODULE ++ arg2.MODULE
  CODE := arg1.CODE /- FIXME - Non-trivial append -/
instance : Append funcinst where
  append arg1 arg2 := _append_funcinst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:75.8-75.16 -/
inductive wf_funcinst : funcinst -> Prop where
  | funcinst_case_ : forall (var_0 : deftype) (var_1 : moduleinst) (var_2 : funccode), 
    (wf_moduleinst var_1) ->
    (wf_funccode var_2) ->
    wf_funcinst { TYPE := var_0, MODULE := var_1, CODE := var_2 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:78.1-79.18 -/
structure datainst where MKdatainst ::
  BYTES : (List byte)
deriving Inhabited, BEq

def _append_datainst (arg1 arg2 : (datainst)) : datainst where
  BYTES := arg1.BYTES ++ arg2.BYTES
instance : Append datainst where
  append arg1 arg2 := _append_datainst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:78.8-78.16 -/
inductive wf_datainst : datainst -> Prop where
  | datainst_case_ : forall (var_0 : (List byte)), 
    Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0 ->
    wf_datainst { BYTES := var_0 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:81.1-82.31 -/
structure eleminst where MKeleminst ::
  TYPE : elemtype
  REFS : (List ref)
deriving Inhabited, BEq

def _append_eleminst (arg1 arg2 : (eleminst)) : eleminst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  REFS := arg1.REFS ++ arg2.REFS
instance : Append eleminst where
  append arg1 arg2 := _append_eleminst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:81.8-81.16 -/
inductive wf_eleminst : eleminst -> Prop where
  | eleminst_case_ : forall (var_0 : elemtype) (var_1 : (List ref)), 
    (wf_reftype var_0) ->
    Forall (fun (var_1 : ref) => (wf_ref var_1)) var_1 ->
    wf_eleminst { TYPE := var_0, REFS := var_1 }

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:88.1-89.64 -/
inductive packval : Type where
  | PACK (v_packtype : packtype) (v_iN : iN) : packval
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:88.8-88.15 -/
inductive wf_packval : packval -> Prop where
  | packval_case_0 : forall (v_packtype : packtype) (v_iN : iN), 
    (wf_uN (psize v_packtype) v_iN) ->
    wf_packval (.PACK v_packtype v_iN)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:91.1-92.18 -/
inductive fieldval : Type where
  | CONST (v_numtype : numtype) (v_num_ : num_) : fieldval
  | VCONST (v_vectype : vectype) (v_vec_ : vec_) : fieldval
  | REF_NULL (v_heaptype : heaptype) : fieldval
  | REF_I31_NUM (v_u31 : u31) : fieldval
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : fieldval
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : fieldval
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : fieldval
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : fieldval
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : fieldval
  | REF_EXTERN (v_addrref : addrref) : fieldval
  | PACK (v_packtype : packtype) (v_iN : iN) : fieldval
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def fieldval_val : ∀  (var_0 : val) , fieldval
  | (.CONST x0 x1) =>
    (.CONST x0 x1)
  | (.VCONST x0 x1) =>
    (.VCONST x0 x1)
  | (.REF_NULL x0) =>
    (.REF_NULL x0)
  | (.REF_I31_NUM x0) =>
    (.REF_I31_NUM x0)
  | (.REF_STRUCT_ADDR x0) =>
    (.REF_STRUCT_ADDR x0)
  | (.REF_ARRAY_ADDR x0) =>
    (.REF_ARRAY_ADDR x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_EXN_ADDR x0) =>
    (.REF_EXN_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)
  | (.REF_EXTERN x0) =>
    (.REF_EXTERN x0)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:91.8-91.16 -/
inductive wf_fieldval : fieldval -> Prop where
  | fieldval_case_0 : forall (v_numtype : numtype) (v_num_ : num_), 
    (wf_num_ v_numtype v_num_) ->
    wf_fieldval (.CONST v_numtype v_num_)
  | fieldval_case_1 : forall (v_vectype : vectype) (v_vec_ : vec_), 
    (wf_uN (vsize v_vectype) v_vec_) ->
    wf_fieldval (.VCONST v_vectype v_vec_)
  | fieldval_case_2 : forall (v_heaptype : heaptype), 
    (wf_heaptype v_heaptype) ->
    wf_fieldval (.REF_NULL v_heaptype)
  | fieldval_case_3 : forall (v_u31 : u31), 
    (wf_uN 31 v_u31) ->
    wf_fieldval (.REF_I31_NUM v_u31)
  | fieldval_case_4 : forall (v_structaddr : structaddr), wf_fieldval (.REF_STRUCT_ADDR v_structaddr)
  | fieldval_case_5 : forall (v_arrayaddr : arrayaddr), wf_fieldval (.REF_ARRAY_ADDR v_arrayaddr)
  | fieldval_case_6 : forall (v_funcaddr : funcaddr), wf_fieldval (.REF_FUNC_ADDR v_funcaddr)
  | fieldval_case_7 : forall (v_exnaddr : exnaddr), wf_fieldval (.REF_EXN_ADDR v_exnaddr)
  | fieldval_case_8 : forall (v_hostaddr : hostaddr), wf_fieldval (.REF_HOST_ADDR v_hostaddr)
  | fieldval_case_9 : forall (v_addrref : addrref), 
    (wf_addrref v_addrref) ->
    wf_fieldval (.REF_EXTERN v_addrref)
  | fieldval_case_10 : forall (v_packtype : packtype) (v_iN : iN), 
    (wf_uN (psize v_packtype) v_iN) ->
    wf_fieldval (.PACK v_packtype v_iN)

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:94.1-95.37 -/
structure structinst where MKstructinst ::
  TYPE : deftype
  FIELDS : (List fieldval)
deriving Inhabited, BEq

def _append_structinst (arg1 arg2 : (structinst)) : structinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  FIELDS := arg1.FIELDS ++ arg2.FIELDS
instance : Append structinst where
  append arg1 arg2 := _append_structinst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:94.8-94.18 -/
inductive wf_structinst : structinst -> Prop where
  | structinst_case_ : forall (var_0 : deftype) (var_1 : (List fieldval)), 
    Forall (fun (var_1 : fieldval) => (wf_fieldval var_1)) var_1 ->
    wf_structinst { TYPE := var_0, FIELDS := var_1 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:97.1-98.37 -/
structure arrayinst where MKarrayinst ::
  TYPE : deftype
  FIELDS : (List fieldval)
deriving Inhabited, BEq

def _append_arrayinst (arg1 arg2 : (arrayinst)) : arrayinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  FIELDS := arg1.FIELDS ++ arg2.FIELDS
instance : Append arrayinst where
  append arg1 arg2 := _append_arrayinst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:97.8-97.17 -/
inductive wf_arrayinst : arrayinst -> Prop where
  | arrayinst_case_ : forall (var_0 : deftype) (var_1 : (List fieldval)), 
    Forall (fun (var_1 : fieldval) => (wf_fieldval var_1)) var_1 ->
    wf_arrayinst { TYPE := var_0, FIELDS := var_1 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:100.1-101.31 -/
structure exninst where MKexninst ::
  TAG : tagaddr
  FIELDS : (List val)
deriving Inhabited, BEq

def _append_exninst (arg1 arg2 : (exninst)) : exninst where
  TAG := arg1.TAG /- FIXME - Non-trivial append -/
  FIELDS := arg1.FIELDS ++ arg2.FIELDS
instance : Append exninst where
  append arg1 arg2 := _append_exninst arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:100.8-100.15 -/
inductive wf_exninst : exninst -> Prop where
  | exninst_case_ : forall (var_0 : tagaddr) (var_1 : (List val)), 
    Forall (fun (var_1 : val) => (wf_val var_1)) var_1 ->
    wf_exninst { TAG := var_0, FIELDS := var_1 }

/- Record Creation Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:118.1-128.20 -/
structure store where MKstore ::
  TAGS : (List taginst)
  GLOBALS : (List globalinst)
  MEMS : (List meminst)
  TABLES : (List tableinst)
  FUNCS : (List funcinst)
  DATAS : (List datainst)
  ELEMS : (List eleminst)
  STRUCTS : (List structinst)
  ARRAYS : (List arrayinst)
  EXNS : (List exninst)
deriving Inhabited, BEq

def _append_store (arg1 arg2 : (store)) : store where
  TAGS := arg1.TAGS ++ arg2.TAGS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  MEMS := arg1.MEMS ++ arg2.MEMS
  TABLES := arg1.TABLES ++ arg2.TABLES
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  DATAS := arg1.DATAS ++ arg2.DATAS
  ELEMS := arg1.ELEMS ++ arg2.ELEMS
  STRUCTS := arg1.STRUCTS ++ arg2.STRUCTS
  ARRAYS := arg1.ARRAYS ++ arg2.ARRAYS
  EXNS := arg1.EXNS ++ arg2.EXNS
instance : Append store where
  append arg1 arg2 := _append_store arg1 arg2



/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:118.8-118.13 -/
inductive wf_store : store -> Prop where
  | store_case_ : forall (var_0 : (List taginst)) (var_1 : (List globalinst)) (var_2 : (List meminst)) (var_3 : (List tableinst)) (var_4 : (List funcinst)) (var_5 : (List datainst)) (var_6 : (List eleminst)) (var_7 : (List structinst)) (var_8 : (List arrayinst)) (var_9 : (List exninst)), 
    Forall (fun (var_0 : taginst) => (wf_taginst var_0)) var_0 ->
    Forall (fun (var_1 : globalinst) => (wf_globalinst var_1)) var_1 ->
    Forall (fun (var_2 : meminst) => (wf_meminst var_2)) var_2 ->
    Forall (fun (var_3 : tableinst) => (wf_tableinst var_3)) var_3 ->
    Forall (fun (var_4 : funcinst) => (wf_funcinst var_4)) var_4 ->
    Forall (fun (var_5 : datainst) => (wf_datainst var_5)) var_5 ->
    Forall (fun (var_6 : eleminst) => (wf_eleminst var_6)) var_6 ->
    Forall (fun (var_7 : structinst) => (wf_structinst var_7)) var_7 ->
    Forall (fun (var_8 : arrayinst) => (wf_arrayinst var_8)) var_8 ->
    Forall (fun (var_9 : exninst) => (wf_exninst var_9)) var_9 ->
    wf_store { TAGS := var_0, GLOBALS := var_1, MEMS := var_2, TABLES := var_3, FUNCS := var_4, DATAS := var_5, ELEMS := var_6, STRUCTS := var_7, ARRAYS := var_8, EXNS := var_9 }

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:147.1-147.47 -/
inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:147.8-147.13 -/
inductive wf_state : state -> Prop where
  | state_case_0 : forall (v_store : store) (v_frame : frame), 
    (wf_store v_store) ->
    (wf_frame v_frame) ->
    wf_state (.mk_state v_store v_frame)

/- Inductive Type Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:148.1-148.57 -/
inductive config : Type where
  | mk_config (v_state : state) (instr_lst : (List instr)) : config
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:148.8-148.14 -/
inductive wf_config : config -> Prop where
  | config_case_0 : forall (v_state : state) (instr_lst : (List instr)), 
    (wf_state v_state) ->
    Forall (fun (v_instr : instr) => (wf_instr v_instr)) instr_lst ->
    wf_config (.mk_config v_state instr_lst)

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:175.1-175.31 -/
def Ki : Nat := 1024

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:181.1-181.100 -/
def packfield_ : ∀  (v_storagetype : storagetype) (v_val : val) , fieldval
  | .BOT, v_val =>
    (fieldval_val v_val)
  | (.REF null_opt v_heaptype), v_val =>
    (fieldval_val v_val)
  | .V128, v_val =>
    (fieldval_val v_val)
  | .F64, v_val =>
    (fieldval_val v_val)
  | .F32, v_val =>
    (fieldval_val v_val)
  | .I64, v_val =>
    (fieldval_val v_val)
  | .I32, v_val =>
    (fieldval_val v_val)
  | .I8, (.CONST .I32 (.mk_num__0 .I32 i)) =>
    (.PACK .I8 (wrap__ 32 (psize .I8) i))
  | .I16, (.CONST .I32 (.mk_num__0 .I32 i)) =>
    (.PACK .I16 (wrap__ 32 (psize .I16) i))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:182.1-182.112 -/
def unpackfield_ : ∀  (v_storagetype : storagetype) (var_0 : (Option sx)) (v_fieldval : fieldval) , val
  | .BOT, none, (.REF_EXTERN v_addrref) =>
    (.REF_EXTERN v_addrref)
  | (.REF null_opt v_heaptype), none, (.REF_EXTERN v_addrref) =>
    (.REF_EXTERN v_addrref)
  | .V128, none, (.REF_EXTERN v_addrref) =>
    (.REF_EXTERN v_addrref)
  | .F64, none, (.REF_EXTERN v_addrref) =>
    (.REF_EXTERN v_addrref)
  | .F32, none, (.REF_EXTERN v_addrref) =>
    (.REF_EXTERN v_addrref)
  | .I64, none, (.REF_EXTERN v_addrref) =>
    (.REF_EXTERN v_addrref)
  | .I32, none, (.REF_EXTERN v_addrref) =>
    (.REF_EXTERN v_addrref)
  | .BOT, none, (.REF_HOST_ADDR v_hostaddr) =>
    (.REF_HOST_ADDR v_hostaddr)
  | (.REF null_opt v_heaptype), none, (.REF_HOST_ADDR v_hostaddr) =>
    (.REF_HOST_ADDR v_hostaddr)
  | .V128, none, (.REF_HOST_ADDR v_hostaddr) =>
    (.REF_HOST_ADDR v_hostaddr)
  | .F64, none, (.REF_HOST_ADDR v_hostaddr) =>
    (.REF_HOST_ADDR v_hostaddr)
  | .F32, none, (.REF_HOST_ADDR v_hostaddr) =>
    (.REF_HOST_ADDR v_hostaddr)
  | .I64, none, (.REF_HOST_ADDR v_hostaddr) =>
    (.REF_HOST_ADDR v_hostaddr)
  | .I32, none, (.REF_HOST_ADDR v_hostaddr) =>
    (.REF_HOST_ADDR v_hostaddr)
  | .BOT, none, (.REF_EXN_ADDR v_exnaddr) =>
    (.REF_EXN_ADDR v_exnaddr)
  | (.REF null_opt v_heaptype), none, (.REF_EXN_ADDR v_exnaddr) =>
    (.REF_EXN_ADDR v_exnaddr)
  | .V128, none, (.REF_EXN_ADDR v_exnaddr) =>
    (.REF_EXN_ADDR v_exnaddr)
  | .F64, none, (.REF_EXN_ADDR v_exnaddr) =>
    (.REF_EXN_ADDR v_exnaddr)
  | .F32, none, (.REF_EXN_ADDR v_exnaddr) =>
    (.REF_EXN_ADDR v_exnaddr)
  | .I64, none, (.REF_EXN_ADDR v_exnaddr) =>
    (.REF_EXN_ADDR v_exnaddr)
  | .I32, none, (.REF_EXN_ADDR v_exnaddr) =>
    (.REF_EXN_ADDR v_exnaddr)
  | .BOT, none, (.REF_FUNC_ADDR v_funcaddr) =>
    (.REF_FUNC_ADDR v_funcaddr)
  | (.REF null_opt v_heaptype), none, (.REF_FUNC_ADDR v_funcaddr) =>
    (.REF_FUNC_ADDR v_funcaddr)
  | .V128, none, (.REF_FUNC_ADDR v_funcaddr) =>
    (.REF_FUNC_ADDR v_funcaddr)
  | .F64, none, (.REF_FUNC_ADDR v_funcaddr) =>
    (.REF_FUNC_ADDR v_funcaddr)
  | .F32, none, (.REF_FUNC_ADDR v_funcaddr) =>
    (.REF_FUNC_ADDR v_funcaddr)
  | .I64, none, (.REF_FUNC_ADDR v_funcaddr) =>
    (.REF_FUNC_ADDR v_funcaddr)
  | .I32, none, (.REF_FUNC_ADDR v_funcaddr) =>
    (.REF_FUNC_ADDR v_funcaddr)
  | .BOT, none, (.REF_ARRAY_ADDR v_arrayaddr) =>
    (.REF_ARRAY_ADDR v_arrayaddr)
  | (.REF null_opt v_heaptype), none, (.REF_ARRAY_ADDR v_arrayaddr) =>
    (.REF_ARRAY_ADDR v_arrayaddr)
  | .V128, none, (.REF_ARRAY_ADDR v_arrayaddr) =>
    (.REF_ARRAY_ADDR v_arrayaddr)
  | .F64, none, (.REF_ARRAY_ADDR v_arrayaddr) =>
    (.REF_ARRAY_ADDR v_arrayaddr)
  | .F32, none, (.REF_ARRAY_ADDR v_arrayaddr) =>
    (.REF_ARRAY_ADDR v_arrayaddr)
  | .I64, none, (.REF_ARRAY_ADDR v_arrayaddr) =>
    (.REF_ARRAY_ADDR v_arrayaddr)
  | .I32, none, (.REF_ARRAY_ADDR v_arrayaddr) =>
    (.REF_ARRAY_ADDR v_arrayaddr)
  | .BOT, none, (.REF_STRUCT_ADDR v_structaddr) =>
    (.REF_STRUCT_ADDR v_structaddr)
  | (.REF null_opt v_heaptype), none, (.REF_STRUCT_ADDR v_structaddr) =>
    (.REF_STRUCT_ADDR v_structaddr)
  | .V128, none, (.REF_STRUCT_ADDR v_structaddr) =>
    (.REF_STRUCT_ADDR v_structaddr)
  | .F64, none, (.REF_STRUCT_ADDR v_structaddr) =>
    (.REF_STRUCT_ADDR v_structaddr)
  | .F32, none, (.REF_STRUCT_ADDR v_structaddr) =>
    (.REF_STRUCT_ADDR v_structaddr)
  | .I64, none, (.REF_STRUCT_ADDR v_structaddr) =>
    (.REF_STRUCT_ADDR v_structaddr)
  | .I32, none, (.REF_STRUCT_ADDR v_structaddr) =>
    (.REF_STRUCT_ADDR v_structaddr)
  | .BOT, none, (.REF_I31_NUM v_u31) =>
    (.REF_I31_NUM v_u31)
  | (.REF null_opt v_heaptype), none, (.REF_I31_NUM v_u31) =>
    (.REF_I31_NUM v_u31)
  | .V128, none, (.REF_I31_NUM v_u31) =>
    (.REF_I31_NUM v_u31)
  | .F64, none, (.REF_I31_NUM v_u31) =>
    (.REF_I31_NUM v_u31)
  | .F32, none, (.REF_I31_NUM v_u31) =>
    (.REF_I31_NUM v_u31)
  | .I64, none, (.REF_I31_NUM v_u31) =>
    (.REF_I31_NUM v_u31)
  | .I32, none, (.REF_I31_NUM v_u31) =>
    (.REF_I31_NUM v_u31)
  | .BOT, none, (.REF_NULL heaptype_0) =>
    (.REF_NULL heaptype_0)
  | (.REF null_opt v_heaptype), none, (.REF_NULL heaptype_0) =>
    (.REF_NULL heaptype_0)
  | .V128, none, (.REF_NULL heaptype_0) =>
    (.REF_NULL heaptype_0)
  | .F64, none, (.REF_NULL heaptype_0) =>
    (.REF_NULL heaptype_0)
  | .F32, none, (.REF_NULL heaptype_0) =>
    (.REF_NULL heaptype_0)
  | .I64, none, (.REF_NULL heaptype_0) =>
    (.REF_NULL heaptype_0)
  | .I32, none, (.REF_NULL heaptype_0) =>
    (.REF_NULL heaptype_0)
  | .BOT, none, (.VCONST v_vectype v_vec_) =>
    (.VCONST v_vectype v_vec_)
  | (.REF null_opt v_heaptype), none, (.VCONST v_vectype v_vec_) =>
    (.VCONST v_vectype v_vec_)
  | .V128, none, (.VCONST v_vectype v_vec_) =>
    (.VCONST v_vectype v_vec_)
  | .F64, none, (.VCONST v_vectype v_vec_) =>
    (.VCONST v_vectype v_vec_)
  | .F32, none, (.VCONST v_vectype v_vec_) =>
    (.VCONST v_vectype v_vec_)
  | .I64, none, (.VCONST v_vectype v_vec_) =>
    (.VCONST v_vectype v_vec_)
  | .I32, none, (.VCONST v_vectype v_vec_) =>
    (.VCONST v_vectype v_vec_)
  | .BOT, none, (.CONST v_numtype v_num_) =>
    (.CONST v_numtype v_num_)
  | (.REF null_opt v_heaptype), none, (.CONST v_numtype v_num_) =>
    (.CONST v_numtype v_num_)
  | .V128, none, (.CONST v_numtype v_num_) =>
    (.CONST v_numtype v_num_)
  | .F64, none, (.CONST v_numtype v_num_) =>
    (.CONST v_numtype v_num_)
  | .F32, none, (.CONST v_numtype v_num_) =>
    (.CONST v_numtype v_num_)
  | .I64, none, (.CONST v_numtype v_num_) =>
    (.CONST v_numtype v_num_)
  | .I32, none, (.CONST v_numtype v_num_) =>
    (.CONST v_numtype v_num_)
  | .I8, (some v_sx), (.PACK .I8 i) =>
    (.CONST .I32 (.mk_num__0 .I32 (extend__ (psize .I8) 32 v_sx i)))
  | .I16, (some v_sx), (.PACK .I16 i) =>
    (.CONST .I32 (.mk_num__0 .I32 (extend__ (psize .I16) 32 v_sx i)))


/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:193.1-193.86 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:193.6-193.13 -/
inductive fun_tagsxa : (List externaddr) -> (List tagaddr) -> Prop where
  | fun_tagsxa_case_0 : fun_tagsxa [] []
  | fun_tagsxa_case_1 : forall (a : Nat) (xa_lst : (List externaddr)) (var_0 : (List tagaddr)), 
    (fun_tagsxa xa_lst var_0) ->
    fun_tagsxa ([(.TAG a)] ++ xa_lst) ([a] ++ var_0)
  | fun_tagsxa_case_2 : forall (v_externaddr : externaddr) (xa_lst : (List externaddr)) (var_0 : (List tagaddr)), 
    (fun_tagsxa xa_lst var_0) ->
    fun_tagsxa ([v_externaddr] ++ xa_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:194.1-194.89 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:194.6-194.16 -/
inductive fun_globalsxa : (List externaddr) -> (List globaladdr) -> Prop where
  | fun_globalsxa_case_0 : fun_globalsxa [] []
  | fun_globalsxa_case_1 : forall (a : Nat) (xa_lst : (List externaddr)) (var_0 : (List globaladdr)), 
    (fun_globalsxa xa_lst var_0) ->
    fun_globalsxa ([(.GLOBAL a)] ++ xa_lst) ([a] ++ var_0)
  | fun_globalsxa_case_2 : forall (v_externaddr : externaddr) (xa_lst : (List externaddr)) (var_0 : (List globaladdr)), 
    (fun_globalsxa xa_lst var_0) ->
    fun_globalsxa ([v_externaddr] ++ xa_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:195.1-195.86 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:195.6-195.13 -/
inductive fun_memsxa : (List externaddr) -> (List memaddr) -> Prop where
  | fun_memsxa_case_0 : fun_memsxa [] []
  | fun_memsxa_case_1 : forall (a : Nat) (xa_lst : (List externaddr)) (var_0 : (List memaddr)), 
    (fun_memsxa xa_lst var_0) ->
    fun_memsxa ([(.MEM a)] ++ xa_lst) ([a] ++ var_0)
  | fun_memsxa_case_2 : forall (v_externaddr : externaddr) (xa_lst : (List externaddr)) (var_0 : (List memaddr)), 
    (fun_memsxa xa_lst var_0) ->
    fun_memsxa ([v_externaddr] ++ xa_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:196.1-196.88 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:196.6-196.15 -/
inductive fun_tablesxa : (List externaddr) -> (List tableaddr) -> Prop where
  | fun_tablesxa_case_0 : fun_tablesxa [] []
  | fun_tablesxa_case_1 : forall (a : Nat) (xa_lst : (List externaddr)) (var_0 : (List tableaddr)), 
    (fun_tablesxa xa_lst var_0) ->
    fun_tablesxa ([(.TABLE a)] ++ xa_lst) ([a] ++ var_0)
  | fun_tablesxa_case_2 : forall (v_externaddr : externaddr) (xa_lst : (List externaddr)) (var_0 : (List tableaddr)), 
    (fun_tablesxa xa_lst var_0) ->
    fun_tablesxa ([v_externaddr] ++ xa_lst) var_0

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:197.1-197.87 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:197.6-197.14 -/
inductive fun_funcsxa : (List externaddr) -> (List funcaddr) -> Prop where
  | fun_funcsxa_case_0 : fun_funcsxa [] []
  | fun_funcsxa_case_1 : forall (a : Nat) (xa_lst : (List externaddr)) (var_0 : (List funcaddr)), 
    (fun_funcsxa xa_lst var_0) ->
    fun_funcsxa ([(.FUNC a)] ++ xa_lst) ([a] ++ var_0)
  | fun_funcsxa_case_2 : forall (v_externaddr : externaddr) (xa_lst : (List externaddr)) (var_0 : (List funcaddr)), 
    (fun_funcsxa xa_lst var_0) ->
    fun_funcsxa ([v_externaddr] ++ xa_lst) var_0

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:222.1-222.74 -/
def fun_store : ∀  (v_state : state) , store
  | (.mk_state s f) =>
    s


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:223.1-223.74 -/
def fun_frame : ∀  (v_state : state) , frame
  | (.mk_state s f) =>
    f


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:228.1-228.76 -/
def fun_tagaddr : ∀  (v_state : state) , (List tagaddr)
  | (.mk_state s f) =>
    ((f.MODULE).TAGS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:231.1-231.76 -/
def fun_moduleinst : ∀  (v_state : state) , moduleinst
  | (.mk_state s f) =>
    (f.MODULE)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:232.1-232.76 -/
def fun_taginst : ∀  (v_state : state) , (List taginst)
  | (.mk_state s f) =>
    (s.TAGS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:233.1-233.76 -/
def fun_globalinst : ∀  (v_state : state) , (List globalinst)
  | (.mk_state s f) =>
    (s.GLOBALS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:234.1-234.76 -/
def fun_meminst : ∀  (v_state : state) , (List meminst)
  | (.mk_state s f) =>
    (s.MEMS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:235.1-235.76 -/
def fun_tableinst : ∀  (v_state : state) , (List tableinst)
  | (.mk_state s f) =>
    (s.TABLES)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:236.1-236.76 -/
def fun_funcinst : ∀  (v_state : state) , (List funcinst)
  | (.mk_state s f) =>
    (s.FUNCS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:237.1-237.76 -/
def fun_datainst : ∀  (v_state : state) , (List datainst)
  | (.mk_state s f) =>
    (s.DATAS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:238.1-238.76 -/
def fun_eleminst : ∀  (v_state : state) , (List eleminst)
  | (.mk_state s f) =>
    (s.ELEMS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:239.1-239.76 -/
def fun_structinst : ∀  (v_state : state) , (List structinst)
  | (.mk_state s f) =>
    (s.STRUCTS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:240.1-240.76 -/
def fun_arrayinst : ∀  (v_state : state) , (List arrayinst)
  | (.mk_state s f) =>
    (s.ARRAYS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:241.1-241.76 -/
def fun_exninst : ∀  (v_state : state) , (List exninst)
  | (.mk_state s f) =>
    (s.EXNS)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:256.1-256.85 -/
def fun_type : ∀  (v_state : state) (v_typeidx : typeidx) , deftype
  | (.mk_state s f), x =>
    (((f.MODULE).TYPES)[(proj_uN_0 x)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:257.1-257.85 -/
def fun_tag : ∀  (v_state : state) (v_tagidx : tagidx) , taginst
  | (.mk_state s f), x =>
    ((s.TAGS)[(((f.MODULE).TAGS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:258.1-258.85 -/
def fun_global : ∀  (v_state : state) (v_globalidx : globalidx) , globalinst
  | (.mk_state s f), x =>
    ((s.GLOBALS)[(((f.MODULE).GLOBALS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:259.1-259.85 -/
def fun_mem : ∀  (v_state : state) (v_memidx : memidx) , meminst
  | (.mk_state s f), x =>
    ((s.MEMS)[(((f.MODULE).MEMS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:260.1-260.85 -/
def fun_table : ∀  (v_state : state) (v_tableidx : tableidx) , tableinst
  | (.mk_state s f), x =>
    ((s.TABLES)[(((f.MODULE).TABLES)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:261.1-261.85 -/
def fun_func : ∀  (v_state : state) (v_funcidx : funcidx) , funcinst
  | (.mk_state s f), x =>
    ((s.FUNCS)[(((f.MODULE).FUNCS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:262.1-262.85 -/
def fun_data : ∀  (v_state : state) (v_dataidx : dataidx) , datainst
  | (.mk_state s f), x =>
    ((s.DATAS)[(((f.MODULE).DATAS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:263.1-263.85 -/
def fun_elem : ∀  (v_state : state) (v_tableidx : tableidx) , eleminst
  | (.mk_state s f), x =>
    ((s.ELEMS)[(((f.MODULE).ELEMS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:264.1-264.85 -/
def fun_local : ∀  (v_state : state) (v_localidx : localidx) , (Option val)
  | (.mk_state s f), x =>
    ((f.LOCALS)[(proj_uN_0 x)]!)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:279.1-279.165 -/
def with_local : ∀  (v_state : state) (v_localidx : localidx) (v_val : val) , state
  | (.mk_state s f), x, v =>
    (.mk_state s (f <| LOCALS := (List.modify (f.LOCALS) (proj_uN_0 x) (fun (_ : (Option val)) => (some v))) |>))


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:280.1-280.172 -/
def with_global : ∀  (v_state : state) (v_globalidx : globalidx) (v_val : val) , state
  | (.mk_state s f), x, v =>
    (.mk_state (s <| GLOBALS := (list_update_func (s.GLOBALS) (((f.MODULE).GLOBALS)[(proj_uN_0 x)]!) (fun (var_1 : globalinst) => (var_1 <| VALUE := v |>))) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:281.1-281.174 -/
def with_table : ∀  (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_ref : ref) , state
  | (.mk_state s f), x, i, r =>
    (.mk_state (s <| TABLES := (list_update_func (s.TABLES) (((f.MODULE).TABLES)[(proj_uN_0 x)]!) (fun (var_1 : tableinst) => (var_1 <| REFS := (List.modify (var_1.REFS) i (fun (_ : ref) => r)) |>))) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:282.1-282.165 -/
def with_tableinst : ∀  (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) , state
  | (.mk_state s f), x, ti =>
    (.mk_state (s <| TABLES := (List.modify (s.TABLES) (((f.MODULE).TABLES)[(proj_uN_0 x)]!) (fun (_ : tableinst) => ti)) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:283.1-283.176 -/
def with_mem : ∀  (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0 : (List byte)) , state
  | (.mk_state s f), x, i, j, b_lst =>
    (.mk_state (s <| MEMS := (list_update_func (s.MEMS) (((f.MODULE).MEMS)[(proj_uN_0 x)]!) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (var_1.BYTES) i j b_lst) |>))) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:284.1-284.167 -/
def with_meminst : ∀  (v_state : state) (v_memidx : memidx) (v_meminst : meminst) , state
  | (.mk_state s f), x, mi =>
    (.mk_state (s <| MEMS := (List.modify (s.MEMS) (((f.MODULE).MEMS)[(proj_uN_0 x)]!) (fun (_ : meminst) => mi)) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:285.1-285.169 -/
def with_elem : ∀  (v_state : state) (v_elemidx : elemidx) (var_0 : (List ref)) , state
  | (.mk_state s f), x, r_lst =>
    (.mk_state (s <| ELEMS := (list_update_func (s.ELEMS) (((f.MODULE).ELEMS)[(proj_uN_0 x)]!) (fun (var_1 : eleminst) => (var_1 <| REFS := r_lst |>))) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:286.1-286.170 -/
def with_data : ∀  (v_state : state) (v_dataidx : dataidx) (var_0 : (List byte)) , state
  | (.mk_state s f), x, b_lst =>
    (.mk_state (s <| DATAS := (list_update_func (s.DATAS) (((f.MODULE).DATAS)[(proj_uN_0 x)]!) (fun (var_1 : datainst) => (var_1 <| BYTES := b_lst |>))) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:287.1-287.181 -/
def with_struct : ∀  (v_state : state) (v_structaddr : structaddr) (nat : Nat) (v_fieldval : fieldval) , state
  | (.mk_state s f), a, i, fv =>
    (.mk_state (s <| STRUCTS := (list_update_func (s.STRUCTS) a (fun (var_1 : structinst) => (var_1 <| FIELDS := (List.modify (var_1.FIELDS) i (fun (_ : fieldval) => fv)) |>))) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:288.1-288.180 -/
def with_array : ∀  (v_state : state) (v_arrayaddr : arrayaddr) (nat : Nat) (v_fieldval : fieldval) , state
  | (.mk_state s f), a, i, fv =>
    (.mk_state (s <| ARRAYS := (list_update_func (s.ARRAYS) a (fun (var_1 : arrayinst) => (var_1 <| FIELDS := (List.modify (var_1.FIELDS) i (fun (_ : fieldval) => fv)) |>))) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:302.1-302.140 -/
def add_structinst : ∀  (v_state : state) (var_0 : (List structinst)) , state
  | (.mk_state s f), si_lst =>
    (.mk_state (s <| STRUCTS := ((STRUCTS s) ++ si_lst) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:303.1-303.139 -/
def add_arrayinst : ∀  (v_state : state) (var_0 : (List arrayinst)) , state
  | (.mk_state s f), ai_lst =>
    (.mk_state (s <| ARRAYS := ((ARRAYS s) ++ ai_lst) |>) f)


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:304.1-304.137 -/
def add_exninst : ∀  (v_state : state) (var_0 : (List exninst)) , state
  | (.mk_state s f), exn_lst =>
    (.mk_state (s <| EXNS := ((EXNS s) ++ exn_lst) |>) f)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:313.6-313.16 -/
inductive fun_growtable : tableinst -> Nat -> ref -> (Option tableinst) -> Prop where
  | fun_growtable_case_0 : forall (v_tableinst : tableinst) (v_n : Nat) (r : ref) (tableinst' : tableinst) («at» : addrtype) (i : uN) (j_opt : (Option u64)) (rt : reftype) (r'_lst : (List ref)) (i' : uN), 
    (v_tableinst == { TYPE := (.mk_tabletype «at» (.mk_limits i j_opt) rt), REFS := r'_lst }) ->
    (tableinst' == { TYPE := (.mk_tabletype «at» (.mk_limits i' j_opt) rt), REFS := (r'_lst ++ (List.replicate v_n r)) }) ->
    ((proj_uN_0 i') == ((List.length r'_lst) + v_n)) ->
    Forall (fun (j : u64) => ((proj_uN_0 i') <= (proj_uN_0 j))) (Option.toList j_opt) ->
    fun_growtable v_tableinst v_n r (some tableinst')
  | fun_growtable_case_1 : forall (x0 : tableinst) (x1 : Nat) (x2 : ref), fun_growtable x0 x1 x2 none

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.0-execution.configurations.spectec:314.6-314.14 -/
inductive fun_growmem : meminst -> Nat -> (Option meminst) -> Prop where
  | fun_growmem_case_0 : forall (v_meminst : meminst) (v_n : Nat) (meminst' : meminst) («at» : addrtype) (i : uN) (j_opt : (Option u64)) (b_lst : (List byte)) (i' : uN), 
    (v_meminst == { TYPE := (.PAGE «at» (.mk_limits i j_opt)), BYTES := b_lst }) ->
    (meminst' == { TYPE := (.PAGE «at» (.mk_limits i' j_opt)), BYTES := (b_lst ++ (List.replicate (v_n * (64 * (Ki ))) (.mk_byte 0))) }) ->
    (((proj_uN_0 i') : Nat) == ((((List.length b_lst) : Nat) / ((64 * (Ki )) : Nat)) + (v_n : Nat))) ->
    Forall (fun (j : u64) => ((proj_uN_0 i') <= (proj_uN_0 j))) (Option.toList j_opt) ->
    fun_growmem v_meminst v_n (some meminst')
  | fun_growmem_case_1 : forall (x0 : meminst) (x1 : Nat), fun_growmem x0 x1 none

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:23.1-23.60 -/
inductive Num_ok : store -> num -> numtype -> Prop where
  | mk_Num_ok : forall (s : store) (nt : numtype) (c : num_), 
    (wf_num_ nt c) ->
    Num_ok s (.CONST nt c) nt

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:24.1-24.60 -/
inductive Vec_ok : store -> vec -> vectype -> Prop where
  | mk_Vec_ok : forall (s : store) (vt : vectype) (c : vec_), Vec_ok s (.VCONST vt c) vt

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:25.1-25.60 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:25.1-25.60 -/
inductive Ref_ok : store -> ref -> reftype -> Prop where
  | null : forall (s : store) (ht : heaptype) (ht' : heaptype), 
    (Heaptype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } ht' ht) ->
    Ref_ok s (.REF_NULL ht) (.REF (some .NULL) ht')
  | i31 : forall (s : store) (i : u31), Ref_ok s (.REF_I31_NUM i) (.REF none .I31)
  | struct : forall (s : store) (a : addr) (dt : deftype), 
    (a < (List.length (s.STRUCTS))) ->
    ((((s.STRUCTS)[a]!).TYPE) == dt) ->
    Ref_ok s (.REF_STRUCT_ADDR a) (.REF none (heaptype_deftype dt))
  | array : forall (s : store) (a : addr) (dt : deftype), 
    (a < (List.length (s.ARRAYS))) ->
    ((((s.ARRAYS)[a]!).TYPE) == dt) ->
    Ref_ok s (.REF_ARRAY_ADDR a) (.REF none (heaptype_deftype dt))
  | func : forall (s : store) (a : addr) (dt : deftype), 
    (a < (List.length (s.FUNCS))) ->
    ((((s.FUNCS)[a]!).TYPE) == dt) ->
    Ref_ok s (.REF_FUNC_ADDR a) (.REF none (heaptype_deftype dt))
  | exn : forall (s : store) (a : addr) (exn : exninst), 
    (a < (List.length (s.EXNS))) ->
    (((s.EXNS)[a]!) == exn) ->
    Ref_ok s (.REF_EXN_ADDR a) (.REF none .EXN)
  | host : forall (s : store) (a : addr), Ref_ok s (.REF_HOST_ADDR a) (.REF none .ANY)
  | extern : forall (s : store) (v_addrref : addrref), 
    (Ref_ok s (ref_addrref v_addrref) (.REF none .ANY)) ->
    Ref_ok s (.REF_EXTERN v_addrref) (.REF none .EXTERN)
  | sub : forall (s : store) (v_ref : ref) (rt : reftype) (rt' : reftype), 
    (Ref_ok s v_ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' rt) ->
    Ref_ok s v_ref rt

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:26.1-26.60 -/
inductive Val_ok : store -> val -> valtype -> Prop where
  | num : forall (s : store) (v_num : num) (nt : numtype), 
    (Num_ok s v_num nt) ->
    Val_ok s (val_num v_num) (valtype_numtype nt)
  | vec : forall (s : store) (v_vec : vec) (vt : vectype), 
    (Vec_ok s v_vec vt) ->
    Val_ok s (val_vec v_vec) (valtype_vectype vt)
  | ref : forall (s : store) (v_ref : ref) (rt : reftype), 
    (Ref_ok s v_ref rt) ->
    Val_ok s (val_ref v_ref) (valtype_reftype rt)

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:86.1-86.84 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.1-execution.values.spectec:86.1-86.84 -/
inductive Externaddr_ok : store -> externaddr -> externtype -> Prop where
  | tag : forall (s : store) (a : addr) (v_taginst : taginst), 
    (a < (List.length (s.TAGS))) ->
    (((s.TAGS)[a]!) == v_taginst) ->
    Externaddr_ok s (.TAG a) (.TAG (v_taginst.TYPE))
  | global : forall (s : store) (a : addr) (v_globalinst : globalinst), 
    (a < (List.length (s.GLOBALS))) ->
    (((s.GLOBALS)[a]!) == v_globalinst) ->
    Externaddr_ok s (.GLOBAL a) (.GLOBAL (v_globalinst.TYPE))
  | mem : forall (s : store) (a : addr) (v_meminst : meminst), 
    (a < (List.length (s.MEMS))) ->
    (((s.MEMS)[a]!) == v_meminst) ->
    Externaddr_ok s (.MEM a) (.MEM (v_meminst.TYPE))
  | table : forall (s : store) (a : addr) (v_tableinst : tableinst), 
    (a < (List.length (s.TABLES))) ->
    (((s.TABLES)[a]!) == v_tableinst) ->
    Externaddr_ok s (.TABLE a) (.TABLE (v_tableinst.TYPE))
  | func : forall (s : store) (a : addr) (v_funcinst : funcinst), 
    (a < (List.length (s.FUNCS))) ->
    (((s.FUNCS)[a]!) == v_funcinst) ->
    Externaddr_ok s (.FUNC a) (.FUNC (typeuse_deftype (v_funcinst.TYPE)))
  | sub : forall (s : store) (v_externaddr : externaddr) (xt : externtype) (xt' : externtype), 
    (Externaddr_ok s v_externaddr xt') ->
    (Externtype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } xt' xt) ->
    Externaddr_ok s v_externaddr xt

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:5.6-5.19 -/
inductive fun_inst_valtype : moduleinst -> valtype -> valtype -> Prop where
  | fun_inst_valtype_case_0 : forall (v_moduleinst : moduleinst) (t : valtype) (dt_lst : (List deftype)) (var_0 : valtype), 
    (fun_subst_all_valtype t (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == (v_moduleinst.TYPES)) ->
    fun_inst_valtype v_moduleinst t var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:6.6-6.19 -/
inductive fun_inst_reftype : moduleinst -> reftype -> reftype -> Prop where
  | fun_inst_reftype_case_0 : forall (v_moduleinst : moduleinst) (rt : reftype) (dt_lst : (List deftype)) (var_0 : reftype), 
    (fun_subst_all_reftype rt (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == (v_moduleinst.TYPES)) ->
    fun_inst_reftype v_moduleinst rt var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:7.6-7.22 -/
inductive fun_inst_globaltype : moduleinst -> globaltype -> globaltype -> Prop where
  | fun_inst_globaltype_case_0 : forall (v_moduleinst : moduleinst) (gt : globaltype) (dt_lst : (List deftype)) (var_0 : globaltype), 
    (fun_subst_all_globaltype gt (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == (v_moduleinst.TYPES)) ->
    fun_inst_globaltype v_moduleinst gt var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:8.6-8.19 -/
inductive fun_inst_memtype : moduleinst -> memtype -> memtype -> Prop where
  | fun_inst_memtype_case_0 : forall (v_moduleinst : moduleinst) (mt : memtype) (dt_lst : (List deftype)) (var_0 : memtype), 
    (fun_subst_all_memtype mt (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == (v_moduleinst.TYPES)) ->
    fun_inst_memtype v_moduleinst mt var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.2-execution.types.spectec:9.6-9.21 -/
inductive fun_inst_tabletype : moduleinst -> tabletype -> tabletype -> Prop where
  | fun_inst_tabletype_case_0 : forall (v_moduleinst : moduleinst) (tt : tabletype) (dt_lst : (List deftype)) (var_0 : tabletype), 
    (fun_subst_all_tabletype tt (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_0) ->
    (dt_lst == (v_moduleinst.TYPES)) ->
    fun_inst_tabletype v_moduleinst tt var_0

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:650.1-653.22 -/
inductive Step_pure_before_ref_eq_true : (List instr) -> Prop where
  | ref_eq_null_0 : forall (ref_1 : ref) (ref_2 : ref) (ht_1 : heaptype) (ht_2 : heaptype), 
    ((ref_1 == (.REF_NULL ht_1)) && (ref_2 == (.REF_NULL ht_2))) ->
    Step_pure_before_ref_eq_true [(instr_ref ref_1), (instr_ref ref_2), .REF_EQ]

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:6.1-6.88 -/
inductive Step_pure : (List instr) -> (List instr) -> Prop where
  | unreachable : Step_pure [.UNREACHABLE] [.TRAP]
  | nop : Step_pure [.NOP] []
  | drop : forall (v_val : val), Step_pure [(instr_val v_val), .DROP] []
  | select_true : forall (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : (Option (List valtype))), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) != 0) ->
    Step_pure [(instr_val val_1), (instr_val val_2), (.CONST .I32 c), (.SELECT t_lst_opt)] [(instr_val val_1)]
  | select_false : forall (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : (Option (List valtype))), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) == 0) ->
    Step_pure [(instr_val val_1), (instr_val val_2), (.CONST .I32 c), (.SELECT t_lst_opt)] [(instr_val val_2)]
  | if_true : forall (c : num_) (bt : blocktype) (instr_1_lst : (List instr)) (instr_2_lst : (List instr)), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) != 0) ->
    Step_pure [(.CONST .I32 c), (.IFELSE bt instr_1_lst instr_2_lst)] [(.BLOCK bt instr_1_lst)]
  | if_false : forall (c : num_) (bt : blocktype) (instr_1_lst : (List instr)) (instr_2_lst : (List instr)), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) == 0) ->
    Step_pure [(.CONST .I32 c), (.IFELSE bt instr_1_lst instr_2_lst)] [(.BLOCK bt instr_2_lst)]
  | label_vals : forall (v_n : n) (instr_lst : (List instr)) (val_lst : (List val)), Step_pure [(.LABEL_ v_n instr_lst (List.map (fun (v_val : val) => (instr_val v_val)) val_lst))] (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)
  | br_label_zero : forall (v_n : n) (instr'_lst : (List instr)) (val'_lst : (List val)) (val_lst : (List val)) (l : labelidx) (instr_lst : (List instr)), 
    ((proj_uN_0 l) == 0) ->
    Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (val' : val) => (instr_val val')) val'_lst) ++ ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BR l)] ++ instr_lst))))] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr'_lst)
  | br_label_succ : forall (v_n : n) (instr'_lst : (List instr)) (val_lst : (List val)) (l : labelidx) (instr_lst : (List instr)), 
    ((proj_uN_0 l) > 0) ->
    Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BR l)] ++ instr_lst)))] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.BR (.mk_uN ((((proj_uN_0 l) : Nat) - (1 : Nat)) : Nat)))])
  | br_handler : forall (v_n : n) (catch_lst : (List «catch»)) (val_lst : (List val)) (l : labelidx) (instr_lst : (List instr)), Step_pure [(.HANDLER_ v_n catch_lst ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.BR l)] ++ instr_lst)))] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.BR l)])
  | br_if_true : forall (c : num_) (l : labelidx), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) != 0) ->
    Step_pure [(.CONST .I32 c), (.BR_IF l)] [(.BR l)]
  | br_if_false : forall (c : num_) (l : labelidx), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) == 0) ->
    Step_pure [(.CONST .I32 c), (.BR_IF l)] []
  | br_table_lt : forall (i : num_) (l_lst : (List labelidx)) (l' : labelidx), 
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length l_lst)) ->
    ((proj_num__0 i) != none) ->
    (wf_num_ .I32 i) ->
    Step_pure [(.CONST .I32 i), (.BR_TABLE l_lst l')] [(.BR (l_lst[(proj_uN_0 (Option.get! (proj_num__0 i)))]!))]
  | br_table_ge : forall (i : num_) (l_lst : (List labelidx)) (l' : labelidx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length l_lst)) ->
    Step_pure [(.CONST .I32 i), (.BR_TABLE l_lst l')] [(.BR l')]
  | br_on_null_null : forall (v_val : val) (l : labelidx) (ht : heaptype), 
    (v_val == (.REF_NULL ht)) ->
    Step_pure [(instr_val v_val), (.BR_ON_NULL l)] [(.BR l)]
  | br_on_null_addr : forall (v_val : val) (l : labelidx) (ht : heaptype), 
    (v_val != (.REF_NULL ht)) ->
    Step_pure [(instr_val v_val), (.BR_ON_NULL l)] [(instr_val v_val)]
  | br_on_non_null_null : forall (v_val : val) (l : labelidx) (ht : heaptype), 
    (v_val == (.REF_NULL ht)) ->
    Step_pure [(instr_val v_val), (.BR_ON_NON_NULL l)] []
  | br_on_non_null_addr : forall (v_val : val) (l : labelidx) (ht : heaptype), 
    (v_val != (.REF_NULL ht)) ->
    Step_pure [(instr_val v_val), (.BR_ON_NON_NULL l)] [(instr_val v_val), (.BR l)]
  | call_indirect : forall (x : idx) (yy : typeuse), Step_pure [(.CALL_INDIRECT x yy)] [(.TABLE_GET x), (.REF_CAST (.REF (some .NULL) (heaptype_typeuse yy))), (.CALL_REF yy)]
  | return_call_indirect : forall (x : idx) (yy : typeuse), Step_pure [(.RETURN_CALL_INDIRECT x yy)] [(.TABLE_GET x), (.REF_CAST (.REF (some .NULL) (heaptype_typeuse yy))), (.RETURN_CALL_REF yy)]
  | frame_vals : forall (v_n : n) (f : frame) (val_lst : (List val)), Step_pure [(.FRAME_ v_n f (List.map (fun (v_val : val) => (instr_val v_val)) val_lst))] (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)
  | return_frame : forall (v_n : n) (f : frame) (val'_lst : (List val)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.FRAME_ v_n f ((List.map (fun (val' : val) => (instr_val val')) val'_lst) ++ ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.RETURN] ++ instr_lst))))] (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)
  | return_label : forall (v_n : n) (instr'_lst : (List instr)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.RETURN] ++ instr_lst)))] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [.RETURN])
  | return_handler : forall (v_n : n) (catch_lst : (List «catch»)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.HANDLER_ v_n catch_lst ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.RETURN] ++ instr_lst)))] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [.RETURN])
  | handler_vals : forall (v_n : n) (catch_lst : (List «catch»)) (val_lst : (List val)), Step_pure [(.HANDLER_ v_n catch_lst (List.map (fun (v_val : val) => (instr_val v_val)) val_lst))] (List.map (fun (v_val : val) => (instr_val v_val)) val_lst)
  | trap_instrs : forall (val_lst : (List val)) (instr_lst : (List instr)), 
    ((val_lst != []) || (instr_lst != [])) ->
    Step_pure ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([.TRAP] ++ instr_lst)) [.TRAP]
  | trap_label : forall (v_n : n) (instr'_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst [.TRAP])] [.TRAP]
  | trap_frame : forall (v_n : n) (f : frame), Step_pure [(.FRAME_ v_n f [.TRAP])] [.TRAP]
  | local_tee : forall (v_val : val) (x : idx), Step_pure [(instr_val v_val), (.LOCAL_TEE x)] [(instr_val v_val), (instr_val v_val), (.LOCAL_SET x)]
  | ref_i31 : forall (i : num_), 
    ((proj_num__0 i) != none) ->
    (wf_num_ .I32 i) ->
    Step_pure [(.CONST .I32 i), .REF_I31] [(.REF_I31_NUM (wrap__ 32 31 (Option.get! (proj_num__0 i))))]
  | ref_is_null_true : forall (v_ref : ref) (ht : heaptype), 
    (v_ref == (.REF_NULL ht)) ->
    Step_pure [(instr_ref v_ref), .REF_IS_NULL] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))]
  | ref_is_null_false : forall (v_ref : ref) (ht : heaptype), 
    (v_ref != (.REF_NULL ht)) ->
    Step_pure [(instr_ref v_ref), .REF_IS_NULL] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)))]
  | ref_as_non_null_null : forall (v_ref : ref) (ht : heaptype), 
    (v_ref == (.REF_NULL ht)) ->
    Step_pure [(instr_ref v_ref), .REF_AS_NON_NULL] [.TRAP]
  | ref_as_non_null_addr : forall (v_ref : ref) (ht : heaptype), 
    (v_ref != (.REF_NULL ht)) ->
    Step_pure [(instr_ref v_ref), .REF_AS_NON_NULL] [(instr_ref v_ref)]
  | ref_eq_null : forall (ref_1 : ref) (ref_2 : ref) (ht_1 : heaptype) (ht_2 : heaptype), 
    ((ref_1 == (.REF_NULL ht_1)) && (ref_2 == (.REF_NULL ht_2))) ->
    Step_pure [(instr_ref ref_1), (instr_ref ref_2), .REF_EQ] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))]
  | ref_eq_true : forall (ref_1 : ref) (ref_2 : ref) (ht_1 : heaptype) (ht_2 : heaptype), 
    ((ref_1 != (.REF_NULL ht_1)) || (ref_2 != (.REF_NULL ht_2))) ->
    (ref_1 == ref_2) ->
    Step_pure [(instr_ref ref_1), (instr_ref ref_2), .REF_EQ] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))]
  | ref_eq_false : forall (ref_1 : ref) (ref_2 : ref) (ht_1 : heaptype) (ht_2 : heaptype), 
    (ref_1 != ref_2) ->
    ((ref_1 != (.REF_NULL ht_1)) || (ref_2 != (.REF_NULL ht_2))) ->
    Step_pure [(instr_ref ref_1), (instr_ref ref_2), .REF_EQ] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)))]
  | i31_get_null : forall (ht : heaptype) (v_sx : sx), Step_pure [(.REF_NULL ht), (.I31_GET v_sx)] [.TRAP]
  | i31_get_num : forall (i : u31) (v_sx : sx), Step_pure [(.REF_I31_NUM i), (.I31_GET v_sx)] [(.CONST .I32 (.mk_num__0 .I32 (extend__ 31 32 v_sx i)))]
  | array_new : forall (v_val : val) (v_n : n) (x : idx), Step_pure [(instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW x)] ((List.replicate v_n (instr_val v_val)) ++ [(.ARRAY_NEW_FIXED x (.mk_uN v_n))])
  | extern_convert_any_null : forall (ht : heaptype), Step_pure [(.REF_NULL ht), .EXTERN_CONVERT_ANY] [(.REF_NULL .EXTERN)]
  | extern_convert_any_addr : forall (v_addrref : addrref), Step_pure [(instr_addrref v_addrref), .EXTERN_CONVERT_ANY] [(.REF_EXTERN v_addrref)]
  | any_convert_extern_null : forall (ht : heaptype), Step_pure [(.REF_NULL ht), .ANY_CONVERT_EXTERN] [(.REF_NULL .ANY)]
  | any_convert_extern_addr : forall (v_addrref : addrref), Step_pure [(.REF_EXTERN v_addrref), .ANY_CONVERT_EXTERN] [(instr_addrref v_addrref)]
  | unop_val : forall (nt : numtype) (c_1 : num_) (unop : unop_) (c : num_) (var_0 : (List num_)), 
    (fun_unop_ nt unop c_1 var_0) ->
    (wf_num_ nt c_1) ->
    (wf_unop_ nt unop) ->
    (wf_num_ nt c) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.CONST nt c_1), (.UNOP nt unop)] [(.CONST nt c)]
  | unop_trap : forall (nt : numtype) (c_1 : num_) (unop : unop_) (var_0 : (List num_)), 
    (fun_unop_ nt unop c_1 var_0) ->
    (wf_num_ nt c_1) ->
    (wf_unop_ nt unop) ->
    (var_0 == []) ->
    Step_pure [(.CONST nt c_1), (.UNOP nt unop)] [.TRAP]
  | binop_val : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (c : num_) (var_0 : (List num_)), 
    (fun_binop_ nt binop c_1 c_2 var_0) ->
    (wf_num_ nt c_1) ->
    (wf_num_ nt c_2) ->
    (wf_binop_ nt binop) ->
    (wf_num_ nt c) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.CONST nt c_1), (.CONST nt c_2), (.BINOP nt binop)] [(.CONST nt c)]
  | binop_trap : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (var_0 : (List num_)), 
    (fun_binop_ nt binop c_1 c_2 var_0) ->
    (wf_num_ nt c_1) ->
    (wf_num_ nt c_2) ->
    (wf_binop_ nt binop) ->
    (var_0 == []) ->
    Step_pure [(.CONST nt c_1), (.CONST nt c_2), (.BINOP nt binop)] [.TRAP]
  | testop : forall (nt : numtype) (c_1 : num_) (testop : testop_) (c : num_), 
    (wf_num_ nt c_1) ->
    (wf_testop_ nt testop) ->
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((Option.get! (proj_num__0 c)) == (fun_testop_ nt testop c_1)) ->
    Step_pure [(.CONST nt c_1), (.TESTOP nt testop)] [(.CONST .I32 c)]
  | relop : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (relop : relop_) (c : num_), 
    (wf_num_ nt c_1) ->
    (wf_num_ nt c_2) ->
    (wf_relop_ nt relop) ->
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((Option.get! (proj_num__0 c)) == (fun_relop_ nt relop c_1 c_2)) ->
    Step_pure [(.CONST nt c_1), (.CONST nt c_2), (.RELOP nt relop)] [(.CONST .I32 c)]
  | cvtop_val : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (cvtop : cvtop__) (c : num_) (var_0 : (List num_)), 
    (fun_cvtop__ nt_1 nt_2 cvtop c_1 var_0) ->
    (wf_num_ nt_1 c_1) ->
    (wf_cvtop__ nt_1 nt_2 cvtop) ->
    (wf_num_ nt_2 c) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.CONST nt_1 c_1), (.CVTOP nt_2 nt_1 cvtop)] [(.CONST nt_2 c)]
  | cvtop_trap : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (cvtop : cvtop__) (var_0 : (List num_)), 
    (fun_cvtop__ nt_1 nt_2 cvtop c_1 var_0) ->
    (wf_num_ nt_1 c_1) ->
    (wf_cvtop__ nt_1 nt_2 cvtop) ->
    (var_0 == []) ->
    Step_pure [(.CONST nt_1 c_1), (.CVTOP nt_2 nt_1 cvtop)] [.TRAP]
  | vvunop : forall (c_1 : vec_) (v_vvunop : vvunop) (c : vec_), 
    ((List.length (vvunop_ .V128 v_vvunop c_1)) > 0) ->
    (List.contains (vvunop_ .V128 v_vvunop c_1) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VVUNOP .V128 v_vvunop)] [(.VCONST .V128 c)]
  | vvbinop : forall (c_1 : vec_) (c_2 : vec_) (v_vvbinop : vvbinop) (c : vec_), 
    ((List.length (vvbinop_ .V128 v_vvbinop c_1 c_2)) > 0) ->
    (List.contains (vvbinop_ .V128 v_vvbinop c_1 c_2) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VVBINOP .V128 v_vvbinop)] [(.VCONST .V128 c)]
  | vvternop : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (v_vvternop : vvternop) (c : vec_), 
    ((List.length (vvternop_ .V128 v_vvternop c_1 c_2 c_3)) > 0) ->
    (List.contains (vvternop_ .V128 v_vvternop c_1 c_2 c_3) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VVTERNOP .V128 v_vvternop)] [(.VCONST .V128 c)]
  | vvtestop : forall (c_1 : vec_) (c : num_), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((Option.get! (proj_num__0 c)) == (inez_ (vsize .V128) c_1)) ->
    Step_pure [(.VCONST .V128 c_1), (.VVTESTOP .V128 .ANY_TRUE)] [(.CONST .I32 c)]
  | vunop_val : forall (c_1 : vec_) (sh : shape) (vunop : vunop_) (c : vec_) (var_0 : (List vec_)), 
    (fun_vunop_ sh vunop c_1 var_0) ->
    (wf_vunop_ sh vunop) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.VCONST .V128 c_1), (.VUNOP sh vunop)] [(.VCONST .V128 c)]
  | vunop_trap : forall (c_1 : vec_) (sh : shape) (vunop : vunop_) (var_0 : (List vec_)), 
    (fun_vunop_ sh vunop c_1 var_0) ->
    (wf_vunop_ sh vunop) ->
    (var_0 == []) ->
    Step_pure [(.VCONST .V128 c_1), (.VUNOP sh vunop)] [.TRAP]
  | vbinop_val : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (c : vec_) (var_0 : (List vec_)), 
    (fun_vbinop_ sh vbinop c_1 c_2 var_0) ->
    (wf_vbinop_ sh vbinop) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VBINOP sh vbinop)] [(.VCONST .V128 c)]
  | vbinop_trap : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (var_0 : (List vec_)), 
    (fun_vbinop_ sh vbinop c_1 c_2 var_0) ->
    (wf_vbinop_ sh vbinop) ->
    (var_0 == []) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VBINOP sh vbinop)] [.TRAP]
  | vternop_val : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (sh : shape) (vternop : vternop_) (c : vec_) (var_0 : (List vec_)), 
    (fun_vternop_ sh vternop c_1 c_2 c_3 var_0) ->
    (wf_vternop_ sh vternop) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VTERNOP sh vternop)] [(.VCONST .V128 c)]
  | vternop_trap : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (sh : shape) (vternop : vternop_) (var_0 : (List vec_)), 
    (fun_vternop_ sh vternop c_1 c_2 c_3 var_0) ->
    (wf_vternop_ sh vternop) ->
    (var_0 == []) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VTERNOP sh vternop)] [.TRAP]
  | vtestop : forall (c_1 : vec_) (v_Jnn : Jnn) (v_M : M) (c : num_) (i_lst : (List lane_)) (var_0 : Nat), 
    Forall (fun (i : lane_) => ((proj_lane__2 i) != none)) i_lst ->
    (fun_prod (List.map (fun (i : lane_) => (proj_uN_0 (inez_ (jsizenn v_Jnn) (Option.get! (proj_lane__2 i))))) i_lst) var_0) ->
    (wf_num_ .I32 c) ->
    Forall (fun (i : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) i)) i_lst ->
    (i_lst == (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c_1)) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) == var_0) ->
    Step_pure [(.VCONST .V128 c_1), (.VTESTOP (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (.mk_vtestop__0 v_Jnn v_M .ALL_TRUE))] [(.CONST .I32 c)]
  | vrelop : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vrelop : vrelop_) (c : vec_) (var_0 : vec_), 
    (fun_vrelop_ sh vrelop c_1 c_2 var_0) ->
    (wf_vrelop_ sh vrelop) ->
    (c == var_0) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VRELOP sh vrelop)] [(.VCONST .V128 c)]
  | vshiftop : forall (c_1 : vec_) (i : num_) (sh : ishape) (vshiftop : vshiftop_) (c : vec_) (var_0 : vec_), 
    ((proj_num__0 i) != none) ->
    (fun_vshiftop_ sh vshiftop c_1 (Option.get! (proj_num__0 i)) var_0) ->
    (wf_num_ .I32 i) ->
    (wf_vshiftop_ sh vshiftop) ->
    (c == var_0) ->
    Step_pure [(.VCONST .V128 c_1), (.CONST .I32 i), (.VSHIFTOP sh vshiftop)] [(.VCONST .V128 c)]
  | vbitmask : forall (c_1 : vec_) (sh : ishape) (c : num_) (var_0 : u32), 
    (fun_vbitmaskop_ sh c_1 var_0) ->
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((Option.get! (proj_num__0 c)) == var_0) ->
    Step_pure [(.VCONST .V128 c_1), (.VBITMASK sh)] [(.CONST .I32 c)]
  | vswizzlop : forall (c_1 : vec_) (c_2 : vec_) (sh : bshape) (swizzlop : vswizzlop_) (c : vec_) (var_0 : vec_), 
    (fun_vswizzlop_ sh swizzlop c_1 c_2 var_0) ->
    (wf_vswizzlop_ sh swizzlop) ->
    (c == var_0) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VSWIZZLOP sh swizzlop)] [(.VCONST .V128 c)]
  | vshuffle : forall (c_1 : vec_) (c_2 : vec_) (sh : bshape) (i_lst : (List laneidx)) (c : vec_) (var_0 : vec_), 
    (fun_vshufflop_ sh i_lst c_1 c_2 var_0) ->
    (c == var_0) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VSHUFFLE sh i_lst)] [(.VCONST .V128 c)]
  | vsplat : forall (v_Lnn : Lnn) (c_1 : num_) (v_M : M) (c : vec_) (var_0 : lane_), 
    (fun_lpacknum_ v_Lnn c_1 var_0) ->
    (wf_num_ (lunpack v_Lnn) c_1) ->
    (c == (inv_lanes_ (.X v_Lnn (.mk_dim v_M)) (List.replicate v_M var_0))) ->
    Step_pure [(.CONST (lunpack v_Lnn) c_1), (.VSPLAT (.X v_Lnn (.mk_dim v_M)))] [(.VCONST .V128 c)]
  | vextract_lane_num : forall (c_1 : vec_) (nt : numtype) (v_M : M) (i : laneidx) (c_2 : num_), 
    (wf_lane_ (fun_lanetype (.X (lanetype_numtype nt) (.mk_dim v_M))) (.mk_lane__0 nt c_2)) ->
    ((proj_uN_0 i) < (List.length (lanes_ (.X (lanetype_numtype nt) (.mk_dim v_M)) c_1))) ->
    ((.mk_lane__0 nt c_2) == ((lanes_ (.X (lanetype_numtype nt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!)) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTRACT_LANE (.X (lanetype_numtype nt) (.mk_dim v_M)) none i)] [(.CONST nt c_2)]
  | vextract_lane_pack : forall (c_1 : vec_) (pt : packtype) (v_M : M) (v_sx : sx) (i : laneidx) (c_2 : num_), 
    (wf_num_ .I32 c_2) ->
    ((proj_num__0 c_2) != none) ->
    ((proj_lane__1 ((lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!)) != none) ->
    ((proj_uN_0 i) < (List.length (lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1))) ->
    ((Option.get! (proj_num__0 c_2)) == (extend__ (psize pt) 32 v_sx (Option.get! (proj_lane__1 ((lanes_ (.X (lanetype_packtype pt) (.mk_dim v_M)) c_1)[(proj_uN_0 i)]!))))) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTRACT_LANE (.X (lanetype_packtype pt) (.mk_dim v_M)) (some v_sx) i)] [(.CONST .I32 c_2)]
  | vreplace_lane : forall (c_1 : vec_) (v_Lnn : Lnn) (c_2 : num_) (v_M : M) (i : laneidx) (c : vec_) (var_0 : lane_), 
    (fun_lpacknum_ v_Lnn c_2 var_0) ->
    (wf_num_ (lunpack v_Lnn) c_2) ->
    (c == (inv_lanes_ (.X v_Lnn (.mk_dim v_M)) (List.modify (lanes_ (.X v_Lnn (.mk_dim v_M)) c_1) (proj_uN_0 i) (fun (_ : lane_) => var_0)))) ->
    Step_pure [(.VCONST .V128 c_1), (.CONST (lunpack v_Lnn) c_2), (.VREPLACE_LANE (.X v_Lnn (.mk_dim v_M)) i)] [(.VCONST .V128 c)]
  | vextunop : forall (c_1 : vec_) (sh_2 : ishape) (sh_1 : ishape) (vextunop : vextunop__) (c : vec_) (var_0 : vec_), 
    (fun_vextunop__ sh_1 sh_2 vextunop c_1 var_0) ->
    (wf_vextunop__ sh_1 sh_2 vextunop) ->
    (var_0 == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTUNOP sh_2 sh_1 vextunop)] [(.VCONST .V128 c)]
  | vextbinop : forall (c_1 : vec_) (c_2 : vec_) (sh_2 : ishape) (sh_1 : ishape) (vextbinop : vextbinop__) (c : vec_) (var_0 : vec_), 
    (fun_vextbinop__ sh_1 sh_2 vextbinop c_1 c_2 var_0) ->
    (wf_vextbinop__ sh_1 sh_2 vextbinop) ->
    (var_0 == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VEXTBINOP sh_2 sh_1 vextbinop)] [(.VCONST .V128 c)]
  | vextternop : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (sh_2 : ishape) (sh_1 : ishape) (vextternop : vextternop__) (c : vec_) (var_0 : vec_), 
    (fun_vextternop__ sh_1 sh_2 vextternop c_1 c_2 c_3 var_0) ->
    (wf_vextternop__ sh_1 sh_2 vextternop) ->
    (var_0 == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VEXTTERNOP sh_2 sh_1 vextternop)] [(.VCONST .V128 c)]
  | vnarrow : forall (c_1 : vec_) (c_2 : vec_) (sh_2 : ishape) (sh_1 : ishape) (v_sx : sx) (c : vec_) (var_0 : vec_), 
    (fun_vnarrowop__ (proj_ishape_0 sh_1) (proj_ishape_0 sh_2) v_sx c_1 c_2 var_0) ->
    (c == var_0) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VNARROW sh_2 sh_1 v_sx)] [(.VCONST .V128 c)]
  | vcvtop : forall (c_1 : vec_) (sh_2 : shape) (sh_1 : shape) (vcvtop : vcvtop__) (c : vec_) (var_0 : vec_), 
    (fun_vcvtop__ sh_1 sh_2 vcvtop c_1 var_0) ->
    (wf_vcvtop__ sh_1 sh_2 vcvtop) ->
    (c == var_0) ->
    Step_pure [(.VCONST .V128 c_1), (.VCVTOP sh_2 sh_1 vcvtop)] [(.VCONST .V128 c)]

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:69.6-69.17 -/
inductive fun_blocktype_ : state -> blocktype -> instrtype -> Prop where
  | fun_blocktype__case_0 : forall (z : state) (x : uN) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Expand (fun_type z x) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    fun_blocktype_ z (._IDX x) (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | fun_blocktype__case_1 : forall (z : state) (t_opt : (Option valtype)), fun_blocktype_ z (._RESULT t_opt) (.mk_instrtype (.mk_list []) [] (.mk_list (Option.toList t_opt)))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:151.1-153.15 -/
inductive Step_read_before_br_on_cast_fail : config -> Prop where
  | br_on_cast_succeed_0 : forall (s : store) (f : frame) (v_ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (rt : reftype) (var_0 : reftype), 
    (fun_inst_reftype (f.MODULE) rt_2 var_0) ->
    (Ref_ok s v_ref rt) ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt var_0) ->
    Step_read_before_br_on_cast_fail (.mk_config (.mk_state s f) [(instr_ref v_ref), (.BR_ON_CAST l rt_1 rt_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:162.1-164.15 -/
inductive Step_read_before_br_on_cast_fail_fail : config -> Prop where
  | br_on_cast_fail_succeed_0 : forall (s : store) (f : frame) (v_ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (rt : reftype) (var_0 : reftype), 
    (fun_inst_reftype (f.MODULE) rt_2 var_0) ->
    (Ref_ok s v_ref rt) ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt var_0) ->
    Step_read_before_br_on_cast_fail_fail (.mk_config (.mk_state s f) [(instr_ref v_ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:357.1-360.14 -/
inductive Step_read_before_table_fill_zero : config -> Prop where
  | table_fill_oob_0 : forall (z : state) («at» : addrtype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS))) ->
    Step_read_before_table_fill_zero (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:374.1-377.14 -/
inductive Step_read_before_table_copy_zero : config -> Prop where
  | table_copy_oob_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length ((fun_table z x_1).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length ((fun_table z x_2).REFS)))) ->
    Step_read_before_table_copy_zero (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:379.1-384.19 -/
inductive Step_read_before_table_copy_le : config -> Prop where
  | table_copy_zero_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    (¬(Step_read_before_table_copy_zero (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x y)]))) ->
    (v_n == 0) ->
    Step_read_before_table_copy_le (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x y)])
  | table_copy_oob_1 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length ((fun_table z x_1).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length ((fun_table z x_2).REFS)))) ->
    Step_read_before_table_copy_le (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:398.1-401.14 -/
inductive Step_read_before_table_init_zero : config -> Prop where
  | table_init_oob_0 : forall (z : state) («at» : addrtype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_elem z y).REFS)))) ->
    Step_read_before_table_init_zero (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:559.1-562.14 -/
inductive Step_read_before_memory_fill_zero : config -> Prop where
  | memory_fill_oob_0 : forall (z : state) («at» : addrtype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read_before_memory_fill_zero (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:576.1-579.14 -/
inductive Step_read_before_memory_copy_zero : config -> Prop where
  | memory_copy_oob_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length ((fun_mem z x_1).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length ((fun_mem z x_2).BYTES)))) ->
    Step_read_before_memory_copy_zero (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:581.1-586.19 -/
inductive Step_read_before_memory_copy_le : config -> Prop where
  | memory_copy_zero_0 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    (¬(Step_read_before_memory_copy_zero (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]))) ->
    (v_n == 0) ->
    Step_read_before_memory_copy_le (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)])
  | memory_copy_oob_1 : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length ((fun_mem z x_1).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length ((fun_mem z x_2).BYTES)))) ->
    Step_read_before_memory_copy_le (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:600.1-603.14 -/
inductive Step_read_before_memory_init_zero : config -> Prop where
  | memory_init_oob_0 : forall (z : state) («at» : addrtype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z x).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_data z y).BYTES)))) ->
    Step_read_before_memory_init_zero (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:666.1-668.15 -/
inductive Step_read_before_ref_test_false : config -> Prop where
  | ref_test_true_0 : forall (s : store) (f : frame) (v_ref : ref) (rt : reftype) (rt' : reftype) (var_0 : reftype), 
    (fun_inst_reftype (f.MODULE) rt var_0) ->
    (Ref_ok s v_ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' var_0) ->
    Step_read_before_ref_test_false (.mk_config (.mk_state s f) [(instr_ref v_ref), (.REF_TEST rt)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:677.1-679.15 -/
inductive Step_read_before_ref_cast_fail : config -> Prop where
  | ref_cast_succeed_0 : forall (s : store) (f : frame) (v_ref : ref) (rt : reftype) (rt' : reftype) (var_0 : reftype), 
    (fun_inst_reftype (f.MODULE) rt var_0) ->
    (Ref_ok s v_ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' var_0) ->
    Step_read_before_ref_cast_fail (.mk_config (.mk_state s f) [(instr_ref v_ref), (.REF_CAST rt)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:805.1-808.14 -/
inductive Step_read_before_array_fill_zero : config -> Prop where
  | array_fill_oob_0 : forall (z : state) (a : addr) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array_fill_zero (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:832.1-836.14 -/
inductive Step_read_before_array_copy_zero : config -> Prop where
  | array_copy_oob2_0 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    ((proj_num__0 i_2) != none) ->
    (a_2 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length (((fun_arrayinst z)[a_2]!).FIELDS))) ->
    Step_read_before_array_copy_zero (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])
  | array_copy_oob1_0 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    ((proj_num__0 i_1) != none) ->
    (a_1 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length (((fun_arrayinst z)[a_1]!).FIELDS))) ->
    Step_read_before_array_copy_zero (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:838.1-848.24 -/
inductive Step_read_before_array_copy_le : config -> Prop where
  | array_copy_zero_0 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    (¬(Step_read_before_array_copy_zero (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]))) ->
    (v_n == 0) ->
    Step_read_before_array_copy_le (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])
  | array_copy_oob2_1 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    ((proj_num__0 i_2) != none) ->
    (a_2 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length (((fun_arrayinst z)[a_2]!).FIELDS))) ->
    Step_read_before_array_copy_le (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])
  | array_copy_oob1_1 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    ((proj_num__0 i_1) != none) ->
    (a_1 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length (((fun_arrayinst z)[a_1]!).FIELDS))) ->
    Step_read_before_array_copy_le (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:850.1-859.24 -/
inductive Step_read_before_array_copy_gt : config -> Prop where
  | array_copy_le_0 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx) (sx_opt : (Option sx)) (mut_opt : (Option «mut»)) (zt_2 : storagetype), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    (¬(Step_read_before_array_copy_le (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]))) ->
    (Expand (fun_type z x_2) (.ARRAY (.mk_fieldtype mut_opt zt_2))) ->
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 i_2)))) && (sx_opt == (fun_sx zt_2))) ->
    Step_read_before_array_copy_gt (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])
  | array_copy_zero_1 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    (¬(Step_read_before_array_copy_zero (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]))) ->
    (v_n == 0) ->
    Step_read_before_array_copy_gt (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])
  | array_copy_oob2_2 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    ((proj_num__0 i_2) != none) ->
    (a_2 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length (((fun_arrayinst z)[a_2]!).FIELDS))) ->
    Step_read_before_array_copy_gt (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])
  | array_copy_oob1_2 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    ((proj_num__0 i_1) != none) ->
    (a_1 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length (((fun_arrayinst z)[a_1]!).FIELDS))) ->
    Step_read_before_array_copy_gt (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:875.1-879.14 -/
inductive Step_read_before_array_init_elem_zero : config -> Prop where
  | array_init_elem_oob2_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_elem z y).REFS))) ->
    Step_read_before_array_init_elem_zero (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)])
  | array_init_elem_oob1_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array_init_elem_zero (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:904.1-908.14 -/
inductive Step_read_before_array_init_data_zero : config -> Prop where
  | array_init_data_oob2_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx) (mut_opt : (Option «mut»)) (zt : storagetype), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((proj_num__0 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 j))) + ((((v_n * (zsize zt)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_data z y).BYTES))) ->
    Step_read_before_array_init_data_zero (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)])
  | array_init_data_oob1_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array_init_data_zero (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:911.1-918.62 -/
inductive Step_read_before_array_init_data_num : config -> Prop where
  | array_init_data_zero_0 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    (¬(Step_read_before_array_init_data_zero (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]))) ->
    (v_n == 0) ->
    Step_read_before_array_init_data_num (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)])
  | array_init_data_oob2_1 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx) (mut_opt : (Option «mut»)) (zt : storagetype), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((proj_num__0 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 j))) + ((((v_n * (zsize zt)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_data z y).BYTES))) ->
    Step_read_before_array_init_data_num (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)])
  | array_init_data_oob1_1 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step_read_before_array_init_data_num (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:7.1-7.88 -/
inductive Step_read : config -> (List instr) -> Prop where
  | block : forall (z : state) (val_lst : (List val)) (v_m : m) (bt : blocktype) (instr_lst : (List instr)) (v_n : n) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (var_0 : instrtype), 
    (fun_blocktype_ z bt var_0) ->
    (var_0 == (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.BLOCK bt instr_lst)])) [(.LABEL_ v_n [] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst))]
  | loop : forall (z : state) (val_lst : (List val)) (v_m : m) (bt : blocktype) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (v_n : n) (var_0 : instrtype), 
    (fun_blocktype_ z bt var_0) ->
    (var_0 == (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.LOOP bt instr_lst)])) [(.LABEL_ v_m [(.LOOP bt instr_lst)] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst))]
  | br_on_cast_succeed : forall (s : store) (f : frame) (v_ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (rt : reftype) (var_0 : reftype), 
    (fun_inst_reftype (f.MODULE) rt_2 var_0) ->
    (Ref_ok s v_ref rt) ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt var_0) ->
    Step_read (.mk_config (.mk_state s f) [(instr_ref v_ref), (.BR_ON_CAST l rt_1 rt_2)]) [(instr_ref v_ref), (.BR l)]
  | br_on_cast_fail : forall (s : store) (f : frame) (v_ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype), 
    (¬(Step_read_before_br_on_cast_fail (.mk_config (.mk_state s f) [(instr_ref v_ref), (.BR_ON_CAST l rt_1 rt_2)]))) ->
    Step_read (.mk_config (.mk_state s f) [(instr_ref v_ref), (.BR_ON_CAST l rt_1 rt_2)]) [(instr_ref v_ref)]
  | br_on_cast_fail_succeed : forall (s : store) (f : frame) (v_ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (rt : reftype) (var_0 : reftype), 
    (fun_inst_reftype (f.MODULE) rt_2 var_0) ->
    (Ref_ok s v_ref rt) ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt var_0) ->
    Step_read (.mk_config (.mk_state s f) [(instr_ref v_ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)]) [(instr_ref v_ref)]
  | br_on_cast_fail_fail : forall (s : store) (f : frame) (v_ref : ref) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype), 
    (¬(Step_read_before_br_on_cast_fail_fail (.mk_config (.mk_state s f) [(instr_ref v_ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)]))) ->
    Step_read (.mk_config (.mk_state s f) [(instr_ref v_ref), (.BR_ON_CAST_FAIL l rt_1 rt_2)]) [(instr_ref v_ref), (.BR l)]
  | call : forall (z : state) (x : idx) (a : addr), 
    (a < (List.length (fun_funcinst z))) ->
    ((proj_uN_0 x) < (List.length ((fun_moduleinst z).FUNCS))) ->
    ((((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!) == a) ->
    Step_read (.mk_config z [(.CALL x)]) [(.REF_FUNC_ADDR a), (.CALL_REF (typeuse_deftype (((fun_funcinst z)[a]!).TYPE)))]
  | call_ref_null : forall (z : state) (ht : heaptype) (yy : typeuse), Step_read (.mk_config z [(.REF_NULL ht), (.CALL_REF yy)]) [.TRAP]
  | call_ref_func : forall (z : state) (val_lst : (List val)) (v_n : n) (a : addr) (yy : typeuse) (v_m : m) (f : frame) (instr_lst : (List instr)) (fi : funcinst) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (x : idx) (t_lst : (List valtype)), 
    (a < (List.length (fun_funcinst z))) ->
    (((fun_funcinst z)[a]!) == fi) ->
    (Expand (fi.TYPE) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    ((fi.CODE) == (.FUNC x (List.map (fun (t : valtype) => (.LOCAL t)) t_lst) instr_lst)) ->
    (f == { LOCALS := ((List.map (fun (v_val : val) => (some v_val)) val_lst) ++ (List.map (fun (t : valtype) => (default_ t)) t_lst)), MODULE := (fi.MODULE) }) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.REF_FUNC_ADDR a), (.CALL_REF yy)])) [(.FRAME_ v_m f [(.LABEL_ v_m [] instr_lst)])]
  | return_call : forall (z : state) (x : idx) (a : addr), 
    (a < (List.length (fun_funcinst z))) ->
    ((proj_uN_0 x) < (List.length ((fun_moduleinst z).FUNCS))) ->
    ((((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!) == a) ->
    Step_read (.mk_config z [(.RETURN_CALL x)]) [(.REF_FUNC_ADDR a), (.RETURN_CALL_REF (typeuse_deftype (((fun_funcinst z)[a]!).TYPE)))]
  | return_call_ref_label : forall (z : state) (k : n) (instr'_lst : (List instr)) (val_lst : (List val)) (yy : typeuse) (instr_lst : (List instr)), Step_read (.mk_config z [(.LABEL_ k instr'_lst ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.RETURN_CALL_REF yy)] ++ instr_lst)))]) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.RETURN_CALL_REF yy)])
  | return_call_ref_handler : forall (z : state) (k : n) (catch_lst : (List «catch»)) (val_lst : (List val)) (yy : typeuse) (instr_lst : (List instr)), Step_read (.mk_config z [(.HANDLER_ k catch_lst ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.RETURN_CALL_REF yy)] ++ instr_lst)))]) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.RETURN_CALL_REF yy)])
  | return_call_ref_frame_null : forall (z : state) (k : n) (f : frame) (val_lst : (List val)) (ht : heaptype) (yy : typeuse) (instr_lst : (List instr)), Step_read (.mk_config z [(.FRAME_ k f ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.REF_NULL ht)] ++ ([(.RETURN_CALL_REF yy)] ++ instr_lst))))]) [.TRAP]
  | return_call_ref_frame_addr : forall (z : state) (k : n) (f : frame) (val'_lst : (List val)) (val_lst : (List val)) (v_n : n) (a : addr) (yy : typeuse) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (v_m : m), 
    (a < (List.length (fun_funcinst z))) ->
    (Expand (((fun_funcinst z)[a]!).TYPE) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Step_read (.mk_config z [(.FRAME_ k f ((List.map (fun (val' : val) => (instr_val val')) val'_lst) ++ ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.REF_FUNC_ADDR a)] ++ ([(.RETURN_CALL_REF yy)] ++ instr_lst)))))]) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.REF_FUNC_ADDR a), (.CALL_REF yy)])
  | throw_ref_null : forall (z : state) (ht : heaptype), Step_read (.mk_config z [(.REF_NULL ht), .THROW_REF]) [.TRAP]
  | throw_ref_instrs : forall (z : state) (val_lst : (List val)) (a : addr) (instr_lst : (List instr)), 
    ((val_lst != []) || (instr_lst != [])) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ ([(.REF_EXN_ADDR a)] ++ ([.THROW_REF] ++ instr_lst)))) [(.REF_EXN_ADDR a), .THROW_REF]
  | throw_ref_label : forall (z : state) (v_n : n) (instr'_lst : (List instr)) (a : addr), Step_read (.mk_config z [(.LABEL_ v_n instr'_lst [(.REF_EXN_ADDR a), .THROW_REF])]) [(.REF_EXN_ADDR a), .THROW_REF]
  | throw_ref_frame : forall (z : state) (v_n : n) (f : frame) (a : addr), Step_read (.mk_config z [(.FRAME_ v_n f [(.REF_EXN_ADDR a), .THROW_REF])]) [(.REF_EXN_ADDR a), .THROW_REF]
  | throw_ref_handler_empty : forall (z : state) (v_n : n) (a : addr), Step_read (.mk_config z [(.HANDLER_ v_n [] [(.REF_EXN_ADDR a), .THROW_REF])]) [(.REF_EXN_ADDR a), .THROW_REF]
  | throw_ref_handler_catch : forall (z : state) (v_n : n) (x : idx) (l : labelidx) (catch'_lst : (List «catch»)) (a : addr) (val_lst : (List val)), 
    (a < (List.length (fun_exninst z))) ->
    ((proj_uN_0 x) < (List.length (fun_tagaddr z))) ->
    ((((fun_exninst z)[a]!).TAG) == ((fun_tagaddr z)[(proj_uN_0 x)]!)) ->
    (val_lst == (((fun_exninst z)[a]!).FIELDS)) ->
    Step_read (.mk_config z [(.HANDLER_ v_n ([(.CATCH x l)] ++ catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.BR l)])
  | throw_ref_handler_catch_ref : forall (z : state) (v_n : n) (x : idx) (l : labelidx) (catch'_lst : (List «catch»)) (a : addr) (val_lst : (List val)), 
    (a < (List.length (fun_exninst z))) ->
    ((proj_uN_0 x) < (List.length (fun_tagaddr z))) ->
    ((((fun_exninst z)[a]!).TAG) == ((fun_tagaddr z)[(proj_uN_0 x)]!)) ->
    (val_lst == (((fun_exninst z)[a]!).FIELDS)) ->
    Step_read (.mk_config z [(.HANDLER_ v_n ([(.CATCH_REF x l)] ++ catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.REF_EXN_ADDR a), (.BR l)])
  | throw_ref_handler_catch_all : forall (z : state) (v_n : n) (l : labelidx) (catch'_lst : (List «catch»)) (a : addr), Step_read (.mk_config z [(.HANDLER_ v_n ([(.CATCH_ALL l)] ++ catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) [(.BR l)]
  | throw_ref_handler_catch_all_ref : forall (z : state) (v_n : n) (l : labelidx) (catch'_lst : (List «catch»)) (a : addr), Step_read (.mk_config z [(.HANDLER_ v_n ([(.CATCH_ALL_REF l)] ++ catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) [(.REF_EXN_ADDR a), (.BR l)]
  | throw_ref_handler_next : forall (z : state) (v_n : n) (v_catch : «catch») (catch'_lst : (List «catch»)) (a : addr) (x : idx) (val_lst : (List val)) (x : idx) (val_lst : (List val)), 
    (a < (List.length (fun_exninst z))) ->
    ((proj_uN_0 x) < (List.length (fun_tagaddr z))) ->
    (((((fun_exninst z)[a]!).TAG) != ((fun_tagaddr z)[(proj_uN_0 x)]!)) || (val_lst != (((fun_exninst z)[a]!).FIELDS))) ->
    Step_read (.mk_config z [(.HANDLER_ v_n ([v_catch] ++ catch'_lst) [(.REF_EXN_ADDR a), .THROW_REF])]) [(.HANDLER_ v_n catch'_lst [(.REF_EXN_ADDR a), .THROW_REF])]
  | try_table : forall (z : state) (val_lst : (List val)) (v_m : m) (bt : blocktype) (catch_lst : (List «catch»)) (instr_lst : (List instr)) (v_n : n) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (var_0 : instrtype), 
    (fun_blocktype_ z bt var_0) ->
    (var_0 == (.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.TRY_TABLE bt (.mk_list catch_lst) instr_lst)])) [(.HANDLER_ v_n catch_lst [(.LABEL_ v_n [] ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ instr_lst))])]
  | local_get : forall (z : state) (x : idx) (v_val : val), 
    ((fun_local z x) == (some v_val)) ->
    Step_read (.mk_config z [(.LOCAL_GET x)]) [(instr_val v_val)]
  | global_get : forall (z : state) (x : idx) (v_val : val), 
    (((fun_global z x).VALUE) == v_val) ->
    Step_read (.mk_config z [(.GLOBAL_GET x)]) [(instr_val v_val)]
  | table_get_oob : forall (z : state) («at» : addrtype) (i : num_) (x : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length ((fun_table z x).REFS))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.TABLE_GET x)]) [.TRAP]
  | table_get_val : forall (z : state) («at» : addrtype) (i : num_) (x : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS))) ->
    ((proj_num__0 i) != none) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.TABLE_GET x)]) [(instr_ref (((fun_table z x).REFS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!))]
  | table_size : forall (z : state) (x : idx) («at» : addrtype) (v_n : n) (lim : limits) (rt : reftype), 
    ((List.length ((fun_table z x).REFS)) == v_n) ->
    (((fun_table z x).TYPE) == (.mk_tabletype «at» lim rt)) ->
    Step_read (.mk_config z [(.TABLE_SIZE x)]) [(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n)))]
  | table_fill_oob : forall (z : state) («at» : addrtype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)]) [.TRAP]
  | table_fill_zero : forall (z : state) («at» : addrtype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)]) []
  | table_fill_succ : forall (z : state) («at» : addrtype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_FILL x)]) [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.TABLE_SET x), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.TABLE_FILL x)]
  | table_copy_oob : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length ((fun_table z x_1).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length ((fun_table z x_2).REFS)))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x_1 x_2)]) [.TRAP]
  | table_copy_zero : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x : idx) (y : idx) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_table z x_1).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_table z x_2).REFS)))) ->
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x y)]) []
  | table_copy_le : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x : idx) (y : idx) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_table z x_1).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_table z x_2).REFS)))) ->
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 i_2)))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x y)]) [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.TABLE_GET y), (.TABLE_SET x), (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i_1))) + 1)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i_2))) + 1)))), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.TABLE_COPY x y)]
  | table_copy_gt : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x : idx) (y : idx) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i_1))) > (proj_uN_0 (Option.get! (proj_num__0 i_2)))) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_table z x_1).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_table z x_2).REFS)))) ->
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.TABLE_COPY x y)]) [(.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.TABLE_GET y), (.TABLE_SET x), (.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.TABLE_COPY x y)]
  | table_init_oob : forall (z : state) («at» : addrtype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_elem z y).REFS)))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) [.TRAP]
  | table_init_zero : forall (z : state) («at» : addrtype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_elem z y).REFS)))) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ .I32 j) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) []
  | table_init_succ : forall (z : state) («at» : addrtype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 j))) < (List.length ((fun_elem z y).REFS))) ->
    ((proj_num__0 j) != none) ->
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_elem z y).REFS)))) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ .I32 j) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) [(.CONST (numtype_addrtype «at») i), (instr_ref (((fun_elem z y).REFS)[(proj_uN_0 (Option.get! (proj_num__0 j)))]!)), (.TABLE_SET x), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.TABLE_INIT x y)]
  | load_num_oob : forall (z : state) («at» : addrtype) (i : num_) (nt : numtype) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((size nt) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.LOAD nt none x ao)]) [.TRAP]
  | load_num_val : forall (z : state) («at» : addrtype) (i : num_) (nt : numtype) (x : idx) (ao : memarg) (c : num_), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ nt c) ->
    ((proj_num__0 i) != none) ->
    ((nbytes_ nt c) == (List.extract ((fun_mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((size nt) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.LOAD nt none x ao)]) [(.CONST nt c)]
  | load_pack_oob : forall (z : state) («at» : addrtype) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_n : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.LOAD (numtype_addrtype v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_n) v_sx))) x ao)]) [.TRAP]
  | load_pack_val : forall (z : state) («at» : addrtype) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (x : idx) (ao : memarg) (c : iN), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((ibytes_ v_n c) == (List.extract ((fun_mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_n : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.LOAD (numtype_addrtype v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_n) v_sx))) x ao)]) [(.CONST (numtype_addrtype v_Inn) (.mk_num__0 v_Inn (extend__ v_n (size (numtype_addrtype v_Inn)) v_sx c)))]
  | vload_oob : forall (z : state) («at» : addrtype) (i : num_) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((vsize .V128) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 none x ao)]) [.TRAP]
  | vload_val : forall (z : state) («at» : addrtype) (i : num_) (x : idx) (ao : memarg) (c : vec_), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((vbytes_ .V128 c) == (List.extract ((fun_mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((vsize .V128) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 none x ao)]) [(.VCONST .V128 c)]
  | vload_pack_oob : forall (z : state) («at» : addrtype) (i : num_) (v_M : M) (v_K : K) (v_sx : sx) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((v_M * v_K) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.SHAPEX_ (.mk_sz v_M) v_K v_sx)) x ao)]) [.TRAP]
  | vload_pack_val : forall (z : state) («at» : addrtype) (i : num_) (v_M : M) (v_K : K) (v_sx : sx) (x : idx) (ao : memarg) (c : vec_) (j_lst : (List iN)) (k_lst : (List Nat)) (v_Jnn : Jnn), 
    (wf_num_ (numtype_addrtype «at») i) ->
    Forall (fun (j : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_K))) (.mk_lane__2 v_Jnn (extend__ v_M (jsizenn v_Jnn) v_sx j)))) j_lst ->
    Forall (fun (j : iN) => ((proj_num__0 i) != none)) j_lst ->
    Forall₂ (fun (j : iN) (k : Nat) => ((ibytes_ v_M j) == (List.extract ((fun_mem z x).BYTES) (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((k * v_M) : Nat) / (8 : Nat)) : Nat)) (((v_M : Nat) / (8 : Nat)) : Nat)))) j_lst k_lst ->
    ((c == (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_K)) (List.map (fun (j : iN) => (.mk_lane__2 v_Jnn (extend__ v_M (jsizenn v_Jnn) v_sx j))) j_lst))) && ((jsizenn v_Jnn) == (v_M * 2))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.SHAPEX_ (.mk_sz v_M) v_K v_sx)) x ao)]) [(.VCONST .V128 c)]
  | vload_splat_oob : forall (z : state) («at» : addrtype) (i : num_) (v_N : N) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_N : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.SPLAT (.mk_sz v_N))) x ao)]) [.TRAP]
  | vload_splat_val : forall (z : state) («at» : addrtype) (i : num_) (v_N : N) (x : idx) (ao : memarg) (c : vec_) (j : iN) (v_Jnn : Jnn) (v_M : M), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_lane__2 v_Jnn (.mk_uN (proj_uN_0 j)))) ->
    ((proj_num__0 i) != none) ->
    ((ibytes_ v_N j) == (List.extract ((fun_mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_N : Nat) / (8 : Nat)) : Nat))) ->
    (v_N == (jsize v_Jnn)) ->
    ((v_M : Nat) == ((128 : Nat) / (v_N : Nat))) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (List.replicate v_M (.mk_lane__2 v_Jnn (.mk_uN (proj_uN_0 j)))))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.SPLAT (.mk_sz v_N))) x ao)]) [(.VCONST .V128 c)]
  | vload_zero_oob : forall (z : state) («at» : addrtype) (i : num_) (v_N : N) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_N : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.ZERO (.mk_sz v_N))) x ao)]) [.TRAP]
  | vload_zero_val : forall (z : state) («at» : addrtype) (i : num_) (v_N : N) (x : idx) (ao : memarg) (c : vec_) (j : iN), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((ibytes_ v_N j) == (List.extract ((fun_mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_N : Nat) / (8 : Nat)) : Nat))) ->
    (c == (extend__ v_N 128 .U j)) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VLOAD .V128 (some (.ZERO (.mk_sz v_N))) x ao)]) [(.VCONST .V128 c)]
  | vload_lane_oob : forall (z : state) («at» : addrtype) (i : num_) (c_1 : vec_) (v_N : N) (x : idx) (ao : memarg) (j : laneidx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_N : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (.mk_sz v_N) x ao j)]) [.TRAP]
  | vload_lane_val : forall (z : state) («at» : addrtype) (i : num_) (c_1 : vec_) (v_N : N) (x : idx) (ao : memarg) (j : laneidx) (c : vec_) (k : iN) (v_Jnn : Jnn) (v_M : M), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_lane__2 v_Jnn (.mk_uN (proj_uN_0 k)))) ->
    ((proj_num__0 i) != none) ->
    ((ibytes_ v_N k) == (List.extract ((fun_mem z x).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_N : Nat) / (8 : Nat)) : Nat))) ->
    (v_N == (jsize v_Jnn)) ->
    ((v_M : Nat) == (((vsize .V128) : Nat) / (v_N : Nat))) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (List.modify (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c_1) (proj_uN_0 j) (fun (_ : lane_) => (.mk_lane__2 v_Jnn (.mk_uN (proj_uN_0 k))))))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (.mk_sz v_N) x ao j)]) [(.VCONST .V128 c)]
  | memory_size : forall (z : state) (x : idx) («at» : addrtype) (v_n : n) (lim : limits), 
    ((v_n * (64 * (Ki ))) == (List.length ((fun_mem z x).BYTES))) ->
    (((fun_mem z x).TYPE) == (.PAGE «at» lim)) ->
    Step_read (.mk_config z [(.MEMORY_SIZE x)]) [(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n)))]
  | memory_fill_oob : forall (z : state) («at» : addrtype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z x).BYTES))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)]) [.TRAP]
  | memory_fill_zero : forall (z : state) («at» : addrtype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z x).BYTES))) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)]) []
  | memory_fill_succ : forall (z : state) («at» : addrtype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z x).BYTES))) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_FILL x)]) [(.CONST (numtype_addrtype «at») i), (instr_val v_val), (.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x (memarg0 )), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (instr_val v_val), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY_FILL x)]
  | memory_copy_oob : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length ((fun_mem z x_1).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length ((fun_mem z x_2).BYTES)))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]) [.TRAP]
  | memory_copy_zero : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_mem z x_1).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_mem z x_2).BYTES)))) ->
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]) []
  | memory_copy_le : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_mem z x_1).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_mem z x_2).BYTES)))) ->
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 i_2)))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]) [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) x_2 (memarg0 )), (.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x_1 (memarg0 )), (.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i_1))) + 1)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i_2))) + 1)))), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY_COPY x_1 x_2)]
  | memory_copy_gt : forall (z : state) (at_1 : addrtype) (i_1 : num_) (at_2 : addrtype) (i_2 : num_) (at' : addrtype) (v_n : n) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i_1))) > (proj_uN_0 (Option.get! (proj_num__0 i_2)))) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length ((fun_mem z x_1).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length ((fun_mem z x_2).BYTES)))) ->
    (wf_num_ (numtype_addrtype at_1) i_1) ->
    (wf_num_ (numtype_addrtype at_2) i_2) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN v_n))), (.MEMORY_COPY x_1 x_2)]) [(.CONST (numtype_addrtype at_1) (.mk_num__0 at_1 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.CONST (numtype_addrtype at_2) (.mk_num__0 at_2 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) x_2 (memarg0 )), (.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x_1 (memarg0 )), (.CONST (numtype_addrtype at_1) i_1), (.CONST (numtype_addrtype at_2) i_2), (.CONST (numtype_addrtype at') (.mk_num__0 at' (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY_COPY x_1 x_2)]
  | memory_init_oob : forall (z : state) («at» : addrtype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z x).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_data z y).BYTES)))) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)]) [.TRAP]
  | memory_init_zero : forall (z : state) («at» : addrtype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z x).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_data z y).BYTES)))) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ .I32 j) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)]) []
  | memory_init_succ : forall (z : state) («at» : addrtype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 j))) < (List.length ((fun_data z y).BYTES))) ->
    ((proj_num__0 j) != none) ->
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z x).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_data z y).BYTES)))) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ .I32 j) ->
    Step_read (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x y)]) [(.CONST (numtype_addrtype «at») i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (proj_byte_0 (((fun_data z y).BYTES)[(proj_uN_0 (Option.get! (proj_num__0 j)))]!))))), (.STORE .I32 (some (.mk_storeop__0 .I32 (.mk_storeop_Inn (.mk_sz 8)))) x (memarg0 )), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY_INIT x y)]
  | ref_null_idx : forall (z : state) (x : idx), Step_read (.mk_config z [(.REF_NULL (._IDX x))]) [(.REF_NULL (heaptype_deftype (fun_type z x)))]
  | ref_func : forall (z : state) (x : idx), 
    ((proj_uN_0 x) < (List.length ((fun_moduleinst z).FUNCS))) ->
    Step_read (.mk_config z [(.REF_FUNC x)]) [(.REF_FUNC_ADDR (((fun_moduleinst z).FUNCS)[(proj_uN_0 x)]!))]
  | ref_test_true : forall (s : store) (f : frame) (v_ref : ref) (rt : reftype) (rt' : reftype) (var_0 : reftype), 
    (fun_inst_reftype (f.MODULE) rt var_0) ->
    (Ref_ok s v_ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' var_0) ->
    Step_read (.mk_config (.mk_state s f) [(instr_ref v_ref), (.REF_TEST rt)]) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))]
  | ref_test_false : forall (s : store) (f : frame) (v_ref : ref) (rt : reftype), 
    (¬(Step_read_before_ref_test_false (.mk_config (.mk_state s f) [(instr_ref v_ref), (.REF_TEST rt)]))) ->
    Step_read (.mk_config (.mk_state s f) [(instr_ref v_ref), (.REF_TEST rt)]) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)))]
  | ref_cast_succeed : forall (s : store) (f : frame) (v_ref : ref) (rt : reftype) (rt' : reftype) (var_0 : reftype), 
    (fun_inst_reftype (f.MODULE) rt var_0) ->
    (Ref_ok s v_ref rt') ->
    (Reftype_sub { TYPES := [], RECS := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], LOCALS := [], LABELS := [], RETURN := none, REFS := [] } rt' var_0) ->
    Step_read (.mk_config (.mk_state s f) [(instr_ref v_ref), (.REF_CAST rt)]) [(instr_ref v_ref)]
  | ref_cast_fail : forall (s : store) (f : frame) (v_ref : ref) (rt : reftype), 
    (¬(Step_read_before_ref_cast_fail (.mk_config (.mk_state s f) [(instr_ref v_ref), (.REF_CAST rt)]))) ->
    Step_read (.mk_config (.mk_state s f) [(instr_ref v_ref), (.REF_CAST rt)]) [.TRAP]
  | struct_new_default : forall (z : state) (x : idx) (val_lst : (List val)) (mut_opt_lst : (List (Option «mut»))) (zt_lst : (List storagetype)), 
    (Expand (fun_type z x) (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => (.mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ->
    ((List.length val_lst) == (List.length zt_lst)) ->
    Forall₂ (fun (v_val : val) (zt : storagetype) => ((default_ (unpack zt)) == (some v_val))) val_lst zt_lst ->
    Step_read (.mk_config z [(.STRUCT_NEW_DEFAULT x)]) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.STRUCT_NEW x)])
  | struct_get_null : forall (z : state) (ht : heaptype) (sx_opt : (Option sx)) (x : idx) (i : u32), Step_read (.mk_config z [(.REF_NULL ht), (.STRUCT_GET sx_opt x i)]) [.TRAP]
  | struct_get_struct : forall (z : state) (a : addr) (sx_opt : (Option sx)) (x : idx) (i : u32) (zt_lst : (List storagetype)) (mut_opt_lst : (List (Option «mut»))), 
    ((proj_uN_0 i) < (List.length zt_lst)) ->
    ((proj_uN_0 i) < (List.length (((fun_structinst z)[a]!).FIELDS))) ->
    (a < (List.length (fun_structinst z))) ->
    (Expand (fun_type z x) (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => (.mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ->
    Step_read (.mk_config z [(.REF_STRUCT_ADDR a), (.STRUCT_GET sx_opt x i)]) [(instr_val (unpackfield_ (zt_lst[(proj_uN_0 i)]!) sx_opt ((((fun_structinst z)[a]!).FIELDS)[(proj_uN_0 i)]!)))]
  | array_new_default : forall (z : state) (v_n : n) (x : idx) (v_val : val) (mut_opt : (Option «mut»)) (zt : storagetype), 
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((default_ (unpack zt)) == (some v_val)) ->
    Step_read (.mk_config z [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_DEFAULT x)]) ((List.replicate v_n (instr_val v_val)) ++ [(.ARRAY_NEW_FIXED x (.mk_uN v_n))])
  | array_new_elem_oob : forall (z : state) (i : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_elem z y).REFS))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_ELEM x y)]) [.TRAP]
  | array_new_elem_alloc : forall (z : state) (i : num_) (v_n : n) (x : idx) (y : idx) (ref_lst : (List ref)), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (ref_lst == (List.extract ((fun_elem z y).REFS) (proj_uN_0 (Option.get! (proj_num__0 i))) v_n)) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_ELEM x y)]) ((List.map (fun (v_ref : ref) => (instr_ref v_ref)) ref_lst) ++ [(.ARRAY_NEW_FIXED x (.mk_uN v_n))])
  | array_new_data_oob : forall (z : state) (i : num_) (v_n : n) (x : idx) (y : idx) (mut_opt : (Option «mut»)) (zt : storagetype), 
    (wf_num_ .I32 i) ->
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + ((((v_n * (zsize zt)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_data z y).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_DATA x y)]) [.TRAP]
  | array_new_data_num : forall (z : state) (i : num_) (v_n : n) (x : idx) (y : idx) (zt : storagetype) (c_lst : (List lit_)) (mut_opt : (Option «mut»)) (var_0_lst : (List lit_)), 
    Forall (fun (var_0 : lit_) => ((cunpack zt) != none)) var_0_lst ->
    Forall₂ (fun (var_0 : lit_) (c : lit_) => (fun_cunpacknum_ zt c var_0)) var_0_lst c_lst ->
    (wf_num_ .I32 i) ->
    Forall (fun (c : lit_) => (wf_lit_ zt c)) c_lst ->
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((proj_num__0 i) != none) ->
    ((concatn_ byte (List.map (fun (c : lit_) => (zbytes_ zt c)) c_lst) ((((zsize zt) : Nat) / (8 : Nat)) : Nat)) == (List.extract ((fun_data z y).BYTES) (proj_uN_0 (Option.get! (proj_num__0 i))) ((((v_n * (zsize zt)) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_NEW_DATA x y)]) ((List.map (fun (var_0 : lit_) => (const (Option.get! (cunpack zt)) var_0)) var_0_lst) ++ [(.ARRAY_NEW_FIXED x (.mk_uN v_n))])
  | array_get_null : forall (z : state) (ht : heaptype) (i : num_) (sx_opt : (Option sx)) (x : idx), 
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.REF_NULL ht), (.CONST .I32 i), (.ARRAY_GET sx_opt x)]) [.TRAP]
  | array_get_oob : forall (z : state) (a : addr) (i : num_) (sx_opt : (Option sx)) (x : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY_GET sx_opt x)]) [.TRAP]
  | array_get_array : forall (z : state) (a : addr) (i : num_) (sx_opt : (Option sx)) (x : idx) (zt : storagetype) (mut_opt : (Option «mut»)), 
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    (a < (List.length (fun_arrayinst z))) ->
    ((proj_num__0 i) != none) ->
    (wf_num_ .I32 i) ->
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.ARRAY_GET sx_opt x)]) [(instr_val (unpackfield_ zt sx_opt ((((fun_arrayinst z)[a]!).FIELDS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!)))]
  | array_len_null : forall (z : state) (ht : heaptype), Step_read (.mk_config z [(.REF_NULL ht), .ARRAY_LEN]) [.TRAP]
  | array_len_array : forall (z : state) (a : addr), 
    (a < (List.length (fun_arrayinst z))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), .ARRAY_LEN]) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN (List.length (((fun_arrayinst z)[a]!).FIELDS)))))]
  | array_fill_null : forall (z : state) (ht : heaptype) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.REF_NULL ht), (.CONST .I32 i), (instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)]) [.TRAP]
  | array_fill_oob : forall (z : state) (a : addr) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)]) [.TRAP]
  | array_fill_zero : forall (z : state) (a : addr) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    (wf_num_ .I32 i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)]) []
  | array_fill_succ : forall (z : state) (a : addr) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_FILL x)]) [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.ARRAY_SET x), (.REF_ARRAY_ADDR a), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (instr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY_FILL x)]
  | array_copy_null1 : forall (z : state) (ht_1 : heaptype) (i_1 : num_) (v_ref : ref) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    Step_read (.mk_config z [(.REF_NULL ht_1), (.CONST .I32 i_1), (instr_ref v_ref), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) [.TRAP]
  | array_copy_null2 : forall (z : state) (v_ref : ref) (i_1 : num_) (ht_2 : heaptype) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    Step_read (.mk_config z [(instr_ref v_ref), (.CONST .I32 i_1), (.REF_NULL ht_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) [.TRAP]
  | array_copy_oob1 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    ((proj_num__0 i_1) != none) ->
    (a_1 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) > (List.length (((fun_arrayinst z)[a_1]!).FIELDS))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) [.TRAP]
  | array_copy_oob2 : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    ((proj_num__0 i_2) != none) ->
    (a_2 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) > (List.length (((fun_arrayinst z)[a_2]!).FIELDS))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) [.TRAP]
  | array_copy_zero : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx), 
    ((proj_num__0 i_2) != none) ->
    (a_2 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length (((fun_arrayinst z)[a_2]!).FIELDS))) ->
    ((proj_num__0 i_1) != none) ->
    (a_1 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length (((fun_arrayinst z)[a_1]!).FIELDS))) ->
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) []
  | array_copy_le : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx) (sx_opt : (Option sx)) (mut_opt : (Option «mut»)) (zt_2 : storagetype), 
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    (v_n != 0) ->
    (a_2 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) <= (List.length (((fun_arrayinst z)[a_2]!).FIELDS))) ->
    (a_1 < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) <= (List.length (((fun_arrayinst z)[a_1]!).FIELDS))) ->
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    (Expand (fun_type z x_2) (.ARRAY (.mk_fieldtype mut_opt zt_2))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i_1))) <= (proj_uN_0 (Option.get! (proj_num__0 i_2)))) && (sx_opt == (fun_sx zt_2))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.ARRAY_GET sx_opt x_2), (.ARRAY_SET x_1), (.REF_ARRAY_ADDR a_1), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i_1))) + 1)))), (.REF_ARRAY_ADDR a_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i_2))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY_COPY x_1 x_2)]
  | array_copy_gt : forall (z : state) (a_1 : addr) (i_1 : num_) (a_2 : addr) (i_2 : num_) (v_n : n) (x_1 : idx) (x_2 : idx) (sx_opt : (Option sx)) (mut_opt : (Option «mut»)) (zt_2 : storagetype), 
    ((proj_num__0 i_1) != none) ->
    ((proj_num__0 i_2) != none) ->
    (wf_num_ .I32 i_1) ->
    (wf_num_ .I32 i_2) ->
    (¬(Step_read_before_array_copy_gt (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]))) ->
    (Expand (fun_type z x_2) (.ARRAY (.mk_fieldtype mut_opt zt_2))) ->
    (sx_opt == (fun_sx zt_2)) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_COPY x_1 x_2)]) [(.REF_ARRAY_ADDR a_1), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 i_1))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.REF_ARRAY_ADDR a_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 i_2))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.ARRAY_GET sx_opt x_2), (.ARRAY_SET x_1), (.REF_ARRAY_ADDR a_1), (.CONST .I32 i_1), (.REF_ARRAY_ADDR a_2), (.CONST .I32 i_2), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY_COPY x_1 x_2)]
  | array_init_elem_null : forall (z : state) (ht : heaptype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    Step_read (.mk_config z [(.REF_NULL ht), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)]) [.TRAP]
  | array_init_elem_oob1 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)]) [.TRAP]
  | array_init_elem_oob2 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_elem z y).REFS))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)]) [.TRAP]
  | array_init_elem_zero : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_num__0 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_elem z y).REFS))) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)]) []
  | array_init_elem_succ : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx) (v_ref : ref), 
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    (v_n != 0) ->
    (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_elem z y).REFS))) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    ((proj_uN_0 (Option.get! (proj_num__0 j))) < (List.length ((fun_elem z y).REFS))) ->
    (v_ref == (((fun_elem z y).REFS)[(proj_uN_0 (Option.get! (proj_num__0 j)))]!)) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_ELEM x y)]) [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_ref v_ref), (.ARRAY_SET x), (.REF_ARRAY_ADDR a), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY_INIT_ELEM x y)]
  | array_init_data_null : forall (z : state) (ht : heaptype) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    Step_read (.mk_config z [(.REF_NULL ht), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]) [.TRAP]
  | array_init_data_oob1 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]) [.TRAP]
  | array_init_data_oob2 : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx) (mut_opt : (Option «mut»)) (zt : storagetype), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((proj_num__0 j) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 j))) + ((((v_n * (zsize zt)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_data z y).BYTES))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]) [.TRAP]
  | array_init_data_zero : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    (¬(Step_read_before_array_init_data_zero (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]))) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]) []
  | array_init_data_num : forall (z : state) (a : addr) (i : num_) (j : num_) (v_n : n) (x : idx) (y : idx) (zt : storagetype) (c : lit_) (mut_opt : (Option «mut»)) (var_0 : lit_), 
    ((cunpack zt) != none) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    (fun_cunpacknum_ zt c var_0) ->
    (wf_num_ .I32 i) ->
    (wf_num_ .I32 j) ->
    (wf_lit_ zt c) ->
    (¬(Step_read_before_array_init_data_num (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]))) ->
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((zbytes_ zt c) == (List.extract ((fun_data z y).BYTES) (proj_uN_0 (Option.get! (proj_num__0 j))) ((((zsize zt) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.ARRAY_INIT_DATA x y)]) [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (const (Option.get! (cunpack zt)) var_0), (.ARRAY_SET x), (.REF_ARRAY_ADDR a), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + ((((zsize zt) : Nat) / (8 : Nat)) : Nat))))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.ARRAY_INIT_DATA x y)]

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:5.1-5.88 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:5.1-5.88 -/
inductive Step : config -> config -> Prop where
  | pure : forall (z : state) (instr_lst : (List instr)) (instr'_lst : (List instr)), 
    (Step_pure instr_lst instr'_lst) ->
    Step (.mk_config z instr_lst) (.mk_config z instr'_lst)
  | read : forall (z : state) (instr_lst : (List instr)) (instr'_lst : (List instr)), 
    (Step_read (.mk_config z instr_lst) instr'_lst) ->
    Step (.mk_config z instr_lst) (.mk_config z instr'_lst)
  | ctxt_instrs : forall (z : state) (val_lst : (List val)) (instr_lst : (List instr)) (instr_1_lst : (List instr)) (z' : state) (instr'_lst : (List instr)), 
    (Step (.mk_config z instr_lst) (.mk_config z' instr'_lst)) ->
    ((val_lst != []) || (instr_1_lst != [])) ->
    Step (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ (instr_lst ++ instr_1_lst))) (.mk_config z' ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ (instr'_lst ++ instr_1_lst)))
  | ctxt_label : forall (z : state) (v_n : n) (instr_0_lst : (List instr)) (instr_lst : (List instr)) (z' : state) (instr'_lst : (List instr)), 
    (Step (.mk_config z instr_lst) (.mk_config z' instr'_lst)) ->
    Step (.mk_config z [(.LABEL_ v_n instr_0_lst instr_lst)]) (.mk_config z' [(.LABEL_ v_n instr_0_lst instr'_lst)])
  | ctxt_frame : forall (s : store) (f : frame) (v_n : n) (f' : frame) (instr_lst : (List instr)) (s' : store) (f'' : frame) (instr'_lst : (List instr)), 
    (Step (.mk_config (.mk_state s f') instr_lst) (.mk_config (.mk_state s' f'') instr'_lst)) ->
    Step (.mk_config (.mk_state s f) [(.FRAME_ v_n f' instr_lst)]) (.mk_config (.mk_state s' f) [(.FRAME_ v_n f'' instr'_lst)])
  | throw : forall (z : state) (val_lst : (List val)) (v_n : n) (x : idx) (exn : exninst) (a : addr) (t_lst : (List valtype)), 
    (Expand (as_deftype ((fun_tag z x).TYPE)) (.FUNC (.mk_list t_lst) (.mk_list []))) ->
    (a == (List.length (fun_exninst z))) ->
    ((proj_uN_0 x) < (List.length (fun_tagaddr z))) ->
    (exn == { TAG := ((fun_tagaddr z)[(proj_uN_0 x)]!), FIELDS := val_lst }) ->
    Step (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.THROW x)])) (.mk_config (add_exninst z [exn]) [(.REF_EXN_ADDR a), .THROW_REF])
  | local_set : forall (z : state) (v_val : val) (x : idx), Step (.mk_config z [(instr_val v_val), (.LOCAL_SET x)]) (.mk_config (with_local z x v_val) [])
  | global_set : forall (z : state) (v_val : val) (x : idx), Step (.mk_config z [(instr_val v_val), (.GLOBAL_SET x)]) (.mk_config (with_global z x v_val) [])
  | table_set_oob : forall (z : state) («at» : addrtype) (i : num_) (v_ref : ref) (x : idx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length ((fun_table z x).REFS))) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_ref v_ref), (.TABLE_SET x)]) (.mk_config z [.TRAP])
  | table_set_val : forall (z : state) («at» : addrtype) (i : num_) (v_ref : ref) (x : idx), 
    ((proj_num__0 i) != none) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS))) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (instr_ref v_ref), (.TABLE_SET x)]) (.mk_config (with_table z x (proj_uN_0 (Option.get! (proj_num__0 i))) v_ref) [])
  | table_grow_succeed : forall (z : state) (v_ref : ref) («at» : addrtype) (v_n : n) (x : idx) (ti : tableinst) (var_0 : (Option tableinst)), 
    (fun_growtable (fun_table z x) v_n v_ref var_0) ->
    (var_0 != none) ->
    (ti == (Option.get! var_0)) ->
    Step (.mk_config z [(instr_ref v_ref), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_GROW x)]) (.mk_config (with_tableinst z x ti) [(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN (List.length ((fun_table z x).REFS)))))])
  | table_grow_fail : forall (z : state) (v_ref : ref) («at» : addrtype) (v_n : n) (x : idx) (var_0 : Nat), 
    (fun_inv_signed_ (size (numtype_addrtype «at»)) (0 - (1 : Nat)) var_0) ->
    Step (.mk_config z [(instr_ref v_ref), (.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.TABLE_GROW x)]) (.mk_config z [(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN var_0)))])
  | elem_drop : forall (z : state) (x : idx), Step (.mk_config z [(.ELEM_DROP x)]) (.mk_config (with_elem z x []) [])
  | store_num_oob : forall (z : state) («at» : addrtype) (i : num_) (nt : numtype) (c : num_) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ nt c) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((size nt) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST nt c), (.STORE nt none x ao)]) (.mk_config z [.TRAP])
  | store_num_val : forall (z : state) («at» : addrtype) (i : num_) (nt : numtype) (c : num_) (x : idx) (ao : memarg) (b_lst : (List byte)), 
    ((proj_num__0 i) != none) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ nt c) ->
    (b_lst == (nbytes_ nt c)) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST nt c), (.STORE nt none x ao)]) (.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((size nt) : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | store_pack_oob : forall (z : state) («at» : addrtype) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ (numtype_addrtype v_Inn) c) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_n : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST (numtype_addrtype v_Inn) c), (.STORE (numtype_addrtype v_Inn) (some (.mk_storeop__0 v_Inn (.mk_storeop_Inn (.mk_sz v_n)))) x ao)]) (.mk_config z [.TRAP])
  | store_pack_val : forall (z : state) («at» : addrtype) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (x : idx) (ao : memarg) (b_lst : (List byte)), 
    ((proj_num__0 i) != none) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (wf_num_ (numtype_addrtype v_Inn) c) ->
    ((proj_num__0 c) != none) ->
    (b_lst == (ibytes_ v_n (wrap__ (size (numtype_addrtype v_Inn)) v_n (Option.get! (proj_num__0 c))))) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (.CONST (numtype_addrtype v_Inn) c), (.STORE (numtype_addrtype v_Inn) (some (.mk_storeop__0 v_Inn (.mk_storeop_Inn (.mk_sz v_n)))) x ao)]) (.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_n : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | vstore_oob : forall (z : state) («at» : addrtype) (i : num_) (c : vec_) (x : idx) (ao : memarg), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((vsize .V128) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z x).BYTES))) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c), (.VSTORE .V128 x ao)]) (.mk_config z [.TRAP])
  | vstore_val : forall (z : state) («at» : addrtype) (i : num_) (c : vec_) (x : idx) (ao : memarg) (b_lst : (List byte)), 
    ((proj_num__0 i) != none) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (b_lst == (vbytes_ .V128 c)) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c), (.VSTORE .V128 x ao)]) (.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((vsize .V128) : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | vstore_lane_oob : forall (z : state) («at» : addrtype) (i : num_) (c : vec_) (v_N : N) (x : idx) (ao : memarg) (j : laneidx), 
    (wf_num_ (numtype_addrtype «at») i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + v_N) > (List.length ((fun_mem z x).BYTES))) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (.mk_sz v_N) x ao j)]) (.mk_config z [.TRAP])
  | vstore_lane_val : forall (z : state) («at» : addrtype) (i : num_) (c : vec_) (v_N : N) (x : idx) (ao : memarg) (j : laneidx) (b_lst : (List byte)) (v_Jnn : Jnn) (v_M : M), 
    ((proj_num__0 i) != none) ->
    (wf_num_ (numtype_addrtype «at») i) ->
    (v_N == (jsize v_Jnn)) ->
    ((v_M : Nat) == ((128 : Nat) / (v_N : Nat))) ->
    ((proj_lane__2 ((lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c)[(proj_uN_0 j)]!)) != none) ->
    ((proj_uN_0 j) < (List.length (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c))) ->
    (b_lst == (ibytes_ v_N (.mk_uN (proj_uN_0 (Option.get! (proj_lane__2 ((lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c)[(proj_uN_0 j)]!))))))) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (.mk_sz v_N) x ao j)]) (.mk_config (with_mem z x ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_N : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | memory_grow_succeed : forall (z : state) («at» : addrtype) (v_n : n) (x : idx) (mi : meminst) (var_0 : (Option meminst)), 
    (fun_growmem (fun_mem z x) v_n var_0) ->
    (var_0 != none) ->
    (mi == (Option.get! var_0)) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_GROW x)]) (.mk_config (with_meminst z x mi) [(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN ((((List.length ((fun_mem z x).BYTES)) : Nat) / ((64 * (Ki )) : Nat)) : Nat))))])
  | memory_grow_fail : forall (z : state) («at» : addrtype) (v_n : n) (x : idx) (var_0 : Nat), 
    (fun_inv_signed_ (size (numtype_addrtype «at»)) (0 - (1 : Nat)) var_0) ->
    Step (.mk_config z [(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN v_n))), (.MEMORY_GROW x)]) (.mk_config z [(.CONST (numtype_addrtype «at») (.mk_num__0 «at» (.mk_uN var_0)))])
  | data_drop : forall (z : state) (x : idx), Step (.mk_config z [(.DATA_DROP x)]) (.mk_config (with_data z x []) [])
  | struct_new : forall (z : state) (val_lst : (List val)) (v_n : n) (x : idx) (si : structinst) (a : addr) (mut_opt_lst : (List (Option «mut»))) (zt_lst : (List storagetype)), 
    (Expand (fun_type z x) (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => (.mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ->
    (a == (List.length (fun_structinst z))) ->
    (si == { TYPE := (fun_type z x), FIELDS := (List.zipWith (fun (v_val : val) (zt : storagetype) => (packfield_ zt v_val)) val_lst zt_lst) }) ->
    Step (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.STRUCT_NEW x)])) (.mk_config (add_structinst z [si]) [(.REF_STRUCT_ADDR a)])
  | struct_set_null : forall (z : state) (ht : heaptype) (v_val : val) (x : idx) (i : u32), Step (.mk_config z [(.REF_NULL ht), (instr_val v_val), (.STRUCT_SET x i)]) (.mk_config z [.TRAP])
  | struct_set_struct : forall (z : state) (a : addr) (v_val : val) (x : idx) (i : u32) (zt_lst : (List storagetype)) (mut_opt_lst : (List (Option «mut»))), 
    ((proj_uN_0 i) < (List.length zt_lst)) ->
    (Expand (fun_type z x) (.STRUCT (.mk_list (List.zipWith (fun (mut_opt : (Option «mut»)) (zt : storagetype) => (.mk_fieldtype mut_opt zt)) mut_opt_lst zt_lst)))) ->
    Step (.mk_config z [(.REF_STRUCT_ADDR a), (instr_val v_val), (.STRUCT_SET x i)]) (.mk_config (with_struct z a (proj_uN_0 i) (packfield_ (zt_lst[(proj_uN_0 i)]!) v_val)) [])
  | array_new_fixed : forall (z : state) (val_lst : (List val)) (v_n : n) (x : idx) (ai : arrayinst) (a : addr) (mut_opt : (Option «mut»)) (zt : storagetype), 
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    ((a == (List.length (fun_arrayinst z))) && (ai == { TYPE := (fun_type z x), FIELDS := (List.map (fun (v_val : val) => (packfield_ zt v_val)) val_lst) })) ->
    Step (.mk_config z ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.ARRAY_NEW_FIXED x (.mk_uN v_n))])) (.mk_config (add_arrayinst z [ai]) [(.REF_ARRAY_ADDR a)])
  | array_set_null : forall (z : state) (ht : heaptype) (i : num_) (v_val : val) (x : idx), 
    (wf_num_ .I32 i) ->
    Step (.mk_config z [(.REF_NULL ht), (.CONST .I32 i), (instr_val v_val), (.ARRAY_SET x)]) (.mk_config z [.TRAP])
  | array_set_oob : forall (z : state) (a : addr) (i : num_) (v_val : val) (x : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_arrayinst z))) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length (((fun_arrayinst z)[a]!).FIELDS))) ->
    Step (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.ARRAY_SET x)]) (.mk_config z [.TRAP])
  | array_set_array : forall (z : state) (a : addr) (i : num_) (v_val : val) (x : idx) (zt : storagetype) (mut_opt : (Option «mut»)), 
    ((proj_num__0 i) != none) ->
    (wf_num_ .I32 i) ->
    (Expand (fun_type z x) (.ARRAY (.mk_fieldtype mut_opt zt))) ->
    Step (.mk_config z [(.REF_ARRAY_ADDR a), (.CONST .I32 i), (instr_val v_val), (.ARRAY_SET x)]) (.mk_config (with_array z a (proj_uN_0 (Option.get! (proj_num__0 i))) (packfield_ zt v_val)) [])

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:8.1-8.92 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:8.1-8.92 -/
inductive Steps : config -> config -> Prop where
  | refl : forall (z : state) (instr_lst : (List instr)), Steps (.mk_config z instr_lst) (.mk_config z instr_lst)
  | trans : forall (z : state) (instr_lst : (List instr)) (z'' : state) (instr''_lst : (List instr)) (z' : state) (instr'_lst : (List instr)), 
    (Step (.mk_config z instr_lst) (.mk_config z' instr'_lst)) ->
    (Steps (.mk_config z' instr'_lst) (.mk_config z'' instr''_lst)) ->
    Steps (.mk_config z instr_lst) (.mk_config z'' instr''_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.3-execution.instructions.spectec:1104.1-1104.108 -/
inductive Eval_expr : state -> expr -> state -> (List val) -> Prop where
  | mk_Eval_expr : forall (z : state) (instr_lst : (List instr)) (z' : state) (val_lst : (List val)), 
    (Steps (.mk_config z instr_lst) (.mk_config z' (List.map (fun (v_val : val) => (instr_val v_val)) val_lst))) ->
    Eval_expr z instr_lst z' val_lst

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:7.1-7.63 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:7.6-7.17 -/
inductive fun_alloctypes : (List type) -> (List deftype) -> Prop where
  | fun_alloctypes_case_0 : fun_alloctypes [] []
  | fun_alloctypes_case_1 : forall (type'_lst : (List type)) (v_type : type) (deftype'_lst : (List deftype)) (deftype_lst : (List deftype)) (v_rectype : rectype) (x : uN) (var_2 : (List deftype)) (var_1 : (List deftype)) (var_0 : (List deftype)), 
    (fun_rolldt x v_rectype var_2) ->
    (fun_subst_all_deftypes var_2 (List.map (fun (deftype' : deftype) => (typeuse_deftype deftype')) deftype'_lst) var_1) ->
    (fun_alloctypes type'_lst var_0) ->
    (deftype'_lst == var_0) ->
    (v_type == (.TYPE v_rectype)) ->
    (deftype_lst == var_1) ->
    ((proj_uN_0 x) == (List.length deftype'_lst)) ->
    fun_alloctypes (type'_lst ++ [v_type]) (deftype'_lst ++ deftype_lst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:15.6-15.15 -/
inductive fun_alloctag : store -> tagtype -> store × tagaddr -> Prop where
  | fun_alloctag_case_0 : forall (s : store) (v_tagtype : typeuse) (v_taginst : taginst), 
    (v_taginst == { TYPE := v_tagtype }) ->
    fun_alloctag s v_tagtype ((s ++ { TAGS := [v_taginst], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], STRUCTS := [], ARRAYS := [], EXNS := [] }), (List.length (s.TAGS)))

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:20.1-20.102 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:20.6-20.16 -/
inductive fun_alloctags : store -> (List tagtype) -> store × (List tagaddr) -> Prop where
  | fun_alloctags_case_0 : forall (s : store), fun_alloctags s [] (s, [])
  | fun_alloctags_case_1 : forall (s : store) (v_tagtype : typeuse) (tagtype'_lst : (List tagtype)) (s_2 : store) (ja : Nat) (ja'_lst : (List tagaddr)) (s_1 : store) (var_1 : store × (List tagaddr)) (var_0 : store × tagaddr), 
    (fun_alloctags s_1 tagtype'_lst var_1) ->
    (fun_alloctag s v_tagtype var_0) ->
    ((s_1, ja) == var_0) ->
    ((s_2, ja'_lst) == var_1) ->
    fun_alloctags s ([v_tagtype] ++ tagtype'_lst) (s_2, ([ja] ++ ja'_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:26.6-26.18 -/
inductive fun_allocglobal : store -> globaltype -> val -> store × globaladdr -> Prop where
  | fun_allocglobal_case_0 : forall (s : store) (v_globaltype : globaltype) (v_val : val) (v_globalinst : globalinst), 
    (v_globalinst == { TYPE := v_globaltype, VALUE := v_val }) ->
    fun_allocglobal s v_globaltype v_val ((s ++ { TAGS := [], GLOBALS := [v_globalinst], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], STRUCTS := [], ARRAYS := [], EXNS := [] }), (List.length (s.GLOBALS)))

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:31.1-31.122 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:31.6-31.19 -/
inductive fun_allocglobals : store -> (List globaltype) -> (List val) -> store × (List globaladdr) -> Prop where
  | fun_allocglobals_case_0 : forall (s : store), fun_allocglobals s [] [] (s, [])
  | fun_allocglobals_case_1 : forall (s : store) (v_globaltype : globaltype) (globaltype'_lst : (List globaltype)) (v_val : val) (val'_lst : (List val)) (s_2 : store) (ga : Nat) (ga'_lst : (List globaladdr)) (s_1 : store) (var_1 : store × (List globaladdr)) (var_0 : store × globaladdr), 
    (fun_allocglobals s_1 globaltype'_lst val'_lst var_1) ->
    (fun_allocglobal s v_globaltype v_val var_0) ->
    ((s_1, ga) == var_0) ->
    ((s_2, ga'_lst) == var_1) ->
    fun_allocglobals s ([v_globaltype] ++ globaltype'_lst) ([v_val] ++ val'_lst) (s_2, ([ga] ++ ga'_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:37.6-37.15 -/
inductive fun_allocmem : store -> memtype -> store × memaddr -> Prop where
  | fun_allocmem_case_0 : forall (s : store) («at» : addrtype) (i : uN) (j_opt : (Option u64)) (v_meminst : meminst), 
    (v_meminst == { TYPE := (.PAGE «at» (.mk_limits i j_opt)), BYTES := (List.replicate ((proj_uN_0 i) * (64 * (Ki ))) (.mk_byte 0)) }) ->
    fun_allocmem s (.PAGE «at» (.mk_limits i j_opt)) ((s ++ { TAGS := [], GLOBALS := [], MEMS := [v_meminst], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], STRUCTS := [], ARRAYS := [], EXNS := [] }), (List.length (s.MEMS)))

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:42.1-42.102 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:42.6-42.16 -/
inductive fun_allocmems : store -> (List memtype) -> store × (List memaddr) -> Prop where
  | fun_allocmems_case_0 : forall (s : store), fun_allocmems s [] (s, [])
  | fun_allocmems_case_1 : forall (s : store) (v_memtype : memtype) (memtype'_lst : (List memtype)) (s_2 : store) (ma : Nat) (ma'_lst : (List memaddr)) (s_1 : store) (var_1 : store × (List memaddr)) (var_0 : store × memaddr), 
    (fun_allocmems s_1 memtype'_lst var_1) ->
    (fun_allocmem s v_memtype var_0) ->
    ((s_1, ma) == var_0) ->
    ((s_2, ma'_lst) == var_1) ->
    fun_allocmems s ([v_memtype] ++ memtype'_lst) (s_2, ([ma] ++ ma'_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:48.6-48.17 -/
inductive fun_alloctable : store -> tabletype -> ref -> store × tableaddr -> Prop where
  | fun_alloctable_case_0 : forall (s : store) («at» : addrtype) (i : uN) (j_opt : (Option u64)) (rt : reftype) (v_ref : ref) (v_tableinst : tableinst), 
    (v_tableinst == { TYPE := (.mk_tabletype «at» (.mk_limits i j_opt) rt), REFS := (List.replicate (proj_uN_0 i) v_ref) }) ->
    fun_alloctable s (.mk_tabletype «at» (.mk_limits i j_opt) rt) v_ref ((s ++ { TAGS := [], GLOBALS := [], MEMS := [], TABLES := [v_tableinst], FUNCS := [], DATAS := [], ELEMS := [], STRUCTS := [], ARRAYS := [], EXNS := [] }), (List.length (s.TABLES)))

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:53.1-53.118 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:53.6-53.18 -/
inductive fun_alloctables : store -> (List tabletype) -> (List ref) -> store × (List tableaddr) -> Prop where
  | fun_alloctables_case_0 : forall (s : store), fun_alloctables s [] [] (s, [])
  | fun_alloctables_case_1 : forall (s : store) (v_tabletype : tabletype) (tabletype'_lst : (List tabletype)) (v_ref : ref) (ref'_lst : (List ref)) (s_2 : store) (ta : Nat) (ta'_lst : (List tableaddr)) (s_1 : store) (var_1 : store × (List tableaddr)) (var_0 : store × tableaddr), 
    (fun_alloctables s_1 tabletype'_lst ref'_lst var_1) ->
    (fun_alloctable s v_tabletype v_ref var_0) ->
    ((s_1, ta) == var_0) ->
    ((s_2, ta'_lst) == var_1) ->
    fun_alloctables s ([v_tabletype] ++ tabletype'_lst) ([v_ref] ++ ref'_lst) (s_2, ([ta] ++ ta'_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:59.6-59.16 -/
inductive fun_allocfunc : store -> deftype -> funccode -> moduleinst -> store × funcaddr -> Prop where
  | fun_allocfunc_case_0 : forall (s : store) (v_deftype : deftype) (v_funccode : funccode) (v_moduleinst : moduleinst) (v_funcinst : funcinst), 
    (v_funcinst == { TYPE := v_deftype, MODULE := v_moduleinst, CODE := v_funccode }) ->
    fun_allocfunc s v_deftype v_funccode v_moduleinst ((s ++ { TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [v_funcinst], DATAS := [], ELEMS := [], STRUCTS := [], ARRAYS := [], EXNS := [] }), (List.length (s.FUNCS)))

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:64.1-64.133 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:64.6-64.17 -/
inductive fun_allocfuncs : store -> (List deftype) -> (List funccode) -> (List moduleinst) -> store × (List funcaddr) -> Prop where
  | fun_allocfuncs_case_0 : forall (s : store), fun_allocfuncs s [] [] [] (s, [])
  | fun_allocfuncs_case_1 : forall (s : store) (dt : deftype) (dt'_lst : (List deftype)) (v_funccode : funccode) (funccode'_lst : (List funccode)) (v_moduleinst : moduleinst) (moduleinst'_lst : (List moduleinst)) (s_2 : store) (fa : Nat) (fa'_lst : (List funcaddr)) (s_1 : store) (var_1 : store × (List funcaddr)) (var_0 : store × funcaddr), 
    (fun_allocfuncs s_1 dt'_lst funccode'_lst moduleinst'_lst var_1) ->
    (fun_allocfunc s dt v_funccode v_moduleinst var_0) ->
    ((s_1, fa) == var_0) ->
    ((s_2, fa'_lst) == var_1) ->
    fun_allocfuncs s ([dt] ++ dt'_lst) ([v_funccode] ++ funccode'_lst) ([v_moduleinst] ++ moduleinst'_lst) (s_2, ([fa] ++ fa'_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:70.6-70.16 -/
inductive fun_allocdata : store -> datatype -> (List byte) -> store × dataaddr -> Prop where
  | fun_allocdata_case_0 : forall (s : store) (byte_lst : (List byte)) (v_datainst : datainst), 
    (v_datainst == { BYTES := byte_lst }) ->
    fun_allocdata s .OK byte_lst ((s ++ { TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [v_datainst], ELEMS := [], STRUCTS := [], ARRAYS := [], EXNS := [] }), (List.length (s.DATAS)))

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:75.1-75.118 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:75.6-75.17 -/
inductive fun_allocdatas : store -> (List datatype) -> (List (List byte)) -> store × (List dataaddr) -> Prop where
  | fun_allocdatas_case_0 : forall (s : store), fun_allocdatas s [] [] (s, [])
  | fun_allocdatas_case_1 : forall (s : store) (ok : datatype) (ok'_lst : (List datatype)) (b_lst : (List byte)) (b'_lst_lst : (List (List byte))) (s_2 : store) (da : Nat) (da'_lst : (List dataaddr)) (s_1 : store) (var_1 : store × (List dataaddr)) (var_0 : store × dataaddr), 
    (fun_allocdatas s_1 ok'_lst b'_lst_lst var_1) ->
    (fun_allocdata s ok b_lst var_0) ->
    ((s_1, da) == var_0) ->
    ((s_2, da'_lst) == var_1) ->
    fun_allocdatas s ([ok] ++ ok'_lst) ([b_lst] ++ b'_lst_lst) (s_2, ([da] ++ da'_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:81.6-81.16 -/
inductive fun_allocelem : store -> elemtype -> (List ref) -> store × elemaddr -> Prop where
  | fun_allocelem_case_0 : forall (s : store) (v_elemtype : reftype) (ref_lst : (List ref)) (v_eleminst : eleminst), 
    (v_eleminst == { TYPE := v_elemtype, REFS := ref_lst }) ->
    fun_allocelem s v_elemtype ref_lst ((s ++ { TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [v_eleminst], STRUCTS := [], ARRAYS := [], EXNS := [] }), (List.length (s.ELEMS)))

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:86.1-86.117 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:86.6-86.17 -/
inductive fun_allocelems : store -> (List elemtype) -> (List (List ref)) -> store × (List elemaddr) -> Prop where
  | fun_allocelems_case_0 : forall (s : store), fun_allocelems s [] [] (s, [])
  | fun_allocelems_case_1 : forall (s : store) (rt : reftype) (rt'_lst : (List reftype)) (ref_lst : (List ref)) (ref'_lst_lst : (List (List ref))) (s_2 : store) (ea : Nat) (ea'_lst : (List elemaddr)) (s_1 : store) (var_1 : store × (List elemaddr)) (var_0 : store × elemaddr), 
    (fun_allocelems s_1 rt'_lst ref'_lst_lst var_1) ->
    (fun_allocelem s rt ref_lst var_0) ->
    ((s_1, ea) == var_0) ->
    ((s_2, ea'_lst) == var_1) ->
    fun_allocelems s ([rt] ++ rt'_lst) ([ref_lst] ++ ref'_lst_lst) (s_2, ([ea] ++ ea'_lst))

/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:92.1-92.90 -/
def allocexport : ∀  (v_moduleinst : moduleinst) (v_export : «export») , exportinst
  | v_moduleinst, (.EXPORT v_name (.TAG x)) =>
    { NAME := v_name, ADDR := (.TAG ((v_moduleinst.TAGS)[(proj_uN_0 x)]!)) }
  | v_moduleinst, (.EXPORT v_name (.GLOBAL x)) =>
    { NAME := v_name, ADDR := (.GLOBAL ((v_moduleinst.GLOBALS)[(proj_uN_0 x)]!)) }
  | v_moduleinst, (.EXPORT v_name (.MEM x)) =>
    { NAME := v_name, ADDR := (.MEM ((v_moduleinst.MEMS)[(proj_uN_0 x)]!)) }
  | v_moduleinst, (.EXPORT v_name (.TABLE x)) =>
    { NAME := v_name, ADDR := (.TABLE ((v_moduleinst.TABLES)[(proj_uN_0 x)]!)) }
  | v_moduleinst, (.EXPORT v_name (.FUNC x)) =>
    { NAME := v_name, ADDR := (.FUNC ((v_moduleinst.FUNCS)[(proj_uN_0 x)]!)) }


/- Auxiliary Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:99.1-99.104 -/
def allocexports : ∀  (v_moduleinst : moduleinst) (var_0 : (List «export»)) , (List exportinst)
  | v_moduleinst, export_lst =>
    (List.map (fun (v_export : «export») => (allocexport v_moduleinst v_export)) export_lst)


/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:103.6-103.18 -/
inductive fun_allocmodule : store -> module -> (List externaddr) -> (List val) -> (List ref) -> (List (List ref)) -> store × moduleinst -> Prop where
  | fun_allocmodule_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (List externaddr)) (val_G_lst : (List val)) (ref_T_lst : (List ref)) (ref_E_lst_lst : (List (List ref))) (s_7 : store) (v_moduleinst : moduleinst) (type_lst : (List type)) (import_lst : (List «import»)) (tag_lst : (List tag)) (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (func_lst : (List func)) (data_lst : (List data)) (elem_lst : (List elem)) (start_opt : (Option start)) (export_lst : (List «export»)) (tagtype_lst : (List tagtype)) (globaltype_lst : (List globaltype)) (expr_G_lst : (List expr)) (memtype_lst : (List memtype)) (tabletype_lst : (List tabletype)) (expr_T_lst : (List expr)) (x_lst : (List idx)) (local_lst_lst : (List (List «local»))) (expr_F_lst : (List expr)) (byte_lst_lst : (List (List byte))) (datamode_lst : (List datamode)) (elemtype_lst : (List elemtype)) (expr_E_lst_lst : (List (List expr))) (elemmode_lst : (List elemmode)) (aa_I_lst : (List tagaddr)) (ga_I_lst : (List globaladdr)) (ma_I_lst : (List memaddr)) (ta_I_lst : (List tableaddr)) (fa_I_lst : (List funcaddr)) (dt_lst : (List deftype)) (fa_lst : (List Nat)) (i_F_lst : (List Nat)) (s_1 : store) (aa_lst : (List tagaddr)) (s_2 : store) (ga_lst : (List globaladdr)) (s_3 : store) (ma_lst : (List memaddr)) (s_4 : store) (ta_lst : (List tableaddr)) (s_5 : store) (da_lst : (List dataaddr)) (s_6 : store) (ea_lst : (List elemaddr)) (xi_lst : (List exportinst)) (var_17 : store × (List funcaddr)) (var_16_lst : (List elemtype)) (var_15 : store × (List elemaddr)) (var_14 : store × (List dataaddr)) (var_13_lst : (List tabletype)) (var_12 : store × (List tableaddr)) (var_11_lst : (List memtype)) (var_10 : store × (List memaddr)) (var_9_lst : (List globaltype)) (var_8 : store × (List globaladdr)) (var_7_lst : (List tagtype)) (var_6 : store × (List tagaddr)) (var_5 : (List deftype)) (var_4 : (List funcaddr)) (var_3 : (List tableaddr)) (var_2 : (List memaddr)) (var_1 : (List globaladdr)) (var_0 : (List tagaddr)), 
    Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length dt_lst))) x_lst ->
    (fun_allocfuncs s_6 (List.map (fun (x : idx) => (dt_lst[(proj_uN_0 x)]!)) x_lst) (list_map3 (fun (expr_F : expr) (local_lst : (List «local»)) (x : idx) => (.FUNC x local_lst expr_F)) expr_F_lst local_lst_lst x_lst) (List.replicate (List.length func_lst) v_moduleinst) var_17) ->
    ((List.length var_16_lst) == (List.length elemtype_lst)) ->
    Forall₂ (fun (var_16 : elemtype) (v_elemtype : elemtype) => (fun_subst_all_reftype v_elemtype (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_16)) var_16_lst elemtype_lst ->
    (fun_allocelems s_5 var_16_lst ref_E_lst_lst var_15) ->
    (fun_allocdatas s_4 (List.replicate (List.length data_lst) .OK) byte_lst_lst var_14) ->
    ((List.length var_13_lst) == (List.length tabletype_lst)) ->
    Forall₂ (fun (var_13 : tabletype) (v_tabletype : tabletype) => (fun_subst_all_tabletype v_tabletype (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_13)) var_13_lst tabletype_lst ->
    (fun_alloctables s_3 var_13_lst ref_T_lst var_12) ->
    ((List.length var_11_lst) == (List.length memtype_lst)) ->
    Forall₂ (fun (var_11 : memtype) (v_memtype : memtype) => (fun_subst_all_memtype v_memtype (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_11)) var_11_lst memtype_lst ->
    (fun_allocmems s_2 var_11_lst var_10) ->
    ((List.length var_9_lst) == (List.length globaltype_lst)) ->
    Forall₂ (fun (var_9 : globaltype) (v_globaltype : globaltype) => (fun_subst_all_globaltype v_globaltype (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_9)) var_9_lst globaltype_lst ->
    (fun_allocglobals s_1 var_9_lst val_G_lst var_8) ->
    ((List.length var_7_lst) == (List.length tagtype_lst)) ->
    Forall₂ (fun (var_7 : tagtype) (v_tagtype : tagtype) => (fun_subst_all_tagtype v_tagtype (List.map (fun (dt : deftype) => (typeuse_deftype dt)) dt_lst) var_7)) var_7_lst tagtype_lst ->
    (fun_alloctags s var_7_lst var_6) ->
    (fun_alloctypes type_lst var_5) ->
    (fun_funcsxa externaddr_lst var_4) ->
    (fun_tablesxa externaddr_lst var_3) ->
    (fun_memsxa externaddr_lst var_2) ->
    (fun_globalsxa externaddr_lst var_1) ->
    (fun_tagsxa externaddr_lst var_0) ->
    (v_module == (.MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst)) ->
    (tag_lst == (List.map (fun (v_tagtype : tagtype) => (.TAG v_tagtype)) tagtype_lst)) ->
    (global_lst == (List.zipWith (fun (expr_G : expr) (v_globaltype : globaltype) => (.GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ->
    (mem_lst == (List.map (fun (v_memtype : memtype) => (.MEMORY v_memtype)) memtype_lst)) ->
    (table_lst == (List.zipWith (fun (expr_T : expr) (v_tabletype : tabletype) => (.TABLE v_tabletype expr_T)) expr_T_lst tabletype_lst)) ->
    (func_lst == (list_map3 (fun (expr_F : expr) (local_lst : (List «local»)) (x : idx) => (.FUNC x local_lst expr_F)) expr_F_lst local_lst_lst x_lst)) ->
    (data_lst == (List.zipWith (fun (byte_lst : (List byte)) (v_datamode : datamode) => (.DATA byte_lst v_datamode)) byte_lst_lst datamode_lst)) ->
    (elem_lst == (list_map3 (fun (v_elemmode : elemmode) (v_elemtype : elemtype) (expr_E_lst : (List expr)) => (.ELEM v_elemtype expr_E_lst v_elemmode)) elemmode_lst elemtype_lst expr_E_lst_lst)) ->
    (aa_I_lst == var_0) ->
    (ga_I_lst == var_1) ->
    (ma_I_lst == var_2) ->
    (ta_I_lst == var_3) ->
    (fa_I_lst == var_4) ->
    (dt_lst == var_5) ->
    (fa_lst == (List.map (fun (i_F : Nat) => ((List.length (s.FUNCS)) + i_F)) i_F_lst)) ->
    ((s_1, aa_lst) == var_6) ->
    ((s_2, ga_lst) == var_8) ->
    ((s_3, ma_lst) == var_10) ->
    ((s_4, ta_lst) == var_12) ->
    ((s_5, da_lst) == var_14) ->
    ((s_6, ea_lst) == var_15) ->
    ((s_7, fa_lst) == var_17) ->
    (xi_lst == (allocexports { TYPES := [], TAGS := (aa_I_lst ++ aa_lst), GLOBALS := (ga_I_lst ++ ga_lst), MEMS := (ma_I_lst ++ ma_lst), TABLES := (ta_I_lst ++ ta_lst), FUNCS := (fa_I_lst ++ fa_lst), DATAS := [], ELEMS := [], EXPORTS := [] } export_lst)) ->
    (v_moduleinst == { TYPES := dt_lst, TAGS := (aa_I_lst ++ aa_lst), GLOBALS := (ga_I_lst ++ ga_lst), MEMS := (ma_I_lst ++ ma_lst), TABLES := (ta_I_lst ++ ta_lst), FUNCS := (fa_I_lst ++ fa_lst), DATAS := da_lst, ELEMS := ea_lst, EXPORTS := xi_lst }) ->
    fun_allocmodule s v_module externaddr_lst val_G_lst ref_T_lst ref_E_lst_lst (s_7, v_moduleinst)

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:148.6-148.15 -/
inductive fun_rundata_ : dataidx -> data -> (List instr) -> Prop where
  | fun_rundata__case_0 : forall (x : uN) (b_lst : (List byte)) (v_n : Nat), fun_rundata_ x (.DATA b_lst .PASSIVE) []
  | fun_rundata__case_1 : forall (x : uN) (b_lst : (List byte)) (v_n : Nat) (y : uN) (instr_lst : (List instr)), fun_rundata_ x (.DATA b_lst (.ACTIVE y instr_lst)) (instr_lst ++ [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT y x), (.DATA_DROP x)])

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:153.6-153.15 -/
inductive fun_runelem_ : elemidx -> elem -> (List instr) -> Prop where
  | fun_runelem__case_0 : forall (x : uN) (rt : reftype) (e_lst : (List expr)) (v_n : Nat), fun_runelem_ x (.ELEM rt e_lst .PASSIVE) []
  | fun_runelem__case_1 : forall (x : uN) (rt : reftype) (e_lst : (List expr)) (v_n : Nat), fun_runelem_ x (.ELEM rt e_lst .DECLARE) [(.ELEM_DROP x)]
  | fun_runelem__case_2 : forall (x : uN) (rt : reftype) (e_lst : (List expr)) (v_n : Nat) (y : uN) (instr_lst : (List instr)), fun_runelem_ x (.ELEM rt e_lst (.ACTIVE y instr_lst)) (instr_lst ++ [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT y x), (.ELEM_DROP x)])

/- Recursive Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:160.1-160.94 -/
/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:160.6-160.18 -/
inductive fun_evalglobals : state -> (List globaltype) -> (List expr) -> state × (List val) -> Prop where
  | fun_evalglobals_case_0 : forall (z : state), fun_evalglobals z [] [] (z, [])
  | fun_evalglobals_case_1 : forall (z : state) (gt : globaltype) (gt'_lst : (List globaltype)) (v_expr : (List instr)) (expr'_lst : (List expr)) (z' : state) (v_val : val) (val'_lst : (List val)) (s : store) (f : frame) (s' : store) (a : Nat) (var_1 : state × (List val)) (var_0 : store × globaladdr), 
    (fun_evalglobals (.mk_state s' (f <| MODULE, GLOBALS := ((GLOBALS (f.MODULE)) ++ [a]) |>)) gt'_lst expr'_lst var_1) ->
    (fun_allocglobal s gt v_val var_0) ->
    (Eval_expr z v_expr z [v_val]) ->
    (z == (.mk_state s f)) ->
    ((s', a) == var_0) ->
    ((z', val'_lst) == var_1) ->
    fun_evalglobals z ([gt] ++ gt'_lst) ([v_expr] ++ expr'_lst) (z', ([v_val] ++ val'_lst))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:169.6-169.18 -/
inductive fun_instantiate : store -> module -> (List externaddr) -> config -> Prop where
  | fun_instantiate_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (List externaddr)) (s' : store) (v_moduleinst : moduleinst) (instr_E_lst : (List instr)) (instr_D_lst : (List instr)) (instr_S_opt : (Option instr)) (xt_I_lst : (List externtype)) (xt_E_lst : (List externtype)) (type_lst : (List type)) (import_lst : (List «import»)) (tag_lst : (List tag)) (global_lst : (List global)) (mem_lst : (List mem)) (table_lst : (List table)) (func_lst : (List func)) (data_lst : (List data)) (elem_lst : (List elem)) (start_opt : (Option start)) (export_lst : (List «export»)) (globaltype_lst : (List globaltype)) (expr_G_lst : (List expr)) (tabletype_lst : (List tabletype)) (expr_T_lst : (List expr)) (byte_lst_lst : (List (List byte))) (datamode_lst : (List datamode)) (reftype_lst : (List reftype)) (expr_E_lst_lst : (List (List expr))) (elemmode_lst : (List elemmode)) (x_opt : (Option idx)) (moduleinst_0 : moduleinst) (i_F_lst : (List Nat)) (z : state) (z' : state) (val_G_lst : (List val)) (ref_T_lst : (List ref)) (ref_E_lst_lst : (List (List ref))) (i_D_lst : (List Nat)) (i_E_lst : (List Nat)) (var_6_lst : (List (List instr))) (var_5_lst : (List (List instr))) (var_4 : store × moduleinst) (var_3 : state × (List val)) (var_2 : (List funcaddr)) (var_1 : (List globaladdr)) (var_0 : (List deftype)), 
    Forall (fun (i_E : Nat) => (i_E < (List.length elem_lst))) i_E_lst ->
    Forall₂ (fun (var_6 : (List instr)) (i_E : Nat) => (fun_runelem_ (.mk_uN i_E) (elem_lst[i_E]!) var_6)) var_6_lst i_E_lst ->
    Forall (fun (i_D : Nat) => (i_D < (List.length data_lst))) i_D_lst ->
    Forall₂ (fun (var_5 : (List instr)) (i_D : Nat) => (fun_rundata_ (.mk_uN i_D) (data_lst[i_D]!) var_5)) var_5_lst i_D_lst ->
    (fun_allocmodule s v_module externaddr_lst val_G_lst ref_T_lst ref_E_lst_lst var_4) ->
    (fun_evalglobals z globaltype_lst expr_G_lst var_3) ->
    (fun_funcsxa externaddr_lst var_2) ->
    (fun_globalsxa externaddr_lst var_1) ->
    (fun_alloctypes type_lst var_0) ->
    (Module_ok v_module (.mk_moduletype xt_I_lst xt_E_lst)) ->
    ((List.length externaddr_lst) == (List.length xt_I_lst)) ->
    Forall₂ (fun (v_externaddr : externaddr) (xt_I : externtype) => (Externaddr_ok s v_externaddr xt_I)) externaddr_lst xt_I_lst ->
    (v_module == (.MODULE type_lst import_lst tag_lst global_lst mem_lst table_lst func_lst data_lst elem_lst start_opt export_lst)) ->
    (global_lst == (List.zipWith (fun (expr_G : expr) (v_globaltype : globaltype) => (.GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ->
    (table_lst == (List.zipWith (fun (expr_T : expr) (v_tabletype : tabletype) => (.TABLE v_tabletype expr_T)) expr_T_lst tabletype_lst)) ->
    (data_lst == (List.zipWith (fun (byte_lst : (List byte)) (v_datamode : datamode) => (.DATA byte_lst v_datamode)) byte_lst_lst datamode_lst)) ->
    (elem_lst == (list_map3 (fun (v_elemmode : elemmode) (expr_E_lst : (List expr)) (v_reftype : reftype) => (.ELEM v_reftype expr_E_lst v_elemmode)) elemmode_lst expr_E_lst_lst reftype_lst)) ->
    (start_opt == (Option.map (fun (x : idx) => (.START x)) x_opt)) ->
    (moduleinst_0 == { TYPES := var_0, TAGS := [], GLOBALS := var_1, MEMS := [], TABLES := [], FUNCS := (var_2 ++ (List.map (fun (i_F : Nat) => ((List.length (s.FUNCS)) + i_F)) i_F_lst)), DATAS := [], ELEMS := [], EXPORTS := [] }) ->
    (z == (.mk_state s { LOCALS := [], MODULE := moduleinst_0 })) ->
    ((z', val_G_lst) == var_3) ->
    ((List.length expr_T_lst) == (List.length ref_T_lst)) ->
    Forall₂ (fun (expr_T : expr) (ref_T : ref) => (Eval_expr z' expr_T z' [(val_ref ref_T)])) expr_T_lst ref_T_lst ->
    ((List.length expr_E_lst_lst) == (List.length ref_E_lst_lst)) ->
    Forall₂ (fun (expr_E_lst : (List expr)) (ref_E_lst : (List ref)) => ((List.length expr_E_lst) == (List.length ref_E_lst))) expr_E_lst_lst ref_E_lst_lst ->
    Forall₂ (fun (expr_E_lst : (List expr)) (ref_E_lst : (List ref)) => Forall₂ (fun (expr_E : expr) (ref_E : ref) => (Eval_expr z' expr_E z' [(val_ref ref_E)])) expr_E_lst ref_E_lst) expr_E_lst_lst ref_E_lst_lst ->
    ((s', v_moduleinst) == var_4) ->
    (instr_D_lst == (concat_ instr var_5_lst)) ->
    (instr_E_lst == (concat_ instr var_6_lst)) ->
    (instr_S_opt == (Option.map (fun (x : idx) => (.CALL x)) x_opt)) ->
    fun_instantiate s v_module externaddr_lst (.mk_config (.mk_state s' { LOCALS := [], MODULE := v_moduleinst }) (instr_E_lst ++ (instr_D_lst ++ (Option.toList instr_S_opt))))

/- Inductive Relations Definition at: ../../../../specification/wasm-3.0/4.4-execution.modules.spectec:199.6-199.13 -/
inductive fun_invoke : store -> funcaddr -> (List val) -> config -> Prop where
  | fun_invoke_case_0 : forall (s : store) (v_funcaddr : Nat) (val_lst : (List val)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (v_funcaddr < (List.length (s.FUNCS))) ->
    (Expand (((s.FUNCS)[v_funcaddr]!).TYPE) (.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    ((List.length t_1_lst) == (List.length val_lst)) ->
    Forall₂ (fun (t_1 : valtype) (v_val : val) => (Val_ok s v_val t_1)) t_1_lst val_lst ->
    fun_invoke s v_funcaddr val_lst (.mk_config (.mk_state s { LOCALS := [], MODULE := { TYPES := [], TAGS := [], GLOBALS := [], MEMS := [], TABLES := [], FUNCS := [], DATAS := [], ELEMS := [], EXPORTS := [] } }) ((List.map (fun (v_val : val) => (instr_val v_val)) val_lst) ++ [(.REF_FUNC_ADDR v_funcaddr), (.CALL_REF (typeuse_deftype (((s.FUNCS)[v_funcaddr]!).TYPE)))]))

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.3-binary.instructions.spectec:18.1-18.31 -/
abbrev castop : Type := (Option null) × (Option null)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.3-binary.instructions.spectec:98.1-98.35 -/
abbrev memidxop : Type := memidx × memarg

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.4-binary.modules.spectec:89.1-89.43 -/
abbrev startopt : Type := (List start)

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.4-binary.modules.spectec:124.1-124.46 -/
abbrev code : Type := (List «local») × expr

/- Type Alias Definition at: ../../../../specification/wasm-3.0/5.4-binary.modules.spectec:156.1-156.33 -/
abbrev nopt : Type := (List u32)
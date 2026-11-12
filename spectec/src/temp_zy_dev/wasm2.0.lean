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

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.14-162.17 -/
inductive MUT : Type where
  | MUT : MUT
deriving Inhabited, BEq


/- Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:7.1-7.15 -/
abbrev N : Type := Nat

/- Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:8.1-8.15 -/
abbrev M : Type := Nat

/- Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:9.1-9.15 -/
abbrev n : Type := Nat

/- Type Alias Definition at: ../specification/wasm-2.0/0-aux.spectec:10.1-10.15 -/
abbrev m : Type := Nat

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:15.1-15.14 -/
def Ki : Nat := 1024

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:21.1-21.25 -/
def min : ∀  (nat : Nat) (nat_0 : Nat) , Nat
  | i, j =>
    (if (i <= j) then i else j)


/- Recursive Definition at: ../specification/wasm-2.0/0-aux.spectec:25.1-25.21 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/0-aux.spectec:25.6-25.10 -/
inductive fun_sum : (List Nat) -> Nat -> Prop where
  | fun_sum_case_0 : fun_sum [] 0
  | fun_sum_case_1 : forall (v_n : Nat) (n'_lst : (List n)) (var_0 : Nat), 
    (fun_sum n'_lst var_0) ->
    fun_sum ([v_n] ++ n'_lst) (v_n + var_0)

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:32.1-32.58 -/
def opt_ : ∀  (X : Type) (var_0 : (List X)) , (Option (Option X))
  | X, [] =>
    (some none)
  | X, [w] =>
    (some (some w))
  | X, x1 =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:36.1-36.45 -/
def list_ : ∀  (X : Type) (var_0 : (Option X)) , (List X)
  | X, none =>
    []
  | X, (some w) =>
    [w]


/- Recursive Definition at: ../specification/wasm-2.0/0-aux.spectec:40.1-40.86 -/
/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:40.1-40.86 -/
def concat_ : ∀  (X : Type) (var_0 : (List (List X))) , (List X)
  | X, [] =>
    []
  | X, (w_lst :: w'_lst_lst) =>
    (w_lst ++ (concat_ X w'_lst_lst))


/- Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:44.1-44.39 -/
opaque inv_concat_ : forall (X : Type) (var_0 : (List X)), (List (List X)) := opaqueDef

/- Recursive Definition at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.46 -/
/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.46 -/
def setproduct2_ : ∀  (X : Type) (X_0 : X) (var_0 : (List (List X))) , (List (List X))
  | X, w_1, [] =>
    []
  | X, w_1, (w'_lst :: w_lst_lst) =>
    ([([w_1] ++ w'_lst)] ++ (setproduct2_ X w_1 w_lst_lst))


/- Recursive Definition at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.47 -/
/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.47 -/
def setproduct1_ : ∀  (X : Type) (var_0 : (List X)) (var_1 : (List (List X))) , (List (List X))
  | X, [], w_lst_lst =>
    []
  | X, (w_1 :: w'_lst), w_lst_lst =>
    ((setproduct2_ X w_1 w_lst_lst) ++ (setproduct1_ X w'_lst w_lst_lst))


/- Recursive Definition at: ../specification/wasm-2.0/0-aux.spectec:49.1-49.84 -/
/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:49.1-49.84 -/
def setproduct_ : ∀  (X : Type) (var_0 : (List (List X))) , (List (List X))
  | X, [] =>
    [[]]
  | X, (w_1_lst :: w_lst_lst) =>
    (setproduct1_ X w_1_lst (setproduct_ X w_lst_lst))


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 -/
inductive list (X : Type 0) : Type where
  | mk_list (X_lst : (List X)) : list X
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 -/
def proj_list_0 : ∀  (X : Type) (x : (list X)) , (List X)
  | X, (.mk_list v_X_list_0) =>
    (v_X_list_0)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36 -/
inductive bit : Type where
  | mk_bit (i : Nat) : bit
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.8-15.11 -/
inductive wf_bit : bit -> Prop where
  | bit_case_0 : forall (i : Nat), 
    ((i == 0) || (i == 1)) ->
    wf_bit (.mk_bit i)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 -/
inductive byte : Type where
  | mk_byte (i : Nat) : byte
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 -/
def proj_byte_0 : ∀  (x : byte) , Nat
  | (.mk_byte v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.8-16.12 -/
inductive wf_byte : byte -> Prop where
  | byte_case_0 : forall (i : Nat), 
    ((i >= 0) && (i <= 255)) ->
    wf_byte (.mk_byte i)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 -/
inductive uN : Type where
  | mk_uN (i : Nat) : uN
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 -/
def proj_uN_0 : ∀  (x : uN) , Nat
  | (.mk_uN v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.8-18.11 -/
inductive wf_uN : N -> uN -> Prop where
  | uN_case_0 : forall (v_N : N) (i : Nat), 
    ((i >= 0) && (i <= ((((2 ^ v_N) : Nat) - (1 : Nat)) : Nat))) ->
    wf_uN v_N (.mk_uN i)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 -/
inductive sN : Type where
  | mk_sN (i : Nat) : sN
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 -/
def proj_sN_0 : ∀  (x : sN) , Nat
  | (.mk_sN v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.8-20.11 -/
inductive wf_sN : N -> sN -> Prop where
  | sN_case_0 : forall (v_N : N) (i : Nat), 
    ((((i >= (0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat))) && (i <= (0 - (1 : Nat)))) || (i == (0 : Nat))) || ((i >= ((1 : Nat))) && (i <= (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat) - (1 : Nat))))) ->
    wf_sN v_N (.mk_sN i)

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:22.1-23.8 -/
abbrev iN : Type := uN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:25.1-25.18 -/
abbrev u8 : Type := uN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:26.1-26.20 -/
abbrev u16 : Type := uN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:27.1-27.20 -/
abbrev u31 : Type := uN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:28.1-28.20 -/
abbrev u32 : Type := uN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:29.1-29.20 -/
abbrev u64 : Type := uN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:30.1-30.20 -/
abbrev s33 : Type := sN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:31.1-31.20 -/
abbrev i32 : Type := iN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:32.1-32.20 -/
abbrev i64 : Type := iN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:33.1-33.22 -/
abbrev i128 : Type := iN

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:40.1-40.35 -/
def signif : ∀  (v_N : N) , (Option Nat)
  | 32 =>
    (some 23)
  | 64 =>
    (some 52)
  | x0 =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:44.1-44.34 -/
def expon : ∀  (v_N : N) , (Option Nat)
  | 32 =>
    (some 8)
  | 64 =>
    (some 11)
  | x0 =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:48.1-48.30 -/
def fun_M : ∀  (v_N : N) , Nat
  | v_N =>
    (Option.get! (signif v_N))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:51.1-51.30 -/
def E : ∀  (v_N : N) , Nat
  | v_N =>
    (Option.get! (expon v_N))


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:58.1-58.30 -/
abbrev exp : Type := Nat

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.1-63.84 -/
inductive fNmag : Type where
  | NORM (v_m : m) (v_exp : exp) : fNmag
  | SUBNORM (v_m : m) : fNmag
  | INF : fNmag
  | NAN (v_m : m) : fNmag
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.8-59.14 -/
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

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.1-56.35 -/
inductive fN : Type where
  | POS (v_fNmag : fNmag) : fN
  | NEG (v_fNmag : fNmag) : fN
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.8-54.11 -/
inductive wf_fN : N -> fN -> Prop where
  | fN_case_0 : forall (v_N : N) (v_fNmag : fNmag), 
    (wf_fNmag v_N v_fNmag) ->
    wf_fN v_N (.POS v_fNmag)
  | fN_case_1 : forall (v_N : N) (v_fNmag : fNmag), 
    (wf_fNmag v_N v_fNmag) ->
    wf_fN v_N (.NEG v_fNmag)

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:65.1-65.20 -/
abbrev f32 : Type := fN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:66.1-66.20 -/
abbrev f64 : Type := fN

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.1-68.39 -/
def fzero : ∀  (v_N : N) , fN
  | v_N =>
    (.POS (.SUBNORM 0))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.1-71.39 -/
def fone : ∀  (v_N : N) , fN
  | v_N =>
    (.POS (.NORM 1 (0 : Nat)))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:74.1-74.21 -/
def canon_ : ∀  (v_N : N) , Nat
  | v_N =>
    (2 ^ ((((Option.get! (signif v_N)) : Nat) - (1 : Nat)) : Nat))


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:80.1-81.8 -/
abbrev vN : Type := iN

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 -/
inductive char : Type where
  | mk_char (i : Nat) : char
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 -/
def proj_char_0 : ∀  (x : char) , Nat
  | (.mk_char v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.8-88.12 -/
inductive wf_char : char -> Prop where
  | char_case_0 : forall (i : Nat), 
    (((i >= 0) && (i <= 55295)) || ((i >= 57344) && (i <= 1114111))) ->
    wf_char (.mk_char i)

/- Recursive Definition at: ../specification/wasm-2.0/1-syntax.spectec:90.1-90.25 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:90.6-90.11 -/
inductive fun_utf8 : (List char) -> (List byte) -> Prop where
  | fun_utf8_case_0 : forall (ch : char) (b : byte), 
    (((proj_char_0 ch) < 128) && ((.mk_byte (proj_char_0 ch)) == b)) ->
    fun_utf8 [ch] [b]
  | fun_utf8_case_1 : forall (ch : char) (b_1 : byte) (b_2 : byte), 
    (((128 <= (proj_char_0 ch)) && ((proj_char_0 ch) < 2048)) && ((proj_char_0 ch) == (((2 ^ 6) * ((((proj_byte_0 b_1) : Nat) - (192 : Nat)) : Nat)) + ((((proj_byte_0 b_2) : Nat) - (128 : Nat)) : Nat)))) ->
    fun_utf8 [ch] [b_1, b_2]
  | fun_utf8_case_2 : forall (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte), 
    ((((2048 <= (proj_char_0 ch)) && ((proj_char_0 ch) < 55296)) || ((57344 <= (proj_char_0 ch)) && ((proj_char_0 ch) < 65536))) && ((proj_char_0 ch) == ((((2 ^ 12) * ((((proj_byte_0 b_1) : Nat) - (224 : Nat)) : Nat)) + ((2 ^ 6) * ((((proj_byte_0 b_2) : Nat) - (128 : Nat)) : Nat))) + ((((proj_byte_0 b_3) : Nat) - (128 : Nat)) : Nat)))) ->
    fun_utf8 [ch] [b_1, b_2, b_3]
  | fun_utf8_case_3 : forall (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) (b_4 : byte), 
    (((65536 <= (proj_char_0 ch)) && ((proj_char_0 ch) < 69632)) && ((proj_char_0 ch) == (((((2 ^ 18) * ((((proj_byte_0 b_1) : Nat) - (240 : Nat)) : Nat)) + ((2 ^ 12) * ((((proj_byte_0 b_2) : Nat) - (128 : Nat)) : Nat))) + ((2 ^ 6) * ((((proj_byte_0 b_3) : Nat) - (128 : Nat)) : Nat))) + ((((proj_byte_0 b_4) : Nat) - (128 : Nat)) : Nat)))) ->
    fun_utf8 [ch] [b_1, b_2, b_3, b_4]
  | fun_utf8_case_4 : forall (ch_lst : (List char)) (var_0_lst : (List (List byte))), 
    ((List.length var_0_lst) == (List.length ch_lst)) ->
    Forall₂ (fun (var_0 : (List byte)) (ch : char) => (fun_utf8 [ch] var_0)) var_0_lst ch_lst ->
    fun_utf8 ch_lst (concat_ byte var_0_lst)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 -/
inductive name : Type where
  | mk_name (char_lst : (List char)) : name
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 -/
def proj_name_0 : ∀  (x : name) , (List char)
  | (.mk_name v_char_list_0) =>
    (v_char_list_0)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.8-92.12 -/
inductive wf_name : name -> Prop where
  | name_case_0 : forall (char_lst : (List char)) (var_0 : (List byte)), 
    (fun_utf8 char_lst var_0) ->
    Forall (fun (v_char : char) => (wf_char v_char)) char_lst ->
    ((List.length var_0) < (2 ^ 32)) ->
    wf_name (.mk_name char_lst)

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:101.1-101.36 -/
abbrev idx : Type := u32

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:102.1-102.44 -/
abbrev laneidx : Type := u8

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:104.1-104.45 -/
abbrev typeidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:105.1-105.49 -/
abbrev funcidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:106.1-106.49 -/
abbrev globalidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:107.1-107.47 -/
abbrev tableidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:108.1-108.46 -/
abbrev memidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:109.1-109.45 -/
abbrev elemidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:110.1-110.45 -/
abbrev dataidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:111.1-111.47 -/
abbrev labelidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:112.1-112.47 -/
abbrev localidx : Type := idx

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:126.1-127.26 -/
inductive numtype : Type where
  | I32 : numtype
  | I64 : numtype
  | F32 : numtype
  | F64 : numtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:129.1-130.9 -/
inductive vectype : Type where
  | V128 : vectype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:132.1-133.22 -/
inductive consttype : Type where
  | I32 : consttype
  | I64 : consttype
  | F32 : consttype
  | F64 : consttype
  | V128 : consttype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:135.1-136.24 -/
inductive reftype : Type where
  | FUNCREF : reftype
  | EXTERNREF : reftype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:138.1-139.38 -/
inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
  | V128 : valtype
  | FUNCREF : valtype
  | EXTERNREF : valtype
  | BOT : valtype
deriving Inhabited, BEq


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
def valtype_reftype : ∀  (var_0 : reftype) , valtype
  | .FUNCREF =>
    .FUNCREF
  | .EXTERNREF =>
    .EXTERNREF


/- Auxiliary Definition at:  -/
def valtype_vectype : ∀  (var_0 : vectype) , valtype
  | .V128 =>
    .V128


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:141.1-141.38 -/
inductive Inn : Type where
  | I32 : Inn
  | I64 : Inn
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def numtype_Inn : ∀  (var_0 : Inn) , numtype
  | .I32 =>
    .I32
  | .I64 =>
    .I64


/- Auxiliary Definition at:  -/
def valtype_Inn : ∀  (var_0 : Inn) , valtype
  | .I32 =>
    .I32
  | .I64 =>
    .I64


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:142.1-142.38 -/
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


/- Auxiliary Definition at:  -/
def valtype_Fnn : ∀  (var_0 : Fnn) , valtype
  | .F32 =>
    .F32
  | .F64 =>
    .F64


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:143.1-143.36 -/
abbrev Vnn : Type := vectype

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:146.1-147.16 -/
abbrev resulttype : Type := (list valtype)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:152.1-152.52 -/
inductive packtype : Type where
  | I8 : packtype
  | I16 : packtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:153.1-153.60 -/
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
def lanetype_Inn : ∀  (var_0 : Inn) , lanetype
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


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:155.1-155.37 -/
abbrev Pnn : Type := packtype

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:156.1-156.38 -/
inductive Jnn : Type where
  | I32 : Jnn
  | I64 : Jnn
  | I8 : Jnn
  | I16 : Jnn
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def Jnn_Inn : ∀  (var_0 : Inn) , Jnn
  | .I32 =>
    .I32
  | .I64 =>
    .I64


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
def Jnn_packtype : ∀  (var_0 : packtype) , Jnn
  | .I8 =>
    .I8
  | .I16 =>
    .I16


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:157.1-157.37 -/
abbrev Lnn : Type := lanetype

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.1-162.18 -/
abbrev «mut» : Type := (Option MUT)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.1-165.17 -/
inductive limits : Type where
  | mk_limits (v_u32 : u32) (_ : (Option u32)) : limits
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.8-164.14 -/
inductive wf_limits : limits -> Prop where
  | limits_case_0 : forall (v_u32 : u32) (var_0 : (Option u32)), 
    (wf_uN 32 v_u32) ->
    Forall (fun (var_0 : u32) => (wf_uN 32 var_0)) (Option.toList var_0) ->
    wf_limits (.mk_limits v_u32 var_0)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:167.1-168.14 -/
inductive globaltype : Type where
  | mk_globaltype (v_mut : «mut») (v_valtype : valtype) : globaltype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:169.1-170.27 -/
inductive functype : Type where
  | mk_functype (v_resulttype : resulttype) (_ : resulttype) : functype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.1-172.17 -/
inductive tabletype : Type where
  | mk_tabletype (v_limits : limits) (v_reftype : reftype) : tabletype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.8-171.17 -/
inductive wf_tabletype : tabletype -> Prop where
  | tabletype_case_0 : forall (v_limits : limits) (v_reftype : reftype), 
    (wf_limits v_limits) ->
    wf_tabletype (.mk_tabletype v_limits v_reftype)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.1-174.14 -/
inductive memtype : Type where
  | PAGE (v_limits : limits) : memtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.8-173.15 -/
inductive wf_memtype : memtype -> Prop where
  | memtype_case_0 : forall (v_limits : limits), 
    (wf_limits v_limits) ->
    wf_memtype (.PAGE v_limits)

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:175.1-176.10 -/
abbrev elemtype : Type := reftype

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:177.1-178.5 -/
inductive datatype : Type where
  | OK : datatype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.1-180.70 -/
inductive externtype : Type where
  | FUNC (v_functype : functype) : externtype
  | GLOBAL (v_globaltype : globaltype) : externtype
  | TABLE (v_tabletype : tabletype) : externtype
  | MEM (v_memtype : memtype) : externtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:179.8-179.18 -/
inductive wf_externtype : externtype -> Prop where
  | externtype_case_0 : forall (v_functype : functype), wf_externtype (.FUNC v_functype)
  | externtype_case_1 : forall (v_globaltype : globaltype), wf_externtype (.GLOBAL v_globaltype)
  | externtype_case_2 : forall (v_tabletype : tabletype), 
    (wf_tabletype v_tabletype) ->
    wf_externtype (.TABLE v_tabletype)
  | externtype_case_3 : forall (v_memtype : memtype), 
    (wf_memtype v_memtype) ->
    wf_externtype (.MEM v_memtype)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.1-318.60 -/
inductive dim : Type where
  | mk_dim (i : Nat) : dim
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.1-318.60 -/
def proj_dim_0 : ∀  (x : dim) , Nat
  | (.mk_dim v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:318.8-318.11 -/
inductive wf_dim : dim -> Prop where
  | dim_case_0 : forall (i : Nat), 
    (((((i == 1) || (i == 2)) || (i == 4)) || (i == 8)) || (i == 16)) ->
    wf_dim (.mk_dim i)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:319.1-319.69 -/
inductive shape : Type where
  | X (v_lanetype : lanetype) (v_dim : dim) : shape
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:319.8-319.13 -/
inductive wf_shape : shape -> Prop where
  | shape_case_0 : forall (v_lanetype : lanetype) (v_dim : dim), 
    (wf_dim v_dim) ->
    wf_shape (.X v_lanetype v_dim)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:206.1-206.32 -/
def fun_lanetype : ∀  (v_shape : shape) , lanetype
  | (.X v_Lnn (.mk_dim v_N)) =>
    v_Lnn


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:208.1-208.59 -/
def size : ∀  (v_valtype : valtype) , (Option Nat)
  | .I32 =>
    (some 32)
  | .I64 =>
    (some 64)
  | .F32 =>
    (some 32)
  | .F64 =>
    (some 64)
  | .V128 =>
    (some 128)
  | x0 =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 -/
def psize : ∀  (v_packtype : packtype) , Nat
  | .I8 =>
    8
  | .I16 =>
    16


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.45 -/
def lsize : ∀  (v_lanetype : lanetype) , Nat
  | .I32 =>
    (Option.get! (size (valtype_numtype .I32)))
  | .I64 =>
    (Option.get! (size (valtype_numtype .I64)))
  | .F32 =>
    (Option.get! (size (valtype_numtype .F32)))
  | .F64 =>
    (Option.get! (size (valtype_numtype .F64)))
  | .I8 =>
    (psize .I8)
  | .I16 =>
    (psize .I16)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 -/
def isize : ∀  (v_Inn : Inn) , Nat
  | v_Inn =>
    (Option.get! (size (valtype_Inn v_Inn)))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 -/
def jsize : ∀  (v_Jnn : Jnn) , Nat
  | v_Jnn =>
    (lsize (lanetype_Jnn v_Jnn))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:213.1-213.70 -/
def fsize : ∀  (v_Fnn : Fnn) , Nat
  | v_Fnn =>
    (Option.get! (size (valtype_Fnn v_Fnn)))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:231.1-231.63 -/
def sizenn : ∀  (v_numtype : numtype) , Nat
  | nt =>
    (Option.get! (size (valtype_numtype nt)))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:232.1-232.63 -/
def sizenn1 : ∀  (v_numtype : numtype) , Nat
  | nt =>
    (Option.get! (size (valtype_numtype nt)))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:233.1-233.63 -/
def sizenn2 : ∀  (v_numtype : numtype) , Nat
  | nt =>
    (Option.get! (size (valtype_numtype nt)))


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:238.1-238.63 -/
def lsizenn : ∀  (v_lanetype : lanetype) , Nat
  | lt =>
    (lsize lt)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:239.1-239.63 -/
def lsizenn1 : ∀  (v_lanetype : lanetype) , Nat
  | lt =>
    (lsize lt)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:240.1-240.63 -/
def lsizenn2 : ∀  (v_lanetype : lanetype) , Nat
  | lt =>
    (lsize lt)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.40 -/
def inv_isize : ∀  (nat : Nat) , (Option Inn)
  | 32 =>
    (some .I32)
  | 64 =>
    (some .I64)
  | x0 =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:246.1-246.40 -/
def inv_jsize : ∀  (nat : Nat) , (Option Jnn)
  | 8 =>
    (some .I8)
  | 16 =>
    (some .I16)
  | 32 =>
    (some .I32)
  | 64 =>
    (some .I64)
  | x0 =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:247.1-247.40 -/
def inv_fsize : ∀  (nat : Nat) , (Option Fnn)
  | 32 =>
    (some .F32)
  | 64 =>
    (some .F64)
  | x0 =>
    none


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 -/
inductive num_ : Type where
  | mk_num__0 (v_Inn : Inn) (var_x : iN) : num_
  | mk_num__1 (v_Fnn : Fnn) (var_x : fN) : num_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.8-259.13 -/
inductive wf_num_ : numtype -> num_ -> Prop where
  | num__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : iN), 
    ((size (valtype_Inn v_Inn)) != none) ->
    (wf_uN (Option.get! (size (valtype_Inn v_Inn))) var_x) ->
    (v_numtype == (numtype_Inn v_Inn)) ->
    wf_num_ v_numtype (.mk_num__0 v_Inn var_x)
  | num__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : fN), 
    (wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x) ->
    (v_numtype == (numtype_Fnn v_Fnn)) ->
    wf_num_ v_numtype (.mk_num__1 v_Fnn var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 -/
def proj_num__0 : ∀  (var_x : num_) , (Option iN)
  | (.mk_num__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 -/
def proj_num__1 : ∀  (var_x : num_) , (Option fN)
  | (.mk_num__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:263.1-263.36 -/
abbrev pack_ : Type := iN

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -/
inductive lane_ : Type where
  | mk_lane__0 (v_numtype : numtype) (var_x : num_) : lane_
  | mk_lane__1 (v_packtype : packtype) (var_x : pack_) : lane_
  | mk_lane__2 (v_Jnn : Jnn) (var_x : iN) : lane_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.8-265.14 -/
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

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -/
def proj_lane__0 : ∀  (var_x : lane_) , (Option num_)
  | (.mk_lane__0 v_numtype var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -/
def proj_lane__1 : ∀  (var_x : lane_) , (Option pack_)
  | (.mk_lane__1 v_packtype var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -/
def proj_lane__2 : ∀  (var_x : lane_) , (Option iN)
  | (.mk_lane__2 v_Jnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:270.1-270.34 -/
abbrev vec_ : Type := vN

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.6-272.11 -/
inductive fun_zero : numtype -> num_ -> Prop where
  | fun_zero_case_0 : 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (.mk_uN 0))) ->
    fun_zero .I32 (.mk_num__0 .I32 (.mk_uN 0))
  | fun_zero_case_1 : 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (.mk_uN 0))) ->
    fun_zero .I64 (.mk_num__0 .I64 (.mk_uN 0))
  | fun_zero_case_2 : 
    ((size (valtype_Fnn .F32)) != none) ->
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 (fzero (Option.get! (size (valtype_Fnn .F32)))))) ->
    fun_zero .F32 (.mk_num__1 .F32 (fzero (Option.get! (size (valtype_Fnn .F32)))))
  | fun_zero_case_3 : 
    ((size (valtype_Fnn .F64)) != none) ->
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 (fzero (Option.get! (size (valtype_Fnn .F64)))))) ->
    fun_zero .F64 (.mk_num__1 .F64 (fzero (Option.get! (size (valtype_Fnn .F64)))))

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:279.1-279.42 -/
inductive sx : Type where
  | U : sx
  | S : sx
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 -/
inductive sz : Type where
  | mk_sz (i : Nat) : sz
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.1-280.56 -/
def proj_sz_0 : ∀  (x : sz) , Nat
  | (.mk_sz v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.8-280.10 -/
inductive wf_sz : sz -> Prop where
  | sz_case_0 : forall (i : Nat), 
    ((((i == 8) || (i == 16)) || (i == 32)) || (i == 64)) ->
    wf_sz (.mk_sz i)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 -/
inductive unop_Inn : Type where
  | CLZ : unop_Inn
  | CTZ : unop_Inn
  | POPCNT : unop_Inn
  | EXTEND (v_n : n) : unop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 -/
inductive unop_Fnn : Type where
  | ABS : unop_Fnn
  | NEG : unop_Fnn
  | SQRT : unop_Fnn
  | CEIL : unop_Fnn
  | FLOOR : unop_Fnn
  | TRUNC : unop_Fnn
  | NEAREST : unop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 -/
inductive unop_ : Type where
  | mk_unop__0 (v_Inn : Inn) (var_x : unop_Inn) : unop_
  | mk_unop__1 (v_Fnn : Fnn) (var_x : unop_Fnn) : unop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.8-282.14 -/
inductive wf_unop_ : numtype -> unop_ -> Prop where
  | unop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : unop_Inn), 
    (v_numtype == (numtype_Inn v_Inn)) ->
    wf_unop_ v_numtype (.mk_unop__0 v_Inn var_x)
  | unop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : unop_Fnn), 
    (v_numtype == (numtype_Fnn v_Fnn)) ->
    wf_unop_ v_numtype (.mk_unop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 -/
def proj_unop__0 : ∀  (var_x : unop_) , (Option unop_Inn)
  | (.mk_unop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 -/
def proj_unop__1 : ∀  (var_x : unop_) , (Option unop_Fnn)
  | (.mk_unop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 -/
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


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 -/
inductive binop_Fnn : Type where
  | ADD : binop_Fnn
  | SUB : binop_Fnn
  | MUL : binop_Fnn
  | DIV : binop_Fnn
  | MIN : binop_Fnn
  | MAX : binop_Fnn
  | COPYSIGN : binop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 -/
inductive binop_ : Type where
  | mk_binop__0 (v_Inn : Inn) (var_x : binop_Inn) : binop_
  | mk_binop__1 (v_Fnn : Fnn) (var_x : binop_Fnn) : binop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.8-286.15 -/
inductive wf_binop_ : numtype -> binop_ -> Prop where
  | binop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : binop_Inn), 
    (v_numtype == (numtype_Inn v_Inn)) ->
    wf_binop_ v_numtype (.mk_binop__0 v_Inn var_x)
  | binop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : binop_Fnn), 
    (v_numtype == (numtype_Fnn v_Fnn)) ->
    wf_binop_ v_numtype (.mk_binop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 -/
def proj_binop__0 : ∀  (var_x : binop_) , (Option binop_Inn)
  | (.mk_binop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 -/
def proj_binop__1 : ∀  (var_x : binop_) , (Option binop_Fnn)
  | (.mk_binop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 -/
inductive testop_Inn : Type where
  | EQZ : testop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 -/
inductive testop_ : Type where
  | mk_testop__0 (v_Inn : Inn) (var_x : testop_Inn) : testop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.8-293.16 -/
inductive wf_testop_ : numtype -> testop_ -> Prop where
  | testop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : testop_Inn), 
    (v_numtype == (numtype_Inn v_Inn)) ->
    wf_testop_ v_numtype (.mk_testop__0 v_Inn var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 -/
def proj_testop__0 : ∀  (var_x : testop_) , testop_Inn
  | (.mk_testop__0 v_Inn var_x) =>
    var_x


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 -/
inductive relop_Inn : Type where
  | EQ : relop_Inn
  | NE : relop_Inn
  | LT (v_sx : sx) : relop_Inn
  | GT (v_sx : sx) : relop_Inn
  | LE (v_sx : sx) : relop_Inn
  | GE (v_sx : sx) : relop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 -/
inductive relop_Fnn : Type where
  | EQ : relop_Fnn
  | NE : relop_Fnn
  | LT : relop_Fnn
  | GT : relop_Fnn
  | LE : relop_Fnn
  | GE : relop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 -/
inductive relop_ : Type where
  | mk_relop__0 (v_Inn : Inn) (var_x : relop_Inn) : relop_
  | mk_relop__1 (v_Fnn : Fnn) (var_x : relop_Fnn) : relop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.8-297.15 -/
inductive wf_relop_ : numtype -> relop_ -> Prop where
  | relop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : relop_Inn), 
    (v_numtype == (numtype_Inn v_Inn)) ->
    wf_relop_ v_numtype (.mk_relop__0 v_Inn var_x)
  | relop__case_1 : forall (v_numtype : numtype) (v_Fnn : Fnn) (var_x : relop_Fnn), 
    (v_numtype == (numtype_Fnn v_Fnn)) ->
    wf_relop_ v_numtype (.mk_relop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 -/
def proj_relop__0 : ∀  (var_x : relop_) , (Option relop_Inn)
  | (.mk_relop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 -/
def proj_relop__1 : ∀  (var_x : relop_) , (Option relop_Fnn)
  | (.mk_relop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-313.16 -/
inductive cvtop : Type where
  | EXTEND (v_sx : sx) : cvtop
  | WRAP : cvtop
  | CONVERT (v_sx : sx) : cvtop
  | TRUNC (v_sx : sx) : cvtop
  | TRUNC_SAT (v_sx : sx) : cvtop
  | PROMOTE : cvtop
  | DEMOTE : cvtop
  | REINTERPRET : cvtop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:320.1-320.69 -/
inductive ishape : Type where
  | X (v_Jnn : Jnn) (v_dim : dim) : ishape
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def shape_ishape : ∀  (var_0 : ishape) , shape
  | (.X x0 x1) =>
    (.X (lanetype_Jnn x0) x1)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:320.8-320.14 -/
inductive wf_ishape : ishape -> Prop where
  | ishape_case_0 : forall (v_Jnn : Jnn) (v_dim : dim), 
    (wf_dim v_dim) ->
    wf_ishape (.X v_Jnn v_dim)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:321.1-321.69 -/
inductive fshape : Type where
  | X (v_Fnn : Fnn) (v_dim : dim) : fshape
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:321.8-321.14 -/
inductive wf_fshape : fshape -> Prop where
  | fshape_case_0 : forall (v_Fnn : Fnn) (v_dim : dim), 
    (wf_dim v_dim) ->
    wf_fshape (.X v_Fnn v_dim)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:322.1-322.69 -/
inductive pshape : Type where
  | X (v_Pnn : Pnn) (v_dim : dim) : pshape
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:322.8-322.14 -/
inductive wf_pshape : pshape -> Prop where
  | pshape_case_0 : forall (v_Pnn : Pnn) (v_dim : dim), 
    (wf_dim v_dim) ->
    wf_pshape (.X v_Pnn v_dim)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.1-324.22 -/
def fun_dim : ∀  (v_shape : shape) , dim
  | (.X v_Lnn (.mk_dim v_N)) =>
    (.mk_dim v_N)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.1-325.41 -/
def shsize : ∀  (v_shape : shape) , Nat
  | (.X v_Lnn (.mk_dim v_N)) =>
    ((lsize v_Lnn) * v_N)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:327.1-327.20 -/
inductive vvunop : Type where
  | NOT : vvunop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:328.1-328.41 -/
inductive vvbinop : Type where
  | AND : vvbinop
  | ANDNOT : vvbinop
  | OR : vvbinop
  | XOR : vvbinop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:329.1-329.28 -/
inductive vvternop : Type where
  | BITSELECT : vvternop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:330.1-330.27 -/
inductive vvtestop : Type where
  | ANY_TRUE : vvtestop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 -/
inductive vunop_Jnn_N : Type where
  | ABS : vunop_Jnn_N
  | NEG : vunop_Jnn_N
  | POPCNT : vunop_Jnn_N
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.8-332.15 -/
inductive wf_vunop_Jnn_N : Jnn -> N -> vunop_Jnn_N -> Prop where
  | vunop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : N), wf_vunop_Jnn_N v_Jnn v_N .ABS
  | vunop_Jnn_N_case_1 : forall (v_Jnn : Jnn) (v_N : N), wf_vunop_Jnn_N v_Jnn v_N .NEG
  | vunop_Jnn_N_case_2 : forall (v_Jnn : Jnn) (v_N : N), 
    (v_Jnn == .I8) ->
    wf_vunop_Jnn_N v_Jnn v_N .POPCNT

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 -/
inductive vunop_Fnn_N : Type where
  | ABS : vunop_Fnn_N
  | NEG : vunop_Fnn_N
  | SQRT : vunop_Fnn_N
  | CEIL : vunop_Fnn_N
  | FLOOR : vunop_Fnn_N
  | TRUNC : vunop_Fnn_N
  | NEAREST : vunop_Fnn_N
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 -/
inductive vunop_ : Type where
  | mk_vunop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vunop_Jnn_N) : vunop_
  | mk_vunop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vunop_Fnn_N) : vunop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.8-332.15 -/
inductive wf_vunop_ : shape -> vunop_ -> Prop where
  | vunop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vunop_Jnn_N), 
    (wf_vunop_Jnn_N v_Jnn v_N var_x) ->
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) ->
    wf_vunop_ v_shape (.mk_vunop__0 v_Jnn v_N var_x)
  | vunop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vunop_Fnn_N), 
    (v_shape == (.X (lanetype_Fnn v_Fnn) (.mk_dim v_N))) ->
    wf_vunop_ v_shape (.mk_vunop__1 v_Fnn v_N var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 -/
def proj_vunop__0 : ∀  (var_x : vunop_) , (Option vunop_Jnn_N)
  | (.mk_vunop__0 v_Jnn v_N var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.21 -/
def proj_vunop__1 : ∀  (var_x : vunop_) , (Option vunop_Fnn_N)
  | (.mk_vunop__1 v_Fnn v_N var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 -/
inductive vbinop_Jnn_N : Type where
  | ADD : vbinop_Jnn_N
  | SUB : vbinop_Jnn_N
  | ADD_SAT (v_sx : sx) : vbinop_Jnn_N
  | SUB_SAT (v_sx : sx) : vbinop_Jnn_N
  | MUL : vbinop_Jnn_N
  | AVGRU : vbinop_Jnn_N
  | Q15MULR_SATS : vbinop_Jnn_N
  | MIN (v_sx : sx) : vbinop_Jnn_N
  | MAX (v_sx : sx) : vbinop_Jnn_N
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.16 -/
inductive wf_vbinop_Jnn_N : Jnn -> N -> vbinop_Jnn_N -> Prop where
  | vbinop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : N), wf_vbinop_Jnn_N v_Jnn v_N .ADD
  | vbinop_Jnn_N_case_1 : forall (v_Jnn : Jnn) (v_N : N), wf_vbinop_Jnn_N v_Jnn v_N .SUB
  | vbinop_Jnn_N_case_2 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
    wf_vbinop_Jnn_N v_Jnn v_N (.ADD_SAT v_sx)
  | vbinop_Jnn_N_case_3 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
    wf_vbinop_Jnn_N v_Jnn v_N (.SUB_SAT v_sx)
  | vbinop_Jnn_N_case_4 : forall (v_Jnn : Jnn) (v_N : N), 
    ((lsizenn (lanetype_Jnn v_Jnn)) >= 16) ->
    wf_vbinop_Jnn_N v_Jnn v_N .MUL
  | vbinop_Jnn_N_case_5 : forall (v_Jnn : Jnn) (v_N : N), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 16) ->
    wf_vbinop_Jnn_N v_Jnn v_N .AVGRU
  | vbinop_Jnn_N_case_6 : forall (v_Jnn : Jnn) (v_N : N), 
    ((lsizenn (lanetype_Jnn v_Jnn)) == 16) ->
    wf_vbinop_Jnn_N v_Jnn v_N .Q15MULR_SATS
  | vbinop_Jnn_N_case_7 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 32) ->
    wf_vbinop_Jnn_N v_Jnn v_N (.MIN v_sx)
  | vbinop_Jnn_N_case_8 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    ((lsizenn (lanetype_Jnn v_Jnn)) <= 32) ->
    wf_vbinop_Jnn_N v_Jnn v_N (.MAX v_sx)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 -/
inductive vbinop_Fnn_N : Type where
  | ADD : vbinop_Fnn_N
  | SUB : vbinop_Fnn_N
  | MUL : vbinop_Fnn_N
  | DIV : vbinop_Fnn_N
  | MIN : vbinop_Fnn_N
  | MAX : vbinop_Fnn_N
  | PMIN : vbinop_Fnn_N
  | PMAX : vbinop_Fnn_N
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 -/
inductive vbinop_ : Type where
  | mk_vbinop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vbinop_Jnn_N) : vbinop_
  | mk_vbinop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vbinop_Fnn_N) : vbinop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.16 -/
inductive wf_vbinop_ : shape -> vbinop_ -> Prop where
  | vbinop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vbinop_Jnn_N), 
    (wf_vbinop_Jnn_N v_Jnn v_N var_x) ->
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) ->
    wf_vbinop_ v_shape (.mk_vbinop__0 v_Jnn v_N var_x)
  | vbinop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vbinop_Fnn_N), 
    (v_shape == (.X (lanetype_Fnn v_Fnn) (.mk_dim v_N))) ->
    wf_vbinop_ v_shape (.mk_vbinop__1 v_Fnn v_N var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 -/
def proj_vbinop__0 : ∀  (var_x : vbinop_) , (Option vbinop_Jnn_N)
  | (.mk_vbinop__0 v_Jnn v_N var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.22 -/
def proj_vbinop__1 : ∀  (var_x : vbinop_) , (Option vbinop_Fnn_N)
  | (.mk_vbinop__1 v_Fnn v_N var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 -/
inductive vtestop_Jnn_N : Type where
  | ALL_TRUE : vtestop_Jnn_N
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 -/
inductive vtestop_ : Type where
  | mk_vtestop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vtestop_Jnn_N) : vtestop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.8-350.17 -/
inductive wf_vtestop_ : shape -> vtestop_ -> Prop where
  | vtestop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vtestop_Jnn_N), 
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) ->
    wf_vtestop_ v_shape (.mk_vtestop__0 v_Jnn v_N var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:350.1-350.23 -/
def proj_vtestop__0 : ∀  (var_x : vtestop_) , vtestop_Jnn_N
  | (.mk_vtestop__0 v_Jnn v_N var_x) =>
    var_x


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 -/
inductive vrelop_Jnn_N : Type where
  | EQ : vrelop_Jnn_N
  | NE : vrelop_Jnn_N
  | LT (v_sx : sx) : vrelop_Jnn_N
  | GT (v_sx : sx) : vrelop_Jnn_N
  | LE (v_sx : sx) : vrelop_Jnn_N
  | GE (v_sx : sx) : vrelop_Jnn_N
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.8-354.16 -/
inductive wf_vrelop_Jnn_N : Jnn -> N -> vrelop_Jnn_N -> Prop where
  | vrelop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : N), wf_vrelop_Jnn_N v_Jnn v_N .EQ
  | vrelop_Jnn_N_case_1 : forall (v_Jnn : Jnn) (v_N : N), wf_vrelop_Jnn_N v_Jnn v_N .NE
  | vrelop_Jnn_N_case_2 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    (((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == .S)) ->
    wf_vrelop_Jnn_N v_Jnn v_N (.LT v_sx)
  | vrelop_Jnn_N_case_3 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    (((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == .S)) ->
    wf_vrelop_Jnn_N v_Jnn v_N (.GT v_sx)
  | vrelop_Jnn_N_case_4 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    (((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == .S)) ->
    wf_vrelop_Jnn_N v_Jnn v_N (.LE v_sx)
  | vrelop_Jnn_N_case_5 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    (((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == .S)) ->
    wf_vrelop_Jnn_N v_Jnn v_N (.GE v_sx)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 -/
inductive vrelop_Fnn_N : Type where
  | EQ : vrelop_Fnn_N
  | NE : vrelop_Fnn_N
  | LT : vrelop_Fnn_N
  | GT : vrelop_Fnn_N
  | LE : vrelop_Fnn_N
  | GE : vrelop_Fnn_N
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 -/
inductive vrelop_ : Type where
  | mk_vrelop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vrelop_Jnn_N) : vrelop_
  | mk_vrelop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vrelop_Fnn_N) : vrelop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.8-354.16 -/
inductive wf_vrelop_ : shape -> vrelop_ -> Prop where
  | vrelop__case_0 : forall (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vrelop_Jnn_N), 
    (wf_vrelop_Jnn_N v_Jnn v_N var_x) ->
    (v_shape == (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) ->
    wf_vrelop_ v_shape (.mk_vrelop__0 v_Jnn v_N var_x)
  | vrelop__case_1 : forall (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vrelop_Fnn_N), 
    (v_shape == (.X (lanetype_Fnn v_Fnn) (.mk_dim v_N))) ->
    wf_vrelop_ v_shape (.mk_vrelop__1 v_Fnn v_N var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 -/
def proj_vrelop__0 : ∀  (var_x : vrelop_) , (Option vrelop_Jnn_N)
  | (.mk_vrelop__0 v_Jnn v_N var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:354.1-354.22 -/
def proj_vrelop__1 : ∀  (var_x : vrelop_) , (Option vrelop_Fnn_N)
  | (.mk_vrelop__1 v_Fnn v_N var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:362.1-362.48 -/
inductive half : Type where
  | LOW : half
  | HIGH : half
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:363.1-363.19 -/
inductive zero : Type where
  | ZERO : zero
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:365.1-365.99 -/
inductive vcvtop : Type where
  | EXTEND (v_half : half) (v_sx : sx) : vcvtop
  | TRUNC_SAT (v_sx : sx) (zero_opt : (Option zero)) : vcvtop
  | CONVERT (half_opt : (Option half)) (v_sx : sx) : vcvtop
  | DEMOTE (v_zero : zero) : vcvtop
  | PROMOTELOW : vcvtop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 -/
inductive vshiftop_Jnn_N : Type where
  | SHL : vshiftop_Jnn_N
  | SHR (v_sx : sx) : vshiftop_Jnn_N
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 -/
inductive vshiftop_ : Type where
  | mk_vshiftop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vshiftop_Jnn_N) : vshiftop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.8-367.18 -/
inductive wf_vshiftop_ : ishape -> vshiftop_ -> Prop where
  | vshiftop__case_0 : forall (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vshiftop_Jnn_N), 
    (v_ishape == (.X v_Jnn (.mk_dim v_N))) ->
    wf_vshiftop_ v_ishape (.mk_vshiftop__0 v_Jnn v_N var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.25 -/
def proj_vshiftop__0 : ∀  (var_x : vshiftop_) , vshiftop_Jnn_N
  | (.mk_vshiftop__0 v_Jnn v_N var_x) =>
    var_x


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 -/
inductive vextunop_Jnn_N : Type where
  | EXTADD_PAIRWISE (v_sx : sx) : vextunop_Jnn_N
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.8-370.18 -/
inductive wf_vextunop_Jnn_N : Jnn -> N -> vextunop_Jnn_N -> Prop where
  | vextunop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : N) (v_sx : sx), 
    ((16 <= (lsizenn (lanetype_Jnn v_Jnn))) && ((lsizenn (lanetype_Jnn v_Jnn)) <= 32)) ->
    wf_vextunop_Jnn_N v_Jnn v_N (.EXTADD_PAIRWISE v_sx)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 -/
inductive vextunop_ : Type where
  | mk_vextunop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vextunop_Jnn_N) : vextunop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.8-370.18 -/
inductive wf_vextunop_ : ishape -> vextunop_ -> Prop where
  | vextunop__case_0 : forall (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vextunop_Jnn_N), 
    (wf_vextunop_Jnn_N v_Jnn v_N var_x) ->
    (v_ishape == (.X v_Jnn (.mk_dim v_N))) ->
    wf_vextunop_ v_ishape (.mk_vextunop__0 v_Jnn v_N var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.25 -/
def proj_vextunop__0 : ∀  (var_x : vextunop_) , vextunop_Jnn_N
  | (.mk_vextunop__0 v_Jnn v_N var_x) =>
    var_x


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 -/
inductive vextbinop_Jnn_N : Type where
  | EXTMUL (v_half : half) (v_sx : sx) : vextbinop_Jnn_N
  | DOTS : vextbinop_Jnn_N
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.8-373.19 -/
inductive wf_vextbinop_Jnn_N : Jnn -> N -> vextbinop_Jnn_N -> Prop where
  | vextbinop_Jnn_N_case_0 : forall (v_Jnn : Jnn) (v_N : N) (v_half : half) (v_sx : sx), wf_vextbinop_Jnn_N v_Jnn v_N (.EXTMUL v_half v_sx)
  | vextbinop_Jnn_N_case_1 : forall (v_Jnn : Jnn) (v_N : N), 
    ((lsizenn (lanetype_Jnn v_Jnn)) == 32) ->
    wf_vextbinop_Jnn_N v_Jnn v_N .DOTS

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 -/
inductive vextbinop_ : Type where
  | mk_vextbinop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vextbinop_Jnn_N) : vextbinop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.8-373.19 -/
inductive wf_vextbinop_ : ishape -> vextbinop_ -> Prop where
  | vextbinop__case_0 : forall (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vextbinop_Jnn_N), 
    (wf_vextbinop_Jnn_N v_Jnn v_N var_x) ->
    (v_ishape == (.X v_Jnn (.mk_dim v_N))) ->
    wf_vextbinop_ v_ishape (.mk_vextbinop__0 v_Jnn v_N var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:373.1-373.26 -/
def proj_vextbinop__0 : ∀  (var_x : vextbinop_) , vextbinop_Jnn_N
  | (.mk_vextbinop__0 v_Jnn v_N var_x) =>
    var_x


/- Record Creation Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.1-381.69 -/
structure memarg where MKmemarg ::
  ALIGN : u32
  OFFSET : u32
deriving Inhabited, BEq

def _append_memarg (arg1 arg2 : (memarg)) : memarg where
  ALIGN := arg1.ALIGN /- FIXME - Non-trivial append -/
  OFFSET := arg1.OFFSET /- FIXME - Non-trivial append -/
instance : Append memarg where
  append arg1 arg2 := _append_memarg arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:381.8-381.14 -/
inductive wf_memarg : memarg -> Prop where
  | memarg_case_ : forall (var_0 : u32) (var_1 : u32), 
    (wf_uN 32 var_0) ->
    (wf_uN 32 var_1) ->
    wf_memarg { ALIGN := var_0, OFFSET := var_1 }

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 -/
inductive loadop_Inn : Type where
  | mk_loadop_Inn (v_sz : sz) (v_sx : sx) : loadop_Inn
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.8-385.16 -/
inductive wf_loadop_Inn : Inn -> loadop_Inn -> Prop where
  | loadop_Inn_case_0 : forall (v_Inn : Inn) (v_sz : sz) (v_sx : sx), 
    (wf_sz v_sz) ->
    ((proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn))) ->
    wf_loadop_Inn v_Inn (.mk_loadop_Inn v_sz v_sx)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 -/
inductive loadop_ : Type where
  | mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.8-385.16 -/
inductive wf_loadop_ : numtype -> loadop_ -> Prop where
  | loadop__case_0 : forall (v_numtype : numtype) (v_Inn : Inn) (var_x : loadop_Inn), 
    (wf_loadop_Inn v_Inn var_x) ->
    (v_numtype == (numtype_Inn v_Inn)) ->
    wf_loadop_ v_numtype (.mk_loadop__0 v_Inn var_x)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:385.1-385.24 -/
def proj_loadop__0 : ∀  (var_x : loadop_) , loadop_Inn
  | (.mk_loadop__0 v_Inn var_x) =>
    var_x


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:388.1-391.46 -/
inductive vloadop : Type where
  | SHAPEX_ (nat : Nat) (_ : Nat) (v_sx : sx) : vloadop
  | SPLAT (nat : Nat) : vloadop
  | ZERO (nat : Nat) : vloadop
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:398.1-400.17 -/
inductive blocktype : Type where
  | _RESULT (valtype_opt : (Option valtype)) : blocktype
  | _IDX (v_typeidx : typeidx) : blocktype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:398.8-398.17 -/
inductive wf_blocktype : blocktype -> Prop where
  | blocktype_case_0 : forall (valtype_opt : (Option valtype)), wf_blocktype (._RESULT valtype_opt)
  | blocktype_case_1 : forall (v_typeidx : typeidx), 
    (wf_uN 32 v_typeidx) ->
    wf_blocktype (._IDX v_typeidx)

/- Recursive Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 -/
/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:519.1-520.22 -/
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
  | CALL (v_funcidx : funcidx) : instr
  | CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : instr
  | RETURN : instr
  | CONST (v_numtype : numtype) (v_num_ : num_) : instr
  | UNOP (v_numtype : numtype) (v_unop_ : unop_) : instr
  | BINOP (v_numtype : numtype) (v_binop_ : binop_) : instr
  | TESTOP (v_numtype : numtype) (v_testop_ : testop_) : instr
  | RELOP (v_numtype : numtype) (v_relop_ : relop_) : instr
  | CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop) : instr
  | EXTEND (v_numtype : numtype) (v_n : n) : instr
  | VCONST (v_vectype : vectype) (v_vec_ : vec_) : instr
  | VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : instr
  | VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : instr
  | VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : instr
  | VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : instr
  | VUNOP (v_shape : shape) (v_vunop_ : vunop_) : instr
  | VBINOP (v_shape : shape) (v_vbinop_ : vbinop_) : instr
  | VTESTOP (v_shape : shape) (v_vtestop_ : vtestop_) : instr
  | VRELOP (v_shape : shape) (v_vrelop_ : vrelop_) : instr
  | VSHIFTOP (v_ishape : ishape) (v_vshiftop_ : vshiftop_) : instr
  | VBITMASK (v_ishape : ishape) : instr
  | VSWIZZLE (v_ishape : ishape) : instr
  | VSHUFFLE (v_ishape : ishape) (laneidx_lst : (List laneidx)) : instr
  | VSPLAT (v_shape : shape) : instr
  | VEXTRACT_LANE (v_shape : shape) (sx_opt : (Option sx)) (v_laneidx : laneidx) : instr
  | VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : instr
  | VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop_ : vextunop_) : instr
  | VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop_ : vextbinop_) : instr
  | VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : instr
  | VCVTOP (v_shape : shape) (_ : shape) (v_vcvtop : vcvtop) : instr
  | REF_NULL (v_reftype : reftype) : instr
  | REF_FUNC (v_funcidx : funcidx) : instr
  | REF_IS_NULL : instr
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
  | LOAD (v_numtype : numtype) (loadop__opt : (Option loadop_)) (v_memarg : memarg) : instr
  | STORE (v_numtype : numtype) (sz_opt : (Option sz)) (v_memarg : memarg) : instr
  | VLOAD (v_vectype : vectype) (vloadop_opt : (Option vloadop)) (v_memarg : memarg) : instr
  | VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : instr
  | VSTORE (v_vectype : vectype) (v_memarg : memarg) : instr
  | VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : instr
  | MEMORY_SIZE : instr
  | MEMORY_GROW : instr
  | MEMORY_FILL : instr
  | MEMORY_COPY : instr
  | MEMORY_INIT (v_dataidx : dataidx) : instr
  | DATA_DROP (v_dataidx : dataidx) : instr
deriving Inhabited, BEq


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:523.1-524.9 -/
abbrev expr : Type := (List instr)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:536.1-536.59 -/
inductive elemmode : Type where
  | ACTIVE (v_tableidx : tableidx) (v_expr : expr) : elemmode
  | PASSIVE : elemmode
  | DECLARE : elemmode
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:536.8-536.16 -/
inductive wf_elemmode : elemmode -> Prop where
  | elemmode_case_0 : forall (v_tableidx : tableidx) (v_expr : expr), 
    (wf_uN 32 v_tableidx) ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_elemmode (.ACTIVE v_tableidx v_expr)
  | elemmode_case_1 : wf_elemmode .PASSIVE
  | elemmode_case_2 : wf_elemmode .DECLARE

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:537.1-537.47 -/
inductive datamode : Type where
  | ACTIVE (v_memidx : memidx) (v_expr : expr) : datamode
  | PASSIVE : datamode
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:537.8-537.16 -/
inductive wf_datamode : datamode -> Prop where
  | datamode_case_0 : forall (v_memidx : memidx) (v_expr : expr), 
    (wf_uN 32 v_memidx) ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_datamode (.ACTIVE v_memidx v_expr)
  | datamode_case_1 : wf_datamode .PASSIVE

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:539.1-540.16 -/
inductive type : Type where
  | TYPE (v_functype : functype) : type
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:541.1-542.16 -/
inductive «local» : Type where
  | LOCAL (v_valtype : valtype) : «local»
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:543.1-544.27 -/
inductive func : Type where
  | FUNC (v_typeidx : typeidx) (local_lst : (List «local»)) (v_expr : expr) : func
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:543.8-543.12 -/
inductive wf_func : func -> Prop where
  | func_case_0 : forall (v_typeidx : typeidx) (local_lst : (List «local»)) (v_expr : expr), 
    (wf_uN 32 v_typeidx) ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_func (.FUNC v_typeidx local_lst v_expr)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:545.1-546.25 -/
inductive global : Type where
  | GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:545.8-545.14 -/
inductive wf_global : global -> Prop where
  | global_case_0 : forall (v_globaltype : globaltype) (v_expr : expr), 
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_global (.GLOBAL v_globaltype v_expr)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:547.1-548.18 -/
inductive table : Type where
  | TABLE (v_tabletype : tabletype) : table
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:547.8-547.13 -/
inductive wf_table : table -> Prop where
  | table_case_0 : forall (v_tabletype : tabletype), 
    (wf_tabletype v_tabletype) ->
    wf_table (.TABLE v_tabletype)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:549.1-550.17 -/
inductive mem : Type where
  | MEMORY (v_memtype : memtype) : mem
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:549.8-549.11 -/
inductive wf_mem : mem -> Prop where
  | mem_case_0 : forall (v_memtype : memtype), 
    (wf_memtype v_memtype) ->
    wf_mem (.MEMORY v_memtype)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.1-552.30 -/
inductive elem : Type where
  | ELEM (v_reftype : reftype) (expr_lst : (List expr)) (v_elemmode : elemmode) : elem
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:551.8-551.12 -/
inductive wf_elem : elem -> Prop where
  | elem_case_0 : forall (v_reftype : reftype) (expr_lst : (List expr)) (v_elemmode : elemmode), 
    Forall (fun (v_expr : expr) => Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr) expr_lst ->
    (wf_elemmode v_elemmode) ->
    wf_elem (.ELEM v_reftype expr_lst v_elemmode)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:553.1-554.22 -/
inductive data : Type where
  | DATA (byte_lst : (List byte)) (v_datamode : datamode) : data
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:553.8-553.12 -/
inductive wf_data : data -> Prop where
  | data_case_0 : forall (byte_lst : (List byte)) (v_datamode : datamode), 
    Forall (fun (v_byte : byte) => (wf_byte v_byte)) byte_lst ->
    (wf_datamode v_datamode) ->
    wf_data (.DATA byte_lst v_datamode)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:555.1-556.16 -/
inductive start : Type where
  | START (v_funcidx : funcidx) : start
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:555.8-555.13 -/
inductive wf_start : start -> Prop where
  | start_case_0 : forall (v_funcidx : funcidx), 
    (wf_uN 32 v_funcidx) ->
    wf_start (.START v_funcidx)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.1-559.66 -/
inductive externidx : Type where
  | FUNC (v_funcidx : funcidx) : externidx
  | GLOBAL (v_globalidx : globalidx) : externidx
  | TABLE (v_tableidx : tableidx) : externidx
  | MEM (v_memidx : memidx) : externidx
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.8-558.17 -/
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

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.1-561.24 -/
inductive «export» : Type where
  | EXPORT (v_name : name) (v_externidx : externidx) : «export»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.8-560.14 -/
inductive wf_export : «export» -> Prop where
  | export_case_0 : forall (v_name : name) (v_externidx : externidx), 
    (wf_name v_name) ->
    (wf_externidx v_externidx) ->
    wf_export (.EXPORT v_name v_externidx)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:562.1-563.30 -/
inductive «import» : Type where
  | IMPORT (v_name : name) (_ : name) (v_externtype : externtype) : «import»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:562.8-562.14 -/
inductive wf_import : «import» -> Prop where
  | import_case_0 : forall (v_name : name) (v_externtype : externtype) (var_0 : name), 
    (wf_name v_name) ->
    (wf_externtype v_externtype) ->
    (wf_name var_0) ->
    wf_import (.IMPORT v_name var_0 v_externtype)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.1-566.76 -/
inductive module : Type where
  | MODULE (type_lst : (List type)) (import_lst : (List «import»)) (func_lst : (List func)) (global_lst : (List global)) (table_lst : (List table)) (mem_lst : (List mem)) (elem_lst : (List elem)) (data_lst : (List data)) (start_opt : (Option start)) (export_lst : (List «export»)) : module
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.8-565.14 -/
inductive wf_module : module -> Prop where
  | module_case_0 : forall (type_lst : (List type)) (import_lst : (List «import»)) (func_lst : (List func)) (global_lst : (List global)) (table_lst : (List table)) (mem_lst : (List mem)) (elem_lst : (List elem)) (data_lst : (List data)) (start_opt : (Option start)) (export_lst : (List «export»)), 
    Forall (fun (v_import : «import») => (wf_import v_import)) import_lst ->
    Forall (fun (v_func : func) => (wf_func v_func)) func_lst ->
    Forall (fun (v_global : global) => (wf_global v_global)) global_lst ->
    Forall (fun (v_table : table) => (wf_table v_table)) table_lst ->
    Forall (fun (v_mem : mem) => (wf_mem v_mem)) mem_lst ->
    Forall (fun (v_elem : elem) => (wf_elem v_elem)) elem_lst ->
    Forall (fun (v_data : data) => (wf_data v_data)) data_lst ->
    Forall (fun (v_start : start) => (wf_start v_start)) (Option.toList start_opt) ->
    Forall (fun (v_export : «export») => (wf_export v_export)) export_lst ->
    wf_module (.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)

/- Recursive Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.1-7.59 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.6-7.19 -/
inductive fun_concat_bytes : (List (List byte)) -> (List byte) -> Prop where
  | fun_concat_bytes_case_0 : fun_concat_bytes [] []
  | fun_concat_bytes_case_1 : forall (b_lst : (List byte)) (b'_lst_lst : (List (List byte))) (var_0 : (List byte)), 
    (fun_concat_bytes b'_lst_lst var_0) ->
    fun_concat_bytes ([b_lst] ++ b'_lst_lst) (b_lst ++ var_0)

/- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:28.1-28.32 -/
def unpack : ∀  (v_lanetype : lanetype) , numtype
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


/- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:44.1-44.54 -/
def shunpack : ∀  (v_shape : shape) , numtype
  | (.X v_Lnn (.mk_dim v_N)) =>
    (unpack v_Lnn)


/- Recursive Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.1-51.64 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.6-51.14 -/
inductive fun_funcsxt : (List externtype) -> (List functype) -> Prop where
  | fun_funcsxt_case_0 : fun_funcsxt [] []
  | fun_funcsxt_case_1 : forall (ft : functype) (xt_lst : (List externtype)) (var_0 : (List functype)), 
    (fun_funcsxt xt_lst var_0) ->
    fun_funcsxt ([(.FUNC ft)] ++ xt_lst) ([ft] ++ var_0)
  | fun_funcsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List functype)), 
    (fun_funcsxt xt_lst var_0) ->
    fun_funcsxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.1-52.66 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.6-52.16 -/
inductive fun_globalsxt : (List externtype) -> (List globaltype) -> Prop where
  | fun_globalsxt_case_0 : fun_globalsxt [] []
  | fun_globalsxt_case_1 : forall (gt : globaltype) (xt_lst : (List externtype)) (var_0 : (List globaltype)), 
    (fun_globalsxt xt_lst var_0) ->
    fun_globalsxt ([(.GLOBAL gt)] ++ xt_lst) ([gt] ++ var_0)
  | fun_globalsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List globaltype)), 
    (fun_globalsxt xt_lst var_0) ->
    fun_globalsxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.1-53.65 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.6-53.15 -/
inductive fun_tablesxt : (List externtype) -> (List tabletype) -> Prop where
  | fun_tablesxt_case_0 : fun_tablesxt [] []
  | fun_tablesxt_case_1 : forall (tt : tabletype) (xt_lst : (List externtype)) (var_0 : (List tabletype)), 
    (fun_tablesxt xt_lst var_0) ->
    fun_tablesxt ([(.TABLE tt)] ++ xt_lst) ([tt] ++ var_0)
  | fun_tablesxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List tabletype)), 
    (fun_tablesxt xt_lst var_0) ->
    fun_tablesxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.1-54.63 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.6-54.13 -/
inductive fun_memsxt : (List externtype) -> (List memtype) -> Prop where
  | fun_memsxt_case_0 : fun_memsxt [] []
  | fun_memsxt_case_1 : forall (mt : memtype) (xt_lst : (List externtype)) (var_0 : (List memtype)), 
    (fun_memsxt xt_lst var_0) ->
    fun_memsxt ([(.MEM mt)] ++ xt_lst) ([mt] ++ var_0)
  | fun_memsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List memtype)), 
    (fun_memsxt xt_lst var_0) ->
    fun_memsxt ([v_externtype] ++ xt_lst) var_0

/- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61 -/
def dataidx_instr : ∀  (v_instr : instr) , (List dataidx)
  | (.MEMORY_INIT x) =>
    [x]
  | (.DATA_DROP x) =>
    [x]
  | in =>
    []


/- Recursive Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.1-85.63 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.6-85.21 -/
inductive fun_dataidx_instrs : (List instr) -> (List dataidx) -> Prop where
  | fun_dataidx_instrs_case_0 : fun_dataidx_instrs [] []
  | fun_dataidx_instrs_case_1 : forall (v_instr : instr) (instr'_lst : (List instr)) (var_0 : (List dataidx)), 
    (fun_dataidx_instrs instr'_lst var_0) ->
    fun_dataidx_instrs ([v_instr] ++ instr'_lst) ((dataidx_instr v_instr) ++ var_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 -/
inductive fun_dataidx_expr : expr -> (List dataidx) -> Prop where
  | fun_dataidx_expr_case_0 : forall (in_lst : (List instr)) (var_0 : (List dataidx)), 
    (fun_dataidx_instrs in_lst var_0) ->
    fun_dataidx_expr in_lst var_0

/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 -/
inductive fun_dataidx_func : func -> (List dataidx) -> Prop where
  | fun_dataidx_func_case_0 : forall (x : uN) (loc_lst : (List «local»)) (e : (List instr)) (var_0 : (List dataidx)), 
    (fun_dataidx_expr e var_0) ->
    fun_dataidx_func (.FUNC x loc_lst e) var_0

/- Recursive Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.1-95.61 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.6-95.20 -/
inductive fun_dataidx_funcs : (List func) -> (List dataidx) -> Prop where
  | fun_dataidx_funcs_case_0 : fun_dataidx_funcs [] []
  | fun_dataidx_funcs_case_1 : forall (v_func : func) (func'_lst : (List func)) (var_1 : (List dataidx)) (var_0 : (List dataidx)), 
    (fun_dataidx_funcs func'_lst var_1) ->
    (fun_dataidx_func v_func var_0) ->
    fun_dataidx_funcs ([v_func] ++ func'_lst) (var_0 ++ var_1)

/- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35 -/
def memarg0 : memarg := { ALIGN := (.mk_uN 0), OFFSET := (.mk_uN 0) }

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41 -/
opaque s33_to_u32 : forall (v_s33 : s33), u32 := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22 -/
def nat_of_bool : ∀  (v_bool : Bool) , Nat
  | false =>
    0
  | true =>
    1


/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23 -/
opaque truncz : forall (rat : Nat), Nat := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:20.6-20.14 -/
inductive fun_signed_ : N -> Nat -> Nat -> Prop where
  | fun_signed__case_0 : forall (v_N : Nat) (i : Nat), 
    (i < (2 ^ (((v_N : Nat) - (1 : Nat)) : Nat))) ->
    fun_signed_ v_N i (i : Nat)
  | fun_signed__case_1 : forall (v_N : Nat) (i : Nat), 
    (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) <= i) && (i < (2 ^ v_N))) ->
    fun_signed_ v_N i ((i : Nat) - ((2 ^ v_N) : Nat))

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:24.6-24.18 -/
inductive fun_inv_signed_ : N -> Nat -> Nat -> Prop where
  | fun_inv_signed__case_0 : forall (v_N : Nat) (i : Nat), 
    (((0 : Nat) <= i) && (i < ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat))) ->
    fun_inv_signed_ v_N i (i : Nat)
  | fun_inv_signed__case_1 : forall (v_N : Nat) (i : Nat), 
    (((0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat)) <= i) && (i < (0 : Nat))) ->
    fun_inv_signed_ v_N i ((i + ((2 ^ v_N) : Nat)) : Nat)

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61 -/
def sat_u_ : ∀  (v_N : N) (int : Nat) , Nat
  | v_N, i =>
    (if (i < (0 : Nat)) then 0 else (if (i > (((2 ^ v_N) : Nat) - (1 : Nat))) then ((((2 ^ v_N) : Nat) - (1 : Nat)) : Nat) else (i : Nat)))


/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61 -/
def sat_s_ : ∀  (v_N : N) (int : Nat) , Nat
  | v_N, i =>
    (if (i < (0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat))) then (0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat)) else (if (i > (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat) - (1 : Nat))) then (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat) - (1 : Nat)) else i))


/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89 -/
opaque extend__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30 -/
opaque fabs_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31 -/
opaque fceil_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32 -/
opaque ffloor_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34 -/
opaque fnearest_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30 -/
opaque fneg_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31 -/
opaque fsqrt_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32 -/
opaque ftrunc_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29 -/
opaque iclz_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29 -/
opaque ictz_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32 -/
opaque ipopcnt_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33 -/
opaque wrap__ : forall (v_M : M) (v_N : N) (v_iN : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 -/
inductive fun_unop_ : numtype -> unop_ -> num_ -> (List num_) -> Prop where
  | fun_unop__case_0 : forall (v_iN : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (iclz_ (sizenn (numtype_Inn .I32)) v_iN))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .CLZ) (.mk_num__0 .I32 v_iN) [(.mk_num__0 .I32 (iclz_ (sizenn (numtype_Inn .I32)) v_iN))]
  | fun_unop__case_1 : forall (v_iN : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (iclz_ (sizenn (numtype_Inn .I64)) v_iN))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .CLZ) (.mk_num__0 .I64 v_iN) [(.mk_num__0 .I64 (iclz_ (sizenn (numtype_Inn .I64)) v_iN))]
  | fun_unop__case_2 : forall (v_iN : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (ictz_ (sizenn (numtype_Inn .I32)) v_iN))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .CTZ) (.mk_num__0 .I32 v_iN) [(.mk_num__0 .I32 (ictz_ (sizenn (numtype_Inn .I32)) v_iN))]
  | fun_unop__case_3 : forall (v_iN : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (ictz_ (sizenn (numtype_Inn .I64)) v_iN))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .CTZ) (.mk_num__0 .I64 v_iN) [(.mk_num__0 .I64 (ictz_ (sizenn (numtype_Inn .I64)) v_iN))]
  | fun_unop__case_4 : forall (v_iN : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (ipopcnt_ (sizenn (numtype_Inn .I32)) v_iN))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .POPCNT) (.mk_num__0 .I32 v_iN) [(.mk_num__0 .I32 (ipopcnt_ (sizenn (numtype_Inn .I32)) v_iN))]
  | fun_unop__case_5 : forall (v_iN : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (ipopcnt_ (sizenn (numtype_Inn .I64)) v_iN))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .POPCNT) (.mk_num__0 .I64 v_iN) [(.mk_num__0 .I64 (ipopcnt_ (sizenn (numtype_Inn .I64)) v_iN))]
  | fun_unop__case_6 : forall (v_M : Nat) (v_iN : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (extend__ v_M (sizenn (numtype_Inn .I32)) .S (wrap__ (sizenn (numtype_Inn .I32)) v_M v_iN)))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 (.EXTEND v_M)) (.mk_num__0 .I32 v_iN) [(.mk_num__0 .I32 (extend__ v_M (sizenn (numtype_Inn .I32)) .S (wrap__ (sizenn (numtype_Inn .I32)) v_M v_iN)))]
  | fun_unop__case_7 : forall (v_M : Nat) (v_iN : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (extend__ v_M (sizenn (numtype_Inn .I64)) .S (wrap__ (sizenn (numtype_Inn .I64)) v_M v_iN)))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 (.EXTEND v_M)) (.mk_num__0 .I64 v_iN) [(.mk_num__0 .I64 (extend__ v_M (sizenn (numtype_Inn .I64)) .S (wrap__ (sizenn (numtype_Inn .I64)) v_M v_iN)))]
  | fun_unop__case_8 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fabs_ (sizenn (numtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .ABS) (.mk_num__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fabs_ (sizenn (numtype_Fnn .F32)) v_fN))
  | fun_unop__case_9 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fabs_ (sizenn (numtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .ABS) (.mk_num__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fabs_ (sizenn (numtype_Fnn .F64)) v_fN))
  | fun_unop__case_10 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fneg_ (sizenn (numtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEG) (.mk_num__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fneg_ (sizenn (numtype_Fnn .F32)) v_fN))
  | fun_unop__case_11 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fneg_ (sizenn (numtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEG) (.mk_num__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fneg_ (sizenn (numtype_Fnn .F64)) v_fN))
  | fun_unop__case_12 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fsqrt_ (sizenn (numtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .SQRT) (.mk_num__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fsqrt_ (sizenn (numtype_Fnn .F32)) v_fN))
  | fun_unop__case_13 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fsqrt_ (sizenn (numtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .SQRT) (.mk_num__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fsqrt_ (sizenn (numtype_Fnn .F64)) v_fN))
  | fun_unop__case_14 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fceil_ (sizenn (numtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .CEIL) (.mk_num__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fceil_ (sizenn (numtype_Fnn .F32)) v_fN))
  | fun_unop__case_15 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fceil_ (sizenn (numtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .CEIL) (.mk_num__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fceil_ (sizenn (numtype_Fnn .F64)) v_fN))
  | fun_unop__case_16 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (ffloor_ (sizenn (numtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .FLOOR) (.mk_num__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (ffloor_ (sizenn (numtype_Fnn .F32)) v_fN))
  | fun_unop__case_17 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (ffloor_ (sizenn (numtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .FLOOR) (.mk_num__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (ffloor_ (sizenn (numtype_Fnn .F64)) v_fN))
  | fun_unop__case_18 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (ftrunc_ (sizenn (numtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .TRUNC) (.mk_num__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (ftrunc_ (sizenn (numtype_Fnn .F32)) v_fN))
  | fun_unop__case_19 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (ftrunc_ (sizenn (numtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .TRUNC) (.mk_num__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (ftrunc_ (sizenn (numtype_Fnn .F64)) v_fN))
  | fun_unop__case_20 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fnearest_ (sizenn (numtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEAREST) (.mk_num__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fnearest_ (sizenn (numtype_Fnn .F32)) v_fN))
  | fun_unop__case_21 : forall (v_fN : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fnearest_ (sizenn (numtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEAREST) (.mk_num__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fnearest_ (sizenn (numtype_Fnn .F64)) v_fN))

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37 -/
opaque fadd_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42 -/
opaque fcopysign_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37 -/
opaque fdiv_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37 -/
opaque fmax_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37 -/
opaque fmin_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37 -/
opaque fmul_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37 -/
opaque fsub_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36 -/
def iadd_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN (((proj_uN_0 i_1) + (proj_uN_0 i_2)) mod (2 ^ v_N)))


/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36 -/
opaque iand_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 -/
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

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36 -/
def imul_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN (((proj_uN_0 i_1) * (proj_uN_0 i_2)) mod (2 ^ v_N)))


/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35 -/
opaque ior_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 -/
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

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37 -/
opaque irotl_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37 -/
opaque irotr_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.1-116.34 -/
opaque ishl_ : forall (v_N : N) (v_iN : iN) (v_u32 : u32), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.1-117.74 -/
opaque ishr_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32), iN := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36 -/
def isub_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN ((((((2 ^ v_N) + (proj_uN_0 i_1)) : Nat) - ((proj_uN_0 i_2) : Nat)) mod ((2 ^ v_N) : Nat)) : Nat))


/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36 -/
opaque ixor_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 -/
inductive fun_binop_ : numtype -> binop_ -> num_ -> num_ -> (List num_) -> Prop where
  | fun_binop__case_0 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ADD) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (iadd_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_1 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ADD) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (iadd_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_2 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (isub_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .SUB) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (isub_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_3 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (isub_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .SUB) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (isub_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_4 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .MUL) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (imul_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_5 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .MUL) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (imul_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (Option iN)), 
    (fun_idiv_ (sizenn (numtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV v_sx)) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) var_0))
  | fun_binop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (Option iN)), 
    (fun_idiv_ (sizenn (numtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.DIV v_sx)) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) var_0))
  | fun_binop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (Option iN)), 
    (fun_irem_ (sizenn (numtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.REM v_sx)) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) var_0))
  | fun_binop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (Option iN)), 
    (fun_irem_ (sizenn (numtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.REM v_sx)) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) var_0))
  | fun_binop__case_10 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (iand_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .AND) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (iand_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_11 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (iand_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .AND) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (iand_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_12 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (ior_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .OR) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (ior_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_13 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (ior_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .OR) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (ior_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_14 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (ixor_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .XOR) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (ixor_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_15 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (ixor_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .XOR) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (ixor_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_16 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (ishl_ (sizenn (numtype_Inn .I32)) iN_1 (.mk_uN (proj_uN_0 iN_2))))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .SHL) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (ishl_ (sizenn (numtype_Inn .I32)) iN_1 (.mk_uN (proj_uN_0 iN_2))))]
  | fun_binop__case_17 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (ishl_ (sizenn (numtype_Inn .I64)) iN_1 (.mk_uN (proj_uN_0 iN_2))))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .SHL) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (ishl_ (sizenn (numtype_Inn .I64)) iN_1 (.mk_uN (proj_uN_0 iN_2))))]
  | fun_binop__case_18 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (ishr_ (sizenn (numtype_Inn .I32)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2))))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.SHR v_sx)) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (ishr_ (sizenn (numtype_Inn .I32)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2))))]
  | fun_binop__case_19 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (ishr_ (sizenn (numtype_Inn .I64)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2))))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.SHR v_sx)) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (ishr_ (sizenn (numtype_Inn .I64)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2))))]
  | fun_binop__case_20 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (irotl_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ROTL) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (irotl_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_21 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (irotl_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ROTL) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (irotl_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_22 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (irotr_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ROTR) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) [(.mk_num__0 .I32 (irotr_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_23 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (irotr_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ROTR) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) [(.mk_num__0 .I64 (irotr_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_24 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fadd_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .ADD) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fadd_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_25 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fadd_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .ADD) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fadd_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_26 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fsub_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .SUB) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fsub_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_27 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fsub_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .SUB) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fsub_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_28 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmul_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MUL) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fmul_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_29 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmul_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MUL) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fmul_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_30 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fdiv_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .DIV) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fdiv_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_31 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fdiv_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .DIV) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fdiv_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_32 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmin_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MIN) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fmin_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_33 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmin_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MIN) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fmin_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_34 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmax_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MAX) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fmax_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_35 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmax_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MAX) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fmax_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_36 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fcopysign_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .COPYSIGN) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (fcopysign_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_37 : forall (fN_1 : fN) (fN_2 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fcopysign_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .COPYSIGN) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (fcopysign_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27 -/
def ieqz_ : ∀  (v_N : N) (v_iN : iN) , u32
  | v_N, i_1 =>
    (.mk_uN (nat_of_bool ((proj_uN_0 i_1) == 0)))


/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 -/
inductive fun_testop_ : numtype -> testop_ -> num_ -> num_ -> Prop where
  | fun_testop__case_0 : forall (v_iN : uN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (ieqz_ (sizenn (numtype_Inn .I32)) v_iN))) ->
    fun_testop_ .I32 (.mk_testop__0 .I32 .EQZ) (.mk_num__0 .I32 v_iN) (.mk_num__0 .I32 (ieqz_ (sizenn (numtype_Inn .I32)) v_iN))
  | fun_testop__case_1 : forall (v_iN : uN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (ieqz_ (sizenn (numtype_Inn .I64)) v_iN))) ->
    fun_testop_ .I64 (.mk_testop__0 .I64 .EQZ) (.mk_num__0 .I64 v_iN) (.mk_num__0 .I32 (ieqz_ (sizenn (numtype_Inn .I64)) v_iN))

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33 -/
opaque feq_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33 -/
opaque fge_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33 -/
opaque fgt_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33 -/
opaque fle_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33 -/
opaque flt_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33 -/
opaque fne_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33 -/
def ieq_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , u32
  | v_N, i_1, i_2 =>
    (.mk_uN (nat_of_bool (i_1 == i_2)))


/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 -/
inductive fun_ige_ : N -> sx -> iN -> iN -> u32 -> Prop where
  | fun_ige__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_ige_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) >= (proj_uN_0 i_2))))
  | fun_ige__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_ige_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 >= var_1)))

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 -/
inductive fun_igt_ : N -> sx -> iN -> iN -> u32 -> Prop where
  | fun_igt__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_igt_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) > (proj_uN_0 i_2))))
  | fun_igt__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_igt_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 > var_1)))

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 -/
inductive fun_ile_ : N -> sx -> iN -> iN -> u32 -> Prop where
  | fun_ile__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_ile_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) <= (proj_uN_0 i_2))))
  | fun_ile__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_ile_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 <= var_1)))

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 -/
inductive fun_ilt_ : N -> sx -> iN -> iN -> u32 -> Prop where
  | fun_ilt__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_ilt_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) < (proj_uN_0 i_2))))
  | fun_ilt__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_ilt_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 < var_1)))

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33 -/
def ine_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , u32
  | v_N, i_1, i_2 =>
    (.mk_uN (nat_of_bool (i_1 != i_2)))


/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 -/
inductive fun_relop_ : numtype -> relop_ -> num_ -> num_ -> num_ -> Prop where
  | fun_relop__case_0 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (ieq_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 .EQ) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) (.mk_num__0 .I32 (ieq_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))
  | fun_relop__case_1 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (ieq_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 .EQ) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) (.mk_num__0 .I32 (ieq_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))
  | fun_relop__case_2 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (ine_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 .NE) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) (.mk_num__0 .I32 (ine_ (sizenn (numtype_Inn .I32)) iN_1 iN_2))
  | fun_relop__case_3 : forall (iN_1 : uN) (iN_2 : uN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (ine_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 .NE) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) (.mk_num__0 .I32 (ine_ (sizenn (numtype_Inn .I64)) iN_1 iN_2))
  | fun_relop__case_4 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
    (fun_ilt_ (sizenn (numtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    (wf_num_ .I32 (.mk_num__0 .I32 var_0)) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 (.LT v_sx)) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) (.mk_num__0 .I32 var_0)
  | fun_relop__case_5 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
    (fun_ilt_ (sizenn (numtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    (wf_num_ .I32 (.mk_num__0 .I32 var_0)) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 (.LT v_sx)) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) (.mk_num__0 .I32 var_0)
  | fun_relop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
    (fun_igt_ (sizenn (numtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    (wf_num_ .I32 (.mk_num__0 .I32 var_0)) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 (.GT v_sx)) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) (.mk_num__0 .I32 var_0)
  | fun_relop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
    (fun_igt_ (sizenn (numtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    (wf_num_ .I32 (.mk_num__0 .I32 var_0)) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 (.GT v_sx)) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) (.mk_num__0 .I32 var_0)
  | fun_relop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
    (fun_ile_ (sizenn (numtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    (wf_num_ .I32 (.mk_num__0 .I32 var_0)) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 (.LE v_sx)) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) (.mk_num__0 .I32 var_0)
  | fun_relop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
    (fun_ile_ (sizenn (numtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    (wf_num_ .I32 (.mk_num__0 .I32 var_0)) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 (.LE v_sx)) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) (.mk_num__0 .I32 var_0)
  | fun_relop__case_10 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
    (fun_ige_ (sizenn (numtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    (wf_num_ .I32 (.mk_num__0 .I32 var_0)) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 (.GE v_sx)) (.mk_num__0 .I32 iN_1) (.mk_num__0 .I32 iN_2) (.mk_num__0 .I32 var_0)
  | fun_relop__case_11 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN), 
    (fun_ige_ (sizenn (numtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    (wf_num_ .I32 (.mk_num__0 .I32 var_0)) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 (.GE v_sx)) (.mk_num__0 .I64 iN_1) (.mk_num__0 .I64 iN_2) (.mk_num__0 .I32 var_0)
  | fun_relop__case_12 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (feq_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .EQ) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (.mk_num__0 .I32 (feq_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_13 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (feq_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .EQ) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (.mk_num__0 .I32 (feq_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_14 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (fne_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .NE) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (.mk_num__0 .I32 (fne_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_15 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (fne_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .NE) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (.mk_num__0 .I32 (fne_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_16 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (flt_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .LT) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (.mk_num__0 .I32 (flt_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_17 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (flt_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .LT) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (.mk_num__0 .I32 (flt_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_18 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (fgt_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .GT) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (.mk_num__0 .I32 (fgt_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_19 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (fgt_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .GT) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (.mk_num__0 .I32 (fgt_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_20 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (fle_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .LE) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (.mk_num__0 .I32 (fle_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_21 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (fle_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .LE) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (.mk_num__0 .I32 (fle_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_22 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (fge_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .GE) (.mk_num__1 .F32 fN_1) (.mk_num__1 .F32 fN_2) (.mk_num__0 .I32 (fge_ (sizenn (numtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_23 : forall (fN_1 : fN) (fN_2 : fN), 
    (wf_num_ .I32 (.mk_num__0 .I32 (fge_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .GE) (.mk_num__1 .F64 fN_1) (.mk_num__1 .F64 fN_2) (.mk_num__0 .I32 (fge_ (sizenn (numtype_Fnn .F64)) fN_1 fN_2))

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90 -/
opaque convert__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN), fN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36 -/
opaque demote__ : forall (v_M : M) (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37 -/
opaque promote__ : forall (v_M : M) (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76 -/
opaque reinterpret__ : forall (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_), num_ := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88 -/
opaque trunc__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN), (Option iN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93 -/
opaque trunc_sat__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN), (Option iN) := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 -/
inductive fun_cvtop__ : numtype -> numtype -> cvtop -> num_ -> (List num_) -> Prop where
  | fun_cvtop___case_0 : forall (v_sx : sx) (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (extend__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Inn .I32)) v_sx iN_1))) ->
    fun_cvtop__ .I32 .I32 (.EXTEND v_sx) (.mk_num__0 .I32 iN_1) [(.mk_num__0 .I32 (extend__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Inn .I32)) v_sx iN_1))]
  | fun_cvtop___case_1 : forall (v_sx : sx) (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (extend__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Inn .I32)) v_sx iN_1))) ->
    fun_cvtop__ .I64 .I32 (.EXTEND v_sx) (.mk_num__0 .I64 iN_1) [(.mk_num__0 .I32 (extend__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Inn .I32)) v_sx iN_1))]
  | fun_cvtop___case_2 : forall (v_sx : sx) (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (extend__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Inn .I64)) v_sx iN_1))) ->
    fun_cvtop__ .I32 .I64 (.EXTEND v_sx) (.mk_num__0 .I32 iN_1) [(.mk_num__0 .I64 (extend__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Inn .I64)) v_sx iN_1))]
  | fun_cvtop___case_3 : forall (v_sx : sx) (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (extend__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Inn .I64)) v_sx iN_1))) ->
    fun_cvtop__ .I64 .I64 (.EXTEND v_sx) (.mk_num__0 .I64 iN_1) [(.mk_num__0 .I64 (extend__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Inn .I64)) v_sx iN_1))]
  | fun_cvtop___case_4 : forall (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Inn .I32)) iN_1))) ->
    fun_cvtop__ .I32 .I32 .WRAP (.mk_num__0 .I32 iN_1) [(.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Inn .I32)) iN_1))]
  | fun_cvtop___case_5 : forall (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Inn .I32)) iN_1))) ->
    fun_cvtop__ .I64 .I32 .WRAP (.mk_num__0 .I64 iN_1) [(.mk_num__0 .I32 (wrap__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Inn .I32)) iN_1))]
  | fun_cvtop___case_6 : forall (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Inn .I64)) iN_1))) ->
    fun_cvtop__ .I32 .I64 .WRAP (.mk_num__0 .I32 iN_1) [(.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Inn .I64)) iN_1))]
  | fun_cvtop___case_7 : forall (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Inn .I64)) iN_1))) ->
    fun_cvtop__ .I64 .I64 .WRAP (.mk_num__0 .I64 iN_1) [(.mk_num__0 .I64 (wrap__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Inn .I64)) iN_1))]
  | fun_cvtop___case_8 : forall (v_sx : sx) (fN_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 iter_0))) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Inn .I32)) v_sx fN_1)) ->
    fun_cvtop__ .F32 .I32 (.TRUNC v_sx) (.mk_num__1 .F32 fN_1) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Inn .I32)) v_sx fN_1)))
  | fun_cvtop___case_9 : forall (v_sx : sx) (fN_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 iter_0))) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Inn .I32)) v_sx fN_1)) ->
    fun_cvtop__ .F64 .I32 (.TRUNC v_sx) (.mk_num__1 .F64 fN_1) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Inn .I32)) v_sx fN_1)))
  | fun_cvtop___case_10 : forall (v_sx : sx) (fN_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 iter_0))) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Inn .I64)) v_sx fN_1)) ->
    fun_cvtop__ .F32 .I64 (.TRUNC v_sx) (.mk_num__1 .F32 fN_1) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (trunc__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Inn .I64)) v_sx fN_1)))
  | fun_cvtop___case_11 : forall (v_sx : sx) (fN_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 iter_0))) (Option.toList (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Inn .I64)) v_sx fN_1)) ->
    fun_cvtop__ .F64 .I64 (.TRUNC v_sx) (.mk_num__1 .F64 fN_1) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (trunc__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Inn .I64)) v_sx fN_1)))
  | fun_cvtop___case_12 : forall (v_sx : sx) (fN_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 iter_0))) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Inn .I32)) v_sx fN_1)) ->
    fun_cvtop__ .F32 .I32 (.TRUNC_SAT v_sx) (.mk_num__1 .F32 fN_1) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Inn .I32)) v_sx fN_1)))
  | fun_cvtop___case_13 : forall (v_sx : sx) (fN_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 iter_0))) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Inn .I32)) v_sx fN_1)) ->
    fun_cvtop__ .F64 .I32 (.TRUNC_SAT v_sx) (.mk_num__1 .F64 fN_1) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I32 iter_0)) (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Inn .I32)) v_sx fN_1)))
  | fun_cvtop___case_14 : forall (v_sx : sx) (fN_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 iter_0))) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Inn .I64)) v_sx fN_1)) ->
    fun_cvtop__ .F32 .I64 (.TRUNC_SAT v_sx) (.mk_num__1 .F32 fN_1) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (trunc_sat__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Inn .I64)) v_sx fN_1)))
  | fun_cvtop___case_15 : forall (v_sx : sx) (fN_1 : fN), 
    Forall (fun (iter_0 : iN) => (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 iter_0))) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Inn .I64)) v_sx fN_1)) ->
    fun_cvtop__ .F64 .I64 (.TRUNC_SAT v_sx) (.mk_num__1 .F64 fN_1) (list_ num_ (Option.map (fun (iter_0 : iN) => (.mk_num__0 .I64 iter_0)) (trunc_sat__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Inn .I64)) v_sx fN_1)))
  | fun_cvtop___case_16 : forall (v_sx : sx) (iN_1 : uN), 
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 (convert__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Fnn .F32)) v_sx iN_1))) ->
    fun_cvtop__ .I32 .F32 (.CONVERT v_sx) (.mk_num__0 .I32 iN_1) [(.mk_num__1 .F32 (convert__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Fnn .F32)) v_sx iN_1))]
  | fun_cvtop___case_17 : forall (v_sx : sx) (iN_1 : uN), 
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 (convert__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Fnn .F32)) v_sx iN_1))) ->
    fun_cvtop__ .I64 .F32 (.CONVERT v_sx) (.mk_num__0 .I64 iN_1) [(.mk_num__1 .F32 (convert__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Fnn .F32)) v_sx iN_1))]
  | fun_cvtop___case_18 : forall (v_sx : sx) (iN_1 : uN), 
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 (convert__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Fnn .F64)) v_sx iN_1))) ->
    fun_cvtop__ .I32 .F64 (.CONVERT v_sx) (.mk_num__0 .I32 iN_1) [(.mk_num__1 .F64 (convert__ (sizenn1 (numtype_Inn .I32)) (sizenn2 (numtype_Fnn .F64)) v_sx iN_1))]
  | fun_cvtop___case_19 : forall (v_sx : sx) (iN_1 : uN), 
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 (convert__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Fnn .F64)) v_sx iN_1))) ->
    fun_cvtop__ .I64 .F64 (.CONVERT v_sx) (.mk_num__0 .I64 iN_1) [(.mk_num__1 .F64 (convert__ (sizenn1 (numtype_Inn .I64)) (sizenn2 (numtype_Fnn .F64)) v_sx iN_1))]
  | fun_cvtop___case_20 : forall (fN_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) fN_1) ->
    fun_cvtop__ .F32 .F32 .PROMOTE (.mk_num__1 .F32 fN_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) fN_1))
  | fun_cvtop___case_21 : forall (fN_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) fN_1) ->
    fun_cvtop__ .F64 .F32 .PROMOTE (.mk_num__1 .F64 fN_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) fN_1))
  | fun_cvtop___case_22 : forall (fN_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) fN_1) ->
    fun_cvtop__ .F32 .F64 .PROMOTE (.mk_num__1 .F32 fN_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (promote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) fN_1))
  | fun_cvtop___case_23 : forall (fN_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) fN_1) ->
    fun_cvtop__ .F64 .F64 .PROMOTE (.mk_num__1 .F64 fN_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (promote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) fN_1))
  | fun_cvtop___case_24 : forall (fN_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) fN_1) ->
    fun_cvtop__ .F32 .F32 .DEMOTE (.mk_num__1 .F32 fN_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F32)) fN_1))
  | fun_cvtop___case_25 : forall (fN_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) fN_1) ->
    fun_cvtop__ .F64 .F32 .DEMOTE (.mk_num__1 .F64 fN_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F32 iter_0)) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F32)) fN_1))
  | fun_cvtop___case_26 : forall (fN_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) fN_1) ->
    fun_cvtop__ .F32 .F64 .DEMOTE (.mk_num__1 .F32 fN_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (demote__ (sizenn1 (numtype_Fnn .F32)) (sizenn2 (numtype_Fnn .F64)) fN_1))
  | fun_cvtop___case_27 : forall (fN_1 : fN), 
    Forall (fun (iter_0 : fN) => (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) fN_1) ->
    fun_cvtop__ .F64 .F64 .DEMOTE (.mk_num__1 .F64 fN_1) (List.map (fun (iter_0 : fN) => (.mk_num__1 .F64 iter_0)) (demote__ (sizenn1 (numtype_Fnn .F64)) (sizenn2 (numtype_Fnn .F64)) fN_1))
  | fun_cvtop___case_28 : forall (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 iN_1)) ->
    ((size (valtype_Inn .I32)) != none) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((Option.get! (size (valtype_Inn .I32))) == (Option.get! (size (valtype_Fnn .F32)))) ->
    fun_cvtop__ .I32 .F32 .REINTERPRET (.mk_num__0 .I32 iN_1) [(reinterpret__ (numtype_Inn .I32) (numtype_Fnn .F32) (.mk_num__0 .I32 iN_1))]
  | fun_cvtop___case_29 : forall (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 iN_1)) ->
    ((size (valtype_Inn .I64)) != none) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((Option.get! (size (valtype_Inn .I64))) == (Option.get! (size (valtype_Fnn .F32)))) ->
    fun_cvtop__ .I64 .F32 .REINTERPRET (.mk_num__0 .I64 iN_1) [(reinterpret__ (numtype_Inn .I64) (numtype_Fnn .F32) (.mk_num__0 .I64 iN_1))]
  | fun_cvtop___case_30 : forall (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I32) (.mk_num__0 .I32 iN_1)) ->
    ((size (valtype_Inn .I32)) != none) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((Option.get! (size (valtype_Inn .I32))) == (Option.get! (size (valtype_Fnn .F64)))) ->
    fun_cvtop__ .I32 .F64 .REINTERPRET (.mk_num__0 .I32 iN_1) [(reinterpret__ (numtype_Inn .I32) (numtype_Fnn .F64) (.mk_num__0 .I32 iN_1))]
  | fun_cvtop___case_31 : forall (iN_1 : uN), 
    (wf_num_ (numtype_Inn .I64) (.mk_num__0 .I64 iN_1)) ->
    ((size (valtype_Inn .I64)) != none) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((Option.get! (size (valtype_Inn .I64))) == (Option.get! (size (valtype_Fnn .F64)))) ->
    fun_cvtop__ .I64 .F64 .REINTERPRET (.mk_num__0 .I64 iN_1) [(reinterpret__ (numtype_Inn .I64) (numtype_Fnn .F64) (.mk_num__0 .I64 iN_1))]
  | fun_cvtop___case_32 : forall (fN_1 : fN), 
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 fN_1)) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((size (valtype_Inn .I32)) != none) ->
    ((Option.get! (size (valtype_Fnn .F32))) == (Option.get! (size (valtype_Inn .I32)))) ->
    fun_cvtop__ .F32 .I32 .REINTERPRET (.mk_num__1 .F32 fN_1) [(reinterpret__ (numtype_Fnn .F32) (numtype_Inn .I32) (.mk_num__1 .F32 fN_1))]
  | fun_cvtop___case_33 : forall (fN_1 : fN), 
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 fN_1)) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((size (valtype_Inn .I32)) != none) ->
    ((Option.get! (size (valtype_Fnn .F64))) == (Option.get! (size (valtype_Inn .I32)))) ->
    fun_cvtop__ .F64 .I32 .REINTERPRET (.mk_num__1 .F64 fN_1) [(reinterpret__ (numtype_Fnn .F64) (numtype_Inn .I32) (.mk_num__1 .F64 fN_1))]
  | fun_cvtop___case_34 : forall (fN_1 : fN), 
    (wf_num_ (numtype_Fnn .F32) (.mk_num__1 .F32 fN_1)) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((size (valtype_Inn .I64)) != none) ->
    ((Option.get! (size (valtype_Fnn .F32))) == (Option.get! (size (valtype_Inn .I64)))) ->
    fun_cvtop__ .F32 .I64 .REINTERPRET (.mk_num__1 .F32 fN_1) [(reinterpret__ (numtype_Fnn .F32) (numtype_Inn .I64) (.mk_num__1 .F32 fN_1))]
  | fun_cvtop___case_35 : forall (fN_1 : fN), 
    (wf_num_ (numtype_Fnn .F64) (.mk_num__1 .F64 fN_1)) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((size (valtype_Inn .I64)) != none) ->
    ((Option.get! (size (valtype_Fnn .F64))) == (Option.get! (size (valtype_Inn .I64)))) ->
    fun_cvtop__ .F64 .I64 .REINTERPRET (.mk_num__1 .F64 fN_1) [(reinterpret__ (numtype_Fnn .F64) (numtype_Inn .I64) (.mk_num__1 .F64 fN_1))]

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87 -/
opaque narrow__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 -/
opaque ibits_ : forall (v_N : N) (v_iN : iN), (List bit) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102 -/
opaque fbits_ : forall (v_N : N) (v_fN : fN), (List bit) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103 -/
opaque ibytes_ : forall (v_N : N) (v_iN : iN), (List byte) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103 -/
opaque fbytes_ : forall (v_N : N) (v_fN : fN), (List byte) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103 -/
opaque nbytes_ : forall (v_numtype : numtype) (v_num_ : num_), (List byte) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103 -/
opaque vbytes_ : forall (v_vectype : vectype) (v_vec_ : vec_), (List byte) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 -/
opaque inv_ibits_ : forall (v_N : N) (var_0 : (List bit)), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 -/
opaque inv_fbits_ : forall (v_N : N) (var_0 : (List bit)), fN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86 -/
opaque inv_ibytes_ : forall (v_N : N) (var_0 : (List byte)), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86 -/
opaque inv_fbytes_ : forall (v_N : N) (var_0 : (List byte)), fN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84 -/
opaque inv_nbytes_ : forall (v_numtype : numtype) (var_0 : (List byte)), num_ := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84 -/
opaque inv_vbytes_ : forall (v_vectype : vectype) (var_0 : (List byte)), vec_ := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29 -/
opaque inot_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29 -/
opaque irev_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39 -/
opaque iandnot_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27 -/
def inez_ : ∀  (v_N : N) (v_iN : iN) , u32
  | v_N, i_1 =>
    (.mk_uN (nat_of_bool ((proj_uN_0 i_1) != 0)))


/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49 -/
opaque ibitselect_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN) (v_iN_1 : iN), iN := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29 -/
def ineg_ : ∀  (v_N : N) (v_iN : iN) , iN
  | v_N, i_1 =>
    (.mk_uN (((((2 ^ v_N) : Nat) - ((proj_uN_0 i_1) : Nat)) mod ((2 ^ v_N) : Nat)) : Nat))


/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 -/
inductive fun_iabs_ : N -> iN -> iN -> Prop where
  | fun_iabs__case_0 : forall (v_N : Nat) (i_1 : uN) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_iabs_ v_N i_1 (if (var_0 >= (0 : Nat)) then i_1 else (ineg_ v_N i_1))

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 -/
inductive fun_imin_ : N -> sx -> iN -> iN -> iN -> Prop where
  | fun_imin__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), 
    ((proj_uN_0 i_1) <= (proj_uN_0 i_2)) ->
    fun_imin_ v_N .U i_1 i_2 i_1
  | fun_imin__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), 
    ((proj_uN_0 i_1) > (proj_uN_0 i_2)) ->
    fun_imin_ v_N .U i_1 i_2 i_2
  | fun_imin__case_2 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_imin_ v_N .S i_1 i_2 (if (var_0 <= var_1) then i_1 else i_2)

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 -/
inductive fun_imax_ : N -> sx -> iN -> iN -> iN -> Prop where
  | fun_imax__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), 
    ((proj_uN_0 i_1) >= (proj_uN_0 i_2)) ->
    fun_imax_ v_N .U i_1 i_2 i_1
  | fun_imax__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), 
    ((proj_uN_0 i_1) < (proj_uN_0 i_2)) ->
    fun_imax_ v_N .U i_1 i_2 i_2
  | fun_imax__case_2 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_imax_ v_N .S i_1 i_2 (if (var_0 >= var_1) then i_1 else i_2)

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 -/
inductive fun_iadd_sat_ : N -> sx -> iN -> iN -> iN -> Prop where
  | fun_iadd_sat__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_iadd_sat_ v_N .U i_1 i_2 (.mk_uN (sat_u_ v_N (((proj_uN_0 i_1) + (proj_uN_0 i_2)) : Nat)))
  | fun_iadd_sat__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Nat) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_2) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_1) ->
    (fun_inv_signed_ v_N (sat_s_ v_N (var_1 + var_2)) var_0) ->
    fun_iadd_sat_ v_N .S i_1 i_2 (.mk_uN var_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 -/
inductive fun_isub_sat_ : N -> sx -> iN -> iN -> iN -> Prop where
  | fun_isub_sat__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_isub_sat_ v_N .U i_1 i_2 (.mk_uN (sat_u_ v_N (((proj_uN_0 i_1) : Nat) - ((proj_uN_0 i_2) : Nat))))
  | fun_isub_sat__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Nat) (var_1 : Nat) (var_0 : Nat), 
    (fun_signed_ v_N (proj_uN_0 i_2) var_2) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_1) ->
    (fun_inv_signed_ v_N (sat_s_ v_N (var_1 - var_2)) var_0) ->
    fun_isub_sat_ v_N .S i_1 i_2 (.mk_uN var_0)

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82 -/
opaque iavgr_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90 -/
opaque iq15mulr_sat_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38 -/
opaque fpmin_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38 -/
opaque fpmax_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.6-323.15 -/
inductive fun_packnum_ : lanetype -> num_ -> lane_ -> Prop where
  | fun_packnum__case_0 : forall (c : num_), 
    (wf_lane_ (lanetype_numtype .I32) (.mk_lane__0 .I32 c)) ->
    fun_packnum_ .I32 c (.mk_lane__0 .I32 c)
  | fun_packnum__case_1 : forall (c : num_), 
    (wf_lane_ (lanetype_numtype .I64) (.mk_lane__0 .I64 c)) ->
    fun_packnum_ .I64 c (.mk_lane__0 .I64 c)
  | fun_packnum__case_2 : forall (c : num_), 
    (wf_lane_ (lanetype_numtype .F32) (.mk_lane__0 .F32 c)) ->
    fun_packnum_ .F32 c (.mk_lane__0 .F32 c)
  | fun_packnum__case_3 : forall (c : num_), 
    (wf_lane_ (lanetype_numtype .F64) (.mk_lane__0 .F64 c)) ->
    fun_packnum_ .F64 c (.mk_lane__0 .F64 c)
  | fun_packnum__case_4 : forall (c : uN), 
    ((size (valtype_numtype (unpack (lanetype_packtype .I8)))) != none) ->
    (wf_lane_ (lanetype_packtype .I8) (.mk_lane__1 .I8 (wrap__ (Option.get! (size (valtype_numtype (unpack (lanetype_packtype .I8))))) (psize .I8) c))) ->
    fun_packnum_ .I8 (.mk_num__0 .I32 c) (.mk_lane__1 .I8 (wrap__ (Option.get! (size (valtype_numtype (unpack (lanetype_packtype .I8))))) (psize .I8) c))
  | fun_packnum__case_5 : forall (c : uN), 
    ((size (valtype_numtype (unpack (lanetype_packtype .I16)))) != none) ->
    (wf_lane_ (lanetype_packtype .I16) (.mk_lane__1 .I16 (wrap__ (Option.get! (size (valtype_numtype (unpack (lanetype_packtype .I16))))) (psize .I16) c))) ->
    fun_packnum_ .I16 (.mk_num__0 .I32 c) (.mk_lane__1 .I16 (wrap__ (Option.get! (size (valtype_numtype (unpack (lanetype_packtype .I16))))) (psize .I16) c))

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.6-328.17 -/
inductive fun_unpacknum_ : lanetype -> lane_ -> num_ -> Prop where
  | fun_unpacknum__case_0 : forall (c : num_), fun_unpacknum_ .I32 (.mk_lane__0 .I32 c) c
  | fun_unpacknum__case_1 : forall (c : num_), fun_unpacknum_ .I64 (.mk_lane__0 .I64 c) c
  | fun_unpacknum__case_2 : forall (c : num_), fun_unpacknum_ .F32 (.mk_lane__0 .F32 c) c
  | fun_unpacknum__case_3 : forall (c : num_), fun_unpacknum_ .F64 (.mk_lane__0 .F64 c) c
  | fun_unpacknum__case_4 : forall (c : uN), 
    ((size (valtype_numtype (unpack (lanetype_packtype .I8)))) != none) ->
    (wf_num_ (unpack (lanetype_packtype .I8)) (.mk_num__0 .I32 (extend__ (psize .I8) (Option.get! (size (valtype_numtype (unpack (lanetype_packtype .I8))))) .U c))) ->
    fun_unpacknum_ .I8 (.mk_lane__1 .I8 c) (.mk_num__0 .I32 (extend__ (psize .I8) (Option.get! (size (valtype_numtype (unpack (lanetype_packtype .I8))))) .U c))
  | fun_unpacknum__case_5 : forall (c : uN), 
    ((size (valtype_numtype (unpack (lanetype_packtype .I16)))) != none) ->
    (wf_num_ (unpack (lanetype_packtype .I16)) (.mk_num__0 .I32 (extend__ (psize .I16) (Option.get! (size (valtype_numtype (unpack (lanetype_packtype .I16))))) .U c))) ->
    fun_unpacknum_ .I16 (.mk_lane__1 .I16 c) (.mk_num__0 .I32 (extend__ (psize .I16) (Option.get! (size (valtype_numtype (unpack (lanetype_packtype .I16))))) .U c))

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.1-336.84 -/
opaque lanes_ : forall (v_shape : shape) (v_vec_ : vec_), (List lane_) := opaqueDef

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.1-340.36 -/
opaque inv_lanes_ : forall (v_shape : shape) (var_0 : (List lane_)), vec_ := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:343.1-343.28 -/
def zeroop : ∀  (v_vcvtop : vcvtop) , (Option zero)
  | (.EXTEND v_half v_sx) =>
    none
  | (.CONVERT half_opt v_sx) =>
    none
  | (.TRUNC_SAT v_sx zero_opt) =>
    zero_opt
  | (.DEMOTE v_zero) =>
    (some v_zero)
  | .PROMOTELOW =>
    none


/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:350.1-350.28 -/
def halfop : ∀  (v_vcvtop : vcvtop) , (Option half)
  | (.EXTEND v_half v_sx) =>
    (some v_half)
  | (.CONVERT half_opt v_sx) =>
    half_opt
  | (.TRUNC_SAT v_sx zero_opt) =>
    none
  | (.DEMOTE v_zero) =>
    none
  | .PROMOTELOW =>
    (some .LOW)


/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:357.1-357.32 -/
def fun_half : ∀  (v_half : half) (nat : Nat) (nat_0 : Nat) , Nat
  | .LOW, i, j =>
    i
  | .HIGH, i, j =>
    j


/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.1-363.28 -/
def vvunop_ : ∀  (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) , vec_
  | .V128, .NOT, v128 =>
    (inot_ (Option.get! (size .V128)) v128)


/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.1-365.31 -/
def vvbinop_ : ∀  (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (v_vec__0 : vec_) , vec_
  | .V128, .AND, v128_1, v128_2 =>
    (iand_ (Option.get! (size .V128)) v128_1 v128_2)
  | .V128, .ANDNOT, v128_1, v128_2 =>
    (iandnot_ (Option.get! (size .V128)) v128_1 v128_2)
  | .V128, .OR, v128_1, v128_2 =>
    (ior_ (Option.get! (size .V128)) v128_1 v128_2)
  | .V128, .XOR, v128_1, v128_2 =>
    (ixor_ (Option.get! (size .V128)) v128_1 v128_2)


/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.1-367.34 -/
def vvternop_ : ∀  (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (v_vec__0 : vec_) (v_vec__1 : vec_) , vec_
  | .V128, .BITSELECT, v128_1, v128_2, v128_3 =>
    (ibitselect_ (Option.get! (size .V128)) v128_1 v128_2 v128_3)


/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 -/
inductive fun_vunop_ : shape -> vunop_ -> vec_ -> (List vec_) -> Prop where
  | fun_vunop__case_0 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall₂ (fun (var_0 : uN) (lane_1 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) var_0)) var_0_lst lane_1_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I32 var_0)) var_0_lst))) ->
    fun_vunop_ (.X .I32 (.mk_dim v_M)) (.mk_vunop__0 .I32 v_M .ABS) v128_1 [v128]
  | fun_vunop__case_1 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall₂ (fun (var_0 : uN) (lane_1 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) var_0)) var_0_lst lane_1_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I64 var_0)) var_0_lst))) ->
    fun_vunop_ (.X .I64 (.mk_dim v_M)) (.mk_vunop__0 .I64 v_M .ABS) v128_1 [v128]
  | fun_vunop__case_2 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall₂ (fun (var_0 : uN) (lane_1 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) var_0)) var_0_lst lane_1_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I8 var_0)) var_0_lst))) ->
    fun_vunop_ (.X .I8 (.mk_dim v_M)) (.mk_vunop__0 .I8 v_M .ABS) v128_1 [v128]
  | fun_vunop__case_3 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall₂ (fun (var_0 : uN) (lane_1 : lane_) => (fun_iabs_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) var_0)) var_0_lst lane_1_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I16 var_0)) var_0_lst))) ->
    fun_vunop_ (.X .I16 (.mk_dim v_M)) (.mk_vunop__0 .I16 v_M .ABS) v128_1 [v128]
  | fun_vunop__case_4 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)), 
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 (ineg_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (lane_1 : lane_) => (.mk_lane__2 .I32 (ineg_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1))))) lane_1_lst))) ->
    fun_vunop_ (.X .I32 (.mk_dim v_M)) (.mk_vunop__0 .I32 v_M .NEG) v128_1 [v128]
  | fun_vunop__case_5 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)), 
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 (ineg_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (lane_1 : lane_) => (.mk_lane__2 .I64 (ineg_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1))))) lane_1_lst))) ->
    fun_vunop_ (.X .I64 (.mk_dim v_M)) (.mk_vunop__0 .I64 v_M .NEG) v128_1 [v128]
  | fun_vunop__case_6 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)), 
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 (ineg_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (lane_1 : lane_) => (.mk_lane__2 .I8 (ineg_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1))))) lane_1_lst))) ->
    fun_vunop_ (.X .I8 (.mk_dim v_M)) (.mk_vunop__0 .I8 v_M .NEG) v128_1 [v128]
  | fun_vunop__case_7 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)), 
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 (ineg_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (lane_1 : lane_) => (.mk_lane__2 .I16 (ineg_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1))))) lane_1_lst))) ->
    fun_vunop_ (.X .I16 (.mk_dim v_M)) (.mk_vunop__0 .I16 v_M .NEG) v128_1 [v128]
  | fun_vunop__case_8 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)), 
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 (ipopcnt_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (lane_1 : lane_) => (.mk_lane__2 .I32 (ipopcnt_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1))))) lane_1_lst))) ->
    fun_vunop_ (.X .I32 (.mk_dim v_M)) (.mk_vunop__0 .I32 v_M .POPCNT) v128_1 [v128]
  | fun_vunop__case_9 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)), 
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 (ipopcnt_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (lane_1 : lane_) => (.mk_lane__2 .I64 (ipopcnt_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1))))) lane_1_lst))) ->
    fun_vunop_ (.X .I64 (.mk_dim v_M)) (.mk_vunop__0 .I64 v_M .POPCNT) v128_1 [v128]
  | fun_vunop__case_10 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)), 
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 (ipopcnt_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (lane_1 : lane_) => (.mk_lane__2 .I8 (ipopcnt_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1))))) lane_1_lst))) ->
    fun_vunop_ (.X .I8 (.mk_dim v_M)) (.mk_vunop__0 .I8 v_M .POPCNT) v128_1 [v128]
  | fun_vunop__case_11 : forall (v_M : Nat) (v128_1 : uN) (v128 : uN) (lane_1_lst : (List lane_)), 
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 (ipopcnt_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (lane_1 : lane_) => (.mk_lane__2 .I16 (ipopcnt_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1))))) lane_1_lst))) ->
    fun_vunop_ (.X .I16 (.mk_dim v_M)) (.mk_vunop__0 .I16 v_M .POPCNT) v128_1 [v128]
  | fun_vunop__case_12 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fabs_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fabs_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .ABS) v128_1 v128_lst
  | fun_vunop__case_13 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fabs_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fabs_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .ABS) v128_1 v128_lst
  | fun_vunop__case_14 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fneg_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fneg_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .NEG) v128_1 v128_lst
  | fun_vunop__case_15 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fneg_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fneg_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .NEG) v128_1 v128_lst
  | fun_vunop__case_16 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fsqrt_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fsqrt_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .SQRT) v128_1 v128_lst
  | fun_vunop__case_17 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fsqrt_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fsqrt_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .SQRT) v128_1 v128_lst
  | fun_vunop__case_18 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fceil_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fceil_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .CEIL) v128_1 v128_lst
  | fun_vunop__case_19 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fceil_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fceil_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .CEIL) v128_1 v128_lst
  | fun_vunop__case_20 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (ffloor_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (ffloor_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .FLOOR) v128_1 v128_lst
  | fun_vunop__case_21 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (ffloor_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (ffloor_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .FLOOR) v128_1 v128_lst
  | fun_vunop__case_22 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (ftrunc_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (ftrunc_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .TRUNC) v128_1 v128_lst
  | fun_vunop__case_23 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (ftrunc_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (ftrunc_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .TRUNC) v128_1 v128_lst
  | fun_vunop__case_24 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fnearest_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fnearest_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F32 (.mk_dim v_M)) (.mk_vunop__1 .F32 v_M .NEAREST) v128_1 v128_lst
  | fun_vunop__case_25 : forall (v_M : Nat) (v128_1 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    Forall (fun (lane_1 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fnearest_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))))) lane_1_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.map (fun (lane_1 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fnearest_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1))))))) lane_1_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vunop_ (.X .F64 (.mk_dim v_M)) (.mk_vunop__1 .F64 v_M .NEAREST) v128_1 v128_lst

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 -/
inductive fun_vbinop_ : shape -> vbinop_ -> vec_ -> vec_ -> (List vec_) -> Prop where
  | fun_vbinop__case_0 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 (iadd_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I32 (iadd_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_1 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 (iadd_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I64 (iadd_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_2 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 (iadd_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I8 (iadd_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_3 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 (iadd_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I16 (iadd_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_4 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 (isub_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I32 (isub_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_5 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 (isub_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I64 (isub_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_6 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 (isub_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I8 (isub_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_7 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 (isub_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I16 (isub_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_8 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I32 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M (.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_9 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I64 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M (.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_10 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I8 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M (.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_11 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_imin_ (lsizenn (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I16 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M (.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_12 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I32 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M (.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_13 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I64 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M (.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_14 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I8 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M (.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_15 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_imax_ (lsizenn (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I16 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M (.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_16 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I32 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M (.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_17 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I64 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M (.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_18 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I8 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M (.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_19 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_iadd_sat_ (lsizenn (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I16 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M (.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_20 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I32 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M (.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_21 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I64 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M (.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_22 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I8 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M (.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_23 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_isub_sat_ (lsizenn (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (var_0 : uN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 var_0))) var_0_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (var_0 : uN) => (.mk_lane__2 .I16 var_0)) var_0_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M (.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_24 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 (imul_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I32 (imul_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_25 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 (imul_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I64 (imul_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_26 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 (imul_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I8 (imul_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_27 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 (imul_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I16 (imul_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_28 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 (iavgr_ (lsizenn (lanetype_Jnn .I32)) .U (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I32 (iavgr_ (lsizenn (lanetype_Jnn .I32)) .U (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_29 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 (iavgr_ (lsizenn (lanetype_Jnn .I64)) .U (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I64 (iavgr_ (lsizenn (lanetype_Jnn .I64)) .U (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_30 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 (iavgr_ (lsizenn (lanetype_Jnn .I8)) .U (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I8 (iavgr_ (lsizenn (lanetype_Jnn .I8)) .U (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_31 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 (iavgr_ (lsizenn (lanetype_Jnn .I16)) .U (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I16 (iavgr_ (lsizenn (lanetype_Jnn .I16)) .U (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_32 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn .I32)) .S (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn .I32)) .S (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I32 (.mk_dim v_M)) (.mk_vbinop__0 .I32 v_M .Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_33 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn .I64)) .S (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn .I64)) .S (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I64 (.mk_dim v_M)) (.mk_vbinop__0 .I64 v_M .Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_34 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn .I8)) .S (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn .I8)) .S (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I8 (.mk_dim v_M)) (.mk_vbinop__0 .I8 v_M .Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_35 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)), 
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn .I16)) .S (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (.mk_lane__2 .I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn .I16)) .S (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))) lane_1_lst lane_2_lst))) ->
    fun_vbinop_ (.X .I16 (.mk_dim v_M)) (.mk_vbinop__0 .I16 v_M .Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_36 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fadd_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fadd_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .ADD) v128_1 v128_2 v128_lst
  | fun_vbinop__case_37 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fadd_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fadd_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .ADD) v128_1 v128_2 v128_lst
  | fun_vbinop__case_38 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fsub_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fsub_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .SUB) v128_1 v128_2 v128_lst
  | fun_vbinop__case_39 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fsub_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fsub_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .SUB) v128_1 v128_2 v128_lst
  | fun_vbinop__case_40 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fmul_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmul_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .MUL) v128_1 v128_2 v128_lst
  | fun_vbinop__case_41 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fmul_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmul_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .MUL) v128_1 v128_2 v128_lst
  | fun_vbinop__case_42 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fdiv_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fdiv_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .DIV) v128_1 v128_2 v128_lst
  | fun_vbinop__case_43 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fdiv_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fdiv_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .DIV) v128_1 v128_2 v128_lst
  | fun_vbinop__case_44 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fmin_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmin_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .MIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_45 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fmin_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmin_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .MIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_46 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fmax_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fmax_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .MAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_47 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fmax_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fmax_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .MAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_48 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fpmin_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fpmin_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .PMIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_49 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fpmin_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fpmin_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .PMIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_50 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F32) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F32) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0)))) (fpmax_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 iter_0))) (fpmax_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F32 (.mk_dim v_M)) (.mk_vbinop__1 .F32 v_M .PMAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_51 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128_lst : (List vec_)) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_lst_lst : (List (List lane_))), 
    Forall (fun (lane_lst : (List lane_)) => Forall (fun (lane : lane_) => (wf_lane_ (lanetype_Fnn .F64) lane)) lane_lst) lane_lst_lst ->
    ((List.length lane_1_lst) == (List.length lane_2_lst)) ->
    Forall₂ (fun (lane_1 : lane_) (lane_2 : lane_) => Forall (fun (iter_0 : fN) => (wf_lane_ (lanetype_Fnn .F64) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0)))) (fpmax_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2)))))) lane_1_lst lane_2_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    (lane_lst_lst == (setproduct_ lane_ (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (List.map (fun (iter_0 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 iter_0))) (fpmax_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))) lane_1_lst lane_2_lst))) ->
    (v128_lst == (List.map (fun (lane_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) lane_lst)) lane_lst_lst)) ->
    fun_vbinop_ (.X .F64 (.mk_dim v_M)) (.mk_vbinop__1 .F64 v_M .PMAX) v128_1 v128_2 v128_lst

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 -/
inductive fun_vrelop_ : shape -> vrelop_ -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_vrelop__case_0 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn .I32)) .S (.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))))) lane_1_lst lane_2_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I32 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M .EQ) v128_1 v128_2 v128
  | fun_vrelop__case_1 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn .I64)) .S (.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))))) lane_1_lst lane_2_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I64 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M .EQ) v128_1 v128_2 v128
  | fun_vrelop__case_2 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn .I8)) .S (.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))))) lane_1_lst lane_2_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I8 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M .EQ) v128_1 v128_2 v128
  | fun_vrelop__case_3 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn .I16)) .S (.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))))) lane_1_lst lane_2_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I16 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M .EQ) v128_1 v128_2 v128
  | fun_vrelop__case_4 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn .I32)) .S (.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn .I32)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))))) lane_1_lst lane_2_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I32 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M .NE) v128_1 v128_2 v128
  | fun_vrelop__case_5 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn .I64)) .S (.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn .I64)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))))) lane_1_lst lane_2_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I64 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M .NE) v128_1 v128_2 v128
  | fun_vrelop__case_6 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn .I8)) .S (.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn .I8)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))))) lane_1_lst lane_2_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I8 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M .NE) v128_1 v128_2 v128
  | fun_vrelop__case_7 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (lsizenn (lanetype_Jnn .I16)) .S (.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn .I16)) (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2))))))) lane_1_lst lane_2_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I16 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M .NE) v128_1 v128_2 v128
  | fun_vrelop__case_8 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I32)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I32 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M (.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_9 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I64)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I64 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M (.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_10 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I8)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I8 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M (.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_11 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ilt_ (lsizenn (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I16)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I16 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M (.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_12 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I32)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I32 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M (.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_13 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I64)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I64 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M (.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_14 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I8)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I8 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M (.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_15 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_igt_ (lsizenn (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I16)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I16 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M (.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_16 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I32)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I32 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M (.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_17 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I64)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I64 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M (.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_18 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I8)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I8 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M (.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_19 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ile_ (lsizenn (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I16)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I16 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M (.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_20 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn .I32)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim v_M))) (.mk_lane__2 .I32 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I32)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I32) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I32 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I32 (.mk_dim v_M)) (.mk_vrelop__0 .I32 v_M (.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_21 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn .I64)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim v_M))) (.mk_lane__2 .I64 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I64)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I64) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I64 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I64 (.mk_dim v_M)) (.mk_vrelop__0 .I64 v_M (.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_22 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn .I8)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim v_M))) (.mk_lane__2 .I8 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I8)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I8) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I8 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I8 (.mk_dim v_M)) (.mk_vrelop__0 .I8 v_M (.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_23 : forall (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length lane_1_lst)) ->
    ((List.length var_0_lst) == (List.length lane_2_lst)) ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__2 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__2 lane_2) != none)) lane_2_lst ->
    Forall₃ (fun (var_0 : uN) (lane_1 : lane_) (lane_2 : lane_) => (fun_ige_ (lsizenn (lanetype_Jnn .I16)) v_sx (Option.get! (proj_lane__2 lane_1)) (Option.get! (proj_lane__2 lane_2)) var_0)) var_0_lst lane_1_lst lane_2_lst ->
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim v_M))) (.mk_lane__2 .I16 lane_3))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) v128_2)) ->
    (lane_3_lst == (List.map (fun (var_0 : uN) => (extend__ 1 (lsizenn (lanetype_Jnn .I16)) .S (.mk_uN (proj_uN_0 var_0)))) var_0_lst)) ->
    (v128 == (inv_lanes_ (.X (lanetype_Jnn .I16) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__2 .I16 lane_3)) lane_3_lst))) ->
    fun_vrelop_ (.X .I16 (.mk_dim v_M)) (.mk_vrelop__0 .I16 v_M (.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_24 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F32)) .S (.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F32)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .EQ) v128_1 v128_2 v128
  | fun_vrelop__case_25 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F64)) .S (.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F64)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .EQ) v128_1 v128_2 v128
  | fun_vrelop__case_26 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F32)) .S (.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F32)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .NE) v128_1 v128_2 v128
  | fun_vrelop__case_27 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F64)) .S (.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F64)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .NE) v128_1 v128_2 v128
  | fun_vrelop__case_28 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F32)) .S (.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F32)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .LT) v128_1 v128_2 v128
  | fun_vrelop__case_29 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F64)) .S (.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F64)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .LT) v128_1 v128_2 v128
  | fun_vrelop__case_30 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F32)) .S (.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F32)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .GT) v128_1 v128_2 v128
  | fun_vrelop__case_31 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F64)) .S (.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F64)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .GT) v128_1 v128_2 v128
  | fun_vrelop__case_32 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F32)) .S (.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F32)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .LE) v128_1 v128_2 v128
  | fun_vrelop__case_33 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F64)) .S (.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F64)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .LE) v128_1 v128_2 v128
  | fun_vrelop__case_34 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F32) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F32)) .S (.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn .F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F32)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F32)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F32 (.mk_dim v_M)) (.mk_vrelop__1 .F32 v_M .GE) v128_1 v128_2 v128
  | fun_vrelop__case_35 : forall (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v128 : uN) (lane_1_lst : (List lane_)) (lane_2_lst : (List lane_)) (lane_3_lst : (List iN)) (v_Inn : Inn), 
    Forall (fun (lane_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_1)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim v_M))) lane_2)) lane_2_lst ->
    Forall (fun (lane_3 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn v_Inn) (.mk_dim v_M))) (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3)))))) lane_3_lst ->
    (lane_1_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_1)) ->
    (lane_2_lst == (lanes_ (.X (lanetype_Fnn .F64) (.mk_dim v_M)) v128_2)) ->
    Forall (fun (lane_1 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_1))) != none)) lane_1_lst ->
    Forall (fun (lane_1 : lane_) => ((proj_lane__0 lane_1) != none)) lane_1_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_num__1 (Option.get! (proj_lane__0 lane_2))) != none)) lane_2_lst ->
    Forall (fun (lane_2 : lane_) => ((proj_lane__0 lane_2) != none)) lane_2_lst ->
    (lane_3_lst == (List.zipWith (fun (lane_1 : lane_) (lane_2 : lane_) => (extend__ 1 (sizenn (numtype_Fnn .F64)) .S (.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn .F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2))))))))) lane_1_lst lane_2_lst)) ->
    ((size (valtype_Fnn .F64)) != none) ->
    ((isize v_Inn) == (Option.get! (size (valtype_Fnn .F64)))) ->
    (v128 == (inv_lanes_ (.X (lanetype_Inn v_Inn) (.mk_dim v_M)) (List.map (fun (lane_3 : iN) => (.mk_lane__0 (numtype_Inn v_Inn) (.mk_num__0 v_Inn (.mk_uN (proj_uN_0 lane_3))))) lane_3_lst))) ->
    fun_vrelop_ (.X .F64 (.mk_dim v_M)) (.mk_vrelop__1 .F64 v_M .GE) v128_1 v128_2 v128

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.15 -/
inductive fun_vcvtop__ : shape -> shape -> vcvtop -> lane_ -> (List lane_) -> Prop where
  | fun_vcvtop___case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Jnn .I32)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I32 iN_1) [(.mk_lane__2 .I32 iN_2)]
  | fun_vcvtop___case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Jnn .I32)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I64 iN_1) [(.mk_lane__2 .I32 iN_2)]
  | fun_vcvtop___case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Jnn .I32)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I8 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I8 iN_1) [(.mk_lane__2 .I32 iN_2)]
  | fun_vcvtop___case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I32) (.mk_dim M_2))) (.mk_lane__2 .I32 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Jnn .I32)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I16 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I16 iN_1) [(.mk_lane__2 .I32 iN_2)]
  | fun_vcvtop___case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Jnn .I64)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I32 iN_1) [(.mk_lane__2 .I64 iN_2)]
  | fun_vcvtop___case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Jnn .I64)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I64 iN_1) [(.mk_lane__2 .I64 iN_2)]
  | fun_vcvtop___case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Jnn .I64)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I8 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I8 iN_1) [(.mk_lane__2 .I64 iN_2)]
  | fun_vcvtop___case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I64) (.mk_dim M_2))) (.mk_lane__2 .I64 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Jnn .I64)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I16 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I16 iN_1) [(.mk_lane__2 .I64 iN_2)]
  | fun_vcvtop___case_8 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Jnn .I8)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I32 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I32 iN_1) [(.mk_lane__2 .I8 iN_2)]
  | fun_vcvtop___case_9 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Jnn .I8)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I64 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I64 iN_1) [(.mk_lane__2 .I8 iN_2)]
  | fun_vcvtop___case_10 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Jnn .I8)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I8 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I8 iN_1) [(.mk_lane__2 .I8 iN_2)]
  | fun_vcvtop___case_11 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I8) (.mk_dim M_2))) (.mk_lane__2 .I8 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Jnn .I8)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I16 (.mk_dim M_1)) (.X .I8 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I16 iN_1) [(.mk_lane__2 .I8 iN_2)]
  | fun_vcvtop___case_12 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Jnn .I16)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I32 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I32 iN_1) [(.mk_lane__2 .I16 iN_2)]
  | fun_vcvtop___case_13 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Jnn .I16)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I64 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I64 iN_1) [(.mk_lane__2 .I16 iN_2)]
  | fun_vcvtop___case_14 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Jnn .I16)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I8 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I8 iN_1) [(.mk_lane__2 .I16 iN_2)]
  | fun_vcvtop___case_15 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (iN_1 : uN) (iN_2 : uN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn .I16) (.mk_dim M_2))) (.mk_lane__2 .I16 iN_2)) ->
    (iN_2 == (extend__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Jnn .I16)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I16 (.mk_dim M_1)) (.X .I16 (.mk_dim M_2)) (.EXTEND v_half v_sx) (.mk_lane__2 .I16 iN_1) [(.mk_lane__2 .I16 iN_2)]
  | fun_vcvtop___case_16 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) ->
    (fN_2 == (convert__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Fnn .F32)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.CONVERT half_opt v_sx) (.mk_lane__2 .I32 iN_1) [(.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))]
  | fun_vcvtop___case_17 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) ->
    (fN_2 == (convert__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Fnn .F32)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.CONVERT half_opt v_sx) (.mk_lane__2 .I64 iN_1) [(.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))]
  | fun_vcvtop___case_18 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) ->
    (fN_2 == (convert__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Fnn .F32)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I8 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.CONVERT half_opt v_sx) (.mk_lane__2 .I8 iN_1) [(.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))]
  | fun_vcvtop___case_19 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) ->
    (fN_2 == (convert__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Fnn .F32)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I16 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.CONVERT half_opt v_sx) (.mk_lane__2 .I16 iN_1) [(.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))]
  | fun_vcvtop___case_20 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) ->
    (fN_2 == (convert__ (lsizenn1 (lanetype_Jnn .I32)) (lsizenn2 (lanetype_Fnn .F64)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.CONVERT half_opt v_sx) (.mk_lane__2 .I32 iN_1) [(.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))]
  | fun_vcvtop___case_21 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) ->
    (fN_2 == (convert__ (lsizenn1 (lanetype_Jnn .I64)) (lsizenn2 (lanetype_Fnn .F64)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.CONVERT half_opt v_sx) (.mk_lane__2 .I64 iN_1) [(.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))]
  | fun_vcvtop___case_22 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) ->
    (fN_2 == (convert__ (lsizenn1 (lanetype_Jnn .I8)) (lsizenn2 (lanetype_Fnn .F64)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I8 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.CONVERT half_opt v_sx) (.mk_lane__2 .I8 iN_1) [(.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))]
  | fun_vcvtop___case_23 : forall (M_1 : Nat) (M_2 : Nat) (half_opt : (Option half)) (v_sx : sx) (iN_1 : uN) (fN_2 : fN), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) ->
    (fN_2 == (convert__ (lsizenn1 (lanetype_Jnn .I16)) (lsizenn2 (lanetype_Fnn .F64)) v_sx iN_1)) ->
    fun_vcvtop__ (.X .I16 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.CONVERT half_opt v_sx) (.mk_lane__2 .I16 iN_1) [(.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))]
  | fun_vcvtop___case_24 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (fN_1 : fN) (iN_2_opt : (Option iN)), 
    Forall (fun (iN_2 : iN) => (wf_lane_ (lanetype_Inn .I32) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 iN_2)))) (Option.toList iN_2_opt) ->
    (iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Inn .I32)) v_sx fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.TRUNC_SAT v_sx zero_opt) (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (list_ lane_ (Option.map (fun (iN_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 iN_2))) iN_2_opt))
  | fun_vcvtop___case_25 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (fN_1 : fN) (iN_2_opt : (Option iN)), 
    Forall (fun (iN_2 : iN) => (wf_lane_ (lanetype_Inn .I32) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 iN_2)))) (Option.toList iN_2_opt) ->
    (iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Inn .I32)) v_sx fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.TRUNC_SAT v_sx zero_opt) (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (list_ lane_ (Option.map (fun (iN_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 iN_2))) iN_2_opt))
  | fun_vcvtop___case_26 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (fN_1 : fN) (iN_2_opt : (Option iN)), 
    Forall (fun (iN_2 : iN) => (wf_lane_ (lanetype_Inn .I64) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 iN_2)))) (Option.toList iN_2_opt) ->
    (iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Inn .I64)) v_sx fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.TRUNC_SAT v_sx zero_opt) (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (list_ lane_ (Option.map (fun (iN_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 iN_2))) iN_2_opt))
  | fun_vcvtop___case_27 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (fN_1 : fN) (iN_2_opt : (Option iN)), 
    Forall (fun (iN_2 : iN) => (wf_lane_ (lanetype_Inn .I64) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 iN_2)))) (Option.toList iN_2_opt) ->
    (iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Inn .I64)) v_sx fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.TRUNC_SAT v_sx zero_opt) (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (list_ lane_ (Option.map (fun (iN_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 iN_2))) iN_2_opt))
  | fun_vcvtop___case_28 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (fN_1 : fN) (iN_2_opt : (Option iN)), 
    Forall (fun (iN_2 : iN) => (wf_lane_ (lanetype_Inn .I32) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 iN_2)))) (Option.toList iN_2_opt) ->
    (iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Inn .I32)) v_sx fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.TRUNC_SAT v_sx zero_opt) (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (list_ lane_ (Option.map (fun (iN_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 iN_2))) iN_2_opt))
  | fun_vcvtop___case_29 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (fN_1 : fN) (iN_2_opt : (Option iN)), 
    Forall (fun (iN_2 : iN) => (wf_lane_ (lanetype_Inn .I32) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 iN_2)))) (Option.toList iN_2_opt) ->
    (iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Inn .I32)) v_sx fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.TRUNC_SAT v_sx zero_opt) (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (list_ lane_ (Option.map (fun (iN_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 iN_2))) iN_2_opt))
  | fun_vcvtop___case_30 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (fN_1 : fN) (iN_2_opt : (Option iN)), 
    Forall (fun (iN_2 : iN) => (wf_lane_ (lanetype_Inn .I64) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 iN_2)))) (Option.toList iN_2_opt) ->
    (iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Inn .I64)) v_sx fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.TRUNC_SAT v_sx zero_opt) (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (list_ lane_ (Option.map (fun (iN_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 iN_2))) iN_2_opt))
  | fun_vcvtop___case_31 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : (Option zero)) (fN_1 : fN) (iN_2_opt : (Option iN)), 
    Forall (fun (iN_2 : iN) => (wf_lane_ (lanetype_Inn .I64) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 iN_2)))) (Option.toList iN_2_opt) ->
    (iN_2_opt == (trunc_sat__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Inn .I64)) v_sx fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.TRUNC_SAT v_sx zero_opt) (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (list_ lane_ (Option.map (fun (iN_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 iN_2))) iN_2_opt))
  | fun_vcvtop___case_32 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2)))) fN_2_lst ->
    (fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F32)) fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.DEMOTE .ZERO) (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) fN_2_lst)
  | fun_vcvtop___case_33 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2)))) fN_2_lst ->
    (fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F32)) fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.DEMOTE .ZERO) (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) fN_2_lst)
  | fun_vcvtop___case_34 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2)))) fN_2_lst ->
    (fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F64)) fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.DEMOTE .ZERO) (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) fN_2_lst)
  | fun_vcvtop___case_35 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2)))) fN_2_lst ->
    (fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F64)) fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.DEMOTE .ZERO) (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) fN_2_lst)
  | fun_vcvtop___case_36 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2)))) fN_2_lst ->
    (fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F32)) fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.DEMOTE .ZERO) (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) fN_2_lst)
  | fun_vcvtop___case_37 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2)))) fN_2_lst ->
    (fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F32)) fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) (.DEMOTE .ZERO) (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) fN_2_lst)
  | fun_vcvtop___case_38 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2)))) fN_2_lst ->
    (fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F64)) fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.DEMOTE .ZERO) (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) fN_2_lst)
  | fun_vcvtop___case_39 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2)))) fN_2_lst ->
    (fN_2_lst == (demote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F64)) fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) (.DEMOTE .ZERO) (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) fN_2_lst)
  | fun_vcvtop___case_40 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2)))) fN_2_lst ->
    (fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F32)) fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) .PROMOTELOW (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) fN_2_lst)
  | fun_vcvtop___case_41 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2)))) fN_2_lst ->
    (fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F32)) fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) .PROMOTELOW (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) fN_2_lst)
  | fun_vcvtop___case_42 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2)))) fN_2_lst ->
    (fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F64)) fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) .PROMOTELOW (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) fN_2_lst)
  | fun_vcvtop___case_43 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2)))) fN_2_lst ->
    (fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn .F32)) (lsizenn2 (lanetype_Fnn .F64)) fN_1)) ->
    fun_vcvtop__ (.X .F32 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) .PROMOTELOW (.mk_lane__0 .F32 (.mk_num__1 .F32 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) fN_2_lst)
  | fun_vcvtop___case_44 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2)))) fN_2_lst ->
    (fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F32)) fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) .PROMOTELOW (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) fN_2_lst)
  | fun_vcvtop___case_45 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F32) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2)))) fN_2_lst ->
    (fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F32)) fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F32 (.mk_dim M_2)) .PROMOTELOW (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F32) (.mk_num__1 .F32 fN_2))) fN_2_lst)
  | fun_vcvtop___case_46 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2)))) fN_2_lst ->
    (fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F64)) fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) .PROMOTELOW (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) fN_2_lst)
  | fun_vcvtop___case_47 : forall (M_1 : Nat) (M_2 : Nat) (fN_1 : fN) (fN_2_lst : (List fN)), 
    Forall (fun (fN_2 : fN) => (wf_lane_ (fun_lanetype (.X (lanetype_Fnn .F64) (.mk_dim M_2))) (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2)))) fN_2_lst ->
    (fN_2_lst == (promote__ (lsizenn1 (lanetype_Fnn .F64)) (lsizenn2 (lanetype_Fnn .F64)) fN_1)) ->
    fun_vcvtop__ (.X .F64 (.mk_dim M_1)) (.X .F64 (.mk_dim M_2)) .PROMOTELOW (.mk_lane__0 .F64 (.mk_num__1 .F64 fN_1)) (List.map (fun (fN_2 : fN) => (.mk_lane__0 (numtype_Fnn .F64) (.mk_num__1 .F64 fN_2))) fN_2_lst)

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 -/
inductive fun_vextunop__ : ishape -> ishape -> vextunop_ -> vec_ -> vec_ -> Prop where
  | fun_vextunop___case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_lst : (List lane_)), 
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci)) ci_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1)) ->
    Forall (fun (ci : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci))) != none)) ci_lst ->
    Forall (fun (ci : lane_) => ((proj_lane__0 ci) != none)) ci_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.map (fun (ci : lane_) => (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci)))))) ci_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextunop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextunop__0 .I32 M_1 (.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_lst : (List lane_)), 
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci)) ci_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1)) ->
    Forall (fun (ci : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci))) != none)) ci_lst ->
    Forall (fun (ci : lane_) => ((proj_lane__0 ci) != none)) ci_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.map (fun (ci : lane_) => (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci)))))) ci_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextunop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextunop__0 .I32 M_1 (.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_lst : (List lane_)), 
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci)) ci_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1)) ->
    Forall (fun (ci : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci))) != none)) ci_lst ->
    Forall (fun (ci : lane_) => ((proj_lane__0 ci) != none)) ci_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.map (fun (ci : lane_) => (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci)))))) ci_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextunop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextunop__0 .I32 M_1 (.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_lst : (List lane_)), 
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci)) ci_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1)) ->
    Forall (fun (ci : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci))) != none)) ci_lst ->
    Forall (fun (ci : lane_) => ((proj_lane__0 ci) != none)) ci_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.map (fun (ci : lane_) => (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci)))))) ci_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextunop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextunop__0 .I32 M_1 (.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_lst : (List lane_)), 
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci)) ci_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1)) ->
    Forall (fun (ci : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci))) != none)) ci_lst ->
    Forall (fun (ci : lane_) => ((proj_lane__0 ci) != none)) ci_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.map (fun (ci : lane_) => (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci)))))) ci_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextunop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextunop__0 .I64 M_1 (.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_lst : (List lane_)), 
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci)) ci_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1)) ->
    Forall (fun (ci : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci))) != none)) ci_lst ->
    Forall (fun (ci : lane_) => ((proj_lane__0 ci) != none)) ci_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.map (fun (ci : lane_) => (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci)))))) ci_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextunop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextunop__0 .I64 M_1 (.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_lst : (List lane_)), 
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci)) ci_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1)) ->
    Forall (fun (ci : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci))) != none)) ci_lst ->
    Forall (fun (ci : lane_) => ((proj_lane__0 ci) != none)) ci_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.map (fun (ci : lane_) => (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci)))))) ci_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextunop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextunop__0 .I64 M_1 (.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_lst : (List lane_)), 
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci)) ci_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1)) ->
    Forall (fun (ci : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci))) != none)) ci_lst ->
    Forall (fun (ci : lane_) => ((proj_lane__0 ci) != none)) ci_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.map (fun (ci : lane_) => (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci)))))) ci_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextunop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextunop__0 .I64 M_1 (.EXTADD_PAIRWISE v_sx)) c_1 c

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 -/
inductive fun_vextbinop__ : ishape -> ishape -> vextbinop_ -> vec_ -> vec_ -> vec_ -> Prop where
  | fun_vextbinop___case_0 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    ((List.length ci_1_lst) == (List.length ci_2_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    Forall₂ (fun (ci_1 : lane_) (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2)))))))))) ci_1_lst ci_2_lst ->
    (ci_1_lst == (List.extract (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
    (ci_2_lst == (List.extract (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))))) ci_1_lst ci_2_lst))) ->
    fun_vextbinop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextbinop__0 .I32 M_1 (.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_1 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    ((List.length ci_1_lst) == (List.length ci_2_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    Forall₂ (fun (ci_1 : lane_) (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2)))))))))) ci_1_lst ci_2_lst ->
    (ci_1_lst == (List.extract (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
    (ci_2_lst == (List.extract (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))))) ci_1_lst ci_2_lst))) ->
    fun_vextbinop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextbinop__0 .I32 M_1 (.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_2 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    ((List.length ci_1_lst) == (List.length ci_2_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    Forall₂ (fun (ci_1 : lane_) (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2)))))))))) ci_1_lst ci_2_lst ->
    (ci_1_lst == (List.extract (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
    (ci_2_lst == (List.extract (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))))) ci_1_lst ci_2_lst))) ->
    fun_vextbinop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextbinop__0 .I32 M_1 (.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_3 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    ((List.length ci_1_lst) == (List.length ci_2_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    Forall₂ (fun (ci_1 : lane_) (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2)))))))))) ci_1_lst ci_2_lst ->
    (ci_1_lst == (List.extract (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
    (ci_2_lst == (List.extract (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))))) ci_1_lst ci_2_lst))) ->
    fun_vextbinop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextbinop__0 .I32 M_1 (.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_4 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    ((List.length ci_1_lst) == (List.length ci_2_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    Forall₂ (fun (ci_1 : lane_) (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2)))))))))) ci_1_lst ci_2_lst ->
    (ci_1_lst == (List.extract (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
    (ci_2_lst == (List.extract (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))))) ci_1_lst ci_2_lst))) ->
    fun_vextbinop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextbinop__0 .I64 M_1 (.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_5 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    ((List.length ci_1_lst) == (List.length ci_2_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    Forall₂ (fun (ci_1 : lane_) (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2)))))))))) ci_1_lst ci_2_lst ->
    (ci_1_lst == (List.extract (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
    (ci_2_lst == (List.extract (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))))) ci_1_lst ci_2_lst))) ->
    fun_vextbinop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextbinop__0 .I64 M_1 (.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_6 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    ((List.length ci_1_lst) == (List.length ci_2_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    Forall₂ (fun (ci_1 : lane_) (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2)))))))))) ci_1_lst ci_2_lst ->
    (ci_1_lst == (List.extract (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
    (ci_2_lst == (List.extract (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))))) ci_1_lst ci_2_lst))) ->
    fun_vextbinop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextbinop__0 .I64 M_1 (.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_7 : forall (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (c : uN) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    ((List.length ci_1_lst) == (List.length ci_2_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    Forall₂ (fun (ci_1 : lane_) (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2)))))))))) ci_1_lst ci_2_lst ->
    (ci_1_lst == (List.extract (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1) (fun_half v_half 0 M_1) M_1)) ->
    (ci_2_lst == (List.extract (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_2) (fun_half v_half 0 M_1) M_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))))) ci_1_lst ci_2_lst))) ->
    fun_vextbinop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextbinop__0 .I64 M_1 (.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_8 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci_2)) ci_2_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))) ci_1_lst ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextbinop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextbinop__0 .I32 M_1 .DOTS) c_1 c_2 c
  | fun_vextbinop___case_9 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci_2)) ci_2_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I32)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))) ci_1_lst ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextbinop__ (.X .I32 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextbinop__0 .I32 M_1 .DOTS) c_1 c_2 c
  | fun_vextbinop___case_10 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci_2)) ci_2_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))) ci_1_lst ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextbinop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextbinop__0 .I32 M_1 .DOTS) c_1 c_2 c
  | fun_vextbinop___case_11 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci_2)) ci_2_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (imul_ (lsizenn1 (lanetype_Inn .I32)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I32)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))) ci_1_lst ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I32) (.mk_num__0 .I32 (iadd_ (lsizenn1 (lanetype_Inn .I32)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextbinop__ (.X .I32 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextbinop__0 .I32 M_1 .DOTS) c_1 c_2 c
  | fun_vextbinop___case_12 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci_2)) ci_2_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))) ci_1_lst ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextbinop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextbinop__0 .I64 M_1 .DOTS) c_1 c_2 c
  | fun_vextbinop___case_13 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I32) (.mk_dim M_2))) ci_2)) ci_2_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Inn .I32) (.mk_dim M_2)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I32)) (lsizenn1 (lanetype_Inn .I64)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))) ci_1_lst ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextbinop__ (.X .I64 (.mk_dim M_1)) (.X .I32 (.mk_dim M_2)) (.mk_vextbinop__0 .I64 M_1 .DOTS) c_1 c_2 c
  | fun_vextbinop___case_14 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci_2)) ci_2_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))) ci_1_lst ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextbinop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextbinop__0 .I64 M_1 .DOTS) c_1 c_2 c
  | fun_vextbinop___case_15 : forall (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c : uN) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_2))) ci_2)) ci_2_lst ->
    ((List.length cj_1_lst) == (List.length cj_2_lst)) ->
    Forall₂ (fun (cj_1 : iN) (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Inn .I64) (.mk_dim M_1))) (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2))))) cj_1_lst cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_2)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_1))) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__0 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_num__0 (Option.get! (proj_lane__0 ci_2))) != none)) ci_2_lst ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__0 ci_2) != none)) ci_2_lst ->
    ((concat_ iN (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => [cj_1, cj_2]) cj_1_lst cj_2_lst)) == (List.zipWith (fun (ci_1 : lane_) (ci_2 : lane_) => (imul_ (lsizenn1 (lanetype_Inn .I64)) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1))))) (extend__ (lsizenn2 (lanetype_Inn .I64)) (lsizenn1 (lanetype_Inn .I64)) .S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2))))))) ci_1_lst ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Inn .I64) (.mk_dim M_1)) (List.zipWith (fun (cj_1 : iN) (cj_2 : iN) => (.mk_lane__0 (numtype_Inn .I64) (.mk_num__0 .I64 (iadd_ (lsizenn1 (lanetype_Inn .I64)) cj_1 cj_2)))) cj_1_lst cj_2_lst))) ->
    fun_vextbinop__ (.X .I64 (.mk_dim M_1)) (.X .I64 (.mk_dim M_2)) (.mk_vextbinop__0 .I64 M_1 .DOTS) c_1 c_2 c

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 -/
inductive fun_vshiftop_ : ishape -> vshiftop_ -> lane_ -> u32 -> lane_ -> Prop where
  | fun_vshiftop__case_0 : forall (v_Jnn : Jnn) (v_M : Nat) (lane : uN) (v_n : Nat), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_lane__2 v_Jnn (ishl_ (lsizenn (lanetype_Jnn v_Jnn)) lane (.mk_uN v_n)))) ->
    fun_vshiftop_ (.X v_Jnn (.mk_dim v_M)) (.mk_vshiftop__0 v_Jnn v_M .SHL) (.mk_lane__2 v_Jnn lane) (.mk_uN v_n) (.mk_lane__2 v_Jnn (ishl_ (lsizenn (lanetype_Jnn v_Jnn)) lane (.mk_uN v_n)))
  | fun_vshiftop__case_1 : forall (v_Jnn : Jnn) (v_M : Nat) (v_sx : sx) (lane : uN) (v_n : Nat), 
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_lane__2 v_Jnn (ishr_ (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (.mk_uN v_n)))) ->
    fun_vshiftop_ (.X v_Jnn (.mk_dim v_M)) (.mk_vshiftop__0 v_Jnn v_M (.SHR v_sx)) (.mk_lane__2 v_Jnn lane) (.mk_uN v_n) (.mk_lane__2 v_Jnn (ishr_ (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (.mk_uN v_n)))

/- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:5.1-5.39 -/
abbrev addr : Type := Nat

/- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:6.1-6.53 -/
abbrev funcaddr : Type := addr

/- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:7.1-7.53 -/
abbrev globaladdr : Type := addr

/- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:8.1-8.51 -/
abbrev tableaddr : Type := addr

/- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:9.1-9.50 -/
abbrev memaddr : Type := addr

/- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:10.1-10.49 -/
abbrev elemaddr : Type := addr

/- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:11.1-11.49 -/
abbrev dataaddr : Type := addr

/- Type Alias Definition at: ../specification/wasm-2.0/4-runtime.spectec:12.1-12.49 -/
abbrev hostaddr : Type := addr

/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:25.1-26.70 -/
inductive externaddr : Type where
  | FUNC (v_funcaddr : funcaddr) : externaddr
  | GLOBAL (v_globaladdr : globaladdr) : externaddr
  | TABLE (v_tableaddr : tableaddr) : externaddr
  | MEM (v_memaddr : memaddr) : externaddr
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.1-38.62 -/
inductive num : Type where
  | CONST (v_numtype : numtype) (v_num_ : num_) : num
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.8-37.11 -/
inductive wf_num : num -> Prop where
  | num_case_0 : forall (v_numtype : numtype) (v_num_ : num_), 
    (wf_num_ v_numtype v_num_) ->
    wf_num (.CONST v_numtype v_num_)

/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.1-40.62 -/
inductive vec : Type where
  | VCONST (v_vectype : vectype) (v_vec_ : vec_) : vec
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.8-39.11 -/
inductive wf_vec : vec -> Prop where
  | vec_case_0 : forall (v_vectype : vectype) (v_vec_ : vec_), 
    ((size (valtype_vectype v_vectype)) != none) ->
    (wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_) ->
    wf_vec (.VCONST v_vectype v_vec_)

/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:41.1-42.71 -/
inductive ref : Type where
  | REF_NULL (v_reftype : reftype) : ref
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : ref
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : ref
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.1-44.20 -/
inductive val : Type where
  | CONST (v_numtype : numtype) (v_num_ : num_) : val
  | VCONST (v_vectype : vectype) (v_vec_ : vec_) : val
  | REF_NULL (v_reftype : reftype) : val
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : val
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : val
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def val_ref : ∀  (var_0 : ref) , val
  | (.REF_NULL x0) =>
    (.REF_NULL x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)


/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.8-43.11 -/
inductive wf_val : val -> Prop where
  | val_case_0 : forall (v_numtype : numtype) (v_num_ : num_), 
    (wf_num_ v_numtype v_num_) ->
    wf_val (.CONST v_numtype v_num_)
  | val_case_1 : forall (v_vectype : vectype) (v_vec_ : vec_), 
    ((size (valtype_vectype v_vectype)) != none) ->
    (wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_) ->
    wf_val (.VCONST v_vectype v_vec_)
  | val_case_2 : forall (v_reftype : reftype), wf_val (.REF_NULL v_reftype)
  | val_case_3 : forall (v_funcaddr : funcaddr), wf_val (.REF_FUNC_ADDR v_funcaddr)
  | val_case_4 : forall (v_hostaddr : hostaddr), wf_val (.REF_HOST_ADDR v_hostaddr)

/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.1-47.22 -/
inductive result : Type where
  | _VALS (val_lst : (List val)) : result
  | TRAP : result
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.8-46.14 -/
inductive wf_result : result -> Prop where
  | result_case_0 : forall (val_lst : (List val)), 
    Forall (fun (v_val : val) => (wf_val v_val)) val_lst ->
    wf_result (._VALS val_lst)
  | result_case_1 : wf_result .TRAP

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.1-80.22 -/
structure exportinst where MKexportinst ::
  NAME : name
  ADDR : externaddr
deriving Inhabited, BEq

def _append_exportinst (arg1 arg2 : (exportinst)) : exportinst where
  NAME := arg1.NAME /- FIXME - Non-trivial append -/
  ADDR := arg1.ADDR /- FIXME - Non-trivial append -/
instance : Append exportinst where
  append arg1 arg2 := _append_exportinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.8-78.18 -/
inductive wf_exportinst : exportinst -> Prop where
  | exportinst_case_ : forall (var_0 : name) (var_1 : externaddr), 
    (wf_name var_0) ->
    wf_exportinst { NAME := var_0, ADDR := var_1 }

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.1-90.26 -/
structure moduleinst where MKmoduleinst ::
  TYPES : (List functype)
  FUNCS : (List funcaddr)
  GLOBALS : (List globaladdr)
  TABLES : (List tableaddr)
  MEMS : (List memaddr)
  ELEMS : (List elemaddr)
  DATAS : (List dataaddr)
  EXPORTS : (List exportinst)
deriving Inhabited, BEq

def _append_moduleinst (arg1 arg2 : (moduleinst)) : moduleinst where
  TYPES := arg1.TYPES ++ arg2.TYPES
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  TABLES := arg1.TABLES ++ arg2.TABLES
  MEMS := arg1.MEMS ++ arg2.MEMS
  ELEMS := arg1.ELEMS ++ arg2.ELEMS
  DATAS := arg1.DATAS ++ arg2.DATAS
  EXPORTS := arg1.EXPORTS ++ arg2.EXPORTS
instance : Append moduleinst where
  append arg1 arg2 := _append_moduleinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.8-82.18 -/
inductive wf_moduleinst : moduleinst -> Prop where
  | moduleinst_case_ : forall (var_0 : (List functype)) (var_1 : (List funcaddr)) (var_2 : (List globaladdr)) (var_3 : (List tableaddr)) (var_4 : (List memaddr)) (var_5 : (List elemaddr)) (var_6 : (List dataaddr)) (var_7 : (List exportinst)), 
    Forall (fun (var_7 : exportinst) => (wf_exportinst var_7)) var_7 ->
    wf_moduleinst { TYPES := var_0, FUNCS := var_1, GLOBALS := var_2, TABLES := var_3, MEMS := var_4, ELEMS := var_5, DATAS := var_6, EXPORTS := var_7 }

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.1-63.16 -/
structure funcinst where MKfuncinst ::
  TYPE : functype
  MODULE : moduleinst
  CODE : func
deriving Inhabited, BEq

def _append_funcinst (arg1 arg2 : (funcinst)) : funcinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  MODULE := arg1.MODULE ++ arg2.MODULE
  CODE := arg1.CODE /- FIXME - Non-trivial append -/
instance : Append funcinst where
  append arg1 arg2 := _append_funcinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.8-60.16 -/
inductive wf_funcinst : funcinst -> Prop where
  | funcinst_case_ : forall (var_0 : functype) (var_1 : moduleinst) (var_2 : func), 
    (wf_moduleinst var_1) ->
    (wf_func var_2) ->
    wf_funcinst { TYPE := var_0, MODULE := var_1, CODE := var_2 }

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.1-66.16 -/
structure globalinst where MKglobalinst ::
  TYPE : globaltype
  VALUE : val
deriving Inhabited, BEq

def _append_globalinst (arg1 arg2 : (globalinst)) : globalinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  VALUE := arg1.VALUE /- FIXME - Non-trivial append -/
instance : Append globalinst where
  append arg1 arg2 := _append_globalinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.8-64.18 -/
inductive wf_globalinst : globalinst -> Prop where
  | globalinst_case_ : forall (var_0 : globaltype) (var_1 : val), 
    (wf_val var_1) ->
    wf_globalinst { TYPE := var_0, VALUE := var_1 }

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.1-69.16 -/
structure tableinst where MKtableinst ::
  TYPE : tabletype
  REFS : (List ref)
deriving Inhabited, BEq

def _append_tableinst (arg1 arg2 : (tableinst)) : tableinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  REFS := arg1.REFS ++ arg2.REFS
instance : Append tableinst where
  append arg1 arg2 := _append_tableinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.8-67.17 -/
inductive wf_tableinst : tableinst -> Prop where
  | tableinst_case_ : forall (var_0 : tabletype) (var_1 : (List ref)), 
    (wf_tabletype var_0) ->
    wf_tableinst { TYPE := var_0, REFS := var_1 }

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.1-72.18 -/
structure meminst where MKmeminst ::
  TYPE : memtype
  BYTES : (List byte)
deriving Inhabited, BEq

def _append_meminst (arg1 arg2 : (meminst)) : meminst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  BYTES := arg1.BYTES ++ arg2.BYTES
instance : Append meminst where
  append arg1 arg2 := _append_meminst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.8-70.15 -/
inductive wf_meminst : meminst -> Prop where
  | meminst_case_ : forall (var_0 : memtype) (var_1 : (List byte)), 
    (wf_memtype var_0) ->
    Forall (fun (var_1 : byte) => (wf_byte var_1)) var_1 ->
    wf_meminst { TYPE := var_0, BYTES := var_1 }

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:73.1-75.16 -/
structure eleminst where MKeleminst ::
  TYPE : elemtype
  REFS : (List ref)
deriving Inhabited, BEq

def _append_eleminst (arg1 arg2 : (eleminst)) : eleminst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  REFS := arg1.REFS ++ arg2.REFS
instance : Append eleminst where
  append arg1 arg2 := _append_eleminst arg1 arg2



/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.1-77.18 -/
structure datainst where MKdatainst ::
  BYTES : (List byte)
deriving Inhabited, BEq

def _append_datainst (arg1 arg2 : (datainst)) : datainst where
  BYTES := arg1.BYTES ++ arg2.BYTES
instance : Append datainst where
  append arg1 arg2 := _append_datainst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.8-76.16 -/
inductive wf_datainst : datainst -> Prop where
  | datainst_case_ : forall (var_0 : (List byte)), 
    Forall (fun (var_0 : byte) => (wf_byte var_0)) var_0 ->
    wf_datainst { BYTES := var_0 }

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.1-110.22 -/
structure store where MKstore ::
  FUNCS : (List funcinst)
  GLOBALS : (List globalinst)
  TABLES : (List tableinst)
  MEMS : (List meminst)
  ELEMS : (List eleminst)
  DATAS : (List datainst)
deriving Inhabited, BEq

def _append_store (arg1 arg2 : (store)) : store where
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  TABLES := arg1.TABLES ++ arg2.TABLES
  MEMS := arg1.MEMS ++ arg2.MEMS
  ELEMS := arg1.ELEMS ++ arg2.ELEMS
  DATAS := arg1.DATAS ++ arg2.DATAS
instance : Append store where
  append arg1 arg2 := _append_store arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.8-104.13 -/
inductive wf_store : store -> Prop where
  | store_case_ : forall (var_0 : (List funcinst)) (var_1 : (List globalinst)) (var_2 : (List tableinst)) (var_3 : (List meminst)) (var_4 : (List eleminst)) (var_5 : (List datainst)), 
    Forall (fun (var_0 : funcinst) => (wf_funcinst var_0)) var_0 ->
    Forall (fun (var_1 : globalinst) => (wf_globalinst var_1)) var_1 ->
    Forall (fun (var_2 : tableinst) => (wf_tableinst var_2)) var_2 ->
    Forall (fun (var_3 : meminst) => (wf_meminst var_3)) var_3 ->
    Forall (fun (var_5 : datainst) => (wf_datainst var_5)) var_5 ->
    wf_store { FUNCS := var_0, GLOBALS := var_1, TABLES := var_2, MEMS := var_3, ELEMS := var_4, DATAS := var_5 }

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.1-114.24 -/
structure frame where MKframe ::
  LOCALS : (List val)
  MODULE : moduleinst
deriving Inhabited, BEq

def _append_frame (arg1 arg2 : (frame)) : frame where
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
  MODULE := arg1.MODULE ++ arg2.MODULE
instance : Append frame where
  append arg1 arg2 := _append_frame arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.8-112.13 -/
inductive wf_frame : frame -> Prop where
  | frame_case_ : forall (var_0 : (List val)) (var_1 : moduleinst), 
    Forall (fun (var_0 : val) => (wf_val var_0)) var_0 ->
    (wf_moduleinst var_1) ->
    wf_frame { LOCALS := var_0, MODULE := var_1 }

/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.1-116.47 -/
inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.8-116.13 -/
inductive wf_state : state -> Prop where
  | state_case_0 : forall (v_store : store) (v_frame : frame), 
    (wf_store v_store) ->
    (wf_frame v_frame) ->
    wf_state (.mk_state v_store v_frame)

/- Recursive Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 -/
/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 -/
inductive admininstr : Type where
  | NOP : admininstr
  | UNREACHABLE : admininstr
  | DROP : admininstr
  | SELECT (valtype_lst_opt : (Option (List valtype))) : admininstr
  | BLOCK (v_blocktype : blocktype) (instr_lst : (List instr)) : admininstr
  | LOOP (v_blocktype : blocktype) (instr_lst : (List instr)) : admininstr
  | IFELSE (v_blocktype : blocktype) (instr_lst : (List instr)) (_ : (List instr)) : admininstr
  | BR (v_labelidx : labelidx) : admininstr
  | BR_IF (v_labelidx : labelidx) : admininstr
  | BR_TABLE (labelidx_lst : (List labelidx)) (_ : labelidx) : admininstr
  | CALL (v_funcidx : funcidx) : admininstr
  | CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : admininstr
  | RETURN : admininstr
  | CONST (v_numtype : numtype) (v_num_ : num_) : admininstr
  | UNOP (v_numtype : numtype) (v_unop_ : unop_) : admininstr
  | BINOP (v_numtype : numtype) (v_binop_ : binop_) : admininstr
  | TESTOP (v_numtype : numtype) (v_testop_ : testop_) : admininstr
  | RELOP (v_numtype : numtype) (v_relop_ : relop_) : admininstr
  | CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop) : admininstr
  | EXTEND (v_numtype : numtype) (v_n : n) : admininstr
  | VCONST (v_vectype : vectype) (v_vec_ : vec_) : admininstr
  | VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : admininstr
  | VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : admininstr
  | VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : admininstr
  | VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : admininstr
  | VUNOP (v_shape : shape) (v_vunop_ : vunop_) : admininstr
  | VBINOP (v_shape : shape) (v_vbinop_ : vbinop_) : admininstr
  | VTESTOP (v_shape : shape) (v_vtestop_ : vtestop_) : admininstr
  | VRELOP (v_shape : shape) (v_vrelop_ : vrelop_) : admininstr
  | VSHIFTOP (v_ishape : ishape) (v_vshiftop_ : vshiftop_) : admininstr
  | VBITMASK (v_ishape : ishape) : admininstr
  | VSWIZZLE (v_ishape : ishape) : admininstr
  | VSHUFFLE (v_ishape : ishape) (laneidx_lst : (List laneidx)) : admininstr
  | VSPLAT (v_shape : shape) : admininstr
  | VEXTRACT_LANE (v_shape : shape) (sx_opt : (Option sx)) (v_laneidx : laneidx) : admininstr
  | VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : admininstr
  | VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop_ : vextunop_) : admininstr
  | VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop_ : vextbinop_) : admininstr
  | VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : admininstr
  | VCVTOP (v_shape : shape) (_ : shape) (v_vcvtop : vcvtop) : admininstr
  | REF_NULL (v_reftype : reftype) : admininstr
  | REF_FUNC (v_funcidx : funcidx) : admininstr
  | REF_IS_NULL : admininstr
  | LOCAL_GET (v_localidx : localidx) : admininstr
  | LOCAL_SET (v_localidx : localidx) : admininstr
  | LOCAL_TEE (v_localidx : localidx) : admininstr
  | GLOBAL_GET (v_globalidx : globalidx) : admininstr
  | GLOBAL_SET (v_globalidx : globalidx) : admininstr
  | TABLE_GET (v_tableidx : tableidx) : admininstr
  | TABLE_SET (v_tableidx : tableidx) : admininstr
  | TABLE_SIZE (v_tableidx : tableidx) : admininstr
  | TABLE_GROW (v_tableidx : tableidx) : admininstr
  | TABLE_FILL (v_tableidx : tableidx) : admininstr
  | TABLE_COPY (v_tableidx : tableidx) (_ : tableidx) : admininstr
  | TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : admininstr
  | ELEM_DROP (v_elemidx : elemidx) : admininstr
  | LOAD (v_numtype : numtype) (loadop__opt : (Option loadop_)) (v_memarg : memarg) : admininstr
  | STORE (v_numtype : numtype) (sz_opt : (Option sz)) (v_memarg : memarg) : admininstr
  | VLOAD (v_vectype : vectype) (vloadop_opt : (Option vloadop)) (v_memarg : memarg) : admininstr
  | VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : admininstr
  | VSTORE (v_vectype : vectype) (v_memarg : memarg) : admininstr
  | VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : admininstr
  | MEMORY_SIZE : admininstr
  | MEMORY_GROW : admininstr
  | MEMORY_FILL : admininstr
  | MEMORY_COPY : admininstr
  | MEMORY_INIT (v_dataidx : dataidx) : admininstr
  | DATA_DROP (v_dataidx : dataidx) : admininstr
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : admininstr
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : admininstr
  | CALL_ADDR (v_funcaddr : funcaddr) : admininstr
  | LABEL_ (v_n : n) (instr_lst : (List instr)) (admininstr_lst : (List admininstr)) : admininstr
  | FRAME_ (v_n : n) (v_frame : frame) (admininstr_lst : (List admininstr)) : admininstr
  | TRAP : admininstr
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def admininstr_instr : ∀  (var_0 : instr) , admininstr
  | .NOP =>
    .NOP
  | .UNREACHABLE =>
    .UNREACHABLE
  | .DROP =>
    .DROP
  | (.SELECT x0) =>
    (.SELECT x0)
  | (.BLOCK x0 x1) =>
    (.BLOCK x0 x1)
  | (.LOOP x0 x1) =>
    (.LOOP x0 x1)
  | (.IFELSE x0 x1 x2) =>
    (.IFELSE x0 x1 x2)
  | (.BR x0) =>
    (.BR x0)
  | (.BR_IF x0) =>
    (.BR_IF x0)
  | (.BR_TABLE x0 x1) =>
    (.BR_TABLE x0 x1)
  | (.CALL x0) =>
    (.CALL x0)
  | (.CALL_INDIRECT x0 x1) =>
    (.CALL_INDIRECT x0 x1)
  | .RETURN =>
    .RETURN
  | (.CONST x0 x1) =>
    (.CONST x0 x1)
  | (.UNOP x0 x1) =>
    (.UNOP x0 x1)
  | (.BINOP x0 x1) =>
    (.BINOP x0 x1)
  | (.TESTOP x0 x1) =>
    (.TESTOP x0 x1)
  | (.RELOP x0 x1) =>
    (.RELOP x0 x1)
  | (.CVTOP x0 x1 x2) =>
    (.CVTOP x0 x1 x2)
  | (.EXTEND x0 x1) =>
    (.EXTEND x0 x1)
  | (.VCONST x0 x1) =>
    (.VCONST x0 x1)
  | (.VVUNOP x0 x1) =>
    (.VVUNOP x0 x1)
  | (.VVBINOP x0 x1) =>
    (.VVBINOP x0 x1)
  | (.VVTERNOP x0 x1) =>
    (.VVTERNOP x0 x1)
  | (.VVTESTOP x0 x1) =>
    (.VVTESTOP x0 x1)
  | (.VUNOP x0 x1) =>
    (.VUNOP x0 x1)
  | (.VBINOP x0 x1) =>
    (.VBINOP x0 x1)
  | (.VTESTOP x0 x1) =>
    (.VTESTOP x0 x1)
  | (.VRELOP x0 x1) =>
    (.VRELOP x0 x1)
  | (.VSHIFTOP x0 x1) =>
    (.VSHIFTOP x0 x1)
  | (.VBITMASK x0) =>
    (.VBITMASK x0)
  | (.VSWIZZLE x0) =>
    (.VSWIZZLE x0)
  | (.VSHUFFLE x0 x1) =>
    (.VSHUFFLE x0 x1)
  | (.VSPLAT x0) =>
    (.VSPLAT x0)
  | (.VEXTRACT_LANE x0 x1 x2) =>
    (.VEXTRACT_LANE x0 x1 x2)
  | (.VREPLACE_LANE x0 x1) =>
    (.VREPLACE_LANE x0 x1)
  | (.VEXTUNOP x0 x1 x2) =>
    (.VEXTUNOP x0 x1 x2)
  | (.VEXTBINOP x0 x1 x2) =>
    (.VEXTBINOP x0 x1 x2)
  | (.VNARROW x0 x1 x2) =>
    (.VNARROW x0 x1 x2)
  | (.VCVTOP x0 x1 x2) =>
    (.VCVTOP x0 x1 x2)
  | (.REF_NULL x0) =>
    (.REF_NULL x0)
  | (.REF_FUNC x0) =>
    (.REF_FUNC x0)
  | .REF_IS_NULL =>
    .REF_IS_NULL
  | (.LOCAL_GET x0) =>
    (.LOCAL_GET x0)
  | (.LOCAL_SET x0) =>
    (.LOCAL_SET x0)
  | (.LOCAL_TEE x0) =>
    (.LOCAL_TEE x0)
  | (.GLOBAL_GET x0) =>
    (.GLOBAL_GET x0)
  | (.GLOBAL_SET x0) =>
    (.GLOBAL_SET x0)
  | (.TABLE_GET x0) =>
    (.TABLE_GET x0)
  | (.TABLE_SET x0) =>
    (.TABLE_SET x0)
  | (.TABLE_SIZE x0) =>
    (.TABLE_SIZE x0)
  | (.TABLE_GROW x0) =>
    (.TABLE_GROW x0)
  | (.TABLE_FILL x0) =>
    (.TABLE_FILL x0)
  | (.TABLE_COPY x0 x1) =>
    (.TABLE_COPY x0 x1)
  | (.TABLE_INIT x0 x1) =>
    (.TABLE_INIT x0 x1)
  | (.ELEM_DROP x0) =>
    (.ELEM_DROP x0)
  | (.LOAD x0 x1 x2) =>
    (.LOAD x0 x1 x2)
  | (.STORE x0 x1 x2) =>
    (.STORE x0 x1 x2)
  | (.VLOAD x0 x1 x2) =>
    (.VLOAD x0 x1 x2)
  | (.VLOAD_LANE x0 x1 x2 x3) =>
    (.VLOAD_LANE x0 x1 x2 x3)
  | (.VSTORE x0 x1) =>
    (.VSTORE x0 x1)
  | (.VSTORE_LANE x0 x1 x2 x3) =>
    (.VSTORE_LANE x0 x1 x2 x3)
  | .MEMORY_SIZE =>
    .MEMORY_SIZE
  | .MEMORY_GROW =>
    .MEMORY_GROW
  | .MEMORY_FILL =>
    .MEMORY_FILL
  | .MEMORY_COPY =>
    .MEMORY_COPY
  | (.MEMORY_INIT x0) =>
    (.MEMORY_INIT x0)
  | (.DATA_DROP x0) =>
    (.DATA_DROP x0)


/- Auxiliary Definition at:  -/
def admininstr_ref : ∀  (var_0 : ref) , admininstr
  | (.REF_NULL x0) =>
    (.REF_NULL x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)


/- Auxiliary Definition at:  -/
def admininstr_val : ∀  (var_0 : val) , admininstr
  | (.CONST x0 x1) =>
    (.CONST x0 x1)
  | (.VCONST x0 x1) =>
    (.VCONST x0 x1)
  | (.REF_NULL x0) =>
    (.REF_NULL x0)
  | (.REF_FUNC_ADDR x0) =>
    (.REF_FUNC_ADDR x0)
  | (.REF_HOST_ADDR x0) =>
    (.REF_HOST_ADDR x0)


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.1-117.62 -/
inductive config : Type where
  | mk_config (v_state : state) (admininstr_lst : (List admininstr)) : config
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.8-117.14 -/
inductive wf_config : config -> Prop where
  | config_case_0 : forall (v_state : state) (admininstr_lst : (List admininstr)), 
    (wf_state v_state) ->
    Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
    wf_config (.mk_config v_state admininstr_lst)

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.1-7.29 -/
def default_ : ∀  (v_valtype : valtype) , val
  | .I32 =>
    (.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)))
  | .I64 =>
    (.CONST .I64 (.mk_num__0 .I64 (.mk_uN 0)))
  | .F32 =>
    (.CONST .F32 (.mk_num__1 .F32 (fzero 32)))
  | .F64 =>
    (.CONST .F64 (.mk_num__1 .F64 (fzero 64)))
  | .V128 =>
    (.VCONST .V128 (.mk_uN 0))
  | .FUNCREF =>
    (.REF_NULL .FUNCREF)
  | .EXTERNREF =>
    (.REF_NULL .EXTERNREF)


/- Recursive Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.1-20.63 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.6-20.14 -/
inductive fun_funcsxa : (List externaddr) -> (List funcaddr) -> Prop where
  | fun_funcsxa_case_0 : fun_funcsxa [] []
  | fun_funcsxa_case_1 : forall (fa : Nat) (xv_lst : (List externaddr)) (var_0 : (List funcaddr)), 
    (fun_funcsxa xv_lst var_0) ->
    fun_funcsxa ([(.FUNC fa)] ++ xv_lst) ([fa] ++ var_0)
  | fun_funcsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (List externaddr)) (var_0 : (List funcaddr)), 
    (fun_funcsxa xv_lst var_0) ->
    fun_funcsxa ([v_externaddr] ++ xv_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.1-21.65 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.6-21.16 -/
inductive fun_globalsxa : (List externaddr) -> (List globaladdr) -> Prop where
  | fun_globalsxa_case_0 : fun_globalsxa [] []
  | fun_globalsxa_case_1 : forall (ga : Nat) (xv_lst : (List externaddr)) (var_0 : (List globaladdr)), 
    (fun_globalsxa xv_lst var_0) ->
    fun_globalsxa ([(.GLOBAL ga)] ++ xv_lst) ([ga] ++ var_0)
  | fun_globalsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (List externaddr)) (var_0 : (List globaladdr)), 
    (fun_globalsxa xv_lst var_0) ->
    fun_globalsxa ([v_externaddr] ++ xv_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.1-22.64 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.6-22.15 -/
inductive fun_tablesxa : (List externaddr) -> (List tableaddr) -> Prop where
  | fun_tablesxa_case_0 : fun_tablesxa [] []
  | fun_tablesxa_case_1 : forall (ta : Nat) (xv_lst : (List externaddr)) (var_0 : (List tableaddr)), 
    (fun_tablesxa xv_lst var_0) ->
    fun_tablesxa ([(.TABLE ta)] ++ xv_lst) ([ta] ++ var_0)
  | fun_tablesxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (List externaddr)) (var_0 : (List tableaddr)), 
    (fun_tablesxa xv_lst var_0) ->
    fun_tablesxa ([v_externaddr] ++ xv_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.1-23.62 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.6-23.13 -/
inductive fun_memsxa : (List externaddr) -> (List memaddr) -> Prop where
  | fun_memsxa_case_0 : fun_memsxa [] []
  | fun_memsxa_case_1 : forall (ma : Nat) (xv_lst : (List externaddr)) (var_0 : (List memaddr)), 
    (fun_memsxa xv_lst var_0) ->
    fun_memsxa ([(.MEM ma)] ++ xv_lst) ([ma] ++ var_0)
  | fun_memsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (List externaddr)) (var_0 : (List memaddr)), 
    (fun_memsxa xv_lst var_0) ->
    fun_memsxa ([v_externaddr] ++ xv_lst) var_0

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.1-48.57 -/
def fun_store : ∀  (v_state : state) , store
  | (.mk_state s f) =>
    s


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57 -/
def fun_frame : ∀  (v_state : state) , frame
  | (.mk_state s f) =>
    f


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:55.1-55.64 -/
def fun_funcaddr : ∀  (v_state : state) , (List funcaddr)
  | (.mk_state s f) =>
    ((f.MODULE).FUNCS)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.1-58.57 -/
def fun_funcinst : ∀  (v_state : state) , (List funcinst)
  | (.mk_state s f) =>
    (s.FUNCS)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59 -/
def fun_globalinst : ∀  (v_state : state) , (List globalinst)
  | (.mk_state s f) =>
    (s.GLOBALS)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58 -/
def fun_tableinst : ∀  (v_state : state) , (List tableinst)
  | (.mk_state s f) =>
    (s.TABLES)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56 -/
def fun_meminst : ∀  (v_state : state) , (List meminst)
  | (.mk_state s f) =>
    (s.MEMS)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:62.1-62.57 -/
def fun_eleminst : ∀  (v_state : state) , (List eleminst)
  | (.mk_state s f) =>
    (s.ELEMS)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.1-63.57 -/
def fun_datainst : ∀  (v_state : state) , (List datainst)
  | (.mk_state s f) =>
    (s.DATAS)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58 -/
def fun_moduleinst : ∀  (v_state : state) , moduleinst
  | (.mk_state s f) =>
    (f.MODULE)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:74.1-74.66 -/
def fun_type : ∀  (v_state : state) (v_typeidx : typeidx) , functype
  | (.mk_state s f), x =>
    (((f.MODULE).TYPES)[(proj_uN_0 x)]!)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.1-75.66 -/
def fun_func : ∀  (v_state : state) (v_funcidx : funcidx) , funcinst
  | (.mk_state s f), x =>
    ((s.FUNCS)[(((f.MODULE).FUNCS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68 -/
def fun_global : ∀  (v_state : state) (v_globalidx : globalidx) , globalinst
  | (.mk_state s f), x =>
    ((s.GLOBALS)[(((f.MODULE).GLOBALS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67 -/
def fun_table : ∀  (v_state : state) (v_tableidx : tableidx) , tableinst
  | (.mk_state s f), x =>
    ((s.TABLES)[(((f.MODULE).TABLES)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65 -/
def fun_mem : ∀  (v_state : state) (v_memidx : memidx) , meminst
  | (.mk_state s f), x =>
    ((s.MEMS)[(((f.MODULE).MEMS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:79.1-79.66 -/
def fun_elem : ∀  (v_state : state) (v_tableidx : tableidx) , eleminst
  | (.mk_state s f), x =>
    ((s.ELEMS)[(((f.MODULE).ELEMS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.1-80.66 -/
def fun_data : ∀  (v_state : state) (v_dataidx : dataidx) , datainst
  | (.mk_state s f), x =>
    ((s.DATAS)[(((f.MODULE).DATAS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67 -/
def fun_local : ∀  (v_state : state) (v_localidx : localidx) , val
  | (.mk_state s f), x =>
    ((f.LOCALS)[(proj_uN_0 x)]!)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89 -/
def with_local : ∀  (v_state : state) (v_localidx : localidx) (v_val : val) , state
  | (.mk_state s f), x, v =>
    (.mk_state s (f <| LOCALS := (List.modify (f.LOCALS) (proj_uN_0 x) (fun (_ : val) => v)) |>))


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96 -/
def with_global : ∀  (v_state : state) (v_globalidx : globalidx) (v_val : val) , state
  | (.mk_state s f), x, v =>
    (.mk_state (s <| GLOBALS := (list_update_func (s.GLOBALS) (((f.MODULE).GLOBALS)[(proj_uN_0 x)]!) (fun (var_1 : globalinst) => (var_1 <| VALUE := v |>))) |>) f)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97 -/
def with_table : ∀  (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_ref : ref) , state
  | (.mk_state s f), x, i, r =>
    (.mk_state (s <| TABLES := (list_update_func (s.TABLES) (((f.MODULE).TABLES)[(proj_uN_0 x)]!) (fun (var_1 : tableinst) => (var_1 <| REFS := (List.modify (var_1.REFS) i (fun (_ : ref) => r)) |>))) |>) f)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89 -/
def with_tableinst : ∀  (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) , state
  | (.mk_state s f), x, ti =>
    (.mk_state (s <| TABLES := (List.modify (s.TABLES) (((f.MODULE).TABLES)[(proj_uN_0 x)]!) (fun (_ : tableinst) => ti)) |>) f)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100 -/
def with_mem : ∀  (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0 : (List byte)) , state
  | (.mk_state s f), x, i, j, b_lst =>
    (.mk_state (s <| MEMS := (list_update_func (s.MEMS) (((f.MODULE).MEMS)[(proj_uN_0 x)]!) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (var_1.BYTES) i j b_lst) |>))) |>) f)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87 -/
def with_meminst : ∀  (v_state : state) (v_memidx : memidx) (v_meminst : meminst) , state
  | (.mk_state s f), x, mi =>
    (.mk_state (s <| MEMS := (List.modify (s.MEMS) (((f.MODULE).MEMS)[(proj_uN_0 x)]!) (fun (_ : meminst) => mi)) |>) f)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93 -/
def with_elem : ∀  (v_state : state) (v_elemidx : elemidx) (var_0 : (List ref)) , state
  | (.mk_state s f), x, r_lst =>
    (.mk_state (s <| ELEMS := (list_update_func (s.ELEMS) (((f.MODULE).ELEMS)[(proj_uN_0 x)]!) (fun (var_1 : eleminst) => (var_1 <| REFS := r_lst |>))) |>) f)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94 -/
def with_data : ∀  (v_state : state) (v_dataidx : dataidx) (var_0 : (List byte)) , state
  | (.mk_state s f), x, b_lst =>
    (.mk_state (s <| DATAS := (list_update_func (s.DATAS) (((f.MODULE).DATAS)[(proj_uN_0 x)]!) (fun (var_1 : datainst) => (var_1 <| BYTES := b_lst |>))) |>) f)


/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 -/
inductive fun_growtable : tableinst -> Nat -> ref -> (Option tableinst) -> Prop where
  | fun_growtable_case_0 : forall (ti : tableinst) (v_n : Nat) (r : ref) (ti' : tableinst) (i : uN) (j_opt : (Option u32)) (rt : reftype) (r'_lst : (List ref)) (i' : Nat), 
    (ti == { TYPE := (.mk_tabletype (.mk_limits i j_opt) rt), REFS := r'_lst }) ->
    (i' == ((List.length r'_lst) + v_n)) ->
    Forall (fun (j : u32) => (i' <= (proj_uN_0 j))) (Option.toList j_opt) ->
    (ti' == { TYPE := (.mk_tabletype (.mk_limits (.mk_uN i') j_opt) rt), REFS := (r'_lst ++ (List.replicate v_n r)) }) ->
    fun_growtable ti v_n r (some ti')
  | fun_growtable_case_1 : forall (x0 : tableinst) (x1 : Nat) (x2 : ref), fun_growtable x0 x1 x2 none

/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 -/
inductive fun_growmemory : meminst -> Nat -> (Option meminst) -> Prop where
  | fun_growmemory_case_0 : forall (mi : meminst) (v_n : Nat) (mi' : meminst) (i : uN) (j_opt : (Option u32)) (b_lst : (List byte)) (i' : Nat), 
    (mi == { TYPE := (.PAGE (.mk_limits i j_opt)), BYTES := b_lst }) ->
    (i' == ((((List.length b_lst) : Nat) / ((64 * (Ki )) : Nat)) + (v_n : Nat))) ->
    Forall (fun (j : u32) => (i' <= ((proj_uN_0 j) : Nat))) (Option.toList j_opt) ->
    (mi' == { TYPE := (.PAGE (.mk_limits (.mk_uN (i' : Nat)) j_opt)), BYTES := (b_lst ++ (List.replicate (v_n * (64 * (Ki ))) (.mk_byte 0))) }) ->
    fun_growmemory mi v_n (some mi')
  | fun_growmemory_case_1 : forall (x0 : meminst) (x1 : Nat), fun_growmemory x0 x1 none

/- Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 -/
structure context where MKcontext ::
  TYPES : (List functype)
  FUNCS : (List functype)
  GLOBALS : (List globaltype)
  TABLES : (List tabletype)
  MEMS : (List memtype)
  ELEMS : (List elemtype)
  DATAS : (List datatype)
  LOCALS : (List valtype)
  LABELS : (List resulttype)
  RETURN : (Option resulttype)
deriving Inhabited, BEq

def _append_context (arg1 arg2 : (context)) : context where
  TYPES := arg1.TYPES ++ arg2.TYPES
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  TABLES := arg1.TABLES ++ arg2.TABLES
  MEMS := arg1.MEMS ++ arg2.MEMS
  ELEMS := arg1.ELEMS ++ arg2.ELEMS
  DATAS := arg1.DATAS ++ arg2.DATAS
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
  LABELS := arg1.LABELS ++ arg2.LABELS
  RETURN := arg1.RETURN ++ arg2.RETURN
instance : Append context where
  append arg1 arg2 := _append_context arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:5.8-5.15 -/
inductive wf_context : context -> Prop where
  | context_case_ : forall (var_0 : (List functype)) (var_1 : (List functype)) (var_2 : (List globaltype)) (var_3 : (List tabletype)) (var_4 : (List memtype)) (var_5 : (List elemtype)) (var_6 : (List datatype)) (var_7 : (List valtype)) (var_8 : (List resulttype)) (var_9 : (Option resulttype)), 
    Forall (fun (var_3 : tabletype) => (wf_tabletype var_3)) var_3 ->
    Forall (fun (var_4 : memtype) => (wf_memtype var_4)) var_4 ->
    wf_context { TYPES := var_0, FUNCS := var_1, GLOBALS := var_2, TABLES := var_3, MEMS := var_4, ELEMS := var_5, DATAS := var_6, LOCALS := var_7, LABELS := var_8, RETURN := var_9 }

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:19.1-19.66 -/
inductive Limits_ok : limits -> Nat -> Prop where
  | mk_Limits_ok : forall (v_n : n) (m_opt : (Option m)) (k : Nat), 
    (v_n <= k) ->
    Forall (fun (v_m : Nat) => ((v_n <= v_m) && (v_m <= k))) (Option.toList m_opt) ->
    Limits_ok (.mk_limits (.mk_uN v_n) (Option.map (fun (v_m : m) => (.mk_uN v_m)) m_opt)) k

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:20.1-20.64 -/
inductive Functype_ok : functype -> Prop where
  | mk_Functype_ok : forall (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), Functype_ok (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:21.1-21.66 -/
inductive Globaltype_ok : globaltype -> Prop where
  | mk_Globaltype_ok : forall (t : valtype), Globaltype_ok (.mk_globaltype (some .MUT) t)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:22.1-22.65 -/
inductive Tabletype_ok : tabletype -> Prop where
  | mk_Tabletype_ok : forall (v_limits : limits) (v_reftype : reftype), 
    (Limits_ok v_limits ((((2 ^ 32) : Nat) - (1 : Nat)) : Nat)) ->
    Tabletype_ok (.mk_tabletype v_limits v_reftype)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:23.1-23.63 -/
inductive Memtype_ok : memtype -> Prop where
  | mk_Memtype_ok : forall (v_limits : limits), 
    (Limits_ok v_limits (2 ^ 16)) ->
    Memtype_ok (.PAGE v_limits)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:24.1-24.66 -/
inductive Externtype_ok : externtype -> Prop where
  | func : forall (v_functype : functype), 
    (Functype_ok v_functype) ->
    Externtype_ok (.FUNC v_functype)
  | global : forall (v_globaltype : globaltype), 
    (Globaltype_ok v_globaltype) ->
    Externtype_ok (.GLOBAL v_globaltype)
  | table : forall (v_tabletype : tabletype), 
    (Tabletype_ok v_tabletype) ->
    Externtype_ok (.TABLE v_tabletype)
  | mem : forall (v_memtype : memtype), 
    (Memtype_ok v_memtype) ->
    Externtype_ok (.MEM v_memtype)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:71.1-71.69 -/
inductive Valtype_sub : valtype -> valtype -> Prop where
  | refl : forall (t : valtype), Valtype_sub t t
  | bot : forall (t : valtype), Valtype_sub .BOT t

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:72.1-72.76 -/
inductive Resulttype_sub : resulttype -> resulttype -> Prop where
  | mk_Resulttype_sub : forall (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((List.length t_1_lst) == (List.length t_2_lst)) ->
    Forall₂ (fun (t_1 : valtype) (t_2 : valtype) => (Valtype_sub t_1 t_2)) t_1_lst t_2_lst ->
    Resulttype_sub (.mk_list t_1_lst) (.mk_list t_2_lst)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:87.1-87.75 -/
inductive Limits_sub : limits -> limits -> Prop where
  | mk_Limits_sub : forall (n_11 : n) (n_12 : n) (n_21 : n) (n_22 : n), 
    (n_11 >= n_21) ->
    (n_12 <= n_22) ->
    Limits_sub (.mk_limits (.mk_uN n_11) (some (.mk_uN n_12))) (.mk_limits (.mk_uN n_21) (some (.mk_uN n_22)))

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:88.1-88.73 -/
inductive Functype_sub : functype -> functype -> Prop where
  | mk_Functype_sub : forall (ft : functype), Functype_sub ft ft

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:89.1-89.75 -/
inductive Globaltype_sub : globaltype -> globaltype -> Prop where
  | mk_Globaltype_sub : forall (gt : globaltype), Globaltype_sub gt gt

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:90.1-90.74 -/
inductive Tabletype_sub : tabletype -> tabletype -> Prop where
  | mk_Tabletype_sub : forall (lim_1 : limits) (rt : reftype) (lim_2 : limits), 
    (Limits_sub lim_1 lim_2) ->
    Tabletype_sub (.mk_tabletype lim_1 rt) (.mk_tabletype lim_2 rt)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:91.1-91.72 -/
inductive Memtype_sub : memtype -> memtype -> Prop where
  | mk_Memtype_sub : forall (lim_1 : limits) (lim_2 : limits), 
    (Limits_sub lim_1 lim_2) ->
    Memtype_sub (.PAGE lim_1) (.PAGE lim_2)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:92.1-92.75 -/
inductive Externtype_sub : externtype -> externtype -> Prop where
  | func : forall (ft_1 : functype) (ft_2 : functype), 
    (Functype_sub ft_1 ft_2) ->
    Externtype_sub (.FUNC ft_1) (.FUNC ft_2)
  | global : forall (gt_1 : globaltype) (gt_2 : globaltype), 
    (Globaltype_sub gt_1 gt_2) ->
    Externtype_sub (.GLOBAL gt_1) (.GLOBAL gt_2)
  | table : forall (tt_1 : tabletype) (tt_2 : tabletype), 
    (Tabletype_sub tt_1 tt_2) ->
    Externtype_sub (.TABLE tt_1) (.TABLE tt_2)
  | mem : forall (mt_1 : memtype) (mt_2 : memtype), 
    (Memtype_sub mt_1 mt_2) ->
    Externtype_sub (.MEM mt_1) (.MEM mt_2)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:194.1-194.76 -/
inductive Blocktype_ok : context -> blocktype -> functype -> Prop where
  | valtype : forall (C : context) (valtype_opt : (Option valtype)), Blocktype_ok C (._RESULT valtype_opt) (.mk_functype (.mk_list []) (.mk_list (Option.toList valtype_opt)))
  | typeidx : forall (C : context) (v_typeidx : typeidx) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 v_typeidx) < (List.length (C.TYPES))) ->
    (((C.TYPES)[(proj_uN_0 v_typeidx)]!) == (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Blocktype_ok C (._IDX v_typeidx) (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))

/- Recursive Definitions at: ../specification/wasm-2.0/6-typing.spectec:137.1-138.65 -/
mutual
/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:137.1-137.64 -/
inductive Instr_ok : context -> instr -> functype -> Prop where
  | nop : forall (C : context), Instr_ok C .NOP (.mk_functype (.mk_list []) (.mk_list []))
  | unreachable : forall (C : context) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), Instr_ok C .UNREACHABLE (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | drop : forall (C : context) (t : valtype), Instr_ok C .DROP (.mk_functype (.mk_list [t]) (.mk_list []))
  | select_expl : forall (C : context) (t : valtype), Instr_ok C (.SELECT (some [t])) (.mk_functype (.mk_list [t, t, .I32]) (.mk_list [t]))
  | select_impl : forall (C : context) (t : valtype) (t' : valtype) (v_numtype : numtype) (v_vectype : vectype), 
    (Valtype_sub t t') ->
    ((t' == (valtype_numtype v_numtype)) || (t' == (valtype_vectype v_vectype))) ->
    Instr_ok C (.SELECT none) (.mk_functype (.mk_list [t, t, .I32]) (.mk_list [t]))
  | block : forall (C : context) (bt : blocktype) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Blocktype_ok C bt (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [(.mk_list t_2_lst)], RETURN := none } ++ C) instr_lst (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instr_ok C (.BLOCK bt instr_lst) (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | loop : forall (C : context) (bt : blocktype) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Blocktype_ok C bt (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [(.mk_list t_1_lst)], RETURN := none } ++ C) instr_lst (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instr_ok C (.LOOP bt instr_lst) (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | if : forall (C : context) (bt : blocktype) (instr_1_lst : (List instr)) (instr_2_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Blocktype_ok C bt (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [(.mk_list t_2_lst)], RETURN := none } ++ C) instr_1_lst (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    (Instrs_ok ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [(.mk_list t_2_lst)], RETURN := none } ++ C) instr_2_lst (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instr_ok C (.IFELSE bt instr_1_lst instr_2_lst) (.mk_functype (.mk_list (t_1_lst ++ [.I32])) (.mk_list t_2_lst))
  | br : forall (C : context) (l : labelidx) (t_1_lst : (List valtype)) (t_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    ((proj_list_0 valtype ((C.LABELS)[(proj_uN_0 l)]!)) == t_lst) ->
    Instr_ok C (.BR l) (.mk_functype (.mk_list (t_1_lst ++ t_lst)) (.mk_list t_2_lst))
  | br_if : forall (C : context) (l : labelidx) (t_lst : (List valtype)), 
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    ((proj_list_0 valtype ((C.LABELS)[(proj_uN_0 l)]!)) == t_lst) ->
    Instr_ok C (.BR_IF l) (.mk_functype (.mk_list (t_lst ++ [.I32])) (.mk_list t_lst))
  | br_table : forall (C : context) (l_lst : (List labelidx)) (l' : labelidx) (t_1_lst : (List valtype)) (t_lst : (List valtype)) (t_2_lst : (List valtype)), 
    Forall (fun (l : labelidx) => ((proj_uN_0 l) < (List.length (C.LABELS)))) l_lst ->
    Forall (fun (l : labelidx) => (Resulttype_sub (.mk_list t_lst) ((C.LABELS)[(proj_uN_0 l)]!))) l_lst ->
    ((proj_uN_0 l') < (List.length (C.LABELS))) ->
    (Resulttype_sub (.mk_list t_lst) ((C.LABELS)[(proj_uN_0 l')]!)) ->
    Instr_ok C (.BR_TABLE l_lst l') (.mk_functype (.mk_list (t_1_lst ++ (t_lst ++ [.I32]))) (.mk_list t_2_lst))
  | call : forall (C : context) (x : idx) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instr_ok C (.CALL x) (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | call_indirect : forall (C : context) (x : idx) (y : idx) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype lim .FUNCREF)) ->
    ((proj_uN_0 y) < (List.length (C.TYPES))) ->
    (((C.TYPES)[(proj_uN_0 y)]!) == (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instr_ok C (.CALL_INDIRECT x y) (.mk_functype (.mk_list (t_1_lst ++ [.I32])) (.mk_list t_2_lst))
  | return : forall (C : context) (t_1_lst : (List valtype)) (t_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((C.RETURN) == (some (.mk_list t_lst))) ->
    Instr_ok C .RETURN (.mk_functype (.mk_list (t_1_lst ++ t_lst)) (.mk_list t_2_lst))
  | const : forall (C : context) (nt : numtype) (c_nt : num_), 
    (wf_num_ nt c_nt) ->
    Instr_ok C (.CONST nt c_nt) (.mk_functype (.mk_list []) (.mk_list [(valtype_numtype nt)]))
  | unop : forall (C : context) (nt : numtype) (unop_nt : unop_), 
    (wf_unop_ nt unop_nt) ->
    Instr_ok C (.UNOP nt unop_nt) (.mk_functype (.mk_list [(valtype_numtype nt)]) (.mk_list [(valtype_numtype nt)]))
  | binop : forall (C : context) (nt : numtype) (binop_nt : binop_), 
    (wf_binop_ nt binop_nt) ->
    Instr_ok C (.BINOP nt binop_nt) (.mk_functype (.mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (.mk_list [(valtype_numtype nt)]))
  | testop : forall (C : context) (nt : numtype) (testop_nt : testop_), 
    (wf_testop_ nt testop_nt) ->
    Instr_ok C (.TESTOP nt testop_nt) (.mk_functype (.mk_list [(valtype_numtype nt)]) (.mk_list [.I32]))
  | relop : forall (C : context) (nt : numtype) (relop_nt : relop_), 
    (wf_relop_ nt relop_nt) ->
    Instr_ok C (.RELOP nt relop_nt) (.mk_functype (.mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (.mk_list [.I32]))
  | cvtop_reinterpret : forall (C : context) (nt_1 : numtype) (nt_2 : numtype), 
    ((size (valtype_numtype nt_1)) != none) ->
    ((size (valtype_numtype nt_2)) != none) ->
    ((Option.get! (size (valtype_numtype nt_1))) == (Option.get! (size (valtype_numtype nt_2)))) ->
    Instr_ok C (.CVTOP nt_1 nt_2 .REINTERPRET) (.mk_functype (.mk_list [(valtype_numtype nt_2)]) (.mk_list [(valtype_numtype nt_1)]))
  | cvtop_convert : forall (C : context) (nt_1 : numtype) (nt_2 : numtype) (v_cvtop : cvtop), Instr_ok C (.CVTOP nt_1 nt_2 v_cvtop) (.mk_functype (.mk_list [(valtype_numtype nt_2)]) (.mk_list [(valtype_numtype nt_1)]))
  | ref_null : forall (C : context) (rt : reftype), Instr_ok C (.REF_NULL rt) (.mk_functype (.mk_list []) (.mk_list [(valtype_reftype rt)]))
  | ref_func : forall (C : context) (x : idx) (ft : functype), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == ft) ->
    Instr_ok C (.REF_FUNC x) (.mk_functype (.mk_list []) (.mk_list [.FUNCREF]))
  | ref_is_null : forall (C : context) (rt : reftype), Instr_ok C .REF_IS_NULL (.mk_functype (.mk_list [(valtype_reftype rt)]) (.mk_list [.I32]))
  | vconst : forall (C : context) (c : vec_), Instr_ok C (.VCONST .V128 c) (.mk_functype (.mk_list []) (.mk_list [.V128]))
  | vvunop : forall (C : context) (v_vvunop : vvunop), Instr_ok C (.VVUNOP .V128 v_vvunop) (.mk_functype (.mk_list [.V128]) (.mk_list [.V128]))
  | vvbinop : forall (C : context) (v_vvbinop : vvbinop), Instr_ok C (.VVBINOP .V128 v_vvbinop) (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128]))
  | vvternop : forall (C : context) (v_vvternop : vvternop), Instr_ok C (.VVTERNOP .V128 v_vvternop) (.mk_functype (.mk_list [.V128, .V128, .V128]) (.mk_list [.V128]))
  | vvtestop : forall (C : context) (v_vvtestop : vvtestop), Instr_ok C (.VVTESTOP .V128 v_vvtestop) (.mk_functype (.mk_list [.V128]) (.mk_list [.I32]))
  | vunop : forall (C : context) (sh : shape) (vunop_sh : vunop_), 
    (wf_vunop_ sh vunop_sh) ->
    Instr_ok C (.VUNOP sh vunop_sh) (.mk_functype (.mk_list [.V128]) (.mk_list [.V128]))
  | vbinop : forall (C : context) (sh : shape) (vbinop_sh : vbinop_), 
    (wf_vbinop_ sh vbinop_sh) ->
    Instr_ok C (.VBINOP sh vbinop_sh) (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128]))
  | vtestop : forall (C : context) (sh : shape) (vtestop_sh : vtestop_), 
    (wf_vtestop_ sh vtestop_sh) ->
    Instr_ok C (.VTESTOP sh vtestop_sh) (.mk_functype (.mk_list [.V128]) (.mk_list [.I32]))
  | vrelop : forall (C : context) (sh : shape) (vrelop_sh : vrelop_), 
    (wf_vrelop_ sh vrelop_sh) ->
    Instr_ok C (.VRELOP sh vrelop_sh) (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128]))
  | vshiftop : forall (C : context) (sh : ishape) (vshiftop_sh : vshiftop_), 
    (wf_vshiftop_ sh vshiftop_sh) ->
    Instr_ok C (.VSHIFTOP sh vshiftop_sh) (.mk_functype (.mk_list [.V128, .I32]) (.mk_list [.V128]))
  | vbitmask : forall (C : context) (sh : ishape), Instr_ok C (.VBITMASK sh) (.mk_functype (.mk_list [.V128]) (.mk_list [.I32]))
  | vswizzle : forall (C : context) (sh : ishape), Instr_ok C (.VSWIZZLE sh) (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128]))
  | vshuffle : forall (C : context) (sh : ishape) (i_lst : (List laneidx)), 
    Forall (fun (i : laneidx) => ((proj_uN_0 i) < (2 * (proj_dim_0 (fun_dim (shape_ishape sh)))))) i_lst ->
    Instr_ok C (.VSHUFFLE sh i_lst) (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128]))
  | vsplat : forall (C : context) (sh : shape), Instr_ok C (.VSPLAT sh) (.mk_functype (.mk_list [(valtype_numtype (shunpack sh))]) (.mk_list [.V128]))
  | vextract_lane : forall (C : context) (sh : shape) (sx_opt : (Option sx)) (i : laneidx), 
    ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) ->
    Instr_ok C (.VEXTRACT_LANE sh sx_opt i) (.mk_functype (.mk_list [.V128]) (.mk_list [(valtype_numtype (shunpack sh))]))
  | vreplace_lane : forall (C : context) (sh : shape) (i : laneidx), 
    ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) ->
    Instr_ok C (.VREPLACE_LANE sh i) (.mk_functype (.mk_list [.V128, (valtype_numtype (shunpack sh))]) (.mk_list [.V128]))
  | vextunop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop_), 
    (wf_vextunop_ sh_1 vextunop) ->
    Instr_ok C (.VEXTUNOP sh_1 sh_2 vextunop) (.mk_functype (.mk_list [.V128]) (.mk_list [.V128]))
  | vextbinop : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop_), 
    (wf_vextbinop_ sh_1 vextbinop) ->
    Instr_ok C (.VEXTBINOP sh_1 sh_2 vextbinop) (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128]))
  | vnarrow : forall (C : context) (sh_1 : ishape) (sh_2 : ishape) (v_sx : sx), Instr_ok C (.VNARROW sh_1 sh_2 v_sx) (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128]))
  | vcvtop : forall (C : context) (sh_1 : shape) (sh_2 : shape) (v_vcvtop : vcvtop), Instr_ok C (.VCVTOP sh_1 sh_2 v_vcvtop) (.mk_functype (.mk_list [.V128]) (.mk_list [.V128]))
  | local_get : forall (C : context) (x : idx) (t : valtype), 
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == t) ->
    Instr_ok C (.LOCAL_GET x) (.mk_functype (.mk_list []) (.mk_list [t]))
  | local_set : forall (C : context) (x : idx) (t : valtype), 
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == t) ->
    Instr_ok C (.LOCAL_SET x) (.mk_functype (.mk_list [t]) (.mk_list []))
  | local_tee : forall (C : context) (x : idx) (t : valtype), 
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == t) ->
    Instr_ok C (.LOCAL_TEE x) (.mk_functype (.mk_list [t]) (.mk_list [t]))
  | global_get : forall (C : context) (x : idx) (t : valtype) (v_mut : «mut»), 
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype v_mut t)) ->
    Instr_ok C (.GLOBAL_GET x) (.mk_functype (.mk_list []) (.mk_list [t]))
  | global_set : forall (C : context) (x : idx) (t : valtype), 
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype (some .MUT) t)) ->
    Instr_ok C (.GLOBAL_SET x) (.mk_functype (.mk_list [t]) (.mk_list []))
  | table_get : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype lim rt)) ->
    Instr_ok C (.TABLE_GET x) (.mk_functype (.mk_list [.I32]) (.mk_list [(valtype_reftype rt)]))
  | table_set : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype lim rt)) ->
    Instr_ok C (.TABLE_SET x) (.mk_functype (.mk_list [.I32, (valtype_reftype rt)]) (.mk_list []))
  | table_size : forall (C : context) (x : idx) (lim : limits) (rt : reftype), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype lim rt)) ->
    Instr_ok C (.TABLE_SIZE x) (.mk_functype (.mk_list []) (.mk_list [.I32]))
  | table_grow : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype lim rt)) ->
    Instr_ok C (.TABLE_GROW x) (.mk_functype (.mk_list [(valtype_reftype rt), .I32]) (.mk_list [.I32]))
  | table_fill : forall (C : context) (x : idx) (rt : reftype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype lim rt)) ->
    Instr_ok C (.TABLE_FILL x) (.mk_functype (.mk_list [.I32, (valtype_reftype rt), .I32]) (.mk_list []))
  | table_copy : forall (C : context) (x_1 : idx) (x_2 : idx) (lim_1 : limits) (rt : reftype) (lim_2 : limits), 
    ((proj_uN_0 x_1) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x_1)]!) == (.mk_tabletype lim_1 rt)) ->
    ((proj_uN_0 x_2) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x_2)]!) == (.mk_tabletype lim_2 rt)) ->
    Instr_ok C (.TABLE_COPY x_1 x_2) (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list []))
  | table_init : forall (C : context) (x_1 : idx) (x_2 : idx) (lim : limits) (rt : reftype), 
    ((proj_uN_0 x_1) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x_1)]!) == (.mk_tabletype lim rt)) ->
    ((proj_uN_0 x_2) < (List.length (C.ELEMS))) ->
    (((C.ELEMS)[(proj_uN_0 x_2)]!) == rt) ->
    Instr_ok C (.TABLE_INIT x_1 x_2) (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list []))
  | elem_drop : forall (C : context) (x : idx) (rt : reftype), 
    ((proj_uN_0 x) < (List.length (C.ELEMS))) ->
    (((C.ELEMS)[(proj_uN_0 x)]!) == rt) ->
    Instr_ok C (.ELEM_DROP x) (.mk_functype (.mk_list []) (.mk_list []))
  | memory_size : forall (C : context) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    Instr_ok C .MEMORY_SIZE (.mk_functype (.mk_list []) (.mk_list [.I32]))
  | memory_grow : forall (C : context) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    Instr_ok C .MEMORY_GROW (.mk_functype (.mk_list [.I32]) (.mk_list [.I32]))
  | memory_fill : forall (C : context) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    Instr_ok C .MEMORY_FILL (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list []))
  | memory_copy : forall (C : context) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    Instr_ok C .MEMORY_COPY (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list []))
  | memory_init : forall (C : context) (x : idx) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    ((proj_uN_0 x) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 x)]!) == .OK) ->
    Instr_ok C (.MEMORY_INIT x) (.mk_functype (.mk_list [.I32, .I32, .I32]) (.mk_list []))
  | data_drop : forall (C : context) (x : idx), 
    ((proj_uN_0 x) < (List.length (C.DATAS))) ->
    (((C.DATAS)[(proj_uN_0 x)]!) == .OK) ->
    Instr_ok C (.DATA_DROP x) (.mk_functype (.mk_list []) (.mk_list []))
  | load_val : forall (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    ((size (valtype_numtype nt)) != none) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= (((Option.get! (size (valtype_numtype nt))) : Nat) / (8 : Nat))) ->
    Instr_ok C (.LOAD nt none v_memarg) (.mk_functype (.mk_list [.I32]) (.mk_list [(valtype_numtype nt)]))
  | load_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (v_memarg : memarg) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= ((v_M : Nat) / (8 : Nat))) ->
    Instr_ok C (.LOAD (numtype_Inn v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_M) v_sx))) v_memarg) (.mk_functype (.mk_list [.I32]) (.mk_list [(valtype_Inn v_Inn)]))
  | store_val : forall (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    ((size (valtype_numtype nt)) != none) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= (((Option.get! (size (valtype_numtype nt))) : Nat) / (8 : Nat))) ->
    Instr_ok C (.STORE nt none v_memarg) (.mk_functype (.mk_list [.I32, (valtype_numtype nt)]) (.mk_list []))
  | store_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= ((v_M : Nat) / (8 : Nat))) ->
    Instr_ok C (.STORE (numtype_Inn v_Inn) (some (.mk_sz v_M)) v_memarg) (.mk_functype (.mk_list [.I32, (valtype_Inn v_Inn)]) (.mk_list []))
  | vload : forall (C : context) (v_M : M) (v_N : N) (v_sx : sx) (v_memarg : memarg) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= (((v_M : Nat) / (8 : Nat)) * (v_N : Nat))) ->
    Instr_ok C (.VLOAD .V128 (some (.SHAPEX_ v_M v_N v_sx)) v_memarg) (.mk_functype (.mk_list [.I32]) (.mk_list [.V128]))
  | vload_splat : forall (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= ((v_n : Nat) / (8 : Nat))) ->
    Instr_ok C (.VLOAD .V128 (some (.SPLAT v_n)) v_memarg) (.mk_functype (.mk_list [.I32]) (.mk_list [.V128]))
  | vload_zero : forall (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= ((v_n : Nat) / (8 : Nat))) ->
    Instr_ok C (.VLOAD .V128 (some (.ZERO v_n)) v_memarg) (.mk_functype (.mk_list [.I32]) (.mk_list [.V128]))
  | vload_lane : forall (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= ((v_n : Nat) / (8 : Nat))) ->
    (((proj_uN_0 v_laneidx) : Nat) < ((128 : Nat) / (v_n : Nat))) ->
    Instr_ok C (.VLOAD_LANE .V128 (.mk_sz v_n) v_memarg v_laneidx) (.mk_functype (.mk_list [.I32, .V128]) (.mk_list [.V128]))
  | vstore : forall (C : context) (v_memarg : memarg) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    ((size .V128) != none) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= (((Option.get! (size .V128)) : Nat) / (8 : Nat))) ->
    Instr_ok C (.VSTORE .V128 v_memarg) (.mk_functype (.mk_list [.I32, .V128]) (.mk_list []))
  | vstore_lane : forall (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= ((v_n : Nat) / (8 : Nat))) ->
    (((proj_uN_0 v_laneidx) : Nat) < ((128 : Nat) / (v_n : Nat))) ->
    Instr_ok C (.VSTORE_LANE .V128 (.mk_sz v_n) v_memarg v_laneidx) (.mk_functype (.mk_list [.I32, .V128]) (.mk_list []))

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:138.1-138.65 -/
inductive Instrs_ok : context -> (List instr) -> functype -> Prop where
  | empty : forall (C : context), Instrs_ok C [] (.mk_functype (.mk_list []) (.mk_list []))
  | seq : forall (C : context) (instr_1 : instr) (instr_2_lst : (List instr)) (t_1_lst : (List valtype)) (t_3_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Instr_ok C instr_1 (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    (Instrs_ok C instr_2_lst (.mk_functype (.mk_list t_2_lst) (.mk_list t_3_lst))) ->
    Instrs_ok C ([instr_1] ++ instr_2_lst) (.mk_functype (.mk_list t_1_lst) (.mk_list t_3_lst))
  | sub : forall (C : context) (instr_lst : (List instr)) (t'_1_lst : (List valtype)) (t'_2_lst : (List valtype)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Instrs_ok C instr_lst (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    (Resulttype_sub (.mk_list t'_1_lst) (.mk_list t_1_lst)) ->
    (Resulttype_sub (.mk_list t_2_lst) (.mk_list t'_2_lst)) ->
    Instrs_ok C instr_lst (.mk_functype (.mk_list t'_1_lst) (.mk_list t'_2_lst))
  | frame : forall (C : context) (instr_lst : (List instr)) (t_lst : (List valtype)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (Instrs_ok C instr_lst (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Instrs_ok C instr_lst (.mk_functype (.mk_list (t_lst ++ t_1_lst)) (.mk_list (t_lst ++ t_2_lst)))

end

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:139.1-139.69 -/
inductive Expr_ok : context -> expr -> resulttype -> Prop where
  | mk_Expr_ok : forall (C : context) (instr_lst : (List instr)) (t_lst : (List valtype)), 
    (Instrs_ok C instr_lst (.mk_functype (.mk_list []) (.mk_list t_lst))) ->
    Expr_ok C instr_lst (.mk_list t_lst)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:525.1-525.78 -/
inductive Instr_const : context -> instr -> Prop where
  | const : forall (C : context) (nt : numtype) (c : num_), 
    (wf_num_ nt c) ->
    Instr_const C (.CONST nt c)
  | vconst : forall (C : context) (vt : vectype) (vc : vec_), Instr_const C (.VCONST vt vc)
  | ref_null : forall (C : context) (rt : reftype), Instr_const C (.REF_NULL rt)
  | ref_func : forall (C : context) (x : idx), Instr_const C (.REF_FUNC x)
  | global_get : forall (C : context) (x : idx) (t : valtype), 
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype none t)) ->
    Instr_const C (.GLOBAL_GET x)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:526.1-526.77 -/
inductive Expr_const : context -> expr -> Prop where
  | mk_Expr_const : forall (C : context) (instr_lst : (List instr)), 
    Forall (fun (v_instr : instr) => (Instr_const C v_instr)) instr_lst ->
    Expr_const C instr_lst

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:527.1-527.78 -/
inductive Expr_ok_const : context -> expr -> valtype -> Prop where
  | mk_Expr_ok_const : forall (C : context) (v_expr : expr) (t : valtype), 
    (Expr_ok C v_expr (.mk_list [t])) ->
    (Expr_const C v_expr) ->
    Expr_ok_const C v_expr t

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:560.1-560.73 -/
inductive Type_ok : type -> functype -> Prop where
  | mk_Type_ok : forall (ft : functype), 
    (Functype_ok ft) ->
    Type_ok (.TYPE ft) ft

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:561.1-561.73 -/
inductive Func_ok : context -> func -> functype -> Prop where
  | mk_Func_ok : forall (C : context) (x : idx) (t_lst : (List valtype)) (v_expr : expr) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (((C.TYPES)[(proj_uN_0 x)]!) == (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Forall (fun (t : valtype) => (t != .BOT)) t_lst ->
    (Expr_ok (C ++ { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := (t_1_lst ++ t_lst), LABELS := [(.mk_list t_2_lst)], RETURN := (some (.mk_list t_2_lst)) }) v_expr (.mk_list t_2_lst)) ->
    Func_ok C (.FUNC x (List.map (fun (t : valtype) => (.LOCAL t)) t_lst) v_expr) (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:562.1-562.75 -/
inductive Global_ok : context -> global -> globaltype -> Prop where
  | mk_Global_ok : forall (C : context) (gt : globaltype) (v_expr : expr) (v_mut : «mut») (t : valtype), 
    (Globaltype_ok gt) ->
    (gt == (.mk_globaltype v_mut t)) ->
    (Expr_ok_const C v_expr t) ->
    Global_ok C (.GLOBAL gt v_expr) gt

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:563.1-563.74 -/
inductive Table_ok : context -> table -> tabletype -> Prop where
  | mk_Table_ok : forall (C : context) (tt : tabletype), 
    (Tabletype_ok tt) ->
    Table_ok C (.TABLE tt) tt

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:564.1-564.72 -/
inductive Mem_ok : context -> mem -> memtype -> Prop where
  | mk_Mem_ok : forall (C : context) (mt : memtype), 
    (Memtype_ok mt) ->
    Mem_ok C (.MEMORY mt) mt

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:567.1-567.77 -/
inductive Elemmode_ok : context -> elemmode -> reftype -> Prop where
  | active : forall (C : context) (x : idx) (v_expr : expr) (rt : reftype) (lim : limits), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == (.mk_tabletype lim rt)) ->
    (Expr_ok_const C v_expr .I32) ->
    Elemmode_ok C (.ACTIVE x v_expr) rt
  | passive : forall (C : context) (rt : reftype), Elemmode_ok C .PASSIVE rt
  | declare : forall (C : context) (rt : reftype), Elemmode_ok C .DECLARE rt

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:565.1-565.73 -/
inductive Elem_ok : context -> elem -> reftype -> Prop where
  | mk_Elem_ok : forall (C : context) (rt : reftype) (expr_lst : (List expr)) (v_elemmode : elemmode), 
    Forall (fun (v_expr : expr) => (Expr_ok_const C v_expr (valtype_reftype rt))) expr_lst ->
    (Elemmode_ok C v_elemmode rt) ->
    Elem_ok C (.ELEM rt expr_lst v_elemmode) rt

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:568.1-568.77 -/
inductive Datamode_ok : context -> datamode -> Prop where
  | active : forall (C : context) (v_expr : expr) (mt : memtype), 
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (Expr_ok_const C v_expr .I32) ->
    Datamode_ok C (.ACTIVE (.mk_uN 0) v_expr)
  | passive : forall (C : context), Datamode_ok C .PASSIVE

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:566.1-566.73 -/
inductive Data_ok : context -> data -> Prop where
  | mk_Data_ok : forall (C : context) (b_lst : (List byte)) (v_datamode : datamode), 
    (Datamode_ok C v_datamode) ->
    Data_ok C (.DATA b_lst v_datamode)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:569.1-569.74 -/
inductive Start_ok : context -> start -> Prop where
  | mk_Start_ok : forall (C : context) (x : idx), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == (.mk_functype (.mk_list []) (.mk_list []))) ->
    Start_ok C (.START x)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:633.1-633.80 -/
inductive Import_ok : context -> «import» -> externtype -> Prop where
  | mk_Import_ok : forall (C : context) (name_1 : name) (name_2 : name) (xt : externtype), 
    (Externtype_ok xt) ->
    Import_ok C (.IMPORT name_1 name_2 xt) xt

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:635.1-635.83 -/
inductive Externidx_ok : context -> externidx -> externtype -> Prop where
  | func : forall (C : context) (x : idx) (ft : functype), 
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == ft) ->
    Externidx_ok C (.FUNC x) (.FUNC ft)
  | global : forall (C : context) (x : idx) (gt : globaltype), 
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == gt) ->
    Externidx_ok C (.GLOBAL x) (.GLOBAL gt)
  | table : forall (C : context) (x : idx) (tt : tabletype), 
    ((proj_uN_0 x) < (List.length (C.TABLES))) ->
    (((C.TABLES)[(proj_uN_0 x)]!) == tt) ->
    Externidx_ok C (.TABLE x) (.TABLE tt)
  | mem : forall (C : context) (x : idx) (mt : memtype), 
    ((proj_uN_0 x) < (List.length (C.MEMS))) ->
    (((C.MEMS)[(proj_uN_0 x)]!) == mt) ->
    Externidx_ok C (.MEM x) (.MEM mt)

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:634.1-634.80 -/
inductive Export_ok : context -> «export» -> externtype -> Prop where
  | mk_Export_ok : forall (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype), 
    (Externidx_ok C v_externidx xt) ->
    Export_ok C (.EXPORT v_name v_externidx) xt

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:665.1-665.62 -/
inductive Module_ok : module -> Prop where
  | mk_Module_ok : forall (type_lst : (List type)) (import_lst : (List «import»)) (func_lst : (List func)) (global_lst : (List global)) (table_lst : (List table)) (mem_lst : (List mem)) (elem_lst : (List elem)) (data_lst : (List data)) (v_n : n) (start_opt : (Option start)) (export_lst : (List «export»)) (ft'_lst : (List functype)) (ixt_lst : (List externtype)) (C' : context) (gt_lst : (List globaltype)) (tt_lst : (List tabletype)) (mt_lst : (List memtype)) (rt_lst : (List reftype)) (C : context) (ft_lst : (List functype)) (xt_lst : (List externtype)) (ift_lst : (List functype)) (igt_lst : (List globaltype)) (itt_lst : (List tabletype)) (imt_lst : (List memtype)) (var_3 : (List memtype)) (var_2 : (List tabletype)) (var_1 : (List globaltype)) (var_0 : (List functype)), 
    (fun_memsxt ixt_lst var_3) ->
    (fun_tablesxt ixt_lst var_2) ->
    (fun_globalsxt ixt_lst var_1) ->
    (fun_funcsxt ixt_lst var_0) ->
    ((List.length ft'_lst) == (List.length type_lst)) ->
    Forall₂ (fun (ft' : functype) (v_type : type) => (Type_ok v_type ft')) ft'_lst type_lst ->
    ((List.length import_lst) == (List.length ixt_lst)) ->
    Forall₂ (fun (v_import : «import») (ixt : externtype) => (Import_ok { TYPES := ft'_lst, FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], LOCALS := [], LABELS := [], RETURN := none } v_import ixt)) import_lst ixt_lst ->
    ((List.length global_lst) == (List.length gt_lst)) ->
    Forall₂ (fun (v_global : global) (gt : globaltype) => (Global_ok C' v_global gt)) global_lst gt_lst ->
    ((List.length table_lst) == (List.length tt_lst)) ->
    Forall₂ (fun (v_table : table) (tt : tabletype) => (Table_ok C' v_table tt)) table_lst tt_lst ->
    ((List.length mem_lst) == (List.length mt_lst)) ->
    Forall₂ (fun (v_mem : mem) (mt : memtype) => (Mem_ok C' v_mem mt)) mem_lst mt_lst ->
    ((List.length elem_lst) == (List.length rt_lst)) ->
    Forall₂ (fun (v_elem : elem) (rt : reftype) => (Elem_ok C' v_elem rt)) elem_lst rt_lst ->
    Forall (fun (v_data : data) => (Data_ok C' v_data)) data_lst ->
    ((List.length ft_lst) == (List.length func_lst)) ->
    Forall₂ (fun (ft : functype) (v_func : func) => (Func_ok C v_func ft)) ft_lst func_lst ->
    Forall (fun (v_start : start) => (Start_ok C v_start)) (Option.toList start_opt) ->
    ((List.length export_lst) == (List.length xt_lst)) ->
    Forall₂ (fun (v_export : «export») (xt : externtype) => (Export_ok C v_export xt)) export_lst xt_lst ->
    ((List.length mt_lst) <= 1) ->
    (C == { TYPES := ft'_lst, FUNCS := (ift_lst ++ ft_lst), GLOBALS := (igt_lst ++ gt_lst), TABLES := (itt_lst ++ tt_lst), MEMS := (imt_lst ++ mt_lst), ELEMS := rt_lst, DATAS := (List.replicate v_n .OK), LOCALS := [], LABELS := [], RETURN := none }) ->
    (C' == { TYPES := ft'_lst, FUNCS := (ift_lst ++ ft_lst), GLOBALS := igt_lst, TABLES := (itt_lst ++ tt_lst), MEMS := (imt_lst ++ mt_lst), ELEMS := [], DATAS := [], LOCALS := [], LABELS := [], RETURN := none }) ->
    (ift_lst == var_0) ->
    (igt_lst == var_1) ->
    (itt_lst == var_2) ->
    (imt_lst == var_3) ->
    Module_ok (.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:276.1-278.15 -/
inductive Step_pure_before_vtestop_false : (List admininstr) -> Prop where
  | vtestop_true_0 : forall (c : vec_) (v_Jnn : Jnn) (v_N : N) (ci_1_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) ci_1)) ci_1_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) c)) ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_uN_0 (Option.get! (proj_lane__2 ci_1))) != 0)) ci_1_lst ->
    Step_pure_before_vtestop_false [(.VCONST .V128 c), (.VTESTOP (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) (.mk_vtestop__0 v_Jnn v_N .ALL_TRUE))]

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.77 -/
inductive Step_pure : (List admininstr) -> (List admininstr) -> Prop where
  | unreachable : Step_pure [.UNREACHABLE] [.TRAP]
  | nop : Step_pure [.NOP] []
  | drop : forall (v_val : val), Step_pure [(admininstr_val v_val), .DROP] []
  | select_true : forall (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : (Option (List valtype))), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) != 0) ->
    Step_pure [(admininstr_val val_1), (admininstr_val val_2), (.CONST .I32 c), (.SELECT t_lst_opt)] [(admininstr_val val_1)]
  | select_false : forall (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : (Option (List valtype))), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 c))) == 0) ->
    Step_pure [(admininstr_val val_1), (admininstr_val val_2), (.CONST .I32 c), (.SELECT t_lst_opt)] [(admininstr_val val_2)]
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
  | label_vals : forall (v_n : n) (instr_lst : (List instr)) (val_lst : (List val)), Step_pure [(.LABEL_ v_n instr_lst (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
  | br_zero : forall (v_n : n) (instr'_lst : (List instr)) (val'_lst : (List val)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([(.BR (.mk_uN 0))] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))))] ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (List.map (fun (instr' : instr) => (admininstr_instr instr')) instr'_lst))
  | br_succ : forall (v_n : n) (instr'_lst : (List instr)) (val_lst : (List val)) (l : labelidx) (instr_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([(.BR (.mk_uN ((proj_uN_0 l) + 1)))] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))))] ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [(.BR l)])
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
  | frame_vals : forall (v_n : n) (f : frame) (val_lst : (List val)), Step_pure [(.FRAME_ v_n f (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
  | return_frame : forall (v_n : n) (f : frame) (val'_lst : (List val)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.FRAME_ v_n f ((List.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([.RETURN] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))))] (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
  | return_label : forall (v_n : n) (instr'_lst : (List instr)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([.RETURN] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))))] ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [.RETURN])
  | trap_vals : forall (val_lst : (List val)) (instr_lst : (List instr)), 
    ((val_lst != []) || (instr_lst != [])) ->
    Step_pure ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([.TRAP] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))) [.TRAP]
  | trap_label : forall (v_n : n) (instr'_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst [.TRAP])] [.TRAP]
  | trap_frame : forall (v_n : n) (f : frame), Step_pure [(.FRAME_ v_n f [.TRAP])] [.TRAP]
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
  | testop : forall (nt : numtype) (c_1 : num_) (testop : testop_) (c : num_) (var_0 : num_), 
    (fun_testop_ nt testop c_1 var_0) ->
    (wf_num_ nt c_1) ->
    (wf_testop_ nt testop) ->
    (wf_num_ .I32 c) ->
    (c == var_0) ->
    Step_pure [(.CONST nt c_1), (.TESTOP nt testop)] [(.CONST .I32 c)]
  | relop : forall (nt : numtype) (c_1 : num_) (c_2 : num_) (relop : relop_) (c : num_) (var_0 : num_), 
    (fun_relop_ nt relop c_1 c_2 var_0) ->
    (wf_num_ nt c_1) ->
    (wf_num_ nt c_2) ->
    (wf_relop_ nt relop) ->
    (wf_num_ .I32 c) ->
    (c == var_0) ->
    Step_pure [(.CONST nt c_1), (.CONST nt c_2), (.RELOP nt relop)] [(.CONST .I32 c)]
  | cvtop_val : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (v_cvtop : cvtop) (c : num_) (var_0 : (List num_)), 
    (fun_cvtop__ nt_1 nt_2 v_cvtop c_1 var_0) ->
    (wf_num_ nt_1 c_1) ->
    (wf_num_ nt_2 c) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.CONST nt_1 c_1), (.CVTOP nt_2 nt_1 v_cvtop)] [(.CONST nt_2 c)]
  | cvtop_trap : forall (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (v_cvtop : cvtop) (var_0 : (List num_)), 
    (fun_cvtop__ nt_1 nt_2 v_cvtop c_1 var_0) ->
    (wf_num_ nt_1 c_1) ->
    (var_0 == []) ->
    Step_pure [(.CONST nt_1 c_1), (.CVTOP nt_2 nt_1 v_cvtop)] [.TRAP]
  | ref_is_null_true : forall (v_ref : ref) (rt : reftype), 
    (v_ref == (.REF_NULL rt)) ->
    Step_pure [(admininstr_ref v_ref), .REF_IS_NULL] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))]
  | ref_is_null_false : forall (v_ref : ref) (rt : reftype), 
    (v_ref != (.REF_NULL rt)) ->
    Step_pure [(admininstr_ref v_ref), .REF_IS_NULL] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)))]
  | vvunop : forall (c_1 : vec_) (v_vvunop : vvunop) (c : vec_), 
    (c == (vvunop_ .V128 v_vvunop c_1)) ->
    Step_pure [(.VCONST .V128 c_1), (.VVUNOP .V128 v_vvunop)] [(.VCONST .V128 c)]
  | vvbinop : forall (c_1 : vec_) (c_2 : vec_) (v_vvbinop : vvbinop) (c : vec_), 
    (c == (vvbinop_ .V128 v_vvbinop c_1 c_2)) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VVBINOP .V128 v_vvbinop)] [(.VCONST .V128 c)]
  | vvternop : forall (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (v_vvternop : vvternop) (c : vec_), 
    (c == (vvternop_ .V128 v_vvternop c_1 c_2 c_3)) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VCONST .V128 c_3), (.VVTERNOP .V128 v_vvternop)] [(.VCONST .V128 c)]
  | vvtestop : forall (c_1 : vec_) (c : num_), 
    (wf_num_ .I32 c) ->
    ((proj_num__0 c) != none) ->
    ((size .V128) != none) ->
    ((Option.get! (proj_num__0 c)) == (ine_ (Option.get! (size .V128)) c_1 (.mk_uN 0))) ->
    Step_pure [(.VCONST .V128 c_1), (.VVTESTOP .V128 .ANY_TRUE)] [(.CONST .I32 c)]
  | vunop : forall (c_1 : vec_) (sh : shape) (vunop : vunop_) (c : vec_) (var_0 : (List vec_)), 
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
  | vtestop_true : forall (c : vec_) (v_Jnn : Jnn) (v_N : N) (ci_1_lst : (List lane_)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) ci_1)) ci_1_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) c)) ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != none)) ci_1_lst ->
    Forall (fun (ci_1 : lane_) => ((proj_uN_0 (Option.get! (proj_lane__2 ci_1))) != 0)) ci_1_lst ->
    Step_pure [(.VCONST .V128 c), (.VTESTOP (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) (.mk_vtestop__0 v_Jnn v_N .ALL_TRUE))] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)))]
  | vtestop_false : forall (c : vec_) (v_Jnn : Jnn) (v_N : N), 
    (¬(Step_pure_before_vtestop_false [(.VCONST .V128 c), (.VTESTOP (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) (.mk_vtestop__0 v_Jnn v_N .ALL_TRUE))])) ->
    Step_pure [(.VCONST .V128 c), (.VTESTOP (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) (.mk_vtestop__0 v_Jnn v_N .ALL_TRUE))] [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0)))]
  | vrelop : forall (c_1 : vec_) (c_2 : vec_) (sh : shape) (vrelop : vrelop_) (c : vec_) (var_0 : vec_), 
    (fun_vrelop_ sh vrelop c_1 c_2 var_0) ->
    (wf_vrelop_ sh vrelop) ->
    (var_0 == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VRELOP sh vrelop)] [(.VCONST .V128 c)]
  | vshiftop : forall (c_1 : vec_) (v_n : n) (v_Jnn : Jnn) (v_N : N) (vshiftop : vshiftop_) (c : vec_) (c'_lst : (List lane_)) (var_0_lst : (List lane_)), 
    ((List.length var_0_lst) == (List.length c'_lst)) ->
    Forall₂ (fun (var_0 : lane_) (c' : lane_) => (fun_vshiftop_ (.X v_Jnn (.mk_dim v_N)) vshiftop c' (.mk_uN v_n) var_0)) var_0_lst c'_lst ->
    (wf_vshiftop_ (.X v_Jnn (.mk_dim v_N)) vshiftop) ->
    Forall (fun (c' : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) c')) c'_lst ->
    (c'_lst == (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) c_1)) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) var_0_lst)) ->
    Step_pure [(.VCONST .V128 c_1), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.VSHIFTOP (.X v_Jnn (.mk_dim v_N)) vshiftop)] [(.VCONST .V128 c)]
  | vbitmask : forall (c : vec_) (v_Jnn : Jnn) (v_N : N) (ci : iN) (ci_1_lst : (List lane_)) (var_0_lst : (List uN)), 
    ((List.length var_0_lst) == (List.length ci_1_lst)) ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != none)) ci_1_lst ->
    Forall₂ (fun (var_0 : uN) (ci_1 : lane_) => (fun_ilt_ (lsize (lanetype_Jnn v_Jnn)) .S (Option.get! (proj_lane__2 ci_1)) (.mk_uN 0) var_0)) var_0_lst ci_1_lst ->
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) ci_1)) ci_1_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) c)) ->
    ((ibits_ 32 ci) == ((List.map (fun (var_0 : uN) => (.mk_bit (proj_uN_0 var_0))) var_0_lst) ++ (List.replicate (((32 : Nat) - (v_N : Nat)) : Nat) (.mk_bit 0)))) ->
    Step_pure [(.VCONST .V128 c), (.VBITMASK (.X v_Jnn (.mk_dim v_N)))] [(.CONST .I32 (.mk_num__0 .I32 (irev_ 32 ci)))]
  | vswizzle : forall (c_1 : vec_) (c_2 : vec_) (v_Pnn : Pnn) (v_M : M) (c : vec_) (c'_lst : (List iN)) (ci_lst : (List lane_)) (k_lst : (List Nat)), 
    Forall (fun (k : Nat) => ((proj_uN_0 (Option.get! (proj_lane__1 (ci_lst[k]!)))) < (List.length c'_lst))) k_lst ->
    Forall (fun (k : Nat) => ((proj_lane__1 (ci_lst[k]!)) != none)) k_lst ->
    Forall (fun (k : Nat) => (k < (List.length ci_lst))) k_lst ->
    Forall (fun (k : Nat) => (wf_lane_ (fun_lanetype (.X (lanetype_packtype v_Pnn) (.mk_dim v_M))) (.mk_lane__1 v_Pnn (c'_lst[(proj_uN_0 (Option.get! (proj_lane__1 (ci_lst[k]!))))]!)))) k_lst ->
    (ci_lst == (lanes_ (.X (lanetype_packtype v_Pnn) (.mk_dim v_M)) c_2)) ->
    Forall (fun (iter_0 : lane_) => ((proj_lane__1 iter_0) != none)) (lanes_ (.X (lanetype_packtype v_Pnn) (.mk_dim v_M)) c_1) ->
    (c'_lst == ((List.map (fun (iter_0 : lane_) => (Option.get! (proj_lane__1 iter_0))) (lanes_ (.X (lanetype_packtype v_Pnn) (.mk_dim v_M)) c_1)) ++ (List.replicate (((256 : Nat) - (v_M : Nat)) : Nat) (.mk_uN 0)))) ->
    (c == (inv_lanes_ (.X (lanetype_packtype v_Pnn) (.mk_dim v_M)) (List.map (fun (k : Nat) => (.mk_lane__1 v_Pnn (c'_lst[(proj_uN_0 (Option.get! (proj_lane__1 (ci_lst[k]!))))]!))) k_lst))) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VSWIZZLE (.X (Jnn_packtype v_Pnn) (.mk_dim v_M)))] [(.VCONST .V128 c)]
  | vshuffle : forall (c_1 : vec_) (c_2 : vec_) (v_Pnn : Pnn) (v_N : N) (i_lst : (List laneidx)) (c : vec_) (c'_lst : (List iN)) (k_lst : (List Nat)), 
    Forall (fun (c' : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_packtype v_Pnn) (.mk_dim v_N))) (.mk_lane__1 v_Pnn c'))) c'_lst ->
    Forall (fun (k : Nat) => ((proj_uN_0 (i_lst[k]!)) < (List.length c'_lst))) k_lst ->
    Forall (fun (k : Nat) => (k < (List.length i_lst))) k_lst ->
    Forall (fun (k : Nat) => (wf_lane_ (fun_lanetype (.X (lanetype_packtype v_Pnn) (.mk_dim v_N))) (.mk_lane__1 v_Pnn (c'_lst[(proj_uN_0 (i_lst[k]!))]!)))) k_lst ->
    ((List.map (fun (c' : iN) => (.mk_lane__1 v_Pnn c')) c'_lst) == ((lanes_ (.X (lanetype_packtype v_Pnn) (.mk_dim v_N)) c_1) ++ (lanes_ (.X (lanetype_packtype v_Pnn) (.mk_dim v_N)) c_2))) ->
    (c == (inv_lanes_ (.X (lanetype_packtype v_Pnn) (.mk_dim v_N)) (List.map (fun (k : Nat) => (.mk_lane__1 v_Pnn (c'_lst[(proj_uN_0 (i_lst[k]!))]!))) k_lst))) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VSHUFFLE (.X (Jnn_packtype v_Pnn) (.mk_dim v_N)) i_lst)] [(.VCONST .V128 c)]
  | vsplat : forall (v_Lnn : Lnn) (c_1 : num_) (v_N : N) (c : vec_) (var_0 : lane_), 
    (fun_packnum_ v_Lnn c_1 var_0) ->
    (wf_num_ (unpack v_Lnn) c_1) ->
    (c == (inv_lanes_ (.X v_Lnn (.mk_dim v_N)) (List.replicate v_N var_0))) ->
    Step_pure [(.CONST (unpack v_Lnn) c_1), (.VSPLAT (.X v_Lnn (.mk_dim v_N)))] [(.VCONST .V128 c)]
  | vextract_lane_num : forall (c_1 : vec_) (nt : numtype) (v_N : N) (i : laneidx) (c_2 : num_), 
    (wf_lane_ (fun_lanetype (.X (lanetype_numtype nt) (.mk_dim v_N))) (.mk_lane__0 nt c_2)) ->
    ((proj_uN_0 i) < (List.length (lanes_ (.X (lanetype_numtype nt) (.mk_dim v_N)) c_1))) ->
    ((.mk_lane__0 nt c_2) == ((lanes_ (.X (lanetype_numtype nt) (.mk_dim v_N)) c_1)[(proj_uN_0 i)]!)) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTRACT_LANE (.X (lanetype_numtype nt) (.mk_dim v_N)) none i)] [(.CONST nt c_2)]
  | vextract_lane_pack : forall (c_1 : vec_) (pt : packtype) (v_N : N) (v_sx : sx) (i : laneidx) (c_2 : num_), 
    (wf_num_ .I32 c_2) ->
    ((proj_num__0 c_2) != none) ->
    ((proj_lane__1 ((lanes_ (.X (lanetype_packtype pt) (.mk_dim v_N)) c_1)[(proj_uN_0 i)]!)) != none) ->
    ((proj_uN_0 i) < (List.length (lanes_ (.X (lanetype_packtype pt) (.mk_dim v_N)) c_1))) ->
    ((Option.get! (proj_num__0 c_2)) == (extend__ (psize pt) 32 v_sx (Option.get! (proj_lane__1 ((lanes_ (.X (lanetype_packtype pt) (.mk_dim v_N)) c_1)[(proj_uN_0 i)]!))))) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTRACT_LANE (.X (lanetype_packtype pt) (.mk_dim v_N)) (some v_sx) i)] [(.CONST .I32 c_2)]
  | vreplace_lane : forall (c_1 : vec_) (v_Lnn : Lnn) (c_2 : num_) (v_N : N) (i : laneidx) (c : vec_) (var_0 : lane_), 
    (fun_packnum_ v_Lnn c_2 var_0) ->
    (wf_num_ (unpack v_Lnn) c_2) ->
    (c == (inv_lanes_ (.X v_Lnn (.mk_dim v_N)) (List.modify (lanes_ (.X v_Lnn (.mk_dim v_N)) c_1) (proj_uN_0 i) (fun (_ : lane_) => var_0)))) ->
    Step_pure [(.VCONST .V128 c_1), (.CONST (unpack v_Lnn) c_2), (.VREPLACE_LANE (.X v_Lnn (.mk_dim v_N)) i)] [(.VCONST .V128 c)]
  | vextunop : forall (c_1 : vec_) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop_) (c : vec_) (var_0 : vec_), 
    (fun_vextunop__ sh_1 sh_2 vextunop c_1 var_0) ->
    (wf_vextunop_ sh_1 vextunop) ->
    (var_0 == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VEXTUNOP sh_1 sh_2 vextunop)] [(.VCONST .V128 c)]
  | vextbinop : forall (c_1 : vec_) (c_2 : vec_) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop_) (c : vec_) (var_0 : vec_), 
    (fun_vextbinop__ sh_1 sh_2 vextbinop c_1 c_2 var_0) ->
    (wf_vextbinop_ sh_1 vextbinop) ->
    (var_0 == c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VEXTBINOP sh_1 sh_2 vextbinop)] [(.VCONST .V128 c)]
  | vnarrow : forall (c_1 : vec_) (c_2 : vec_) (Jnn_2 : Jnn) (N_2 : N) (Jnn_1 : Jnn) (N_1 : N) (v_sx : sx) (c : vec_) (ci_1_lst : (List lane_)) (ci_2_lst : (List lane_)) (cj_1_lst : (List iN)) (cj_2_lst : (List iN)), 
    Forall (fun (ci_1 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn Jnn_1) (.mk_dim N_1))) ci_1)) ci_1_lst ->
    Forall (fun (ci_2 : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn Jnn_1) (.mk_dim N_1))) ci_2)) ci_2_lst ->
    Forall (fun (cj_1 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn Jnn_2) (.mk_dim N_2))) (.mk_lane__2 Jnn_2 cj_1))) cj_1_lst ->
    Forall (fun (cj_2 : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn Jnn_2) (.mk_dim N_2))) (.mk_lane__2 Jnn_2 cj_2))) cj_2_lst ->
    (ci_1_lst == (lanes_ (.X (lanetype_Jnn Jnn_1) (.mk_dim N_1)) c_1)) ->
    (ci_2_lst == (lanes_ (.X (lanetype_Jnn Jnn_1) (.mk_dim N_1)) c_2)) ->
    Forall (fun (ci_1 : lane_) => ((proj_lane__2 ci_1) != none)) ci_1_lst ->
    (cj_1_lst == (List.map (fun (ci_1 : lane_) => (narrow__ (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (Option.get! (proj_lane__2 ci_1)))) ci_1_lst)) ->
    Forall (fun (ci_2 : lane_) => ((proj_lane__2 ci_2) != none)) ci_2_lst ->
    (cj_2_lst == (List.map (fun (ci_2 : lane_) => (narrow__ (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (Option.get! (proj_lane__2 ci_2)))) ci_2_lst)) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn Jnn_2) (.mk_dim N_2)) ((List.map (fun (cj_1 : iN) => (.mk_lane__2 Jnn_2 cj_1)) cj_1_lst) ++ (List.map (fun (cj_2 : iN) => (.mk_lane__2 Jnn_2 cj_2)) cj_2_lst)))) ->
    Step_pure [(.VCONST .V128 c_1), (.VCONST .V128 c_2), (.VNARROW (.X Jnn_2 (.mk_dim N_2)) (.X Jnn_1 (.mk_dim N_1)) v_sx)] [(.VCONST .V128 c)]
  | vcvtop_full : forall (c_1 : vec_) (Lnn_2 : Lnn) (v_M : M) (Lnn_1 : Lnn) (v_vcvtop : vcvtop) (c : vec_) (ci_lst : (List lane_)) (cj_lst_lst : (List (List lane_))) (var_0_lst : (List (List lane_))), 
    ((List.length var_0_lst) == (List.length ci_lst)) ->
    Forall₂ (fun (var_0 : (List lane_)) (ci : lane_) => (fun_vcvtop__ (.X Lnn_1 (.mk_dim v_M)) (.X Lnn_2 (.mk_dim v_M)) v_vcvtop ci var_0)) var_0_lst ci_lst ->
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X Lnn_1 (.mk_dim v_M))) ci)) ci_lst ->
    Forall (fun (cj_lst : (List lane_)) => Forall (fun (cj : lane_) => (wf_lane_ Lnn_2 cj)) cj_lst) cj_lst_lst ->
    (((halfop v_vcvtop) == none) && ((zeroop v_vcvtop) == none)) ->
    (ci_lst == (lanes_ (.X Lnn_1 (.mk_dim v_M)) c_1)) ->
    (cj_lst_lst == (setproduct_ lane_ var_0_lst)) ->
    ((List.length (List.map (fun (cj_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim v_M)) cj_lst)) cj_lst_lst)) > 0) ->
    (List.contains (List.map (fun (cj_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim v_M)) cj_lst)) cj_lst_lst) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCVTOP (.X Lnn_2 (.mk_dim v_M)) (.X Lnn_1 (.mk_dim v_M)) v_vcvtop)] [(.VCONST .V128 c)]
  | vcvtop_half : forall (c_1 : vec_) (Lnn_2 : Lnn) (M_2 : M) (Lnn_1 : Lnn) (M_1 : M) (v_vcvtop : vcvtop) (c : vec_) (v_half : half) (ci_lst : (List lane_)) (cj_lst_lst : (List (List lane_))) (var_0_lst : (List (List lane_))), 
    ((List.length var_0_lst) == (List.length ci_lst)) ->
    Forall₂ (fun (var_0 : (List lane_)) (ci : lane_) => (fun_vcvtop__ (.X Lnn_1 (.mk_dim M_1)) (.X Lnn_2 (.mk_dim M_2)) v_vcvtop ci var_0)) var_0_lst ci_lst ->
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X Lnn_1 (.mk_dim M_1))) ci)) ci_lst ->
    Forall (fun (cj_lst : (List lane_)) => Forall (fun (cj : lane_) => (wf_lane_ Lnn_2 cj)) cj_lst) cj_lst_lst ->
    ((halfop v_vcvtop) == (some v_half)) ->
    (ci_lst == (List.extract (lanes_ (.X Lnn_1 (.mk_dim M_1)) c_1) (fun_half v_half 0 M_2) M_2)) ->
    (cj_lst_lst == (setproduct_ lane_ var_0_lst)) ->
    ((List.length (List.map (fun (cj_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim M_2)) cj_lst)) cj_lst_lst)) > 0) ->
    (List.contains (List.map (fun (cj_lst : (List lane_)) => (inv_lanes_ (.X Lnn_2 (.mk_dim M_2)) cj_lst)) cj_lst_lst) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCVTOP (.X Lnn_2 (.mk_dim M_2)) (.X Lnn_1 (.mk_dim M_1)) v_vcvtop)] [(.VCONST .V128 c)]
  | vcvtop_zero : forall (c_1 : vec_) (nt_2 : numtype) (M_2 : M) (nt_1 : numtype) (M_1 : M) (v_vcvtop : vcvtop) (c : vec_) (ci_lst : (List lane_)) (cj_lst_lst : (List (List lane_))) (var_1_lst : (List (List lane_))) (var_0 : num_), 
    ((List.length var_1_lst) == (List.length ci_lst)) ->
    Forall₂ (fun (var_1 : (List lane_)) (ci : lane_) => (fun_vcvtop__ (.X (lanetype_numtype nt_1) (.mk_dim M_1)) (.X (lanetype_numtype nt_2) (.mk_dim M_2)) v_vcvtop ci var_1)) var_1_lst ci_lst ->
    (fun_zero nt_2 var_0) ->
    Forall (fun (ci : lane_) => (wf_lane_ (fun_lanetype (.X (lanetype_numtype nt_1) (.mk_dim M_1))) ci)) ci_lst ->
    Forall (fun (cj_lst : (List lane_)) => Forall (fun (cj : lane_) => (wf_lane_ (lanetype_numtype nt_2) cj)) cj_lst) cj_lst_lst ->
    (wf_lane_ (lanetype_numtype nt_2) (.mk_lane__0 nt_2 var_0)) ->
    ((zeroop v_vcvtop) == (some .ZERO)) ->
    (ci_lst == (lanes_ (.X (lanetype_numtype nt_1) (.mk_dim M_1)) c_1)) ->
    (cj_lst_lst == (setproduct_ lane_ (var_1_lst ++ (List.replicate M_1 [(.mk_lane__0 nt_2 var_0)])))) ->
    ((List.length (List.map (fun (cj_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_numtype nt_2) (.mk_dim M_2)) cj_lst)) cj_lst_lst)) > 0) ->
    (List.contains (List.map (fun (cj_lst : (List lane_)) => (inv_lanes_ (.X (lanetype_numtype nt_2) (.mk_dim M_2)) cj_lst)) cj_lst_lst) c) ->
    Step_pure [(.VCONST .V128 c_1), (.VCVTOP (.X (lanetype_numtype nt_2) (.mk_dim M_2)) (.X (lanetype_numtype nt_1) (.mk_dim M_1)) v_vcvtop)] [(.VCONST .V128 c)]
  | local_tee : forall (v_val : val) (x : idx), Step_pure [(admininstr_val v_val), (.LOCAL_TEE x)] [(admininstr_val v_val), (admininstr_val v_val), (.LOCAL_SET x)]

/- Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 -/
def fun_blocktype : ∀  (v_state : state) (v_blocktype : blocktype) , functype
  | z, (._RESULT none) =>
    (.mk_functype (.mk_list []) (.mk_list []))
  | z, (._RESULT (some t)) =>
    (.mk_functype (.mk_list []) (.mk_list [t]))
  | z, (._IDX x) =>
    (fun_type z x)


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:436.1-439.14 -/
inductive Step_read_before_table_fill_zero : config -> Prop where
  | table_fill_trap_0 : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS))) ->
    Step_read_before_table_fill_zero (.mk_config z [(.CONST .I32 i), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_FILL x)])

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:452.1-455.14 -/
inductive Step_read_before_table_copy_zero : config -> Prop where
  | table_copy_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z y).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS)))) ->
    Step_read_before_table_copy_zero (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_COPY x y)])

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:457.1-462.15 -/
inductive Step_read_before_table_copy_le : config -> Prop where
  | table_copy_zero_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    (¬(Step_read_before_table_copy_zero (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_COPY x y)]))) ->
    (v_n == 0) ->
    Step_read_before_table_copy_le (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_COPY x y)])
  | table_copy_trap_1 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z y).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS)))) ->
    Step_read_before_table_copy_le (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_COPY x y)])

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:475.1-478.14 -/
inductive Step_read_before_table_init_zero : config -> Prop where
  | table_init_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_elem z y).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS)))) ->
    Step_read_before_table_init_zero (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)])

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:616.1-619.14 -/
inductive Step_read_before_memory_fill_zero : config -> Prop where
  | memory_fill_trap_0 : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read_before_memory_fill_zero (.mk_config z [(.CONST .I32 i), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_FILL])

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:632.1-635.14 -/
inductive Step_read_before_memory_copy_zero : config -> Prop where
  | memory_copy_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    Step_read_before_memory_copy_zero (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_COPY])

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:637.1-642.15 -/
inductive Step_read_before_memory_copy_le : config -> Prop where
  | memory_copy_zero_0 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    (¬(Step_read_before_memory_copy_zero (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_COPY]))) ->
    (v_n == 0) ->
    Step_read_before_memory_copy_le (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_COPY])
  | memory_copy_trap_1 : forall (z : state) (j : num_) (i : num_) (v_n : n), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    Step_read_before_memory_copy_le (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_COPY])

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:655.1-658.14 -/
inductive Step_read_before_memory_init_zero : config -> Prop where
  | memory_init_trap_0 : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_data z x).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    Step_read_before_memory_init_zero (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x)])

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.77 -/
inductive Step_read : config -> (List admininstr) -> Prop where
  | block : forall (z : state) (val_lst : (List val)) (k : Nat) (bt : blocktype) (instr_lst : (List instr)) (v_n : n) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    ((fun_blocktype z bt) == (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [(.BLOCK bt instr_lst)])) [(.LABEL_ v_n [] ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))]
  | loop : forall (z : state) (val_lst : (List val)) (k : Nat) (bt : blocktype) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (v_n : n), 
    ((fun_blocktype z bt) == (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [(.LOOP bt instr_lst)])) [(.LABEL_ k [(.LOOP bt instr_lst)] ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))]
  | call : forall (z : state) (x : idx), 
    ((proj_uN_0 x) < (List.length (fun_funcaddr z))) ->
    Step_read (.mk_config z [(.CALL x)]) [(.CALL_ADDR ((fun_funcaddr z)[(proj_uN_0 x)]!))]
  | call_indirect_call : forall (z : state) (i : num_) (x : idx) (y : idx) (a : addr), 
    (wf_num_ .I32 i) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS))) ->
    ((proj_num__0 i) != none) ->
    ((((fun_table z x).REFS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!) == (.REF_FUNC_ADDR a)) ->
    (a < (List.length (fun_funcinst z))) ->
    ((fun_type z y) == (((fun_funcinst z)[a]!).TYPE)) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.CALL_INDIRECT x y)]) [(.CALL_ADDR a)]
  | call_indirect_trap : forall (z : state) (i : num_) (x : idx) (y : idx) (a : addr), 
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS))) ->
    ((proj_num__0 i) != none) ->
    (a < (List.length (fun_funcinst z))) ->
    (((((fun_table z x).REFS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!) != (.REF_FUNC_ADDR a)) || ((fun_type z y) != (((fun_funcinst z)[a]!).TYPE))) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.CALL_INDIRECT x y)]) [.TRAP]
  | call_addr : forall (z : state) (val_lst : (List val)) (k : Nat) (a : addr) (v_n : n) (f : frame) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (mm : moduleinst) (v_func : func) (x : idx) (t_lst : (List valtype)), 
    (a < (List.length (fun_funcinst z))) ->
    (((fun_funcinst z)[a]!) == { TYPE := (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)), MODULE := mm, CODE := v_func }) ->
    (v_func == (.FUNC x (List.map (fun (t : valtype) => (.LOCAL t)) t_lst) instr_lst)) ->
    (f == { LOCALS := (val_lst ++ (List.map (fun (t : valtype) => (default_ t)) t_lst)), MODULE := mm }) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [(.CALL_ADDR a)])) [(.FRAME_ v_n f [(.LABEL_ v_n [] (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))])]
  | ref_func : forall (z : state) (x : idx), 
    ((proj_uN_0 x) < (List.length (fun_funcaddr z))) ->
    Step_read (.mk_config z [(.REF_FUNC x)]) [(.REF_FUNC_ADDR ((fun_funcaddr z)[(proj_uN_0 x)]!))]
  | local_get : forall (z : state) (x : idx), Step_read (.mk_config z [(.LOCAL_GET x)]) [(admininstr_val (fun_local z x))]
  | global_get : forall (z : state) (x : idx), Step_read (.mk_config z [(.GLOBAL_GET x)]) [(admininstr_val ((fun_global z x).VALUE))]
  | table_get_trap : forall (z : state) (i : num_) (x : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length ((fun_table z x).REFS))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.TABLE_GET x)]) [.TRAP]
  | table_get_val : forall (z : state) (i : num_) (x : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS))) ->
    ((proj_num__0 i) != none) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.TABLE_GET x)]) [(admininstr_ref (((fun_table z x).REFS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!))]
  | table_size : forall (z : state) (x : idx) (v_n : n), 
    ((List.length ((fun_table z x).REFS)) == v_n) ->
    Step_read (.mk_config z [(.TABLE_SIZE x)]) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n)))]
  | table_fill_trap : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_FILL x)]) [.TRAP]
  | table_fill_zero : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) ->
    (wf_num_ .I32 i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST .I32 i), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_FILL x)]) []
  | table_fill_succ : forall (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z x).REFS))) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 i), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_FILL x)]) [(.CONST .I32 i), (admininstr_val v_val), (.TABLE_SET x), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.TABLE_FILL x)]
  | table_copy_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z y).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS)))) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_COPY x y)]) [.TRAP]
  | table_copy_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z y).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_table z x).REFS)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_COPY x y)]) []
  | table_copy_le : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_num__0 j) != none) ->
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z y).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_table z x).REFS)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_uN_0 (Option.get! (proj_num__0 j))) <= (proj_uN_0 (Option.get! (proj_num__0 i)))) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_COPY x y)]) [(.CONST .I32 j), (.CONST .I32 i), (.TABLE_GET y), (.TABLE_SET x), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.TABLE_COPY x y)]
  | table_copy_gt : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_num__0 j) != none) ->
    ((proj_num__0 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 j))) > (proj_uN_0 (Option.get! (proj_num__0 i)))) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_table z y).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_table z x).REFS)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_COPY x y)]) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.TABLE_GET y), (.TABLE_SET x), (.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.TABLE_COPY x y)]
  | table_init_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_elem z y).REFS))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS)))) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) [.TRAP]
  | table_init_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_elem z y).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_table z x).REFS)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) []
  | table_init_succ : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_elem z y).REFS))) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_elem z y).REFS))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_table z x).REFS)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x y)]) [(.CONST .I32 j), (admininstr_ref (((fun_elem z y).REFS)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!)), (.TABLE_SET x), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.TABLE_INIT x y)]
  | load_num_trap : forall (z : state) (i : num_) (nt : numtype) (ao : memarg), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((size (valtype_numtype nt)) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((Option.get! (size (valtype_numtype nt))) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.LOAD nt none ao)]) [.TRAP]
  | load_num_val : forall (z : state) (i : num_) (nt : numtype) (ao : memarg) (c : num_), 
    (wf_num_ .I32 i) ->
    (wf_num_ nt c) ->
    ((proj_num__0 i) != none) ->
    ((size (valtype_numtype nt)) != none) ->
    ((nbytes_ nt c) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((Option.get! (size (valtype_numtype nt))) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.LOAD nt none ao)]) [(.CONST nt c)]
  | load_pack_trap : forall (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_n : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.LOAD (numtype_Inn v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_n) v_sx))) ao)]) [.TRAP]
  | load_pack_val : forall (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) (c : iN), 
    ((size (valtype_Inn v_Inn)) != none) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((ibytes_ v_n c) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_n : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.LOAD (numtype_Inn v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_n) v_sx))) ao)]) [(.CONST (numtype_Inn v_Inn) (.mk_num__0 v_Inn (extend__ v_n (Option.get! (size (valtype_Inn v_Inn))) v_sx c)))]
  | vload_oob : forall (z : state) (i : num_) (ao : memarg), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((size .V128) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((Option.get! (size .V128)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VLOAD .V128 none ao)]) [.TRAP]
  | vload_val : forall (z : state) (i : num_) (ao : memarg) (c : vec_), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((size .V128) != none) ->
    ((vbytes_ .V128 c) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((Option.get! (size .V128)) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VLOAD .V128 none ao)]) [(.VCONST .V128 c)]
  | vload_shape_oob : forall (z : state) (i : num_) (v_M : M) (v_N : N) (v_sx : sx) (ao : memarg), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((v_M * v_N) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VLOAD .V128 (some (.SHAPEX_ v_M v_N v_sx)) ao)]) [.TRAP]
  | vload_shape_val : forall (z : state) (i : num_) (v_M : M) (v_N : N) (v_sx : sx) (ao : memarg) (c : vec_) (j_lst : (List iN)) (k_lst : (List Nat)) (v_Jnn : Jnn), 
    (wf_num_ .I32 i) ->
    Forall (fun (j : iN) => (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N))) (.mk_lane__2 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j)))) j_lst ->
    Forall (fun (j : iN) => ((proj_num__0 i) != none)) j_lst ->
    Forall₂ (fun (j : iN) (k : Nat) => ((ibytes_ v_M j) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((k * v_M) : Nat) / (8 : Nat)) : Nat)) (((v_M : Nat) / (8 : Nat)) : Nat)))) j_lst k_lst ->
    ((jsize v_Jnn) == (v_M * 2)) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_N)) (List.map (fun (j : iN) => (.mk_lane__2 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j))) j_lst))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VLOAD .V128 (some (.SHAPEX_ v_M v_N v_sx)) ao)]) [(.VCONST .V128 c)]
  | vload_splat_oob : forall (z : state) (i : num_) (v_N : N) (ao : memarg), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_N : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VLOAD .V128 (some (.SPLAT v_N)) ao)]) [.TRAP]
  | vload_splat_val : forall (z : state) (i : num_) (v_N : N) (ao : memarg) (c : vec_) (j : iN) (v_Jnn : Jnn) (v_M : M), 
    (wf_num_ .I32 i) ->
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_lane__2 v_Jnn (.mk_uN (proj_uN_0 j)))) ->
    ((proj_num__0 i) != none) ->
    ((ibytes_ v_N j) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_N : Nat) / (8 : Nat)) : Nat))) ->
    (v_N == (jsize v_Jnn)) ->
    ((v_M : Nat) == ((128 : Nat) / (v_N : Nat))) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (List.replicate v_M (.mk_lane__2 v_Jnn (.mk_uN (proj_uN_0 j)))))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VLOAD .V128 (some (.SPLAT v_N)) ao)]) [(.VCONST .V128 c)]
  | vload_zero_oob : forall (z : state) (i : num_) (v_N : N) (ao : memarg), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_N : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VLOAD .V128 (some (.ZERO v_N)) ao)]) [.TRAP]
  | vload_zero_val : forall (z : state) (i : num_) (v_N : N) (ao : memarg) (c : vec_) (j : iN), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((ibytes_ v_N j) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_N : Nat) / (8 : Nat)) : Nat))) ->
    (c == (extend__ v_N 128 .U j)) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VLOAD .V128 (some (.ZERO v_N)) ao)]) [(.VCONST .V128 c)]
  | vload_lane_oob : forall (z : state) (i : num_) (c_1 : vec_) (v_N : N) (ao : memarg) (j : laneidx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_N : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (.mk_sz v_N) ao j)]) [.TRAP]
  | vload_lane_val : forall (z : state) (i : num_) (c_1 : vec_) (v_N : N) (ao : memarg) (j : laneidx) (c : vec_) (k : iN) (v_Jnn : Jnn) (v_M : M), 
    (wf_num_ .I32 i) ->
    (wf_lane_ (fun_lanetype (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M))) (.mk_lane__2 v_Jnn (.mk_uN (proj_uN_0 k)))) ->
    ((proj_num__0 i) != none) ->
    ((ibytes_ v_N k) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_N : Nat) / (8 : Nat)) : Nat))) ->
    (v_N == (jsize v_Jnn)) ->
    ((v_M : Nat) == ((128 : Nat) / (v_N : Nat))) ->
    (c == (inv_lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) (List.modify (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c_1) (proj_uN_0 j) (fun (_ : lane_) => (.mk_lane__2 v_Jnn (.mk_uN (proj_uN_0 k))))))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.VCONST .V128 c_1), (.VLOAD_LANE .V128 (.mk_sz v_N) ao j)]) [(.VCONST .V128 c)]
  | memory_size : forall (z : state) (v_n : n), 
    (((v_n * 64) * (Ki )) == (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [.MEMORY_SIZE]) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n)))]
  | memory_fill_trap : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_FILL]) [.TRAP]
  | memory_fill_zero : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
    ((proj_num__0 i) != none) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    (wf_num_ .I32 i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST .I32 i), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_FILL]) []
  | memory_fill_succ : forall (z : state) (i : num_) (v_val : val) (v_n : n), 
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 i), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_FILL]) [(.CONST .I32 i), (admininstr_val v_val), (.STORE .I32 (some (.mk_sz 8)) (memarg0 )), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (admininstr_val v_val), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), .MEMORY_FILL]
  | memory_copy_trap : forall (z : state) (j : num_) (i : num_) (v_n : n), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_COPY]) [.TRAP]
  | memory_copy_zero : forall (z : state) (j : num_) (i : num_) (v_n : n), 
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_COPY]) []
  | memory_copy_le : forall (z : state) (j : num_) (i : num_) (v_n : n), 
    ((proj_num__0 j) != none) ->
    ((proj_num__0 i) != none) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_uN_0 (Option.get! (proj_num__0 j))) <= (proj_uN_0 (Option.get! (proj_num__0 i)))) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_COPY]) [(.CONST .I32 j), (.CONST .I32 i), (.LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) (memarg0 )), (.STORE .I32 (some (.mk_sz 8)) (memarg0 )), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), .MEMORY_COPY]
  | memory_copy_gt : forall (z : state) (j : num_) (i : num_) (v_n : n), 
    ((proj_num__0 j) != none) ->
    ((proj_num__0 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 j))) > (proj_uN_0 (Option.get! (proj_num__0 i)))) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_COPY]) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) : Nat) - (1 : Nat)) : Nat)))), (.LOAD .I32 (some (.mk_loadop__0 .I32 (.mk_loadop_Inn (.mk_sz 8) .U))) (memarg0 )), (.STORE .I32 (some (.mk_sz 8)) (memarg0 )), (.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), .MEMORY_COPY]
  | memory_init_trap : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_data z x).BYTES))) || (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x)]) [.TRAP]
  | memory_init_zero : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_data z x).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    (v_n == 0) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x)]) []
  | memory_init_succ : forall (z : state) (j : num_) (i : num_) (v_n : n) (x : idx), 
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_data z x).BYTES))) ->
    ((proj_num__0 i) != none) ->
    ((proj_num__0 j) != none) ->
    (v_n != 0) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) <= (List.length ((fun_data z x).BYTES))) && (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) <= (List.length ((fun_mem z (.mk_uN 0)).BYTES)))) ->
    (wf_num_ .I32 j) ->
    (wf_num_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 j), (.CONST .I32 i), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT x)]) [(.CONST .I32 j), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (proj_byte_0 (((fun_data z x).BYTES)[(proj_uN_0 (Option.get! (proj_num__0 i)))]!))))), (.STORE .I32 (some (.mk_sz 8)) (memarg0 )), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1)))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (((v_n : Nat) - (1 : Nat)) : Nat)))), (.MEMORY_INIT x)]

/- Recursive Definition at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.77 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.77 -/
inductive Step : config -> config -> Prop where
  | pure : forall (z : state) (admininstr_lst : (List admininstr)) (admininstr'_lst : (List admininstr)), 
    (Step_pure admininstr_lst admininstr'_lst) ->
    Step (.mk_config z admininstr_lst) (.mk_config z admininstr'_lst)
  | read : forall (z : state) (admininstr_lst : (List admininstr)) (admininstr'_lst : (List admininstr)), 
    (Step_read (.mk_config z admininstr_lst) admininstr'_lst) ->
    Step (.mk_config z admininstr_lst) (.mk_config z admininstr'_lst)
  | ctxt_label : forall (z : state) (v_n : n) (instr_0_lst : (List instr)) (admininstr_lst : (List admininstr)) (z' : state) (admininstr'_lst : (List admininstr)), 
    (Step (.mk_config z admininstr_lst) (.mk_config z' admininstr'_lst)) ->
    Step (.mk_config z [(.LABEL_ v_n instr_0_lst admininstr_lst)]) (.mk_config z' [(.LABEL_ v_n instr_0_lst admininstr'_lst)])
  | ctxt_frame : forall (s : store) (f : frame) (v_n : n) (f' : frame) (admininstr_lst : (List admininstr)) (s' : store) (f'' : frame) (admininstr'_lst : (List admininstr)), 
    (Step (.mk_config (.mk_state s f') admininstr_lst) (.mk_config (.mk_state s' f'') admininstr'_lst)) ->
    Step (.mk_config (.mk_state s f) [(.FRAME_ v_n f' admininstr_lst)]) (.mk_config (.mk_state s' f) [(.FRAME_ v_n f'' admininstr'_lst)])
  | ctxt_instrs : forall (z : state) (val_lst : (List val)) (admininstr_lst : (List admininstr)) (admininstr_1_lst : (List admininstr)) (z' : state) (admininstr'_lst : (List admininstr)), 
    (Step (.mk_config z admininstr_lst) (.mk_config z' admininstr'_lst)) ->
    ((val_lst != []) || (admininstr_1_lst != [])) ->
    Step (.mk_config z ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (admininstr_lst ++ admininstr_1_lst))) (.mk_config z' ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (admininstr'_lst ++ admininstr_1_lst)))
  | local_set : forall (z : state) (v_val : val) (x : idx), Step (.mk_config z [(admininstr_val v_val), (.LOCAL_SET x)]) (.mk_config (with_local z x v_val) [])
  | global_set : forall (z : state) (v_val : val) (x : idx), Step (.mk_config z [(admininstr_val v_val), (.GLOBAL_SET x)]) (.mk_config (with_global z x v_val) [])
  | table_set_trap : forall (z : state) (i : num_) (v_ref : ref) (x : idx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) >= (List.length ((fun_table z x).REFS))) ->
    Step (.mk_config z [(.CONST .I32 i), (admininstr_ref v_ref), (.TABLE_SET x)]) (.mk_config z [.TRAP])
  | table_set_val : forall (z : state) (i : num_) (v_ref : ref) (x : idx), 
    ((proj_num__0 i) != none) ->
    (wf_num_ .I32 i) ->
    ((proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS))) ->
    Step (.mk_config z [(.CONST .I32 i), (admininstr_ref v_ref), (.TABLE_SET x)]) (.mk_config (with_table z x (proj_uN_0 (Option.get! (proj_num__0 i))) v_ref) [])
  | table_grow_succeed : forall (z : state) (v_ref : ref) (v_n : n) (x : idx) (ti : tableinst) (var_0 : (Option tableinst)), 
    (fun_growtable (fun_table z x) v_n v_ref var_0) ->
    (var_0 != none) ->
    ((Option.get! var_0) == ti) ->
    Step (.mk_config z [(admininstr_ref v_ref), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_GROW x)]) (.mk_config (with_tableinst z x ti) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN (List.length ((fun_table z x).REFS)))))])
  | table_grow_fail : forall (z : state) (v_ref : ref) (v_n : n) (x : idx) (var_0 : Nat), 
    (fun_inv_signed_ 32 (0 - (1 : Nat)) var_0) ->
    Step (.mk_config z [(admininstr_ref v_ref), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_GROW x)]) (.mk_config z [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN var_0)))])
  | elem_drop : forall (z : state) (x : idx), Step (.mk_config z [(.ELEM_DROP x)]) (.mk_config (with_elem z x []) [])
  | store_num_trap : forall (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg), 
    (wf_num_ .I32 i) ->
    (wf_num_ nt c) ->
    ((proj_num__0 i) != none) ->
    ((size (valtype_numtype nt)) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((Option.get! (size (valtype_numtype nt))) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step (.mk_config z [(.CONST .I32 i), (.CONST nt c), (.STORE nt none ao)]) (.mk_config z [.TRAP])
  | store_num_val : forall (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) (b_lst : (List byte)), 
    ((proj_num__0 i) != none) ->
    ((size (valtype_numtype nt)) != none) ->
    (wf_num_ .I32 i) ->
    (wf_num_ nt c) ->
    (b_lst == (nbytes_ nt c)) ->
    Step (.mk_config z [(.CONST .I32 i), (.CONST nt c), (.STORE nt none ao)]) (.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((Option.get! (size (valtype_numtype nt))) : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | store_pack_trap : forall (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg), 
    (wf_num_ .I32 i) ->
    (wf_num_ (numtype_Inn v_Inn) c) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_n : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step (.mk_config z [(.CONST .I32 i), (.CONST (numtype_Inn v_Inn) c), (.STORE (numtype_Inn v_Inn) (some (.mk_sz v_n)) ao)]) (.mk_config z [.TRAP])
  | store_pack_val : forall (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) (b_lst : (List byte)), 
    ((proj_num__0 i) != none) ->
    (wf_num_ .I32 i) ->
    (wf_num_ (numtype_Inn v_Inn) c) ->
    ((size (valtype_Inn v_Inn)) != none) ->
    ((proj_num__0 c) != none) ->
    (b_lst == (ibytes_ v_n (wrap__ (Option.get! (size (valtype_Inn v_Inn))) v_n (Option.get! (proj_num__0 c))))) ->
    Step (.mk_config z [(.CONST .I32 i), (.CONST (numtype_Inn v_Inn) c), (.STORE (numtype_Inn v_Inn) (some (.mk_sz v_n)) ao)]) (.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_n : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | vstore_oob : forall (z : state) (i : num_) (c : vec_) (ao : memarg), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((size .V128) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((Option.get! (size .V128)) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step (.mk_config z [(.CONST .I32 i), (.VCONST .V128 c), (.VSTORE .V128 ao)]) (.mk_config z [.TRAP])
  | vstore_val : forall (z : state) (i : num_) (c : vec_) (ao : memarg) (b_lst : (List byte)), 
    ((proj_num__0 i) != none) ->
    ((size .V128) != none) ->
    (wf_num_ .I32 i) ->
    (b_lst == (vbytes_ .V128 c)) ->
    Step (.mk_config z [(.CONST .I32 i), (.VCONST .V128 c), (.VSTORE .V128 ao)]) (.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((Option.get! (size .V128)) : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | vstore_lane_oob : forall (z : state) (i : num_) (c : vec_) (v_N : N) (ao : memarg) (j : laneidx), 
    (wf_num_ .I32 i) ->
    ((proj_num__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + v_N) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step (.mk_config z [(.CONST .I32 i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (.mk_sz v_N) ao j)]) (.mk_config z [.TRAP])
  | vstore_lane_val : forall (z : state) (i : num_) (c : vec_) (v_N : N) (ao : memarg) (j : laneidx) (b_lst : (List byte)) (v_Jnn : Jnn) (v_M : M), 
    ((proj_num__0 i) != none) ->
    (wf_num_ .I32 i) ->
    (v_N == (jsize v_Jnn)) ->
    ((v_M : Nat) == ((128 : Nat) / (v_N : Nat))) ->
    ((proj_lane__2 ((lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c)[(proj_uN_0 j)]!)) != none) ->
    ((proj_uN_0 j) < (List.length (lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c))) ->
    (b_lst == (ibytes_ v_N (.mk_uN (proj_uN_0 (Option.get! (proj_lane__2 ((lanes_ (.X (lanetype_Jnn v_Jnn) (.mk_dim v_M)) c)[(proj_uN_0 j)]!))))))) ->
    Step (.mk_config z [(.CONST .I32 i), (.VCONST .V128 c), (.VSTORE_LANE .V128 (.mk_sz v_N) ao j)]) (.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_N : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | memory_grow_succeed : forall (z : state) (v_n : n) (mi : meminst) (var_0 : (Option meminst)), 
    (fun_growmemory (fun_mem z (.mk_uN 0)) v_n var_0) ->
    (var_0 != none) ->
    ((Option.get! var_0) == mi) ->
    Step (.mk_config z [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_GROW]) (.mk_config (with_meminst z (.mk_uN 0) mi) [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((((List.length ((fun_mem z (.mk_uN 0)).BYTES)) : Nat) / ((64 * (Ki )) : Nat)) : Nat))))])
  | memory_grow_fail : forall (z : state) (v_n : n) (var_0 : Nat), 
    (fun_inv_signed_ 32 (0 - (1 : Nat)) var_0) ->
    Step (.mk_config z [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), .MEMORY_GROW]) (.mk_config z [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN var_0)))])
  | data_drop : forall (z : state) (x : idx), Step (.mk_config z [(.DATA_DROP x)]) (.mk_config (with_data z x []) [])

/- Recursive Definition at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 -/
inductive Steps : config -> config -> Prop where
  | refl : forall (z : state) (admininstr_lst : (List admininstr)), Steps (.mk_config z admininstr_lst) (.mk_config z admininstr_lst)
  | trans : forall (z : state) (admininstr_lst : (List admininstr)) (z'' : state) (admininstr''_lst : (List admininstr)) (z' : state) (admininstr'_lst : (List admininstr)), 
    (Step (.mk_config z admininstr_lst) (.mk_config z' admininstr'_lst)) ->
    (Steps (.mk_config z' admininstr'_lst) (.mk_config z'' admininstr''_lst)) ->
    Steps (.mk_config z admininstr_lst) (.mk_config z'' admininstr''_lst)

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83 -/
inductive Eval_expr : state -> expr -> state -> (List val) -> Prop where
  | mk_Eval_expr : forall (z : state) (instr_lst : (List instr)) (z' : state) (val_lst : (List val)), 
    (Steps (.mk_config z (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)) (.mk_config z' (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))) ->
    Eval_expr z instr_lst z' val_lst

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:5.1-5.36 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:5.6-5.12 -/
inductive fun_funcs : (List externaddr) -> (List funcaddr) -> Prop where
  | fun_funcs_case_0 : fun_funcs [] []
  | fun_funcs_case_1 : forall (fa : Nat) (externaddr'_lst : (List externaddr)) (var_0 : (List funcaddr)), 
    (fun_funcs externaddr'_lst var_0) ->
    fun_funcs ([(.FUNC fa)] ++ externaddr'_lst) ([fa] ++ var_0)
  | fun_funcs_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (List externaddr)) (var_0 : (List funcaddr)), 
    (fun_funcs externaddr'_lst var_0) ->
    fun_funcs ([v_externaddr] ++ externaddr'_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:11.1-11.40 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:11.6-11.14 -/
inductive fun_globals : (List externaddr) -> (List globaladdr) -> Prop where
  | fun_globals_case_0 : fun_globals [] []
  | fun_globals_case_1 : forall (ga : Nat) (externaddr'_lst : (List externaddr)) (var_0 : (List globaladdr)), 
    (fun_globals externaddr'_lst var_0) ->
    fun_globals ([(.GLOBAL ga)] ++ externaddr'_lst) ([ga] ++ var_0)
  | fun_globals_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (List externaddr)) (var_0 : (List globaladdr)), 
    (fun_globals externaddr'_lst var_0) ->
    fun_globals ([v_externaddr] ++ externaddr'_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:17.1-17.38 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:17.6-17.13 -/
inductive fun_tables : (List externaddr) -> (List tableaddr) -> Prop where
  | fun_tables_case_0 : fun_tables [] []
  | fun_tables_case_1 : forall (ta : Nat) (externaddr'_lst : (List externaddr)) (var_0 : (List tableaddr)), 
    (fun_tables externaddr'_lst var_0) ->
    fun_tables ([(.TABLE ta)] ++ externaddr'_lst) ([ta] ++ var_0)
  | fun_tables_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (List externaddr)) (var_0 : (List tableaddr)), 
    (fun_tables externaddr'_lst var_0) ->
    fun_tables ([v_externaddr] ++ externaddr'_lst) var_0

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:23.1-23.34 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:23.6-23.11 -/
inductive fun_mems : (List externaddr) -> (List memaddr) -> Prop where
  | fun_mems_case_0 : fun_mems [] []
  | fun_mems_case_1 : forall (ma : Nat) (externaddr'_lst : (List externaddr)) (var_0 : (List memaddr)), 
    (fun_mems externaddr'_lst var_0) ->
    fun_mems ([(.MEM ma)] ++ externaddr'_lst) ([ma] ++ var_0)
  | fun_mems_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (List externaddr)) (var_0 : (List memaddr)), 
    (fun_mems externaddr'_lst var_0) ->
    fun_mems ([v_externaddr] ++ externaddr'_lst) var_0

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 -/
inductive fun_allocfunc : store -> moduleinst -> func -> store × funcaddr -> Prop where
  | fun_allocfunc_case_0 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (fi : funcinst) (x : uN) (local_lst : (List «local»)) (v_expr : (List instr)), 
    ((proj_uN_0 x) < (List.length (v_moduleinst.TYPES))) ->
    (fi == { TYPE := ((v_moduleinst.TYPES)[(proj_uN_0 x)]!), MODULE := v_moduleinst, CODE := v_func }) ->
    (v_func == (.FUNC x local_lst v_expr)) ->
    fun_allocfunc s v_moduleinst v_func ((s <| FUNCS := ((FUNCS s) ++ [fi]) |>), (List.length (s.FUNCS)))

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:41.1-41.63 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:41.6-41.17 -/
inductive fun_allocfuncs : store -> moduleinst -> (List func) -> store × (List funcaddr) -> Prop where
  | fun_allocfuncs_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_allocfuncs s v_moduleinst [] (s, [])
  | fun_allocfuncs_case_1 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (func'_lst : (List func)) (s_2 : store) (fa : Nat) (fa'_lst : (List funcaddr)) (s_1 : store) (var_1 : store × (List funcaddr)) (var_0 : store × funcaddr), 
    (fun_allocfuncs s_1 v_moduleinst func'_lst var_1) ->
    (fun_allocfunc s v_moduleinst v_func var_0) ->
    ((s_1, fa) == var_0) ->
    ((s_2, fa'_lst) == var_1) ->
    fun_allocfuncs s v_moduleinst ([v_func] ++ func'_lst) (s_2, ([fa] ++ fa'_lst))

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 -/
inductive fun_allocglobal : store -> globaltype -> val -> store × globaladdr -> Prop where
  | fun_allocglobal_case_0 : forall (s : store) (v_globaltype : globaltype) (v_val : val) (gi : globalinst), 
    (gi == { TYPE := v_globaltype, VALUE := v_val }) ->
    fun_allocglobal s v_globaltype v_val ((s <| GLOBALS := ((GLOBALS s) ++ [gi]) |>), (List.length (s.GLOBALS)))

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:51.1-51.67 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:51.6-51.19 -/
inductive fun_allocglobals : store -> (List globaltype) -> (List val) -> store × (List globaladdr) -> Prop where
  | fun_allocglobals_case_0 : forall (s : store), fun_allocglobals s [] [] (s, [])
  | fun_allocglobals_case_1 : forall (s : store) (v_globaltype : globaltype) (globaltype'_lst : (List globaltype)) (v_val : val) (val'_lst : (List val)) (s_2 : store) (ga : Nat) (ga'_lst : (List globaladdr)) (s_1 : store) (var_1 : store × (List globaladdr)) (var_0 : store × globaladdr), 
    (fun_allocglobals s_1 globaltype'_lst val'_lst var_1) ->
    (fun_allocglobal s v_globaltype v_val var_0) ->
    ((s_1, ga) == var_0) ->
    ((s_2, ga'_lst) == var_1) ->
    fun_allocglobals s ([v_globaltype] ++ globaltype'_lst) ([v_val] ++ val'_lst) (s_2, ([ga] ++ ga'_lst))

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 -/
inductive fun_alloctable : store -> tabletype -> store × tableaddr -> Prop where
  | fun_alloctable_case_0 : forall (s : store) (i : uN) (j_opt : (Option u32)) (rt : reftype) (ti : tableinst), 
    (ti == { TYPE := (.mk_tabletype (.mk_limits i j_opt) rt), REFS := (List.replicate (proj_uN_0 i) (.REF_NULL rt)) }) ->
    fun_alloctable s (.mk_tabletype (.mk_limits i j_opt) rt) ((s <| TABLES := ((TABLES s) ++ [ti]) |>), (List.length (s.TABLES)))

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:61.1-61.58 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:61.6-61.18 -/
inductive fun_alloctables : store -> (List tabletype) -> store × (List tableaddr) -> Prop where
  | fun_alloctables_case_0 : forall (s : store), fun_alloctables s [] (s, [])
  | fun_alloctables_case_1 : forall (s : store) (v_tabletype : tabletype) (tabletype'_lst : (List tabletype)) (s_2 : store) (ta : Nat) (ta'_lst : (List tableaddr)) (s_1 : store) (var_1 : store × (List tableaddr)) (var_0 : store × tableaddr), 
    (fun_alloctables s_1 tabletype'_lst var_1) ->
    (fun_alloctable s v_tabletype var_0) ->
    ((s_1, ta) == var_0) ->
    ((s_2, ta'_lst) == var_1) ->
    fun_alloctables s ([v_tabletype] ++ tabletype'_lst) (s_2, ([ta] ++ ta'_lst))

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 -/
inductive fun_allocmem : store -> memtype -> store × memaddr -> Prop where
  | fun_allocmem_case_0 : forall (s : store) (i : uN) (j_opt : (Option u32)) (mi : meminst), 
    (mi == { TYPE := (.PAGE (.mk_limits i j_opt)), BYTES := (List.replicate ((proj_uN_0 i) * (64 * (Ki ))) (.mk_byte 0)) }) ->
    fun_allocmem s (.PAGE (.mk_limits i j_opt)) ((s <| MEMS := ((MEMS s) ++ [mi]) |>), (List.length (s.MEMS)))

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:71.1-71.52 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:71.6-71.16 -/
inductive fun_allocmems : store -> (List memtype) -> store × (List memaddr) -> Prop where
  | fun_allocmems_case_0 : forall (s : store), fun_allocmems s [] (s, [])
  | fun_allocmems_case_1 : forall (s : store) (v_memtype : memtype) (memtype'_lst : (List memtype)) (s_2 : store) (ma : Nat) (ma'_lst : (List memaddr)) (s_1 : store) (var_1 : store × (List memaddr)) (var_0 : store × memaddr), 
    (fun_allocmems s_1 memtype'_lst var_1) ->
    (fun_allocmem s v_memtype var_0) ->
    ((s_1, ma) == var_0) ->
    ((s_2, ma'_lst) == var_1) ->
    fun_allocmems s ([v_memtype] ++ memtype'_lst) (s_2, ([ma] ++ ma'_lst))

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 -/
inductive fun_allocelem : store -> reftype -> (List ref) -> store × elemaddr -> Prop where
  | fun_allocelem_case_0 : forall (s : store) (rt : reftype) (ref_lst : (List ref)) (ei : eleminst), 
    (ei == { TYPE := rt, REFS := ref_lst }) ->
    fun_allocelem s rt ref_lst ((s <| ELEMS := ((ELEMS s) ++ [ei]) |>), (List.length (s.ELEMS)))

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:81.1-81.63 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:81.6-81.17 -/
inductive fun_allocelems : store -> (List reftype) -> (List (List ref)) -> store × (List elemaddr) -> Prop where
  | fun_allocelems_case_0 : forall (s : store), fun_allocelems s [] [] (s, [])
  | fun_allocelems_case_1 : forall (s : store) (rt : reftype) (rt'_lst : (List reftype)) (ref_lst : (List ref)) (ref'_lst_lst : (List (List ref))) (s_2 : store) (ea : Nat) (ea'_lst : (List elemaddr)) (s_1 : store) (var_1 : store × (List elemaddr)) (var_0 : store × elemaddr), 
    (fun_allocelems s_1 rt'_lst ref'_lst_lst var_1) ->
    (fun_allocelem s rt ref_lst var_0) ->
    ((s_1, ea) == var_0) ->
    ((s_2, ea'_lst) == var_1) ->
    fun_allocelems s ([rt] ++ rt'_lst) ([ref_lst] ++ ref'_lst_lst) (s_2, ([ea] ++ ea'_lst))

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 -/
inductive fun_allocdata : store -> (List byte) -> store × dataaddr -> Prop where
  | fun_allocdata_case_0 : forall (s : store) (byte_lst : (List byte)) (di : datainst), 
    (di == { BYTES := byte_lst }) ->
    fun_allocdata s byte_lst ((s <| DATAS := ((DATAS s) ++ [di]) |>), (List.length (s.DATAS)))

/- Recursive Definition at: ../specification/wasm-2.0/9-module.spectec:91.1-91.54 -/
/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:91.6-91.17 -/
inductive fun_allocdatas : store -> (List (List byte)) -> store × (List dataaddr) -> Prop where
  | fun_allocdatas_case_0 : forall (s : store), fun_allocdatas s [] (s, [])
  | fun_allocdatas_case_1 : forall (s : store) (byte_lst : (List byte)) (byte'_lst_lst : (List (List byte))) (s_2 : store) (da : Nat) (da'_lst : (List dataaddr)) (s_1 : store) (var_1 : store × (List dataaddr)) (var_0 : store × dataaddr), 
    (fun_allocdatas s_1 byte'_lst_lst var_1) ->
    (fun_allocdata s byte_lst var_0) ->
    ((s_1, da) == var_0) ->
    ((s_2, da'_lst) == var_1) ->
    fun_allocdatas s ([byte_lst] ++ byte'_lst_lst) (s_2, ([da] ++ da'_lst))

/- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:100.1-100.83 -/
def instexport : ∀  (var_0 : (List funcaddr)) (var_1 : (List globaladdr)) (var_2 : (List tableaddr)) (var_3 : (List memaddr)) (v_export : «export») , exportinst
  | fa_lst, ga_lst, ta_lst, ma_lst, (.EXPORT v_name (.FUNC x)) =>
    { NAME := v_name, ADDR := (.FUNC (fa_lst[(proj_uN_0 x)]!)) }
  | fa_lst, ga_lst, ta_lst, ma_lst, (.EXPORT v_name (.GLOBAL x)) =>
    { NAME := v_name, ADDR := (.GLOBAL (ga_lst[(proj_uN_0 x)]!)) }
  | fa_lst, ga_lst, ta_lst, ma_lst, (.EXPORT v_name (.TABLE x)) =>
    { NAME := v_name, ADDR := (.TABLE (ta_lst[(proj_uN_0 x)]!)) }
  | fa_lst, ga_lst, ta_lst, ma_lst, (.EXPORT v_name (.MEM x)) =>
    { NAME := v_name, ADDR := (.MEM (ma_lst[(proj_uN_0 x)]!)) }


/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 -/
inductive fun_allocmodule : store -> module -> (List externaddr) -> (List val) -> (List (List ref)) -> store × moduleinst -> Prop where
  | fun_allocmodule_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (List externaddr)) (val_lst : (List val)) (ref_lst_lst : (List (List ref))) (s_6 : store) (v_moduleinst : moduleinst) (ft_lst : (List functype)) (import_lst : (List «import»)) (func_lst : (List func)) (n_func : Nat) (globaltype_lst : (List globaltype)) (expr_1_lst : (List expr)) (n_global : Nat) (tabletype_lst : (List tabletype)) (n_table : Nat) (memtype_lst : (List memtype)) (n_mem : Nat) (rt_lst : (List reftype)) (expr_2_lst_lst : (List (List expr))) (elemmode_lst : (List elemmode)) (n_elem : Nat) (byte_lst_lst : (List (List byte))) (datamode_lst : (List datamode)) (n_data : Nat) (start_opt : (Option start)) (export_lst : (List «export»)) (fa_ex_lst : (List funcaddr)) (ga_ex_lst : (List globaladdr)) (ta_ex_lst : (List tableaddr)) (ma_ex_lst : (List memaddr)) (fa_lst : (List funcaddr)) (i_func_lst : (List Nat)) (ga_lst : (List globaladdr)) (i_global_lst : (List Nat)) (ta_lst : (List tableaddr)) (i_table_lst : (List Nat)) (ma_lst : (List memaddr)) (i_mem_lst : (List Nat)) (ea_lst : (List elemaddr)) (i_elem_lst : (List Nat)) (da_lst : (List dataaddr)) (i_data_lst : (List Nat)) (xi_lst : (List exportinst)) (s_1 : store) (s_2 : store) (s_3 : store) (s_4 : store) (s_5 : store) (var_9 : store × (List dataaddr)) (var_8 : store × (List elemaddr)) (var_7 : store × (List memaddr)) (var_6 : store × (List tableaddr)) (var_5 : store × (List globaladdr)) (var_4 : store × (List funcaddr)) (var_3 : (List memaddr)) (var_2 : (List tableaddr)) (var_1 : (List globaladdr)) (var_0 : (List funcaddr)), 
    (fun_allocdatas s_5 byte_lst_lst var_9) ->
    (fun_allocelems s_4 rt_lst ref_lst_lst var_8) ->
    (fun_allocmems s_3 memtype_lst var_7) ->
    (fun_alloctables s_2 tabletype_lst var_6) ->
    (fun_allocglobals s_1 globaltype_lst val_lst var_5) ->
    (fun_allocfuncs s v_moduleinst func_lst var_4) ->
    (fun_mems externaddr_lst var_3) ->
    (fun_tables externaddr_lst var_2) ->
    (fun_globals externaddr_lst var_1) ->
    (fun_funcs externaddr_lst var_0) ->
    (v_module == (.MODULE (List.map (fun (ft : functype) => (.TYPE ft)) ft_lst) import_lst func_lst (List.zipWith (fun (expr_1 : expr) (v_globaltype : globaltype) => (.GLOBAL v_globaltype expr_1)) expr_1_lst globaltype_lst) (List.map (fun (v_tabletype : tabletype) => (.TABLE v_tabletype)) tabletype_lst) (List.map (fun (v_memtype : memtype) => (.MEMORY v_memtype)) memtype_lst) (list_map3 (fun (v_elemmode : elemmode) (expr_2_lst : (List expr)) (rt : reftype) => (.ELEM rt expr_2_lst v_elemmode)) elemmode_lst expr_2_lst_lst rt_lst) (List.zipWith (fun (byte_lst : (List byte)) (v_datamode : datamode) => (.DATA byte_lst v_datamode)) byte_lst_lst datamode_lst) start_opt export_lst)) ->
    (fa_ex_lst == var_0) ->
    (ga_ex_lst == var_1) ->
    (ta_ex_lst == var_2) ->
    (ma_ex_lst == var_3) ->
    (fa_lst == (List.map (fun (i_func : Nat) => ((List.length (s.FUNCS)) + i_func)) i_func_lst)) ->
    (ga_lst == (List.map (fun (i_global : Nat) => ((List.length (s.GLOBALS)) + i_global)) i_global_lst)) ->
    (ta_lst == (List.map (fun (i_table : Nat) => ((List.length (s.TABLES)) + i_table)) i_table_lst)) ->
    (ma_lst == (List.map (fun (i_mem : Nat) => ((List.length (s.MEMS)) + i_mem)) i_mem_lst)) ->
    (ea_lst == (List.map (fun (i_elem : Nat) => ((List.length (s.ELEMS)) + i_elem)) i_elem_lst)) ->
    (da_lst == (List.map (fun (i_data : Nat) => ((List.length (s.DATAS)) + i_data)) i_data_lst)) ->
    (xi_lst == (List.map (fun (v_export : «export») => (instexport (fa_ex_lst ++ fa_lst) (ga_ex_lst ++ ga_lst) (ta_ex_lst ++ ta_lst) (ma_ex_lst ++ ma_lst) v_export)) export_lst)) ->
    (v_moduleinst == { TYPES := ft_lst, FUNCS := (fa_ex_lst ++ fa_lst), GLOBALS := (ga_ex_lst ++ ga_lst), TABLES := (ta_ex_lst ++ ta_lst), MEMS := (ma_ex_lst ++ ma_lst), ELEMS := ea_lst, DATAS := da_lst, EXPORTS := xi_lst }) ->
    ((s_1, fa_lst) == var_4) ->
    ((s_2, ga_lst) == var_5) ->
    ((s_3, ta_lst) == var_6) ->
    ((s_4, ma_lst) == var_7) ->
    ((s_5, ea_lst) == var_8) ->
    ((s_6, da_lst) == var_9) ->
    fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst (s_6, v_moduleinst)

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:154.6-154.14 -/
inductive fun_runelem : elem -> idx -> (List instr) -> Prop where
  | fun_runelem_case_0 : forall (v_reftype : reftype) (expr_lst : (List expr)) (i : uN), fun_runelem (.ELEM v_reftype expr_lst .PASSIVE) i []
  | fun_runelem_case_1 : forall (v_reftype : reftype) (expr_lst : (List expr)) (i : uN), fun_runelem (.ELEM v_reftype expr_lst .DECLARE) i [(.ELEM_DROP i)]
  | fun_runelem_case_2 : forall (v_reftype : reftype) (expr_lst : (List expr)) (x : uN) (instr_lst : (List instr)) (i : uN) (v_n : Nat), 
    (v_n == (List.length expr_lst)) ->
    fun_runelem (.ELEM v_reftype expr_lst (.ACTIVE x instr_lst)) i (instr_lst ++ [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.TABLE_INIT x i), (.ELEM_DROP i)])

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:161.6-161.14 -/
inductive fun_rundata : data -> idx -> (List instr) -> Prop where
  | fun_rundata_case_0 : forall (byte_lst : (List byte)) (i : uN), fun_rundata (.DATA byte_lst .PASSIVE) i []
  | fun_rundata_case_1 : forall (byte_lst : (List byte)) (instr_lst : (List instr)) (i : uN) (v_n : Nat), 
    (v_n == (List.length byte_lst)) ->
    fun_rundata (.DATA byte_lst (.ACTIVE (.mk_uN 0) instr_lst)) i (instr_lst ++ [(.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))), (.CONST .I32 (.mk_num__0 .I32 (.mk_uN v_n))), (.MEMORY_INIT i), (.DATA_DROP i)])

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 -/
inductive fun_instantiate : store -> module -> (List externaddr) -> config -> Prop where
  | fun_instantiate_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (List externaddr)) (s' : store) (f : frame) (instr_E_lst : (List instr)) (instr_D_lst : (List instr)) (x_opt : (Option idx)) (type_lst : (List type)) (import_lst : (List «import»)) (func_lst : (List func)) (global_lst : (List global)) (table_lst : (List table)) (mem_lst : (List mem)) (elem_lst : (List elem)) (data_lst : (List data)) (start_opt : (Option start)) (export_lst : (List «export»)) (functype_lst : (List functype)) (globaltype_lst : (List globaltype)) (expr_G_lst : (List expr)) (reftype_lst : (List reftype)) (expr_E_lst_lst : (List (List expr))) (elemmode_lst : (List elemmode)) (n_F : Nat) (n_E : Nat) (n_D : Nat) (moduleinst_init : moduleinst) (i_F_lst : (List Nat)) (f_init : frame) (z : state) (val_lst : (List val)) (ref_lst_lst : (List (List ref))) (v_moduleinst : moduleinst) (i_lst : (List Nat)) (j_lst : (List Nat)) (var_4_lst : (List (List instr))) (var_3_lst : (List (List instr))) (var_2 : store × moduleinst) (var_1 : (List globaladdr)) (var_0 : (List funcaddr)), 
    Forall (fun (j : Nat) => (j < (List.length data_lst))) j_lst ->
    Forall₂ (fun (var_4 : (List instr)) (j : Nat) => (fun_rundata (data_lst[j]!) (.mk_uN j) var_4)) var_4_lst j_lst ->
    Forall (fun (i : Nat) => (i < (List.length elem_lst))) i_lst ->
    Forall₂ (fun (var_3 : (List instr)) (i : Nat) => (fun_runelem (elem_lst[i]!) (.mk_uN i) var_3)) var_3_lst i_lst ->
    (fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst var_2) ->
    (fun_globals externaddr_lst var_1) ->
    (fun_funcs externaddr_lst var_0) ->
    (v_module == (.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ->
    (type_lst == (List.map (fun (v_functype : functype) => (.TYPE v_functype)) functype_lst)) ->
    (global_lst == (List.zipWith (fun (expr_G : expr) (v_globaltype : globaltype) => (.GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ->
    (elem_lst == (list_map3 (fun (v_elemmode : elemmode) (expr_E_lst : (List expr)) (v_reftype : reftype) => (.ELEM v_reftype expr_E_lst v_elemmode)) elemmode_lst expr_E_lst_lst reftype_lst)) ->
    (start_opt == (Option.map (fun (x : idx) => (.START x)) x_opt)) ->
    (n_F == (List.length func_lst)) ->
    (n_E == (List.length elem_lst)) ->
    (n_D == (List.length data_lst)) ->
    (moduleinst_init == { TYPES := functype_lst, FUNCS := (var_0 ++ (List.map (fun (i_F : Nat) => ((List.length (s.FUNCS)) + i_F)) i_F_lst)), GLOBALS := var_1, TABLES := [], MEMS := [], ELEMS := [], DATAS := [], EXPORTS := [] }) ->
    (f_init == { LOCALS := [], MODULE := moduleinst_init }) ->
    (z == (.mk_state s f_init)) ->
    ((List.length expr_G_lst) == (List.length val_lst)) ->
    Forall₂ (fun (expr_G : expr) (v_val : val) => (Eval_expr z expr_G z [v_val])) expr_G_lst val_lst ->
    ((List.length expr_E_lst_lst) == (List.length ref_lst_lst)) ->
    Forall₂ (fun (expr_E_lst : (List expr)) (ref_lst : (List ref)) => ((List.length expr_E_lst) == (List.length ref_lst))) expr_E_lst_lst ref_lst_lst ->
    Forall₂ (fun (expr_E_lst : (List expr)) (ref_lst : (List ref)) => Forall₂ (fun (expr_E : expr) (v_ref : ref) => (Eval_expr z expr_E z [(val_ref v_ref)])) expr_E_lst ref_lst) expr_E_lst_lst ref_lst_lst ->
    ((s', v_moduleinst) == var_2) ->
    (f == { LOCALS := [], MODULE := v_moduleinst }) ->
    (instr_E_lst == (concat_ instr var_3_lst)) ->
    (instr_D_lst == (concat_ instr var_4_lst)) ->
    fun_instantiate s v_module externaddr_lst (.mk_config (.mk_state s' f) ((List.map (fun (instr_E : instr) => (admininstr_instr instr_E)) instr_E_lst) ++ ((List.map (fun (instr_D : instr) => (admininstr_instr instr_D)) instr_D_lst) ++ (Option.toList (Option.map (fun (x : idx) => (.CALL x)) x_opt)))))

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 -/
inductive fun_invoke : store -> funcaddr -> (List val) -> config -> Prop where
  | fun_invoke_case_0 : forall (s : store) (fa : Nat) (val_lst : (List val)) (v_n : Nat) (f : frame) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), 
    (f == { LOCALS := [], MODULE := { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [], EXPORTS := [] } }) ->
    (fa < (List.length (fun_funcinst (.mk_state s f)))) ->
    ((((fun_funcinst (.mk_state s f))[fa]!).TYPE) == (.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) ->
    fun_invoke s fa val_lst (.mk_config (.mk_state s f) ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [(.CALL_ADDR fa)]))

/- Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:849.1-849.43 -/
abbrev startopt : Type := (List start)

/- Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:884.1-884.29 -/
abbrev code : Type := (List «local») × expr

/- Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:915.1-915.33 -/
abbrev nopt : Type := (List u32)
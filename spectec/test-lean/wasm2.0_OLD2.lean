def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


def Forall {α₁ : Type} (P : α₁ → Prop) (xs₁ : List α₁) : Prop :=
  ∀ t_elem ∈ xs₁, P t_elem

def Forall₂ {α₁ α₂ : Type} (P : α₁ → α₂ → Prop) (xs₁ : List α₁) (xs₂ : List α₂) : Prop :=
  ∀ t ∈ xs₁ |>.zip xs₂, P (t.1) (t.2)

def Forall₃ {α₁ α₂ α₃ : Type} (P : α₁ → α₂ → α₃ → Prop) (xs₁ : List α₁) (xs₂ : List α₂) (xs₃ : List α₃) : Prop :=
  ∀ t ∈ xs₁ |>.zip xs₂ |>.zip xs₃, P (t.1.1) (t.1.2) (t.2)

def Map {α₁ β : Type} (f : α₁ → β) (xs₁ : List α₁) : List β :=
  xs₁ |>.map f

def Map₂ {α₁ α₂ β : Type} (f : α₁ → α₂ → β) (xs₁ : List α₁) (xs₂ : List α₂) : List β :=
  xs₁ |>.map f |>.ap xs₂

def Map₃ {α₁ α₂ α₃ β : Type} (f : α₁ → α₂ → α₃ → β) (xs₁ : List α₁) (xs₂ : List α₂) (xs₃ : List α₃) : List β :=
  xs₁ |>.map f |>.ap xs₂ |>.ap xs₃

def OMap {α₁ β : Type} (f : α₁ → β) (xs₁ : Option α₁) : Option β :=
  xs₁ |>.map f

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.14-162.17 -/
inductive r_MUT : Type where
  | MUT : r_MUT
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
def Ki : Nat :=
  1024

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:21.1-21.25 -/
def min (nat : Nat) (nat_0 : Nat) : Nat :=
  if
    nat ≤ nat_0
  then
    nat
  else
    nat_0

/- Inductive Relations Definition at: ../specification/wasm-2.0/0-aux.spectec:25.6-25.10 -/
inductive fun_sum : List Nat → Nat → Prop where
  | fun_sum_case_0 : fun_sum [] 0
  | fun_sum_case_1 (v_n : Nat) (n'_lst : List n) (var_0 : Nat) :
    fun_sum n'_lst var_0 →
    fun_sum ([v_n] ++ n'_lst) (v_n + var_0)


/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:32.1-32.58 -/
def opt_ (X : Type) (var_0_lst : List X) : Option (Option X) :=
  match var_0_lst with
  | [] => some none
  | [w] => some (some w)
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:36.1-36.45 -/
def list_ (X : Type) (var_0_opt : Option X) : List X :=
  match var_0_opt with
  | none => []
  | some w => [w]

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:40.1-40.86 -/
def concat_ (X : Type) (var_0_lst_lst : List (List X)) : List X :=
  match var_0_lst_lst with
  | [] => []
  | w_lst :: w'_lst_lst => w_lst ++ (concat_ X w'_lst_lst)

/- Axiom Definition at: ../specification/wasm-2.0/0-aux.spectec:44.1-44.39 -/
opaque inv_concat_ (X : Type) (var_0_lst : List X) : List (List X) := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:51.1-51.46 -/
def setproduct2_ (X : Type) (X_0 : X) (var_0_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst_lst with
  | [] => []
  | w'_lst :: w_lst_lst => [[X_0] ++ w'_lst] ++ (setproduct2_ X X_0 w_lst_lst)

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:50.1-50.47 -/
def setproduct1_ (X : Type) (var_0_lst : List X) (var_1_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst with
  | [] => []
  | w_1 :: w'_lst => (setproduct2_ X w_1 var_1_lst_lst) ++ (setproduct1_ X w'_lst var_1_lst_lst)

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:49.1-49.84 -/
def setproduct_ (X : Type) (var_0_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst_lst with
  | [] => [[]]
  | w_1_lst :: w_lst_lst => setproduct1_ X w_1_lst (setproduct_ X w_lst_lst)

/- Auxiliary Definition at: ../specification/wasm-2.0/0-aux.spectec:60.1-60.78 -/
def disjoint_ (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => true
  | w :: w'_lst => (! (List.contains w'_lst w)) && (disjoint_ X w'_lst)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 -/
inductive list (X : Type) : Type where
  | mk_list (X_lst : List X) : list X
deriving Inhabited, BEq

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:6.1-6.49 -/
def proj_list_0 (X : Type) (x : list X) : List X :=
  match x with
  | list.mk_list v_X_list_0 => (v_X_list_0)

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.1-15.36 -/
inductive bit : Type where
  | mk_bit (i : Nat) : bit
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:15.8-15.11 -/
inductive wf_bit : bit → Prop where
  | bit_case_0 (i : Nat) :
    (i = 0) ∨ (i = 1) →
    wf_bit (bit.mk_bit i)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 -/
inductive byte : Type where
  | mk_byte (i : Nat) : byte
deriving Inhabited, BEq

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.1-16.50 -/
def proj_byte_0 (x : byte) : Nat :=
  match x with
  | byte.mk_byte v_num_0 => (v_num_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:16.8-16.12 -/
inductive wf_byte : byte → Prop where
  | byte_case_0 (i : Nat) :
    (i ≥ 0) ∧ (i ≤ 255) →
    wf_byte (byte.mk_byte i)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 -/
inductive uN : Type where
  | mk_uN (i : Nat) : uN
deriving Inhabited, BEq

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.1-19.25 -/
def proj_uN_0 (x : uN) : Nat :=
  match x with
  | uN.mk_uN v_num_0 => (v_num_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:18.8-18.11 -/
inductive wf_uN : N → uN → Prop where
  | uN_case_0 (v_N : N) (i : Nat) :
    (i ≥ 0) ∧ (i ≤ (Int.toNat (((2 ^ v_N) : Int) - (1 : Int)))) →
    wf_uN v_N (uN.mk_uN i)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 -/
inductive sN : Type where
  | mk_sN (i : Int) : sN
deriving Inhabited, BEq

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.1-21.49 -/
def proj_sN_0 (x : sN) : Int :=
  match x with
  | sN.mk_sN v_num_0 => (v_num_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:20.8-20.11 -/
inductive wf_sN : N → sN → Prop where
  | sN_case_0 (v_N : N) (i : Int) :
    (((i ≥ (- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int))) ∧ (i ≤ (- (1 : Int)))) ∨ (i = (0 : Int))) ∨ ((i ≥ (1 : Int)) ∧ (i ≤ (((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int)))) →
    wf_sN v_N (sN.mk_sN i)


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
def signif (v_N : N) : Option Nat :=
  match v_N with
  | 32 => some 23
  | 64 => some 52
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:44.1-44.34 -/
def expon (v_N : N) : Option Nat :=
  match v_N with
  | 32 => some 8
  | 64 => some 11
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:48.1-48.30 -/
def fun_M (v_N : N) : Nat :=
  Option.get! (signif v_N)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:51.1-51.30 -/
def E (v_N : N) : Nat :=
  Option.get! (expon v_N)

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:58.1-58.30 -/
abbrev exp : Type := Int

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.1-63.84 -/
inductive fNmag : Type where
  | NORM (v_m : m) (v_exp : exp) : fNmag
  | SUBNORM (v_m : m) : fNmag
  | INF : fNmag
  | NAN (v_m : m) : fNmag
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:59.8-59.14 -/
inductive wf_fNmag : N → fNmag → Prop where
  | fNmag_case_0 (v_N : N) (v_m : m) (v_exp : exp) :
    (v_m < (2 ^ (fun_M v_N))) ∧ ((((2 : Int) - ((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int)) ≤ v_exp) ∧ (v_exp ≤ (((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int) - (1 : Int)))) →
    wf_fNmag v_N (fNmag.NORM v_m v_exp)
  | fNmag_case_1 (v_N : N) (v_exp : exp) (v_m : m) :
    (v_m < (2 ^ (fun_M v_N))) ∧ (((2 : Int) - ((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int)) = v_exp) →
    wf_fNmag v_N (fNmag.SUBNORM v_m)
  | fNmag_case_2 (v_N : N) : wf_fNmag v_N fNmag.INF
  | fNmag_case_3 (v_N : N) (v_m : m) :
    (1 ≤ v_m) ∧ (v_m < (2 ^ (fun_M v_N))) →
    wf_fNmag v_N (fNmag.NAN v_m)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.1-56.35 -/
inductive fN : Type where
  | POS (_ : fNmag) : fN
  | NEG (_ : fNmag) : fN
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:54.8-54.11 -/
inductive wf_fN : N → fN → Prop where
  | fN_case_0 (v_N : N) (var_0 : fNmag) :
    wf_fNmag v_N var_0 →
    wf_fN v_N (fN.POS var_0)
  | fN_case_1 (v_N : N) (var_0 : fNmag) :
    wf_fNmag v_N var_0 →
    wf_fN v_N (fN.NEG var_0)


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:65.1-65.20 -/
abbrev f32 : Type := fN

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:66.1-66.20 -/
abbrev f64 : Type := fN

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:68.1-68.39 -/
def fzero (v_N : N) : fN :=
  fN.POS (fNmag.SUBNORM 0)

/- Well-Formedness Theorem at: ../specification/wasm-2.0/1-syntax.spectec:68.6-68.12 -/
theorem fzero_is_wf (v_N : N) (ret_val : fN) :
  ret_val = (fzero v_N) →
  wf_fN v_N ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:71.1-71.39 -/
def fone (v_N : N) : fN :=
  fN.POS (fNmag.NORM 1 (0 : Int))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/1-syntax.spectec:71.6-71.11 -/
theorem fone_is_wf (v_N : N) (ret_val : fN) :
  ret_val = (fone v_N) →
  wf_fN v_N ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:74.1-74.21 -/
def canon_ (v_N : N) : Nat :=
  2 ^ (Int.toNat (((Option.get! (signif v_N)) : Int) - (1 : Int)))

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:80.1-81.8 -/
abbrev vN : Type := iN

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 -/
inductive char : Type where
  | mk_char (i : Nat) : char
deriving Inhabited, BEq

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.1-88.85 -/
def proj_char_0 (x : char) : Nat :=
  match x with
  | char.mk_char v_num_0 => (v_num_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:88.8-88.12 -/
inductive wf_char : char → Prop where
  | char_case_0 (i : Nat) :
    ((i ≥ 0) ∧ (i ≤ 55295)) ∨ ((i ≥ 57344) ∧ (i ≤ 1114111)) →
    wf_char (char.mk_char i)


/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:90.6-90.11 -/
inductive fun_utf8 : List char → List byte → Prop where
  | fun_utf8_case_0 (ch : char) (b : byte) :
    ((proj_char_0 ch) < 128) ∧ ((byte.mk_byte (proj_char_0 ch)) = b) →
    wf_byte (byte.mk_byte (proj_char_0 ch)) →
    fun_utf8 [ch] [b]
  | fun_utf8_case_1 (ch : char) (b_1 : byte) (b_2 : byte) :
    ((128 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 2048)) ∧ ((proj_char_0 ch) = (((2 ^ 6) * (Int.toNat (((proj_byte_0 b_1) : Int) - (192 : Int)))) + (Int.toNat (((proj_byte_0 b_2) : Int) - (128 : Int))))) →
    fun_utf8 [ch] [b_1, b_2]
  | fun_utf8_case_2 (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) :
    (((2048 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 55296)) ∨ ((57344 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 65536))) ∧ ((proj_char_0 ch) = ((((2 ^ 12) * (Int.toNat (((proj_byte_0 b_1) : Int) - (224 : Int)))) + ((2 ^ 6) * (Int.toNat (((proj_byte_0 b_2) : Int) - (128 : Int))))) + (Int.toNat (((proj_byte_0 b_3) : Int) - (128 : Int))))) →
    fun_utf8 [ch] [b_1, b_2, b_3]
  | fun_utf8_case_3 (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) (b_4 : byte) :
    ((65536 ≤ (proj_char_0 ch)) ∧ ((proj_char_0 ch) < 69632)) ∧ ((proj_char_0 ch) = (((((2 ^ 18) * (Int.toNat (((proj_byte_0 b_1) : Int) - (240 : Int)))) + ((2 ^ 12) * (Int.toNat (((proj_byte_0 b_2) : Int) - (128 : Int))))) + ((2 ^ 6) * (Int.toNat (((proj_byte_0 b_3) : Int) - (128 : Int))))) + (Int.toNat (((proj_byte_0 b_4) : Int) - (128 : Int))))) →
    fun_utf8 [ch] [b_1, b_2, b_3, b_4]
  | fun_utf8_case_4 (ch_lst : List char) (var_0_lst : List (List byte)) :
    (List.length var_0_lst) = (List.length ch_lst) →
    Forall₂ (fun (var_0_elem : List byte) (ch_elem : char) => fun_utf8 [ch_elem] var_0_elem) var_0_lst ch_lst →
    fun_utf8 ch_lst (concat_ byte var_0_lst)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/1-syntax.spectec:90.6-90.11 -/
theorem utf8_is_wf (var_0_lst : List char) (ret_val_lst : List byte) (var_0 : List byte) :
  fun_utf8 var_0_lst var_0 →
  Forall (fun (var_0_elem : char) => wf_char var_0_elem) var_0_lst →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 -/
inductive name : Type where
  | mk_name (char_lst : List char) : name
deriving Inhabited, BEq

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.1-92.70 -/
def proj_name_0 (x : name) : List char :=
  match x with
  | name.mk_name v_char_list_0 => (v_char_list_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:92.8-92.12 -/
inductive wf_name : name → Prop where
  | name_case_0 (char_lst : List char) (var_0 : List byte) :
    fun_utf8 char_lst var_0 →
    Forall (fun (v_char_elem : char) => wf_char v_char_elem) char_lst →
    (List.length var_0) < (2 ^ 32) →
    wf_name (name.mk_name char_lst)


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
def valtype_numtype (var_0 : numtype) : valtype :=
  match var_0 with
  | numtype.I32 => valtype.I32
  | numtype.I64 => valtype.I64
  | numtype.F32 => valtype.F32
  | numtype.F64 => valtype.F64

/- Auxiliary Definition at:  -/
def valtype_reftype (var_0 : reftype) : valtype :=
  match var_0 with
  | reftype.FUNCREF => valtype.FUNCREF
  | reftype.EXTERNREF => valtype.EXTERNREF

/- Auxiliary Definition at:  -/
def valtype_vectype (var_0 : vectype) : valtype :=
  match var_0 with
  | vectype.V128 => valtype.V128

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:141.1-141.38 -/
inductive Inn : Type where
  | I32 : Inn
  | I64 : Inn
deriving Inhabited, BEq

/- Auxiliary Definition at:  -/
def numtype_Inn (var_0 : Inn) : numtype :=
  match var_0 with
  | Inn.I32 => numtype.I32
  | Inn.I64 => numtype.I64

/- Auxiliary Definition at:  -/
def valtype_Inn (var_0 : Inn) : valtype :=
  match var_0 with
  | Inn.I32 => valtype.I32
  | Inn.I64 => valtype.I64

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:142.1-142.38 -/
inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq

/- Auxiliary Definition at:  -/
def numtype_Fnn (var_0 : Fnn) : numtype :=
  match var_0 with
  | Fnn.F32 => numtype.F32
  | Fnn.F64 => numtype.F64

/- Auxiliary Definition at:  -/
def valtype_Fnn (var_0 : Fnn) : valtype :=
  match var_0 with
  | Fnn.F32 => valtype.F32
  | Fnn.F64 => valtype.F64

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:143.1-143.36 -/
abbrev Vnn : Type := vectype

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:146.1-147.16 -/
abbrev resulttype : Type := list valtype

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
def lanetype_Fnn (var_0 : Fnn) : lanetype :=
  match var_0 with
  | Fnn.F32 => lanetype.F32
  | Fnn.F64 => lanetype.F64

/- Auxiliary Definition at:  -/
def lanetype_Inn (var_0 : Inn) : lanetype :=
  match var_0 with
  | Inn.I32 => lanetype.I32
  | Inn.I64 => lanetype.I64

/- Auxiliary Definition at:  -/
def lanetype_numtype (var_0 : numtype) : lanetype :=
  match var_0 with
  | numtype.I32 => lanetype.I32
  | numtype.I64 => lanetype.I64
  | numtype.F32 => lanetype.F32
  | numtype.F64 => lanetype.F64

/- Auxiliary Definition at:  -/
def lanetype_packtype (var_0 : packtype) : lanetype :=
  match var_0 with
  | packtype.I8 => lanetype.I8
  | packtype.I16 => lanetype.I16

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
def lanetype_Jnn (var_0 : Jnn) : lanetype :=
  match var_0 with
  | Jnn.I32 => lanetype.I32
  | Jnn.I64 => lanetype.I64
  | Jnn.I8 => lanetype.I8
  | Jnn.I16 => lanetype.I16

/- Auxiliary Definition at:  -/
def Jnn_packtype (var_0 : packtype) : Jnn :=
  match var_0 with
  | packtype.I8 => Jnn.I8
  | packtype.I16 => Jnn.I16

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:157.1-157.37 -/
abbrev Lnn : Type := lanetype

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:162.1-162.18 -/
abbrev «mut» : Type := Option r_MUT

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.1-165.17 -/
inductive limits : Type where
  | mk_limits (v_u32 : u32) (u32_opt : Option u32) : limits
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:164.8-164.14 -/
inductive wf_limits : limits → Prop where
  | limits_case_0 (v_u32 : u32) (u32_opt : Option u32) :
    wf_uN 32 v_u32 →
    Forall (fun (v_u32_elem : u32) => wf_uN 32 v_u32_elem) (Option.toList u32_opt) →
    wf_limits (limits.mk_limits v_u32 u32_opt)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:167.1-168.14 -/
inductive globaltype : Type where
  | mk_globaltype (v_mut : «mut») (v_valtype : valtype) : globaltype
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:169.1-170.27 -/
inductive functype : Type where
  | mk_functype (v_resulttype_0 : resulttype) (v_resulttype_1 : resulttype) : functype
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.1-172.17 -/
inductive tabletype : Type where
  | mk_tabletype (v_limits : limits) (v_reftype : reftype) : tabletype
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:171.8-171.17 -/
inductive wf_tabletype : tabletype → Prop where
  | tabletype_case_0 (v_limits : limits) (v_reftype : reftype) :
    wf_limits v_limits →
    wf_tabletype (tabletype.mk_tabletype v_limits v_reftype)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.1-174.14 -/
inductive memtype : Type where
  | PAGE (v_limits : limits) : memtype
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:173.8-173.15 -/
inductive wf_memtype : memtype → Prop where
  | memtype_case_0 (v_limits : limits) :
    wf_limits v_limits →
    wf_memtype (memtype.PAGE v_limits)


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
inductive wf_externtype : externtype → Prop where
  | externtype_case_0 (v_functype : functype) : wf_externtype (externtype.FUNC v_functype)
  | externtype_case_1 (v_globaltype : globaltype) : wf_externtype (externtype.GLOBAL v_globaltype)
  | externtype_case_2 (v_tabletype : tabletype) :
    wf_tabletype v_tabletype →
    wf_externtype (externtype.TABLE v_tabletype)
  | externtype_case_3 (v_memtype : memtype) :
    wf_memtype v_memtype →
    wf_externtype (externtype.MEM v_memtype)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:323.1-323.60 -/
inductive dim : Type where
  | mk_dim (i : Nat) : dim
deriving Inhabited, BEq

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:323.1-323.60 -/
def proj_dim_0 (x : dim) : Nat :=
  match x with
  | dim.mk_dim v_num_0 => (v_num_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:323.8-323.11 -/
inductive wf_dim : dim → Prop where
  | dim_case_0 (i : Nat) :
    ((((i = 1) ∨ (i = 2)) ∨ (i = 4)) ∨ (i = 8)) ∨ (i = 16) →
    wf_dim (dim.mk_dim i)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.1-324.69 -/
inductive shape : Type where
  | X (v_lanetype : lanetype) (v_dim : dim) : shape
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:324.8-324.13 -/
inductive wf_shape : shape → Prop where
  | shape_case_0 (v_lanetype : lanetype) (v_dim : dim) :
    wf_dim v_dim →
    wf_shape (shape.X v_lanetype v_dim)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:206.1-206.32 -/
def fun_lanetype (v_shape : shape) : lanetype :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => v_Lnn

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:208.1-208.59 -/
def size (v_valtype : valtype) : Option Nat :=
  match v_valtype with
  | valtype.I32 => some 32
  | valtype.I64 => some 64
  | valtype.F32 => some 32
  | valtype.F64 => some 64
  | valtype.V128 => some 128
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:209.1-209.45 -/
def psize (v_packtype : packtype) : Nat :=
  match v_packtype with
  | packtype.I8 => 8
  | packtype.I16 => 16

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:210.1-210.45 -/
def lsize (v_lanetype : lanetype) : Nat :=
  match v_lanetype with
  | lanetype.I32 => Option.get! (size (valtype_numtype numtype.I32))
  | lanetype.I64 => Option.get! (size (valtype_numtype numtype.I64))
  | lanetype.F32 => Option.get! (size (valtype_numtype numtype.F32))
  | lanetype.F64 => Option.get! (size (valtype_numtype numtype.F64))
  | lanetype.I8 => psize packtype.I8
  | lanetype.I16 => psize packtype.I16

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:211.1-211.70 -/
def isize (v_Inn : Inn) : Nat :=
  Option.get! (size (valtype_Inn v_Inn))

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:212.1-212.70 -/
def jsize (v_Jnn : Jnn) : Nat :=
  lsize (lanetype_Jnn v_Jnn)

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:213.1-213.70 -/
def fsize (v_Fnn : Fnn) : Nat :=
  Option.get! (size (valtype_Fnn v_Fnn))

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:231.1-231.63 -/
def sizenn (v_numtype : numtype) : Nat :=
  Option.get! (size (valtype_numtype v_numtype))

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:232.1-232.63 -/
def sizenn1 (v_numtype : numtype) : Nat :=
  Option.get! (size (valtype_numtype v_numtype))

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:233.1-233.63 -/
def sizenn2 (v_numtype : numtype) : Nat :=
  Option.get! (size (valtype_numtype v_numtype))

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:238.1-238.63 -/
def lsizenn (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:239.1-239.63 -/
def lsizenn1 (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:240.1-240.63 -/
def lsizenn2 (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:245.1-245.40 -/
def inv_isize (nat : Nat) : Option Inn :=
  match nat with
  | 32 => some Inn.I32
  | 64 => some Inn.I64
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:246.1-246.40 -/
def inv_jsize (nat : Nat) : Option Jnn :=
  match nat with
  | 8 => some Jnn.I8
  | 16 => some Jnn.I16
  | 32 => some Jnn.I32
  | 64 => some Jnn.I64
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:247.1-247.40 -/
def inv_fsize (nat : Nat) : Option Fnn :=
  match nat with
  | 32 => some Fnn.F32
  | 64 => some Fnn.F64
  | _ => none

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 -/
inductive num_ : Type where
  | mk_num__0 (v_Inn : Inn) (var_x : iN) : num_
  | mk_num__1 (v_Fnn : Fnn) (var_x : fN) : num_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.8-259.13 -/
inductive wf_num_ : numtype → num_ → Prop where
  | num__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : iN) :
    (size (valtype_Inn v_Inn)) ≠ none →
    wf_uN (Option.get! (size (valtype_Inn v_Inn))) var_x →
    v_numtype = (numtype_Inn v_Inn) →
    wf_num_ v_numtype (num_.mk_num__0 v_Inn var_x)
  | num__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : fN) :
    wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x →
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_num_ v_numtype (num_.mk_num__1 v_Fnn var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 -/
def proj_num__0 (var_x : num_) : Option iN :=
  match var_x with
  | num_.mk_num__0 v_Inn var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:259.1-259.21 -/
def proj_num__1 (var_x : num_) : Option fN :=
  match var_x with
  | num_.mk_num__1 v_Fnn var_x => some var_x
  | _ => none

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:263.1-263.36 -/
abbrev pack_ : Type := iN

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -/
inductive lane_ : Type where
  | mk_lane__0 (v_numtype : numtype) (var_x : num_) : lane_
  | mk_lane__1 (v_packtype : packtype) (var_x : pack_) : lane_
  | mk_lane__2 (v_Jnn : Jnn) (var_x : iN) : lane_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.8-265.14 -/
inductive wf_lane_ : lanetype → lane_ → Prop where
  | lane__case_0 (v_lanetype : lanetype) (v_numtype : numtype) (var_x : num_) :
    wf_num_ v_numtype var_x →
    v_lanetype = (lanetype_numtype v_numtype) →
    wf_lane_ v_lanetype (lane_.mk_lane__0 v_numtype var_x)
  | lane__case_1 (v_lanetype : lanetype) (v_packtype : packtype) (var_x : pack_) :
    wf_uN (psize v_packtype) var_x →
    v_lanetype = (lanetype_packtype v_packtype) →
    wf_lane_ v_lanetype (lane_.mk_lane__1 v_packtype var_x)
  | lane__case_2 (v_lanetype : lanetype) (v_Jnn : Jnn) (var_x : iN) :
    wf_uN (lsize (lanetype_Jnn v_Jnn)) var_x →
    v_lanetype = (lanetype_Jnn v_Jnn) →
    wf_lane_ v_lanetype (lane_.mk_lane__2 v_Jnn var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -/
def proj_lane__0 (var_x : lane_) : Option num_ :=
  match var_x with
  | lane_.mk_lane__0 v_numtype var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -/
def proj_lane__1 (var_x : lane_) : Option pack_ :=
  match var_x with
  | lane_.mk_lane__1 v_packtype var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:265.1-265.23 -/
def proj_lane__2 (var_x : lane_) : Option iN :=
  match var_x with
  | lane_.mk_lane__2 v_Jnn var_x => some var_x
  | _ => none

/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:270.1-270.34 -/
abbrev vec_ : Type := vN

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:272.1-272.35 -/
def fun_zero (v_numtype : numtype) : num_ :=
  match v_numtype with
  | numtype.I32 => num_.mk_num__0 Inn.I32 (uN.mk_uN 0)
  | numtype.I64 => num_.mk_num__0 Inn.I64 (uN.mk_uN 0)
  | numtype.F32 => num_.mk_num__1 Fnn.F32 (fzero (Option.get! (size (valtype_Fnn Fnn.F32))))
  | numtype.F64 => num_.mk_num__1 Fnn.F64 (fzero (Option.get! (size (valtype_Fnn Fnn.F64))))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/1-syntax.spectec:272.6-272.11 -/
theorem zero_is_wf (v_numtype : numtype) (ret_val : num_) :
  ret_val = (fun_zero v_numtype) →
  wf_num_ v_numtype ret_val :=
  sorry

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
def proj_sz_0 (x : sz) : Nat :=
  match x with
  | sz.mk_sz v_num_0 => (v_num_0)

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:280.8-280.10 -/
inductive wf_sz : sz → Prop where
  | sz_case_0 (i : Nat) :
    (((i = 8) ∨ (i = 16)) ∨ (i = 32)) ∨ (i = 64) →
    wf_sz (sz.mk_sz i)


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
inductive wf_unop_ : numtype → unop_ → Prop where
  | unop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : unop_Inn) :
    v_numtype = (numtype_Inn v_Inn) →
    wf_unop_ v_numtype (unop_.mk_unop__0 v_Inn var_x)
  | unop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : unop_Fnn) :
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_unop_ v_numtype (unop_.mk_unop__1 v_Fnn var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 -/
def proj_unop__0 (var_x : unop_) : Option unop_Inn :=
  match var_x with
  | unop_.mk_unop__0 v_Inn var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:282.1-282.22 -/
def proj_unop__1 (var_x : unop_) : Option unop_Fnn :=
  match var_x with
  | unop_.mk_unop__1 v_Fnn var_x => some var_x
  | _ => none

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
inductive wf_binop_ : numtype → binop_ → Prop where
  | binop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : binop_Inn) :
    v_numtype = (numtype_Inn v_Inn) →
    wf_binop_ v_numtype (binop_.mk_binop__0 v_Inn var_x)
  | binop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : binop_Fnn) :
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_binop_ v_numtype (binop_.mk_binop__1 v_Fnn var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 -/
def proj_binop__0 (var_x : binop_) : Option binop_Inn :=
  match var_x with
  | binop_.mk_binop__0 v_Inn var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:286.1-286.23 -/
def proj_binop__1 (var_x : binop_) : Option binop_Fnn :=
  match var_x with
  | binop_.mk_binop__1 v_Fnn var_x => some var_x
  | _ => none

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 -/
inductive testop_Inn : Type where
  | EQZ : testop_Inn
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 -/
inductive testop_ : Type where
  | mk_testop__0 (v_Inn : Inn) (var_x : testop_Inn) : testop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.8-293.16 -/
inductive wf_testop_ : numtype → testop_ → Prop where
  | testop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : testop_Inn) :
    v_numtype = (numtype_Inn v_Inn) →
    wf_testop_ v_numtype (testop_.mk_testop__0 v_Inn var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:293.1-293.24 -/
def proj_testop__0 (var_x : testop_) : testop_Inn :=
  match var_x with
  | testop_.mk_testop__0 v_Inn var_x => var_x

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
inductive wf_relop_ : numtype → relop_ → Prop where
  | relop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : relop_Inn) :
    v_numtype = (numtype_Inn v_Inn) →
    wf_relop_ v_numtype (relop_.mk_relop__0 v_Inn var_x)
  | relop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : relop_Fnn) :
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_relop_ v_numtype (relop_.mk_relop__1 v_Fnn var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 -/
def proj_relop__0 (var_x : relop_) : Option relop_Inn :=
  match var_x with
  | relop_.mk_relop__0 v_Inn var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:297.1-297.23 -/
def proj_relop__1 (var_x : relop_) : Option relop_Fnn :=
  match var_x with
  | relop_.mk_relop__1 v_Fnn var_x => some var_x
  | _ => none

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
inductive cvtop__Inn_1_Inn_2 : Type where
  | EXTEND (v_sx : sx) : cvtop__Inn_1_Inn_2
  | WRAP : cvtop__Inn_1_Inn_2
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 -/
inductive wf_cvtop__Inn_1_Inn_2 : Inn → Inn → cvtop__Inn_1_Inn_2 → Prop where
  | cvtop__Inn_1_Inn_2_case_0 (Inn_1 : Inn) (Inn_2 : Inn) (v_sx : sx) :
    (sizenn1 (numtype_Inn Inn_1)) < (sizenn2 (numtype_Inn Inn_2)) →
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 (cvtop__Inn_1_Inn_2.EXTEND v_sx)
  | cvtop__Inn_1_Inn_2_case_1 (Inn_1 : Inn) (Inn_2 : Inn) :
    (sizenn1 (numtype_Inn Inn_1)) > (sizenn2 (numtype_Inn Inn_2)) →
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 cvtop__Inn_1_Inn_2.WRAP


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
inductive cvtop__Inn_1_Fnn_2 : Type where
  | CONVERT (v_sx : sx) : cvtop__Inn_1_Fnn_2
  | REINTERPRET : cvtop__Inn_1_Fnn_2
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 -/
inductive wf_cvtop__Inn_1_Fnn_2 : Inn → Fnn → cvtop__Inn_1_Fnn_2 → Prop where
  | cvtop__Inn_1_Fnn_2_case_0 (Inn_1 : Inn) (Fnn_2 : Fnn) (v_sx : sx) : wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)
  | cvtop__Inn_1_Fnn_2_case_1 (Inn_1 : Inn) (Fnn_2 : Fnn) :
    (sizenn1 (numtype_Inn Inn_1)) = (sizenn2 (numtype_Fnn Fnn_2)) →
    wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 cvtop__Inn_1_Fnn_2.REINTERPRET


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
inductive cvtop__Fnn_1_Inn_2 : Type where
  | TRUNC (v_sx : sx) : cvtop__Fnn_1_Inn_2
  | TRUNC_SAT (v_sx : sx) : cvtop__Fnn_1_Inn_2
  | REINTERPRET : cvtop__Fnn_1_Inn_2
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 -/
inductive wf_cvtop__Fnn_1_Inn_2 : Fnn → Inn → cvtop__Fnn_1_Inn_2 → Prop where
  | cvtop__Fnn_1_Inn_2_case_0 (Fnn_1 : Fnn) (Inn_2 : Inn) (v_sx : sx) : wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)
  | cvtop__Fnn_1_Inn_2_case_1 (Fnn_1 : Fnn) (Inn_2 : Inn) (v_sx : sx) : wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)
  | cvtop__Fnn_1_Inn_2_case_2 (Fnn_1 : Fnn) (Inn_2 : Inn) :
    (sizenn1 (numtype_Fnn Fnn_1)) = (sizenn2 (numtype_Inn Inn_2)) →
    wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 cvtop__Fnn_1_Inn_2.REINTERPRET


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
inductive cvtop__Fnn_1_Fnn_2 : Type where
  | PROMOTE : cvtop__Fnn_1_Fnn_2
  | DEMOTE : cvtop__Fnn_1_Fnn_2
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 -/
inductive wf_cvtop__Fnn_1_Fnn_2 : Fnn → Fnn → cvtop__Fnn_1_Fnn_2 → Prop where
  | cvtop__Fnn_1_Fnn_2_case_0 (Fnn_1 : Fnn) (Fnn_2 : Fnn) :
    (sizenn1 (numtype_Fnn Fnn_1)) < (sizenn2 (numtype_Fnn Fnn_2)) →
    wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 cvtop__Fnn_1_Fnn_2.PROMOTE
  | cvtop__Fnn_1_Fnn_2_case_1 (Fnn_1 : Fnn) (Fnn_2 : Fnn) :
    (sizenn1 (numtype_Fnn Fnn_1)) > (sizenn2 (numtype_Fnn Fnn_2)) →
    wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 cvtop__Fnn_1_Fnn_2.DEMOTE


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
inductive cvtop__ : Type where
  | mk_cvtop___0 (Inn_1 : Inn) (Inn_2 : Inn) (var_x : cvtop__Inn_1_Inn_2) : cvtop__
  | mk_cvtop___1 (Inn_1 : Inn) (Fnn_2 : Fnn) (var_x : cvtop__Inn_1_Fnn_2) : cvtop__
  | mk_cvtop___2 (Fnn_1 : Fnn) (Inn_2 : Inn) (var_x : cvtop__Fnn_1_Inn_2) : cvtop__
  | mk_cvtop___3 (Fnn_1 : Fnn) (Fnn_2 : Fnn) (var_x : cvtop__Fnn_1_Fnn_2) : cvtop__
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.8-305.16 -/
inductive wf_cvtop__ : numtype → numtype → cvtop__ → Prop where
  | cvtop___case_0 (numtype_1 : numtype) (numtype_2 : numtype) (Inn_1 : Inn) (Inn_2 : Inn) (var_x : cvtop__Inn_1_Inn_2) :
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 var_x →
    numtype_1 = (numtype_Inn Inn_1) →
    numtype_2 = (numtype_Inn Inn_2) →
    wf_cvtop__ numtype_1 numtype_2 (cvtop__.mk_cvtop___0 Inn_1 Inn_2 var_x)
  | cvtop___case_1 (numtype_1 : numtype) (numtype_2 : numtype) (Inn_1 : Inn) (Fnn_2 : Fnn) (var_x : cvtop__Inn_1_Fnn_2) :
    wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 var_x →
    numtype_1 = (numtype_Inn Inn_1) →
    numtype_2 = (numtype_Fnn Fnn_2) →
    wf_cvtop__ numtype_1 numtype_2 (cvtop__.mk_cvtop___1 Inn_1 Fnn_2 var_x)
  | cvtop___case_2 (numtype_1 : numtype) (numtype_2 : numtype) (Fnn_1 : Fnn) (Inn_2 : Inn) (var_x : cvtop__Fnn_1_Inn_2) :
    wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 var_x →
    numtype_1 = (numtype_Fnn Fnn_1) →
    numtype_2 = (numtype_Inn Inn_2) →
    wf_cvtop__ numtype_1 numtype_2 (cvtop__.mk_cvtop___2 Fnn_1 Inn_2 var_x)
  | cvtop___case_3 (numtype_1 : numtype) (numtype_2 : numtype) (Fnn_1 : Fnn) (Fnn_2 : Fnn) (var_x : cvtop__Fnn_1_Fnn_2) :
    wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 var_x →
    numtype_1 = (numtype_Fnn Fnn_1) →
    numtype_2 = (numtype_Fnn Fnn_2) →
    wf_cvtop__ numtype_1 numtype_2 (cvtop__.mk_cvtop___3 Fnn_1 Fnn_2 var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
def proj_cvtop___0 (var_x : cvtop__) : Option cvtop__Inn_1_Inn_2 :=
  match var_x with
  | cvtop__.mk_cvtop___0 Inn_1 Inn_2 var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
def proj_cvtop___1 (var_x : cvtop__) : Option cvtop__Inn_1_Fnn_2 :=
  match var_x with
  | cvtop__.mk_cvtop___1 Inn_1 Fnn_2 var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
def proj_cvtop___2 (var_x : cvtop__) : Option cvtop__Fnn_1_Inn_2 :=
  match var_x with
  | cvtop__.mk_cvtop___2 Fnn_1 Inn_2 var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:305.1-305.37 -/
def proj_cvtop___3 (var_x : cvtop__) : Option cvtop__Fnn_1_Fnn_2 :=
  match var_x with
  | cvtop__.mk_cvtop___3 Fnn_1 Fnn_2 var_x => some var_x
  | _ => none

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.1-325.69 -/
inductive ishape : Type where
  | X (v_Jnn : Jnn) (v_dim : dim) : ishape
deriving Inhabited, BEq

/- Auxiliary Definition at:  -/
def shape_ishape (var_0 : ishape) : shape :=
  match var_0 with
  | ishape.X x0 x1 => shape.X (lanetype_Jnn x0) x1

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:325.8-325.14 -/
inductive wf_ishape : ishape → Prop where
  | ishape_case_0 (v_Jnn : Jnn) (v_dim : dim) :
    wf_dim v_dim →
    wf_ishape (ishape.X v_Jnn v_dim)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:326.1-326.69 -/
inductive fshape : Type where
  | X (v_Fnn : Fnn) (v_dim : dim) : fshape
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:326.8-326.14 -/
inductive wf_fshape : fshape → Prop where
  | fshape_case_0 (v_Fnn : Fnn) (v_dim : dim) :
    wf_dim v_dim →
    wf_fshape (fshape.X v_Fnn v_dim)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:327.1-327.69 -/
inductive pshape : Type where
  | X (v_Pnn : Pnn) (v_dim : dim) : pshape
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:327.8-327.14 -/
inductive wf_pshape : pshape → Prop where
  | pshape_case_0 (v_Pnn : Pnn) (v_dim : dim) :
    wf_dim v_dim →
    wf_pshape (pshape.X v_Pnn v_dim)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:329.1-329.22 -/
def fun_dim (v_shape : shape) : dim :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => dim.mk_dim v_N

/- Well-Formedness Theorem at: ../specification/wasm-2.0/1-syntax.spectec:329.6-329.10 -/
theorem dim_is_wf (v_shape : shape) (ret_val : dim) :
  wf_shape v_shape →
  ret_val = (fun_dim v_shape) →
  wf_dim ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:330.1-330.41 -/
def shsize (v_shape : shape) : Nat :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => (lsize v_Lnn) * v_N

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:332.1-332.20 -/
inductive vvunop : Type where
  | NOT : vvunop
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:333.1-333.41 -/
inductive vvbinop : Type where
  | AND : vvbinop
  | ANDNOT : vvbinop
  | OR : vvbinop
  | XOR : vvbinop
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:334.1-334.28 -/
inductive vvternop : Type where
  | BITSELECT : vvternop
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:335.1-335.27 -/
inductive vvtestop : Type where
  | ANY_TRUE : vvtestop
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 -/
inductive vunop_Jnn_N : Type where
  | ABS : vunop_Jnn_N
  | NEG : vunop_Jnn_N
  | POPCNT : vunop_Jnn_N
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.15 -/
inductive wf_vunop_Jnn_N : Jnn → N → vunop_Jnn_N → Prop where
  | vunop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) : wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N.ABS
  | vunop_Jnn_N_case_1 (v_Jnn : Jnn) (v_N : N) : wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N.NEG
  | vunop_Jnn_N_case_2 (v_Jnn : Jnn) (v_N : N) :
    v_Jnn = Jnn.I8 →
    wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N.POPCNT


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 -/
inductive vunop_Fnn_N : Type where
  | ABS : vunop_Fnn_N
  | NEG : vunop_Fnn_N
  | SQRT : vunop_Fnn_N
  | CEIL : vunop_Fnn_N
  | FLOOR : vunop_Fnn_N
  | TRUNC : vunop_Fnn_N
  | NEAREST : vunop_Fnn_N
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 -/
inductive vunop_ : Type where
  | mk_vunop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vunop_Jnn_N) : vunop_
  | mk_vunop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vunop_Fnn_N) : vunop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.8-337.15 -/
inductive wf_vunop_ : shape → vunop_ → Prop where
  | vunop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vunop_Jnn_N) :
    wf_vunop_Jnn_N v_Jnn v_N var_x →
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_vunop_ v_shape (vunop_.mk_vunop__0 v_Jnn v_N var_x)
  | vunop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vunop_Fnn_N) :
    v_shape = (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_N)) →
    wf_vunop_ v_shape (vunop_.mk_vunop__1 v_Fnn v_N var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 -/
def proj_vunop__0 (var_x : vunop_) : Option vunop_Jnn_N :=
  match var_x with
  | vunop_.mk_vunop__0 v_Jnn v_N var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:337.1-337.21 -/
def proj_vunop__1 (var_x : vunop_) : Option vunop_Fnn_N :=
  match var_x with
  | vunop_.mk_vunop__1 v_Fnn v_N var_x => some var_x
  | _ => none

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 -/
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

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.8-342.16 -/
inductive wf_vbinop_Jnn_N : Jnn → N → vbinop_Jnn_N → Prop where
  | vbinop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) : wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.ADD
  | vbinop_Jnn_N_case_1 (v_Jnn : Jnn) (v_N : N) : wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.SUB
  | vbinop_Jnn_N_case_2 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N.ADD_SAT v_sx)
  | vbinop_Jnn_N_case_3 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N.SUB_SAT v_sx)
  | vbinop_Jnn_N_case_4 (v_Jnn : Jnn) (v_N : N) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≥ 16 →
    wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.MUL
  | vbinop_Jnn_N_case_5 (v_Jnn : Jnn) (v_N : N) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.AVGRU
  | vbinop_Jnn_N_case_6 (v_Jnn : Jnn) (v_N : N) :
    (lsizenn (lanetype_Jnn v_Jnn)) = 16 →
    wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.Q15MULR_SATS
  | vbinop_Jnn_N_case_7 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 32 →
    wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N.MIN v_sx)
  | vbinop_Jnn_N_case_8 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 32 →
    wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N.MAX v_sx)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 -/
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

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 -/
inductive vbinop_ : Type where
  | mk_vbinop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vbinop_Jnn_N) : vbinop_
  | mk_vbinop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vbinop_Fnn_N) : vbinop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.8-342.16 -/
inductive wf_vbinop_ : shape → vbinop_ → Prop where
  | vbinop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vbinop_Jnn_N) :
    wf_vbinop_Jnn_N v_Jnn v_N var_x →
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_vbinop_ v_shape (vbinop_.mk_vbinop__0 v_Jnn v_N var_x)
  | vbinop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vbinop_Fnn_N) :
    v_shape = (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_N)) →
    wf_vbinop_ v_shape (vbinop_.mk_vbinop__1 v_Fnn v_N var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 -/
def proj_vbinop__0 (var_x : vbinop_) : Option vbinop_Jnn_N :=
  match var_x with
  | vbinop_.mk_vbinop__0 v_Jnn v_N var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:342.1-342.22 -/
def proj_vbinop__1 (var_x : vbinop_) : Option vbinop_Fnn_N :=
  match var_x with
  | vbinop_.mk_vbinop__1 v_Fnn v_N var_x => some var_x
  | _ => none

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:355.1-355.23 -/
inductive vtestop_Jnn_N : Type where
  | ALL_TRUE : vtestop_Jnn_N
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:355.1-355.23 -/
inductive vtestop_ : Type where
  | mk_vtestop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vtestop_Jnn_N) : vtestop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:355.8-355.17 -/
inductive wf_vtestop_ : shape → vtestop_ → Prop where
  | vtestop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vtestop_Jnn_N) :
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_vtestop_ v_shape (vtestop_.mk_vtestop__0 v_Jnn v_N var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:355.1-355.23 -/
def proj_vtestop__0 (var_x : vtestop_) : vtestop_Jnn_N :=
  match var_x with
  | vtestop_.mk_vtestop__0 v_Jnn v_N var_x => var_x

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 -/
inductive vrelop_Jnn_N : Type where
  | EQ : vrelop_Jnn_N
  | NE : vrelop_Jnn_N
  | LT (v_sx : sx) : vrelop_Jnn_N
  | GT (v_sx : sx) : vrelop_Jnn_N
  | LE (v_sx : sx) : vrelop_Jnn_N
  | GE (v_sx : sx) : vrelop_Jnn_N
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.8-359.16 -/
inductive wf_vrelop_Jnn_N : Jnn → N → vrelop_Jnn_N → Prop where
  | vrelop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) : wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N.EQ
  | vrelop_Jnn_N_case_1 (v_Jnn : Jnn) (v_N : N) : wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N.NE
  | vrelop_Jnn_N_case_2 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    ((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = sx.S) →
    wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N.LT v_sx)
  | vrelop_Jnn_N_case_3 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    ((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = sx.S) →
    wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N.GT v_sx)
  | vrelop_Jnn_N_case_4 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    ((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = sx.S) →
    wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N.LE v_sx)
  | vrelop_Jnn_N_case_5 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    ((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = sx.S) →
    wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N.GE v_sx)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 -/
inductive vrelop_Fnn_N : Type where
  | EQ : vrelop_Fnn_N
  | NE : vrelop_Fnn_N
  | LT : vrelop_Fnn_N
  | GT : vrelop_Fnn_N
  | LE : vrelop_Fnn_N
  | GE : vrelop_Fnn_N
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 -/
inductive vrelop_ : Type where
  | mk_vrelop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vrelop_Jnn_N) : vrelop_
  | mk_vrelop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vrelop_Fnn_N) : vrelop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.8-359.16 -/
inductive wf_vrelop_ : shape → vrelop_ → Prop where
  | vrelop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vrelop_Jnn_N) :
    wf_vrelop_Jnn_N v_Jnn v_N var_x →
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_vrelop_ v_shape (vrelop_.mk_vrelop__0 v_Jnn v_N var_x)
  | vrelop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vrelop_Fnn_N) :
    v_shape = (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_N)) →
    wf_vrelop_ v_shape (vrelop_.mk_vrelop__1 v_Fnn v_N var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 -/
def proj_vrelop__0 (var_x : vrelop_) : Option vrelop_Jnn_N :=
  match var_x with
  | vrelop_.mk_vrelop__0 v_Jnn v_N var_x => some var_x
  | _ => none

/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:359.1-359.22 -/
def proj_vrelop__1 (var_x : vrelop_) : Option vrelop_Fnn_N :=
  match var_x with
  | vrelop_.mk_vrelop__1 v_Fnn v_N var_x => some var_x
  | _ => none

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:367.1-367.48 -/
inductive half : Type where
  | LOW : half
  | HIGH : half
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:368.1-368.19 -/
inductive zero : Type where
  | ZERO : zero
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:370.1-370.99 -/
inductive vcvtop : Type where
  | EXTEND (v_half : half) (v_sx : sx) : vcvtop
  | TRUNC_SAT (v_sx : sx) (zero_opt : Option zero) : vcvtop
  | CONVERT (half_opt : Option half) (v_sx : sx) : vcvtop
  | DEMOTE (v_zero : zero) : vcvtop
  | PROMOTELOW : vcvtop
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:372.1-372.25 -/
inductive vshiftop_Jnn_N : Type where
  | SHL : vshiftop_Jnn_N
  | SHR (v_sx : sx) : vshiftop_Jnn_N
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:372.1-372.25 -/
inductive vshiftop_ : Type where
  | mk_vshiftop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vshiftop_Jnn_N) : vshiftop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:372.8-372.18 -/
inductive wf_vshiftop_ : ishape → vshiftop_ → Prop where
  | vshiftop__case_0 (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vshiftop_Jnn_N) :
    v_ishape = (ishape.X v_Jnn (dim.mk_dim v_N)) →
    wf_vshiftop_ v_ishape (vshiftop_.mk_vshiftop__0 v_Jnn v_N var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:372.1-372.25 -/
def proj_vshiftop__0 (var_x : vshiftop_) : vshiftop_Jnn_N :=
  match var_x with
  | vshiftop_.mk_vshiftop__0 v_Jnn v_N var_x => var_x

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.1-375.25 -/
inductive vextunop_Jnn_N : Type where
  | EXTADD_PAIRWISE (v_sx : sx) : vextunop_Jnn_N
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.8-375.18 -/
inductive wf_vextunop_Jnn_N : Jnn → N → vextunop_Jnn_N → Prop where
  | vextunop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) :
    (16 ≤ (lsizenn (lanetype_Jnn v_Jnn))) ∧ ((lsizenn (lanetype_Jnn v_Jnn)) ≤ 32) →
    wf_vextunop_Jnn_N v_Jnn v_N (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.1-375.25 -/
inductive vextunop_ : Type where
  | mk_vextunop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vextunop_Jnn_N) : vextunop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.8-375.18 -/
inductive wf_vextunop_ : ishape → vextunop_ → Prop where
  | vextunop__case_0 (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vextunop_Jnn_N) :
    wf_vextunop_Jnn_N v_Jnn v_N var_x →
    v_ishape = (ishape.X v_Jnn (dim.mk_dim v_N)) →
    wf_vextunop_ v_ishape (vextunop_.mk_vextunop__0 v_Jnn v_N var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:375.1-375.25 -/
def proj_vextunop__0 (var_x : vextunop_) : vextunop_Jnn_N :=
  match var_x with
  | vextunop_.mk_vextunop__0 v_Jnn v_N var_x => var_x

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.1-378.26 -/
inductive vextbinop_Jnn_N : Type where
  | EXTMUL (v_half : half) (v_sx : sx) : vextbinop_Jnn_N
  | DOTS : vextbinop_Jnn_N
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.8-378.19 -/
inductive wf_vextbinop_Jnn_N : Jnn → N → vextbinop_Jnn_N → Prop where
  | vextbinop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) (v_half : half) (v_sx : sx) : wf_vextbinop_Jnn_N v_Jnn v_N (vextbinop_Jnn_N.EXTMUL v_half v_sx)
  | vextbinop_Jnn_N_case_1 (v_Jnn : Jnn) (v_N : N) :
    (lsizenn (lanetype_Jnn v_Jnn)) = 32 →
    wf_vextbinop_Jnn_N v_Jnn v_N vextbinop_Jnn_N.DOTS


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.1-378.26 -/
inductive vextbinop_ : Type where
  | mk_vextbinop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vextbinop_Jnn_N) : vextbinop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.8-378.19 -/
inductive wf_vextbinop_ : ishape → vextbinop_ → Prop where
  | vextbinop__case_0 (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vextbinop_Jnn_N) :
    wf_vextbinop_Jnn_N v_Jnn v_N var_x →
    v_ishape = (ishape.X v_Jnn (dim.mk_dim v_N)) →
    wf_vextbinop_ v_ishape (vextbinop_.mk_vextbinop__0 v_Jnn v_N var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:378.1-378.26 -/
def proj_vextbinop__0 (var_x : vextbinop_) : vextbinop_Jnn_N :=
  match var_x with
  | vextbinop_.mk_vextbinop__0 v_Jnn v_N var_x => var_x

/- Record Creation Definition at: ../specification/wasm-2.0/1-syntax.spectec:386.1-386.69 -/
structure memarg where
  MKmemarg ::
  ALIGN : u32
  OFFSET : u32
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:386.8-386.14 -/
inductive wf_memarg : memarg → Prop where
  | memarg_case_ (var_0 : u32) (var_1 : u32) :
    wf_uN 32 var_0 →
    wf_uN 32 var_1 →
    wf_memarg ({
      ALIGN := var_0
      OFFSET := var_1 : memarg
    })


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.1-390.24 -/
inductive loadop_Inn : Type where
  | mk_loadop_Inn (v_sz : sz) (v_sx : sx) : loadop_Inn
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.8-390.16 -/
inductive wf_loadop_Inn : Inn → loadop_Inn → Prop where
  | loadop_Inn_case_0 (v_Inn : Inn) (v_sz : sz) (v_sx : sx) :
    wf_sz v_sz →
    (proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn)) →
    wf_loadop_Inn v_Inn (loadop_Inn.mk_loadop_Inn v_sz v_sx)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.1-390.24 -/
inductive loadop_ : Type where
  | mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.8-390.16 -/
inductive wf_loadop_ : numtype → loadop_ → Prop where
  | loadop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : loadop_Inn) :
    wf_loadop_Inn v_Inn var_x →
    v_numtype = (numtype_Inn v_Inn) →
    wf_loadop_ v_numtype (loadop_.mk_loadop__0 v_Inn var_x)


/- Auxiliary Definition at: ../specification/wasm-2.0/1-syntax.spectec:390.1-390.24 -/
def proj_loadop__0 (var_x : loadop_) : loadop_Inn :=
  match var_x with
  | loadop_.mk_loadop__0 v_Inn var_x => var_x

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:393.1-396.46 -/
inductive vloadop : Type where
  | SHAPEX_ (__0 : Nat) (__1 : Nat) (v_sx : sx) : vloadop
  | SPLAT (_ : Nat) : vloadop
  | ZERO (_ : Nat) : vloadop
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:403.1-405.17 -/
inductive blocktype : Type where
  | _RESULT (valtype_opt : Option valtype) : blocktype
  | _IDX (v_typeidx : typeidx) : blocktype
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:403.8-403.17 -/
inductive wf_blocktype : blocktype → Prop where
  | blocktype_case_0 (valtype_opt : Option valtype) : wf_blocktype (blocktype._RESULT valtype_opt)
  | blocktype_case_1 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_blocktype (blocktype._IDX v_typeidx)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.1-525.22 -/
inductive instr : Type where
  | NOP : instr
  | UNREACHABLE : instr
  | DROP : instr
  | SELECT (valtype_lst_opt : Option (List valtype)) : instr
  | BLOCK (v_blocktype : blocktype) (instr_lst : List instr) : instr
  | LOOP (v_blocktype : blocktype) (instr_lst : List instr) : instr
  | IFELSE (v_blocktype : blocktype) (instr_lst_0 : List instr) (instr_lst_1 : List instr) : instr
  | BR (v_labelidx : labelidx) : instr
  | BR_IF (v_labelidx : labelidx) : instr
  | BR_TABLE (labelidx_lst : List labelidx) (v_labelidx : labelidx) : instr
  | CALL (v_funcidx : funcidx) : instr
  | CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : instr
  | RETURN : instr
  | CONST (v_numtype : numtype) (_ : num_) : instr
  | UNOP (v_numtype : numtype) (_ : unop_) : instr
  | BINOP (v_numtype : numtype) (_ : binop_) : instr
  | TESTOP (v_numtype : numtype) (_ : testop_) : instr
  | RELOP (v_numtype : numtype) (_ : relop_) : instr
  | CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (_ : cvtop__) : instr
  | EXTEND (v_numtype : numtype) (v_n : n) : instr
  | VCONST (v_vectype : vectype) (_ : vec_) : instr
  | VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : instr
  | VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : instr
  | VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : instr
  | VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : instr
  | VUNOP (v_shape : shape) (_ : vunop_) : instr
  | VBINOP (v_shape : shape) (_ : vbinop_) : instr
  | VTESTOP (v_shape : shape) (_ : vtestop_) : instr
  | VRELOP (v_shape : shape) (_ : vrelop_) : instr
  | VSHIFTOP (v_ishape : ishape) (_ : vshiftop_) : instr
  | VBITMASK (v_ishape : ishape) : instr
  | VSWIZZLE (v_ishape : ishape) : instr
  | VSHUFFLE (v_ishape : ishape) (laneidx_lst : List laneidx) : instr
  | VSPLAT (v_shape : shape) : instr
  | VEXTRACT_LANE (v_shape : shape) (sx_opt : Option sx) (v_laneidx : laneidx) : instr
  | VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : instr
  | VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextunop_) : instr
  | VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextbinop_) : instr
  | VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : instr
  | VCVTOP (v_shape_0 : shape) (v_shape_1 : shape) (v_vcvtop : vcvtop) : instr
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
  | TABLE_COPY (v_tableidx_0 : tableidx) (v_tableidx_1 : tableidx) : instr
  | TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : instr
  | ELEM_DROP (v_elemidx : elemidx) : instr
  | LOAD (v_numtype : numtype) (_ : Option loadop_) (v_memarg : memarg) : instr
  | STORE (v_numtype : numtype) (sz_opt : Option sz) (v_memarg : memarg) : instr
  | VLOAD (v_vectype : vectype) (vloadop_opt : Option vloadop) (v_memarg : memarg) : instr
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

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:524.8-524.13 -/
inductive wf_instr : instr → Prop where
  | instr_case_0 : wf_instr instr.NOP
  | instr_case_1 : wf_instr instr.UNREACHABLE
  | instr_case_2 : wf_instr instr.DROP
  | instr_case_3 (valtype_lst_opt : Option (List valtype)) : wf_instr (instr.SELECT valtype_lst_opt)
  | instr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.BLOCK v_blocktype instr_lst)
  | instr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.LOOP v_blocktype instr_lst)
  | instr_case_6 (v_blocktype : blocktype) (instr_lst : List instr) (instr_lst_0_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    Forall (fun (instr_lst_0_elem : instr) => wf_instr instr_lst_0_elem) instr_lst_0_lst →
    wf_instr (instr.IFELSE v_blocktype instr_lst instr_lst_0_lst)
  | instr_case_7 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR v_labelidx)
  | instr_case_8 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_IF v_labelidx)
  | instr_case_9 (labelidx_lst : List labelidx) (v_labelidx : labelidx) :
    Forall (fun (v_labelidx_elem : labelidx) => wf_uN 32 v_labelidx_elem) labelidx_lst →
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_TABLE labelidx_lst v_labelidx)
  | instr_case_10 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_instr (instr.CALL v_funcidx)
  | instr_case_11 (v_tableidx : tableidx) (v_typeidx : typeidx) :
    wf_uN 32 v_tableidx →
    wf_uN 32 v_typeidx →
    wf_instr (instr.CALL_INDIRECT v_tableidx v_typeidx)
  | instr_case_12 : wf_instr instr.RETURN
  | instr_case_13 (v_numtype : numtype) (var_0 : num_) :
    wf_num_ v_numtype var_0 →
    wf_instr (instr.CONST v_numtype var_0)
  | instr_case_14 (v_numtype : numtype) (var_0 : unop_) :
    wf_unop_ v_numtype var_0 →
    wf_instr (instr.UNOP v_numtype var_0)
  | instr_case_15 (v_numtype : numtype) (var_0 : binop_) :
    wf_binop_ v_numtype var_0 →
    wf_instr (instr.BINOP v_numtype var_0)
  | instr_case_16 (v_numtype : numtype) (var_0 : testop_) :
    wf_testop_ v_numtype var_0 →
    wf_instr (instr.TESTOP v_numtype var_0)
  | instr_case_17 (v_numtype : numtype) (var_0 : relop_) :
    wf_relop_ v_numtype var_0 →
    wf_instr (instr.RELOP v_numtype var_0)
  | instr_case_18 (numtype_1 : numtype) (numtype_2 : numtype) (var_0 : cvtop__) :
    wf_cvtop__ numtype_2 numtype_1 var_0 →
    numtype_1 ≠ numtype_2 →
    wf_instr (instr.CVTOP numtype_1 numtype_2 var_0)
  | instr_case_19 (v_numtype : numtype) (v_n : n) : wf_instr (instr.EXTEND v_numtype v_n)
  | instr_case_20 (v_vectype : vectype) (var_0 : vec_) :
    (size (valtype_vectype v_vectype)) ≠ none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) var_0 →
    wf_instr (instr.VCONST v_vectype var_0)
  | instr_case_21 (v_vectype : vectype) (v_vvunop : vvunop) : wf_instr (instr.VVUNOP v_vectype v_vvunop)
  | instr_case_22 (v_vectype : vectype) (v_vvbinop : vvbinop) : wf_instr (instr.VVBINOP v_vectype v_vvbinop)
  | instr_case_23 (v_vectype : vectype) (v_vvternop : vvternop) : wf_instr (instr.VVTERNOP v_vectype v_vvternop)
  | instr_case_24 (v_vectype : vectype) (v_vvtestop : vvtestop) : wf_instr (instr.VVTESTOP v_vectype v_vvtestop)
  | instr_case_25 (v_shape : shape) (var_0 : vunop_) :
    wf_shape v_shape →
    wf_vunop_ v_shape var_0 →
    wf_instr (instr.VUNOP v_shape var_0)
  | instr_case_26 (v_shape : shape) (var_0 : vbinop_) :
    wf_shape v_shape →
    wf_vbinop_ v_shape var_0 →
    wf_instr (instr.VBINOP v_shape var_0)
  | instr_case_27 (v_shape : shape) (var_0 : vtestop_) :
    wf_shape v_shape →
    wf_vtestop_ v_shape var_0 →
    wf_instr (instr.VTESTOP v_shape var_0)
  | instr_case_28 (v_shape : shape) (var_0 : vrelop_) :
    wf_shape v_shape →
    wf_vrelop_ v_shape var_0 →
    wf_instr (instr.VRELOP v_shape var_0)
  | instr_case_29 (v_ishape : ishape) (var_0 : vshiftop_) :
    wf_ishape v_ishape →
    wf_vshiftop_ v_ishape var_0 →
    wf_instr (instr.VSHIFTOP v_ishape var_0)
  | instr_case_30 (v_ishape : ishape) :
    wf_ishape v_ishape →
    wf_instr (instr.VBITMASK v_ishape)
  | instr_case_31 (v_ishape : ishape) :
    wf_ishape v_ishape →
    v_ishape = (ishape.X Jnn.I8 (dim.mk_dim 16)) →
    wf_instr (instr.VSWIZZLE v_ishape)
  | instr_case_32 (v_ishape : ishape) (laneidx_lst : List laneidx) :
    wf_ishape v_ishape →
    Forall (fun (v_laneidx_elem : laneidx) => wf_uN 8 v_laneidx_elem) laneidx_lst →
    (v_ishape = (ishape.X Jnn.I8 (dim.mk_dim 16))) ∧ ((List.length laneidx_lst) = 16) →
    wf_instr (instr.VSHUFFLE v_ishape laneidx_lst)
  | instr_case_33 (v_shape : shape) :
    wf_shape v_shape →
    wf_instr (instr.VSPLAT v_shape)
  | instr_case_34 (v_numtype : numtype) (v_shape : shape) (sx_opt : Option sx) (v_laneidx : laneidx) :
    wf_shape v_shape →
    wf_uN 8 v_laneidx →
    (((fun_lanetype v_shape) = (lanetype_numtype v_numtype)) ↔ (sx_opt = none)) →
    wf_instr (instr.VEXTRACT_LANE v_shape sx_opt v_laneidx)
  | instr_case_35 (v_shape : shape) (v_laneidx : laneidx) :
    wf_shape v_shape →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VREPLACE_LANE v_shape v_laneidx)
  | instr_case_36 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextunop_) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextunop_ ishape_1 var_0 →
    (lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2)))) →
    wf_instr (instr.VEXTUNOP ishape_1 ishape_2 var_0)
  | instr_case_37 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextbinop_) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextbinop_ ishape_1 var_0 →
    (lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2)))) →
    wf_instr (instr.VEXTBINOP ishape_1 ishape_2 var_0)
  | instr_case_38 (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    ((lsize (fun_lanetype (shape_ishape ishape_2))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) ∧ ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) ≤ 32) →
    wf_instr (instr.VNARROW ishape_1 ishape_2 v_sx)
  | instr_case_39 (v_shape : shape) (shape_0 : shape) (v_vcvtop : vcvtop) :
    wf_shape v_shape →
    wf_shape shape_0 →
    wf_instr (instr.VCVTOP v_shape shape_0 v_vcvtop)
  | instr_case_40 (v_reftype : reftype) : wf_instr (instr.REF_NULL v_reftype)
  | instr_case_41 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_instr (instr.REF_FUNC v_funcidx)
  | instr_case_42 : wf_instr instr.REF_IS_NULL
  | instr_case_43 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_GET v_localidx)
  | instr_case_44 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_SET v_localidx)
  | instr_case_45 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_TEE v_localidx)
  | instr_case_46 (v_globalidx : globalidx) :
    wf_uN 32 v_globalidx →
    wf_instr (instr.GLOBAL_GET v_globalidx)
  | instr_case_47 (v_globalidx : globalidx) :
    wf_uN 32 v_globalidx →
    wf_instr (instr.GLOBAL_SET v_globalidx)
  | instr_case_48 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_GET v_tableidx)
  | instr_case_49 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_SET v_tableidx)
  | instr_case_50 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_SIZE v_tableidx)
  | instr_case_51 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_GROW v_tableidx)
  | instr_case_52 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_FILL v_tableidx)
  | instr_case_53 (v_tableidx : tableidx) (tableidx_0 : tableidx) :
    wf_uN 32 v_tableidx →
    wf_uN 32 tableidx_0 →
    wf_instr (instr.TABLE_COPY v_tableidx tableidx_0)
  | instr_case_54 (v_tableidx : tableidx) (v_elemidx : elemidx) :
    wf_uN 32 v_tableidx →
    wf_uN 32 v_elemidx →
    wf_instr (instr.TABLE_INIT v_tableidx v_elemidx)
  | instr_case_55 (v_elemidx : elemidx) :
    wf_uN 32 v_elemidx →
    wf_instr (instr.ELEM_DROP v_elemidx)
  | instr_case_56 (v_numtype : numtype) (var_0_opt : Option loadop_) (v_memarg : memarg) :
    Forall (fun (var_0_elem : loadop_) => wf_loadop_ v_numtype var_0_elem) (Option.toList var_0_opt) →
    wf_memarg v_memarg →
    wf_instr (instr.LOAD v_numtype var_0_opt v_memarg)
  | instr_case_57 (Inn_opt : Option Inn) (numtype_opt : Option numtype) (v_numtype : numtype) (sz_opt : Option sz) (v_memarg : memarg) :
    Forall (fun (v_sz_elem : sz) => wf_sz v_sz_elem) (Option.toList sz_opt) →
    wf_memarg v_memarg →
    ((Inn_opt = none) ↔ (numtype_opt = none)) →
    ((Inn_opt = none) ↔ (sz_opt = none)) →
    Forall₃ (fun (v_Inn_elem : Inn) (v_numtype_elem : numtype) (v_sz_elem : sz) => (v_numtype_elem = (numtype_Inn v_Inn_elem)) ∧ ((proj_sz_0 v_sz_elem) < (sizenn (numtype_Inn v_Inn_elem)))) (Option.toList Inn_opt) (Option.toList numtype_opt) (Option.toList sz_opt) →
    wf_instr (instr.STORE v_numtype sz_opt v_memarg)
  | instr_case_58 (v_vectype : vectype) (vloadop_opt : Option vloadop) (v_memarg : memarg) :
    wf_memarg v_memarg →
    wf_instr (instr.VLOAD v_vectype vloadop_opt v_memarg)
  | instr_case_59 (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) :
    wf_sz v_sz →
    wf_memarg v_memarg →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VLOAD_LANE v_vectype v_sz v_memarg v_laneidx)
  | instr_case_60 (v_vectype : vectype) (v_memarg : memarg) :
    wf_memarg v_memarg →
    wf_instr (instr.VSTORE v_vectype v_memarg)
  | instr_case_61 (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) :
    wf_sz v_sz →
    wf_memarg v_memarg →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VSTORE_LANE v_vectype v_sz v_memarg v_laneidx)
  | instr_case_62 : wf_instr instr.MEMORY_SIZE
  | instr_case_63 : wf_instr instr.MEMORY_GROW
  | instr_case_64 : wf_instr instr.MEMORY_FILL
  | instr_case_65 : wf_instr instr.MEMORY_COPY
  | instr_case_66 (v_dataidx : dataidx) :
    wf_uN 32 v_dataidx →
    wf_instr (instr.MEMORY_INIT v_dataidx)
  | instr_case_67 (v_dataidx : dataidx) :
    wf_uN 32 v_dataidx →
    wf_instr (instr.DATA_DROP v_dataidx)


/- Type Alias Definition at: ../specification/wasm-2.0/1-syntax.spectec:528.1-529.9 -/
abbrev expr : Type := List instr

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:541.1-541.59 -/
inductive elemmode : Type where
  | ACTIVE (v_tableidx : tableidx) (v_expr : expr) : elemmode
  | PASSIVE : elemmode
  | DECLARE : elemmode
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:541.8-541.16 -/
inductive wf_elemmode : elemmode → Prop where
  | elemmode_case_0 (v_tableidx : tableidx) (v_expr : expr) :
    wf_uN 32 v_tableidx →
    Forall (fun (v_expr_elem : instr) => wf_instr v_expr_elem) v_expr →
    wf_elemmode (elemmode.ACTIVE v_tableidx v_expr)
  | elemmode_case_1 : wf_elemmode elemmode.PASSIVE
  | elemmode_case_2 : wf_elemmode elemmode.DECLARE


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:542.1-542.47 -/
inductive datamode : Type where
  | ACTIVE (v_memidx : memidx) (v_expr : expr) : datamode
  | PASSIVE : datamode
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:542.8-542.16 -/
inductive wf_datamode : datamode → Prop where
  | datamode_case_0 (v_memidx : memidx) (v_expr : expr) :
    wf_uN 32 v_memidx →
    Forall (fun (v_expr_elem : instr) => wf_instr v_expr_elem) v_expr →
    wf_datamode (datamode.ACTIVE v_memidx v_expr)
  | datamode_case_1 : wf_datamode datamode.PASSIVE


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:544.1-545.16 -/
inductive type : Type where
  | TYPE (v_functype : functype) : type
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:546.1-547.16 -/
inductive «local» : Type where
  | LOCAL (v_valtype : valtype) : «local»
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:548.1-549.27 -/
inductive func : Type where
  | FUNC (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) : func
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:548.8-548.12 -/
inductive wf_func : func → Prop where
  | func_case_0 (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) :
    wf_uN 32 v_typeidx →
    Forall (fun (v_expr_elem : instr) => wf_instr v_expr_elem) v_expr →
    wf_func (func.FUNC v_typeidx local_lst v_expr)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:550.1-551.25 -/
inductive global : Type where
  | GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:550.8-550.14 -/
inductive wf_global : global → Prop where
  | global_case_0 (v_globaltype : globaltype) (v_expr : expr) :
    Forall (fun (v_expr_elem : instr) => wf_instr v_expr_elem) v_expr →
    wf_global (global.GLOBAL v_globaltype v_expr)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:552.1-553.18 -/
inductive table : Type where
  | TABLE (v_tabletype : tabletype) : table
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:552.8-552.13 -/
inductive wf_table : table → Prop where
  | table_case_0 (v_tabletype : tabletype) :
    wf_tabletype v_tabletype →
    wf_table (table.TABLE v_tabletype)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:554.1-555.17 -/
inductive mem : Type where
  | MEMORY (v_memtype : memtype) : mem
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:554.8-554.11 -/
inductive wf_mem : mem → Prop where
  | mem_case_0 (v_memtype : memtype) :
    wf_memtype v_memtype →
    wf_mem (mem.MEMORY v_memtype)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:556.1-557.30 -/
inductive elem : Type where
  | ELEM (v_reftype : reftype) (expr_lst : List expr) (v_elemmode : elemmode) : elem
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:556.8-556.12 -/
inductive wf_elem : elem → Prop where
  | elem_case_0 (v_reftype : reftype) (expr_lst : List expr) (v_elemmode : elemmode) :
    Forall (fun (v_expr_elem : expr) => Forall (fun (v_expr_elem : instr) => wf_instr v_expr_elem) v_expr_elem) expr_lst →
    wf_elemmode v_elemmode →
    wf_elem (elem.ELEM v_reftype expr_lst v_elemmode)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.1-559.22 -/
inductive data : Type where
  | DATA (byte_lst : List byte) (v_datamode : datamode) : data
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:558.8-558.12 -/
inductive wf_data : data → Prop where
  | data_case_0 (byte_lst : List byte) (v_datamode : datamode) :
    Forall (fun (v_byte_elem : byte) => wf_byte v_byte_elem) byte_lst →
    wf_datamode v_datamode →
    wf_data (data.DATA byte_lst v_datamode)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.1-561.16 -/
inductive start : Type where
  | START (v_funcidx : funcidx) : start
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:560.8-560.13 -/
inductive wf_start : start → Prop where
  | start_case_0 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_start (start.START v_funcidx)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.1-564.66 -/
inductive externidx : Type where
  | FUNC (v_funcidx : funcidx) : externidx
  | GLOBAL (v_globalidx : globalidx) : externidx
  | TABLE (v_tableidx : tableidx) : externidx
  | MEM (v_memidx : memidx) : externidx
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:563.8-563.17 -/
inductive wf_externidx : externidx → Prop where
  | externidx_case_0 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_externidx (externidx.FUNC v_funcidx)
  | externidx_case_1 (v_globalidx : globalidx) :
    wf_uN 32 v_globalidx →
    wf_externidx (externidx.GLOBAL v_globalidx)
  | externidx_case_2 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_externidx (externidx.TABLE v_tableidx)
  | externidx_case_3 (v_memidx : memidx) :
    wf_uN 32 v_memidx →
    wf_externidx (externidx.MEM v_memidx)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.1-566.24 -/
inductive «export» : Type where
  | EXPORT (v_name : name) (v_externidx : externidx) : «export»
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:565.8-565.14 -/
inductive wf_export : «export» → Prop where
  | export_case_0 (v_name : name) (v_externidx : externidx) :
    wf_name v_name →
    wf_externidx v_externidx →
    wf_export (export.EXPORT v_name v_externidx)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:567.1-568.30 -/
inductive «import» : Type where
  | IMPORT (v_name_0 : name) (v_name_1 : name) (v_externtype : externtype) : «import»
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:567.8-567.14 -/
inductive wf_import : «import» → Prop where
  | import_case_0 (v_name : name) (name_0 : name) (v_externtype : externtype) :
    wf_name v_name →
    wf_name name_0 →
    wf_externtype v_externtype →
    wf_import (import.IMPORT v_name name_0 v_externtype)


/- Inductive Type Definition at: ../specification/wasm-2.0/1-syntax.spectec:570.1-571.76 -/
inductive module : Type where
  | MODULE (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») : module
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/1-syntax.spectec:570.8-570.14 -/
inductive wf_module : module → Prop where
  | module_case_0 (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») :
    Forall (fun (v_import_elem : «import») => wf_import v_import_elem) import_lst →
    Forall (fun (v_func_elem : func) => wf_func v_func_elem) func_lst →
    Forall (fun (v_global_elem : global) => wf_global v_global_elem) global_lst →
    Forall (fun (v_table_elem : table) => wf_table v_table_elem) table_lst →
    Forall (fun (v_mem_elem : mem) => wf_mem v_mem_elem) mem_lst →
    Forall (fun (v_elem_elem : elem) => wf_elem v_elem_elem) elem_lst →
    Forall (fun (v_data_elem : data) => wf_data v_data_elem) data_lst →
    Forall (fun (v_start_elem : start) => wf_start v_start_elem) (Option.toList start_opt) →
    Forall (fun (v_export_elem : «export») => wf_export v_export_elem) export_lst →
    wf_module (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)


/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.6-7.19 -/
inductive fun_concat_bytes : List (List byte) → List byte → Prop where
  | fun_concat_bytes_case_0 : fun_concat_bytes [] []
  | fun_concat_bytes_case_1 (b_lst : List byte) (b'_lst_lst : List (List byte)) (var_0 : List byte) :
    fun_concat_bytes b'_lst_lst var_0 →
    fun_concat_bytes ([b_lst] ++ b'_lst_lst) (b_lst ++ var_0)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:7.6-7.19 -/
theorem concat_bytes_is_wf (var_0_lst_lst : List (List byte)) (ret_val_lst : List byte) (var_0 : List byte) :
  fun_concat_bytes var_0_lst_lst var_0 →
  Forall (fun (var_0_lst_elem : List byte) => Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst_elem) var_0_lst_lst →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:28.1-28.32 -/
def unpack (v_lanetype : lanetype) : numtype :=
  match v_lanetype with
  | lanetype.I32 => numtype.I32
  | lanetype.I64 => numtype.I64
  | lanetype.F32 => numtype.F32
  | lanetype.F64 => numtype.F64
  | lanetype.I8 => numtype.I32
  | lanetype.I16 => numtype.I32

/- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:44.1-44.54 -/
def shunpack (v_shape : shape) : numtype :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => unpack v_Lnn

/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:51.6-51.14 -/
inductive fun_funcsxt : List externtype → List functype → Prop where
  | fun_funcsxt_case_0 : fun_funcsxt [] []
  | fun_funcsxt_case_1 (ft : functype) (xt_lst : List externtype) (var_0 : List functype) :
    fun_funcsxt xt_lst var_0 →
    fun_funcsxt ([externtype.FUNC ft] ++ xt_lst) ([ft] ++ var_0)
  | fun_funcsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List functype) :
    fun_funcsxt xt_lst var_0 →
    fun_funcsxt ([v_externtype] ++ xt_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:52.6-52.16 -/
inductive fun_globalsxt : List externtype → List globaltype → Prop where
  | fun_globalsxt_case_0 : fun_globalsxt [] []
  | fun_globalsxt_case_1 (gt : globaltype) (xt_lst : List externtype) (var_0 : List globaltype) :
    fun_globalsxt xt_lst var_0 →
    fun_globalsxt ([externtype.GLOBAL gt] ++ xt_lst) ([gt] ++ var_0)
  | fun_globalsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List globaltype) :
    fun_globalsxt xt_lst var_0 →
    fun_globalsxt ([v_externtype] ++ xt_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.6-53.15 -/
inductive fun_tablesxt : List externtype → List tabletype → Prop where
  | fun_tablesxt_case_0 : fun_tablesxt [] []
  | fun_tablesxt_case_1 (tt : tabletype) (xt_lst : List externtype) (var_0 : List tabletype) :
    fun_tablesxt xt_lst var_0 →
    fun_tablesxt ([externtype.TABLE tt] ++ xt_lst) ([tt] ++ var_0)
  | fun_tablesxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List tabletype) :
    fun_tablesxt xt_lst var_0 →
    fun_tablesxt ([v_externtype] ++ xt_lst) var_0


/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:53.6-53.15 -/
theorem tablesxt_is_wf (var_0_lst : List externtype) (ret_val_lst : List tabletype) (var_0 : List tabletype) :
  fun_tablesxt var_0_lst var_0 →
  Forall (fun (var_0_elem : externtype) => wf_externtype var_0_elem) var_0_lst →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : tabletype) => wf_tabletype ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.6-54.13 -/
inductive fun_memsxt : List externtype → List memtype → Prop where
  | fun_memsxt_case_0 : fun_memsxt [] []
  | fun_memsxt_case_1 (mt : memtype) (xt_lst : List externtype) (var_0 : List memtype) :
    fun_memsxt xt_lst var_0 →
    fun_memsxt ([externtype.MEM mt] ++ xt_lst) ([mt] ++ var_0)
  | fun_memsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List memtype) :
    fun_memsxt xt_lst var_0 →
    fun_memsxt ([v_externtype] ++ xt_lst) var_0


/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:54.6-54.13 -/
theorem memsxt_is_wf (var_0_lst : List externtype) (ret_val_lst : List memtype) (var_0 : List memtype) :
  fun_memsxt var_0_lst var_0 →
  Forall (fun (var_0_elem : externtype) => wf_externtype var_0_elem) var_0_lst →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : memtype) => wf_memtype ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.1-80.61 -/
def dataidx_instr (v_instr : instr) : List dataidx :=
  match v_instr with
  | instr.MEMORY_INIT x => [x]
  | instr.DATA_DROP x => [x]
  | _ => []

/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:80.6-80.20 -/
theorem dataidx_instr_is_wf (v_instr : instr) (ret_val_lst : List dataidx) :
  wf_instr v_instr →
  ret_val_lst = (dataidx_instr v_instr) →
  Forall (fun (ret_val_elem : dataidx) => wf_uN 32 ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.6-85.21 -/
inductive fun_dataidx_instrs : List instr → List dataidx → Prop where
  | fun_dataidx_instrs_case_0 : fun_dataidx_instrs [] []
  | fun_dataidx_instrs_case_1 (v_instr : instr) (instr'_lst : List instr) (var_0 : List dataidx) :
    fun_dataidx_instrs instr'_lst var_0 →
    fun_dataidx_instrs ([v_instr] ++ instr'_lst) ((dataidx_instr v_instr) ++ var_0)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:85.6-85.21 -/
theorem dataidx_instrs_is_wf (var_0_lst : List instr) (ret_val_lst : List dataidx) (var_0 : List dataidx) :
  fun_dataidx_instrs var_0_lst var_0 →
  Forall (fun (var_0_elem : instr) => wf_instr var_0_elem) var_0_lst →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : dataidx) => wf_uN 32 ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 -/
inductive fun_dataidx_expr : expr → List dataidx → Prop where
  | fun_dataidx_expr_case_0 (in_lst : List instr) (var_0 : List dataidx) :
    fun_dataidx_instrs in_lst var_0 →
    fun_dataidx_expr in_lst var_0


/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:89.6-89.19 -/
theorem dataidx_expr_is_wf (v_expr : expr) (ret_val_lst : List dataidx) (var_0 : List dataidx) :
  fun_dataidx_expr v_expr var_0 →
  Forall (fun (v_expr_elem : instr) => wf_instr v_expr_elem) v_expr →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : dataidx) => wf_uN 32 ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 -/
inductive fun_dataidx_func : func → List dataidx → Prop where
  | fun_dataidx_func_case_0 (x : uN) (loc_lst : List «local») (e : List instr) (var_0 : List dataidx) :
    fun_dataidx_expr e var_0 →
    fun_dataidx_func (func.FUNC x loc_lst e) var_0


/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:92.6-92.19 -/
theorem dataidx_func_is_wf (v_func : func) (ret_val_lst : List dataidx) (var_0 : List dataidx) :
  fun_dataidx_func v_func var_0 →
  wf_func v_func →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : dataidx) => wf_uN 32 ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.6-95.20 -/
inductive fun_dataidx_funcs : List func → List dataidx → Prop where
  | fun_dataidx_funcs_case_0 : fun_dataidx_funcs [] []
  | fun_dataidx_funcs_case_1 (v_func : func) (func'_lst : List func) (var_1 : List dataidx) (var_0 : List dataidx) :
    fun_dataidx_funcs func'_lst var_1 →
    fun_dataidx_func v_func var_0 →
    fun_dataidx_funcs ([v_func] ++ func'_lst) (var_0 ++ var_1)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:95.6-95.20 -/
theorem dataidx_funcs_is_wf (var_0_lst : List func) (ret_val_lst : List dataidx) (var_0 : List dataidx) :
  fun_dataidx_funcs var_0_lst var_0 →
  Forall (fun (var_0_elem : func) => wf_func var_0_elem) var_0_lst →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : dataidx) => wf_uN 32 ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.1-106.35 -/
def memarg0 : memarg :=
  {
    ALIGN := uN.mk_uN 0
    OFFSET := uN.mk_uN 0 : memarg
  }

/- Well-Formedness Theorem at: ../specification/wasm-2.0/2-syntax-aux.spectec:106.6-106.13 -/
theorem memarg0_is_wf (ret_val : memarg) :
  ret_val = memarg0 →
  wf_memarg ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:7.1-7.41 -/
opaque s33_to_u32 (v_s33 : s33) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:7.6-7.17 -/
theorem s33_to_u32_is_wf (v_s33 : s33) (ret_val : u32) :
  wf_sN 33 v_s33 →
  ret_val = (s33_to_u32 v_s33) →
  wf_uN 32 ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:9.1-9.22 -/
def nat_of_bool (v_bool : Bool) : Nat :=
  match v_bool with
  | false => 0
  | true => 1

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:13.1-13.23 -/
opaque truncz (rat : Rat) : Int := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:20.6-20.14 -/
inductive fun_signed_ : N → Nat → Int → Prop where
  | fun_signed__case_0 (v_N : Nat) (i : Nat) :
    i < (2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) →
    fun_signed_ v_N i (i : Int)
  | fun_signed__case_1 (v_N : Nat) (i : Nat) :
    ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) ≤ i) ∧ (i < (2 ^ v_N)) →
    fun_signed_ v_N i ((i : Int) - ((2 ^ v_N) : Int))


/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:24.6-24.18 -/
inductive fun_inv_signed_ : N → Int → Nat → Prop where
  | fun_inv_signed__case_0 (v_N : Nat) (i : Int) :
    ((0 : Int) ≤ i) ∧ (i < ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) →
    fun_inv_signed_ v_N i (Int.toNat i)
  | fun_inv_signed__case_1 (v_N : Nat) (i : Int) :
    ((- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) ≤ i) ∧ (i < (0 : Int)) →
    fun_inv_signed_ v_N i (Int.toNat (i + ((2 ^ v_N) : Int)))


/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:31.1-31.61 -/
def sat_u_ (v_N : N) (int : Int) : Nat :=
  if
    int < (0 : Int)
  then
    0
  else
    if
      int > (((2 ^ v_N) : Int) - (1 : Int))
    then
      Int.toNat (((2 ^ v_N) : Int) - (1 : Int))
    else
      Int.toNat int

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:36.1-36.61 -/
def sat_s_ (v_N : N) (int : Int) : Int :=
  if
    int < (- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int))
  then
    - ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)
  else
    if
      int > (((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int))
    then
      ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int)
    else
      int

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:56.1-56.89 -/
opaque extend__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:56.6-56.15 -/
theorem extend___is_wf (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN) :
  wf_uN v_M v_iN →
  ret_val = (extend__ v_M v_N v_sx v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:224.1-224.30 -/
opaque fabs_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:224.6-224.12 -/
theorem fabs__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  ret_val_lst = (fabs_ v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:227.1-227.31 -/
opaque fceil_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:227.6-227.13 -/
theorem fceil__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  ret_val_lst = (fceil_ v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:228.1-228.32 -/
opaque ffloor_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:228.6-228.14 -/
theorem ffloor__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  ret_val_lst = (ffloor_ v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:230.1-230.34 -/
opaque fnearest_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:230.6-230.16 -/
theorem fnearest__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  ret_val_lst = (fnearest_ v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:225.1-225.30 -/
opaque fneg_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:225.6-225.12 -/
theorem fneg__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  ret_val_lst = (fneg_ v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:226.1-226.31 -/
opaque fsqrt_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:226.6-226.13 -/
theorem fsqrt__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  ret_val_lst = (fsqrt_ v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:229.1-229.32 -/
opaque ftrunc_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:229.6-229.14 -/
theorem ftrunc__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  ret_val_lst = (ftrunc_ v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:120.1-120.29 -/
opaque iclz_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:120.6-120.12 -/
theorem iclz__is_wf (v_N : N) (v_iN : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  ret_val = (iclz_ v_N v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:121.1-121.29 -/
opaque ictz_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:121.6-121.12 -/
theorem ictz__is_wf (v_N : N) (v_iN : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  ret_val = (ictz_ v_N v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:122.1-122.32 -/
opaque ipopcnt_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:122.6-122.15 -/
theorem ipopcnt__is_wf (v_N : N) (v_iN : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  ret_val = (ipopcnt_ v_N v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:55.1-55.33 -/
opaque wrap__ (v_M : M) (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:55.6-55.13 -/
theorem wrap___is_wf (v_M : M) (v_N : N) (v_iN : iN) (ret_val : iN) :
  wf_uN v_M v_iN →
  ret_val = (wrap__ v_M v_N v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:44.1-45.32 -/
def fun_unop_ (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) : List num_ :=
  match v_numtype, v_unop_, v_num_ with
  | numtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.CLZ, num_.mk_num__0 Inn.I32 v_iN => [num_.mk_num__0 Inn.I32 (iclz_ (sizenn (numtype_Inn Inn.I32)) v_iN)]
  | numtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.CLZ, num_.mk_num__0 Inn.I64 v_iN => [num_.mk_num__0 Inn.I64 (iclz_ (sizenn (numtype_Inn Inn.I64)) v_iN)]
  | numtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.CTZ, num_.mk_num__0 Inn.I32 v_iN => [num_.mk_num__0 Inn.I32 (ictz_ (sizenn (numtype_Inn Inn.I32)) v_iN)]
  | numtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.CTZ, num_.mk_num__0 Inn.I64 v_iN => [num_.mk_num__0 Inn.I64 (ictz_ (sizenn (numtype_Inn Inn.I64)) v_iN)]
  | numtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.POPCNT, num_.mk_num__0 Inn.I32 v_iN => [num_.mk_num__0 Inn.I32 (ipopcnt_ (sizenn (numtype_Inn Inn.I32)) v_iN)]
  | numtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.POPCNT, num_.mk_num__0 Inn.I64 v_iN => [num_.mk_num__0 Inn.I64 (ipopcnt_ (sizenn (numtype_Inn Inn.I64)) v_iN)]
  | numtype.I32, unop_.mk_unop__0 Inn.I32 (unop_Inn.EXTEND v_M), num_.mk_num__0 Inn.I32 v_iN => [num_.mk_num__0 Inn.I32 (extend__ v_M (sizenn (numtype_Inn Inn.I32)) sx.S (wrap__ (sizenn (numtype_Inn Inn.I32)) v_M v_iN))]
  | numtype.I64, unop_.mk_unop__0 Inn.I64 (unop_Inn.EXTEND v_M), num_.mk_num__0 Inn.I64 v_iN => [num_.mk_num__0 Inn.I64 (extend__ v_M (sizenn (numtype_Inn Inn.I64)) sx.S (wrap__ (sizenn (numtype_Inn Inn.I64)) v_M v_iN))]
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.ABS, num_.mk_num__1 Fnn.F32 v_fN => Map (fun (iter_0_1_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_1_elem) (fabs_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.ABS, num_.mk_num__1 Fnn.F64 v_fN => Map (fun (iter_0_2_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_2_elem) (fabs_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.NEG, num_.mk_num__1 Fnn.F32 v_fN => Map (fun (iter_0_3_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_3_elem) (fneg_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.NEG, num_.mk_num__1 Fnn.F64 v_fN => Map (fun (iter_0_4_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_4_elem) (fneg_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.SQRT, num_.mk_num__1 Fnn.F32 v_fN => Map (fun (iter_0_5_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_5_elem) (fsqrt_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.SQRT, num_.mk_num__1 Fnn.F64 v_fN => Map (fun (iter_0_6_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_6_elem) (fsqrt_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.CEIL, num_.mk_num__1 Fnn.F32 v_fN => Map (fun (iter_0_7_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_7_elem) (fceil_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.CEIL, num_.mk_num__1 Fnn.F64 v_fN => Map (fun (iter_0_8_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_8_elem) (fceil_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.FLOOR, num_.mk_num__1 Fnn.F32 v_fN => Map (fun (iter_0_9_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_9_elem) (ffloor_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.FLOOR, num_.mk_num__1 Fnn.F64 v_fN => Map (fun (iter_0_10_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_10_elem) (ffloor_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.TRUNC, num_.mk_num__1 Fnn.F32 v_fN => Map (fun (iter_0_11_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_11_elem) (ftrunc_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.TRUNC, num_.mk_num__1 Fnn.F64 v_fN => Map (fun (iter_0_12_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_12_elem) (ftrunc_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.NEAREST, num_.mk_num__1 Fnn.F32 v_fN => Map (fun (iter_0_13_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_13_elem) (fnearest_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.NEAREST, num_.mk_num__1 Fnn.F64 v_fN => Map (fun (iter_0_14_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_14_elem) (fnearest_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | _, _, _ => Inhabited.default

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:44.6-44.12 -/
theorem unop__is_wf (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) (ret_val_lst : List num_) :
  wf_unop_ v_numtype v_unop_ →
  wf_num_ v_numtype v_num_ →
  ret_val_lst = (fun_unop_ v_numtype v_unop_ v_num_) →
  Forall (fun (ret_val_elem : num_) => wf_num_ v_numtype ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:215.1-215.37 -/
opaque fadd_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:215.6-215.12 -/
theorem fadd__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fadd_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:223.1-223.42 -/
opaque fcopysign_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:223.6-223.17 -/
theorem fcopysign__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fcopysign_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:218.1-218.37 -/
opaque fdiv_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:218.6-218.12 -/
theorem fdiv__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fdiv_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:220.1-220.37 -/
opaque fmax_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:220.6-220.12 -/
theorem fmax__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fmax_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:219.1-219.37 -/
opaque fmin_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:219.6-219.12 -/
theorem fmin__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fmin_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:217.1-217.37 -/
opaque fmul_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:217.6-217.12 -/
theorem fmul__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fmul_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:216.1-216.37 -/
opaque fsub_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:216.6-216.12 -/
theorem fsub__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fsub_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:105.1-105.36 -/
def iadd_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  uN.mk_uN (((proj_uN_0 v_iN) + (proj_uN_0 iN_0)) % (2 ^ v_N))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:105.6-105.12 -/
theorem iadd__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (iadd_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:112.1-112.36 -/
opaque iand_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:112.6-112.12 -/
theorem iand__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (iand_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 -/
inductive fun_idiv_ : N → sx → iN → iN → Option iN → Prop where
  | fun_idiv__case_0 (v_N : Nat) (i_1 : uN) : fun_idiv_ v_N sx.U i_1 (uN.mk_uN 0) none
  | fun_idiv__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_idiv_ v_N sx.U i_1 i_2 (some (uN.mk_uN (Int.toNat (truncz (((proj_uN_0 i_1) : Rat) / ((proj_uN_0 i_2) : Rat))))))
  | fun_idiv__case_2 (v_N : Nat) (i_1 : uN) : fun_idiv_ v_N sx.S i_1 (uN.mk_uN 0) none
  | fun_idiv__case_3 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) :
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    ((var_0 : Rat) / (var_1 : Rat)) = ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Rat) →
    fun_idiv_ v_N sx.S i_1 i_2 none
  | fun_idiv__case_4 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Int) (var_1 : Int) (var_0 : Nat) :
    fun_signed_ v_N (proj_uN_0 i_2) var_2 →
    fun_signed_ v_N (proj_uN_0 i_1) var_1 →
    fun_inv_signed_ v_N (truncz ((var_1 : Rat) / (var_2 : Rat))) var_0 →
    fun_idiv_ v_N sx.S i_1 i_2 (some (uN.mk_uN var_0))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:108.6-108.12 -/
theorem idiv__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : Option iN) (var_0 : Option iN) :
  fun_idiv_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val_opt = var_0 →
  Forall (fun (ret_val_elem : iN) => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:107.1-107.36 -/
def imul_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  uN.mk_uN (((proj_uN_0 v_iN) * (proj_uN_0 iN_0)) % (2 ^ v_N))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:107.6-107.12 -/
theorem imul__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (imul_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:114.1-114.35 -/
opaque ior_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:114.6-114.11 -/
theorem ior__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (ior_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 -/
inductive fun_irem_ : N → sx → iN → iN → Option iN → Prop where
  | fun_irem__case_0 (v_N : Nat) (i_1 : uN) : fun_irem_ v_N sx.U i_1 (uN.mk_uN 0) none
  | fun_irem__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_irem_ v_N sx.U i_1 i_2 (some (uN.mk_uN (Int.toNat (((proj_uN_0 i_1) : Int) - (((proj_uN_0 i_2) * (Int.toNat (truncz (((proj_uN_0 i_1) : Rat) / ((proj_uN_0 i_2) : Rat))))) : Int)))))
  | fun_irem__case_2 (v_N : Nat) (i_1 : uN) : fun_irem_ v_N sx.S i_1 (uN.mk_uN 0) none
  | fun_irem__case_3 (v_N : Nat) (i_1 : uN) (i_2 : uN) (j_1 : Int) (j_2 : Int) (var_2 : Int) (var_1 : Int) (var_0 : Nat) :
    fun_signed_ v_N (proj_uN_0 i_2) var_2 →
    fun_signed_ v_N (proj_uN_0 i_1) var_1 →
    fun_inv_signed_ v_N (j_1 - (j_2 * (truncz ((j_1 : Rat) / (j_2 : Rat))))) var_0 →
    (j_1 = var_1) ∧ (j_2 = var_2) →
    fun_irem_ v_N sx.S i_1 i_2 (some (uN.mk_uN var_0))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:109.6-109.12 -/
theorem irem__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : Option iN) (var_0 : Option iN) :
  fun_irem_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val_opt = var_0 →
  Forall (fun (ret_val_elem : iN) => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:118.1-118.37 -/
opaque irotl_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:118.6-118.13 -/
theorem irotl__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (irotl_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:119.1-119.37 -/
opaque irotr_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:119.6-119.13 -/
theorem irotr__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (irotr_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:116.1-116.34 -/
opaque ishl_ (v_N : N) (v_iN : iN) (v_u32 : u32) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:116.6-116.12 -/
theorem ishl__is_wf (v_N : N) (v_iN : iN) (v_u32 : u32) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN 32 v_u32 →
  ret_val = (ishl_ v_N v_iN v_u32) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:117.1-117.74 -/
opaque ishr_ (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:117.6-117.12 -/
theorem ishr__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN 32 v_u32 →
  ret_val = (ishr_ v_N v_sx v_iN v_u32) →
  wf_uN v_N ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:106.1-106.36 -/
def isub_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  uN.mk_uN (Int.toNat (((((2 ^ v_N) + (proj_uN_0 v_iN)) : Int) - ((proj_uN_0 iN_0) : Int)) % ((2 ^ v_N) : Int)))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:106.6-106.12 -/
theorem isub__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (isub_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:115.1-115.36 -/
opaque ixor_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:115.6-115.12 -/
theorem ixor__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (ixor_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 -/
inductive fun_binop_ : numtype → binop_ → num_ → num_ → List num_ → Prop where
  | fun_binop__case_0 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ADD) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (iadd_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_1 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ADD) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (iadd_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_2 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.SUB) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (isub_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_3 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.SUB) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (isub_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_4 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.MUL) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (imul_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_5 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.MUL) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (imul_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_6 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) :
    fun_idiv_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.DIV v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (list_ num_ (OMap (fun (iter_0_15_elem : iN) => num_.mk_num__0 Inn.I32 iter_0_15_elem) var_0))
  | fun_binop__case_7 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) :
    fun_idiv_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.DIV v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (list_ num_ (OMap (fun (iter_0_16_elem : iN) => num_.mk_num__0 Inn.I64 iter_0_16_elem) var_0))
  | fun_binop__case_8 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) :
    fun_irem_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.REM v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (list_ num_ (OMap (fun (iter_0_17_elem : iN) => num_.mk_num__0 Inn.I32 iter_0_17_elem) var_0))
  | fun_binop__case_9 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) :
    fun_irem_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.REM v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (list_ num_ (OMap (fun (iter_0_18_elem : iN) => num_.mk_num__0 Inn.I64 iter_0_18_elem) var_0))
  | fun_binop__case_10 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.AND) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (iand_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_11 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.AND) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (iand_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_12 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.OR) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (ior_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_13 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.OR) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (ior_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_14 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.XOR) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (ixor_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_15 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.XOR) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (ixor_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_16 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.SHL) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (ishl_ (sizenn (numtype_Inn Inn.I32)) iN_1 (uN.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_17 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.SHL) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (ishl_ (sizenn (numtype_Inn Inn.I64)) iN_1 (uN.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_18 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.SHR v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (ishr_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 (uN.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_19 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.SHR v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (ishr_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 (uN.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_20 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ROTL) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (irotl_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_21 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ROTL) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (irotl_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_22 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ROTR) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (irotr_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_23 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ROTR) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (irotr_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_24 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.ADD) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun (iter_0_19_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_19_elem) (fadd_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_25 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.ADD) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun (iter_0_20_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_20_elem) (fadd_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_26 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.SUB) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun (iter_0_21_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_21_elem) (fsub_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_27 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.SUB) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun (iter_0_22_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_22_elem) (fsub_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_28 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MUL) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun (iter_0_23_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_23_elem) (fmul_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_29 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MUL) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun (iter_0_24_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_24_elem) (fmul_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_30 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.DIV) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun (iter_0_25_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_25_elem) (fdiv_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_31 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.DIV) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun (iter_0_26_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_26_elem) (fdiv_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_32 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MIN) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun (iter_0_27_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_27_elem) (fmin_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_33 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MIN) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun (iter_0_28_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_28_elem) (fmin_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_34 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MAX) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun (iter_0_29_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_29_elem) (fmax_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_35 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MAX) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun (iter_0_30_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_30_elem) (fmax_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_36 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.COPYSIGN) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun (iter_0_31_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_31_elem) (fcopysign_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_37 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.COPYSIGN) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun (iter_0_32_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_32_elem) (fcopysign_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:46.6-46.13 -/
theorem binop__is_wf (v_numtype : numtype) (v_binop_ : binop_) (v_num_ : num_) (num__0 : num_) (ret_val_lst : List num_) (var_0 : List num_) :
  fun_binop_ v_numtype v_binop_ v_num_ num__0 var_0 →
  wf_binop_ v_numtype v_binop_ →
  wf_num_ v_numtype v_num_ →
  wf_num_ v_numtype num__0 →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : num_) => wf_num_ v_numtype ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:123.1-123.27 -/
def ieqz_ (v_N : N) (v_iN : iN) : u32 :=
  uN.mk_uN (nat_of_bool ((proj_uN_0 v_iN) == 0))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:123.6-123.12 -/
theorem ieqz__is_wf (v_N : N) (v_iN : iN) (ret_val : u32) :
  wf_uN v_N v_iN →
  ret_val = (ieqz_ v_N v_iN) →
  wf_uN 32 ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:48.1-49.32 -/
def fun_testop_ (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) : num_ :=
  match v_numtype, v_testop_, v_num_ with
  | numtype.I32, testop_.mk_testop__0 Inn.I32 testop_Inn.EQZ, num_.mk_num__0 Inn.I32 v_iN => num_.mk_num__0 Inn.I32 (ieqz_ (sizenn (numtype_Inn Inn.I32)) v_iN)
  | numtype.I64, testop_.mk_testop__0 Inn.I64 testop_Inn.EQZ, num_.mk_num__0 Inn.I64 v_iN => num_.mk_num__0 Inn.I32 (ieqz_ (sizenn (numtype_Inn Inn.I64)) v_iN)
  | _, _, _ => Inhabited.default

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:48.6-48.14 -/
theorem testop__is_wf (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) (ret_val : num_) :
  wf_testop_ v_numtype v_testop_ →
  wf_num_ v_numtype v_num_ →
  ret_val = (fun_testop_ v_numtype v_testop_ v_num_) →
  wf_num_ numtype.I32 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:231.1-231.33 -/
opaque feq_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:231.6-231.11 -/
theorem feq__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val = (feq_ v_N v_fN fN_0) →
  wf_uN 32 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:236.1-236.33 -/
opaque fge_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:236.6-236.11 -/
theorem fge__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val = (fge_ v_N v_fN fN_0) →
  wf_uN 32 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:234.1-234.33 -/
opaque fgt_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:234.6-234.11 -/
theorem fgt__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val = (fgt_ v_N v_fN fN_0) →
  wf_uN 32 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:235.1-235.33 -/
opaque fle_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:235.6-235.11 -/
theorem fle__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val = (fle_ v_N v_fN fN_0) →
  wf_uN 32 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:233.1-233.33 -/
opaque flt_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:233.6-233.11 -/
theorem flt__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val = (flt_ v_N v_fN fN_0) →
  wf_uN 32 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:232.1-232.33 -/
opaque fne_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:232.6-232.11 -/
theorem fne__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val = (fne_ v_N v_fN fN_0) →
  wf_uN 32 ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:125.1-125.33 -/
def ieq_ (v_N : N) (v_iN : iN) (iN_0 : iN) : u32 :=
  uN.mk_uN (nat_of_bool (v_iN == iN_0))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:125.6-125.11 -/
theorem ieq__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (ieq_ v_N v_iN iN_0) →
  wf_uN 32 ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 -/
inductive fun_ige_ : N → sx → iN → iN → u32 → Prop where
  | fun_ige__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ige_ v_N sx.U i_1 i_2 (uN.mk_uN (nat_of_bool ((proj_uN_0 i_1) ≥ (proj_uN_0 i_2))))
  | fun_ige__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) :
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_ige_ v_N sx.S i_1 i_2 (uN.mk_uN (nat_of_bool (var_0 ≥ var_1)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:130.6-130.11 -/
theorem ige__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) :
  fun_ige_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = var_0 →
  wf_uN 32 ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 -/
inductive fun_igt_ : N → sx → iN → iN → u32 → Prop where
  | fun_igt__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_igt_ v_N sx.U i_1 i_2 (uN.mk_uN (nat_of_bool ((proj_uN_0 i_1) > (proj_uN_0 i_2))))
  | fun_igt__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) :
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_igt_ v_N sx.S i_1 i_2 (uN.mk_uN (nat_of_bool (var_0 > var_1)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:128.6-128.11 -/
theorem igt__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) :
  fun_igt_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = var_0 →
  wf_uN 32 ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 -/
inductive fun_ile_ : N → sx → iN → iN → u32 → Prop where
  | fun_ile__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ile_ v_N sx.U i_1 i_2 (uN.mk_uN (nat_of_bool ((proj_uN_0 i_1) ≤ (proj_uN_0 i_2))))
  | fun_ile__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) :
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_ile_ v_N sx.S i_1 i_2 (uN.mk_uN (nat_of_bool (var_0 ≤ var_1)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:129.6-129.11 -/
theorem ile__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) :
  fun_ile_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = var_0 →
  wf_uN 32 ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 -/
inductive fun_ilt_ : N → sx → iN → iN → u32 → Prop where
  | fun_ilt__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ilt_ v_N sx.U i_1 i_2 (uN.mk_uN (nat_of_bool ((proj_uN_0 i_1) < (proj_uN_0 i_2))))
  | fun_ilt__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) :
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_ilt_ v_N sx.S i_1 i_2 (uN.mk_uN (nat_of_bool (var_0 < var_1)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:127.6-127.11 -/
theorem ilt__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) :
  fun_ilt_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = var_0 →
  wf_uN 32 ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:126.1-126.33 -/
def ine_ (v_N : N) (v_iN : iN) (iN_0 : iN) : u32 :=
  uN.mk_uN (nat_of_bool (v_iN != iN_0))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:126.6-126.11 -/
theorem ine__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (ine_ v_N v_iN iN_0) →
  wf_uN 32 ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 -/
inductive fun_relop_ : numtype → relop_ → num_ → num_ → num_ → Prop where
  | fun_relop__case_0 (iN_1 : uN) (iN_2 : uN) : fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 relop_Inn.EQ) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 (ieq_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2))
  | fun_relop__case_1 (iN_1 : uN) (iN_2 : uN) : fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 relop_Inn.EQ) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 (ieq_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2))
  | fun_relop__case_2 (iN_1 : uN) (iN_2 : uN) : fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 relop_Inn.NE) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 (ine_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2))
  | fun_relop__case_3 (iN_1 : uN) (iN_2 : uN) : fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 relop_Inn.NE) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 (ine_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2))
  | fun_relop__case_4 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) :
    fun_ilt_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.LT v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_5 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) :
    fun_ilt_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.LT v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_6 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) :
    fun_igt_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.GT v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_7 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) :
    fun_igt_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.GT v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_8 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) :
    fun_ile_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.LE v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_9 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) :
    fun_ile_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.LE v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_10 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) :
    fun_ige_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.GE v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_11 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) :
    fun_ige_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.GE v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_12 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.EQ) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (feq_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_13 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.EQ) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (feq_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_14 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.NE) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (fne_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_15 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.NE) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (fne_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_16 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.LT) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (flt_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_17 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.LT) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (flt_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_18 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.GT) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (fgt_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_19 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.GT) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (fgt_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_20 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.LE) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (fle_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_21 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.LE) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (fle_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_22 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.GE) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (fge_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_23 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.GE) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (fge_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:50.6-50.13 -/
theorem relop__is_wf (v_numtype : numtype) (v_relop_ : relop_) (v_num_ : num_) (num__0 : num_) (ret_val : num_) (var_0 : num_) :
  fun_relop_ v_numtype v_relop_ v_num_ num__0 var_0 →
  wf_relop_ v_numtype v_relop_ →
  wf_num_ v_numtype v_num_ →
  wf_num_ v_numtype num__0 →
  ret_val = var_0 →
  wf_num_ numtype.I32 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:61.1-61.90 -/
opaque convert__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:61.6-61.16 -/
theorem convert___is_wf (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : fN) :
  wf_uN v_M v_iN →
  ret_val = (convert__ v_M v_N v_sx v_iN) →
  wf_fN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:59.1-59.36 -/
opaque demote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:59.6-59.15 -/
theorem demote___is_wf (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_M v_fN →
  ret_val_lst = (demote__ v_M v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:60.1-60.37 -/
opaque promote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:60.6-60.16 -/
theorem promote___is_wf (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
  wf_fN v_M v_fN →
  ret_val_lst = (promote__ v_M v_N v_fN) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:63.1-63.76 -/
opaque reinterpret__ (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) : num_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:63.6-63.20 -/
theorem reinterpret___is_wf (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) (ret_val : num_) :
  wf_num_ numtype_1 v_num_ →
  ret_val = (reinterpret__ numtype_1 numtype_2 v_num_) →
  wf_num_ numtype_2 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:57.1-57.88 -/
opaque trunc__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:57.6-57.14 -/
theorem trunc___is_wf (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) :
  wf_fN v_M v_fN →
  ret_val_opt = (trunc__ v_M v_N v_sx v_fN) →
  Forall (fun (ret_val_elem : iN) => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:58.1-58.93 -/
opaque trunc_sat__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:58.6-58.18 -/
theorem trunc_sat___is_wf (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) :
  wf_fN v_M v_fN →
  ret_val_opt = (trunc_sat__ v_M v_N v_sx v_fN) →
  Forall (fun (ret_val_elem : iN) => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 -/
inductive fun_cvtop__ : numtype → numtype → cvtop__ → num_ → List num_ → Prop where
  | fun_cvtop___case_0 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.I32 (cvtop__.mk_cvtop___0 Inn.I32 Inn.I32 (cvtop__Inn_1_Inn_2.EXTEND v_sx)) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__0 Inn.I32 (extend__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Inn Inn.I32)) v_sx iN_1)]
  | fun_cvtop___case_1 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.I32 (cvtop__.mk_cvtop___0 Inn.I64 Inn.I32 (cvtop__Inn_1_Inn_2.EXTEND v_sx)) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__0 Inn.I32 (extend__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Inn Inn.I32)) v_sx iN_1)]
  | fun_cvtop___case_2 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.I64 (cvtop__.mk_cvtop___0 Inn.I32 Inn.I64 (cvtop__Inn_1_Inn_2.EXTEND v_sx)) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__0 Inn.I64 (extend__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Inn Inn.I64)) v_sx iN_1)]
  | fun_cvtop___case_3 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.I64 (cvtop__.mk_cvtop___0 Inn.I64 Inn.I64 (cvtop__Inn_1_Inn_2.EXTEND v_sx)) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__0 Inn.I64 (extend__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Inn Inn.I64)) v_sx iN_1)]
  | fun_cvtop___case_4 (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.I32 (cvtop__.mk_cvtop___0 Inn.I32 Inn.I32 cvtop__Inn_1_Inn_2.WRAP) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__0 Inn.I32 (wrap__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Inn Inn.I32)) iN_1)]
  | fun_cvtop___case_5 (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.I32 (cvtop__.mk_cvtop___0 Inn.I64 Inn.I32 cvtop__Inn_1_Inn_2.WRAP) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__0 Inn.I32 (wrap__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Inn Inn.I32)) iN_1)]
  | fun_cvtop___case_6 (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.I64 (cvtop__.mk_cvtop___0 Inn.I32 Inn.I64 cvtop__Inn_1_Inn_2.WRAP) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__0 Inn.I64 (wrap__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Inn Inn.I64)) iN_1)]
  | fun_cvtop___case_7 (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.I64 (cvtop__.mk_cvtop___0 Inn.I64 Inn.I64 cvtop__Inn_1_Inn_2.WRAP) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__0 Inn.I64 (wrap__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Inn Inn.I64)) iN_1)]
  | fun_cvtop___case_8 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F32 Inn.I32 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)) (num_.mk_num__1 Fnn.F32 fN_1) (list_ num_ (OMap (fun (iter_0_33_elem : iN) => num_.mk_num__0 Inn.I32 iter_0_33_elem) (trunc__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Inn Inn.I32)) v_sx fN_1)))
  | fun_cvtop___case_9 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F64 Inn.I32 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)) (num_.mk_num__1 Fnn.F64 fN_1) (list_ num_ (OMap (fun (iter_0_34_elem : iN) => num_.mk_num__0 Inn.I32 iter_0_34_elem) (trunc__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Inn Inn.I32)) v_sx fN_1)))
  | fun_cvtop___case_10 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F32 Inn.I64 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)) (num_.mk_num__1 Fnn.F32 fN_1) (list_ num_ (OMap (fun (iter_0_35_elem : iN) => num_.mk_num__0 Inn.I64 iter_0_35_elem) (trunc__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Inn Inn.I64)) v_sx fN_1)))
  | fun_cvtop___case_11 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F64 Inn.I64 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)) (num_.mk_num__1 Fnn.F64 fN_1) (list_ num_ (OMap (fun (iter_0_36_elem : iN) => num_.mk_num__0 Inn.I64 iter_0_36_elem) (trunc__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Inn Inn.I64)) v_sx fN_1)))
  | fun_cvtop___case_12 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F32 Inn.I32 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)) (num_.mk_num__1 Fnn.F32 fN_1) (list_ num_ (OMap (fun (iter_0_37_elem : iN) => num_.mk_num__0 Inn.I32 iter_0_37_elem) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Inn Inn.I32)) v_sx fN_1)))
  | fun_cvtop___case_13 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F64 Inn.I32 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)) (num_.mk_num__1 Fnn.F64 fN_1) (list_ num_ (OMap (fun (iter_0_38_elem : iN) => num_.mk_num__0 Inn.I32 iter_0_38_elem) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Inn Inn.I32)) v_sx fN_1)))
  | fun_cvtop___case_14 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F32 Inn.I64 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)) (num_.mk_num__1 Fnn.F32 fN_1) (list_ num_ (OMap (fun (iter_0_39_elem : iN) => num_.mk_num__0 Inn.I64 iter_0_39_elem) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Inn Inn.I64)) v_sx fN_1)))
  | fun_cvtop___case_15 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F64 Inn.I64 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)) (num_.mk_num__1 Fnn.F64 fN_1) (list_ num_ (OMap (fun (iter_0_40_elem : iN) => num_.mk_num__0 Inn.I64 iter_0_40_elem) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Inn Inn.I64)) v_sx fN_1)))
  | fun_cvtop___case_16 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.F32 (cvtop__.mk_cvtop___1 Inn.I32 Fnn.F32 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__1 Fnn.F32 (convert__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Fnn Fnn.F32)) v_sx iN_1)]
  | fun_cvtop___case_17 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.F32 (cvtop__.mk_cvtop___1 Inn.I64 Fnn.F32 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__1 Fnn.F32 (convert__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Fnn Fnn.F32)) v_sx iN_1)]
  | fun_cvtop___case_18 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.F64 (cvtop__.mk_cvtop___1 Inn.I32 Fnn.F64 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__1 Fnn.F64 (convert__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Fnn Fnn.F64)) v_sx iN_1)]
  | fun_cvtop___case_19 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.F64 (cvtop__.mk_cvtop___1 Inn.I64 Fnn.F64 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__1 Fnn.F64 (convert__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Fnn Fnn.F64)) v_sx iN_1)]
  | fun_cvtop___case_20 (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.F32 (cvtop__.mk_cvtop___3 Fnn.F32 Fnn.F32 cvtop__Fnn_1_Fnn_2.PROMOTE) (num_.mk_num__1 Fnn.F32 fN_1) (Map (fun (iter_0_41_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_41_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F32)) fN_1))
  | fun_cvtop___case_21 (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.F32 (cvtop__.mk_cvtop___3 Fnn.F64 Fnn.F32 cvtop__Fnn_1_Fnn_2.PROMOTE) (num_.mk_num__1 Fnn.F64 fN_1) (Map (fun (iter_0_42_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_42_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F32)) fN_1))
  | fun_cvtop___case_22 (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.F64 (cvtop__.mk_cvtop___3 Fnn.F32 Fnn.F64 cvtop__Fnn_1_Fnn_2.PROMOTE) (num_.mk_num__1 Fnn.F32 fN_1) (Map (fun (iter_0_43_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_43_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F64)) fN_1))
  | fun_cvtop___case_23 (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.F64 (cvtop__.mk_cvtop___3 Fnn.F64 Fnn.F64 cvtop__Fnn_1_Fnn_2.PROMOTE) (num_.mk_num__1 Fnn.F64 fN_1) (Map (fun (iter_0_44_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_44_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F64)) fN_1))
  | fun_cvtop___case_24 (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.F32 (cvtop__.mk_cvtop___3 Fnn.F32 Fnn.F32 cvtop__Fnn_1_Fnn_2.DEMOTE) (num_.mk_num__1 Fnn.F32 fN_1) (Map (fun (iter_0_45_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_45_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F32)) fN_1))
  | fun_cvtop___case_25 (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.F32 (cvtop__.mk_cvtop___3 Fnn.F64 Fnn.F32 cvtop__Fnn_1_Fnn_2.DEMOTE) (num_.mk_num__1 Fnn.F64 fN_1) (Map (fun (iter_0_46_elem : fN) => num_.mk_num__1 Fnn.F32 iter_0_46_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F32)) fN_1))
  | fun_cvtop___case_26 (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.F64 (cvtop__.mk_cvtop___3 Fnn.F32 Fnn.F64 cvtop__Fnn_1_Fnn_2.DEMOTE) (num_.mk_num__1 Fnn.F32 fN_1) (Map (fun (iter_0_47_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_47_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F64)) fN_1))
  | fun_cvtop___case_27 (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.F64 (cvtop__.mk_cvtop___3 Fnn.F64 Fnn.F64 cvtop__Fnn_1_Fnn_2.DEMOTE) (num_.mk_num__1 Fnn.F64 fN_1) (Map (fun (iter_0_48_elem : fN) => num_.mk_num__1 Fnn.F64 iter_0_48_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F64)) fN_1))
  | fun_cvtop___case_28 (iN_1 : uN) :
    (size (valtype_Inn Inn.I32)) ≠ none →
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (Option.get! (size (valtype_Inn Inn.I32))) = (Option.get! (size (valtype_Fnn Fnn.F32))) →
    fun_cvtop__ numtype.I32 numtype.F32 (cvtop__.mk_cvtop___1 Inn.I32 Fnn.F32 cvtop__Inn_1_Fnn_2.REINTERPRET) (num_.mk_num__0 Inn.I32 iN_1) [reinterpret__ (numtype_Inn Inn.I32) (numtype_Fnn Fnn.F32) (num_.mk_num__0 Inn.I32 iN_1)]
  | fun_cvtop___case_29 (iN_1 : uN) :
    (size (valtype_Inn Inn.I64)) ≠ none →
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (Option.get! (size (valtype_Inn Inn.I64))) = (Option.get! (size (valtype_Fnn Fnn.F32))) →
    fun_cvtop__ numtype.I64 numtype.F32 (cvtop__.mk_cvtop___1 Inn.I64 Fnn.F32 cvtop__Inn_1_Fnn_2.REINTERPRET) (num_.mk_num__0 Inn.I64 iN_1) [reinterpret__ (numtype_Inn Inn.I64) (numtype_Fnn Fnn.F32) (num_.mk_num__0 Inn.I64 iN_1)]
  | fun_cvtop___case_30 (iN_1 : uN) :
    (size (valtype_Inn Inn.I32)) ≠ none →
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (Option.get! (size (valtype_Inn Inn.I32))) = (Option.get! (size (valtype_Fnn Fnn.F64))) →
    fun_cvtop__ numtype.I32 numtype.F64 (cvtop__.mk_cvtop___1 Inn.I32 Fnn.F64 cvtop__Inn_1_Fnn_2.REINTERPRET) (num_.mk_num__0 Inn.I32 iN_1) [reinterpret__ (numtype_Inn Inn.I32) (numtype_Fnn Fnn.F64) (num_.mk_num__0 Inn.I32 iN_1)]
  | fun_cvtop___case_31 (iN_1 : uN) :
    (size (valtype_Inn Inn.I64)) ≠ none →
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (Option.get! (size (valtype_Inn Inn.I64))) = (Option.get! (size (valtype_Fnn Fnn.F64))) →
    fun_cvtop__ numtype.I64 numtype.F64 (cvtop__.mk_cvtop___1 Inn.I64 Fnn.F64 cvtop__Inn_1_Fnn_2.REINTERPRET) (num_.mk_num__0 Inn.I64 iN_1) [reinterpret__ (numtype_Inn Inn.I64) (numtype_Fnn Fnn.F64) (num_.mk_num__0 Inn.I64 iN_1)]
  | fun_cvtop___case_32 (fN_1 : fN) :
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (size (valtype_Inn Inn.I32)) ≠ none →
    (Option.get! (size (valtype_Fnn Fnn.F32))) = (Option.get! (size (valtype_Inn Inn.I32))) →
    fun_cvtop__ numtype.F32 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F32 Inn.I32 cvtop__Fnn_1_Inn_2.REINTERPRET) (num_.mk_num__1 Fnn.F32 fN_1) [reinterpret__ (numtype_Fnn Fnn.F32) (numtype_Inn Inn.I32) (num_.mk_num__1 Fnn.F32 fN_1)]
  | fun_cvtop___case_33 (fN_1 : fN) :
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (size (valtype_Inn Inn.I32)) ≠ none →
    (Option.get! (size (valtype_Fnn Fnn.F64))) = (Option.get! (size (valtype_Inn Inn.I32))) →
    fun_cvtop__ numtype.F64 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F64 Inn.I32 cvtop__Fnn_1_Inn_2.REINTERPRET) (num_.mk_num__1 Fnn.F64 fN_1) [reinterpret__ (numtype_Fnn Fnn.F64) (numtype_Inn Inn.I32) (num_.mk_num__1 Fnn.F64 fN_1)]
  | fun_cvtop___case_34 (fN_1 : fN) :
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (size (valtype_Inn Inn.I64)) ≠ none →
    (Option.get! (size (valtype_Fnn Fnn.F32))) = (Option.get! (size (valtype_Inn Inn.I64))) →
    fun_cvtop__ numtype.F32 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F32 Inn.I64 cvtop__Fnn_1_Inn_2.REINTERPRET) (num_.mk_num__1 Fnn.F32 fN_1) [reinterpret__ (numtype_Fnn Fnn.F32) (numtype_Inn Inn.I64) (num_.mk_num__1 Fnn.F32 fN_1)]
  | fun_cvtop___case_35 (fN_1 : fN) :
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (size (valtype_Inn Inn.I64)) ≠ none →
    (Option.get! (size (valtype_Fnn Fnn.F64))) = (Option.get! (size (valtype_Inn Inn.I64))) →
    fun_cvtop__ numtype.F64 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F64 Inn.I64 cvtop__Fnn_1_Inn_2.REINTERPRET) (num_.mk_num__1 Fnn.F64 fN_1) [reinterpret__ (numtype_Fnn Fnn.F64) (numtype_Inn Inn.I64) (num_.mk_num__1 Fnn.F64 fN_1)]


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:52.6-52.14 -/
theorem cvtop___is_wf (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop__ : cvtop__) (v_num_ : num_) (ret_val_lst : List num_) (var_0 : List num_) :
  fun_cvtop__ numtype_1 numtype_2 v_cvtop__ v_num_ var_0 →
  wf_cvtop__ numtype_1 numtype_2 v_cvtop__ →
  wf_num_ numtype_1 v_num_ →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : num_) => wf_num_ numtype_2 ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:62.1-62.87 -/
opaque narrow__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:62.6-62.15 -/
theorem narrow___is_wf (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN) :
  wf_uN v_M v_iN →
  ret_val = (narrow__ v_M v_N v_sx v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:76.1-76.102 -/
opaque ibits_ (v_N : N) (v_iN : iN) : List bit := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:76.6-76.13 -/
theorem ibits__is_wf (v_N : N) (v_iN : iN) (ret_val_lst : List bit) :
  wf_uN v_N v_iN →
  ret_val_lst = (ibits_ v_N v_iN) →
  Forall (fun (ret_val_elem : bit) => wf_bit ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:77.1-77.102 -/
opaque fbits_ (v_N : N) (v_fN : fN) : List bit := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:77.6-77.13 -/
theorem fbits__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List bit) :
  wf_fN v_N v_fN →
  ret_val_lst = (fbits_ v_N v_fN) →
  Forall (fun (ret_val_elem : bit) => wf_bit ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:78.1-78.103 -/
opaque ibytes_ (v_N : N) (v_iN : iN) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:78.6-78.14 -/
theorem ibytes__is_wf (v_N : N) (v_iN : iN) (ret_val_lst : List byte) :
  wf_uN v_N v_iN →
  ret_val_lst = (ibytes_ v_N v_iN) →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:79.1-79.103 -/
opaque fbytes_ (v_N : N) (v_fN : fN) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:79.6-79.14 -/
theorem fbytes__is_wf (v_N : N) (v_fN : fN) (ret_val_lst : List byte) :
  wf_fN v_N v_fN →
  ret_val_lst = (fbytes_ v_N v_fN) →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:80.1-80.103 -/
opaque nbytes_ (v_numtype : numtype) (v_num_ : num_) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:80.6-80.14 -/
theorem nbytes__is_wf (v_numtype : numtype) (v_num_ : num_) (ret_val_lst : List byte) :
  wf_num_ v_numtype v_num_ →
  ret_val_lst = (nbytes_ v_numtype v_num_) →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:81.1-81.103 -/
opaque vbytes_ (v_vectype : vectype) (v_vec_ : vec_) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:81.6-81.14 -/
theorem vbytes__is_wf (v_vectype : vectype) (v_vec_ : vec_) (ret_val_lst : List byte) :
  (size (valtype_vectype v_vectype)) ≠ none →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
  ret_val_lst = (vbytes_ v_vectype v_vec_) →
  Forall (fun (ret_val_elem : byte) => wf_byte ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:83.1-83.85 -/
opaque inv_ibits_ (v_N : N) (var_0_lst : List bit) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:83.6-83.17 -/
theorem inv_ibits__is_wf (v_N : N) (var_0_lst : List bit) (ret_val : iN) :
  Forall (fun (var_0_elem : bit) => wf_bit var_0_elem) var_0_lst →
  ret_val = (inv_ibits_ v_N var_0_lst) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:84.1-84.85 -/
opaque inv_fbits_ (v_N : N) (var_0_lst : List bit) : fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:84.6-84.17 -/
theorem inv_fbits__is_wf (v_N : N) (var_0_lst : List bit) (ret_val : fN) :
  Forall (fun (var_0_elem : bit) => wf_bit var_0_elem) var_0_lst →
  ret_val = (inv_fbits_ v_N var_0_lst) →
  wf_fN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:85.1-85.86 -/
opaque inv_ibytes_ (v_N : N) (var_0_lst : List byte) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:85.6-85.18 -/
theorem inv_ibytes__is_wf (v_N : N) (var_0_lst : List byte) (ret_val : iN) :
  Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst →
  ret_val = (inv_ibytes_ v_N var_0_lst) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:86.1-86.86 -/
opaque inv_fbytes_ (v_N : N) (var_0_lst : List byte) : fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:86.6-86.18 -/
theorem inv_fbytes__is_wf (v_N : N) (var_0_lst : List byte) (ret_val : fN) :
  Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst →
  ret_val = (inv_fbytes_ v_N var_0_lst) →
  wf_fN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:87.1-87.84 -/
opaque inv_nbytes_ (v_numtype : numtype) (var_0_lst : List byte) : num_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:87.6-87.18 -/
theorem inv_nbytes__is_wf (v_numtype : numtype) (var_0_lst : List byte) (ret_val : num_) :
  Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst →
  ret_val = (inv_nbytes_ v_numtype var_0_lst) →
  wf_num_ v_numtype ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:88.1-88.84 -/
opaque inv_vbytes_ (v_vectype : vectype) (var_0_lst : List byte) : vec_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:88.6-88.18 -/
theorem inv_vbytes__is_wf (v_vectype : vectype) (var_0_lst : List byte) (ret_val : vec_) :
  Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst →
  ret_val = (inv_vbytes_ v_vectype var_0_lst) →
  (size (valtype_vectype v_vectype)) ≠ none →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:110.1-110.29 -/
opaque inot_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:110.6-110.12 -/
theorem inot__is_wf (v_N : N) (v_iN : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  ret_val = (inot_ v_N v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:111.1-111.29 -/
opaque irev_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:111.6-111.12 -/
theorem irev__is_wf (v_N : N) (v_iN : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  ret_val = (irev_ v_N v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:113.1-113.39 -/
opaque iandnot_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:113.6-113.15 -/
theorem iandnot__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (iandnot_ v_N v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:124.1-124.27 -/
def inez_ (v_N : N) (v_iN : iN) : u32 :=
  uN.mk_uN (nat_of_bool ((proj_uN_0 v_iN) != 0))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:124.6-124.12 -/
theorem inez__is_wf (v_N : N) (v_iN : iN) (ret_val : u32) :
  wf_uN v_N v_iN →
  ret_val = (inez_ v_N v_iN) →
  wf_uN 32 ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:131.1-131.49 -/
opaque ibitselect_ (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:131.6-131.18 -/
theorem ibitselect__is_wf (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  wf_uN v_N iN_1 →
  ret_val = (ibitselect_ v_N v_iN iN_0 iN_1) →
  wf_uN v_N ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:133.1-133.29 -/
def ineg_ (v_N : N) (v_iN : iN) : iN :=
  uN.mk_uN (Int.toNat ((((2 ^ v_N) : Int) - ((proj_uN_0 v_iN) : Int)) % ((2 ^ v_N) : Int)))

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:133.6-133.12 -/
theorem ineg__is_wf (v_N : N) (v_iN : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  ret_val = (ineg_ v_N v_iN) →
  wf_uN v_N ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 -/
inductive fun_iabs_ : N → iN → iN → Prop where
  | fun_iabs__case_0 (v_N : Nat) (i_1 : uN) (var_0 : Int) :
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_iabs_ v_N i_1 (if
      var_0 ≥ (0 : Int)
    then
      i_1
    else
      ineg_ v_N i_1)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:132.6-132.12 -/
theorem iabs__is_wf (v_N : N) (v_iN : iN) (ret_val : iN) (var_0 : iN) :
  fun_iabs_ v_N v_iN var_0 →
  wf_uN v_N v_iN →
  ret_val = var_0 →
  wf_uN v_N ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 -/
inductive fun_imin_ : N → sx → iN → iN → iN → Prop where
  | fun_imin__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) :
    (proj_uN_0 i_1) ≤ (proj_uN_0 i_2) →
    fun_imin_ v_N sx.U i_1 i_2 i_1
  | fun_imin__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) :
    (proj_uN_0 i_1) > (proj_uN_0 i_2) →
    fun_imin_ v_N sx.U i_1 i_2 i_2
  | fun_imin__case_2 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) :
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_imin_ v_N sx.S i_1 i_2 (if
      var_0 ≤ var_1
    then
      i_1
    else
      i_2)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:134.6-134.12 -/
theorem imin__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN) :
  fun_imin_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = var_0 →
  wf_uN v_N ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 -/
inductive fun_imax_ : N → sx → iN → iN → iN → Prop where
  | fun_imax__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) :
    (proj_uN_0 i_1) ≥ (proj_uN_0 i_2) →
    fun_imax_ v_N sx.U i_1 i_2 i_1
  | fun_imax__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) :
    (proj_uN_0 i_1) < (proj_uN_0 i_2) →
    fun_imax_ v_N sx.U i_1 i_2 i_2
  | fun_imax__case_2 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) :
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_imax_ v_N sx.S i_1 i_2 (if
      var_0 ≥ var_1
    then
      i_1
    else
      i_2)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:135.6-135.12 -/
theorem imax__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN) :
  fun_imax_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = var_0 →
  wf_uN v_N ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 -/
inductive fun_iadd_sat_ : N → sx → iN → iN → iN → Prop where
  | fun_iadd_sat__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_iadd_sat_ v_N sx.U i_1 i_2 (uN.mk_uN (sat_u_ v_N (((proj_uN_0 i_1) + (proj_uN_0 i_2)) : Int)))
  | fun_iadd_sat__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Int) (var_1 : Int) (var_0 : Nat) :
    fun_signed_ v_N (proj_uN_0 i_2) var_2 →
    fun_signed_ v_N (proj_uN_0 i_1) var_1 →
    fun_inv_signed_ v_N (sat_s_ v_N (var_1 + var_2)) var_0 →
    fun_iadd_sat_ v_N sx.S i_1 i_2 (uN.mk_uN var_0)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:136.6-136.16 -/
theorem iadd_sat__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN) :
  fun_iadd_sat_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = var_0 →
  wf_uN v_N ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 -/
inductive fun_isub_sat_ : N → sx → iN → iN → iN → Prop where
  | fun_isub_sat__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_isub_sat_ v_N sx.U i_1 i_2 (uN.mk_uN (sat_u_ v_N (((proj_uN_0 i_1) : Int) - ((proj_uN_0 i_2) : Int))))
  | fun_isub_sat__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Int) (var_1 : Int) (var_0 : Nat) :
    fun_signed_ v_N (proj_uN_0 i_2) var_2 →
    fun_signed_ v_N (proj_uN_0 i_1) var_1 →
    fun_inv_signed_ v_N (sat_s_ v_N (var_1 - var_2)) var_0 →
    fun_isub_sat_ v_N sx.S i_1 i_2 (uN.mk_uN var_0)


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:137.6-137.16 -/
theorem isub_sat__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN) :
  fun_isub_sat_ v_N v_sx v_iN iN_0 var_0 →
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = var_0 →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:138.1-138.82 -/
opaque iavgr_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:138.6-138.13 -/
theorem iavgr__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (iavgr_ v_N v_sx v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:139.1-139.90 -/
opaque iq15mulr_sat_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:139.6-139.20 -/
theorem iq15mulr_sat__is_wf (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
  wf_uN v_N v_iN →
  wf_uN v_N iN_0 →
  ret_val = (iq15mulr_sat_ v_N v_sx v_iN iN_0) →
  wf_uN v_N ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:221.1-221.38 -/
opaque fpmin_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:221.6-221.13 -/
theorem fpmin__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fpmin_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:222.1-222.38 -/
opaque fpmax_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:222.6-222.13 -/
theorem fpmax__is_wf (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
  wf_fN v_N v_fN →
  wf_fN v_N fN_0 →
  ret_val_lst = (fpmax_ v_N v_fN fN_0) →
  Forall (fun (ret_val_elem : fN) => wf_fN v_N ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:323.1-324.27 -/
def packnum_ (v_lanetype : lanetype) (v_num_ : num_) : lane_ :=
  match v_lanetype, v_num_ with
  | lanetype.I32, _ => lane_.mk_lane__0 numtype.I32 v_num_
  | lanetype.I64, _ => lane_.mk_lane__0 numtype.I64 v_num_
  | lanetype.F32, _ => lane_.mk_lane__0 numtype.F32 v_num_
  | lanetype.F64, _ => lane_.mk_lane__0 numtype.F64 v_num_
  | lanetype.I8, num_.mk_num__0 Inn.I32 c => lane_.mk_lane__1 packtype.I8 (wrap__ (Option.get! (size (valtype_numtype (unpack (lanetype_packtype packtype.I8))))) (psize packtype.I8) c)
  | lanetype.I16, num_.mk_num__0 Inn.I32 c => lane_.mk_lane__1 packtype.I16 (wrap__ (Option.get! (size (valtype_numtype (unpack (lanetype_packtype packtype.I16))))) (psize packtype.I16) c)
  | _, _ => Inhabited.default

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:323.6-323.15 -/
theorem packnum__is_wf (v_lanetype : lanetype) (v_num_ : num_) (ret_val : lane_) :
  wf_num_ (unpack v_lanetype) v_num_ →
  ret_val = (packnum_ v_lanetype v_num_) →
  wf_lane_ v_lanetype ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:328.1-329.29 -/
def unpacknum_ (v_lanetype : lanetype) (v_lane_ : lane_) : num_ :=
  match v_lanetype, v_lane_ with
  | lanetype.I32, lane_.mk_lane__0 numtype.I32 c => c
  | lanetype.I64, lane_.mk_lane__0 numtype.I64 c => c
  | lanetype.F32, lane_.mk_lane__0 numtype.F32 c => c
  | lanetype.F64, lane_.mk_lane__0 numtype.F64 c => c
  | lanetype.I8, lane_.mk_lane__1 packtype.I8 c => num_.mk_num__0 Inn.I32 (extend__ (psize packtype.I8) (Option.get! (size (valtype_numtype (unpack (lanetype_packtype packtype.I8))))) sx.U c)
  | lanetype.I16, lane_.mk_lane__1 packtype.I16 c => num_.mk_num__0 Inn.I32 (extend__ (psize packtype.I16) (Option.get! (size (valtype_numtype (unpack (lanetype_packtype packtype.I16))))) sx.U c)
  | _, _ => Inhabited.default

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:328.6-328.17 -/
theorem unpacknum__is_wf (v_lanetype : lanetype) (v_lane_ : lane_) (ret_val : num_) :
  wf_lane_ v_lanetype v_lane_ →
  ret_val = (unpacknum_ v_lanetype v_lane_) →
  wf_num_ (unpack v_lanetype) ret_val :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:336.1-336.84 -/
opaque lanes_ (v_shape : shape) (v_vec_ : vec_) : List lane_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:336.6-336.13 -/
theorem lanes__is_wf (v_shape : shape) (v_vec_ : vec_) (ret_val_lst : List lane_) :
  wf_shape v_shape →
  wf_uN 128 v_vec_ →
  ret_val_lst = (lanes_ v_shape v_vec_) →
  Forall (fun (ret_val_elem : lane_) => wf_lane_ (fun_lanetype v_shape) ret_val_elem) ret_val_lst :=
  sorry

/- Axiom Definition at: ../specification/wasm-2.0/3-numerics.spectec:339.1-340.36 -/
opaque inv_lanes_ (v_shape : shape) (var_0_lst : List lane_) : vec_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:339.6-339.17 -/
theorem inv_lanes__is_wf (v_shape : shape) (var_0_lst : List lane_) (ret_val : vec_) :
  wf_shape v_shape →
  Forall (fun (var_0_elem : lane_) => wf_lane_ (fun_lanetype v_shape) var_0_elem) var_0_lst →
  ret_val = (inv_lanes_ v_shape var_0_lst) →
  wf_uN 128 ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:343.1-343.28 -/
def zeroop (v_vcvtop : vcvtop) : Option zero :=
  match v_vcvtop with
  | vcvtop.EXTEND v_half v_sx => none
  | vcvtop.CONVERT half_opt v_sx => none
  | vcvtop.TRUNC_SAT v_sx zero_opt => zero_opt
  | vcvtop.DEMOTE v_zero => some v_zero
  | vcvtop.PROMOTELOW => none

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:350.1-350.28 -/
def halfop (v_vcvtop : vcvtop) : Option half :=
  match v_vcvtop with
  | vcvtop.EXTEND v_half v_sx => some v_half
  | vcvtop.CONVERT half_opt v_sx => half_opt
  | vcvtop.TRUNC_SAT v_sx zero_opt => none
  | vcvtop.DEMOTE v_zero => none
  | vcvtop.PROMOTELOW => some half.LOW

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:357.1-357.32 -/
def fun_half (v_half : half) (nat : Nat) (nat_0 : Nat) : Nat :=
  match v_half with
  | half.LOW => nat
  | half.HIGH => nat_0

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:362.1-363.28 -/
def vvunop_ (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) : vec_ :=
  match v_vectype, v_vvunop with
  | vectype.V128, vvunop.NOT => inot_ (Option.get! (size valtype.V128)) v_vec_

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:362.6-362.14 -/
theorem vvunop__is_wf (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) (ret_val : vec_) :
  (size (valtype_vectype v_vectype)) ≠ none →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
  ret_val = (vvunop_ v_vectype v_vvunop v_vec_) →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:364.1-365.31 -/
def vvbinop_ (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) : vec_ :=
  match v_vectype, v_vvbinop with
  | vectype.V128, vvbinop.AND => iand_ (Option.get! (size valtype.V128)) v_vec_ vec__0
  | vectype.V128, vvbinop.ANDNOT => iandnot_ (Option.get! (size valtype.V128)) v_vec_ vec__0
  | vectype.V128, vvbinop.OR => ior_ (Option.get! (size valtype.V128)) v_vec_ vec__0
  | vectype.V128, vvbinop.XOR => ixor_ (Option.get! (size valtype.V128)) v_vec_ vec__0

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:364.6-364.15 -/
theorem vvbinop__is_wf (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) :
  (size (valtype_vectype v_vectype)) ≠ none →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) vec__0 →
  ret_val = (vvbinop_ v_vectype v_vvbinop v_vec_ vec__0) →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:366.1-367.34 -/
def vvternop_ (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) : vec_ :=
  match v_vectype, v_vvternop with
  | vectype.V128, vvternop.BITSELECT => ibitselect_ (Option.get! (size valtype.V128)) v_vec_ vec__0 vec__1

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:366.6-366.16 -/
theorem vvternop__is_wf (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val : vec_) :
  (size (valtype_vectype v_vectype)) ≠ none →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) vec__0 →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) vec__1 →
  ret_val = (vvternop_ v_vectype v_vvternop v_vec_ vec__0 vec__1) →
  wf_uN (Option.get! (size (valtype_vectype v_vectype))) ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 -/
inductive fun_vunop_ : shape → vunop_ → vec_ → List vec_ → Prop where
  | fun_vunop__case_0 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    Forall (fun (lane_1_3_elem : lane_) => (proj_lane__2 lane_1_3_elem) ≠ none) lane_1_lst →
    Forall₂ (fun (var_1_elem : uN) (lane_1_3_elem : lane_) => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_3_elem)) var_1_elem) var_1_lst lane_1_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    Forall (fun (lane_1_2_elem : lane_) => (proj_lane__2 lane_1_2_elem) ≠ none) lane_1_lst →
    Forall₂ (fun (var_0_elem : uN) (lane_1_2_elem : lane_) => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_2_elem)) var_0_elem) var_0_lst lane_1_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_N.ABS) v128_1 [v128]
  | fun_vunop__case_1 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    Forall (fun (lane_1_6_elem : lane_) => (proj_lane__2 lane_1_6_elem) ≠ none) lane_1_lst →
    Forall₂ (fun (var_1_elem : uN) (lane_1_6_elem : lane_) => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_6_elem)) var_1_elem) var_1_lst lane_1_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    Forall (fun (lane_1_5_elem : lane_) => (proj_lane__2 lane_1_5_elem) ≠ none) lane_1_lst →
    Forall₂ (fun (var_0_elem : uN) (lane_1_5_elem : lane_) => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_5_elem)) var_0_elem) var_0_lst lane_1_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_N.ABS) v128_1 [v128]
  | fun_vunop__case_2 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    Forall (fun (lane_1_9_elem : lane_) => (proj_lane__2 lane_1_9_elem) ≠ none) lane_1_lst →
    Forall₂ (fun (var_1_elem : uN) (lane_1_9_elem : lane_) => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_9_elem)) var_1_elem) var_1_lst lane_1_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    Forall (fun (lane_1_8_elem : lane_) => (proj_lane__2 lane_1_8_elem) ≠ none) lane_1_lst →
    Forall₂ (fun (var_0_elem : uN) (lane_1_8_elem : lane_) => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_8_elem)) var_0_elem) var_0_lst lane_1_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_N.ABS) v128_1 [v128]
  | fun_vunop__case_3 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    Forall (fun (lane_1_12_elem : lane_) => (proj_lane__2 lane_1_12_elem) ≠ none) lane_1_lst →
    Forall₂ (fun (var_1_elem : uN) (lane_1_12_elem : lane_) => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_12_elem)) var_1_elem) var_1_lst lane_1_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    Forall (fun (lane_1_11_elem : lane_) => (proj_lane__2 lane_1_11_elem) ≠ none) lane_1_lst →
    Forall₂ (fun (var_0_elem : uN) (lane_1_11_elem : lane_) => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_11_elem)) var_0_elem) var_0_lst lane_1_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_N.ABS) v128_1 [v128]
  | fun_vunop__case_4 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    Forall (fun (lane_1_14_elem : lane_) => (proj_lane__2 lane_1_14_elem) ≠ none) lane_1_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (lane_1_14_elem : lane_) => lane_.mk_lane__2 Jnn.I32 (ineg_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_14_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_15_elem : lane_) => (proj_lane__2 lane_1_15_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_1_15_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (ineg_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_15_elem))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_N.NEG) v128_1 [v128]
  | fun_vunop__case_5 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    Forall (fun (lane_1_17_elem : lane_) => (proj_lane__2 lane_1_17_elem) ≠ none) lane_1_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (lane_1_17_elem : lane_) => lane_.mk_lane__2 Jnn.I64 (ineg_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_17_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_18_elem : lane_) => (proj_lane__2 lane_1_18_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_1_18_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (ineg_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_18_elem))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_N.NEG) v128_1 [v128]
  | fun_vunop__case_6 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    Forall (fun (lane_1_20_elem : lane_) => (proj_lane__2 lane_1_20_elem) ≠ none) lane_1_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (lane_1_20_elem : lane_) => lane_.mk_lane__2 Jnn.I8 (ineg_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_20_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_21_elem : lane_) => (proj_lane__2 lane_1_21_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_1_21_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (ineg_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_21_elem))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_N.NEG) v128_1 [v128]
  | fun_vunop__case_7 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    Forall (fun (lane_1_23_elem : lane_) => (proj_lane__2 lane_1_23_elem) ≠ none) lane_1_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (lane_1_23_elem : lane_) => lane_.mk_lane__2 Jnn.I16 (ineg_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_23_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_24_elem : lane_) => (proj_lane__2 lane_1_24_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_1_24_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (ineg_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_24_elem))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_N.NEG) v128_1 [v128]
  | fun_vunop__case_8 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    Forall (fun (lane_1_26_elem : lane_) => (proj_lane__2 lane_1_26_elem) ≠ none) lane_1_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (lane_1_26_elem : lane_) => lane_.mk_lane__2 Jnn.I32 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_26_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_27_elem : lane_) => (proj_lane__2 lane_1_27_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_1_27_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_27_elem))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_N.POPCNT) v128_1 [v128]
  | fun_vunop__case_9 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    Forall (fun (lane_1_29_elem : lane_) => (proj_lane__2 lane_1_29_elem) ≠ none) lane_1_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (lane_1_29_elem : lane_) => lane_.mk_lane__2 Jnn.I64 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_29_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_30_elem : lane_) => (proj_lane__2 lane_1_30_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_1_30_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_30_elem))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_N.POPCNT) v128_1 [v128]
  | fun_vunop__case_10 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    Forall (fun (lane_1_32_elem : lane_) => (proj_lane__2 lane_1_32_elem) ≠ none) lane_1_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (lane_1_32_elem : lane_) => lane_.mk_lane__2 Jnn.I8 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_32_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_33_elem : lane_) => (proj_lane__2 lane_1_33_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_1_33_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_33_elem))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_N.POPCNT) v128_1 [v128]
  | fun_vunop__case_11 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    Forall (fun (lane_1_35_elem : lane_) => (proj_lane__2 lane_1_35_elem) ≠ none) lane_1_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (lane_1_35_elem : lane_) => lane_.mk_lane__2 Jnn.I16 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_35_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_36_elem : lane_) => (proj_lane__2 lane_1_36_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_1_36_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_36_elem))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_N.POPCNT) v128_1 [v128]
  | fun_vunop__case_12 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_38_elem : lane_) => Map (fun (iter_0_49_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_49_elem)) (fabs_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_38_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_2_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_2_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_39_elem : lane_) => Forall (fun (iter_0_50_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_50_elem))) (fabs_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_39_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.ABS) v128_1 v128_lst
  | fun_vunop__case_13 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_41_elem : lane_) => Map (fun (iter_0_51_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_51_elem)) (fabs_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_41_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_4_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_4_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_42_elem : lane_) => Forall (fun (iter_0_52_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_52_elem))) (fabs_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_42_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.ABS) v128_1 v128_lst
  | fun_vunop__case_14 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_44_elem : lane_) => Map (fun (iter_0_53_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_53_elem)) (fneg_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_44_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_6_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_6_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_45_elem : lane_) => Forall (fun (iter_0_54_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_54_elem))) (fneg_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_45_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.NEG) v128_1 v128_lst
  | fun_vunop__case_15 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_47_elem : lane_) => Map (fun (iter_0_55_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_55_elem)) (fneg_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_47_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_8_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_8_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_48_elem : lane_) => Forall (fun (iter_0_56_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_56_elem))) (fneg_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_48_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.NEG) v128_1 v128_lst
  | fun_vunop__case_16 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_50_elem : lane_) => Map (fun (iter_0_57_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_57_elem)) (fsqrt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_50_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_10_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_10_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_51_elem : lane_) => Forall (fun (iter_0_58_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_58_elem))) (fsqrt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_51_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.SQRT) v128_1 v128_lst
  | fun_vunop__case_17 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_53_elem : lane_) => Map (fun (iter_0_59_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_59_elem)) (fsqrt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_53_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_12_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_12_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_54_elem : lane_) => Forall (fun (iter_0_60_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_60_elem))) (fsqrt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_54_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.SQRT) v128_1 v128_lst
  | fun_vunop__case_18 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_56_elem : lane_) => Map (fun (iter_0_61_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_61_elem)) (fceil_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_56_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_14_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_14_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_57_elem : lane_) => Forall (fun (iter_0_62_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_62_elem))) (fceil_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_57_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.CEIL) v128_1 v128_lst
  | fun_vunop__case_19 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_59_elem : lane_) => Map (fun (iter_0_63_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_63_elem)) (fceil_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_59_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_16_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_16_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_60_elem : lane_) => Forall (fun (iter_0_64_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_64_elem))) (fceil_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_60_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.CEIL) v128_1 v128_lst
  | fun_vunop__case_20 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_62_elem : lane_) => Map (fun (iter_0_65_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_65_elem)) (ffloor_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_62_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_18_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_18_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_63_elem : lane_) => Forall (fun (iter_0_66_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_66_elem))) (ffloor_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_63_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.FLOOR) v128_1 v128_lst
  | fun_vunop__case_21 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_65_elem : lane_) => Map (fun (iter_0_67_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_67_elem)) (ffloor_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_65_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_20_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_20_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_66_elem : lane_) => Forall (fun (iter_0_68_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_68_elem))) (ffloor_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_66_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.FLOOR) v128_1 v128_lst
  | fun_vunop__case_22 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_68_elem : lane_) => Map (fun (iter_0_69_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_69_elem)) (ftrunc_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_68_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_22_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_22_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_69_elem : lane_) => Forall (fun (iter_0_70_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_70_elem))) (ftrunc_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_69_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.TRUNC) v128_1 v128_lst
  | fun_vunop__case_23 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_71_elem : lane_) => Map (fun (iter_0_71_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_71_elem)) (ftrunc_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_71_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_24_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_24_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_72_elem : lane_) => Forall (fun (iter_0_72_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_72_elem))) (ftrunc_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_72_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.TRUNC) v128_1 v128_lst
  | fun_vunop__case_24 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_74_elem : lane_) => Map (fun (iter_0_73_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_73_elem)) (fnearest_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_74_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_26_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_26_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_75_elem : lane_) => Forall (fun (iter_0_74_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_74_elem))) (fnearest_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_75_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.NEAREST) v128_1 v128_lst
  | fun_vunop__case_25 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst = (setproduct_ lane_ (Map (fun (lane_1_77_elem : lane_) => Map (fun (iter_0_75_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_75_elem)) (fnearest_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_77_elem)))))) lane_1_lst)) →
    v128_lst = (Map (fun (lane_lst_28_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_28_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun (lane_1_78_elem : lane_) => Forall (fun (iter_0_76_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_76_elem))) (fnearest_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_78_elem)))))) lane_1_lst →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.NEAREST) v128_1 v128_lst


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:377.6-377.13 -/
theorem vunop__is_wf (v_shape : shape) (v_vunop_ : vunop_) (v_vec_ : vec_) (ret_val_lst : List vec_) (var_0 : List vec_) :
  fun_vunop_ v_shape v_vunop_ v_vec_ var_0 →
  wf_shape v_shape →
  wf_vunop_ v_shape v_vunop_ →
  wf_uN 128 v_vec_ →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : vec_) => wf_uN 128 ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 -/
inductive fun_vbinop_ : shape → vbinop_ → vec_ → vec_ → List vec_ → Prop where
  | fun_vbinop__case_0 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_80_elem : lane_) => (proj_lane__2 lane_1_80_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_2_elem : lane_) => (proj_lane__2 lane_2_2_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_80_elem : lane_) (lane_2_2_elem : lane_) => lane_.mk_lane__2 Jnn.I32 (iadd_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_80_elem)) (Option.get! (proj_lane__2 lane_2_2_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_81_elem : lane_) => (proj_lane__2 lane_1_81_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_3_elem : lane_) => (proj_lane__2 lane_2_3_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_81_elem : lane_) (lane_2_3_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (iadd_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_81_elem)) (Option.get! (proj_lane__2 lane_2_3_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_1 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_83_elem : lane_) => (proj_lane__2 lane_1_83_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_5_elem : lane_) => (proj_lane__2 lane_2_5_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_83_elem : lane_) (lane_2_5_elem : lane_) => lane_.mk_lane__2 Jnn.I64 (iadd_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_83_elem)) (Option.get! (proj_lane__2 lane_2_5_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_84_elem : lane_) => (proj_lane__2 lane_1_84_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_6_elem : lane_) => (proj_lane__2 lane_2_6_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_84_elem : lane_) (lane_2_6_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (iadd_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_84_elem)) (Option.get! (proj_lane__2 lane_2_6_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_2 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_86_elem : lane_) => (proj_lane__2 lane_1_86_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_8_elem : lane_) => (proj_lane__2 lane_2_8_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_86_elem : lane_) (lane_2_8_elem : lane_) => lane_.mk_lane__2 Jnn.I8 (iadd_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_86_elem)) (Option.get! (proj_lane__2 lane_2_8_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_87_elem : lane_) => (proj_lane__2 lane_1_87_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_9_elem : lane_) => (proj_lane__2 lane_2_9_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_87_elem : lane_) (lane_2_9_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (iadd_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_87_elem)) (Option.get! (proj_lane__2 lane_2_9_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_3 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_89_elem : lane_) => (proj_lane__2 lane_1_89_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_11_elem : lane_) => (proj_lane__2 lane_2_11_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_89_elem : lane_) (lane_2_11_elem : lane_) => lane_.mk_lane__2 Jnn.I16 (iadd_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_89_elem)) (Option.get! (proj_lane__2 lane_2_11_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_90_elem : lane_) => (proj_lane__2 lane_1_90_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_12_elem : lane_) => (proj_lane__2 lane_2_12_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_90_elem : lane_) (lane_2_12_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (iadd_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_90_elem)) (Option.get! (proj_lane__2 lane_2_12_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_4 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_92_elem : lane_) => (proj_lane__2 lane_1_92_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_14_elem : lane_) => (proj_lane__2 lane_2_14_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_92_elem : lane_) (lane_2_14_elem : lane_) => lane_.mk_lane__2 Jnn.I32 (isub_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_92_elem)) (Option.get! (proj_lane__2 lane_2_14_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_93_elem : lane_) => (proj_lane__2 lane_1_93_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_15_elem : lane_) => (proj_lane__2 lane_2_15_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_93_elem : lane_) (lane_2_15_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (isub_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_93_elem)) (Option.get! (proj_lane__2 lane_2_15_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_5 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_95_elem : lane_) => (proj_lane__2 lane_1_95_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_17_elem : lane_) => (proj_lane__2 lane_2_17_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_95_elem : lane_) (lane_2_17_elem : lane_) => lane_.mk_lane__2 Jnn.I64 (isub_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_95_elem)) (Option.get! (proj_lane__2 lane_2_17_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_96_elem : lane_) => (proj_lane__2 lane_1_96_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_18_elem : lane_) => (proj_lane__2 lane_2_18_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_96_elem : lane_) (lane_2_18_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (isub_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_96_elem)) (Option.get! (proj_lane__2 lane_2_18_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_6 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_98_elem : lane_) => (proj_lane__2 lane_1_98_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_20_elem : lane_) => (proj_lane__2 lane_2_20_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_98_elem : lane_) (lane_2_20_elem : lane_) => lane_.mk_lane__2 Jnn.I8 (isub_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_98_elem)) (Option.get! (proj_lane__2 lane_2_20_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_99_elem : lane_) => (proj_lane__2 lane_1_99_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_21_elem : lane_) => (proj_lane__2 lane_2_21_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_99_elem : lane_) (lane_2_21_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (isub_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_99_elem)) (Option.get! (proj_lane__2 lane_2_21_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_7 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_101_elem : lane_) => (proj_lane__2 lane_1_101_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_23_elem : lane_) => (proj_lane__2 lane_2_23_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_101_elem : lane_) (lane_2_23_elem : lane_) => lane_.mk_lane__2 Jnn.I16 (isub_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_101_elem)) (Option.get! (proj_lane__2 lane_2_23_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_102_elem : lane_) => (proj_lane__2 lane_1_102_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_24_elem : lane_) => (proj_lane__2 lane_2_24_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_102_elem : lane_) (lane_2_24_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (isub_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_102_elem)) (Option.get! (proj_lane__2 lane_2_24_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_8 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_105_elem : lane_) => (proj_lane__2 lane_1_105_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_27_elem : lane_) => (proj_lane__2 lane_2_27_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_105_elem : lane_) (lane_2_27_elem : lane_) => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_105_elem)) (Option.get! (proj_lane__2 lane_2_27_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_104_elem : lane_) => (proj_lane__2 lane_1_104_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_26_elem : lane_) => (proj_lane__2 lane_2_26_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_104_elem : lane_) (lane_2_26_elem : lane_) => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_104_elem)) (Option.get! (proj_lane__2 lane_2_26_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_N.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_9 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_108_elem : lane_) => (proj_lane__2 lane_1_108_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_30_elem : lane_) => (proj_lane__2 lane_2_30_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_108_elem : lane_) (lane_2_30_elem : lane_) => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_108_elem)) (Option.get! (proj_lane__2 lane_2_30_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_107_elem : lane_) => (proj_lane__2 lane_1_107_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_29_elem : lane_) => (proj_lane__2 lane_2_29_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_107_elem : lane_) (lane_2_29_elem : lane_) => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_107_elem)) (Option.get! (proj_lane__2 lane_2_29_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_N.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_10 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_111_elem : lane_) => (proj_lane__2 lane_1_111_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_33_elem : lane_) => (proj_lane__2 lane_2_33_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_111_elem : lane_) (lane_2_33_elem : lane_) => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_111_elem)) (Option.get! (proj_lane__2 lane_2_33_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_110_elem : lane_) => (proj_lane__2 lane_1_110_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_32_elem : lane_) => (proj_lane__2 lane_2_32_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_110_elem : lane_) (lane_2_32_elem : lane_) => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_110_elem)) (Option.get! (proj_lane__2 lane_2_32_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_N.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_11 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_114_elem : lane_) => (proj_lane__2 lane_1_114_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_36_elem : lane_) => (proj_lane__2 lane_2_36_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_114_elem : lane_) (lane_2_36_elem : lane_) => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_114_elem)) (Option.get! (proj_lane__2 lane_2_36_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_113_elem : lane_) => (proj_lane__2 lane_1_113_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_35_elem : lane_) => (proj_lane__2 lane_2_35_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_113_elem : lane_) (lane_2_35_elem : lane_) => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_113_elem)) (Option.get! (proj_lane__2 lane_2_35_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_N.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_12 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_117_elem : lane_) => (proj_lane__2 lane_1_117_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_39_elem : lane_) => (proj_lane__2 lane_2_39_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_117_elem : lane_) (lane_2_39_elem : lane_) => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_117_elem)) (Option.get! (proj_lane__2 lane_2_39_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_116_elem : lane_) => (proj_lane__2 lane_1_116_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_38_elem : lane_) => (proj_lane__2 lane_2_38_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_116_elem : lane_) (lane_2_38_elem : lane_) => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_116_elem)) (Option.get! (proj_lane__2 lane_2_38_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_N.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_13 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_120_elem : lane_) => (proj_lane__2 lane_1_120_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_42_elem : lane_) => (proj_lane__2 lane_2_42_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_120_elem : lane_) (lane_2_42_elem : lane_) => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_120_elem)) (Option.get! (proj_lane__2 lane_2_42_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_119_elem : lane_) => (proj_lane__2 lane_1_119_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_41_elem : lane_) => (proj_lane__2 lane_2_41_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_119_elem : lane_) (lane_2_41_elem : lane_) => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_119_elem)) (Option.get! (proj_lane__2 lane_2_41_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_N.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_14 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_123_elem : lane_) => (proj_lane__2 lane_1_123_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_45_elem : lane_) => (proj_lane__2 lane_2_45_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_123_elem : lane_) (lane_2_45_elem : lane_) => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_123_elem)) (Option.get! (proj_lane__2 lane_2_45_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_122_elem : lane_) => (proj_lane__2 lane_1_122_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_44_elem : lane_) => (proj_lane__2 lane_2_44_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_122_elem : lane_) (lane_2_44_elem : lane_) => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_122_elem)) (Option.get! (proj_lane__2 lane_2_44_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_N.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_15 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_126_elem : lane_) => (proj_lane__2 lane_1_126_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_48_elem : lane_) => (proj_lane__2 lane_2_48_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_126_elem : lane_) (lane_2_48_elem : lane_) => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_126_elem)) (Option.get! (proj_lane__2 lane_2_48_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_125_elem : lane_) => (proj_lane__2 lane_1_125_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_47_elem : lane_) => (proj_lane__2 lane_2_47_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_125_elem : lane_) (lane_2_47_elem : lane_) => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_125_elem)) (Option.get! (proj_lane__2 lane_2_47_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_N.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_16 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_129_elem : lane_) => (proj_lane__2 lane_1_129_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_51_elem : lane_) => (proj_lane__2 lane_2_51_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_129_elem : lane_) (lane_2_51_elem : lane_) => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_129_elem)) (Option.get! (proj_lane__2 lane_2_51_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_128_elem : lane_) => (proj_lane__2 lane_1_128_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_50_elem : lane_) => (proj_lane__2 lane_2_50_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_128_elem : lane_) (lane_2_50_elem : lane_) => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_128_elem)) (Option.get! (proj_lane__2 lane_2_50_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_N.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_17 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_132_elem : lane_) => (proj_lane__2 lane_1_132_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_54_elem : lane_) => (proj_lane__2 lane_2_54_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_132_elem : lane_) (lane_2_54_elem : lane_) => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_132_elem)) (Option.get! (proj_lane__2 lane_2_54_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_131_elem : lane_) => (proj_lane__2 lane_1_131_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_53_elem : lane_) => (proj_lane__2 lane_2_53_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_131_elem : lane_) (lane_2_53_elem : lane_) => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_131_elem)) (Option.get! (proj_lane__2 lane_2_53_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_N.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_18 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_135_elem : lane_) => (proj_lane__2 lane_1_135_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_57_elem : lane_) => (proj_lane__2 lane_2_57_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_135_elem : lane_) (lane_2_57_elem : lane_) => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_135_elem)) (Option.get! (proj_lane__2 lane_2_57_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_134_elem : lane_) => (proj_lane__2 lane_1_134_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_56_elem : lane_) => (proj_lane__2 lane_2_56_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_134_elem : lane_) (lane_2_56_elem : lane_) => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_134_elem)) (Option.get! (proj_lane__2 lane_2_56_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_N.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_19 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_138_elem : lane_) => (proj_lane__2 lane_1_138_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_60_elem : lane_) => (proj_lane__2 lane_2_60_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_138_elem : lane_) (lane_2_60_elem : lane_) => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_138_elem)) (Option.get! (proj_lane__2 lane_2_60_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_137_elem : lane_) => (proj_lane__2 lane_1_137_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_59_elem : lane_) => (proj_lane__2 lane_2_59_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_137_elem : lane_) (lane_2_59_elem : lane_) => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_137_elem)) (Option.get! (proj_lane__2 lane_2_59_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_N.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_20 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_141_elem : lane_) => (proj_lane__2 lane_1_141_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_63_elem : lane_) => (proj_lane__2 lane_2_63_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_141_elem : lane_) (lane_2_63_elem : lane_) => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_141_elem)) (Option.get! (proj_lane__2 lane_2_63_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_140_elem : lane_) => (proj_lane__2 lane_1_140_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_62_elem : lane_) => (proj_lane__2 lane_2_62_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_140_elem : lane_) (lane_2_62_elem : lane_) => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_140_elem)) (Option.get! (proj_lane__2 lane_2_62_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_N.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_21 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_144_elem : lane_) => (proj_lane__2 lane_1_144_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_66_elem : lane_) => (proj_lane__2 lane_2_66_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_144_elem : lane_) (lane_2_66_elem : lane_) => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_144_elem)) (Option.get! (proj_lane__2 lane_2_66_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_143_elem : lane_) => (proj_lane__2 lane_1_143_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_65_elem : lane_) => (proj_lane__2 lane_2_65_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_143_elem : lane_) (lane_2_65_elem : lane_) => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_143_elem)) (Option.get! (proj_lane__2 lane_2_65_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_N.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_22 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_147_elem : lane_) => (proj_lane__2 lane_1_147_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_69_elem : lane_) => (proj_lane__2 lane_2_69_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_147_elem : lane_) (lane_2_69_elem : lane_) => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_147_elem)) (Option.get! (proj_lane__2 lane_2_69_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_146_elem : lane_) => (proj_lane__2 lane_1_146_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_68_elem : lane_) => (proj_lane__2 lane_2_68_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_146_elem : lane_) (lane_2_68_elem : lane_) => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_146_elem)) (Option.get! (proj_lane__2 lane_2_68_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_N.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_23 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_150_elem : lane_) => (proj_lane__2 lane_1_150_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_72_elem : lane_) => (proj_lane__2 lane_2_72_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_150_elem : lane_) (lane_2_72_elem : lane_) => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_150_elem)) (Option.get! (proj_lane__2 lane_2_72_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_149_elem : lane_) => (proj_lane__2 lane_1_149_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_71_elem : lane_) => (proj_lane__2 lane_2_71_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_149_elem : lane_) (lane_2_71_elem : lane_) => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_149_elem)) (Option.get! (proj_lane__2 lane_2_71_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (var_0_elem : uN) => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_N.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_24 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_152_elem : lane_) => (proj_lane__2 lane_1_152_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_74_elem : lane_) => (proj_lane__2 lane_2_74_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_152_elem : lane_) (lane_2_74_elem : lane_) => lane_.mk_lane__2 Jnn.I32 (imul_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_152_elem)) (Option.get! (proj_lane__2 lane_2_74_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_153_elem : lane_) => (proj_lane__2 lane_1_153_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_75_elem : lane_) => (proj_lane__2 lane_2_75_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_153_elem : lane_) (lane_2_75_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (imul_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_153_elem)) (Option.get! (proj_lane__2 lane_2_75_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_25 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_155_elem : lane_) => (proj_lane__2 lane_1_155_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_77_elem : lane_) => (proj_lane__2 lane_2_77_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_155_elem : lane_) (lane_2_77_elem : lane_) => lane_.mk_lane__2 Jnn.I64 (imul_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_155_elem)) (Option.get! (proj_lane__2 lane_2_77_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_156_elem : lane_) => (proj_lane__2 lane_1_156_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_78_elem : lane_) => (proj_lane__2 lane_2_78_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_156_elem : lane_) (lane_2_78_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (imul_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_156_elem)) (Option.get! (proj_lane__2 lane_2_78_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_26 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_158_elem : lane_) => (proj_lane__2 lane_1_158_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_80_elem : lane_) => (proj_lane__2 lane_2_80_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_158_elem : lane_) (lane_2_80_elem : lane_) => lane_.mk_lane__2 Jnn.I8 (imul_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_158_elem)) (Option.get! (proj_lane__2 lane_2_80_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_159_elem : lane_) => (proj_lane__2 lane_1_159_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_81_elem : lane_) => (proj_lane__2 lane_2_81_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_159_elem : lane_) (lane_2_81_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (imul_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_159_elem)) (Option.get! (proj_lane__2 lane_2_81_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_27 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_161_elem : lane_) => (proj_lane__2 lane_1_161_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_83_elem : lane_) => (proj_lane__2 lane_2_83_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_161_elem : lane_) (lane_2_83_elem : lane_) => lane_.mk_lane__2 Jnn.I16 (imul_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_161_elem)) (Option.get! (proj_lane__2 lane_2_83_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_162_elem : lane_) => (proj_lane__2 lane_1_162_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_84_elem : lane_) => (proj_lane__2 lane_2_84_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_162_elem : lane_) (lane_2_84_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (imul_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_162_elem)) (Option.get! (proj_lane__2 lane_2_84_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_28 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_164_elem : lane_) => (proj_lane__2 lane_1_164_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_86_elem : lane_) => (proj_lane__2 lane_2_86_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_164_elem : lane_) (lane_2_86_elem : lane_) => lane_.mk_lane__2 Jnn.I32 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.U (Option.get! (proj_lane__2 lane_1_164_elem)) (Option.get! (proj_lane__2 lane_2_86_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_165_elem : lane_) => (proj_lane__2 lane_1_165_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_87_elem : lane_) => (proj_lane__2 lane_2_87_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_165_elem : lane_) (lane_2_87_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.U (Option.get! (proj_lane__2 lane_1_165_elem)) (Option.get! (proj_lane__2 lane_2_87_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_29 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_167_elem : lane_) => (proj_lane__2 lane_1_167_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_89_elem : lane_) => (proj_lane__2 lane_2_89_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_167_elem : lane_) (lane_2_89_elem : lane_) => lane_.mk_lane__2 Jnn.I64 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.U (Option.get! (proj_lane__2 lane_1_167_elem)) (Option.get! (proj_lane__2 lane_2_89_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_168_elem : lane_) => (proj_lane__2 lane_1_168_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_90_elem : lane_) => (proj_lane__2 lane_2_90_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_168_elem : lane_) (lane_2_90_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.U (Option.get! (proj_lane__2 lane_1_168_elem)) (Option.get! (proj_lane__2 lane_2_90_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_30 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_170_elem : lane_) => (proj_lane__2 lane_1_170_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_92_elem : lane_) => (proj_lane__2 lane_2_92_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_170_elem : lane_) (lane_2_92_elem : lane_) => lane_.mk_lane__2 Jnn.I8 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.U (Option.get! (proj_lane__2 lane_1_170_elem)) (Option.get! (proj_lane__2 lane_2_92_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_171_elem : lane_) => (proj_lane__2 lane_1_171_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_93_elem : lane_) => (proj_lane__2 lane_2_93_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_171_elem : lane_) (lane_2_93_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.U (Option.get! (proj_lane__2 lane_1_171_elem)) (Option.get! (proj_lane__2 lane_2_93_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_31 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_173_elem : lane_) => (proj_lane__2 lane_1_173_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_95_elem : lane_) => (proj_lane__2 lane_2_95_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_173_elem : lane_) (lane_2_95_elem : lane_) => lane_.mk_lane__2 Jnn.I16 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.U (Option.get! (proj_lane__2 lane_1_173_elem)) (Option.get! (proj_lane__2 lane_2_95_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_174_elem : lane_) => (proj_lane__2 lane_1_174_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_96_elem : lane_) => (proj_lane__2 lane_2_96_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_174_elem : lane_) (lane_2_96_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.U (Option.get! (proj_lane__2 lane_1_174_elem)) (Option.get! (proj_lane__2 lane_2_96_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_32 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_176_elem : lane_) => (proj_lane__2 lane_1_176_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_98_elem : lane_) => (proj_lane__2 lane_2_98_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_176_elem : lane_) (lane_2_98_elem : lane_) => lane_.mk_lane__2 Jnn.I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (Option.get! (proj_lane__2 lane_1_176_elem)) (Option.get! (proj_lane__2 lane_2_98_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_177_elem : lane_) => (proj_lane__2 lane_1_177_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_99_elem : lane_) => (proj_lane__2 lane_2_99_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_177_elem : lane_) (lane_2_99_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (Option.get! (proj_lane__2 lane_1_177_elem)) (Option.get! (proj_lane__2 lane_2_99_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_33 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_179_elem : lane_) => (proj_lane__2 lane_1_179_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_101_elem : lane_) => (proj_lane__2 lane_2_101_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_179_elem : lane_) (lane_2_101_elem : lane_) => lane_.mk_lane__2 Jnn.I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (Option.get! (proj_lane__2 lane_1_179_elem)) (Option.get! (proj_lane__2 lane_2_101_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_180_elem : lane_) => (proj_lane__2 lane_1_180_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_102_elem : lane_) => (proj_lane__2 lane_2_102_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_180_elem : lane_) (lane_2_102_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (Option.get! (proj_lane__2 lane_1_180_elem)) (Option.get! (proj_lane__2 lane_2_102_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_34 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_182_elem : lane_) => (proj_lane__2 lane_1_182_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_104_elem : lane_) => (proj_lane__2 lane_2_104_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_182_elem : lane_) (lane_2_104_elem : lane_) => lane_.mk_lane__2 Jnn.I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (Option.get! (proj_lane__2 lane_1_182_elem)) (Option.get! (proj_lane__2 lane_2_104_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_183_elem : lane_) => (proj_lane__2 lane_1_183_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_105_elem : lane_) => (proj_lane__2 lane_2_105_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_183_elem : lane_) (lane_2_105_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (Option.get! (proj_lane__2 lane_1_183_elem)) (Option.get! (proj_lane__2 lane_2_105_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_35 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_185_elem : lane_) => (proj_lane__2 lane_1_185_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_107_elem : lane_) => (proj_lane__2 lane_2_107_elem) ≠ none) lane_2_lst →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun (lane_1_185_elem : lane_) (lane_2_107_elem : lane_) => lane_.mk_lane__2 Jnn.I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (Option.get! (proj_lane__2 lane_1_185_elem)) (Option.get! (proj_lane__2 lane_2_107_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_186_elem : lane_) => (proj_lane__2 lane_1_186_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_108_elem : lane_) => (proj_lane__2 lane_2_108_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_186_elem : lane_) (lane_2_108_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (Option.get! (proj_lane__2 lane_1_186_elem)) (Option.get! (proj_lane__2 lane_2_108_elem))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_36 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_188_elem : lane_) (lane_2_110_elem : lane_) => Map (fun (iter_0_77_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_77_elem)) (fadd_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_188_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_110_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_30_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_30_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_189_elem : lane_) (lane_2_111_elem : lane_) => Forall (fun (iter_0_78_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_78_elem))) (fadd_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_189_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_111_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.ADD) v128_1 v128_2 v128_lst
  | fun_vbinop__case_37 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_191_elem : lane_) (lane_2_113_elem : lane_) => Map (fun (iter_0_79_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_79_elem)) (fadd_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_191_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_113_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_32_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_32_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_192_elem : lane_) (lane_2_114_elem : lane_) => Forall (fun (iter_0_80_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_80_elem))) (fadd_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_192_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_114_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.ADD) v128_1 v128_2 v128_lst
  | fun_vbinop__case_38 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_194_elem : lane_) (lane_2_116_elem : lane_) => Map (fun (iter_0_81_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_81_elem)) (fsub_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_194_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_116_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_34_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_34_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_195_elem : lane_) (lane_2_117_elem : lane_) => Forall (fun (iter_0_82_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_82_elem))) (fsub_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_195_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_117_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.SUB) v128_1 v128_2 v128_lst
  | fun_vbinop__case_39 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_197_elem : lane_) (lane_2_119_elem : lane_) => Map (fun (iter_0_83_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_83_elem)) (fsub_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_197_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_119_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_36_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_36_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_198_elem : lane_) (lane_2_120_elem : lane_) => Forall (fun (iter_0_84_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_84_elem))) (fsub_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_198_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_120_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.SUB) v128_1 v128_2 v128_lst
  | fun_vbinop__case_40 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_200_elem : lane_) (lane_2_122_elem : lane_) => Map (fun (iter_0_85_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_85_elem)) (fmul_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_200_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_122_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_38_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_38_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_201_elem : lane_) (lane_2_123_elem : lane_) => Forall (fun (iter_0_86_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_86_elem))) (fmul_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_201_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_123_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.MUL) v128_1 v128_2 v128_lst
  | fun_vbinop__case_41 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_203_elem : lane_) (lane_2_125_elem : lane_) => Map (fun (iter_0_87_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_87_elem)) (fmul_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_203_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_125_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_40_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_40_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_204_elem : lane_) (lane_2_126_elem : lane_) => Forall (fun (iter_0_88_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_88_elem))) (fmul_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_204_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_126_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.MUL) v128_1 v128_2 v128_lst
  | fun_vbinop__case_42 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_206_elem : lane_) (lane_2_128_elem : lane_) => Map (fun (iter_0_89_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_89_elem)) (fdiv_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_206_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_128_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_42_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_42_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_207_elem : lane_) (lane_2_129_elem : lane_) => Forall (fun (iter_0_90_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_90_elem))) (fdiv_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_207_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_129_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.DIV) v128_1 v128_2 v128_lst
  | fun_vbinop__case_43 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_209_elem : lane_) (lane_2_131_elem : lane_) => Map (fun (iter_0_91_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_91_elem)) (fdiv_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_209_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_131_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_44_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_44_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_210_elem : lane_) (lane_2_132_elem : lane_) => Forall (fun (iter_0_92_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_92_elem))) (fdiv_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_210_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_132_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.DIV) v128_1 v128_2 v128_lst
  | fun_vbinop__case_44 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_212_elem : lane_) (lane_2_134_elem : lane_) => Map (fun (iter_0_93_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_93_elem)) (fmin_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_212_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_134_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_46_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_46_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_213_elem : lane_) (lane_2_135_elem : lane_) => Forall (fun (iter_0_94_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_94_elem))) (fmin_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_213_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_135_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.MIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_45 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_215_elem : lane_) (lane_2_137_elem : lane_) => Map (fun (iter_0_95_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_95_elem)) (fmin_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_215_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_137_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_48_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_48_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_216_elem : lane_) (lane_2_138_elem : lane_) => Forall (fun (iter_0_96_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_96_elem))) (fmin_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_216_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_138_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.MIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_46 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_218_elem : lane_) (lane_2_140_elem : lane_) => Map (fun (iter_0_97_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_97_elem)) (fmax_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_218_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_140_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_50_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_50_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_219_elem : lane_) (lane_2_141_elem : lane_) => Forall (fun (iter_0_98_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_98_elem))) (fmax_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_219_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_141_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.MAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_47 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_221_elem : lane_) (lane_2_143_elem : lane_) => Map (fun (iter_0_99_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_99_elem)) (fmax_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_221_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_143_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_52_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_52_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_222_elem : lane_) (lane_2_144_elem : lane_) => Forall (fun (iter_0_100_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_100_elem))) (fmax_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_222_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_144_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.MAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_48 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_224_elem : lane_) (lane_2_146_elem : lane_) => Map (fun (iter_0_101_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_101_elem)) (fpmin_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_224_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_146_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_54_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_54_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_225_elem : lane_) (lane_2_147_elem : lane_) => Forall (fun (iter_0_102_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_102_elem))) (fpmin_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_225_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_147_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.PMIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_49 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_227_elem : lane_) (lane_2_149_elem : lane_) => Map (fun (iter_0_103_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_103_elem)) (fpmin_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_227_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_149_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_56_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_56_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_228_elem : lane_) (lane_2_150_elem : lane_) => Forall (fun (iter_0_104_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_104_elem))) (fpmin_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_228_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_150_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.PMIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_50 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_230_elem : lane_) (lane_2_152_elem : lane_) => Map (fun (iter_0_105_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_105_elem)) (fpmax_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_230_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_152_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_58_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_58_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_231_elem : lane_) (lane_2_153_elem : lane_) => Forall (fun (iter_0_106_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_106_elem))) (fpmax_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_231_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_153_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.PMAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_51 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst = (setproduct_ lane_ (Map₂ (fun (lane_1_233_elem : lane_) (lane_2_155_elem : lane_) => Map (fun (iter_0_107_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_107_elem)) (fpmax_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_233_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_155_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst = (Map (fun (lane_lst_60_elem : List lane_) => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_60_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall₂ (fun (lane_1_234_elem : lane_) (lane_2_156_elem : lane_) => Forall (fun (iter_0_108_elem : fN) => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_108_elem))) (fpmax_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_234_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_156_elem)))))) lane_1_lst lane_2_lst →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.PMAX) v128_1 v128_2 v128_lst


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:379.6-379.14 -/
theorem vbinop__is_wf (v_shape : shape) (v_vbinop_ : vbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : List vec_) (var_0 : List vec_) :
  fun_vbinop_ v_shape v_vbinop_ v_vec_ vec__0 var_0 →
  wf_shape v_shape →
  wf_vbinop_ v_shape v_vbinop_ →
  wf_uN 128 v_vec_ →
  wf_uN 128 vec__0 →
  ret_val_lst = var_0 →
  Forall (fun (ret_val_elem : vec_) => wf_uN 128 ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 -/
inductive fun_vrelop_ : shape → vrelop_ → vec_ → vec_ → vec_ → Prop where
  | fun_vrelop__case_0 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_236_elem : lane_) => (proj_lane__2 lane_1_236_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_158_elem : lane_) => (proj_lane__2 lane_2_158_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_236_elem : lane_) (lane_2_158_elem : lane_) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_236_elem)) (Option.get! (proj_lane__2 lane_2_158_elem)))))) lane_1_lst lane_2_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (lane_3_2_elem : iN) => lane_.mk_lane__2 Jnn.I32 lane_3_2_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_237_elem : lane_) => (proj_lane__2 lane_1_237_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_159_elem : lane_) => (proj_lane__2 lane_2_159_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_237_elem : lane_) (lane_2_159_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_237_elem)) (Option.get! (proj_lane__2 lane_2_159_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun (lane_3_3_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_3_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 vrelop_Jnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_1 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_239_elem : lane_) => (proj_lane__2 lane_1_239_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_161_elem : lane_) => (proj_lane__2 lane_2_161_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_239_elem : lane_) (lane_2_161_elem : lane_) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_239_elem)) (Option.get! (proj_lane__2 lane_2_161_elem)))))) lane_1_lst lane_2_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (lane_3_5_elem : iN) => lane_.mk_lane__2 Jnn.I64 lane_3_5_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_240_elem : lane_) => (proj_lane__2 lane_1_240_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_162_elem : lane_) => (proj_lane__2 lane_2_162_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_240_elem : lane_) (lane_2_162_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_240_elem)) (Option.get! (proj_lane__2 lane_2_162_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun (lane_3_6_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_6_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 vrelop_Jnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_2 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_242_elem : lane_) => (proj_lane__2 lane_1_242_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_164_elem : lane_) => (proj_lane__2 lane_2_164_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_242_elem : lane_) (lane_2_164_elem : lane_) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_242_elem)) (Option.get! (proj_lane__2 lane_2_164_elem)))))) lane_1_lst lane_2_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (lane_3_8_elem : iN) => lane_.mk_lane__2 Jnn.I8 lane_3_8_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_243_elem : lane_) => (proj_lane__2 lane_1_243_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_165_elem : lane_) => (proj_lane__2 lane_2_165_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_243_elem : lane_) (lane_2_165_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_243_elem)) (Option.get! (proj_lane__2 lane_2_165_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun (lane_3_9_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_9_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 vrelop_Jnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_3 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_245_elem : lane_) => (proj_lane__2 lane_1_245_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_167_elem : lane_) => (proj_lane__2 lane_2_167_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_245_elem : lane_) (lane_2_167_elem : lane_) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_245_elem)) (Option.get! (proj_lane__2 lane_2_167_elem)))))) lane_1_lst lane_2_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (lane_3_11_elem : iN) => lane_.mk_lane__2 Jnn.I16 lane_3_11_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_246_elem : lane_) => (proj_lane__2 lane_1_246_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_168_elem : lane_) => (proj_lane__2 lane_2_168_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_246_elem : lane_) (lane_2_168_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_246_elem)) (Option.get! (proj_lane__2 lane_2_168_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun (lane_3_12_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_12_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 vrelop_Jnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_4 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_248_elem : lane_) => (proj_lane__2 lane_1_248_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_170_elem : lane_) => (proj_lane__2 lane_2_170_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_248_elem : lane_) (lane_2_170_elem : lane_) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_248_elem)) (Option.get! (proj_lane__2 lane_2_170_elem)))))) lane_1_lst lane_2_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (lane_3_14_elem : iN) => lane_.mk_lane__2 Jnn.I32 lane_3_14_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_249_elem : lane_) => (proj_lane__2 lane_1_249_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_171_elem : lane_) => (proj_lane__2 lane_2_171_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_249_elem : lane_) (lane_2_171_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_249_elem)) (Option.get! (proj_lane__2 lane_2_171_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun (lane_3_15_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_15_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 vrelop_Jnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_5 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_251_elem : lane_) => (proj_lane__2 lane_1_251_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_173_elem : lane_) => (proj_lane__2 lane_2_173_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_251_elem : lane_) (lane_2_173_elem : lane_) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_251_elem)) (Option.get! (proj_lane__2 lane_2_173_elem)))))) lane_1_lst lane_2_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (lane_3_17_elem : iN) => lane_.mk_lane__2 Jnn.I64 lane_3_17_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_252_elem : lane_) => (proj_lane__2 lane_1_252_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_174_elem : lane_) => (proj_lane__2 lane_2_174_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_252_elem : lane_) (lane_2_174_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_252_elem)) (Option.get! (proj_lane__2 lane_2_174_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun (lane_3_18_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_18_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 vrelop_Jnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_6 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_254_elem : lane_) => (proj_lane__2 lane_1_254_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_176_elem : lane_) => (proj_lane__2 lane_2_176_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_254_elem : lane_) (lane_2_176_elem : lane_) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_254_elem)) (Option.get! (proj_lane__2 lane_2_176_elem)))))) lane_1_lst lane_2_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (lane_3_20_elem : iN) => lane_.mk_lane__2 Jnn.I8 lane_3_20_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_255_elem : lane_) => (proj_lane__2 lane_1_255_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_177_elem : lane_) => (proj_lane__2 lane_2_177_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_255_elem : lane_) (lane_2_177_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_255_elem)) (Option.get! (proj_lane__2 lane_2_177_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun (lane_3_21_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_21_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 vrelop_Jnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_7 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_257_elem : lane_) => (proj_lane__2 lane_1_257_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_179_elem : lane_) => (proj_lane__2 lane_2_179_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_257_elem : lane_) (lane_2_179_elem : lane_) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_257_elem)) (Option.get! (proj_lane__2 lane_2_179_elem)))))) lane_1_lst lane_2_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (lane_3_23_elem : iN) => lane_.mk_lane__2 Jnn.I16 lane_3_23_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_258_elem : lane_) => (proj_lane__2 lane_1_258_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_180_elem : lane_) => (proj_lane__2 lane_2_180_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_258_elem : lane_) (lane_2_180_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_258_elem)) (Option.get! (proj_lane__2 lane_2_180_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun (lane_3_24_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_24_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 vrelop_Jnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_8 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_261_elem : lane_) => (proj_lane__2 lane_1_261_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_183_elem : lane_) => (proj_lane__2 lane_2_183_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_261_elem : lane_) (lane_2_183_elem : lane_) => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_261_elem)) (Option.get! (proj_lane__2 lane_2_183_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_260_elem : lane_) => (proj_lane__2 lane_1_260_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_182_elem : lane_) => (proj_lane__2 lane_2_182_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_260_elem : lane_) (lane_2_182_elem : lane_) => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_260_elem)) (Option.get! (proj_lane__2 lane_2_182_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (lane_3_26_elem : iN) => lane_.mk_lane__2 Jnn.I32 lane_3_26_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_27_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_27_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_N.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_9 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_264_elem : lane_) => (proj_lane__2 lane_1_264_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_186_elem : lane_) => (proj_lane__2 lane_2_186_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_264_elem : lane_) (lane_2_186_elem : lane_) => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_264_elem)) (Option.get! (proj_lane__2 lane_2_186_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_263_elem : lane_) => (proj_lane__2 lane_1_263_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_185_elem : lane_) => (proj_lane__2 lane_2_185_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_263_elem : lane_) (lane_2_185_elem : lane_) => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_263_elem)) (Option.get! (proj_lane__2 lane_2_185_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (lane_3_29_elem : iN) => lane_.mk_lane__2 Jnn.I64 lane_3_29_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_30_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_30_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_N.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_10 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_267_elem : lane_) => (proj_lane__2 lane_1_267_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_189_elem : lane_) => (proj_lane__2 lane_2_189_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_267_elem : lane_) (lane_2_189_elem : lane_) => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_267_elem)) (Option.get! (proj_lane__2 lane_2_189_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_266_elem : lane_) => (proj_lane__2 lane_1_266_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_188_elem : lane_) => (proj_lane__2 lane_2_188_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_266_elem : lane_) (lane_2_188_elem : lane_) => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_266_elem)) (Option.get! (proj_lane__2 lane_2_188_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (lane_3_32_elem : iN) => lane_.mk_lane__2 Jnn.I8 lane_3_32_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_33_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_33_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_N.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_11 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_270_elem : lane_) => (proj_lane__2 lane_1_270_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_192_elem : lane_) => (proj_lane__2 lane_2_192_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_270_elem : lane_) (lane_2_192_elem : lane_) => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_270_elem)) (Option.get! (proj_lane__2 lane_2_192_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_269_elem : lane_) => (proj_lane__2 lane_1_269_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_191_elem : lane_) => (proj_lane__2 lane_2_191_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_269_elem : lane_) (lane_2_191_elem : lane_) => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_269_elem)) (Option.get! (proj_lane__2 lane_2_191_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (lane_3_35_elem : iN) => lane_.mk_lane__2 Jnn.I16 lane_3_35_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_36_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_36_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_N.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_12 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_273_elem : lane_) => (proj_lane__2 lane_1_273_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_195_elem : lane_) => (proj_lane__2 lane_2_195_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_273_elem : lane_) (lane_2_195_elem : lane_) => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_273_elem)) (Option.get! (proj_lane__2 lane_2_195_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_272_elem : lane_) => (proj_lane__2 lane_1_272_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_194_elem : lane_) => (proj_lane__2 lane_2_194_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_272_elem : lane_) (lane_2_194_elem : lane_) => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_272_elem)) (Option.get! (proj_lane__2 lane_2_194_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (lane_3_38_elem : iN) => lane_.mk_lane__2 Jnn.I32 lane_3_38_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_39_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_39_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_N.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_13 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_276_elem : lane_) => (proj_lane__2 lane_1_276_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_198_elem : lane_) => (proj_lane__2 lane_2_198_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_276_elem : lane_) (lane_2_198_elem : lane_) => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_276_elem)) (Option.get! (proj_lane__2 lane_2_198_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_275_elem : lane_) => (proj_lane__2 lane_1_275_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_197_elem : lane_) => (proj_lane__2 lane_2_197_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_275_elem : lane_) (lane_2_197_elem : lane_) => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_275_elem)) (Option.get! (proj_lane__2 lane_2_197_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (lane_3_41_elem : iN) => lane_.mk_lane__2 Jnn.I64 lane_3_41_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_42_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_42_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_N.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_14 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_279_elem : lane_) => (proj_lane__2 lane_1_279_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_201_elem : lane_) => (proj_lane__2 lane_2_201_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_279_elem : lane_) (lane_2_201_elem : lane_) => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_279_elem)) (Option.get! (proj_lane__2 lane_2_201_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_278_elem : lane_) => (proj_lane__2 lane_1_278_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_200_elem : lane_) => (proj_lane__2 lane_2_200_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_278_elem : lane_) (lane_2_200_elem : lane_) => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_278_elem)) (Option.get! (proj_lane__2 lane_2_200_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (lane_3_44_elem : iN) => lane_.mk_lane__2 Jnn.I8 lane_3_44_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_45_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_45_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_N.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_15 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_282_elem : lane_) => (proj_lane__2 lane_1_282_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_204_elem : lane_) => (proj_lane__2 lane_2_204_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_282_elem : lane_) (lane_2_204_elem : lane_) => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_282_elem)) (Option.get! (proj_lane__2 lane_2_204_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_281_elem : lane_) => (proj_lane__2 lane_1_281_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_203_elem : lane_) => (proj_lane__2 lane_2_203_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_281_elem : lane_) (lane_2_203_elem : lane_) => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_281_elem)) (Option.get! (proj_lane__2 lane_2_203_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (lane_3_47_elem : iN) => lane_.mk_lane__2 Jnn.I16 lane_3_47_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_48_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_48_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_N.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_16 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_285_elem : lane_) => (proj_lane__2 lane_1_285_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_207_elem : lane_) => (proj_lane__2 lane_2_207_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_285_elem : lane_) (lane_2_207_elem : lane_) => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_285_elem)) (Option.get! (proj_lane__2 lane_2_207_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_284_elem : lane_) => (proj_lane__2 lane_1_284_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_206_elem : lane_) => (proj_lane__2 lane_2_206_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_284_elem : lane_) (lane_2_206_elem : lane_) => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_284_elem)) (Option.get! (proj_lane__2 lane_2_206_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (lane_3_50_elem : iN) => lane_.mk_lane__2 Jnn.I32 lane_3_50_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_51_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_51_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_N.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_17 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_288_elem : lane_) => (proj_lane__2 lane_1_288_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_210_elem : lane_) => (proj_lane__2 lane_2_210_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_288_elem : lane_) (lane_2_210_elem : lane_) => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_288_elem)) (Option.get! (proj_lane__2 lane_2_210_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_287_elem : lane_) => (proj_lane__2 lane_1_287_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_209_elem : lane_) => (proj_lane__2 lane_2_209_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_287_elem : lane_) (lane_2_209_elem : lane_) => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_287_elem)) (Option.get! (proj_lane__2 lane_2_209_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (lane_3_53_elem : iN) => lane_.mk_lane__2 Jnn.I64 lane_3_53_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_54_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_54_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_N.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_18 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_291_elem : lane_) => (proj_lane__2 lane_1_291_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_213_elem : lane_) => (proj_lane__2 lane_2_213_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_291_elem : lane_) (lane_2_213_elem : lane_) => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_291_elem)) (Option.get! (proj_lane__2 lane_2_213_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_290_elem : lane_) => (proj_lane__2 lane_1_290_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_212_elem : lane_) => (proj_lane__2 lane_2_212_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_290_elem : lane_) (lane_2_212_elem : lane_) => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_290_elem)) (Option.get! (proj_lane__2 lane_2_212_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (lane_3_56_elem : iN) => lane_.mk_lane__2 Jnn.I8 lane_3_56_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_57_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_57_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_N.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_19 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_294_elem : lane_) => (proj_lane__2 lane_1_294_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_216_elem : lane_) => (proj_lane__2 lane_2_216_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_294_elem : lane_) (lane_2_216_elem : lane_) => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_294_elem)) (Option.get! (proj_lane__2 lane_2_216_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_293_elem : lane_) => (proj_lane__2 lane_1_293_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_215_elem : lane_) => (proj_lane__2 lane_2_215_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_293_elem : lane_) (lane_2_215_elem : lane_) => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_293_elem)) (Option.get! (proj_lane__2 lane_2_215_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (lane_3_59_elem : iN) => lane_.mk_lane__2 Jnn.I16 lane_3_59_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_60_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_60_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_N.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_20 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_297_elem : lane_) => (proj_lane__2 lane_1_297_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_219_elem : lane_) => (proj_lane__2 lane_2_219_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_297_elem : lane_) (lane_2_219_elem : lane_) => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_297_elem)) (Option.get! (proj_lane__2 lane_2_219_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_296_elem : lane_) => (proj_lane__2 lane_1_296_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_218_elem : lane_) => (proj_lane__2 lane_2_218_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_296_elem : lane_) (lane_2_218_elem : lane_) => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_296_elem)) (Option.get! (proj_lane__2 lane_2_218_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun (lane_3_62_elem : iN) => lane_.mk_lane__2 Jnn.I32 lane_3_62_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_63_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_63_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_N.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_21 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_300_elem : lane_) => (proj_lane__2 lane_1_300_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_222_elem : lane_) => (proj_lane__2 lane_2_222_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_300_elem : lane_) (lane_2_222_elem : lane_) => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_300_elem)) (Option.get! (proj_lane__2 lane_2_222_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_299_elem : lane_) => (proj_lane__2 lane_1_299_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_221_elem : lane_) => (proj_lane__2 lane_2_221_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_299_elem : lane_) (lane_2_221_elem : lane_) => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_299_elem)) (Option.get! (proj_lane__2 lane_2_221_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun (lane_3_65_elem : iN) => lane_.mk_lane__2 Jnn.I64 lane_3_65_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_66_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_66_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_N.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_22 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_303_elem : lane_) => (proj_lane__2 lane_1_303_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_225_elem : lane_) => (proj_lane__2 lane_2_225_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_303_elem : lane_) (lane_2_225_elem : lane_) => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_303_elem)) (Option.get! (proj_lane__2 lane_2_225_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_302_elem : lane_) => (proj_lane__2 lane_1_302_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_224_elem : lane_) => (proj_lane__2 lane_2_224_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_302_elem : lane_) (lane_2_224_elem : lane_) => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_302_elem)) (Option.get! (proj_lane__2 lane_2_224_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun (lane_3_68_elem : iN) => lane_.mk_lane__2 Jnn.I8 lane_3_68_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_69_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_69_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_N.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_23 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) :
    (List.length var_1_lst) = (List.length lane_1_lst) →
    (List.length var_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_306_elem : lane_) => (proj_lane__2 lane_1_306_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_228_elem : lane_) => (proj_lane__2 lane_2_228_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_1_elem : uN) (lane_1_306_elem : lane_) (lane_2_228_elem : lane_) => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_306_elem)) (Option.get! (proj_lane__2 lane_2_228_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) = (List.length lane_1_lst) →
    (List.length var_0_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_305_elem : lane_) => (proj_lane__2 lane_1_305_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_227_elem : lane_) => (proj_lane__2 lane_2_227_elem) ≠ none) lane_2_lst →
    Forall₃ (fun (var_0_elem : uN) (lane_1_305_elem : lane_) (lane_2_227_elem : lane_) => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_305_elem)) (Option.get! (proj_lane__2 lane_2_227_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst = (Map (fun (var_0_elem : uN) => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (uN.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun (lane_3_71_elem : iN) => lane_.mk_lane__2 Jnn.I16 lane_3_71_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun (var_1_elem : uN) => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun (lane_3_72_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_72_elem)) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_N.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_24 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_308_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_308_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_308_elem : lane_) => (proj_lane__0 lane_1_308_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_230_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_230_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_230_elem : lane_) => (proj_lane__0 lane_2_230_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_308_elem : lane_) (lane_2_230_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (uN.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_308_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_230_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_74_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_74_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_309_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_309_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_309_elem : lane_) => (proj_lane__0 lane_1_309_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_231_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_231_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_231_elem : lane_) => (proj_lane__0 lane_2_231_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_309_elem : lane_) (lane_2_231_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_309_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_231_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_75_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_75_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_25 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_311_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_311_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_311_elem : lane_) => (proj_lane__0 lane_1_311_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_233_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_233_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_233_elem : lane_) => (proj_lane__0 lane_2_233_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_311_elem : lane_) (lane_2_233_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (uN.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_311_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_233_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_77_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_77_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_312_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_312_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_312_elem : lane_) => (proj_lane__0 lane_1_312_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_234_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_234_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_234_elem : lane_) => (proj_lane__0 lane_2_234_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_312_elem : lane_) (lane_2_234_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_312_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_234_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_78_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_78_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_26 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_314_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_314_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_314_elem : lane_) => (proj_lane__0 lane_1_314_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_236_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_236_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_236_elem : lane_) => (proj_lane__0 lane_2_236_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_314_elem : lane_) (lane_2_236_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (uN.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_314_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_236_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_80_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_80_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_315_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_315_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_315_elem : lane_) => (proj_lane__0 lane_1_315_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_237_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_237_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_237_elem : lane_) => (proj_lane__0 lane_2_237_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_315_elem : lane_) (lane_2_237_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_315_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_237_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_81_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_81_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_27 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_317_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_317_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_317_elem : lane_) => (proj_lane__0 lane_1_317_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_239_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_239_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_239_elem : lane_) => (proj_lane__0 lane_2_239_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_317_elem : lane_) (lane_2_239_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (uN.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_317_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_239_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_83_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_83_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_318_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_318_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_318_elem : lane_) => (proj_lane__0 lane_1_318_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_240_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_240_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_240_elem : lane_) => (proj_lane__0 lane_2_240_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_318_elem : lane_) (lane_2_240_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_318_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_240_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_84_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_84_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_28 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_320_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_320_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_320_elem : lane_) => (proj_lane__0 lane_1_320_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_242_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_242_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_242_elem : lane_) => (proj_lane__0 lane_2_242_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_320_elem : lane_) (lane_2_242_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (uN.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_320_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_242_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_86_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_86_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_321_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_321_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_321_elem : lane_) => (proj_lane__0 lane_1_321_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_243_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_243_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_243_elem : lane_) => (proj_lane__0 lane_2_243_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_321_elem : lane_) (lane_2_243_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_321_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_243_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_87_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_87_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.LT) v128_1 v128_2 v128
  | fun_vrelop__case_29 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_323_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_323_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_323_elem : lane_) => (proj_lane__0 lane_1_323_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_245_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_245_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_245_elem : lane_) => (proj_lane__0 lane_2_245_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_323_elem : lane_) (lane_2_245_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (uN.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_323_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_245_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_89_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_89_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_324_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_324_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_324_elem : lane_) => (proj_lane__0 lane_1_324_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_246_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_246_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_246_elem : lane_) => (proj_lane__0 lane_2_246_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_324_elem : lane_) (lane_2_246_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_324_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_246_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_90_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_90_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.LT) v128_1 v128_2 v128
  | fun_vrelop__case_30 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_326_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_326_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_326_elem : lane_) => (proj_lane__0 lane_1_326_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_248_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_248_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_248_elem : lane_) => (proj_lane__0 lane_2_248_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_326_elem : lane_) (lane_2_248_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (uN.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_326_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_248_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_92_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_92_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_327_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_327_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_327_elem : lane_) => (proj_lane__0 lane_1_327_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_249_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_249_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_249_elem : lane_) => (proj_lane__0 lane_2_249_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_327_elem : lane_) (lane_2_249_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_327_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_249_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_93_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_93_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.GT) v128_1 v128_2 v128
  | fun_vrelop__case_31 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_329_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_329_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_329_elem : lane_) => (proj_lane__0 lane_1_329_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_251_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_251_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_251_elem : lane_) => (proj_lane__0 lane_2_251_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_329_elem : lane_) (lane_2_251_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (uN.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_329_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_251_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_95_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_95_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_330_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_330_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_330_elem : lane_) => (proj_lane__0 lane_1_330_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_252_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_252_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_252_elem : lane_) => (proj_lane__0 lane_2_252_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_330_elem : lane_) (lane_2_252_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_330_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_252_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_96_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_96_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.GT) v128_1 v128_2 v128
  | fun_vrelop__case_32 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_332_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_332_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_332_elem : lane_) => (proj_lane__0 lane_1_332_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_254_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_254_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_254_elem : lane_) => (proj_lane__0 lane_2_254_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_332_elem : lane_) (lane_2_254_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (uN.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_332_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_254_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_98_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_98_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_333_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_333_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_333_elem : lane_) => (proj_lane__0 lane_1_333_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_255_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_255_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_255_elem : lane_) => (proj_lane__0 lane_2_255_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_333_elem : lane_) (lane_2_255_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_333_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_255_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_99_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_99_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.LE) v128_1 v128_2 v128
  | fun_vrelop__case_33 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_335_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_335_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_335_elem : lane_) => (proj_lane__0 lane_1_335_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_257_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_257_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_257_elem : lane_) => (proj_lane__0 lane_2_257_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_335_elem : lane_) (lane_2_257_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (uN.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_335_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_257_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_101_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_101_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_336_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_336_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_336_elem : lane_) => (proj_lane__0 lane_1_336_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_258_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_258_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_258_elem : lane_) => (proj_lane__0 lane_2_258_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_336_elem : lane_) (lane_2_258_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_336_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_258_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_102_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_102_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.LE) v128_1 v128_2 v128
  | fun_vrelop__case_34 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_338_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_338_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_338_elem : lane_) => (proj_lane__0 lane_1_338_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_260_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_260_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_260_elem : lane_) => (proj_lane__0 lane_2_260_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_338_elem : lane_) (lane_2_260_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (uN.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_338_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_260_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_104_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_104_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_339_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_339_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_339_elem : lane_) => (proj_lane__0 lane_1_339_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_261_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_261_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_261_elem : lane_) => (proj_lane__0 lane_2_261_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_339_elem : lane_) (lane_2_261_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_339_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_261_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_105_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_105_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.GE) v128_1 v128_2 v128
  | fun_vrelop__case_35 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) :
    lane_1_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst = (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun (lane_1_341_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_341_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_341_elem : lane_) => (proj_lane__0 lane_1_341_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_263_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_263_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_263_elem : lane_) => (proj_lane__0 lane_2_263_elem) ≠ none) lane_2_lst →
    lane_3_lst = (Map₂ (fun (lane_1_341_elem : lane_) (lane_2_263_elem : lane_) => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (uN.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_341_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_263_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) ≠ none →
    (isize v_Inn) = (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 = (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun (lane_3_107_elem : iN) => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_107_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) = (List.length lane_2_lst) →
    Forall (fun (lane_1_342_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_1_342_elem))) ≠ none) lane_1_lst →
    Forall (fun (lane_1_342_elem : lane_) => (proj_lane__0 lane_1_342_elem) ≠ none) lane_1_lst →
    Forall (fun (lane_2_264_elem : lane_) => (proj_num__1 (Option.get! (proj_lane__0 lane_2_264_elem))) ≠ none) lane_2_lst →
    Forall (fun (lane_2_264_elem : lane_) => (proj_lane__0 lane_2_264_elem) ≠ none) lane_2_lst →
    Forall₂ (fun (lane_1_342_elem : lane_) (lane_2_264_elem : lane_) => wf_uN 1 (uN.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_342_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_264_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun (lane_3_108_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_108_elem))))) lane_3_lst →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.GE) v128_1 v128_2 v128


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:381.6-381.14 -/
theorem vrelop__is_wf (v_shape : shape) (v_vrelop_ : vrelop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_) :
  fun_vrelop_ v_shape v_vrelop_ v_vec_ vec__0 var_0 →
  wf_shape v_shape →
  wf_vrelop_ v_shape v_vrelop_ →
  wf_uN 128 v_vec_ →
  wf_uN 128 vec__0 →
  ret_val = var_0 →
  wf_uN 128 ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/3-numerics.spectec:383.1-384.41 -/
def vcvtop__ (shape_1 : shape) (shape_2 : shape) (v_vcvtop : vcvtop) (v_lane_ : lane_) : List lane_ :=
  match shape_1, shape_2, v_vcvtop, v_lane_ with
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I32 iN_2]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I32 iN_2]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I32 iN_2]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I32 iN_2]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I64 iN_2]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I64 iN_2]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I64 iN_2]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I64 iN_2]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I8 iN_2]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I8 iN_2]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I8 iN_2]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I8 iN_2]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I16 iN_2]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I16 iN_2]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I16 iN_2]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => let iN_2 := extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx iN_1
  [lane_.mk_lane__2 Jnn.I16 iN_2]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => let fN_2 := convert__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Fnn Fnn.F32)) v_sx iN_1
  [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2)]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => let fN_2 := convert__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Fnn Fnn.F32)) v_sx iN_1
  [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2)]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => let fN_2 := convert__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Fnn Fnn.F32)) v_sx iN_1
  [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2)]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => let fN_2 := convert__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Fnn Fnn.F32)) v_sx iN_1
  [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2)]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => let fN_2 := convert__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Fnn Fnn.F64)) v_sx iN_1
  [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2)]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => let fN_2 := convert__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Fnn Fnn.F64)) v_sx iN_1
  [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2)]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => let fN_2 := convert__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Fnn Fnn.F64)) v_sx iN_1
  [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2)]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => let fN_2 := convert__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Fnn Fnn.F64)) v_sx iN_1
  [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2)]
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.TRUNC_SAT v_sx zero_opt, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => let iN_2_opt := trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Inn Inn.I32)) v_sx fN_1
  list_ lane_ (OMap (fun (iN_2_2_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 iN_2_2_elem)) iN_2_opt)
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.TRUNC_SAT v_sx zero_opt, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => let iN_2_opt := trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Inn Inn.I64)) v_sx fN_1
  list_ lane_ (OMap (fun (iN_2_4_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 iN_2_4_elem)) iN_2_opt)
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.TRUNC_SAT v_sx zero_opt, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => let iN_2_opt := trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Inn Inn.I32)) v_sx fN_1
  list_ lane_ (OMap (fun (iN_2_6_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 iN_2_6_elem)) iN_2_opt)
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.TRUNC_SAT v_sx zero_opt, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => let iN_2_opt := trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Inn Inn.I64)) v_sx fN_1
  list_ lane_ (OMap (fun (iN_2_8_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 iN_2_8_elem)) iN_2_opt)
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.DEMOTE zero.ZERO, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => let fN_2_lst := demote__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Fnn Fnn.F32)) fN_1
  Map (fun (fN_2_2_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2_2_elem)) fN_2_lst
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.DEMOTE zero.ZERO, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => let fN_2_lst := demote__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Fnn Fnn.F64)) fN_1
  Map (fun (fN_2_4_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2_4_elem)) fN_2_lst
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.DEMOTE zero.ZERO, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => let fN_2_lst := demote__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Fnn Fnn.F32)) fN_1
  Map (fun (fN_2_6_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2_6_elem)) fN_2_lst
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.DEMOTE zero.ZERO, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => let fN_2_lst := demote__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Fnn Fnn.F64)) fN_1
  Map (fun (fN_2_8_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2_8_elem)) fN_2_lst
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.PROMOTELOW, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => let fN_2_lst := promote__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Fnn Fnn.F32)) fN_1
  Map (fun (fN_2_10_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2_10_elem)) fN_2_lst
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.PROMOTELOW, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => let fN_2_lst := promote__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Fnn Fnn.F64)) fN_1
  Map (fun (fN_2_12_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2_12_elem)) fN_2_lst
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.PROMOTELOW, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => let fN_2_lst := promote__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Fnn Fnn.F32)) fN_1
  Map (fun (fN_2_14_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2_14_elem)) fN_2_lst
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.PROMOTELOW, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => let fN_2_lst := promote__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Fnn Fnn.F64)) fN_1
  Map (fun (fN_2_16_elem : fN) => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2_16_elem)) fN_2_lst
  | _, _, _, _ => Inhabited.default

/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:383.6-383.15 -/
theorem vcvtop___is_wf (shape_1 : shape) (shape_2 : shape) (v_vcvtop : vcvtop) (v_lane_ : lane_) (ret_val_lst : List lane_) :
  wf_shape shape_1 →
  wf_shape shape_2 →
  wf_lane_ (fun_lanetype shape_1) v_lane_ →
  ret_val_lst = (vcvtop__ shape_1 shape_2 v_vcvtop v_lane_) →
  Forall (fun (ret_val_elem : lane_) => wf_lane_ (fun_lanetype shape_2) ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 -/
inductive fun_vextunop__ : ishape → ishape → vextunop_ → vec_ → vec_ → Prop where
  | fun_vextunop___case_0 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_lst : List lane_) (c : vec_) :
    ci_lst = (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1) →
    Forall (fun (ci_2_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_elem))) ≠ none) ci_lst →
    Forall (fun (ci_2_elem : lane_) => (proj_lane__0 ci_2_elem) ≠ none) ci_lst →
    (concat_ iN (Map₂ (fun (cj_1_1_elem : iN) (cj_2_1_elem : iN) => [cj_1_1_elem, cj_2_1_elem]) cj_1_lst cj_2_lst)) = (Map (fun (ci_2_elem : lane_) => extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_elem))))) ci_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun (cj_1_2_elem : iN) (cj_2_2_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_2_elem cj_2_2_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) = (List.length cj_2_lst) →
    Forall₂ (fun (cj_1_3_elem : iN) (cj_2_3_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_3_elem cj_2_3_elem)))) cj_1_lst cj_2_lst →
    M_1 = M_1_0 →
    fun_vextunop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextunop_.mk_vextunop__0 Jnn.I32 M_1_0 (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_1 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_lst : List lane_) (c : vec_) :
    ci_lst = (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1) →
    Forall (fun (ci_4_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_4_elem))) ≠ none) ci_lst →
    Forall (fun (ci_4_elem : lane_) => (proj_lane__0 ci_4_elem) ≠ none) ci_lst →
    (concat_ iN (Map₂ (fun (cj_1_4_elem : iN) (cj_2_4_elem : iN) => [cj_1_4_elem, cj_2_4_elem]) cj_1_lst cj_2_lst)) = (Map (fun (ci_4_elem : lane_) => extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_4_elem))))) ci_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun (cj_1_5_elem : iN) (cj_2_5_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_5_elem cj_2_5_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) = (List.length cj_2_lst) →
    Forall₂ (fun (cj_1_6_elem : iN) (cj_2_6_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_6_elem cj_2_6_elem)))) cj_1_lst cj_2_lst →
    M_1 = M_1_0 →
    fun_vextunop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextunop_.mk_vextunop__0 Jnn.I32 M_1_0 (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_2 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_lst : List lane_) (c : vec_) :
    ci_lst = (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1) →
    Forall (fun (ci_6_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_6_elem))) ≠ none) ci_lst →
    Forall (fun (ci_6_elem : lane_) => (proj_lane__0 ci_6_elem) ≠ none) ci_lst →
    (concat_ iN (Map₂ (fun (cj_1_7_elem : iN) (cj_2_7_elem : iN) => [cj_1_7_elem, cj_2_7_elem]) cj_1_lst cj_2_lst)) = (Map (fun (ci_6_elem : lane_) => extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_6_elem))))) ci_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun (cj_1_8_elem : iN) (cj_2_8_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_8_elem cj_2_8_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) = (List.length cj_2_lst) →
    Forall₂ (fun (cj_1_9_elem : iN) (cj_2_9_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_9_elem cj_2_9_elem)))) cj_1_lst cj_2_lst →
    M_1 = M_1_0 →
    fun_vextunop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextunop_.mk_vextunop__0 Jnn.I64 M_1_0 (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_3 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_lst : List lane_) (c : vec_) :
    ci_lst = (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1) →
    Forall (fun (ci_8_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_8_elem))) ≠ none) ci_lst →
    Forall (fun (ci_8_elem : lane_) => (proj_lane__0 ci_8_elem) ≠ none) ci_lst →
    (concat_ iN (Map₂ (fun (cj_1_10_elem : iN) (cj_2_10_elem : iN) => [cj_1_10_elem, cj_2_10_elem]) cj_1_lst cj_2_lst)) = (Map (fun (ci_8_elem : lane_) => extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_8_elem))))) ci_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun (cj_1_11_elem : iN) (cj_2_11_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_11_elem cj_2_11_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) = (List.length cj_2_lst) →
    Forall₂ (fun (cj_1_12_elem : iN) (cj_2_12_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_12_elem cj_2_12_elem)))) cj_1_lst cj_2_lst →
    M_1 = M_1_0 →
    fun_vextunop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextunop_.mk_vextunop__0 Jnn.I64 M_1_0 (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)) c_1 c


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:583.6-583.17 -/
theorem vextunop___is_wf (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop_ : vextunop_) (v_vec_ : vec_) (ret_val : vec_) (var_0 : vec_) :
  fun_vextunop__ ishape_1 ishape_2 v_vextunop_ v_vec_ var_0 →
  wf_ishape ishape_1 →
  wf_ishape ishape_2 →
  wf_vextunop_ ishape_1 v_vextunop_ →
  wf_uN 128 v_vec_ →
  ret_val = var_0 →
  wf_uN 128 ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 -/
inductive fun_vextbinop__ : ishape → ishape → vextbinop_ → vec_ → vec_ → vec_ → Prop where
  | fun_vextbinop___case_0 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) :
    ci_1_lst = (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1))) →
    ci_2_lst = (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_2))) →
    Forall (fun (ci_1_2_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_2_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_2_elem : lane_) => (proj_lane__0 ci_1_2_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_2_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_2_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_2_elem : lane_) => (proj_lane__0 ci_2_2_elem) ≠ none) ci_2_lst →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun (ci_1_2_elem : lane_) (ci_2_2_elem : lane_) => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_2_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_2_elem)))))))) ci_1_lst ci_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length ci_1_lst) = (List.length ci_2_lst) →
    Forall (fun (ci_1_3_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_3_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_3_elem : lane_) => (proj_lane__0 ci_1_3_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_3_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_3_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_3_elem : lane_) => (proj_lane__0 ci_2_3_elem) ≠ none) ci_2_lst →
    Forall₂ (fun (ci_1_3_elem : lane_) (ci_2_3_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_3_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_3_elem))))))))) ci_1_lst ci_2_lst →
    M_1 = M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I32 M_1_0 (vextbinop_Jnn_N.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_1 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) :
    ci_1_lst = (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1))) →
    ci_2_lst = (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_2))) →
    Forall (fun (ci_1_5_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_5_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_5_elem : lane_) => (proj_lane__0 ci_1_5_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_5_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_5_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_5_elem : lane_) => (proj_lane__0 ci_2_5_elem) ≠ none) ci_2_lst →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun (ci_1_5_elem : lane_) (ci_2_5_elem : lane_) => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_5_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_5_elem)))))))) ci_1_lst ci_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length ci_1_lst) = (List.length ci_2_lst) →
    Forall (fun (ci_1_6_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_6_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_6_elem : lane_) => (proj_lane__0 ci_1_6_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_6_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_6_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_6_elem : lane_) => (proj_lane__0 ci_2_6_elem) ≠ none) ci_2_lst →
    Forall₂ (fun (ci_1_6_elem : lane_) (ci_2_6_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_6_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_6_elem))))))))) ci_1_lst ci_2_lst →
    M_1 = M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I32 M_1_0 (vextbinop_Jnn_N.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_2 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) :
    ci_1_lst = (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1))) →
    ci_2_lst = (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_2))) →
    Forall (fun (ci_1_8_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_8_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_8_elem : lane_) => (proj_lane__0 ci_1_8_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_8_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_8_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_8_elem : lane_) => (proj_lane__0 ci_2_8_elem) ≠ none) ci_2_lst →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun (ci_1_8_elem : lane_) (ci_2_8_elem : lane_) => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_8_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_8_elem)))))))) ci_1_lst ci_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length ci_1_lst) = (List.length ci_2_lst) →
    Forall (fun (ci_1_9_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_9_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_9_elem : lane_) => (proj_lane__0 ci_1_9_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_9_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_9_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_9_elem : lane_) => (proj_lane__0 ci_2_9_elem) ≠ none) ci_2_lst →
    Forall₂ (fun (ci_1_9_elem : lane_) (ci_2_9_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_9_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_9_elem))))))))) ci_1_lst ci_2_lst →
    M_1 = M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I64 M_1_0 (vextbinop_Jnn_N.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_3 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) :
    ci_1_lst = (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1))) →
    ci_2_lst = (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_2))) →
    Forall (fun (ci_1_11_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_11_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_11_elem : lane_) => (proj_lane__0 ci_1_11_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_11_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_11_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_11_elem : lane_) => (proj_lane__0 ci_2_11_elem) ≠ none) ci_2_lst →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun (ci_1_11_elem : lane_) (ci_2_11_elem : lane_) => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_11_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_11_elem)))))))) ci_1_lst ci_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length ci_1_lst) = (List.length ci_2_lst) →
    Forall (fun (ci_1_12_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_12_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_12_elem : lane_) => (proj_lane__0 ci_1_12_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_12_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_12_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_12_elem : lane_) => (proj_lane__0 ci_2_12_elem) ≠ none) ci_2_lst →
    Forall₂ (fun (ci_1_12_elem : lane_) (ci_2_12_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_12_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_12_elem))))))))) ci_1_lst ci_2_lst →
    M_1 = M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I64 M_1_0 (vextbinop_Jnn_N.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_4 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) :
    ci_1_lst = (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1) →
    ci_2_lst = (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_2) →
    Forall (fun (ci_1_14_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_14_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_14_elem : lane_) => (proj_lane__0 ci_1_14_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_14_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_14_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_14_elem : lane_) => (proj_lane__0 ci_2_14_elem) ≠ none) ci_2_lst →
    (concat_ iN (Map₂ (fun (cj_1_13_elem : iN) (cj_2_13_elem : iN) => [cj_1_13_elem, cj_2_13_elem]) cj_1_lst cj_2_lst)) = (Map₂ (fun (ci_1_14_elem : lane_) (ci_2_14_elem : lane_) => imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_14_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_14_elem)))))) ci_1_lst ci_2_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun (cj_1_14_elem : iN) (cj_2_14_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_14_elem cj_2_14_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) = (List.length cj_2_lst) →
    Forall₂ (fun (cj_1_15_elem : iN) (cj_2_15_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_15_elem cj_2_15_elem)))) cj_1_lst cj_2_lst →
    M_1 = M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I32 M_1_0 vextbinop_Jnn_N.DOTS) c_1 c_2 c
  | fun_vextbinop___case_5 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) :
    ci_1_lst = (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1) →
    ci_2_lst = (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_2) →
    Forall (fun (ci_1_16_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_16_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_16_elem : lane_) => (proj_lane__0 ci_1_16_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_16_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_16_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_16_elem : lane_) => (proj_lane__0 ci_2_16_elem) ≠ none) ci_2_lst →
    (concat_ iN (Map₂ (fun (cj_1_16_elem : iN) (cj_2_16_elem : iN) => [cj_1_16_elem, cj_2_16_elem]) cj_1_lst cj_2_lst)) = (Map₂ (fun (ci_1_16_elem : lane_) (ci_2_16_elem : lane_) => imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_16_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_16_elem)))))) ci_1_lst ci_2_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun (cj_1_17_elem : iN) (cj_2_17_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_17_elem cj_2_17_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) = (List.length cj_2_lst) →
    Forall₂ (fun (cj_1_18_elem : iN) (cj_2_18_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_18_elem cj_2_18_elem)))) cj_1_lst cj_2_lst →
    M_1 = M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I32 M_1_0 vextbinop_Jnn_N.DOTS) c_1 c_2 c
  | fun_vextbinop___case_6 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) :
    ci_1_lst = (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1) →
    ci_2_lst = (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_2) →
    Forall (fun (ci_1_18_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_18_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_18_elem : lane_) => (proj_lane__0 ci_1_18_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_18_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_18_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_18_elem : lane_) => (proj_lane__0 ci_2_18_elem) ≠ none) ci_2_lst →
    (concat_ iN (Map₂ (fun (cj_1_19_elem : iN) (cj_2_19_elem : iN) => [cj_1_19_elem, cj_2_19_elem]) cj_1_lst cj_2_lst)) = (Map₂ (fun (ci_1_18_elem : lane_) (ci_2_18_elem : lane_) => imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_18_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_18_elem)))))) ci_1_lst ci_2_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun (cj_1_20_elem : iN) (cj_2_20_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_20_elem cj_2_20_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) = (List.length cj_2_lst) →
    Forall₂ (fun (cj_1_21_elem : iN) (cj_2_21_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_21_elem cj_2_21_elem)))) cj_1_lst cj_2_lst →
    M_1 = M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I64 M_1_0 vextbinop_Jnn_N.DOTS) c_1 c_2 c
  | fun_vextbinop___case_7 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) :
    ci_1_lst = (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1) →
    ci_2_lst = (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_2) →
    Forall (fun (ci_1_20_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_1_20_elem))) ≠ none) ci_1_lst →
    Forall (fun (ci_1_20_elem : lane_) => (proj_lane__0 ci_1_20_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_2_20_elem : lane_) => (proj_num__0 (Option.get! (proj_lane__0 ci_2_20_elem))) ≠ none) ci_2_lst →
    Forall (fun (ci_2_20_elem : lane_) => (proj_lane__0 ci_2_20_elem) ≠ none) ci_2_lst →
    (concat_ iN (Map₂ (fun (cj_1_22_elem : iN) (cj_2_22_elem : iN) => [cj_1_22_elem, cj_2_22_elem]) cj_1_lst cj_2_lst)) = (Map₂ (fun (ci_1_20_elem : lane_) (ci_2_20_elem : lane_) => imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_20_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_20_elem)))))) ci_1_lst ci_2_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun (cj_1_23_elem : iN) (cj_2_23_elem : iN) => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_23_elem cj_2_23_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) = (List.length cj_2_lst) →
    Forall₂ (fun (cj_1_24_elem : iN) (cj_2_24_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_24_elem cj_2_24_elem)))) cj_1_lst cj_2_lst →
    M_1 = M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I64 M_1_0 vextbinop_Jnn_N.DOTS) c_1 c_2 c


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:585.6-585.18 -/
theorem vextbinop___is_wf (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop_ : vextbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_) :
  fun_vextbinop__ ishape_1 ishape_2 v_vextbinop_ v_vec_ vec__0 var_0 →
  wf_ishape ishape_1 →
  wf_ishape ishape_2 →
  wf_vextbinop_ ishape_1 v_vextbinop_ →
  wf_uN 128 v_vec_ →
  wf_uN 128 vec__0 →
  ret_val = var_0 →
  wf_uN 128 ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 -/
inductive fun_vshiftop_ : ishape → vshiftop_ → lane_ → u32 → lane_ → Prop where
  | fun_vshiftop__case_0 (v_Jnn : Jnn) (v_M : Nat) (lane : uN) (v_n : Nat) (Jnn_1 : Jnn) (Jnn_0 : Jnn) (M_0 : Nat) :
    v_Jnn = Jnn_1 →
    v_Jnn = Jnn_0 →
    v_M = M_0 →
    fun_vshiftop_ (ishape.X v_Jnn (dim.mk_dim v_M)) (vshiftop_.mk_vshiftop__0 Jnn_0 M_0 vshiftop_Jnn_N.SHL) (lane_.mk_lane__2 Jnn_1 lane) (uN.mk_uN v_n) (lane_.mk_lane__2 v_Jnn (ishl_ (lsizenn (lanetype_Jnn v_Jnn)) lane (uN.mk_uN v_n)))
  | fun_vshiftop__case_1 (v_Jnn : Jnn) (v_M : Nat) (v_sx : sx) (lane : uN) (v_n : Nat) (Jnn_1 : Jnn) (Jnn_0 : Jnn) (M_0 : Nat) :
    v_Jnn = Jnn_1 →
    v_Jnn = Jnn_0 →
    v_M = M_0 →
    fun_vshiftop_ (ishape.X v_Jnn (dim.mk_dim v_M)) (vshiftop_.mk_vshiftop__0 Jnn_0 M_0 (vshiftop_Jnn_N.SHR v_sx)) (lane_.mk_lane__2 Jnn_1 lane) (uN.mk_uN v_n) (lane_.mk_lane__2 v_Jnn (ishr_ (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (uN.mk_uN v_n)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/3-numerics.spectec:608.6-608.16 -/
theorem vshiftop__is_wf (v_ishape : ishape) (v_vshiftop_ : vshiftop_) (v_lane_ : lane_) (v_u32 : u32) (ret_val : lane_) (var_0 : lane_) :
  fun_vshiftop_ v_ishape v_vshiftop_ v_lane_ v_u32 var_0 →
  wf_ishape v_ishape →
  wf_vshiftop_ v_ishape v_vshiftop_ →
  wf_lane_ (fun_lanetype (shape_ishape v_ishape)) v_lane_ →
  wf_uN 32 v_u32 →
  ret_val = var_0 →
  wf_lane_ (fun_lanetype (shape_ishape v_ishape)) ret_val :=
  sorry

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
  | CONST (v_numtype : numtype) (_ : num_) : num
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:37.8-37.11 -/
inductive wf_num : num → Prop where
  | num_case_0 (v_numtype : numtype) (var_0 : num_) :
    wf_num_ v_numtype var_0 →
    wf_num (num.CONST v_numtype var_0)


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.1-40.62 -/
inductive vec : Type where
  | VCONST (v_vectype : vectype) (_ : vec_) : vec
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:39.8-39.11 -/
inductive wf_vec : vec → Prop where
  | vec_case_0 (v_vectype : vectype) (var_0 : vec_) :
    (size (valtype_vectype v_vectype)) ≠ none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) var_0 →
    wf_vec (vec.VCONST v_vectype var_0)


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:41.1-42.71 -/
inductive ref : Type where
  | REF_NULL (v_reftype : reftype) : ref
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : ref
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : ref
deriving Inhabited, BEq

/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.1-44.20 -/
inductive val : Type where
  | CONST (v_numtype : numtype) (_ : num_) : val
  | VCONST (v_vectype : vectype) (_ : vec_) : val
  | REF_NULL (v_reftype : reftype) : val
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : val
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : val
deriving Inhabited, BEq

/- Auxiliary Definition at:  -/
def val_ref (var_0 : ref) : val :=
  match var_0 with
  | ref.REF_NULL x0 => val.REF_NULL x0
  | ref.REF_FUNC_ADDR x0 => val.REF_FUNC_ADDR x0
  | ref.REF_HOST_ADDR x0 => val.REF_HOST_ADDR x0

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:43.8-43.11 -/
inductive wf_val : val → Prop where
  | val_case_0 (v_numtype : numtype) (var_0 : num_) :
    wf_num_ v_numtype var_0 →
    wf_val (val.CONST v_numtype var_0)
  | val_case_1 (v_vectype : vectype) (var_0 : vec_) :
    (size (valtype_vectype v_vectype)) ≠ none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) var_0 →
    wf_val (val.VCONST v_vectype var_0)
  | val_case_2 (v_reftype : reftype) : wf_val (val.REF_NULL v_reftype)
  | val_case_3 (v_funcaddr : funcaddr) : wf_val (val.REF_FUNC_ADDR v_funcaddr)
  | val_case_4 (v_hostaddr : hostaddr) : wf_val (val.REF_HOST_ADDR v_hostaddr)


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.1-47.22 -/
inductive result : Type where
  | _VALS (val_lst : List val) : result
  | TRAP : result
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:46.8-46.14 -/
inductive wf_result : result → Prop where
  | result_case_0 (val_lst : List val) :
    Forall (fun (v_val_elem : val) => wf_val v_val_elem) val_lst →
    wf_result (result._VALS val_lst)
  | result_case_1 : wf_result result.TRAP


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.1-80.22 -/
structure exportinst where
  MKexportinst ::
  NAME : name
  ADDR : externaddr
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:78.8-78.18 -/
inductive wf_exportinst : exportinst → Prop where
  | exportinst_case_ (var_0 : name) (var_1 : externaddr) :
    wf_name var_0 →
    wf_exportinst ({
      NAME := var_0
      ADDR := var_1 : exportinst
    })


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.1-90.26 -/
structure moduleinst where
  MKmoduleinst ::
  TYPES : List functype
  FUNCS : List funcaddr
  GLOBALS : List globaladdr
  TABLES : List tableaddr
  MEMS : List memaddr
  ELEMS : List elemaddr
  DATAS : List dataaddr
  EXPORTS : List exportinst
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:82.8-82.18 -/
inductive wf_moduleinst : moduleinst → Prop where
  | moduleinst_case_ (var_0_lst : List functype) (var_1_lst : List funcaddr) (var_2_lst : List globaladdr) (var_3_lst : List tableaddr) (var_4_lst : List memaddr) (var_5_lst : List elemaddr) (var_6_lst : List dataaddr) (var_7_lst : List exportinst) :
    Forall (fun (var_7_elem : exportinst) => wf_exportinst var_7_elem) var_7_lst →
    wf_moduleinst ({
      TYPES := var_0_lst
      FUNCS := var_1_lst
      GLOBALS := var_2_lst
      TABLES := var_3_lst
      MEMS := var_4_lst
      ELEMS := var_5_lst
      DATAS := var_6_lst
      EXPORTS := var_7_lst : moduleinst
    })


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.1-63.16 -/
structure funcinst where
  MKfuncinst ::
  TYPE : functype
  MODULE : moduleinst
  CODE : func
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:60.8-60.16 -/
inductive wf_funcinst : funcinst → Prop where
  | funcinst_case_ (var_0 : functype) (var_1 : moduleinst) (var_2 : func) :
    wf_moduleinst var_1 →
    wf_func var_2 →
    wf_funcinst ({
      TYPE := var_0
      MODULE := var_1
      CODE := var_2 : funcinst
    })


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.1-66.16 -/
structure globalinst where
  MKglobalinst ::
  TYPE : globaltype
  VALUE : val
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:64.8-64.18 -/
inductive wf_globalinst : globalinst → Prop where
  | globalinst_case_ (var_0 : globaltype) (var_1 : val) :
    wf_val var_1 →
    wf_globalinst ({
      TYPE := var_0
      VALUE := var_1 : globalinst
    })


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.1-69.16 -/
structure tableinst where
  MKtableinst ::
  TYPE : tabletype
  REFS : List ref
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:67.8-67.17 -/
inductive wf_tableinst : tableinst → Prop where
  | tableinst_case_ (var_0 : tabletype) (var_1_lst : List ref) :
    wf_tabletype var_0 →
    wf_tableinst ({
      TYPE := var_0
      REFS := var_1_lst : tableinst
    })


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.1-72.18 -/
structure meminst where
  MKmeminst ::
  TYPE : memtype
  BYTES : List byte
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:70.8-70.15 -/
inductive wf_meminst : meminst → Prop where
  | meminst_case_ (var_0 : memtype) (var_1_lst : List byte) :
    wf_memtype var_0 →
    Forall (fun (var_1_elem : byte) => wf_byte var_1_elem) var_1_lst →
    wf_meminst ({
      TYPE := var_0
      BYTES := var_1_lst : meminst
    })


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:73.1-75.16 -/
structure eleminst where
  MKeleminst ::
  TYPE : elemtype
  REFS : List ref
deriving Inhabited, BEq

/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.1-77.18 -/
structure datainst where
  MKdatainst ::
  BYTES : List byte
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:76.8-76.16 -/
inductive wf_datainst : datainst → Prop where
  | datainst_case_ (var_0_lst : List byte) :
    Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst →
    wf_datainst ({
      BYTES := var_0_lst : datainst
    })


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.1-110.22 -/
structure store where
  MKstore ::
  FUNCS : List funcinst
  GLOBALS : List globalinst
  TABLES : List tableinst
  MEMS : List meminst
  ELEMS : List eleminst
  DATAS : List datainst
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:104.8-104.13 -/
inductive wf_store : store → Prop where
  | store_case_ (var_0_lst : List funcinst) (var_1_lst : List globalinst) (var_2_lst : List tableinst) (var_3_lst : List meminst) (var_4_lst : List eleminst) (var_5_lst : List datainst) :
    Forall (fun (var_0_elem : funcinst) => wf_funcinst var_0_elem) var_0_lst →
    Forall (fun (var_1_elem : globalinst) => wf_globalinst var_1_elem) var_1_lst →
    Forall (fun (var_2_elem : tableinst) => wf_tableinst var_2_elem) var_2_lst →
    Forall (fun (var_3_elem : meminst) => wf_meminst var_3_elem) var_3_lst →
    Forall (fun (var_5_elem : datainst) => wf_datainst var_5_elem) var_5_lst →
    wf_store ({
      FUNCS := var_0_lst
      GLOBALS := var_1_lst
      TABLES := var_2_lst
      MEMS := var_3_lst
      ELEMS := var_4_lst
      DATAS := var_5_lst : store
    })


/- Record Creation Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.1-114.24 -/
structure frame where
  MKframe ::
  LOCALS : List val
  MODULE : moduleinst
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:112.8-112.13 -/
inductive wf_frame : frame → Prop where
  | frame_case_ (var_0_lst : List val) (var_1 : moduleinst) :
    Forall (fun (var_0_elem : val) => wf_val var_0_elem) var_0_lst →
    wf_moduleinst var_1 →
    wf_frame ({
      LOCALS := var_0_lst
      MODULE := var_1 : frame
    })


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.1-116.47 -/
inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:116.8-116.13 -/
inductive wf_state : state → Prop where
  | state_case_0 (v_store : store) (v_frame : frame) :
    wf_store v_store →
    wf_frame v_frame →
    wf_state (state.mk_state v_store v_frame)


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.1-135.9 -/
inductive admininstr : Type where
  | NOP : admininstr
  | UNREACHABLE : admininstr
  | DROP : admininstr
  | SELECT (valtype_lst_opt : Option (List valtype)) : admininstr
  | BLOCK (v_blocktype : blocktype) (instr_lst : List instr) : admininstr
  | LOOP (v_blocktype : blocktype) (instr_lst : List instr) : admininstr
  | IFELSE (v_blocktype : blocktype) (instr_lst_0 : List instr) (instr_lst_1 : List instr) : admininstr
  | BR (v_labelidx : labelidx) : admininstr
  | BR_IF (v_labelidx : labelidx) : admininstr
  | BR_TABLE (labelidx_lst : List labelidx) (v_labelidx : labelidx) : admininstr
  | CALL (v_funcidx : funcidx) : admininstr
  | CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : admininstr
  | RETURN : admininstr
  | CONST (v_numtype : numtype) (_ : num_) : admininstr
  | UNOP (v_numtype : numtype) (_ : unop_) : admininstr
  | BINOP (v_numtype : numtype) (_ : binop_) : admininstr
  | TESTOP (v_numtype : numtype) (_ : testop_) : admininstr
  | RELOP (v_numtype : numtype) (_ : relop_) : admininstr
  | CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (_ : cvtop__) : admininstr
  | EXTEND (v_numtype : numtype) (v_n : n) : admininstr
  | VCONST (v_vectype : vectype) (_ : vec_) : admininstr
  | VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : admininstr
  | VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : admininstr
  | VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : admininstr
  | VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : admininstr
  | VUNOP (v_shape : shape) (_ : vunop_) : admininstr
  | VBINOP (v_shape : shape) (_ : vbinop_) : admininstr
  | VTESTOP (v_shape : shape) (_ : vtestop_) : admininstr
  | VRELOP (v_shape : shape) (_ : vrelop_) : admininstr
  | VSHIFTOP (v_ishape : ishape) (_ : vshiftop_) : admininstr
  | VBITMASK (v_ishape : ishape) : admininstr
  | VSWIZZLE (v_ishape : ishape) : admininstr
  | VSHUFFLE (v_ishape : ishape) (laneidx_lst : List laneidx) : admininstr
  | VSPLAT (v_shape : shape) : admininstr
  | VEXTRACT_LANE (v_shape : shape) (sx_opt : Option sx) (v_laneidx : laneidx) : admininstr
  | VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : admininstr
  | VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextunop_) : admininstr
  | VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextbinop_) : admininstr
  | VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : admininstr
  | VCVTOP (v_shape_0 : shape) (v_shape_1 : shape) (v_vcvtop : vcvtop) : admininstr
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
  | TABLE_COPY (v_tableidx_0 : tableidx) (v_tableidx_1 : tableidx) : admininstr
  | TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : admininstr
  | ELEM_DROP (v_elemidx : elemidx) : admininstr
  | LOAD (v_numtype : numtype) (_ : Option loadop_) (v_memarg : memarg) : admininstr
  | STORE (v_numtype : numtype) (sz_opt : Option sz) (v_memarg : memarg) : admininstr
  | VLOAD (v_vectype : vectype) (vloadop_opt : Option vloadop) (v_memarg : memarg) : admininstr
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
  | LABEL_ (v_n : n) (instr_lst : List instr) (admininstr_lst : List admininstr) : admininstr
  | FRAME_ (v_n : n) (v_frame : frame) (admininstr_lst : List admininstr) : admininstr
  | TRAP : admininstr
deriving Inhabited, BEq

/- Auxiliary Definition at:  -/
def admininstr_instr (var_0 : instr) : admininstr :=
  match var_0 with
  | instr.NOP => admininstr.NOP
  | instr.UNREACHABLE => admininstr.UNREACHABLE
  | instr.DROP => admininstr.DROP
  | instr.SELECT x0 => admininstr.SELECT x0
  | instr.BLOCK x0 x1 => admininstr.BLOCK x0 x1
  | instr.LOOP x0 x1 => admininstr.LOOP x0 x1
  | instr.IFELSE x0 x1 x2 => admininstr.IFELSE x0 x1 x2
  | instr.BR x0 => admininstr.BR x0
  | instr.BR_IF x0 => admininstr.BR_IF x0
  | instr.BR_TABLE x0 x1 => admininstr.BR_TABLE x0 x1
  | instr.CALL x0 => admininstr.CALL x0
  | instr.CALL_INDIRECT x0 x1 => admininstr.CALL_INDIRECT x0 x1
  | instr.RETURN => admininstr.RETURN
  | instr.CONST x0 x1 => admininstr.CONST x0 x1
  | instr.UNOP x0 x1 => admininstr.UNOP x0 x1
  | instr.BINOP x0 x1 => admininstr.BINOP x0 x1
  | instr.TESTOP x0 x1 => admininstr.TESTOP x0 x1
  | instr.RELOP x0 x1 => admininstr.RELOP x0 x1
  | instr.CVTOP x0 x1 x2 => admininstr.CVTOP x0 x1 x2
  | instr.EXTEND x0 x1 => admininstr.EXTEND x0 x1
  | instr.VCONST x0 x1 => admininstr.VCONST x0 x1
  | instr.VVUNOP x0 x1 => admininstr.VVUNOP x0 x1
  | instr.VVBINOP x0 x1 => admininstr.VVBINOP x0 x1
  | instr.VVTERNOP x0 x1 => admininstr.VVTERNOP x0 x1
  | instr.VVTESTOP x0 x1 => admininstr.VVTESTOP x0 x1
  | instr.VUNOP x0 x1 => admininstr.VUNOP x0 x1
  | instr.VBINOP x0 x1 => admininstr.VBINOP x0 x1
  | instr.VTESTOP x0 x1 => admininstr.VTESTOP x0 x1
  | instr.VRELOP x0 x1 => admininstr.VRELOP x0 x1
  | instr.VSHIFTOP x0 x1 => admininstr.VSHIFTOP x0 x1
  | instr.VBITMASK x0 => admininstr.VBITMASK x0
  | instr.VSWIZZLE x0 => admininstr.VSWIZZLE x0
  | instr.VSHUFFLE x0 x1 => admininstr.VSHUFFLE x0 x1
  | instr.VSPLAT x0 => admininstr.VSPLAT x0
  | instr.VEXTRACT_LANE x0 x1 x2 => admininstr.VEXTRACT_LANE x0 x1 x2
  | instr.VREPLACE_LANE x0 x1 => admininstr.VREPLACE_LANE x0 x1
  | instr.VEXTUNOP x0 x1 x2 => admininstr.VEXTUNOP x0 x1 x2
  | instr.VEXTBINOP x0 x1 x2 => admininstr.VEXTBINOP x0 x1 x2
  | instr.VNARROW x0 x1 x2 => admininstr.VNARROW x0 x1 x2
  | instr.VCVTOP x0 x1 x2 => admininstr.VCVTOP x0 x1 x2
  | instr.REF_NULL x0 => admininstr.REF_NULL x0
  | instr.REF_FUNC x0 => admininstr.REF_FUNC x0
  | instr.REF_IS_NULL => admininstr.REF_IS_NULL
  | instr.LOCAL_GET x0 => admininstr.LOCAL_GET x0
  | instr.LOCAL_SET x0 => admininstr.LOCAL_SET x0
  | instr.LOCAL_TEE x0 => admininstr.LOCAL_TEE x0
  | instr.GLOBAL_GET x0 => admininstr.GLOBAL_GET x0
  | instr.GLOBAL_SET x0 => admininstr.GLOBAL_SET x0
  | instr.TABLE_GET x0 => admininstr.TABLE_GET x0
  | instr.TABLE_SET x0 => admininstr.TABLE_SET x0
  | instr.TABLE_SIZE x0 => admininstr.TABLE_SIZE x0
  | instr.TABLE_GROW x0 => admininstr.TABLE_GROW x0
  | instr.TABLE_FILL x0 => admininstr.TABLE_FILL x0
  | instr.TABLE_COPY x0 x1 => admininstr.TABLE_COPY x0 x1
  | instr.TABLE_INIT x0 x1 => admininstr.TABLE_INIT x0 x1
  | instr.ELEM_DROP x0 => admininstr.ELEM_DROP x0
  | instr.LOAD x0 x1 x2 => admininstr.LOAD x0 x1 x2
  | instr.STORE x0 x1 x2 => admininstr.STORE x0 x1 x2
  | instr.VLOAD x0 x1 x2 => admininstr.VLOAD x0 x1 x2
  | instr.VLOAD_LANE x0 x1 x2 x3 => admininstr.VLOAD_LANE x0 x1 x2 x3
  | instr.VSTORE x0 x1 => admininstr.VSTORE x0 x1
  | instr.VSTORE_LANE x0 x1 x2 x3 => admininstr.VSTORE_LANE x0 x1 x2 x3
  | instr.MEMORY_SIZE => admininstr.MEMORY_SIZE
  | instr.MEMORY_GROW => admininstr.MEMORY_GROW
  | instr.MEMORY_FILL => admininstr.MEMORY_FILL
  | instr.MEMORY_COPY => admininstr.MEMORY_COPY
  | instr.MEMORY_INIT x0 => admininstr.MEMORY_INIT x0
  | instr.DATA_DROP x0 => admininstr.DATA_DROP x0

/- Auxiliary Definition at:  -/
def admininstr_ref (var_0 : ref) : admininstr :=
  match var_0 with
  | ref.REF_NULL x0 => admininstr.REF_NULL x0
  | ref.REF_FUNC_ADDR x0 => admininstr.REF_FUNC_ADDR x0
  | ref.REF_HOST_ADDR x0 => admininstr.REF_HOST_ADDR x0

/- Auxiliary Definition at:  -/
def admininstr_val (var_0 : val) : admininstr :=
  match var_0 with
  | val.CONST x0 x1 => admininstr.CONST x0 x1
  | val.VCONST x0 x1 => admininstr.VCONST x0 x1
  | val.REF_NULL x0 => admininstr.REF_NULL x0
  | val.REF_FUNC_ADDR x0 => admininstr.REF_FUNC_ADDR x0
  | val.REF_HOST_ADDR x0 => admininstr.REF_HOST_ADDR x0

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:128.8-128.18 -/
inductive wf_admininstr : admininstr → Prop where
  | admininstr_case_0 : wf_admininstr admininstr.NOP
  | admininstr_case_1 : wf_admininstr admininstr.UNREACHABLE
  | admininstr_case_2 : wf_admininstr admininstr.DROP
  | admininstr_case_3 (valtype_lst_opt : Option (List valtype)) : wf_admininstr (admininstr.SELECT valtype_lst_opt)
  | admininstr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    wf_admininstr (admininstr.BLOCK v_blocktype instr_lst)
  | admininstr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    wf_admininstr (admininstr.LOOP v_blocktype instr_lst)
  | admininstr_case_6 (v_blocktype : blocktype) (instr_lst : List instr) (instr_lst_0_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    Forall (fun (instr_lst_0_elem : instr) => wf_instr instr_lst_0_elem) instr_lst_0_lst →
    wf_admininstr (admininstr.IFELSE v_blocktype instr_lst instr_lst_0_lst)
  | admininstr_case_7 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_admininstr (admininstr.BR v_labelidx)
  | admininstr_case_8 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_admininstr (admininstr.BR_IF v_labelidx)
  | admininstr_case_9 (labelidx_lst : List labelidx) (v_labelidx : labelidx) :
    Forall (fun (v_labelidx_elem : labelidx) => wf_uN 32 v_labelidx_elem) labelidx_lst →
    wf_uN 32 v_labelidx →
    wf_admininstr (admininstr.BR_TABLE labelidx_lst v_labelidx)
  | admininstr_case_10 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_admininstr (admininstr.CALL v_funcidx)
  | admininstr_case_11 (v_tableidx : tableidx) (v_typeidx : typeidx) :
    wf_uN 32 v_tableidx →
    wf_uN 32 v_typeidx →
    wf_admininstr (admininstr.CALL_INDIRECT v_tableidx v_typeidx)
  | admininstr_case_12 : wf_admininstr admininstr.RETURN
  | admininstr_case_13 (v_numtype : numtype) (var_0 : num_) :
    wf_num_ v_numtype var_0 →
    wf_admininstr (admininstr.CONST v_numtype var_0)
  | admininstr_case_14 (v_numtype : numtype) (var_0 : unop_) :
    wf_unop_ v_numtype var_0 →
    wf_admininstr (admininstr.UNOP v_numtype var_0)
  | admininstr_case_15 (v_numtype : numtype) (var_0 : binop_) :
    wf_binop_ v_numtype var_0 →
    wf_admininstr (admininstr.BINOP v_numtype var_0)
  | admininstr_case_16 (v_numtype : numtype) (var_0 : testop_) :
    wf_testop_ v_numtype var_0 →
    wf_admininstr (admininstr.TESTOP v_numtype var_0)
  | admininstr_case_17 (v_numtype : numtype) (var_0 : relop_) :
    wf_relop_ v_numtype var_0 →
    wf_admininstr (admininstr.RELOP v_numtype var_0)
  | admininstr_case_18 (numtype_1 : numtype) (numtype_2 : numtype) (var_0 : cvtop__) :
    wf_cvtop__ numtype_2 numtype_1 var_0 →
    numtype_1 ≠ numtype_2 →
    wf_admininstr (admininstr.CVTOP numtype_1 numtype_2 var_0)
  | admininstr_case_19 (v_numtype : numtype) (v_n : n) : wf_admininstr (admininstr.EXTEND v_numtype v_n)
  | admininstr_case_20 (v_vectype : vectype) (var_0 : vec_) :
    (size (valtype_vectype v_vectype)) ≠ none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) var_0 →
    wf_admininstr (admininstr.VCONST v_vectype var_0)
  | admininstr_case_21 (v_vectype : vectype) (v_vvunop : vvunop) : wf_admininstr (admininstr.VVUNOP v_vectype v_vvunop)
  | admininstr_case_22 (v_vectype : vectype) (v_vvbinop : vvbinop) : wf_admininstr (admininstr.VVBINOP v_vectype v_vvbinop)
  | admininstr_case_23 (v_vectype : vectype) (v_vvternop : vvternop) : wf_admininstr (admininstr.VVTERNOP v_vectype v_vvternop)
  | admininstr_case_24 (v_vectype : vectype) (v_vvtestop : vvtestop) : wf_admininstr (admininstr.VVTESTOP v_vectype v_vvtestop)
  | admininstr_case_25 (v_shape : shape) (var_0 : vunop_) :
    wf_shape v_shape →
    wf_vunop_ v_shape var_0 →
    wf_admininstr (admininstr.VUNOP v_shape var_0)
  | admininstr_case_26 (v_shape : shape) (var_0 : vbinop_) :
    wf_shape v_shape →
    wf_vbinop_ v_shape var_0 →
    wf_admininstr (admininstr.VBINOP v_shape var_0)
  | admininstr_case_27 (v_shape : shape) (var_0 : vtestop_) :
    wf_shape v_shape →
    wf_vtestop_ v_shape var_0 →
    wf_admininstr (admininstr.VTESTOP v_shape var_0)
  | admininstr_case_28 (v_shape : shape) (var_0 : vrelop_) :
    wf_shape v_shape →
    wf_vrelop_ v_shape var_0 →
    wf_admininstr (admininstr.VRELOP v_shape var_0)
  | admininstr_case_29 (v_ishape : ishape) (var_0 : vshiftop_) :
    wf_ishape v_ishape →
    wf_vshiftop_ v_ishape var_0 →
    wf_admininstr (admininstr.VSHIFTOP v_ishape var_0)
  | admininstr_case_30 (v_ishape : ishape) :
    wf_ishape v_ishape →
    wf_admininstr (admininstr.VBITMASK v_ishape)
  | admininstr_case_31 (v_ishape : ishape) :
    wf_ishape v_ishape →
    v_ishape = (ishape.X Jnn.I8 (dim.mk_dim 16)) →
    wf_admininstr (admininstr.VSWIZZLE v_ishape)
  | admininstr_case_32 (v_ishape : ishape) (laneidx_lst : List laneidx) :
    wf_ishape v_ishape →
    Forall (fun (v_laneidx_elem : laneidx) => wf_uN 8 v_laneidx_elem) laneidx_lst →
    (v_ishape = (ishape.X Jnn.I8 (dim.mk_dim 16))) ∧ ((List.length laneidx_lst) = 16) →
    wf_admininstr (admininstr.VSHUFFLE v_ishape laneidx_lst)
  | admininstr_case_33 (v_shape : shape) :
    wf_shape v_shape →
    wf_admininstr (admininstr.VSPLAT v_shape)
  | admininstr_case_34 (v_numtype : numtype) (v_shape : shape) (sx_opt : Option sx) (v_laneidx : laneidx) :
    wf_shape v_shape →
    wf_uN 8 v_laneidx →
    (((fun_lanetype v_shape) = (lanetype_numtype v_numtype)) ↔ (sx_opt = none)) →
    wf_admininstr (admininstr.VEXTRACT_LANE v_shape sx_opt v_laneidx)
  | admininstr_case_35 (v_shape : shape) (v_laneidx : laneidx) :
    wf_shape v_shape →
    wf_uN 8 v_laneidx →
    wf_admininstr (admininstr.VREPLACE_LANE v_shape v_laneidx)
  | admininstr_case_36 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextunop_) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextunop_ ishape_1 var_0 →
    (lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2)))) →
    wf_admininstr (admininstr.VEXTUNOP ishape_1 ishape_2 var_0)
  | admininstr_case_37 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextbinop_) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextbinop_ ishape_1 var_0 →
    (lsize (fun_lanetype (shape_ishape ishape_1))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_2)))) →
    wf_admininstr (admininstr.VEXTBINOP ishape_1 ishape_2 var_0)
  | admininstr_case_38 (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    ((lsize (fun_lanetype (shape_ishape ishape_2))) = (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) ∧ ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) ≤ 32) →
    wf_admininstr (admininstr.VNARROW ishape_1 ishape_2 v_sx)
  | admininstr_case_39 (v_shape : shape) (shape_0 : shape) (v_vcvtop : vcvtop) :
    wf_shape v_shape →
    wf_shape shape_0 →
    wf_admininstr (admininstr.VCVTOP v_shape shape_0 v_vcvtop)
  | admininstr_case_40 (v_reftype : reftype) : wf_admininstr (admininstr.REF_NULL v_reftype)
  | admininstr_case_41 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_admininstr (admininstr.REF_FUNC v_funcidx)
  | admininstr_case_42 : wf_admininstr admininstr.REF_IS_NULL
  | admininstr_case_43 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_admininstr (admininstr.LOCAL_GET v_localidx)
  | admininstr_case_44 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_admininstr (admininstr.LOCAL_SET v_localidx)
  | admininstr_case_45 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_admininstr (admininstr.LOCAL_TEE v_localidx)
  | admininstr_case_46 (v_globalidx : globalidx) :
    wf_uN 32 v_globalidx →
    wf_admininstr (admininstr.GLOBAL_GET v_globalidx)
  | admininstr_case_47 (v_globalidx : globalidx) :
    wf_uN 32 v_globalidx →
    wf_admininstr (admininstr.GLOBAL_SET v_globalidx)
  | admininstr_case_48 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_admininstr (admininstr.TABLE_GET v_tableidx)
  | admininstr_case_49 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_admininstr (admininstr.TABLE_SET v_tableidx)
  | admininstr_case_50 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_admininstr (admininstr.TABLE_SIZE v_tableidx)
  | admininstr_case_51 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_admininstr (admininstr.TABLE_GROW v_tableidx)
  | admininstr_case_52 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_admininstr (admininstr.TABLE_FILL v_tableidx)
  | admininstr_case_53 (v_tableidx : tableidx) (tableidx_0 : tableidx) :
    wf_uN 32 v_tableidx →
    wf_uN 32 tableidx_0 →
    wf_admininstr (admininstr.TABLE_COPY v_tableidx tableidx_0)
  | admininstr_case_54 (v_tableidx : tableidx) (v_elemidx : elemidx) :
    wf_uN 32 v_tableidx →
    wf_uN 32 v_elemidx →
    wf_admininstr (admininstr.TABLE_INIT v_tableidx v_elemidx)
  | admininstr_case_55 (v_elemidx : elemidx) :
    wf_uN 32 v_elemidx →
    wf_admininstr (admininstr.ELEM_DROP v_elemidx)
  | admininstr_case_56 (v_numtype : numtype) (var_0_opt : Option loadop_) (v_memarg : memarg) :
    Forall (fun (var_0_elem : loadop_) => wf_loadop_ v_numtype var_0_elem) (Option.toList var_0_opt) →
    wf_memarg v_memarg →
    wf_admininstr (admininstr.LOAD v_numtype var_0_opt v_memarg)
  | admininstr_case_57 (Inn_opt : Option Inn) (numtype_opt : Option numtype) (v_numtype : numtype) (sz_opt : Option sz) (v_memarg : memarg) :
    Forall (fun (v_sz_elem : sz) => wf_sz v_sz_elem) (Option.toList sz_opt) →
    wf_memarg v_memarg →
    ((Inn_opt = none) ↔ (numtype_opt = none)) →
    ((Inn_opt = none) ↔ (sz_opt = none)) →
    Forall₃ (fun (v_Inn_elem : Inn) (v_numtype_elem : numtype) (v_sz_elem : sz) => (v_numtype_elem = (numtype_Inn v_Inn_elem)) ∧ ((proj_sz_0 v_sz_elem) < (sizenn (numtype_Inn v_Inn_elem)))) (Option.toList Inn_opt) (Option.toList numtype_opt) (Option.toList sz_opt) →
    wf_admininstr (admininstr.STORE v_numtype sz_opt v_memarg)
  | admininstr_case_58 (v_vectype : vectype) (vloadop_opt : Option vloadop) (v_memarg : memarg) :
    wf_memarg v_memarg →
    wf_admininstr (admininstr.VLOAD v_vectype vloadop_opt v_memarg)
  | admininstr_case_59 (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) :
    wf_sz v_sz →
    wf_memarg v_memarg →
    wf_uN 8 v_laneidx →
    wf_admininstr (admininstr.VLOAD_LANE v_vectype v_sz v_memarg v_laneidx)
  | admininstr_case_60 (v_vectype : vectype) (v_memarg : memarg) :
    wf_memarg v_memarg →
    wf_admininstr (admininstr.VSTORE v_vectype v_memarg)
  | admininstr_case_61 (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) :
    wf_sz v_sz →
    wf_memarg v_memarg →
    wf_uN 8 v_laneidx →
    wf_admininstr (admininstr.VSTORE_LANE v_vectype v_sz v_memarg v_laneidx)
  | admininstr_case_62 : wf_admininstr admininstr.MEMORY_SIZE
  | admininstr_case_63 : wf_admininstr admininstr.MEMORY_GROW
  | admininstr_case_64 : wf_admininstr admininstr.MEMORY_FILL
  | admininstr_case_65 : wf_admininstr admininstr.MEMORY_COPY
  | admininstr_case_66 (v_dataidx : dataidx) :
    wf_uN 32 v_dataidx →
    wf_admininstr (admininstr.MEMORY_INIT v_dataidx)
  | admininstr_case_67 (v_dataidx : dataidx) :
    wf_uN 32 v_dataidx →
    wf_admininstr (admininstr.DATA_DROP v_dataidx)
  | admininstr_case_68 (v_funcaddr : funcaddr) : wf_admininstr (admininstr.REF_FUNC_ADDR v_funcaddr)
  | admininstr_case_69 (v_hostaddr : hostaddr) : wf_admininstr (admininstr.REF_HOST_ADDR v_hostaddr)
  | admininstr_case_70 (v_funcaddr : funcaddr) : wf_admininstr (admininstr.CALL_ADDR v_funcaddr)
  | admininstr_case_71 (v_n : n) (instr_lst : List instr) (admininstr_lst : List admininstr) :
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst →
    wf_admininstr (admininstr.LABEL_ v_n instr_lst admininstr_lst)
  | admininstr_case_72 (v_n : n) (v_frame : frame) (admininstr_lst : List admininstr) :
    wf_frame v_frame →
    Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst →
    wf_admininstr (admininstr.FRAME_ v_n v_frame admininstr_lst)
  | admininstr_case_73 : wf_admininstr admininstr.TRAP


/- Inductive Type Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.1-117.62 -/
inductive config : Type where
  | mk_config (v_state : state) (admininstr_lst : List admininstr) : config
deriving Inhabited, BEq

/- Inductive Relations Definition at: ../specification/wasm-2.0/4-runtime.spectec:117.8-117.14 -/
inductive wf_config : config → Prop where
  | config_case_0 (v_state : state) (admininstr_lst : List admininstr) :
    wf_state v_state →
    Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst →
    wf_config (config.mk_config v_state admininstr_lst)


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.1-7.43 -/
def default_ (v_valtype : valtype) : Option val :=
  match v_valtype with
  | valtype.I32 => some (val.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)))
  | valtype.I64 => some (val.CONST numtype.I64 (num_.mk_num__0 Inn.I64 (uN.mk_uN 0)))
  | valtype.F32 => some (val.CONST numtype.F32 (num_.mk_num__1 Fnn.F32 (fzero 32)))
  | valtype.F64 => some (val.CONST numtype.F64 (num_.mk_num__1 Fnn.F64 (fzero 64)))
  | valtype.V128 => some (val.VCONST vectype.V128 (uN.mk_uN 0))
  | valtype.FUNCREF => some (val.REF_NULL reftype.FUNCREF)
  | valtype.EXTERNREF => some (val.REF_NULL reftype.EXTERNREF)
  | _ => none

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:7.6-7.15 -/
theorem default__is_wf (v_valtype : valtype) (ret_val : val) :
  (default_ v_valtype) ≠ none →
  ret_val = (Option.get! (default_ v_valtype)) →
  wf_val ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:20.6-20.14 -/
inductive fun_funcsxa : List externaddr → List funcaddr → Prop where
  | fun_funcsxa_case_0 : fun_funcsxa [] []
  | fun_funcsxa_case_1 (fa : Nat) (xv_lst : List externaddr) (var_0 : List funcaddr) :
    fun_funcsxa xv_lst var_0 →
    fun_funcsxa ([externaddr.FUNC fa] ++ xv_lst) ([fa] ++ var_0)
  | fun_funcsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List funcaddr) :
    fun_funcsxa xv_lst var_0 →
    fun_funcsxa ([v_externaddr] ++ xv_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:21.6-21.16 -/
inductive fun_globalsxa : List externaddr → List globaladdr → Prop where
  | fun_globalsxa_case_0 : fun_globalsxa [] []
  | fun_globalsxa_case_1 (ga : Nat) (xv_lst : List externaddr) (var_0 : List globaladdr) :
    fun_globalsxa xv_lst var_0 →
    fun_globalsxa ([externaddr.GLOBAL ga] ++ xv_lst) ([ga] ++ var_0)
  | fun_globalsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List globaladdr) :
    fun_globalsxa xv_lst var_0 →
    fun_globalsxa ([v_externaddr] ++ xv_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:22.6-22.15 -/
inductive fun_tablesxa : List externaddr → List tableaddr → Prop where
  | fun_tablesxa_case_0 : fun_tablesxa [] []
  | fun_tablesxa_case_1 (ta : Nat) (xv_lst : List externaddr) (var_0 : List tableaddr) :
    fun_tablesxa xv_lst var_0 →
    fun_tablesxa ([externaddr.TABLE ta] ++ xv_lst) ([ta] ++ var_0)
  | fun_tablesxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List tableaddr) :
    fun_tablesxa xv_lst var_0 →
    fun_tablesxa ([v_externaddr] ++ xv_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:23.6-23.13 -/
inductive fun_memsxa : List externaddr → List memaddr → Prop where
  | fun_memsxa_case_0 : fun_memsxa [] []
  | fun_memsxa_case_1 (ma : Nat) (xv_lst : List externaddr) (var_0 : List memaddr) :
    fun_memsxa xv_lst var_0 →
    fun_memsxa ([externaddr.MEM ma] ++ xv_lst) ([ma] ++ var_0)
  | fun_memsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List memaddr) :
    fun_memsxa xv_lst var_0 →
    fun_memsxa ([v_externaddr] ++ xv_lst) var_0


/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.1-48.57 -/
def fun_store (v_state : state) : store :=
  match v_state with
  | state.mk_state s f => s

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:48.6-48.12 -/
theorem store_is_wf (v_state : state) (ret_val : store) :
  wf_state v_state →
  ret_val = (fun_store v_state) →
  wf_store ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.1-49.57 -/
def fun_frame (v_state : state) : frame :=
  match v_state with
  | state.mk_state s f => f

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:49.6-49.12 -/
theorem frame_is_wf (v_state : state) (ret_val : frame) :
  wf_state v_state →
  ret_val = (fun_frame v_state) →
  wf_frame ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:55.1-55.64 -/
def fun_funcaddr (v_state : state) : List funcaddr :=
  match v_state with
  | state.mk_state s f => f.MODULE.FUNCS

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.1-58.57 -/
def fun_funcinst (v_state : state) : List funcinst :=
  match v_state with
  | state.mk_state s f => s.FUNCS

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:58.6-58.15 -/
theorem funcinst_is_wf (v_state : state) (ret_val_lst : List funcinst) :
  wf_state v_state →
  ret_val_lst = (fun_funcinst v_state) →
  Forall (fun (ret_val_elem : funcinst) => wf_funcinst ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.1-59.59 -/
def fun_globalinst (v_state : state) : List globalinst :=
  match v_state with
  | state.mk_state s f => s.GLOBALS

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:59.6-59.17 -/
theorem globalinst_is_wf (v_state : state) (ret_val_lst : List globalinst) :
  wf_state v_state →
  ret_val_lst = (fun_globalinst v_state) →
  Forall (fun (ret_val_elem : globalinst) => wf_globalinst ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.1-60.58 -/
def fun_tableinst (v_state : state) : List tableinst :=
  match v_state with
  | state.mk_state s f => s.TABLES

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:60.6-60.16 -/
theorem tableinst_is_wf (v_state : state) (ret_val_lst : List tableinst) :
  wf_state v_state →
  ret_val_lst = (fun_tableinst v_state) →
  Forall (fun (ret_val_elem : tableinst) => wf_tableinst ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.1-61.56 -/
def fun_meminst (v_state : state) : List meminst :=
  match v_state with
  | state.mk_state s f => s.MEMS

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:61.6-61.14 -/
theorem meminst_is_wf (v_state : state) (ret_val_lst : List meminst) :
  wf_state v_state →
  ret_val_lst = (fun_meminst v_state) →
  Forall (fun (ret_val_elem : meminst) => wf_meminst ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:62.1-62.57 -/
def fun_eleminst (v_state : state) : List eleminst :=
  match v_state with
  | state.mk_state s f => s.ELEMS

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.1-63.57 -/
def fun_datainst (v_state : state) : List datainst :=
  match v_state with
  | state.mk_state s f => s.DATAS

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:63.6-63.15 -/
theorem datainst_is_wf (v_state : state) (ret_val_lst : List datainst) :
  wf_state v_state →
  ret_val_lst = (fun_datainst v_state) →
  Forall (fun (ret_val_elem : datainst) => wf_datainst ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.1-64.58 -/
def fun_moduleinst (v_state : state) : moduleinst :=
  match v_state with
  | state.mk_state s f => f.MODULE

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:64.6-64.17 -/
theorem moduleinst_is_wf (v_state : state) (ret_val : moduleinst) :
  wf_state v_state →
  ret_val = (fun_moduleinst v_state) →
  wf_moduleinst ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:74.1-74.66 -/
def fun_type (v_state : state) (v_typeidx : typeidx) : functype :=
  match v_state with
  | state.mk_state s f => (f.MODULE.TYPES)[proj_uN_0 v_typeidx]!

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.1-75.66 -/
def fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
  match v_state with
  | state.mk_state s f => (s.FUNCS)[(f.MODULE.FUNCS)[proj_uN_0 v_funcidx]!]!

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:75.6-75.11 -/
theorem func_is_wf (v_state : state) (v_funcidx : funcidx) (ret_val : funcinst) :
  wf_state v_state →
  wf_uN 32 v_funcidx →
  ret_val = (fun_func v_state v_funcidx) →
  wf_funcinst ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.1-76.68 -/
def fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
  match v_state with
  | state.mk_state s f => (s.GLOBALS)[(f.MODULE.GLOBALS)[proj_uN_0 v_globalidx]!]!

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:76.6-76.13 -/
theorem global_is_wf (v_state : state) (v_globalidx : globalidx) (ret_val : globalinst) :
  wf_state v_state →
  wf_uN 32 v_globalidx →
  ret_val = (fun_global v_state v_globalidx) →
  wf_globalinst ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.1-77.67 -/
def fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
  match v_state with
  | state.mk_state s f => (s.TABLES)[(f.MODULE.TABLES)[proj_uN_0 v_tableidx]!]!

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:77.6-77.12 -/
theorem table_is_wf (v_state : state) (v_tableidx : tableidx) (ret_val : tableinst) :
  wf_state v_state →
  wf_uN 32 v_tableidx →
  ret_val = (fun_table v_state v_tableidx) →
  wf_tableinst ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.1-78.65 -/
def fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
  match v_state with
  | state.mk_state s f => (s.MEMS)[(f.MODULE.MEMS)[proj_uN_0 v_memidx]!]!

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:78.6-78.10 -/
theorem mem_is_wf (v_state : state) (v_memidx : memidx) (ret_val : meminst) :
  wf_state v_state →
  wf_uN 32 v_memidx →
  ret_val = (fun_mem v_state v_memidx) →
  wf_meminst ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:79.1-79.66 -/
def fun_elem (v_state : state) (v_tableidx : tableidx) : eleminst :=
  match v_state with
  | state.mk_state s f => (s.ELEMS)[(f.MODULE.ELEMS)[proj_uN_0 v_tableidx]!]!

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.1-80.66 -/
def fun_data (v_state : state) (v_dataidx : dataidx) : datainst :=
  match v_state with
  | state.mk_state s f => (s.DATAS)[(f.MODULE.DATAS)[proj_uN_0 v_dataidx]!]!

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:80.6-80.11 -/
theorem data_is_wf (v_state : state) (v_dataidx : dataidx) (ret_val : datainst) :
  wf_state v_state →
  wf_uN 32 v_dataidx →
  ret_val = (fun_data v_state v_dataidx) →
  wf_datainst ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.1-81.67 -/
def fun_local (v_state : state) (v_localidx : localidx) : val :=
  match v_state with
  | state.mk_state s f => (f.LOCALS)[proj_uN_0 v_localidx]!

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:81.6-81.12 -/
theorem local_is_wf (v_state : state) (v_localidx : localidx) (ret_val : val) :
  wf_state v_state →
  wf_uN 32 v_localidx →
  ret_val = (fun_local v_state v_localidx) →
  wf_val ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.1-95.89 -/
def with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state s ({
    f with
    LOCALS := List.modify (f.LOCALS) (proj_uN_0 v_localidx) (fun elem_1 => v_val)
  })

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:95.6-95.17 -/
theorem with_local_is_wf (v_state : state) (v_localidx : localidx) (v_val : val) (ret_val : state) :
  wf_state v_state →
  wf_uN 32 v_localidx →
  wf_val v_val →
  ret_val = (with_local v_state v_localidx v_val) →
  wf_state ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.1-96.96 -/
def with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with
    GLOBALS := List.modify (s.GLOBALS) ((f.MODULE.GLOBALS)[proj_uN_0 v_globalidx]!) (fun elem_1 => {
      elem_1 with
      VALUE := v_val
    })
  }) f

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:96.6-96.18 -/
theorem with_global_is_wf (v_state : state) (v_globalidx : globalidx) (v_val : val) (ret_val : state) :
  wf_state v_state →
  wf_uN 32 v_globalidx →
  wf_val v_val →
  ret_val = (with_global v_state v_globalidx v_val) →
  wf_state ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.1-97.97 -/
def with_table (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_ref : ref) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with
    TABLES := List.modify (s.TABLES) ((f.MODULE.TABLES)[proj_uN_0 v_tableidx]!) (fun elem_1 => {
      elem_1 with
      REFS := List.modify (elem_1.REFS) nat (fun elem_2 => v_ref)
    })
  }) f

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:97.6-97.17 -/
theorem with_table_is_wf (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_ref : ref) (ret_val : state) :
  wf_state v_state →
  wf_uN 32 v_tableidx →
  ret_val = (with_table v_state v_tableidx nat v_ref) →
  wf_state ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.1-98.89 -/
def with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with
    TABLES := List.modify (s.TABLES) ((f.MODULE.TABLES)[proj_uN_0 v_tableidx]!) (fun elem_1 => v_tableinst)
  }) f

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:98.6-98.21 -/
theorem with_tableinst_is_wf (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) (ret_val : state) :
  wf_state v_state →
  wf_uN 32 v_tableidx →
  wf_tableinst v_tableinst →
  ret_val = (with_tableinst v_state v_tableidx v_tableinst) →
  wf_state ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.1-99.100 -/
def with_mem (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : List byte) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with
    MEMS := List.modify (s.MEMS) ((f.MODULE.MEMS)[proj_uN_0 v_memidx]!) (fun elem_1 => {
      elem_1 with
      BYTES := ((elem_1.BYTES.take nat) ++ var_0_lst) ++ (elem_1.BYTES.drop (nat + nat_0))
    })
  }) f

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:99.6-99.15 -/
theorem with_mem_is_wf (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : List byte) (ret_val : state) :
  wf_state v_state →
  wf_uN 32 v_memidx →
  Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst →
  ret_val = (with_mem v_state v_memidx nat nat_0 var_0_lst) →
  wf_state ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.1-100.87 -/
def with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with
    MEMS := List.modify (s.MEMS) ((f.MODULE.MEMS)[proj_uN_0 v_memidx]!) (fun elem_1 => v_meminst)
  }) f

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:100.6-100.19 -/
theorem with_meminst_is_wf (v_state : state) (v_memidx : memidx) (v_meminst : meminst) (ret_val : state) :
  wf_state v_state →
  wf_uN 32 v_memidx →
  wf_meminst v_meminst →
  ret_val = (with_meminst v_state v_memidx v_meminst) →
  wf_state ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.1-101.93 -/
def with_elem (v_state : state) (v_elemidx : elemidx) (var_0_lst : List ref) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with
    ELEMS := List.modify (s.ELEMS) ((f.MODULE.ELEMS)[proj_uN_0 v_elemidx]!) (fun elem_1 => {
      elem_1 with
      REFS := var_0_lst
    })
  }) f

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:101.6-101.16 -/
theorem with_elem_is_wf (v_state : state) (v_elemidx : elemidx) (var_0_lst : List ref) (ret_val : state) :
  wf_state v_state →
  wf_uN 32 v_elemidx →
  ret_val = (with_elem v_state v_elemidx var_0_lst) →
  wf_state ret_val :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.1-102.94 -/
def with_data (v_state : state) (v_dataidx : dataidx) (var_0_lst : List byte) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with
    DATAS := List.modify (s.DATAS) ((f.MODULE.DATAS)[proj_uN_0 v_dataidx]!) (fun elem_1 => {
      elem_1 with
      BYTES := var_0_lst
    })
  }) f

/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:102.6-102.16 -/
theorem with_data_is_wf (v_state : state) (v_dataidx : dataidx) (var_0_lst : List byte) (ret_val : state) :
  wf_state v_state →
  wf_uN 32 v_dataidx →
  Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst →
  ret_val = (with_data v_state v_dataidx var_0_lst) →
  wf_state ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 -/
inductive fun_growtable_before_fun_growtable_case_1 : tableinst → Nat → ref → Prop where
  | fun_growtable_case_0 (ti : tableinst) (v_n : Nat) (r : ref) (ti' : tableinst) (i : u32) (j_opt : Option u32) (rt : reftype) (r'_lst : List ref) (i' : Nat) :
    ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits i j_opt) rt
      REFS := r'_lst : tableinst
    }) = ti →
    i' = ((List.length r'_lst) + v_n) →
    Forall (fun (j_2_elem : u32) => i' ≤ (proj_uN_0 j_2_elem)) (Option.toList j_opt) →
    ti' = ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN i') j_opt) rt
      REFS := r'_lst ++ (List.replicate v_n r) : tableinst
    }) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits i j_opt) rt
      REFS := r'_lst : tableinst
    }) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN i') j_opt) rt
      REFS := r'_lst ++ (List.replicate v_n r) : tableinst
    }) →
    fun_growtable_before_fun_growtable_case_1 ti v_n r


/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 -/
inductive fun_growtable : tableinst → Nat → ref → Option tableinst → Prop where
  | fun_growtable_case_0 (ti : tableinst) (v_n : Nat) (r : ref) (ti' : tableinst) (i : u32) (j_opt : Option u32) (rt : reftype) (r'_lst : List ref) (i' : Nat) :
    ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits i j_opt) rt
      REFS := r'_lst : tableinst
    }) = ti →
    i' = ((List.length r'_lst) + v_n) →
    Forall (fun (j_2_elem : u32) => i' ≤ (proj_uN_0 j_2_elem)) (Option.toList j_opt) →
    ti' = ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN i') j_opt) rt
      REFS := r'_lst ++ (List.replicate v_n r) : tableinst
    }) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits i j_opt) rt
      REFS := r'_lst : tableinst
    }) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN i') j_opt) rt
      REFS := r'_lst ++ (List.replicate v_n r) : tableinst
    }) →
    fun_growtable ti v_n r (some ti')
  | fun_growtable_case_1 (x0 : tableinst) (x1 : Nat) (x2 : ref) :
    ¬ fun_growtable_before_fun_growtable_case_1 x0 x1 x2 →
    fun_growtable x0 x1 x2 none


/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:116.6-116.16 -/
theorem growtable_is_wf (v_tableinst : tableinst) (nat : Nat) (v_ref : ref) (ret_val : tableinst) (var_0 : Option tableinst) :
  fun_growtable v_tableinst nat v_ref var_0 →
  wf_tableinst v_tableinst →
  var_0 ≠ none →
  ret_val = (Option.get! var_0) →
  wf_tableinst ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 -/
inductive fun_growmemory_before_fun_growmemory_case_1 : meminst → Nat → Prop where
  | fun_growmemory_case_0 (mi : meminst) (v_n : Nat) (mi' : meminst) (i : u32) (j_opt : Option u32) (b_lst : List byte) (i' : Rat) :
    ({
      TYPE := memtype.PAGE (limits.mk_limits i j_opt)
      BYTES := b_lst : meminst
    }) = mi →
    i' = ((((List.length b_lst) : Rat) / ((64 * Ki) : Rat)) + (v_n : Rat)) →
    Forall (fun (j_7_elem : u32) => i' ≤ ((proj_uN_0 j_7_elem) : Rat)) (Option.toList j_opt) →
    mi' = ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN (rat_to_nat i')) j_opt)
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    wf_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits i j_opt)
      BYTES := b_lst : meminst
    }) →
    wf_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN (rat_to_nat i')) j_opt)
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    fun_growmemory_before_fun_growmemory_case_1 mi v_n


/- Inductive Relations Definition at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 -/
inductive fun_growmemory : meminst → Nat → Option meminst → Prop where
  | fun_growmemory_case_0 (mi : meminst) (v_n : Nat) (mi' : meminst) (i : u32) (j_opt : Option u32) (b_lst : List byte) (i' : Rat) :
    ({
      TYPE := memtype.PAGE (limits.mk_limits i j_opt)
      BYTES := b_lst : meminst
    }) = mi →
    i' = ((((List.length b_lst) : Rat) / ((64 * Ki) : Rat)) + (v_n : Rat)) →
    Forall (fun (j_7_elem : u32) => i' ≤ ((proj_uN_0 j_7_elem) : Rat)) (Option.toList j_opt) →
    mi' = ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN (rat_to_nat i')) j_opt)
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    wf_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits i j_opt)
      BYTES := b_lst : meminst
    }) →
    wf_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN (rat_to_nat i')) j_opt)
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    fun_growmemory mi v_n (some mi')
  | fun_growmemory_case_1 (x0 : meminst) (x1 : Nat) :
    ¬ fun_growmemory_before_fun_growmemory_case_1 x0 x1 →
    fun_growmemory x0 x1 none


/- Well-Formedness Theorem at: ../specification/wasm-2.0/5-runtime-aux.spectec:117.6-117.17 -/
theorem growmemory_is_wf (v_meminst : meminst) (nat : Nat) (ret_val : meminst) (var_0 : Option meminst) :
  fun_growmemory v_meminst nat var_0 →
  wf_meminst v_meminst →
  var_0 ≠ none →
  ret_val = (Option.get! var_0) →
  wf_meminst ret_val :=
  sorry

/- Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 -/
structure context where
  MKcontext ::
  TYPES : List functype
  FUNCS : List functype
  GLOBALS : List globaltype
  TABLES : List tabletype
  MEMS : List memtype
  ELEMS : List elemtype
  DATAS : List datatype
  LOCALS : List valtype
  LABELS : List resulttype
  RETURN : Option resulttype
deriving Inhabited, BEq

/- Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 -/
def append_context (arg1 arg2 : context) : context where
  TYPES := (arg1.TYPES) ++ (arg2.TYPES)
  FUNCS := (arg1.FUNCS) ++ (arg2.FUNCS)
  GLOBALS := (arg1.GLOBALS) ++ (arg2.GLOBALS)
  TABLES := (arg1.TABLES) ++ (arg2.TABLES)
  MEMS := (arg1.MEMS) ++ (arg2.MEMS)
  ELEMS := (arg1.ELEMS) ++ (arg2.ELEMS)
  DATAS := (arg1.DATAS) ++ (arg2.DATAS)
  LOCALS := (arg1.LOCALS) ++ (arg2.LOCALS)
  LABELS := (arg1.LABELS) ++ (arg2.LABELS)
  RETURN := Option.orElse (arg1.RETURN) (fun _ => arg2.RETURN)

/- Record Creation Definition at: ../specification/wasm-2.0/6-typing.spectec:5.1-9.62 -/
instance  : Append context where
  append := append_context

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:5.8-5.15 -/
inductive wf_context : context → Prop where
  | context_case_ (var_0_lst : List functype) (var_1_lst : List functype) (var_2_lst : List globaltype) (var_3_lst : List tabletype) (var_4_lst : List memtype) (var_5_lst : List elemtype) (var_6_lst : List datatype) (var_7_lst : List valtype) (var_8_lst : List resulttype) (var_9_opt : Option resulttype) :
    Forall (fun (var_3_elem : tabletype) => wf_tabletype var_3_elem) var_3_lst →
    Forall (fun (var_4_elem : memtype) => wf_memtype var_4_elem) var_4_lst →
    wf_context ({
      TYPES := var_0_lst
      FUNCS := var_1_lst
      GLOBALS := var_2_lst
      TABLES := var_3_lst
      MEMS := var_4_lst
      ELEMS := var_5_lst
      DATAS := var_6_lst
      LOCALS := var_7_lst
      LABELS := var_8_lst
      RETURN := var_9_opt : context
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:19.1-19.66 -/
inductive Limits_ok : limits → Nat → Prop where
  | mk_Limits_ok (v_n : n) (m_opt : Option m) (k : Nat) :
    v_n ≤ k →
    Forall (fun (v_m_elem : Nat) => (v_n ≤ v_m_elem) ∧ (v_m_elem ≤ k)) (Option.toList m_opt) →
    wf_limits (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) →
    Limits_ok (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) k


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:20.1-20.64 -/
inductive Functype_ok : functype → Prop where
  | mk_Functype_ok (t_1_lst : List valtype) (t_2_lst : List valtype) : Functype_ok (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:21.1-21.66 -/
inductive Globaltype_ok : globaltype → Prop where
  | mk_Globaltype_ok (t : valtype) : Globaltype_ok (globaltype.mk_globaltype (some r_MUT.MUT) t)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:22.1-22.65 -/
inductive Tabletype_ok : tabletype → Prop where
  | mk_Tabletype_ok (v_limits : limits) (v_reftype : reftype) :
    Limits_ok v_limits (Int.toNat (((2 ^ 32) : Int) - (1 : Int))) →
    wf_tabletype (tabletype.mk_tabletype v_limits v_reftype) →
    Tabletype_ok (tabletype.mk_tabletype v_limits v_reftype)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:23.1-23.63 -/
inductive Memtype_ok : memtype → Prop where
  | mk_Memtype_ok (v_limits : limits) :
    Limits_ok v_limits (2 ^ 16) →
    wf_memtype (memtype.PAGE v_limits) →
    Memtype_ok (memtype.PAGE v_limits)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:24.1-24.66 -/
inductive Externtype_ok : externtype → Prop where
  | func (v_functype : functype) :
    Functype_ok v_functype →
    wf_externtype (externtype.FUNC v_functype) →
    Externtype_ok (externtype.FUNC v_functype)
  | global (v_globaltype : globaltype) :
    Globaltype_ok v_globaltype →
    wf_externtype (externtype.GLOBAL v_globaltype) →
    Externtype_ok (externtype.GLOBAL v_globaltype)
  | table (v_tabletype : tabletype) :
    Tabletype_ok v_tabletype →
    wf_externtype (externtype.TABLE v_tabletype) →
    Externtype_ok (externtype.TABLE v_tabletype)
  | mem (v_memtype : memtype) :
    Memtype_ok v_memtype →
    wf_externtype (externtype.MEM v_memtype) →
    Externtype_ok (externtype.MEM v_memtype)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:71.1-71.69 -/
inductive Valtype_sub : valtype → valtype → Prop where
  | refl (t : valtype) : Valtype_sub t t
  | bot (t : valtype) : Valtype_sub valtype.BOT t


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:72.1-72.76 -/
inductive Resulttype_sub : resulttype → resulttype → Prop where
  | mk_Resulttype_sub (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (List.length t_1_lst) = (List.length t_2_lst) →
    Forall₂ (fun (t_1_elem : valtype) (t_2_elem : valtype) => Valtype_sub t_1_elem t_2_elem) t_1_lst t_2_lst →
    Resulttype_sub (.mk_list t_1_lst) (.mk_list t_2_lst)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:87.1-87.75 -/
inductive Limits_sub : limits → limits → Prop where
  | max (n_1 : n) (m_1 : m) (n_2 : n) (m_2_opt : Option m) :
    n_1 ≥ n_2 →
    Forall (fun (m_2_elem : Nat) => m_1 ≤ m_2_elem) (Option.toList m_2_opt) →
    wf_limits (limits.mk_limits (uN.mk_uN n_1) (some (uN.mk_uN m_1))) →
    wf_limits (limits.mk_limits (uN.mk_uN n_2) (OMap (fun (m_2_elem : m) => uN.mk_uN m_2_elem) m_2_opt)) →
    Limits_sub (limits.mk_limits (uN.mk_uN n_1) (some (uN.mk_uN m_1))) (limits.mk_limits (uN.mk_uN n_2) (OMap (fun (m_2_elem : m) => uN.mk_uN m_2_elem) m_2_opt))
  | eps (n_1 : n) (n_2 : n) :
    n_1 ≥ n_2 →
    wf_limits (limits.mk_limits (uN.mk_uN n_1) none) →
    wf_limits (limits.mk_limits (uN.mk_uN n_2) none) →
    Limits_sub (limits.mk_limits (uN.mk_uN n_1) none) (limits.mk_limits (uN.mk_uN n_2) none)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:88.1-88.73 -/
inductive Functype_sub : functype → functype → Prop where
  | mk_Functype_sub (ft : functype) : Functype_sub ft ft


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:89.1-89.75 -/
inductive Globaltype_sub : globaltype → globaltype → Prop where
  | mk_Globaltype_sub (gt : globaltype) : Globaltype_sub gt gt


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:90.1-90.74 -/
inductive Tabletype_sub : tabletype → tabletype → Prop where
  | mk_Tabletype_sub (lim_1 : limits) (rt : reftype) (lim_2 : limits) :
    Limits_sub lim_1 lim_2 →
    wf_tabletype (tabletype.mk_tabletype lim_1 rt) →
    wf_tabletype (tabletype.mk_tabletype lim_2 rt) →
    Tabletype_sub (tabletype.mk_tabletype lim_1 rt) (tabletype.mk_tabletype lim_2 rt)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:91.1-91.72 -/
inductive Memtype_sub : memtype → memtype → Prop where
  | mk_Memtype_sub (lim_1 : limits) (lim_2 : limits) :
    Limits_sub lim_1 lim_2 →
    wf_memtype (memtype.PAGE lim_1) →
    wf_memtype (memtype.PAGE lim_2) →
    Memtype_sub (memtype.PAGE lim_1) (memtype.PAGE lim_2)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:92.1-92.75 -/
inductive Externtype_sub : externtype → externtype → Prop where
  | func (ft_1 : functype) (ft_2 : functype) :
    Functype_sub ft_1 ft_2 →
    wf_externtype (externtype.FUNC ft_1) →
    wf_externtype (externtype.FUNC ft_2) →
    Externtype_sub (externtype.FUNC ft_1) (externtype.FUNC ft_2)
  | global (gt_1 : globaltype) (gt_2 : globaltype) :
    Globaltype_sub gt_1 gt_2 →
    wf_externtype (externtype.GLOBAL gt_1) →
    wf_externtype (externtype.GLOBAL gt_2) →
    Externtype_sub (externtype.GLOBAL gt_1) (externtype.GLOBAL gt_2)
  | table (tt_1 : tabletype) (tt_2 : tabletype) :
    Tabletype_sub tt_1 tt_2 →
    wf_externtype (externtype.TABLE tt_1) →
    wf_externtype (externtype.TABLE tt_2) →
    Externtype_sub (externtype.TABLE tt_1) (externtype.TABLE tt_2)
  | mem (mt_1 : memtype) (mt_2 : memtype) :
    Memtype_sub mt_1 mt_2 →
    wf_externtype (externtype.MEM mt_1) →
    wf_externtype (externtype.MEM mt_2) →
    Externtype_sub (externtype.MEM mt_1) (externtype.MEM mt_2)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:202.1-202.76 -/
inductive Blocktype_ok : context → blocktype → functype → Prop where
  | valtype (C : context) (valtype_opt : Option valtype) :
    wf_context C →
    wf_blocktype (blocktype._RESULT valtype_opt) →
    Blocktype_ok C (blocktype._RESULT valtype_opt) (functype.mk_functype (.mk_list []) (.mk_list (Option.toList valtype_opt)))
  | typeidx (C : context) (v_typeidx : typeidx) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (proj_uN_0 v_typeidx) < (List.length (C.TYPES)) →
    ((C.TYPES)[proj_uN_0 v_typeidx]!) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_blocktype (blocktype._IDX v_typeidx) →
    Blocktype_ok C (blocktype._IDX v_typeidx) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))


mutual
/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:141.1-141.64 -/
inductive Instr_ok : context → instr → functype → Prop where
  | nop (C : context) :
    wf_context C →
    wf_instr instr.NOP →
    Instr_ok C instr.NOP (functype.mk_functype (.mk_list []) (.mk_list []))
  | unreachable (C : context) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    wf_context C →
    wf_instr instr.UNREACHABLE →
    Instr_ok C instr.UNREACHABLE (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | drop (C : context) (t : valtype) :
    wf_context C →
    wf_instr instr.DROP →
    Instr_ok C instr.DROP (functype.mk_functype (.mk_list [t]) (.mk_list []))
  | select_expl (C : context) (t : valtype) :
    wf_context C →
    wf_instr (instr.SELECT (some [t])) →
    Instr_ok C (instr.SELECT (some [t])) (functype.mk_functype (.mk_list [t, t, valtype.I32]) (.mk_list [t]))
  | select_impl (C : context) (t : valtype) (t' : valtype) (v_numtype : numtype) (v_vectype : vectype) :
    Valtype_sub t t' →
    (t' = (valtype_numtype v_numtype)) ∨ (t' = (valtype_vectype v_vectype)) →
    wf_context C →
    wf_instr (instr.SELECT none) →
    Instr_ok C (instr.SELECT none) (functype.mk_functype (.mk_list [t, t, valtype.I32]) (.mk_list [t]))
  | block (C : context) (bt : blocktype) (instr_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Blocktype_ok C bt (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none : context
    }) ++ C) instr_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.BLOCK bt instr_lst) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none : context
    }) →
    Instr_ok C (instr.BLOCK bt instr_lst) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | loop (C : context) (bt : blocktype) (instr_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Blocktype_ok C bt (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t_1_lst]
      RETURN := none : context
    }) ++ C) instr_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.LOOP bt instr_lst) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t_1_lst]
      RETURN := none : context
    }) →
    Instr_ok C (instr.LOOP bt instr_lst) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | if (C : context) (bt : blocktype) (instr_1_lst : List instr) (instr_2_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Blocktype_ok C bt (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none : context
    }) ++ C) instr_1_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none : context
    }) ++ C) instr_2_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.IFELSE bt instr_1_lst instr_2_lst) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none : context
    }) →
    Instr_ok C (instr.IFELSE bt instr_1_lst instr_2_lst) (functype.mk_functype (.mk_list (t_1_lst ++ [valtype.I32])) (.mk_list t_2_lst))
  | br (C : context) (l : labelidx) (t_1_lst : List valtype) (t_lst : List valtype) (t_2_lst : List valtype) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    (proj_list_0 valtype ((C.LABELS)[proj_uN_0 l]!)) = t_lst →
    wf_context C →
    wf_instr (instr.BR l) →
    Instr_ok C (instr.BR l) (functype.mk_functype (.mk_list (t_1_lst ++ t_lst)) (.mk_list t_2_lst))
  | br_if (C : context) (l : labelidx) (t_lst : List valtype) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    (proj_list_0 valtype ((C.LABELS)[proj_uN_0 l]!)) = t_lst →
    wf_context C →
    wf_instr (instr.BR_IF l) →
    Instr_ok C (instr.BR_IF l) (functype.mk_functype (.mk_list (t_lst ++ [valtype.I32])) (.mk_list t_lst))
  | br_table (C : context) (l_lst : List labelidx) (l' : labelidx) (t_1_lst : List valtype) (t_lst : List valtype) (t_2_lst : List valtype) :
    Forall (fun (l_elem : labelidx) => (proj_uN_0 l_elem) < (List.length (C.LABELS))) l_lst →
    Forall (fun (l_elem : labelidx) => Resulttype_sub (.mk_list t_lst) ((C.LABELS)[proj_uN_0 l_elem]!)) l_lst →
    (proj_uN_0 l') < (List.length (C.LABELS)) →
    Resulttype_sub (.mk_list t_lst) ((C.LABELS)[proj_uN_0 l']!) →
    wf_context C →
    wf_instr (instr.BR_TABLE l_lst l') →
    Instr_ok C (instr.BR_TABLE l_lst l') (functype.mk_functype (.mk_list (t_1_lst ++ (t_lst ++ [valtype.I32]))) (.mk_list t_2_lst))
  | call (C : context) (x : idx) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.CALL x) →
    Instr_ok C (instr.CALL x) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | call_indirect (C : context) (x : idx) (y : idx) (t_1_lst : List valtype) (t_2_lst : List valtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype lim reftype.FUNCREF) →
    (proj_uN_0 y) < (List.length (C.TYPES)) →
    ((C.TYPES)[proj_uN_0 y]!) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.CALL_INDIRECT x y) →
    wf_tabletype (tabletype.mk_tabletype lim reftype.FUNCREF) →
    Instr_ok C (instr.CALL_INDIRECT x y) (functype.mk_functype (.mk_list (t_1_lst ++ [valtype.I32])) (.mk_list t_2_lst))
  | return (C : context) (t_1_lst : List valtype) (t_lst : List valtype) (t_2_lst : List valtype) :
    (C.RETURN) = (some (.mk_list t_lst)) →
    wf_context C →
    wf_instr instr.RETURN →
    Instr_ok C instr.RETURN (functype.mk_functype (.mk_list (t_1_lst ++ t_lst)) (.mk_list t_2_lst))
  | const (C : context) (nt : numtype) (c_nt : num_) :
    wf_context C →
    wf_instr (instr.CONST nt c_nt) →
    Instr_ok C (instr.CONST nt c_nt) (functype.mk_functype (.mk_list []) (.mk_list [valtype_numtype nt]))
  | unop (C : context) (nt : numtype) (unop_nt : unop_) :
    wf_context C →
    wf_instr (instr.UNOP nt unop_nt) →
    Instr_ok C (instr.UNOP nt unop_nt) (functype.mk_functype (.mk_list [valtype_numtype nt]) (.mk_list [valtype_numtype nt]))
  | binop (C : context) (nt : numtype) (binop_nt : binop_) :
    wf_context C →
    wf_instr (instr.BINOP nt binop_nt) →
    Instr_ok C (instr.BINOP nt binop_nt) (functype.mk_functype (.mk_list [valtype_numtype nt, valtype_numtype nt]) (.mk_list [valtype_numtype nt]))
  | testop (C : context) (nt : numtype) (testop_nt : testop_) :
    wf_context C →
    wf_instr (instr.TESTOP nt testop_nt) →
    Instr_ok C (instr.TESTOP nt testop_nt) (functype.mk_functype (.mk_list [valtype_numtype nt]) (.mk_list [valtype.I32]))
  | relop (C : context) (nt : numtype) (relop_nt : relop_) :
    wf_context C →
    wf_instr (instr.RELOP nt relop_nt) →
    Instr_ok C (instr.RELOP nt relop_nt) (functype.mk_functype (.mk_list [valtype_numtype nt, valtype_numtype nt]) (.mk_list [valtype.I32]))
  | cvtop (C : context) (nt_1 : numtype) (nt_2 : numtype) (cvtop : cvtop__) :
    wf_context C →
    wf_instr (instr.CVTOP nt_1 nt_2 cvtop) →
    Instr_ok C (instr.CVTOP nt_1 nt_2 cvtop) (functype.mk_functype (.mk_list [valtype_numtype nt_2]) (.mk_list [valtype_numtype nt_1]))
  | ref_null (C : context) (rt : reftype) :
    wf_context C →
    wf_instr (instr.REF_NULL rt) →
    Instr_ok C (instr.REF_NULL rt) (functype.mk_functype (.mk_list []) (.mk_list [valtype_reftype rt]))
  | ref_func (C : context) (x : idx) (ft : functype) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) = ft →
    wf_context C →
    wf_instr (instr.REF_FUNC x) →
    Instr_ok C (instr.REF_FUNC x) (functype.mk_functype (.mk_list []) (.mk_list [valtype.FUNCREF]))
  | ref_is_null (C : context) (rt : reftype) :
    wf_context C →
    wf_instr instr.REF_IS_NULL →
    Instr_ok C instr.REF_IS_NULL (functype.mk_functype (.mk_list [valtype_reftype rt]) (.mk_list [valtype.I32]))
  | vconst (C : context) (c : vec_) :
    wf_context C →
    wf_instr (instr.VCONST vectype.V128 c) →
    Instr_ok C (instr.VCONST vectype.V128 c) (functype.mk_functype (.mk_list []) (.mk_list [valtype.V128]))
  | vvunop (C : context) (v_vvunop : vvunop) :
    wf_context C →
    wf_instr (instr.VVUNOP vectype.V128 v_vvunop) →
    Instr_ok C (instr.VVUNOP vectype.V128 v_vvunop) (functype.mk_functype (.mk_list [valtype.V128]) (.mk_list [valtype.V128]))
  | vvbinop (C : context) (v_vvbinop : vvbinop) :
    wf_context C →
    wf_instr (instr.VVBINOP vectype.V128 v_vvbinop) →
    Instr_ok C (instr.VVBINOP vectype.V128 v_vvbinop) (functype.mk_functype (.mk_list [valtype.V128, valtype.V128]) (.mk_list [valtype.V128]))
  | vvternop (C : context) (v_vvternop : vvternop) :
    wf_context C →
    wf_instr (instr.VVTERNOP vectype.V128 v_vvternop) →
    Instr_ok C (instr.VVTERNOP vectype.V128 v_vvternop) (functype.mk_functype (.mk_list [valtype.V128, valtype.V128, valtype.V128]) (.mk_list [valtype.V128]))
  | vvtestop (C : context) (v_vvtestop : vvtestop) :
    wf_context C →
    wf_instr (instr.VVTESTOP vectype.V128 v_vvtestop) →
    Instr_ok C (instr.VVTESTOP vectype.V128 v_vvtestop) (functype.mk_functype (.mk_list [valtype.V128]) (.mk_list [valtype.I32]))
  | vunop (C : context) (sh : shape) (vunop_sh : vunop_) :
    wf_context C →
    wf_instr (instr.VUNOP sh vunop_sh) →
    Instr_ok C (instr.VUNOP sh vunop_sh) (functype.mk_functype (.mk_list [valtype.V128]) (.mk_list [valtype.V128]))
  | vbinop (C : context) (sh : shape) (vbinop_sh : vbinop_) :
    wf_context C →
    wf_instr (instr.VBINOP sh vbinop_sh) →
    Instr_ok C (instr.VBINOP sh vbinop_sh) (functype.mk_functype (.mk_list [valtype.V128, valtype.V128]) (.mk_list [valtype.V128]))
  | vtestop (C : context) (sh : shape) (vtestop_sh : vtestop_) :
    wf_context C →
    wf_instr (instr.VTESTOP sh vtestop_sh) →
    Instr_ok C (instr.VTESTOP sh vtestop_sh) (functype.mk_functype (.mk_list [valtype.V128]) (.mk_list [valtype.I32]))
  | vrelop (C : context) (sh : shape) (vrelop_sh : vrelop_) :
    wf_context C →
    wf_instr (instr.VRELOP sh vrelop_sh) →
    Instr_ok C (instr.VRELOP sh vrelop_sh) (functype.mk_functype (.mk_list [valtype.V128, valtype.V128]) (.mk_list [valtype.V128]))
  | vshiftop (C : context) (sh : ishape) (vshiftop_sh : vshiftop_) :
    wf_context C →
    wf_instr (instr.VSHIFTOP sh vshiftop_sh) →
    Instr_ok C (instr.VSHIFTOP sh vshiftop_sh) (functype.mk_functype (.mk_list [valtype.V128, valtype.I32]) (.mk_list [valtype.V128]))
  | vbitmask (C : context) (sh : ishape) :
    wf_context C →
    wf_instr (instr.VBITMASK sh) →
    Instr_ok C (instr.VBITMASK sh) (functype.mk_functype (.mk_list [valtype.V128]) (.mk_list [valtype.I32]))
  | vswizzle (C : context) (sh : ishape) :
    wf_context C →
    wf_instr (instr.VSWIZZLE sh) →
    Instr_ok C (instr.VSWIZZLE sh) (functype.mk_functype (.mk_list [valtype.V128, valtype.V128]) (.mk_list [valtype.V128]))
  | vshuffle (C : context) (sh : ishape) (i_lst : List laneidx) :
    Forall (fun (i_elem : laneidx) => (proj_uN_0 i_elem) < (2 * (proj_dim_0 (fun_dim (shape_ishape sh))))) i_lst →
    wf_context C →
    wf_dim (fun_dim (shape_ishape sh)) →
    wf_instr (instr.VSHUFFLE sh i_lst) →
    Instr_ok C (instr.VSHUFFLE sh i_lst) (functype.mk_functype (.mk_list [valtype.V128, valtype.V128]) (.mk_list [valtype.V128]))
  | vsplat (C : context) (sh : shape) :
    wf_context C →
    wf_instr (instr.VSPLAT sh) →
    Instr_ok C (instr.VSPLAT sh) (functype.mk_functype (.mk_list [valtype_numtype (shunpack sh)]) (.mk_list [valtype.V128]))
  | vextract_lane (C : context) (sh : shape) (sx_opt : Option sx) (i : laneidx) :
    (proj_uN_0 i) < (proj_dim_0 (fun_dim sh)) →
    wf_context C →
    wf_dim (fun_dim sh) →
    wf_instr (instr.VEXTRACT_LANE sh sx_opt i) →
    Instr_ok C (instr.VEXTRACT_LANE sh sx_opt i) (functype.mk_functype (.mk_list [valtype.V128]) (.mk_list [valtype_numtype (shunpack sh)]))
  | vreplace_lane (C : context) (sh : shape) (i : laneidx) :
    (proj_uN_0 i) < (proj_dim_0 (fun_dim sh)) →
    wf_context C →
    wf_dim (fun_dim sh) →
    wf_instr (instr.VREPLACE_LANE sh i) →
    Instr_ok C (instr.VREPLACE_LANE sh i) (functype.mk_functype (.mk_list [valtype.V128, valtype_numtype (shunpack sh)]) (.mk_list [valtype.V128]))
  | vextunop (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop_) :
    wf_context C →
    wf_instr (instr.VEXTUNOP sh_1 sh_2 vextunop) →
    Instr_ok C (instr.VEXTUNOP sh_1 sh_2 vextunop) (functype.mk_functype (.mk_list [valtype.V128]) (.mk_list [valtype.V128]))
  | vextbinop (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop_) :
    wf_context C →
    wf_instr (instr.VEXTBINOP sh_1 sh_2 vextbinop) →
    Instr_ok C (instr.VEXTBINOP sh_1 sh_2 vextbinop) (functype.mk_functype (.mk_list [valtype.V128, valtype.V128]) (.mk_list [valtype.V128]))
  | vnarrow (C : context) (sh_1 : ishape) (sh_2 : ishape) (v_sx : sx) :
    wf_context C →
    wf_instr (instr.VNARROW sh_1 sh_2 v_sx) →
    Instr_ok C (instr.VNARROW sh_1 sh_2 v_sx) (functype.mk_functype (.mk_list [valtype.V128, valtype.V128]) (.mk_list [valtype.V128]))
  | vcvtop (C : context) (sh_1 : shape) (sh_2 : shape) (v_vcvtop : vcvtop) :
    wf_context C →
    wf_instr (instr.VCVTOP sh_1 sh_2 v_vcvtop) →
    Instr_ok C (instr.VCVTOP sh_1 sh_2 v_vcvtop) (functype.mk_functype (.mk_list [valtype.V128]) (.mk_list [valtype.V128]))
  | local_get (C : context) (x : idx) (t : valtype) :
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) = t →
    wf_context C →
    wf_instr (instr.LOCAL_GET x) →
    Instr_ok C (instr.LOCAL_GET x) (functype.mk_functype (.mk_list []) (.mk_list [t]))
  | local_set (C : context) (x : idx) (t : valtype) :
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) = t →
    wf_context C →
    wf_instr (instr.LOCAL_SET x) →
    Instr_ok C (instr.LOCAL_SET x) (functype.mk_functype (.mk_list [t]) (.mk_list []))
  | local_tee (C : context) (x : idx) (t : valtype) :
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) = t →
    wf_context C →
    wf_instr (instr.LOCAL_TEE x) →
    Instr_ok C (instr.LOCAL_TEE x) (functype.mk_functype (.mk_list [t]) (.mk_list [t]))
  | global_get (C : context) (x : idx) (t : valtype) (v_mut : «mut») :
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) = (globaltype.mk_globaltype v_mut t) →
    wf_context C →
    wf_instr (instr.GLOBAL_GET x) →
    Instr_ok C (instr.GLOBAL_GET x) (functype.mk_functype (.mk_list []) (.mk_list [t]))
  | global_set (C : context) (x : idx) (t : valtype) :
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) = (globaltype.mk_globaltype (some r_MUT.MUT) t) →
    wf_context C →
    wf_instr (instr.GLOBAL_SET x) →
    Instr_ok C (instr.GLOBAL_SET x) (functype.mk_functype (.mk_list [t]) (.mk_list []))
  | table_get (C : context) (x : idx) (rt : reftype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_GET x) →
    wf_tabletype (tabletype.mk_tabletype lim rt) →
    Instr_ok C (instr.TABLE_GET x) (functype.mk_functype (.mk_list [valtype.I32]) (.mk_list [valtype_reftype rt]))
  | table_set (C : context) (x : idx) (rt : reftype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_SET x) →
    wf_tabletype (tabletype.mk_tabletype lim rt) →
    Instr_ok C (instr.TABLE_SET x) (functype.mk_functype (.mk_list [valtype.I32, valtype_reftype rt]) (.mk_list []))
  | table_size (C : context) (x : idx) (lim : limits) (rt : reftype) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_SIZE x) →
    wf_tabletype (tabletype.mk_tabletype lim rt) →
    Instr_ok C (instr.TABLE_SIZE x) (functype.mk_functype (.mk_list []) (.mk_list [valtype.I32]))
  | table_grow (C : context) (x : idx) (rt : reftype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_GROW x) →
    wf_tabletype (tabletype.mk_tabletype lim rt) →
    Instr_ok C (instr.TABLE_GROW x) (functype.mk_functype (.mk_list [valtype_reftype rt, valtype.I32]) (.mk_list [valtype.I32]))
  | table_fill (C : context) (x : idx) (rt : reftype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_FILL x) →
    wf_tabletype (tabletype.mk_tabletype lim rt) →
    Instr_ok C (instr.TABLE_FILL x) (functype.mk_functype (.mk_list [valtype.I32, valtype_reftype rt, valtype.I32]) (.mk_list []))
  | table_copy (C : context) (x_1 : idx) (x_2 : idx) (lim_1 : limits) (rt : reftype) (lim_2 : limits) :
    (proj_uN_0 x_1) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x_1]!) = (tabletype.mk_tabletype lim_1 rt) →
    (proj_uN_0 x_2) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x_2]!) = (tabletype.mk_tabletype lim_2 rt) →
    wf_context C →
    wf_instr (instr.TABLE_COPY x_1 x_2) →
    wf_tabletype (tabletype.mk_tabletype lim_1 rt) →
    wf_tabletype (tabletype.mk_tabletype lim_2 rt) →
    Instr_ok C (instr.TABLE_COPY x_1 x_2) (functype.mk_functype (.mk_list [valtype.I32, valtype.I32, valtype.I32]) (.mk_list []))
  | table_init (C : context) (x_1 : idx) (x_2 : idx) (lim : limits) (rt : reftype) :
    (proj_uN_0 x_1) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x_1]!) = (tabletype.mk_tabletype lim rt) →
    (proj_uN_0 x_2) < (List.length (C.ELEMS)) →
    ((C.ELEMS)[proj_uN_0 x_2]!) = rt →
    wf_context C →
    wf_instr (instr.TABLE_INIT x_1 x_2) →
    wf_tabletype (tabletype.mk_tabletype lim rt) →
    Instr_ok C (instr.TABLE_INIT x_1 x_2) (functype.mk_functype (.mk_list [valtype.I32, valtype.I32, valtype.I32]) (.mk_list []))
  | elem_drop (C : context) (x : idx) (rt : reftype) :
    (proj_uN_0 x) < (List.length (C.ELEMS)) →
    ((C.ELEMS)[proj_uN_0 x]!) = rt →
    wf_context C →
    wf_instr (instr.ELEM_DROP x) →
    Instr_ok C (instr.ELEM_DROP x) (functype.mk_functype (.mk_list []) (.mk_list []))
  | memory_size (C : context) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    wf_context C →
    wf_memtype mt →
    wf_instr instr.MEMORY_SIZE →
    Instr_ok C instr.MEMORY_SIZE (functype.mk_functype (.mk_list []) (.mk_list [valtype.I32]))
  | memory_grow (C : context) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    wf_context C →
    wf_memtype mt →
    wf_instr instr.MEMORY_GROW →
    Instr_ok C instr.MEMORY_GROW (functype.mk_functype (.mk_list [valtype.I32]) (.mk_list [valtype.I32]))
  | memory_fill (C : context) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    wf_context C →
    wf_memtype mt →
    wf_instr instr.MEMORY_FILL →
    Instr_ok C instr.MEMORY_FILL (functype.mk_functype (.mk_list [valtype.I32, valtype.I32, valtype.I32]) (.mk_list []))
  | memory_copy (C : context) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    wf_context C →
    wf_memtype mt →
    wf_instr instr.MEMORY_COPY →
    Instr_ok C instr.MEMORY_COPY (functype.mk_functype (.mk_list [valtype.I32, valtype.I32, valtype.I32]) (.mk_list []))
  | memory_init (C : context) (x : idx) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    (proj_uN_0 x) < (List.length (C.DATAS)) →
    ((C.DATAS)[proj_uN_0 x]!) = datatype.OK →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.MEMORY_INIT x) →
    Instr_ok C (instr.MEMORY_INIT x) (functype.mk_functype (.mk_list [valtype.I32, valtype.I32, valtype.I32]) (.mk_list []))
  | data_drop (C : context) (x : idx) :
    (proj_uN_0 x) < (List.length (C.DATAS)) →
    ((C.DATAS)[proj_uN_0 x]!) = datatype.OK →
    wf_context C →
    wf_instr (instr.DATA_DROP x) →
    Instr_ok C (instr.DATA_DROP x) (functype.mk_functype (.mk_list []) (.mk_list []))
  | load_val (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    (size (valtype_numtype nt)) ≠ none →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.LOAD nt none v_memarg) →
    Instr_ok C (instr.LOAD nt none v_memarg) (functype.mk_functype (.mk_list [valtype.I32]) (.mk_list [valtype_numtype nt]))
  | load_pack (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (v_memarg : memarg) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_M : Rat) / (8 : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.LOAD (numtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_M) v_sx))) v_memarg) →
    Instr_ok C (instr.LOAD (numtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_M) v_sx))) v_memarg) (functype.mk_functype (.mk_list [valtype.I32]) (.mk_list [valtype_Inn v_Inn]))
  | store_val (C : context) (nt : numtype) (v_memarg : memarg) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    (size (valtype_numtype nt)) ≠ none →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.STORE nt none v_memarg) →
    Instr_ok C (instr.STORE nt none v_memarg) (functype.mk_functype (.mk_list [valtype.I32, valtype_numtype nt]) (.mk_list []))
  | store_pack (C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_M : Rat) / (8 : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_M)) v_memarg) →
    Instr_ok C (instr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_M)) v_memarg) (functype.mk_functype (.mk_list [valtype.I32, valtype_Inn v_Inn]) (.mk_list []))
  | vload (C : context) (v_M : M) (v_N : N) (v_sx : sx) (v_memarg : memarg) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((v_M : Rat) / (8 : Rat)) * (v_N : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.VLOAD vectype.V128 (some (vloadop.SHAPEX_ v_M v_N v_sx)) v_memarg) →
    Instr_ok C (instr.VLOAD vectype.V128 (some (vloadop.SHAPEX_ v_M v_N v_sx)) v_memarg) (functype.mk_functype (.mk_list [valtype.I32]) (.mk_list [valtype.V128]))
  | vload_splat (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_n : Rat) / (8 : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.VLOAD vectype.V128 (some (vloadop.SPLAT v_n)) v_memarg) →
    Instr_ok C (instr.VLOAD vectype.V128 (some (vloadop.SPLAT v_n)) v_memarg) (functype.mk_functype (.mk_list [valtype.I32]) (.mk_list [valtype.V128]))
  | vload_zero (C : context) (v_n : n) (v_memarg : memarg) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_n : Rat) / (8 : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.VLOAD vectype.V128 (some (vloadop.ZERO v_n)) v_memarg) →
    Instr_ok C (instr.VLOAD vectype.V128 (some (vloadop.ZERO v_n)) v_memarg) (functype.mk_functype (.mk_list [valtype.I32]) (.mk_list [valtype.V128]))
  | vload_lane (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_n : Rat) / (8 : Rat)) →
    ((proj_uN_0 v_laneidx) : Rat) < ((128 : Rat) / (v_n : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.VLOAD_LANE vectype.V128 (sz.mk_sz v_n) v_memarg v_laneidx) →
    Instr_ok C (instr.VLOAD_LANE vectype.V128 (sz.mk_sz v_n) v_memarg v_laneidx) (functype.mk_functype (.mk_list [valtype.I32, valtype.V128]) (.mk_list [valtype.V128]))
  | vstore (C : context) (v_memarg : memarg) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    (size valtype.V128) ≠ none →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.VSTORE vectype.V128 v_memarg) →
    Instr_ok C (instr.VSTORE vectype.V128 v_memarg) (functype.mk_functype (.mk_list [valtype.I32, valtype.V128]) (.mk_list []))
  | vstore_lane (C : context) (v_n : n) (v_memarg : memarg) (v_laneidx : laneidx) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_n : Rat) / (8 : Rat)) →
    ((proj_uN_0 v_laneidx) : Rat) < ((128 : Rat) / (v_n : Rat)) →
    wf_context C →
    wf_memtype mt →
    wf_instr (instr.VSTORE_LANE vectype.V128 (sz.mk_sz v_n) v_memarg v_laneidx) →
    Instr_ok C (instr.VSTORE_LANE vectype.V128 (sz.mk_sz v_n) v_memarg v_laneidx) (functype.mk_functype (.mk_list [valtype.I32, valtype.V128]) (.mk_list []))

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:142.1-142.65 -/
inductive Instrs_ok : context → List instr → functype → Prop where
  | empty (C : context) :
    wf_context C →
    Instrs_ok C [] (functype.mk_functype (.mk_list []) (.mk_list []))
  | instr (C : context) (v_instr : instr) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instr_ok C v_instr (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr v_instr →
    Instrs_ok C [v_instr] (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | seq (C : context) (instr_1_lst : List instr) (instr_2_lst : List instr) (t_1_lst : List valtype) (t_3_lst : List valtype) (t_2_lst : List valtype) :
    Instrs_ok C instr_1_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instrs_ok C instr_2_lst (functype.mk_functype (.mk_list t_2_lst) (.mk_list t_3_lst)) →
    wf_context C →
    Forall (fun (instr_1_elem : instr) => wf_instr instr_1_elem) instr_1_lst →
    Forall (fun (instr_2_elem : instr) => wf_instr instr_2_elem) instr_2_lst →
    Instrs_ok C (instr_1_lst ++ instr_2_lst) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_3_lst))
  | sub (C : context) (instr_lst : List instr) (t'_1_lst : List valtype) (t'_2_lst : List valtype) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instrs_ok C instr_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Resulttype_sub (.mk_list t'_1_lst) (.mk_list t_1_lst) →
    Resulttype_sub (.mk_list t_2_lst) (.mk_list t'_2_lst) →
    wf_context C →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    Instrs_ok C instr_lst (functype.mk_functype (.mk_list t'_1_lst) (.mk_list t'_2_lst))
  | frame (C : context) (instr_lst : List instr) (t_lst : List valtype) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instrs_ok C instr_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    Instrs_ok C instr_lst (functype.mk_functype (.mk_list (t_lst ++ t_1_lst)) (.mk_list (t_lst ++ t_2_lst)))


end

/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:143.1-143.69 -/
inductive Expr_ok : context → expr → resulttype → Prop where
  | mk_Expr_ok (C : context) (instr_lst : List instr) (t_lst : List valtype) :
    Instrs_ok C instr_lst (functype.mk_functype (.mk_list []) (.mk_list t_lst)) →
    wf_context C →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    Expr_ok C instr_lst (.mk_list t_lst)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:527.1-527.78 -/
inductive Instr_const : context → instr → Prop where
  | const (C : context) (nt : numtype) (c : num_) :
    wf_context C →
    wf_instr (instr.CONST nt c) →
    Instr_const C (instr.CONST nt c)
  | vconst (C : context) (vt : vectype) (vc : vec_) :
    wf_context C →
    wf_instr (instr.VCONST vt vc) →
    Instr_const C (instr.VCONST vt vc)
  | ref_null (C : context) (rt : reftype) :
    wf_context C →
    wf_instr (instr.REF_NULL rt) →
    Instr_const C (instr.REF_NULL rt)
  | ref_func (C : context) (x : idx) :
    wf_context C →
    wf_instr (instr.REF_FUNC x) →
    Instr_const C (instr.REF_FUNC x)
  | global_get (C : context) (x : idx) (t : valtype) :
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) = (globaltype.mk_globaltype none t) →
    wf_context C →
    wf_instr (instr.GLOBAL_GET x) →
    Instr_const C (instr.GLOBAL_GET x)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:528.1-528.77 -/
inductive Expr_const : context → expr → Prop where
  | mk_Expr_const (C : context) (instr_lst : List instr) :
    Forall (fun (v_instr_elem : instr) => Instr_const C v_instr_elem) instr_lst →
    wf_context C →
    Forall (fun (v_instr_elem : instr) => wf_instr v_instr_elem) instr_lst →
    Expr_const C instr_lst


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:529.1-529.78 -/
inductive Expr_ok_const : context → expr → valtype → Prop where
  | mk_Expr_ok_const (C : context) (v_expr : expr) (t : valtype) :
    Expr_ok C v_expr (.mk_list [t]) →
    Expr_const C v_expr →
    wf_context C →
    Forall (fun (v_expr_elem : instr) => wf_instr v_expr_elem) v_expr →
    Expr_ok_const C v_expr t


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:562.1-562.73 -/
inductive Type_ok : type → functype → Prop where
  | mk_Type_ok (ft : functype) :
    Functype_ok ft →
    Type_ok (type.TYPE ft) ft


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:563.1-563.73 -/
inductive Func_ok : context → func → functype → Prop where
  | mk_Func_ok (C : context) (x : idx) (t_lst : List valtype) (v_expr : expr) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    ((C.TYPES)[proj_uN_0 x]!) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Forall (fun (t_elem : valtype) => t_elem ≠ valtype.BOT) t_lst →
    Expr_ok (C ++ ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := t_1_lst ++ t_lst
      LABELS := [.mk_list t_2_lst]
      RETURN := some (.mk_list t_2_lst) : context
    })) v_expr (.mk_list t_2_lst) →
    wf_context C →
    wf_func (func.FUNC x (Map (fun (t_elem : valtype) => local.LOCAL t_elem) t_lst) v_expr) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := t_1_lst ++ t_lst
      LABELS := [.mk_list t_2_lst]
      RETURN := some (.mk_list t_2_lst) : context
    }) →
    Func_ok C (func.FUNC x (Map (fun (t_elem : valtype) => local.LOCAL t_elem) t_lst) v_expr) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:564.1-564.75 -/
inductive Global_ok : context → global → globaltype → Prop where
  | mk_Global_ok (C : context) (gt : globaltype) (v_expr : expr) (v_mut : «mut») (t : valtype) :
    Globaltype_ok gt →
    gt = (globaltype.mk_globaltype v_mut t) →
    Expr_ok_const C v_expr t →
    wf_context C →
    wf_global (global.GLOBAL gt v_expr) →
    Global_ok C (global.GLOBAL gt v_expr) gt


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:565.1-565.74 -/
inductive Table_ok : context → table → tabletype → Prop where
  | mk_Table_ok (C : context) (tt : tabletype) :
    Tabletype_ok tt →
    wf_context C →
    wf_table (table.TABLE tt) →
    Table_ok C (table.TABLE tt) tt


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:566.1-566.72 -/
inductive Mem_ok : context → mem → memtype → Prop where
  | mk_Mem_ok (C : context) (mt : memtype) :
    Memtype_ok mt →
    wf_context C →
    wf_mem (mem.MEMORY mt) →
    Mem_ok C (mem.MEMORY mt) mt


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:569.1-569.77 -/
inductive Elemmode_ok : context → elemmode → reftype → Prop where
  | active (C : context) (x : idx) (v_expr : expr) (rt : reftype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype lim rt) →
    Expr_ok_const C v_expr valtype.I32 →
    wf_context C →
    wf_elemmode (elemmode.ACTIVE x v_expr) →
    wf_tabletype (tabletype.mk_tabletype lim rt) →
    Elemmode_ok C (elemmode.ACTIVE x v_expr) rt
  | passive (C : context) (rt : reftype) :
    wf_context C →
    wf_elemmode elemmode.PASSIVE →
    Elemmode_ok C elemmode.PASSIVE rt
  | declare (C : context) (rt : reftype) :
    wf_context C →
    wf_elemmode elemmode.DECLARE →
    Elemmode_ok C elemmode.DECLARE rt


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:567.1-567.73 -/
inductive Elem_ok : context → elem → reftype → Prop where
  | mk_Elem_ok (C : context) (rt : reftype) (expr_lst : List expr) (v_elemmode : elemmode) :
    Forall (fun (v_expr_elem : expr) => Expr_ok_const C v_expr_elem (valtype_reftype rt)) expr_lst →
    Elemmode_ok C v_elemmode rt →
    wf_context C →
    wf_elem (elem.ELEM rt expr_lst v_elemmode) →
    Elem_ok C (elem.ELEM rt expr_lst v_elemmode) rt


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:570.1-570.77 -/
inductive Datamode_ok : context → datamode → Prop where
  | active (C : context) (v_expr : expr) (mt : memtype) :
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) = mt →
    Expr_ok_const C v_expr valtype.I32 →
    wf_context C →
    wf_memtype mt →
    wf_datamode (datamode.ACTIVE (uN.mk_uN 0) v_expr) →
    Datamode_ok C (datamode.ACTIVE (uN.mk_uN 0) v_expr)
  | passive (C : context) :
    wf_context C →
    wf_datamode datamode.PASSIVE →
    Datamode_ok C datamode.PASSIVE


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:568.1-568.73 -/
inductive Data_ok : context → data → Prop where
  | mk_Data_ok (C : context) (b_lst : List byte) (v_datamode : datamode) :
    Datamode_ok C v_datamode →
    wf_context C →
    wf_data (data.DATA b_lst v_datamode) →
    Data_ok C (data.DATA b_lst v_datamode)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:571.1-571.74 -/
inductive Start_ok : context → start → Prop where
  | mk_Start_ok (C : context) (x : idx) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) = (functype.mk_functype (.mk_list []) (.mk_list [])) →
    wf_context C →
    wf_start (start.START x) →
    Start_ok C (start.START x)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:635.1-635.80 -/
inductive Import_ok : context → «import» → externtype → Prop where
  | mk_Import_ok (C : context) (name_1 : name) (name_2 : name) (xt : externtype) :
    Externtype_ok xt →
    wf_context C →
    wf_import (import.IMPORT name_1 name_2 xt) →
    Import_ok C (import.IMPORT name_1 name_2 xt) xt


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:637.1-637.83 -/
inductive Externidx_ok : context → externidx → externtype → Prop where
  | func (C : context) (x : idx) (ft : functype) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) = ft →
    wf_context C →
    wf_externidx (externidx.FUNC x) →
    wf_externtype (externtype.FUNC ft) →
    Externidx_ok C (externidx.FUNC x) (externtype.FUNC ft)
  | global (C : context) (x : idx) (gt : globaltype) :
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) = gt →
    wf_context C →
    wf_externidx (externidx.GLOBAL x) →
    wf_externtype (externtype.GLOBAL gt) →
    Externidx_ok C (externidx.GLOBAL x) (externtype.GLOBAL gt)
  | table (C : context) (x : idx) (tt : tabletype) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = tt →
    wf_context C →
    wf_externidx (externidx.TABLE x) →
    wf_externtype (externtype.TABLE tt) →
    Externidx_ok C (externidx.TABLE x) (externtype.TABLE tt)
  | mem (C : context) (x : idx) (mt : memtype) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = mt →
    wf_context C →
    wf_externidx (externidx.MEM x) →
    wf_externtype (externtype.MEM mt) →
    Externidx_ok C (externidx.MEM x) (externtype.MEM mt)


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:636.1-636.80 -/
inductive Export_ok : context → «export» → externtype → Prop where
  | mk_Export_ok (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype) :
    Externidx_ok C v_externidx xt →
    wf_context C →
    wf_externtype xt →
    wf_export (export.EXPORT v_name v_externidx) →
    Export_ok C (export.EXPORT v_name v_externidx) xt


/- Inductive Relations Definition at: ../specification/wasm-2.0/6-typing.spectec:667.1-667.62 -/
inductive Module_ok : module → Prop where
  | mk_Module_ok (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (v_n : n) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») (ft'_lst : List functype) (ixt_lst : List externtype) (C' : context) (gt_lst : List globaltype) (tt_lst : List tabletype) (mt_lst : List memtype) (rt_lst : List reftype) (C : context) (ft_lst : List functype) (xt_lst : List externtype) (ift_lst : List functype) (igt_lst : List globaltype) (itt_lst : List tabletype) (imt_lst : List memtype) (var_3 : List memtype) (var_2 : List tabletype) (var_1 : List globaltype) (var_0 : List functype) :
    fun_memsxt ixt_lst var_3 →
    fun_tablesxt ixt_lst var_2 →
    fun_globalsxt ixt_lst var_1 →
    fun_funcsxt ixt_lst var_0 →
    (List.length ft'_lst) = (List.length type_lst) →
    Forall₂ (fun (ft'_elem : functype) (v_type_elem : type) => Type_ok v_type_elem ft'_elem) ft'_lst type_lst →
    (List.length import_lst) = (List.length ixt_lst) →
    Forall₂ (fun (v_import_elem : «import») (ixt_elem : externtype) => Import_ok ({
      TYPES := ft'_lst
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) v_import_elem ixt_elem) import_lst ixt_lst →
    (List.length global_lst) = (List.length gt_lst) →
    Forall₂ (fun (v_global_elem : global) (gt_elem : globaltype) => Global_ok C' v_global_elem gt_elem) global_lst gt_lst →
    (List.length table_lst) = (List.length tt_lst) →
    Forall₂ (fun (v_table_elem : table) (tt_elem : tabletype) => Table_ok C' v_table_elem tt_elem) table_lst tt_lst →
    (List.length mem_lst) = (List.length mt_lst) →
    Forall₂ (fun (v_mem_elem : mem) (mt_elem : memtype) => Mem_ok C' v_mem_elem mt_elem) mem_lst mt_lst →
    (List.length elem_lst) = (List.length rt_lst) →
    Forall₂ (fun (v_elem_elem : elem) (rt_elem : reftype) => Elem_ok C' v_elem_elem rt_elem) elem_lst rt_lst →
    Forall (fun (v_data_elem : data) => Data_ok C' v_data_elem) data_lst →
    (List.length ft_lst) = (List.length func_lst) →
    Forall₂ (fun (ft_elem : functype) (v_func_elem : func) => Func_ok C v_func_elem ft_elem) ft_lst func_lst →
    Forall (fun (v_start_elem : start) => Start_ok C v_start_elem) (Option.toList start_opt) →
    (List.length export_lst) = (List.length xt_lst) →
    Forall₂ (fun (v_export_elem : «export») (xt_elem : externtype) => Export_ok C v_export_elem xt_elem) export_lst xt_lst →
    (List.length mt_lst) ≤ 1 →
    C = ({
      TYPES := ft'_lst
      FUNCS := ift_lst ++ ft_lst
      GLOBALS := igt_lst ++ gt_lst
      TABLES := itt_lst ++ tt_lst
      MEMS := imt_lst ++ mt_lst
      ELEMS := rt_lst
      DATAS := List.replicate v_n datatype.OK
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    C' = ({
      TYPES := ft'_lst
      FUNCS := ift_lst ++ ft_lst
      GLOBALS := igt_lst
      TABLES := itt_lst ++ tt_lst
      MEMS := imt_lst ++ mt_lst
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    ift_lst = var_0 →
    igt_lst = var_1 →
    itt_lst = var_2 →
    imt_lst = var_3 →
    Forall (fun (ixt_elem : externtype) => wf_externtype ixt_elem) ixt_lst →
    wf_context C' →
    wf_context C →
    Forall (fun (xt_elem : externtype) => wf_externtype xt_elem) xt_lst →
    Forall (fun (iter_elem : tabletype) => wf_tabletype iter_elem) var_2 →
    Forall (fun (iter_elem : memtype) => wf_memtype iter_elem) var_3 →
    wf_module (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) →
    wf_context ({
      TYPES := ft'_lst
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    wf_context ({
      TYPES := ft'_lst
      FUNCS := ift_lst ++ ft_lst
      GLOBALS := igt_lst ++ gt_lst
      TABLES := itt_lst ++ tt_lst
      MEMS := imt_lst ++ mt_lst
      ELEMS := rt_lst
      DATAS := List.replicate v_n datatype.OK
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    wf_context ({
      TYPES := ft'_lst
      FUNCS := ift_lst ++ ft_lst
      GLOBALS := igt_lst
      TABLES := itt_lst ++ tt_lst
      MEMS := imt_lst ++ mt_lst
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    v_n = (List.length data_lst) →
    Module_ok (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:224.1-226.15 -/
inductive Step_pure_before_ref_is_null_false : List admininstr → Prop where
  | ref_is_null_true_0 (v_ref : ref) (rt : reftype) :
    v_ref = (ref.REF_NULL rt) →
    Step_pure_before_ref_is_null_false [admininstr_ref v_ref, admininstr.REF_IS_NULL]


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:276.1-278.15 -/
inductive Step_pure_before_vtestop_false : List admininstr → Prop where
  | vtestop_true_0 (c : vec_) (v_Jnn : Jnn) (v_N : N) (ci_1_lst : List lane_) :
    ci_1_lst = (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) c) →
    Forall (fun (ci_1_elem : lane_) => (proj_lane__2 ci_1_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_1_elem : lane_) => (proj_uN_0 (Option.get! (proj_lane__2 ci_1_elem))) ≠ 0) ci_1_lst →
    Forall (fun (ci_1_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N))) ci_1_elem) ci_1_lst →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    Step_pure_before_vtestop_false [admininstr.VCONST vectype.V128 c, admininstr.VTESTOP (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) (vtestop_.mk_vtestop__0 v_Jnn v_N vtestop_Jnn_N.ALL_TRUE)]


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:6.1-6.109 -/
inductive Step_pure : List admininstr → List admininstr → Prop where
  | unreachable : Step_pure [admininstr.UNREACHABLE] [admininstr.TRAP]
  | nop : Step_pure [admininstr.NOP] []
  | drop (v_val : val) : Step_pure [admininstr_val v_val, admininstr.DROP] []
  | select_true (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : Option (List valtype)) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0 →
    Step_pure [admininstr_val val_1, admininstr_val val_2, admininstr.CONST numtype.I32 c, admininstr.SELECT t_lst_opt] [admininstr_val val_1]
  | select_false (val_1 : val) (val_2 : val) (c : num_) (t_lst_opt : Option (List valtype)) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) = 0 →
    Step_pure [admininstr_val val_1, admininstr_val val_2, admininstr.CONST numtype.I32 c, admininstr.SELECT t_lst_opt] [admininstr_val val_2]
  | if_true (c : num_) (bt : blocktype) (instr_1_lst : List instr) (instr_2_lst : List instr) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0 →
    Step_pure [admininstr.CONST numtype.I32 c, admininstr.IFELSE bt instr_1_lst instr_2_lst] [admininstr.BLOCK bt instr_1_lst]
  | if_false (c : num_) (bt : blocktype) (instr_1_lst : List instr) (instr_2_lst : List instr) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) = 0 →
    Step_pure [admininstr.CONST numtype.I32 c, admininstr.IFELSE bt instr_1_lst instr_2_lst] [admininstr.BLOCK bt instr_2_lst]
  | label_vals (v_n : n) (instr_lst : List instr) (val_lst : List val) : Step_pure [admininstr.LABEL_ v_n instr_lst (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)] (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)
  | br_zero (v_n : n) (instr'_lst : List instr) (val'_lst : List val) (val_lst : List val) (instr_lst : List instr) :
    v_n = (List.length val_lst) →
    Step_pure [admininstr.LABEL_ v_n instr'_lst ((((Map (fun (val'_elem : val) => admininstr_val val'_elem) val'_lst) ++ (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)) ++ [admininstr.BR (uN.mk_uN 0)]) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (Map (fun (instr'_elem : instr) => admininstr_instr instr'_elem) instr'_lst))
  | br_succ (v_n : n) (instr'_lst : List instr) (val_lst : List val) (l : labelidx) (instr_lst : List instr) : Step_pure [admininstr.LABEL_ v_n instr'_lst (((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.BR (uN.mk_uN ((proj_uN_0 l) + 1))]) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.BR l])
  | br_if_true (c : num_) (l : labelidx) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) ≠ 0 →
    Step_pure [admininstr.CONST numtype.I32 c, admininstr.BR_IF l] [admininstr.BR l]
  | br_if_false (c : num_) (l : labelidx) :
    (proj_num__0 c) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 c))) = 0 →
    Step_pure [admininstr.CONST numtype.I32 c, admininstr.BR_IF l] []
  | br_table_lt (i : num_) (l_lst : List labelidx) (l' : labelidx) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length l_lst) →
    (proj_num__0 i) ≠ none →
    Step_pure [admininstr.CONST numtype.I32 i, admininstr.BR_TABLE l_lst l'] [admininstr.BR ((l_lst)[proj_uN_0 (Option.get! (proj_num__0 i))]!)]
  | br_table_ge (i : num_) (l_lst : List labelidx) (l' : labelidx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) ≥ (List.length l_lst) →
    Step_pure [admininstr.CONST numtype.I32 i, admininstr.BR_TABLE l_lst l'] [admininstr.BR l']
  | frame_vals (v_n : n) (f : frame) (val_lst : List val) :
    v_n = (List.length val_lst) →
    Step_pure [admininstr.FRAME_ v_n f (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)] (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)
  | return_frame (v_n : n) (f : frame) (val'_lst : List val) (val_lst : List val) (instr_lst : List instr) :
    v_n = (List.length val_lst) →
    Step_pure [admininstr.FRAME_ v_n f ((((Map (fun (val'_elem : val) => admininstr_val val'_elem) val'_lst) ++ (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)) ++ [admininstr.RETURN]) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))] (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)
  | return_label (v_n : n) (instr'_lst : List instr) (val_lst : List val) (instr_lst : List instr) : Step_pure [admininstr.LABEL_ v_n instr'_lst (((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.RETURN]) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.RETURN])
  | trap_vals (val_lst : List val) (instr_lst : List instr) :
    (val_lst ≠ []) ∨ (instr_lst ≠ []) →
    Step_pure ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ ([admininstr.TRAP] ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))) [admininstr.TRAP]
  | trap_label (v_n : n) (instr'_lst : List instr) : Step_pure [admininstr.LABEL_ v_n instr'_lst [admininstr.TRAP]] [admininstr.TRAP]
  | trap_frame (v_n : n) (f : frame) : Step_pure [admininstr.FRAME_ v_n f [admininstr.TRAP]] [admininstr.TRAP]
  | unop_val (nt : numtype) (c_1 : num_) (unop : unop_) (c : num_) :
    (List.length (fun_unop_ nt unop c_1)) > 0 →
    List.contains (fun_unop_ nt unop c_1) c →
    Step_pure [admininstr.CONST nt c_1, admininstr.UNOP nt unop] [admininstr.CONST nt c]
  | unop_trap (nt : numtype) (c_1 : num_) (unop : unop_) :
    (fun_unop_ nt unop c_1) = [] →
    Step_pure [admininstr.CONST nt c_1, admininstr.UNOP nt unop] [admininstr.TRAP]
  | binop_val (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (c : num_) (var_0 : List num_) :
    fun_binop_ nt binop c_1 c_2 var_0 →
    (List.length var_0) > 0 →
    List.contains var_0 c →
    Step_pure [admininstr.CONST nt c_1, admininstr.CONST nt c_2, admininstr.BINOP nt binop] [admininstr.CONST nt c]
  | binop_trap (nt : numtype) (c_1 : num_) (c_2 : num_) (binop : binop_) (var_0 : List num_) :
    fun_binop_ nt binop c_1 c_2 var_0 →
    var_0 = [] →
    Step_pure [admininstr.CONST nt c_1, admininstr.CONST nt c_2, admininstr.BINOP nt binop] [admininstr.TRAP]
  | testop (nt : numtype) (c_1 : num_) (testop : testop_) (c : num_) :
    c = (fun_testop_ nt testop c_1) →
    Step_pure [admininstr.CONST nt c_1, admininstr.TESTOP nt testop] [admininstr.CONST numtype.I32 c]
  | relop (nt : numtype) (c_1 : num_) (c_2 : num_) (relop : relop_) (c : num_) (var_0 : num_) :
    fun_relop_ nt relop c_1 c_2 var_0 →
    c = var_0 →
    Step_pure [admininstr.CONST nt c_1, admininstr.CONST nt c_2, admininstr.RELOP nt relop] [admininstr.CONST numtype.I32 c]
  | cvtop_val (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (cvtop : cvtop__) (c : num_) (var_0 : List num_) :
    fun_cvtop__ nt_1 nt_2 cvtop c_1 var_0 →
    (List.length var_0) > 0 →
    List.contains var_0 c →
    Step_pure [admininstr.CONST nt_1 c_1, admininstr.CVTOP nt_2 nt_1 cvtop] [admininstr.CONST nt_2 c]
  | cvtop_trap (nt_1 : numtype) (c_1 : num_) (nt_2 : numtype) (cvtop : cvtop__) (var_0 : List num_) :
    fun_cvtop__ nt_1 nt_2 cvtop c_1 var_0 →
    var_0 = [] →
    Step_pure [admininstr.CONST nt_1 c_1, admininstr.CVTOP nt_2 nt_1 cvtop] [admininstr.TRAP]
  | ref_is_null_true (v_ref : ref) (rt : reftype) :
    v_ref = (ref.REF_NULL rt) →
    Step_pure [admininstr_ref v_ref, admininstr.REF_IS_NULL] [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))]
  | ref_is_null_false (v_ref : ref) :
    ¬ Step_pure_before_ref_is_null_false [admininstr_ref v_ref, admininstr.REF_IS_NULL] →
    Step_pure [admininstr_ref v_ref, admininstr.REF_IS_NULL] [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))]
  | vvunop (c_1 : vec_) (v_vvunop : vvunop) (c : vec_) :
    c = (vvunop_ vectype.V128 v_vvunop c_1) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VVUNOP vectype.V128 v_vvunop] [admininstr.VCONST vectype.V128 c]
  | vvbinop (c_1 : vec_) (c_2 : vec_) (v_vvbinop : vvbinop) (c : vec_) :
    c = (vvbinop_ vectype.V128 v_vvbinop c_1 c_2) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VVBINOP vectype.V128 v_vvbinop] [admininstr.VCONST vectype.V128 c]
  | vvternop (c_1 : vec_) (c_2 : vec_) (c_3 : vec_) (v_vvternop : vvternop) (c : vec_) :
    c = (vvternop_ vectype.V128 v_vvternop c_1 c_2 c_3) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VCONST vectype.V128 c_3, admininstr.VVTERNOP vectype.V128 v_vvternop] [admininstr.VCONST vectype.V128 c]
  | vvtestop (c_1 : vec_) (c : num_) :
    (proj_num__0 c) ≠ none →
    (size valtype.V128) ≠ none →
    (Option.get! (proj_num__0 c)) = (ine_ (Option.get! (size valtype.V128)) c_1 (uN.mk_uN 0)) →
    wf_uN 128 (uN.mk_uN 0) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VVTESTOP vectype.V128 vvtestop.ANY_TRUE] [admininstr.CONST numtype.I32 c]
  | vunop (c_1 : vec_) (sh : shape) (vunop : vunop_) (c : vec_) (var_0 : List vec_) :
    fun_vunop_ sh vunop c_1 var_0 →
    (List.length var_0) > 0 →
    List.contains var_0 c →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VUNOP sh vunop] [admininstr.VCONST vectype.V128 c]
  | vunop_trap (c_1 : vec_) (sh : shape) (vunop : vunop_) (var_0 : List vec_) :
    fun_vunop_ sh vunop c_1 var_0 →
    var_0 = [] →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VUNOP sh vunop] [admininstr.TRAP]
  | vbinop_val (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (c : vec_) (var_0 : List vec_) :
    fun_vbinop_ sh vbinop c_1 c_2 var_0 →
    (List.length var_0) > 0 →
    List.contains var_0 c →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VBINOP sh vbinop] [admininstr.VCONST vectype.V128 c]
  | vbinop_trap (c_1 : vec_) (c_2 : vec_) (sh : shape) (vbinop : vbinop_) (var_0 : List vec_) :
    fun_vbinop_ sh vbinop c_1 c_2 var_0 →
    var_0 = [] →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VBINOP sh vbinop] [admininstr.TRAP]
  | vtestop_true (c : vec_) (v_Jnn : Jnn) (v_N : N) (ci_1_lst : List lane_) :
    ci_1_lst = (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) c) →
    Forall (fun (ci_1_elem : lane_) => (proj_lane__2 ci_1_elem) ≠ none) ci_1_lst →
    Forall (fun (ci_1_elem : lane_) => (proj_uN_0 (Option.get! (proj_lane__2 ci_1_elem))) ≠ 0) ci_1_lst →
    Forall (fun (ci_1_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N))) ci_1_elem) ci_1_lst →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    Step_pure [admininstr.VCONST vectype.V128 c, admininstr.VTESTOP (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) (vtestop_.mk_vtestop__0 v_Jnn v_N vtestop_Jnn_N.ALL_TRUE)] [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))]
  | vtestop_false (c : vec_) (v_Jnn : Jnn) (v_N : N) :
    ¬ Step_pure_before_vtestop_false [admininstr.VCONST vectype.V128 c, admininstr.VTESTOP (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) (vtestop_.mk_vtestop__0 v_Jnn v_N vtestop_Jnn_N.ALL_TRUE)] →
    Step_pure [admininstr.VCONST vectype.V128 c, admininstr.VTESTOP (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) (vtestop_.mk_vtestop__0 v_Jnn v_N vtestop_Jnn_N.ALL_TRUE)] [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))]
  | vrelop (c_1 : vec_) (c_2 : vec_) (sh : shape) (vrelop : vrelop_) (c : vec_) (var_0 : vec_) :
    fun_vrelop_ sh vrelop c_1 c_2 var_0 →
    var_0 = c →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VRELOP sh vrelop] [admininstr.VCONST vectype.V128 c]
  | vshiftop (c_1 : vec_) (v_n : n) (v_Jnn : Jnn) (v_N : N) (vshiftop : vshiftop_) (c : vec_) (c'_lst : List lane_) (var_0_lst : List lane_) :
    (List.length var_0_lst) = (List.length c'_lst) →
    Forall₂ (fun (var_0_elem : lane_) (c'_elem : lane_) => fun_vshiftop_ (ishape.X v_Jnn (dim.mk_dim v_N)) vshiftop c'_elem (uN.mk_uN v_n) var_0_elem) var_0_lst c'_lst →
    c'_lst = (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) c_1) →
    c = (inv_lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) var_0_lst) →
    Forall (fun (c'_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N))) c'_elem) c'_lst →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_ishape (ishape.X v_Jnn (dim.mk_dim v_N)) →
    wf_uN 32 (uN.mk_uN v_n) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.VSHIFTOP (ishape.X v_Jnn (dim.mk_dim v_N)) vshiftop] [admininstr.VCONST vectype.V128 c]
  | vbitmask (c : vec_) (v_Jnn : Jnn) (v_N : N) (ci : iN) (ci_1_lst : List lane_) (var_0_lst : List uN) :
    (List.length var_0_lst) = (List.length ci_1_lst) →
    Forall (fun (ci_1_elem : lane_) => (proj_lane__2 ci_1_elem) ≠ none) ci_1_lst →
    Forall₂ (fun (var_0_elem : uN) (ci_1_elem : lane_) => fun_ilt_ (lsize (lanetype_Jnn v_Jnn)) sx.S (Option.get! (proj_lane__2 ci_1_elem)) (uN.mk_uN 0) var_0_elem) var_0_lst ci_1_lst →
    ci_1_lst = (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) c) →
    (ibits_ 32 ci) = ((Map (fun (var_0_elem : uN) => bit.mk_bit (proj_uN_0 var_0_elem)) var_0_lst) ++ (List.replicate (Int.toNat ((32 : Int) - (v_N : Int))) (bit.mk_bit 0))) →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    Forall (fun (var_0_elem : uN) => wf_bit (bit.mk_bit (proj_uN_0 var_0_elem))) var_0_lst →
    wf_bit (bit.mk_bit 0) →
    Step_pure [admininstr.VCONST vectype.V128 c, admininstr.VBITMASK (ishape.X v_Jnn (dim.mk_dim v_N))] [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (irev_ 32 ci))]
  | vswizzle (c_1 : vec_) (c_2 : vec_) (v_Pnn : Pnn) (v_M : M) (c : vec_) (ci_lst : List lane_) (c'_lst : List iN) (k : Nat) :
    ci_lst = (lanes_ (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_M)) c_2) →
    Forall (fun (iter_0_elem : lane_) => (proj_lane__1 iter_0_elem) ≠ none) (lanes_ (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_M)) c_1) →
    c'_lst = ((Map (fun (iter_0_elem : lane_) => Option.get! (proj_lane__1 iter_0_elem)) (lanes_ (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_M)) c_1)) ++ (List.replicate (Int.toNat ((256 : Int) - (v_M : Int))) (uN.mk_uN 0))) →
    Forall (fun (k : Nat) => (proj_uN_0 (Option.get! (proj_lane__1 ((ci_lst)[k]!)))) < (List.length c'_lst)) (List.range v_M) →
    Forall (fun (k : Nat) => (proj_lane__1 ((ci_lst)[k]!)) ≠ none) (List.range v_M) →
    Forall (fun (k : Nat) => k < (List.length ci_lst)) (List.range v_M) →
    c = (inv_lanes_ (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_M)) (List.range v_M |>.map (fun (k : Nat) => lane_.mk_lane__1 v_Pnn ((c'_lst)[proj_uN_0 (Option.get! (proj_lane__1 ((ci_lst)[k]!)))]!)))) →
    wf_shape (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_M)) →
    wf_uN (psize v_Pnn) (uN.mk_uN 0) →
    Forall (fun (k : Nat) => wf_lane_ (fun_lanetype (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_M))) (lane_.mk_lane__1 v_Pnn ((c'_lst)[proj_uN_0 (Option.get! (proj_lane__1 ((ci_lst)[k]!)))]!))) (List.range v_M) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VSWIZZLE (ishape.X (Jnn_packtype v_Pnn) (dim.mk_dim v_M))] [admininstr.VCONST vectype.V128 c]
  | vshuffle (c_1 : vec_) (c_2 : vec_) (v_Pnn : Pnn) (v_N : N) (i_lst : List laneidx) (c : vec_) (c'_lst : List iN) (k : Nat) :
    (Map (fun (c'_elem : iN) => lane_.mk_lane__1 v_Pnn c'_elem) c'_lst) = ((lanes_ (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_N)) c_1) ++ (lanes_ (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_N)) c_2)) →
    Forall (fun (k : Nat) => (proj_uN_0 ((i_lst)[k]!)) < (List.length c'_lst)) (List.range v_N) →
    Forall (fun (k : Nat) => k < (List.length i_lst)) (List.range v_N) →
    c = (inv_lanes_ (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_N)) (List.range v_N |>.map (fun (k : Nat) => lane_.mk_lane__1 v_Pnn ((c'_lst)[proj_uN_0 ((i_lst)[k]!)]!)))) →
    Forall (fun (c'_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_N))) (lane_.mk_lane__1 v_Pnn c'_elem)) c'_lst →
    wf_shape (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_N)) →
    Forall (fun (k : Nat) => wf_lane_ (fun_lanetype (shape.X (lanetype_packtype v_Pnn) (dim.mk_dim v_N))) (lane_.mk_lane__1 v_Pnn ((c'_lst)[proj_uN_0 ((i_lst)[k]!)]!))) (List.range v_N) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VSHUFFLE (ishape.X (Jnn_packtype v_Pnn) (dim.mk_dim v_N)) i_lst] [admininstr.VCONST vectype.V128 c]
  | vsplat (v_Lnn : Lnn) (c_1 : num_) (v_N : N) (c : vec_) :
    c = (inv_lanes_ (shape.X v_Lnn (dim.mk_dim v_N)) (List.replicate v_N (packnum_ v_Lnn c_1))) →
    wf_shape (shape.X v_Lnn (dim.mk_dim v_N)) →
    Step_pure [admininstr.CONST (unpack v_Lnn) c_1, admininstr.VSPLAT (shape.X v_Lnn (dim.mk_dim v_N))] [admininstr.VCONST vectype.V128 c]
  | vextract_lane_num (c_1 : vec_) (nt : numtype) (v_N : N) (i : laneidx) (c_2 : num_) :
    (proj_uN_0 i) < (List.length (lanes_ (shape.X (lanetype_numtype nt) (dim.mk_dim v_N)) c_1)) →
    (lane_.mk_lane__0 nt c_2) = ((lanes_ (shape.X (lanetype_numtype nt) (dim.mk_dim v_N)) c_1)[proj_uN_0 i]!) →
    wf_lane_ (fun_lanetype (shape.X (lanetype_numtype nt) (dim.mk_dim v_N))) (lane_.mk_lane__0 nt c_2) →
    wf_shape (shape.X (lanetype_numtype nt) (dim.mk_dim v_N)) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VEXTRACT_LANE (shape.X (lanetype_numtype nt) (dim.mk_dim v_N)) none i] [admininstr.CONST nt c_2]
  | vextract_lane_pack (c_1 : vec_) (pt : packtype) (v_N : N) (v_sx : sx) (i : laneidx) (c_2 : num_) :
    (proj_num__0 c_2) ≠ none →
    (proj_lane__1 ((lanes_ (shape.X (lanetype_packtype pt) (dim.mk_dim v_N)) c_1)[proj_uN_0 i]!)) ≠ none →
    (proj_uN_0 i) < (List.length (lanes_ (shape.X (lanetype_packtype pt) (dim.mk_dim v_N)) c_1)) →
    (Option.get! (proj_num__0 c_2)) = (extend__ (psize pt) 32 v_sx (Option.get! (proj_lane__1 ((lanes_ (shape.X (lanetype_packtype pt) (dim.mk_dim v_N)) c_1)[proj_uN_0 i]!)))) →
    wf_shape (shape.X (lanetype_packtype pt) (dim.mk_dim v_N)) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VEXTRACT_LANE (shape.X (lanetype_packtype pt) (dim.mk_dim v_N)) (some v_sx) i] [admininstr.CONST numtype.I32 c_2]
  | vreplace_lane (c_1 : vec_) (v_Lnn : Lnn) (c_2 : num_) (v_N : N) (i : laneidx) (c : vec_) :
    c = (inv_lanes_ (shape.X v_Lnn (dim.mk_dim v_N)) (List.modify (lanes_ (shape.X v_Lnn (dim.mk_dim v_N)) c_1) (proj_uN_0 i) (fun elem_1 => packnum_ v_Lnn c_2))) →
    wf_shape (shape.X v_Lnn (dim.mk_dim v_N)) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.CONST (unpack v_Lnn) c_2, admininstr.VREPLACE_LANE (shape.X v_Lnn (dim.mk_dim v_N)) i] [admininstr.VCONST vectype.V128 c]
  | vextunop (c_1 : vec_) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop_) (c : vec_) (var_0 : vec_) :
    fun_vextunop__ sh_1 sh_2 vextunop c_1 var_0 →
    var_0 = c →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VEXTUNOP sh_1 sh_2 vextunop] [admininstr.VCONST vectype.V128 c]
  | vextbinop (c_1 : vec_) (c_2 : vec_) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop_) (c : vec_) (var_0 : vec_) :
    fun_vextbinop__ sh_1 sh_2 vextbinop c_1 c_2 var_0 →
    var_0 = c →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VEXTBINOP sh_1 sh_2 vextbinop] [admininstr.VCONST vectype.V128 c]
  | vnarrow (c_1 : vec_) (c_2 : vec_) (Jnn_2 : Jnn) (N_2 : N) (Jnn_1 : Jnn) (N_1 : N) (v_sx : sx) (c : vec_) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (cj_1_lst : List iN) (cj_2_lst : List iN) :
    ci_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim N_1)) c_1) →
    ci_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim N_1)) c_2) →
    Forall (fun (ci_1_elem : lane_) => (proj_lane__2 ci_1_elem) ≠ none) ci_1_lst →
    cj_1_lst = (Map (fun (ci_1_elem : lane_) => narrow__ (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (Option.get! (proj_lane__2 ci_1_elem))) ci_1_lst) →
    Forall (fun (ci_2_elem : lane_) => (proj_lane__2 ci_2_elem) ≠ none) ci_2_lst →
    cj_2_lst = (Map (fun (ci_2_elem : lane_) => narrow__ (lsize (lanetype_Jnn Jnn_1)) (lsize (lanetype_Jnn Jnn_2)) v_sx (Option.get! (proj_lane__2 ci_2_elem))) ci_2_lst) →
    c = (inv_lanes_ (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim N_2)) ((Map (fun (cj_1_elem : iN) => lane_.mk_lane__2 Jnn_2 cj_1_elem) cj_1_lst) ++ (Map (fun (cj_2_elem : iN) => lane_.mk_lane__2 Jnn_2 cj_2_elem) cj_2_lst))) →
    Forall (fun (ci_1_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim N_1))) ci_1_elem) ci_1_lst →
    Forall (fun (ci_2_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim N_1))) ci_2_elem) ci_2_lst →
    wf_shape (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim N_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim N_2)) →
    Forall (fun (cj_1_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim N_2))) (lane_.mk_lane__2 Jnn_2 cj_1_elem)) cj_1_lst →
    Forall (fun (cj_2_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim N_2))) (lane_.mk_lane__2 Jnn_2 cj_2_elem)) cj_2_lst →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCONST vectype.V128 c_2, admininstr.VNARROW (ishape.X Jnn_2 (dim.mk_dim N_2)) (ishape.X Jnn_1 (dim.mk_dim N_1)) v_sx] [admininstr.VCONST vectype.V128 c]
  | vcvtop_full (c_1 : vec_) (Lnn_2 : Lnn) (v_M : M) (Lnn_1 : Lnn) (v_vcvtop : vcvtop) (c : vec_) (ci_lst : List lane_) (cj_lst_lst : List (List lane_)) :
    ((halfop v_vcvtop) = none) ∧ ((zeroop v_vcvtop) = none) →
    ci_lst = (lanes_ (shape.X Lnn_1 (dim.mk_dim v_M)) c_1) →
    cj_lst_lst = (setproduct_ lane_ (Map (fun (ci_elem : lane_) => vcvtop__ (shape.X Lnn_1 (dim.mk_dim v_M)) (shape.X Lnn_2 (dim.mk_dim v_M)) v_vcvtop ci_elem) ci_lst)) →
    (List.length (Map (fun (cj_lst_elem : List lane_) => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim v_M)) cj_lst_elem) cj_lst_lst)) > 0 →
    List.contains (Map (fun (cj_lst_elem : List lane_) => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim v_M)) cj_lst_elem) cj_lst_lst) c →
    Forall (fun (ci_elem : lane_) => wf_lane_ (fun_lanetype (shape.X Lnn_1 (dim.mk_dim v_M))) ci_elem) ci_lst →
    Forall (fun (cj_lst_elem : List lane_) => Forall (fun (cj_elem : lane_) => wf_lane_ Lnn_2 cj_elem) cj_lst_elem) cj_lst_lst →
    wf_shape (shape.X Lnn_1 (dim.mk_dim v_M)) →
    wf_shape (shape.X Lnn_2 (dim.mk_dim v_M)) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCVTOP (shape.X Lnn_2 (dim.mk_dim v_M)) (shape.X Lnn_1 (dim.mk_dim v_M)) v_vcvtop] [admininstr.VCONST vectype.V128 c]
  | vcvtop_half (c_1 : vec_) (Lnn_2 : Lnn) (M_2 : M) (Lnn_1 : Lnn) (M_1 : M) (v_vcvtop : vcvtop) (c : vec_) (v_half : half) (ci_lst : List lane_) (cj_lst_lst : List (List lane_)) :
    (halfop v_vcvtop) = (some v_half) →
    ci_lst = (List.take M_2 (List.drop (fun_half v_half 0 M_2) (lanes_ (shape.X Lnn_1 (dim.mk_dim M_1)) c_1))) →
    cj_lst_lst = (setproduct_ lane_ (Map (fun (ci_elem : lane_) => vcvtop__ (shape.X Lnn_1 (dim.mk_dim M_1)) (shape.X Lnn_2 (dim.mk_dim M_2)) v_vcvtop ci_elem) ci_lst)) →
    (List.length (Map (fun (cj_lst_elem : List lane_) => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim M_2)) cj_lst_elem) cj_lst_lst)) > 0 →
    List.contains (Map (fun (cj_lst_elem : List lane_) => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim M_2)) cj_lst_elem) cj_lst_lst) c →
    Forall (fun (ci_elem : lane_) => wf_lane_ (fun_lanetype (shape.X Lnn_1 (dim.mk_dim M_1))) ci_elem) ci_lst →
    Forall (fun (cj_lst_elem : List lane_) => Forall (fun (cj_elem : lane_) => wf_lane_ Lnn_2 cj_elem) cj_lst_elem) cj_lst_lst →
    wf_shape (shape.X Lnn_1 (dim.mk_dim M_1)) →
    wf_shape (shape.X Lnn_2 (dim.mk_dim M_2)) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCVTOP (shape.X Lnn_2 (dim.mk_dim M_2)) (shape.X Lnn_1 (dim.mk_dim M_1)) v_vcvtop] [admininstr.VCONST vectype.V128 c]
  | vcvtop_zero (c_1 : vec_) (nt_2 : numtype) (M_2 : M) (nt_1 : numtype) (M_1 : M) (v_vcvtop : vcvtop) (c : vec_) (ci_lst : List lane_) (cj_lst_lst : List (List lane_)) :
    (zeroop v_vcvtop) = (some zero.ZERO) →
    ci_lst = (lanes_ (shape.X (lanetype_numtype nt_1) (dim.mk_dim M_1)) c_1) →
    cj_lst_lst = (setproduct_ lane_ ((Map (fun (ci_elem : lane_) => vcvtop__ (shape.X (lanetype_numtype nt_1) (dim.mk_dim M_1)) (shape.X (lanetype_numtype nt_2) (dim.mk_dim M_2)) v_vcvtop ci_elem) ci_lst) ++ (List.replicate M_1 [lane_.mk_lane__0 nt_2 (fun_zero nt_2)]))) →
    (List.length (Map (fun (cj_lst_elem : List lane_) => inv_lanes_ (shape.X (lanetype_numtype nt_2) (dim.mk_dim M_2)) cj_lst_elem) cj_lst_lst)) > 0 →
    List.contains (Map (fun (cj_lst_elem : List lane_) => inv_lanes_ (shape.X (lanetype_numtype nt_2) (dim.mk_dim M_2)) cj_lst_elem) cj_lst_lst) c →
    Forall (fun (ci_elem : lane_) => wf_lane_ (fun_lanetype (shape.X (lanetype_numtype nt_1) (dim.mk_dim M_1))) ci_elem) ci_lst →
    Forall (fun (cj_lst_elem : List lane_) => Forall (fun (cj_elem : lane_) => wf_lane_ (lanetype_numtype nt_2) cj_elem) cj_lst_elem) cj_lst_lst →
    wf_shape (shape.X (lanetype_numtype nt_1) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_numtype nt_2) (dim.mk_dim M_2)) →
    wf_lane_ (lanetype_numtype nt_2) (lane_.mk_lane__0 nt_2 (fun_zero nt_2)) →
    Step_pure [admininstr.VCONST vectype.V128 c_1, admininstr.VCVTOP (shape.X (lanetype_numtype nt_2) (dim.mk_dim M_2)) (shape.X (lanetype_numtype nt_1) (dim.mk_dim M_1)) v_vcvtop] [admininstr.VCONST vectype.V128 c]
  | local_tee (v_val : val) (x : idx) : Step_pure [admininstr_val v_val, admininstr.LOCAL_TEE x] [admininstr_val v_val, admininstr_val v_val, admininstr.LOCAL_SET x]


/- Well-Formedness Theorem at: ../specification/wasm-2.0/8-reduction.spectec:6.10-6.19 -/
theorem Step_pure_is_wf (var_0 : List admininstr) (var_1 : List admininstr) :
  Forall (fun (var_0_elem : admininstr) => wf_admininstr var_0_elem) var_0 →
  Step_pure var_0 var_1 →
  Forall (fun (var_1_elem : admininstr) => wf_admininstr var_1_elem) var_1 :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/8-reduction.spectec:63.1-63.73 -/
def fun_blocktype (v_state : state) (v_blocktype : blocktype) : functype :=
  match v_blocktype with
  | blocktype._RESULT none => functype.mk_functype (.mk_list []) (.mk_list [])
  | blocktype._RESULT (some t) => functype.mk_functype (.mk_list []) (.mk_list [t])
  | blocktype._IDX x => fun_type v_state x

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:127.1-129.15 -/
inductive Step_read_before_call_indirect_trap : config → Prop where
  | call_indirect_call_0 (z : state) (i : num_) (x : idx) (y : idx) (a : addr) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    (proj_num__0 i) ≠ none →
    (((fun_table z x).REFS)[proj_uN_0 (Option.get! (proj_num__0 i))]!) = (ref.REF_FUNC_ADDR a) →
    a < (List.length (fun_funcinst z)) →
    (fun_type z y) = (((fun_funcinst z)[a]!).TYPE) →
    Step_read_before_call_indirect_trap (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CALL_INDIRECT x y])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:436.1-439.14 -/
inductive Step_read_before_table_fill_zero : config → Prop where
  | table_fill_trap_0 (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS)) →
    Step_read_before_table_fill_zero (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_FILL x])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:452.1-455.14 -/
inductive Step_read_before_table_copy_zero : config → Prop where
  | table_copy_trap_0 (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z y).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS))) →
    Step_read_before_table_copy_zero (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:457.1-462.15 -/
inductive Step_read_before_table_copy_le : config → Prop where
  | table_copy_zero_0 (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    ¬ Step_read_before_table_copy_zero (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) →
    v_n = 0 →
    Step_read_before_table_copy_le (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y])
  | table_copy_trap_1 (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z y).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS))) →
    Step_read_before_table_copy_le (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:475.1-478.14 -/
inductive Step_read_before_table_init_zero : config → Prop where
  | table_init_trap_0 (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_elem z y).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS))) →
    Step_read_before_table_init_zero (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_INIT x y])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:616.1-619.14 -/
inductive Step_read_before_memory_fill_zero : config → Prop where
  | memory_fill_trap_0 (z : state) (i : num_) (v_val : val) (v_n : n) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read_before_memory_fill_zero (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_FILL])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:632.1-635.14 -/
inductive Step_read_before_memory_copy_zero : config → Prop where
  | memory_copy_trap_0 (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read_before_memory_copy_zero (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:637.1-642.15 -/
inductive Step_read_before_memory_copy_le : config → Prop where
  | memory_copy_zero_0 (z : state) (j : num_) (i : num_) (v_n : n) :
    ¬ Step_read_before_memory_copy_zero (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) →
    v_n = 0 →
    Step_read_before_memory_copy_le (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY])
  | memory_copy_trap_1 (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read_before_memory_copy_le (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:655.1-658.14 -/
inductive Step_read_before_memory_init_zero : config → Prop where
  | memory_init_trap_0 (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_data z x).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read_before_memory_init_zero (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_INIT x])


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:7.1-7.109 -/
inductive Step_read : config → List admininstr → Prop where
  | block (z : state) (k : Nat) (val_lst : List val) (bt : blocktype) (instr_lst : List instr) (v_n : n) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (fun_blocktype z bt) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    k = (List.length val_lst) →
    k = (List.length t_1_lst) →
    v_n = (List.length t_2_lst) →
    Step_read (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.BLOCK bt instr_lst])) [admininstr.LABEL_ v_n [] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))]
  | loop (z : state) (k : Nat) (val_lst : List val) (bt : blocktype) (instr_lst : List instr) (t_1_lst : List valtype) (v_n : n) (t_2_lst : List valtype) :
    (fun_blocktype z bt) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    k = (List.length val_lst) →
    k = (List.length t_1_lst) →
    v_n = (List.length t_2_lst) →
    Step_read (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.LOOP bt instr_lst])) [admininstr.LABEL_ k [instr.LOOP bt instr_lst] ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst))]
  | call (z : state) (x : idx) :
    (proj_uN_0 x) < (List.length (fun_funcaddr z)) →
    Step_read (config.mk_config z [admininstr.CALL x]) [admininstr.CALL_ADDR ((fun_funcaddr z)[proj_uN_0 x]!)]
  | call_indirect_call (z : state) (i : num_) (x : idx) (y : idx) (a : addr) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    (proj_num__0 i) ≠ none →
    (((fun_table z x).REFS)[proj_uN_0 (Option.get! (proj_num__0 i))]!) = (ref.REF_FUNC_ADDR a) →
    a < (List.length (fun_funcinst z)) →
    (fun_type z y) = (((fun_funcinst z)[a]!).TYPE) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CALL_INDIRECT x y]) [admininstr.CALL_ADDR a]
  | call_indirect_trap (z : state) (i : num_) (x : idx) (y : idx) :
    ¬ Step_read_before_call_indirect_trap (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CALL_INDIRECT x y]) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CALL_INDIRECT x y]) [admininstr.TRAP]
  | call_addr (z : state) (k : Nat) (val_lst : List val) (a : addr) (v_n : n) (f : frame) (instr_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) (mm : moduleinst) (v_func : func) (x : idx) (t_lst : List valtype) :
    a < (List.length (fun_funcinst z)) →
    ((fun_funcinst z)[a]!) = ({
      TYPE := functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)
      MODULE := mm
      CODE := v_func : funcinst
    }) →
    v_func = (func.FUNC x (Map (fun (t_elem : valtype) => local.LOCAL t_elem) t_lst) instr_lst) →
    Forall (fun (t_elem : valtype) => (default_ t_elem) ≠ none) t_lst →
    f = ({
      LOCALS := val_lst ++ (Map (fun (t_elem : valtype) => Option.get! (default_ t_elem)) t_lst)
      MODULE := mm : frame
    }) →
    wf_funcinst ({
      TYPE := functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)
      MODULE := mm
      CODE := v_func : funcinst
    }) →
    wf_func (func.FUNC x (Map (fun (t_elem : valtype) => local.LOCAL t_elem) t_lst) instr_lst) →
    wf_frame ({
      LOCALS := val_lst ++ (Map (fun (t_elem : valtype) => Option.get! (default_ t_elem)) t_lst)
      MODULE := mm : frame
    }) →
    k = (List.length val_lst) →
    k = (List.length t_1_lst) →
    v_n = (List.length t_2_lst) →
    Step_read (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.CALL_ADDR a])) [admininstr.FRAME_ v_n f [admininstr.LABEL_ v_n [] (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst)]]
  | ref_func (z : state) (x : idx) :
    (proj_uN_0 x) < (List.length (fun_funcaddr z)) →
    Step_read (config.mk_config z [admininstr.REF_FUNC x]) [admininstr.REF_FUNC_ADDR ((fun_funcaddr z)[proj_uN_0 x]!)]
  | local_get (z : state) (x : idx) : Step_read (config.mk_config z [admininstr.LOCAL_GET x]) [admininstr_val (fun_local z x)]
  | global_get (z : state) (x : idx) : Step_read (config.mk_config z [admininstr.GLOBAL_GET x]) [admininstr_val ((fun_global z x).VALUE)]
  | table_get_trap (z : state) (i : num_) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) ≥ (List.length ((fun_table z x).REFS)) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.TABLE_GET x]) [admininstr.TRAP]
  | table_get_val (z : state) (i : num_) (x : idx) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    (proj_num__0 i) ≠ none →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.TABLE_GET x]) [admininstr_ref (((fun_table z x).REFS)[proj_uN_0 (Option.get! (proj_num__0 i))]!)]
  | table_size (z : state) (x : idx) (v_n : n) :
    (List.length ((fun_table z x).REFS)) = v_n →
    Step_read (config.mk_config z [admininstr.TABLE_SIZE x]) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))]
  | table_fill_trap (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z x).REFS)) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_FILL x]) [admininstr.TRAP]
  | table_fill_zero (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z x).REFS)) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_FILL x]) []
  | table_fill_succ (z : state) (i : num_) (v_val : val) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    v_n ≠ 0 →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z x).REFS)) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_FILL x]) [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.TABLE_SET x, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.TABLE_FILL x]
  | table_copy_trap (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_table z y).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) [admininstr.TRAP]
  | table_copy_zero (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) []
  | table_copy_le (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 j) ≠ none →
    (proj_num__0 i) ≠ none →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    (proj_uN_0 (Option.get! (proj_num__0 j))) ≤ (proj_uN_0 (Option.get! (proj_num__0 i))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.TABLE_GET y, admininstr.TABLE_SET x, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.TABLE_COPY x y]
  | table_copy_gt (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 j) ≠ none →
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 j))) > (proj_uN_0 (Option.get! (proj_num__0 i))) →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_table z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_COPY x y]) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) : Int) - (1 : Int))))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) : Int) - (1 : Int))))), admininstr.TABLE_GET y, admininstr.TABLE_SET x, admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.TABLE_COPY x y]
  | table_init_trap (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_elem z y).REFS))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_table z x).REFS))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_INIT x y]) [admininstr.TRAP]
  | table_init_zero (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_elem z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_INIT x y]) []
  | table_init_succ (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) (y : idx) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_elem z y).REFS)) →
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_elem z y).REFS))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_table z x).REFS))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_INIT x y]) [admininstr.CONST numtype.I32 j, admininstr_ref (((fun_elem z y).REFS)[proj_uN_0 (Option.get! (proj_num__0 i))]!), admininstr.TABLE_SET x, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.TABLE_INIT x y]
  | load_num_trap (z : state) (i : num_) (nt : numtype) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.LOAD nt none ao]) [admininstr.TRAP]
  | load_num_val (z : state) (i : num_) (nt : numtype) (ao : memarg) (c : num_) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    (nbytes_ nt c) = (List.take (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.LOAD nt none ao]) [admininstr.CONST nt c]
  | load_pack_trap (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_n : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.LOAD (numtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao]) [admininstr.TRAP]
  | load_pack_val (z : state) (i : num_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) (c : iN) :
    (size (valtype_Inn v_Inn)) ≠ none →
    (proj_num__0 i) ≠ none →
    (ibytes_ v_n c) = (List.take (rat_to_nat ((v_n : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.LOAD (numtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao]) [admininstr.CONST (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (extend__ v_n (Option.get! (size (valtype_Inn v_Inn))) v_sx c))]
  | vload_oob (z : state) (i : num_) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 none ao]) [admininstr.TRAP]
  | vload_val (z : state) (i : num_) (ao : memarg) (c : vec_) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    (vbytes_ vectype.V128 c) = (List.take (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 none ao]) [admininstr.VCONST vectype.V128 c]
  | vload_shape_oob (z : state) (i : num_) (v_M : M) (v_N : N) (v_sx : sx) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((v_M * v_N) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop.SHAPEX_ v_M v_N v_sx)) ao]) [admininstr.TRAP]
  | vload_shape_val (z : state) (i : num_) (v_M : M) (v_N : N) (v_sx : sx) (ao : memarg) (c : vec_) (j_lst : List iN) (v_Jnn : Jnn) :
    Forall (fun (k : Nat) => (proj_num__0 i) ≠ none) (List.range v_N) →
    Forall₂ (fun (k : Nat) (j_elem : iN) => (ibytes_ v_M j_elem) = (List.take (rat_to_nat ((v_M : Rat) / (8 : Rat))) (List.drop (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((k * v_M) : Rat) / (8 : Rat)))) ((fun_mem z (uN.mk_uN 0)).BYTES)))) (List.range v_N) j_lst →
    (jsize v_Jnn) = (v_M * 2) →
    c = (inv_lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) (Map (fun (j_elem : iN) => lane_.mk_lane__2 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j_elem)) j_lst)) →
    wf_uN 32 (uN.mk_uN 0) →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    Forall (fun (j_elem : iN) => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N))) (lane_.mk_lane__2 v_Jnn (extend__ v_M (jsize v_Jnn) v_sx j_elem))) j_lst →
    v_N = (List.length j_lst) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop.SHAPEX_ v_M v_N v_sx)) ao]) [admininstr.VCONST vectype.V128 c]
  | vload_splat_oob (z : state) (i : num_) (v_N : N) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_N : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop.SPLAT v_N)) ao]) [admininstr.TRAP]
  | vload_splat_val (z : state) (i : num_) (v_N : N) (ao : memarg) (c : vec_) (j : iN) (v_Jnn : Jnn) (v_M : M) :
    (proj_num__0 i) ≠ none →
    (ibytes_ v_N j) = (List.take (rat_to_nat ((v_N : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    v_N = (jsize v_Jnn) →
    (v_M : Rat) = ((128 : Rat) / (v_N : Rat)) →
    c = (inv_lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) (List.replicate v_M (lane_.mk_lane__2 v_Jnn (uN.mk_uN (proj_uN_0 j))))) →
    wf_uN 32 (uN.mk_uN 0) →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (lane_.mk_lane__2 v_Jnn (uN.mk_uN (proj_uN_0 j))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop.SPLAT v_N)) ao]) [admininstr.VCONST vectype.V128 c]
  | vload_zero_oob (z : state) (i : num_) (v_N : N) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_N : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop.ZERO v_N)) ao]) [admininstr.TRAP]
  | vload_zero_val (z : state) (i : num_) (v_N : N) (ao : memarg) (c : vec_) (j : iN) :
    (proj_num__0 i) ≠ none →
    (ibytes_ v_N j) = (List.take (rat_to_nat ((v_N : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    c = (extend__ v_N 128 sx.U j) →
    wf_uN v_N j →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VLOAD vectype.V128 (some (vloadop.ZERO v_N)) ao]) [admininstr.VCONST vectype.V128 c]
  | vload_lane_oob (z : state) (i : num_) (c_1 : vec_) (v_N : N) (ao : memarg) (j : laneidx) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_N : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c_1, admininstr.VLOAD_LANE vectype.V128 (sz.mk_sz v_N) ao j]) [admininstr.TRAP]
  | vload_lane_val (z : state) (i : num_) (c_1 : vec_) (v_N : N) (ao : memarg) (j : laneidx) (c : vec_) (k : iN) (v_Jnn : Jnn) (v_M : M) :
    (proj_num__0 i) ≠ none →
    (ibytes_ v_N k) = (List.take (rat_to_nat ((v_N : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    v_N = (jsize v_Jnn) →
    (v_M : Rat) = ((128 : Rat) / (v_N : Rat)) →
    c = (inv_lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) (List.modify (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c_1) (proj_uN_0 j) (fun elem_1 => lane_.mk_lane__2 v_Jnn (uN.mk_uN (proj_uN_0 k))))) →
    wf_uN 32 (uN.mk_uN 0) →
    wf_shape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (lane_.mk_lane__2 v_Jnn (uN.mk_uN (proj_uN_0 k))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c_1, admininstr.VLOAD_LANE vectype.V128 (sz.mk_sz v_N) ao j]) [admininstr.VCONST vectype.V128 c]
  | memory_size (z : state) (v_n : n) :
    ((v_n * 64) * Ki) = (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.MEMORY_SIZE]) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))]
  | memory_fill_trap (z : state) (i : num_) (v_val : val) (v_n : n) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_FILL]) [admininstr.TRAP]
  | memory_fill_zero (z : state) (i : num_) (v_val : val) (v_n : n) :
    (proj_num__0 i) ≠ none →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_FILL]) []
  | memory_fill_succ (z : state) (i : num_) (v_val : val) (v_n : n) :
    (proj_num__0 i) ≠ none →
    v_n ≠ 0 →
    ((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_FILL]) [admininstr.CONST numtype.I32 i, admininstr_val v_val, admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr_val v_val, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.MEMORY_FILL]
  | memory_copy_trap (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) [admininstr.TRAP]
  | memory_copy_zero (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) []
  | memory_copy_le (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 j) ≠ none →
    (proj_num__0 i) ≠ none →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    (proj_uN_0 (Option.get! (proj_num__0 j))) ≤ (proj_uN_0 (Option.get! (proj_num__0 i))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.LOAD numtype.I32 (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0, admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.MEMORY_COPY]
  | memory_copy_gt (z : state) (j : num_) (i : num_) (v_n : n) :
    (proj_num__0 j) ≠ none →
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 j))) > (proj_uN_0 (Option.get! (proj_num__0 i))) →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_COPY]) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) : Int) - (1 : Int))))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) : Int) - (1 : Int))))), admininstr.LOAD numtype.I32 (some (loadop_.mk_loadop__0 Inn.I32 (loadop_Inn.mk_loadop_Inn (sz.mk_sz 8) sx.U))) memarg0, admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0, admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.MEMORY_COPY]
  | memory_init_trap (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) > (List.length ((fun_data z x).BYTES))) ∨ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_INIT x]) [admininstr.TRAP]
  | memory_init_zero (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_data z x).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    v_n = 0 →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_INIT x]) []
  | memory_init_succ (z : state) (j : num_) (i : num_) (v_n : n) (x : idx) :
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_data z x).BYTES)) →
    (proj_num__0 i) ≠ none →
    (proj_num__0 j) ≠ none →
    v_n ≠ 0 →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + v_n) ≤ (List.length ((fun_data z x).BYTES))) ∧ (((proj_uN_0 (Option.get! (proj_num__0 j))) + v_n) ≤ (List.length ((fun_mem z (uN.mk_uN 0)).BYTES))) →
    Step_read (config.mk_config z [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 i, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_INIT x]) [admininstr.CONST numtype.I32 j, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (proj_byte_0 (((fun_data z x).BYTES)[proj_uN_0 (Option.get! (proj_num__0 i))]!)))), admininstr.STORE numtype.I32 (some (sz.mk_sz 8)) memarg0, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 j))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN ((proj_uN_0 (Option.get! (proj_num__0 i))) + 1))), admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (Int.toNat ((v_n : Int) - (1 : Int))))), admininstr.MEMORY_INIT x]


/- Well-Formedness Theorem at: ../specification/wasm-2.0/8-reduction.spectec:7.10-7.19 -/
theorem Step_read_is_wf (var_0 : config) (var_1 : List admininstr) :
  wf_config var_0 →
  Step_read var_0 var_1 →
  Forall (fun (var_1_elem : admininstr) => wf_admininstr var_1_elem) var_1 :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:5.1-5.109 -/
inductive Step : config → config → Prop where
  | pure (z : state) (admininstr_lst : List admininstr) (admininstr'_lst : List admininstr) :
    Step_pure admininstr_lst admininstr'_lst →
    Step (config.mk_config z admininstr_lst) (config.mk_config z admininstr'_lst)
  | read (z : state) (admininstr_lst : List admininstr) (admininstr'_lst : List admininstr) :
    Step_read (config.mk_config z admininstr_lst) admininstr'_lst →
    Step (config.mk_config z admininstr_lst) (config.mk_config z admininstr'_lst)
  | ctxt_label (z : state) (v_n : n) (instr_0_lst : List instr) (admininstr_lst : List admininstr) (z' : state) (admininstr'_lst : List admininstr) :
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z' admininstr'_lst) →
    Step (config.mk_config z [admininstr.LABEL_ v_n instr_0_lst admininstr_lst]) (config.mk_config z' [admininstr.LABEL_ v_n instr_0_lst admininstr'_lst])
  | ctxt_frame (s : store) (f : frame) (v_n : n) (f' : frame) (admininstr_lst : List admininstr) (s' : store) (f'' : frame) (admininstr'_lst : List admininstr) :
    Step (config.mk_config (state.mk_state s f') admininstr_lst) (config.mk_config (state.mk_state s' f'') admininstr'_lst) →
    wf_config (config.mk_config (state.mk_state s f') admininstr_lst) →
    wf_config (config.mk_config (state.mk_state s' f'') admininstr'_lst) →
    Step (config.mk_config (state.mk_state s f) [admininstr.FRAME_ v_n f' admininstr_lst]) (config.mk_config (state.mk_state s' f) [admininstr.FRAME_ v_n f'' admininstr'_lst])
  | ctxt_instrs (z : state) (val_lst : List val) (admininstr_lst : List admininstr) (admininstr_1_lst : List admininstr) (z' : state) (admininstr'_lst : List admininstr) :
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    (val_lst ≠ []) ∨ (admininstr_1_lst ≠ []) →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z' admininstr'_lst) →
    Step (config.mk_config z ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (admininstr_lst ++ admininstr_1_lst))) (config.mk_config z' ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ (admininstr'_lst ++ admininstr_1_lst)))
  | local_set (z : state) (v_val : val) (x : idx) : Step (config.mk_config z [admininstr_val v_val, admininstr.LOCAL_SET x]) (config.mk_config (with_local z x v_val) [])
  | global_set (z : state) (v_val : val) (x : idx) : Step (config.mk_config z [admininstr_val v_val, admininstr.GLOBAL_SET x]) (config.mk_config (with_global z x v_val) [])
  | table_set_trap (z : state) (i : num_) (v_ref : ref) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) ≥ (List.length ((fun_table z x).REFS)) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_ref v_ref, admininstr.TABLE_SET x]) (config.mk_config z [admininstr.TRAP])
  | table_set_val (z : state) (i : num_) (v_ref : ref) (x : idx) :
    (proj_num__0 i) ≠ none →
    (proj_uN_0 (Option.get! (proj_num__0 i))) < (List.length ((fun_table z x).REFS)) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr_ref v_ref, admininstr.TABLE_SET x]) (config.mk_config (with_table z x (proj_uN_0 (Option.get! (proj_num__0 i))) v_ref) [])
  | table_grow_succeed (z : state) (v_ref : ref) (v_n : n) (x : idx) (ti : tableinst) (var_0 : Option tableinst) :
    fun_growtable (fun_table z x) v_n v_ref var_0 →
    var_0 ≠ none →
    (Option.get! var_0) = ti →
    Step (config.mk_config z [admininstr_ref v_ref, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_GROW x]) (config.mk_config (with_tableinst z x ti) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (List.length ((fun_table z x).REFS))))])
  | table_grow_fail (z : state) (v_ref : ref) (v_n : n) (x : idx) (var_0 : Nat) :
    fun_inv_signed_ 32 (- (1 : Int)) var_0 →
    Step (config.mk_config z [admininstr_ref v_ref, admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.TABLE_GROW x]) (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN var_0))])
  | elem_drop (z : state) (x : idx) : Step (config.mk_config z [admininstr.ELEM_DROP x]) (config.mk_config (with_elem z x []) [])
  | store_num_trap (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST nt c, admininstr.STORE nt none ao]) (config.mk_config z [admininstr.TRAP])
  | store_num_val (z : state) (i : num_) (nt : numtype) (c : num_) (ao : memarg) (b_lst : List byte) :
    (proj_num__0 i) ≠ none →
    (size (valtype_numtype nt)) ≠ none →
    b_lst = (nbytes_ nt c) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST nt c, admininstr.STORE nt none ao]) (config.mk_config (with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat (((Option.get! (size (valtype_numtype nt))) : Rat) / (8 : Rat))) b_lst) [])
  | store_pack_trap (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_n : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST (numtype_Inn v_Inn) c, admininstr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) (config.mk_config z [admininstr.TRAP])
  | store_pack_val (z : state) (i : num_) (v_Inn : Inn) (c : num_) (v_n : n) (ao : memarg) (b_lst : List byte) :
    (proj_num__0 i) ≠ none →
    (size (valtype_Inn v_Inn)) ≠ none →
    (proj_num__0 c) ≠ none →
    b_lst = (ibytes_ v_n (wrap__ (Option.get! (size (valtype_Inn v_Inn))) v_n (Option.get! (proj_num__0 c)))) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.CONST (numtype_Inn v_Inn) c, admininstr.STORE (numtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) (config.mk_config (with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat ((v_n : Rat) / (8 : Rat))) b_lst) [])
  | vstore_oob (z : state) (i : num_) (c : vec_) (ao : memarg) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE vectype.V128 ao]) (config.mk_config z [admininstr.TRAP])
  | vstore_val (z : state) (i : num_) (c : vec_) (ao : memarg) (b_lst : List byte) :
    (proj_num__0 i) ≠ none →
    (size valtype.V128) ≠ none →
    b_lst = (vbytes_ vectype.V128 c) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE vectype.V128 ao]) (config.mk_config (with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat (((Option.get! (size valtype.V128)) : Rat) / (8 : Rat))) b_lst) [])
  | vstore_lane_oob (z : state) (i : num_) (c : vec_) (v_N : N) (ao : memarg) (j : laneidx) :
    (proj_num__0 i) ≠ none →
    (((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) + v_N) > (List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) ao j]) (config.mk_config z [admininstr.TRAP])
  | vstore_lane_val (z : state) (i : num_) (c : vec_) (v_N : N) (ao : memarg) (j : laneidx) (b_lst : List byte) (v_Jnn : Jnn) (v_M : M) :
    (proj_num__0 i) ≠ none →
    v_N = (jsize v_Jnn) →
    (v_M : Rat) = ((128 : Rat) / (v_N : Rat)) →
    (proj_lane__2 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!)) ≠ none →
    (proj_uN_0 j) < (List.length (lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)) →
    b_lst = (ibytes_ v_N (uN.mk_uN (proj_uN_0 (Option.get! (proj_lane__2 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!)))))) →
    wf_uN v_N (uN.mk_uN (proj_uN_0 (Option.get! (proj_lane__2 ((lanes_ (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) c)[proj_uN_0 j]!))))) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 i, admininstr.VCONST vectype.V128 c, admininstr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) ao j]) (config.mk_config (with_mem z (uN.mk_uN 0) ((proj_uN_0 (Option.get! (proj_num__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat ((v_N : Rat) / (8 : Rat))) b_lst) [])
  | memory_grow_succeed (z : state) (v_n : n) (mi : meminst) (var_0 : Option meminst) :
    fun_growmemory (fun_mem z (uN.mk_uN 0)) v_n var_0 →
    var_0 ≠ none →
    (Option.get! var_0) = mi →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_GROW]) (config.mk_config (with_meminst z (uN.mk_uN 0) mi) [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN (rat_to_nat (((List.length ((fun_mem z (uN.mk_uN 0)).BYTES)) : Rat) / ((64 * Ki) : Rat)))))])
  | memory_grow_fail (z : state) (v_n : n) (var_0 : Nat) :
    fun_inv_signed_ 32 (- (1 : Int)) var_0 →
    Step (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_GROW]) (config.mk_config z [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN var_0))])
  | data_drop (z : state) (x : idx) : Step (config.mk_config z [admininstr.DATA_DROP x]) (config.mk_config (with_data z x []) [])


/- Well-Formedness Theorem at: ../specification/wasm-2.0/8-reduction.spectec:5.10-5.14 -/
theorem Step_is_wf (var_0 : config) (var_1 : config) :
  wf_config var_0 →
  Step var_0 var_1 →
  wf_config var_1 :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:8.1-8.77 -/
inductive Steps : config → config → Prop where
  | refl (z : state) (admininstr_lst : List admininstr) :
    wf_config (config.mk_config z admininstr_lst) →
    Steps (config.mk_config z admininstr_lst) (config.mk_config z admininstr_lst)
  | trans (z : state) (admininstr_lst : List admininstr) (z'' : state) (admininstr''_lst : List admininstr) (z' : state) (admininstr'_lst : List admininstr) :
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    Steps (config.mk_config z' admininstr'_lst) (config.mk_config z'' admininstr''_lst) →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z'' admininstr''_lst) →
    wf_config (config.mk_config z' admininstr'_lst) →
    Steps (config.mk_config z admininstr_lst) (config.mk_config z'' admininstr''_lst)


/- Inductive Relations Definition at: ../specification/wasm-2.0/8-reduction.spectec:29.1-29.83 -/
inductive Eval_expr : state → expr → state → List val → Prop where
  | mk_Eval_expr (z : state) (instr_lst : List instr) (z' : state) (val_lst : List val) :
    Steps (config.mk_config z (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst)) (config.mk_config z' (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)) →
    wf_config (config.mk_config z (Map (fun (v_instr_elem : instr) => admininstr_instr v_instr_elem) instr_lst)) →
    wf_config (config.mk_config z' (Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst)) →
    Eval_expr z instr_lst z' val_lst


/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:5.6-5.12 -/
inductive fun_funcs : List externaddr → List funcaddr → Prop where
  | fun_funcs_case_0 : fun_funcs [] []
  | fun_funcs_case_1 (fa : Nat) (externaddr'_lst : List externaddr) (var_0 : List funcaddr) :
    fun_funcs externaddr'_lst var_0 →
    fun_funcs ([externaddr.FUNC fa] ++ externaddr'_lst) ([fa] ++ var_0)
  | fun_funcs_case_2 (v_externaddr : externaddr) (externaddr'_lst : List externaddr) (var_0 : List funcaddr) :
    fun_funcs externaddr'_lst var_0 →
    fun_funcs ([v_externaddr] ++ externaddr'_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:11.6-11.14 -/
inductive fun_globals : List externaddr → List globaladdr → Prop where
  | fun_globals_case_0 : fun_globals [] []
  | fun_globals_case_1 (ga : Nat) (externaddr'_lst : List externaddr) (var_0 : List globaladdr) :
    fun_globals externaddr'_lst var_0 →
    fun_globals ([externaddr.GLOBAL ga] ++ externaddr'_lst) ([ga] ++ var_0)
  | fun_globals_case_2 (v_externaddr : externaddr) (externaddr'_lst : List externaddr) (var_0 : List globaladdr) :
    fun_globals externaddr'_lst var_0 →
    fun_globals ([v_externaddr] ++ externaddr'_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:17.6-17.13 -/
inductive fun_tables : List externaddr → List tableaddr → Prop where
  | fun_tables_case_0 : fun_tables [] []
  | fun_tables_case_1 (ta : Nat) (externaddr'_lst : List externaddr) (var_0 : List tableaddr) :
    fun_tables externaddr'_lst var_0 →
    fun_tables ([externaddr.TABLE ta] ++ externaddr'_lst) ([ta] ++ var_0)
  | fun_tables_case_2 (v_externaddr : externaddr) (externaddr'_lst : List externaddr) (var_0 : List tableaddr) :
    fun_tables externaddr'_lst var_0 →
    fun_tables ([v_externaddr] ++ externaddr'_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:23.6-23.11 -/
inductive fun_mems : List externaddr → List memaddr → Prop where
  | fun_mems_case_0 : fun_mems [] []
  | fun_mems_case_1 (ma : Nat) (externaddr'_lst : List externaddr) (var_0 : List memaddr) :
    fun_mems externaddr'_lst var_0 →
    fun_mems ([externaddr.MEM ma] ++ externaddr'_lst) ([ma] ++ var_0)
  | fun_mems_case_2 (v_externaddr : externaddr) (externaddr'_lst : List externaddr) (var_0 : List memaddr) :
    fun_mems externaddr'_lst var_0 →
    fun_mems ([v_externaddr] ++ externaddr'_lst) var_0


/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 -/
inductive fun_allocfunc : store → moduleinst → func → store × funcaddr → Prop where
  | fun_allocfunc_case_0 (s : store) (v_moduleinst : moduleinst) (v_func : func) (fi : funcinst) (x : uN) (local_lst : List «local») (v_expr : List instr) :
    (proj_uN_0 x) < (List.length (v_moduleinst.TYPES)) →
    fi = ({
      TYPE := (v_moduleinst.TYPES)[proj_uN_0 x]!
      MODULE := v_moduleinst
      CODE := v_func : funcinst
    }) →
    v_func = (func.FUNC x local_lst v_expr) →
    wf_funcinst ({
      TYPE := (v_moduleinst.TYPES)[proj_uN_0 x]!
      MODULE := v_moduleinst
      CODE := v_func : funcinst
    }) →
    wf_func (func.FUNC x local_lst v_expr) →
    fun_allocfunc s v_moduleinst v_func (({
      s with
      FUNCS := (s.FUNCS) ++ [fi]
    }, List.length (s.FUNCS)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:36.6-36.16 -/
theorem allocfunc_is_wf (v_store : store) (v_moduleinst : moduleinst) (v_func : func) (ret_val : store × funcaddr) (var_0 : store × funcaddr) :
  fun_allocfunc v_store v_moduleinst v_func var_0 →
  wf_store v_store →
  wf_moduleinst v_moduleinst →
  wf_func v_func →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:41.6-41.17 -/
inductive fun_allocfuncs : store → moduleinst → List func → store × List funcaddr → Prop where
  | fun_allocfuncs_case_0 (s : store) (v_moduleinst : moduleinst) : fun_allocfuncs s v_moduleinst [] ((s, []))
  | fun_allocfuncs_case_1 (s : store) (v_moduleinst : moduleinst) (v_func : func) (func'_lst : List func) (fa : funcaddr) (s_1 : store) (s_2 : store) (fa'_lst : List funcaddr) (var_1 : store × List funcaddr) (var_0 : store × funcaddr) :
    fun_allocfuncs s_1 v_moduleinst func'_lst var_1 →
    fun_allocfunc s v_moduleinst v_func var_0 →
    ((s_1, fa)) = var_0 →
    ((s_2, fa'_lst)) = var_1 →
    fun_allocfuncs s v_moduleinst ([v_func] ++ func'_lst) ((s_2, [fa] ++ fa'_lst))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:41.6-41.17 -/
theorem allocfuncs_is_wf (v_store : store) (v_moduleinst : moduleinst) (var_0_lst : List func) (ret_val : store × List funcaddr) (var_0 : store × List funcaddr) :
  fun_allocfuncs v_store v_moduleinst var_0_lst var_0 →
  wf_store v_store →
  wf_moduleinst v_moduleinst →
  Forall (fun (var_0_elem : func) => wf_func var_0_elem) var_0_lst →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 -/
inductive fun_allocglobal : store → globaltype → val → store × globaladdr → Prop where
  | fun_allocglobal_case_0 (s : store) (v_globaltype : globaltype) (v_val : val) (gi : globalinst) :
    gi = ({
      TYPE := v_globaltype
      VALUE := v_val : globalinst
    }) →
    wf_globalinst ({
      TYPE := v_globaltype
      VALUE := v_val : globalinst
    }) →
    fun_allocglobal s v_globaltype v_val (({
      s with
      GLOBALS := (s.GLOBALS) ++ [gi]
    }, List.length (s.GLOBALS)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:47.6-47.18 -/
theorem allocglobal_is_wf (v_store : store) (v_globaltype : globaltype) (v_val : val) (ret_val : store × globaladdr) (var_0 : store × globaladdr) :
  fun_allocglobal v_store v_globaltype v_val var_0 →
  wf_store v_store →
  wf_val v_val →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:51.6-51.19 -/
inductive fun_allocglobals : store → List globaltype → List val → store × List globaladdr → Prop where
  | fun_allocglobals_case_0 (s : store) : fun_allocglobals s [] [] ((s, []))
  | fun_allocglobals_case_1 (s : store) (v_globaltype : globaltype) (globaltype'_lst : List globaltype) (v_val : val) (val'_lst : List val) (ga : globaladdr) (s_1 : store) (s_2 : store) (ga'_lst : List globaladdr) (var_1 : store × List globaladdr) (var_0 : store × globaladdr) :
    fun_allocglobals s_1 globaltype'_lst val'_lst var_1 →
    fun_allocglobal s v_globaltype v_val var_0 →
    ((s_1, ga)) = var_0 →
    ((s_2, ga'_lst)) = var_1 →
    fun_allocglobals s ([v_globaltype] ++ globaltype'_lst) ([v_val] ++ val'_lst) ((s_2, [ga] ++ ga'_lst))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:51.6-51.19 -/
theorem allocglobals_is_wf (v_store : store) (var_0_lst : List globaltype) (var_1_lst : List val) (ret_val : store × List globaladdr) (var_0 : store × List globaladdr) :
  fun_allocglobals v_store var_0_lst var_1_lst var_0 →
  wf_store v_store →
  Forall (fun (var_1_elem : val) => wf_val var_1_elem) var_1_lst →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 -/
inductive fun_alloctable : store → tabletype → store × tableaddr → Prop where
  | fun_alloctable_case_0 (s : store) (i : uN) (j_opt : Option u32) (rt : reftype) (ti : tableinst) :
    ti = ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits i j_opt) rt
      REFS := List.replicate (proj_uN_0 i) (ref.REF_NULL rt) : tableinst
    }) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits i j_opt) rt
      REFS := List.replicate (proj_uN_0 i) (ref.REF_NULL rt) : tableinst
    }) →
    fun_alloctable s (tabletype.mk_tabletype (limits.mk_limits i j_opt) rt) (({
      s with
      TABLES := (s.TABLES) ++ [ti]
    }, List.length (s.TABLES)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:57.6-57.17 -/
theorem alloctable_is_wf (v_store : store) (v_tabletype : tabletype) (ret_val : store × tableaddr) (var_0 : store × tableaddr) :
  fun_alloctable v_store v_tabletype var_0 →
  wf_store v_store →
  wf_tabletype v_tabletype →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:61.6-61.18 -/
inductive fun_alloctables : store → List tabletype → store × List tableaddr → Prop where
  | fun_alloctables_case_0 (s : store) : fun_alloctables s [] ((s, []))
  | fun_alloctables_case_1 (s : store) (v_tabletype : tabletype) (tabletype'_lst : List tabletype) (ta : tableaddr) (s_1 : store) (s_2 : store) (ta'_lst : List tableaddr) (var_1 : store × List tableaddr) (var_0 : store × tableaddr) :
    fun_alloctables s_1 tabletype'_lst var_1 →
    fun_alloctable s v_tabletype var_0 →
    ((s_1, ta)) = var_0 →
    ((s_2, ta'_lst)) = var_1 →
    fun_alloctables s ([v_tabletype] ++ tabletype'_lst) ((s_2, [ta] ++ ta'_lst))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:61.6-61.18 -/
theorem alloctables_is_wf (v_store : store) (var_0_lst : List tabletype) (ret_val : store × List tableaddr) (var_0 : store × List tableaddr) :
  fun_alloctables v_store var_0_lst var_0 →
  wf_store v_store →
  Forall (fun (var_0_elem : tabletype) => wf_tabletype var_0_elem) var_0_lst →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 -/
inductive fun_allocmem : store → memtype → store × memaddr → Prop where
  | fun_allocmem_case_0 (s : store) (i : uN) (j_opt : Option u32) (mi : meminst) :
    mi = ({
      TYPE := memtype.PAGE (limits.mk_limits i j_opt)
      BYTES := List.replicate ((proj_uN_0 i) * (64 * Ki)) (byte.mk_byte 0) : meminst
    }) →
    wf_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits i j_opt)
      BYTES := List.replicate ((proj_uN_0 i) * (64 * Ki)) (byte.mk_byte 0) : meminst
    }) →
    fun_allocmem s (memtype.PAGE (limits.mk_limits i j_opt)) (({
      s with
      MEMS := (s.MEMS) ++ [mi]
    }, List.length (s.MEMS)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:67.6-67.15 -/
theorem allocmem_is_wf (v_store : store) (v_memtype : memtype) (ret_val : store × memaddr) (var_0 : store × memaddr) :
  fun_allocmem v_store v_memtype var_0 →
  wf_store v_store →
  wf_memtype v_memtype →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:71.6-71.16 -/
inductive fun_allocmems : store → List memtype → store × List memaddr → Prop where
  | fun_allocmems_case_0 (s : store) : fun_allocmems s [] ((s, []))
  | fun_allocmems_case_1 (s : store) (v_memtype : memtype) (memtype'_lst : List memtype) (ma : memaddr) (s_1 : store) (s_2 : store) (ma'_lst : List memaddr) (var_1 : store × List memaddr) (var_0 : store × memaddr) :
    fun_allocmems s_1 memtype'_lst var_1 →
    fun_allocmem s v_memtype var_0 →
    ((s_1, ma)) = var_0 →
    ((s_2, ma'_lst)) = var_1 →
    fun_allocmems s ([v_memtype] ++ memtype'_lst) ((s_2, [ma] ++ ma'_lst))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:71.6-71.16 -/
theorem allocmems_is_wf (v_store : store) (var_0_lst : List memtype) (ret_val : store × List memaddr) (var_0 : store × List memaddr) :
  fun_allocmems v_store var_0_lst var_0 →
  wf_store v_store →
  Forall (fun (var_0_elem : memtype) => wf_memtype var_0_elem) var_0_lst →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 -/
inductive fun_allocelem : store → reftype → List ref → store × elemaddr → Prop where
  | fun_allocelem_case_0 (s : store) (rt : reftype) (ref_lst : List ref) (ei : eleminst) :
    ei = ({
      TYPE := rt
      REFS := ref_lst : eleminst
    }) →
    fun_allocelem s rt ref_lst (({
      s with
      ELEMS := (s.ELEMS) ++ [ei]
    }, List.length (s.ELEMS)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:77.6-77.16 -/
theorem allocelem_is_wf (v_store : store) (v_reftype : reftype) (var_0_lst : List ref) (ret_val : store × elemaddr) (var_0 : store × elemaddr) :
  fun_allocelem v_store v_reftype var_0_lst var_0 →
  wf_store v_store →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:81.6-81.17 -/
inductive fun_allocelems : store → List reftype → List (List ref) → store × List elemaddr → Prop where
  | fun_allocelems_case_0 (s : store) : fun_allocelems s [] [] ((s, []))
  | fun_allocelems_case_1 (s : store) (rt : reftype) (rt'_lst : List reftype) (ref_lst : List ref) (ref'_lst_lst : List (List ref)) (ea : elemaddr) (s_1 : store) (s_2 : store) (ea'_lst : List elemaddr) (var_1 : store × List elemaddr) (var_0 : store × elemaddr) :
    fun_allocelems s_1 rt'_lst ref'_lst_lst var_1 →
    fun_allocelem s rt ref_lst var_0 →
    ((s_1, ea)) = var_0 →
    ((s_2, ea'_lst)) = var_1 →
    fun_allocelems s ([rt] ++ rt'_lst) ([ref_lst] ++ ref'_lst_lst) ((s_2, [ea] ++ ea'_lst))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:81.6-81.17 -/
theorem allocelems_is_wf (v_store : store) (var_0_lst : List reftype) (var_1_lst_lst : List (List ref)) (ret_val : store × List elemaddr) (var_0 : store × List elemaddr) :
  fun_allocelems v_store var_0_lst var_1_lst_lst var_0 →
  wf_store v_store →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 -/
inductive fun_allocdata : store → List byte → store × dataaddr → Prop where
  | fun_allocdata_case_0 (s : store) (byte_lst : List byte) (di : datainst) :
    di = ({
      BYTES := byte_lst : datainst
    }) →
    wf_datainst ({
      BYTES := byte_lst : datainst
    }) →
    fun_allocdata s byte_lst (({
      s with
      DATAS := (s.DATAS) ++ [di]
    }, List.length (s.DATAS)))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:87.6-87.16 -/
theorem allocdata_is_wf (v_store : store) (var_0_lst : List byte) (ret_val : store × dataaddr) (var_0 : store × dataaddr) :
  fun_allocdata v_store var_0_lst var_0 →
  wf_store v_store →
  Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:91.6-91.17 -/
inductive fun_allocdatas : store → List (List byte) → store × List dataaddr → Prop where
  | fun_allocdatas_case_0 (s : store) : fun_allocdatas s [] ((s, []))
  | fun_allocdatas_case_1 (s : store) (byte_lst : List byte) (byte'_lst_lst : List (List byte)) (da : dataaddr) (s_1 : store) (s_2 : store) (da'_lst : List dataaddr) (var_1 : store × List dataaddr) (var_0 : store × dataaddr) :
    fun_allocdatas s_1 byte'_lst_lst var_1 →
    fun_allocdata s byte_lst var_0 →
    ((s_1, da)) = var_0 →
    ((s_2, da'_lst)) = var_1 →
    fun_allocdatas s ([byte_lst] ++ byte'_lst_lst) ((s_2, [da] ++ da'_lst))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:91.6-91.17 -/
theorem allocdatas_is_wf (v_store : store) (var_0_lst_lst : List (List byte)) (ret_val : store × List dataaddr) (var_0 : store × List dataaddr) :
  fun_allocdatas v_store var_0_lst_lst var_0 →
  wf_store v_store →
  Forall (fun (var_0_lst_elem : List byte) => Forall (fun (var_0_elem : byte) => wf_byte var_0_elem) var_0_lst_elem) var_0_lst_lst →
  ret_val = var_0 →
  wf_store (ret_val.1) :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:100.1-100.83 -/
def instexport (var_0_lst : List funcaddr) (var_1_lst : List globaladdr) (var_2_lst : List tableaddr) (var_3_lst : List memaddr) (v_export : «export») : exportinst :=
  match v_export with
  | export.EXPORT v_name (externidx.FUNC x) => {
    NAME := v_name
    ADDR := externaddr.FUNC ((var_0_lst)[proj_uN_0 x]!) : exportinst
  }
  | export.EXPORT v_name (externidx.GLOBAL x) => {
    NAME := v_name
    ADDR := externaddr.GLOBAL ((var_1_lst)[proj_uN_0 x]!) : exportinst
  }
  | export.EXPORT v_name (externidx.TABLE x) => {
    NAME := v_name
    ADDR := externaddr.TABLE ((var_2_lst)[proj_uN_0 x]!) : exportinst
  }
  | export.EXPORT v_name (externidx.MEM x) => {
    NAME := v_name
    ADDR := externaddr.MEM ((var_3_lst)[proj_uN_0 x]!) : exportinst
  }

/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:100.6-100.17 -/
theorem instexport_is_wf (var_0_lst : List funcaddr) (var_1_lst : List globaladdr) (var_2_lst : List tableaddr) (var_3_lst : List memaddr) (v_export : «export») (ret_val : exportinst) :
  wf_export v_export →
  ret_val = (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export) →
  wf_exportinst ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 -/
inductive fun_allocmodule : store → module → List externaddr → List val → List (List ref) → store × moduleinst → Prop where
  | fun_allocmodule_case_0 (s : store) (v_module : module) (externaddr_lst : List externaddr) (val_lst : List val) (ref_lst_lst : List (List ref)) (s_6 : store) (v_moduleinst : moduleinst) (ft_lst : List functype) (import_lst : List «import») (n_func : Nat) (func_lst : List func) (n_global : Nat) (expr_1_lst : List expr) (globaltype_lst : List globaltype) (n_table : Nat) (tabletype_lst : List tabletype) (n_mem : Nat) (memtype_lst : List memtype) (n_elem : Nat) (elemmode_lst : List elemmode) (expr_2_lst_lst : List (List expr)) (rt_lst : List reftype) (n_data : Nat) (byte_lst_lst : List (List byte)) (datamode_lst : List datamode) (start_opt : Option start) (export_lst : List «export») (s_1 : store) (s_2 : store) (s_3 : store) (s_4 : store) (s_5 : store) (fa_ex_lst : List funcaddr) (ga_ex_lst : List globaladdr) (ta_ex_lst : List tableaddr) (ma_ex_lst : List memaddr) (fa_lst : List funcaddr) (ga_lst : List globaladdr) (ta_lst : List tableaddr) (ma_lst : List memaddr) (ea_lst : List elemaddr) (da_lst : List dataaddr) (xi_lst : List exportinst) (var_9 : store × List dataaddr) (var_8 : store × List elemaddr) (var_7 : store × List memaddr) (var_6 : store × List tableaddr) (var_5 : store × List globaladdr) (var_4 : store × List funcaddr) (var_3 : List memaddr) (var_2 : List tableaddr) (var_1 : List globaladdr) (var_0 : List funcaddr) :
    fun_allocdatas s_5 byte_lst_lst var_9 →
    fun_allocelems s_4 rt_lst ref_lst_lst var_8 →
    fun_allocmems s_3 memtype_lst var_7 →
    fun_alloctables s_2 tabletype_lst var_6 →
    fun_allocglobals s_1 globaltype_lst val_lst var_5 →
    fun_allocfuncs s v_moduleinst func_lst var_4 →
    fun_mems externaddr_lst var_3 →
    fun_tables externaddr_lst var_2 →
    fun_globals externaddr_lst var_1 →
    fun_funcs externaddr_lst var_0 →
    v_module = (module.MODULE (Map (fun (ft_1_elem : functype) => type.TYPE ft_1_elem) ft_lst) import_lst func_lst (Map₂ (fun (expr_1_1_elem : expr) (globaltype_195_elem : globaltype) => global.GLOBAL globaltype_195_elem expr_1_1_elem) expr_1_lst globaltype_lst) (Map (fun (tabletype_241_elem : tabletype) => table.TABLE tabletype_241_elem) tabletype_lst) (Map (fun (memtype_293_elem : memtype) => mem.MEMORY memtype_293_elem) memtype_lst) (Map₃ (fun (elemmode_397_elem : elemmode) (expr_2_lst_1_elem : List expr) (rt_1_elem : reftype) => elem.ELEM rt_1_elem expr_2_lst_1_elem elemmode_397_elem) elemmode_lst expr_2_lst_lst rt_lst) (Map₂ (fun (byte_lst_419_elem : List byte) (datamode_419_elem : datamode) => data.DATA byte_lst_419_elem datamode_419_elem) byte_lst_lst datamode_lst) start_opt export_lst) →
    fa_ex_lst = var_0 →
    ga_ex_lst = var_1 →
    ta_ex_lst = var_2 →
    ma_ex_lst = var_3 →
    fa_lst = (List.range n_func |>.map (fun (i_func_1 : Nat) => (List.length (s.FUNCS)) + i_func_1)) →
    ga_lst = (List.range n_global |>.map (fun (i_global_1 : Nat) => (List.length (s.GLOBALS)) + i_global_1)) →
    ta_lst = (List.range n_table |>.map (fun (i_table_1 : Nat) => (List.length (s.TABLES)) + i_table_1)) →
    ma_lst = (List.range n_mem |>.map (fun (i_mem_1 : Nat) => (List.length (s.MEMS)) + i_mem_1)) →
    ea_lst = (List.range n_elem |>.map (fun (i_elem_1 : Nat) => (List.length (s.ELEMS)) + i_elem_1)) →
    da_lst = (List.range n_data |>.map (fun (i_data_1 : Nat) => (List.length (s.DATAS)) + i_data_1)) →
    xi_lst = (Map (fun (export_2_elem : «export») => instexport (fa_ex_lst ++ fa_lst) (ga_ex_lst ++ ga_lst) (ta_ex_lst ++ ta_lst) (ma_ex_lst ++ ma_lst) export_2_elem) export_lst) →
    v_moduleinst = ({
      TYPES := ft_lst
      FUNCS := fa_ex_lst ++ fa_lst
      GLOBALS := ga_ex_lst ++ ga_lst
      TABLES := ta_ex_lst ++ ta_lst
      MEMS := ma_ex_lst ++ ma_lst
      ELEMS := ea_lst
      DATAS := da_lst
      EXPORTS := xi_lst : moduleinst
    }) →
    ((s_1, fa_lst)) = var_4 →
    ((s_2, ga_lst)) = var_5 →
    ((s_3, ta_lst)) = var_6 →
    ((s_4, ma_lst)) = var_7 →
    ((s_5, ea_lst)) = var_8 →
    ((s_6, da_lst)) = var_9 →
    wf_store s_1 →
    wf_store s_2 →
    wf_store s_3 →
    wf_store s_4 →
    wf_store s_5 →
    wf_module (module.MODULE (Map (fun (ft_3_elem : functype) => type.TYPE ft_3_elem) ft_lst) import_lst func_lst (Map₂ (fun (expr_1_2_elem : expr) (globaltype_198_elem : globaltype) => global.GLOBAL globaltype_198_elem expr_1_2_elem) expr_1_lst globaltype_lst) (Map (fun (tabletype_244_elem : tabletype) => table.TABLE tabletype_244_elem) tabletype_lst) (Map (fun (memtype_296_elem : memtype) => mem.MEMORY memtype_296_elem) memtype_lst) (Map₃ (fun (elemmode_399_elem : elemmode) (expr_2_lst_2_elem : List expr) (rt_3_elem : reftype) => elem.ELEM rt_3_elem expr_2_lst_2_elem elemmode_399_elem) elemmode_lst expr_2_lst_lst rt_lst) (Map₂ (fun (byte_lst_422_elem : List byte) (datamode_421_elem : datamode) => data.DATA byte_lst_422_elem datamode_421_elem) byte_lst_lst datamode_lst) start_opt export_lst) →
    wf_moduleinst ({
      TYPES := ft_lst
      FUNCS := fa_ex_lst ++ fa_lst
      GLOBALS := ga_ex_lst ++ ga_lst
      TABLES := ta_ex_lst ++ ta_lst
      MEMS := ma_ex_lst ++ ma_lst
      ELEMS := ea_lst
      DATAS := da_lst
      EXPORTS := xi_lst : moduleinst
    }) →
    fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst ((s_6, v_moduleinst))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:107.6-107.18 -/
theorem allocmodule_is_wf (v_store : store) (v_module : module) (var_0_lst : List externaddr) (var_1_lst : List val) (var_2_lst_lst : List (List ref)) (ret_val : store × moduleinst) (var_0 : store × moduleinst) :
  fun_allocmodule v_store v_module var_0_lst var_1_lst var_2_lst_lst var_0 →
  wf_store v_store →
  wf_module v_module →
  Forall (fun (var_1_elem : val) => wf_val var_1_elem) var_1_lst →
  ret_val = var_0 →
  wf_store (ret_val.1) →
  wf_moduleinst (ret_val.2) :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:154.1-154.33 -/
def runelem (v_elem : elem) (v_idx : idx) : List instr :=
  match v_elem with
  | elem.ELEM v_reftype expr_lst elemmode.PASSIVE => []
  | elem.ELEM v_reftype expr_lst elemmode.DECLARE => [instr.ELEM_DROP v_idx]
  | elem.ELEM v_reftype expr_lst (elemmode.ACTIVE x instr_lst) => let v_n := List.length expr_lst
  instr_lst ++ [instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)), instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), instr.TABLE_INIT x v_idx, instr.ELEM_DROP v_idx]

/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:154.6-154.14 -/
theorem runelem_is_wf (v_elem : elem) (v_idx : idx) (ret_val_lst : List instr) :
  wf_elem v_elem →
  wf_uN 32 v_idx →
  ret_val_lst = (runelem v_elem v_idx) →
  Forall (fun (ret_val_elem : instr) => wf_instr ret_val_elem) ret_val_lst :=
  sorry

/- Auxiliary Definition at: ../specification/wasm-2.0/9-module.spectec:161.1-161.47 -/
def rundata (v_data : data) (v_idx : idx) : Option (List instr) :=
  match v_data with
  | data.DATA byte_lst datamode.PASSIVE => some []
  | data.DATA byte_lst (datamode.ACTIVE (uN.mk_uN 0) instr_lst) => let v_n := List.length byte_lst
  some (instr_lst ++ [instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)), instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)), instr.MEMORY_INIT v_idx, instr.DATA_DROP v_idx])
  | _ => none

/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:161.6-161.14 -/
theorem rundata_is_wf (v_data : data) (v_idx : idx) (ret_val_lst : List instr) :
  wf_data v_data →
  wf_uN 32 v_idx →
  (rundata v_data v_idx) ≠ none →
  ret_val_lst = (Option.get! (rundata v_data v_idx)) →
  Forall (fun (ret_val_elem : instr) => wf_instr ret_val_elem) ret_val_lst :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 -/
inductive fun_instantiate : store → module → List externaddr → config → Prop where
  | fun_instantiate_case_0 (s : store) (v_module : module) (externaddr_lst : List externaddr) (f : frame) (x_opt : Option idx) (functype_lst : List functype) (expr_G_lst : List expr) (globaltype_lst : List globaltype) (elemmode_lst : List elemmode) (expr_E_lst_lst : List (List expr)) (reftype_lst : List reftype) (moduleinst_init : moduleinst) (f_init : frame) (val_lst : List val) (ref_lst_lst : List (List ref)) (i : Nat) (j : Nat) (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») (n_F : n) (n_E : n) (n_D : n) (z : state) (s' : store) (v_moduleinst : moduleinst) (instr_E_lst : List instr) (instr_D_lst : List instr) (var_4 : List globaladdr) (var_3 : List funcaddr) (var_2 : store × moduleinst) (var_1 : List globaladdr) (var_0 : List funcaddr) :
    fun_globals externaddr_lst var_4 →
    fun_funcs externaddr_lst var_3 →
    fun_allocmodule s v_module externaddr_lst val_lst ref_lst_lst var_2 →
    fun_globals externaddr_lst var_1 →
    fun_funcs externaddr_lst var_0 →
    (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) = v_module →
    type_lst = (Map (fun (functype_49_elem : functype) => type.TYPE functype_49_elem) functype_lst) →
    global_lst = (Map₂ (fun (expr_G_1_elem : expr) (globaltype_200_elem : globaltype) => global.GLOBAL globaltype_200_elem expr_G_1_elem) expr_G_lst globaltype_lst) →
    elem_lst = (Map₃ (fun (elemmode_404_elem : elemmode) (expr_E_lst_1_elem : List expr) (reftype_611_elem : reftype) => elem.ELEM reftype_611_elem expr_E_lst_1_elem elemmode_404_elem) elemmode_lst expr_E_lst_lst reftype_lst) →
    start_opt = (OMap (fun (x_1_elem : idx) => start.START x_1_elem) x_opt) →
    n_F = (List.length func_lst) →
    n_E = (List.length elem_lst) →
    n_D = (List.length data_lst) →
    moduleinst_init = ({
      TYPES := functype_lst
      FUNCS := var_0 ++ (List.range n_F |>.map (fun (i_F_1 : Nat) => (List.length (s.FUNCS)) + i_F_1))
      GLOBALS := var_1
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      EXPORTS := [] : moduleinst
    }) →
    f_init = ({
      LOCALS := []
      MODULE := moduleinst_init : frame
    }) →
    z = (state.mk_state s f_init) →
    (List.length expr_G_lst) = (List.length val_lst) →
    Forall₂ (fun (expr_G_2_elem : expr) (val_3_elem : val) => Eval_expr z expr_G_2_elem z [val_3_elem]) expr_G_lst val_lst →
    (List.length expr_E_lst_lst) = (List.length ref_lst_lst) →
    Forall₂ (fun (expr_E_lst_2_elem : List expr) (ref_lst_3_elem : List ref) => (List.length expr_E_lst_2_elem) = (List.length ref_lst_3_elem)) expr_E_lst_lst ref_lst_lst →
    Forall₂ (fun (expr_E_lst_2_elem : List expr) (ref_lst_3_elem : List ref) => Forall₂ (fun (expr_E_2_elem : expr) (ref_7_elem : ref) => Eval_expr z expr_E_2_elem z [val_ref ref_7_elem]) expr_E_lst_2_elem ref_lst_3_elem) expr_E_lst_lst ref_lst_lst →
    ((s', v_moduleinst)) = var_2 →
    f = ({
      LOCALS := []
      MODULE := v_moduleinst : frame
    }) →
    Forall (fun (i_71346 : Nat) => i_71346 < (List.length elem_lst)) (List.range n_E) →
    instr_E_lst = (concat_ instr (List.range n_E |>.map (fun (i_71346 : Nat) => runelem ((elem_lst)[i_71346]!) (uN.mk_uN i_71346)))) →
    Forall (fun (j_17 : Nat) => (rundata ((data_lst)[j_17]!) (uN.mk_uN j_17)) ≠ none) (List.range n_D) →
    Forall (fun (j_17 : Nat) => j_17 < (List.length data_lst)) (List.range n_D) →
    instr_D_lst = (concat_ instr (List.range n_D |>.map (fun (j_17 : Nat) => Option.get! (rundata ((data_lst)[j_17]!) (uN.mk_uN j_17))))) →
    Forall (fun (val_5_elem : val) => wf_val val_5_elem) val_lst →
    wf_module (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) →
    (List.length expr_G_lst) = (List.length globaltype_lst) →
    Forall₂ (fun (expr_G_3_elem : expr) (globaltype_202_elem : globaltype) => wf_global (global.GLOBAL globaltype_202_elem expr_G_3_elem)) expr_G_lst globaltype_lst →
    (List.length elemmode_lst) = (List.length expr_E_lst_lst) →
    (List.length elemmode_lst) = (List.length reftype_lst) →
    Forall₃ (fun (elemmode_406_elem : elemmode) (expr_E_lst_3_elem : List expr) (reftype_613_elem : reftype) => wf_elem (elem.ELEM reftype_613_elem expr_E_lst_3_elem elemmode_406_elem)) elemmode_lst expr_E_lst_lst reftype_lst →
    Forall (fun (x_2_elem : idx) => wf_start (start.START x_2_elem)) (Option.toList x_opt) →
    wf_moduleinst ({
      TYPES := functype_lst
      FUNCS := var_3 ++ (List.range n_F |>.map (fun (i_F_2 : Nat) => (List.length (s.FUNCS)) + i_F_2))
      GLOBALS := var_4
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      EXPORTS := [] : moduleinst
    }) →
    wf_frame ({
      LOCALS := []
      MODULE := moduleinst_init : frame
    }) →
    wf_state (state.mk_state s f_init) →
    wf_frame ({
      LOCALS := []
      MODULE := v_moduleinst : frame
    }) →
    Forall (fun (i_71349 : Nat) => wf_uN 32 (uN.mk_uN i_71349)) (List.range n_E) →
    Forall (fun (j_18 : Nat) => wf_uN 32 (uN.mk_uN j_18)) (List.range n_D) →
    fun_instantiate s v_module externaddr_lst (config.mk_config (state.mk_state s' f) ((Map (fun (instr_E_elem : instr) => admininstr_instr instr_E_elem) instr_E_lst) ++ ((Map (fun (instr_D_elem : instr) => admininstr_instr instr_D_elem) instr_D_lst) ++ (Option.toList (OMap (fun (x_elem : idx) => admininstr.CALL x_elem) x_opt)))))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:167.6-167.18 -/
theorem instantiate_is_wf (v_store : store) (v_module : module) (var_0_lst : List externaddr) (ret_val : config) (var_0 : config) :
  fun_instantiate v_store v_module var_0_lst var_0 →
  wf_store v_store →
  wf_module v_module →
  ret_val = var_0 →
  wf_config ret_val :=
  sorry

/- Inductive Relations Definition at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 -/
inductive fun_invoke : store → funcaddr → List val → config → Prop where
  | fun_invoke_case_0 (s : store) (fa : Nat) (v_n : Nat) (val_lst : List val) (f : frame) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    f = ({
      LOCALS := []
      MODULE := {
        TYPES := []
        FUNCS := []
        GLOBALS := []
        TABLES := []
        MEMS := []
        ELEMS := []
        DATAS := []
        EXPORTS := [] : moduleinst
      } : frame
    }) →
    fa < (List.length (fun_funcinst (state.mk_state s f))) →
    (((fun_funcinst (state.mk_state s f))[fa]!).TYPE) = (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_frame ({
      LOCALS := []
      MODULE := {
        TYPES := []
        FUNCS := []
        GLOBALS := []
        TABLES := []
        MEMS := []
        ELEMS := []
        DATAS := []
        EXPORTS := [] : moduleinst
      } : frame
    }) →
    wf_state (state.mk_state s f) →
    v_n = (List.length val_lst) →
    fun_invoke s fa val_lst (config.mk_config (state.mk_state s f) ((Map (fun (v_val_elem : val) => admininstr_val v_val_elem) val_lst) ++ [admininstr.CALL_ADDR fa]))


/- Well-Formedness Theorem at: ../specification/wasm-2.0/9-module.spectec:196.6-196.13 -/
theorem invoke_is_wf (v_store : store) (v_funcaddr : funcaddr) (var_0_lst : List val) (ret_val : config) (var_0 : config) :
  fun_invoke v_store v_funcaddr var_0_lst var_0 →
  wf_store v_store →
  Forall (fun (var_0_elem : val) => wf_val var_0_elem) var_0_lst →
  ret_val = var_0 →
  wf_config ret_val :=
  sorry

/- Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:849.1-849.43 -/
abbrev startopt : Type := List start

/- Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:884.1-884.29 -/
abbrev code : Type := List «local» × expr

/- Type Alias Definition at: ../specification/wasm-2.0/A-binary.spectec:915.1-915.33 -/
abbrev nopt : Type := List u32

/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:3.1-3.61 -/
inductive Context_ok : context → Prop where
  | mk_Context_ok (C : context) (ft_lst : List functype) (ft_2_lst : List functype) (gt_lst : List globaltype) (tt_lst : List tabletype) (mt_lst : List memtype) (et_lst : List elemtype) (ok_lst : List datatype) (lct_lst : List valtype) (rt_lst : List reftype) (rt'_opt : Option reftype) :
    C = ({
      TYPES := ft_lst
      FUNCS := ft_2_lst
      GLOBALS := gt_lst
      TABLES := tt_lst
      MEMS := mt_lst
      ELEMS := et_lst
      DATAS := ok_lst
      LOCALS := lct_lst
      LABELS := [.mk_list (Map (fun (rt_elem : reftype) => valtype_reftype rt_elem) rt_lst)]
      RETURN := some (.mk_list (Option.toList (OMap (fun (rt'_elem : reftype) => valtype_reftype rt'_elem) rt'_opt))) : context
    }) →
    Forall (fun (ft_elem : functype) => Functype_ok ft_elem) ft_lst →
    Forall (fun (gt_elem : globaltype) => Globaltype_ok gt_elem) gt_lst →
    Forall (fun (mt_elem : memtype) => Memtype_ok mt_elem) mt_lst →
    Forall (fun (tt_elem : tabletype) => Tabletype_ok tt_elem) tt_lst →
    Forall (fun (ft_2_elem : functype) => Functype_ok ft_2_elem) ft_2_lst →
    wf_context C →
    wf_context ({
      TYPES := ft_lst
      FUNCS := ft_2_lst
      GLOBALS := gt_lst
      TABLES := tt_lst
      MEMS := mt_lst
      ELEMS := et_lst
      DATAS := ok_lst
      LOCALS := lct_lst
      LABELS := [.mk_list (Map (fun (rt_elem : reftype) => valtype_reftype rt_elem) rt_lst)]
      RETURN := some (.mk_list (Option.toList (OMap (fun (rt'_elem : reftype) => valtype_reftype rt'_elem) rt'_opt))) : context
    }) →
    Context_ok C


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:129.1-129.84 -/
inductive Externaddr_ok : store → externaddr → externtype → Prop where
  | global (s : store) (a : addr) (v_globalinst : globalinst) :
    a < (List.length (s.GLOBALS)) →
    ((s.GLOBALS)[a]!) = v_globalinst →
    wf_store s →
    wf_externtype (externtype.GLOBAL (v_globalinst.TYPE)) →
    Externaddr_ok s (externaddr.GLOBAL a) (externtype.GLOBAL (v_globalinst.TYPE))
  | mem (s : store) (a : addr) (v_meminst : meminst) :
    a < (List.length (s.MEMS)) →
    ((s.MEMS)[a]!) = v_meminst →
    wf_store s →
    wf_externtype (externtype.MEM (v_meminst.TYPE)) →
    Externaddr_ok s (externaddr.MEM a) (externtype.MEM (v_meminst.TYPE))
  | table (s : store) (a : addr) (v_tableinst : tableinst) :
    a < (List.length (s.TABLES)) →
    ((s.TABLES)[a]!) = v_tableinst →
    wf_store s →
    wf_externtype (externtype.TABLE (v_tableinst.TYPE)) →
    Externaddr_ok s (externaddr.TABLE a) (externtype.TABLE (v_tableinst.TYPE))
  | func (s : store) (a : addr) (v_funcinst : funcinst) :
    a < (List.length (s.FUNCS)) →
    ((s.FUNCS)[a]!) = v_funcinst →
    wf_store s →
    wf_externtype (externtype.FUNC (v_funcinst.TYPE)) →
    Externaddr_ok s (externaddr.FUNC a) (externtype.FUNC (v_funcinst.TYPE))
  | sub (s : store) (v_externaddr : externaddr) (xt : externtype) (xt' : externtype) :
    Externaddr_ok s v_externaddr xt' →
    Externtype_sub xt' xt →
    wf_store s →
    wf_externtype xt →
    wf_externtype xt' →
    Externaddr_ok s v_externaddr xt


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:27.1-27.40 -/
inductive Ref_ok : store → ref → reftype → Prop where
  | null (s : store) (rt : reftype) :
    wf_store s →
    Ref_ok s (ref.REF_NULL rt) rt
  | func (s : store) (a : addr) (ext : functype) :
    Externaddr_ok s (externaddr.FUNC a) (externtype.FUNC ext) →
    wf_store s →
    wf_externtype (externtype.FUNC ext) →
    Ref_ok s (ref.REF_FUNC_ADDR a) reftype.FUNCREF
  | extern (s : store) (a : addr) :
    wf_store s →
    Ref_ok s (ref.REF_HOST_ADDR a) reftype.EXTERNREF


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:41.1-41.40 -/
inductive Val_ok : store → val → valtype → Prop where
  | numtype (s : store) (nt : numtype) (c_t : num_) :
    wf_store s →
    wf_val (val.CONST nt c_t) →
    Val_ok s (val.CONST nt c_t) (valtype_numtype nt)
  | vectype (s : store) (vt : vectype) (c_t : vec_) :
    wf_store s →
    wf_val (val.VCONST vt c_t) →
    Val_ok s (val.VCONST vt c_t) (valtype_vectype vt)
  | reftype (s : store) (r : ref) (rt : reftype) :
    Ref_ok s r rt →
    wf_store s →
    Val_ok s (val_ref r) (valtype_reftype rt)


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:55.1-55.47 -/
inductive Result_ok : store → result → List valtype → Prop where
  | result (s : store) (v_lst : List val) (t_lst : List valtype) :
    (List.length t_lst) = (List.length v_lst) →
    Forall₂ (fun (t_elem : valtype) (v_elem : val) => Val_ok s v_elem t_elem) t_lst v_lst →
    wf_store s →
    wf_result (result._VALS v_lst) →
    Result_ok s (result._VALS v_lst) t_lst
  | trap (s : store) (t_lst : List valtype) :
    wf_store s →
    wf_result result.TRAP →
    Result_ok s result.TRAP t_lst


/- Type Alias Definition at: ../specification/wasm-2.0/B-soundness.spectec:66.1-66.31 -/
abbrev adminexpr : Type := List admininstr

/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:158.1-158.51 -/
inductive Datainst_ok : store → datainst → datatype → Prop where
  | mk_Datainst_ok (s : store) (b_lst : List byte) :
    wf_store s →
    wf_datainst ({
      BYTES := b_lst : datainst
    }) →
    Datainst_ok s ({
      BYTES := b_lst : datainst
    }) datatype.OK


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:159.1-159.51 -/
inductive Eleminst_ok : store → eleminst → elemtype → Prop where
  | mk_Eleminst_ok (s : store) (rt : reftype) (ref_lst : List ref) :
    Forall (fun (v_ref_elem : ref) => Ref_ok s v_ref_elem rt) ref_lst →
    wf_store s →
    Eleminst_ok s ({
      TYPE := rt
      REFS := ref_lst : eleminst
    }) rt


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:160.1-160.49 -/
inductive Exportinst_ok : store → exportinst → Prop where
  | mk_Exportinst_ok (s : store) (nm : name) (xa : externaddr) (xt : externtype) :
    Externaddr_ok s xa xt →
    wf_store s →
    wf_externtype xt →
    wf_exportinst ({
      NAME := nm
      ADDR := xa : exportinst
    }) →
    Exportinst_ok s ({
      NAME := nm
      ADDR := xa : exportinst
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:198.1-198.54 -/
inductive Moduleinst_ok : store → moduleinst → context → Prop where
  | mk_Moduleinst_ok (s : store) (functype_lst : List functype) (funcaddr_lst : List funcaddr) (globaladdr_lst : List globaladdr) (tableaddr_lst : List tableaddr) (memaddr_lst : List memaddr) (elemaddr_lst : List elemaddr) (dataaddr_lst : List dataaddr) (exportinst_lst : List exportinst) (functype_F_lst : List functype) (globaltype_lst : List globaltype) (tabletype_lst : List tabletype) (memtype_lst : List memtype) (elemtype_lst : List elemtype) (datatype_lst : List datatype) :
    Forall (fun (v_functype_elem : functype) => Functype_ok v_functype_elem) functype_lst →
    (List.length globaladdr_lst) = (List.length globaltype_lst) →
    Forall₂ (fun (v_globaladdr_elem : globaladdr) (v_globaltype_elem : globaltype) => Externaddr_ok s (externaddr.GLOBAL v_globaladdr_elem) (externtype.GLOBAL v_globaltype_elem)) globaladdr_lst globaltype_lst →
    (List.length funcaddr_lst) = (List.length functype_F_lst) →
    Forall₂ (fun (v_funcaddr_elem : funcaddr) (functype_F_elem : functype) => Externaddr_ok s (externaddr.FUNC v_funcaddr_elem) (externtype.FUNC functype_F_elem)) funcaddr_lst functype_F_lst →
    (List.length memaddr_lst) = (List.length memtype_lst) →
    Forall₂ (fun (v_memaddr_elem : memaddr) (v_memtype_elem : memtype) => Externaddr_ok s (externaddr.MEM v_memaddr_elem) (externtype.MEM v_memtype_elem)) memaddr_lst memtype_lst →
    (List.length tableaddr_lst) = (List.length tabletype_lst) →
    Forall₂ (fun (v_tableaddr_elem : tableaddr) (v_tabletype_elem : tabletype) => Externaddr_ok s (externaddr.TABLE v_tableaddr_elem) (externtype.TABLE v_tabletype_elem)) tableaddr_lst tabletype_lst →
    Forall (fun (v_exportinst_elem : exportinst) => Exportinst_ok s v_exportinst_elem) exportinst_lst →
    (List.length dataaddr_lst) = (List.length datatype_lst) →
    Forall (fun (v_dataaddr_elem : Nat) => v_dataaddr_elem < (List.length (s.DATAS))) dataaddr_lst →
    Forall₂ (fun (v_dataaddr_elem : Nat) (v_datatype_elem : datatype) => Datainst_ok s ((s.DATAS)[v_dataaddr_elem]!) v_datatype_elem) dataaddr_lst datatype_lst →
    (List.length elemaddr_lst) = (List.length elemtype_lst) →
    Forall (fun (v_elemaddr_elem : Nat) => v_elemaddr_elem < (List.length (s.ELEMS))) elemaddr_lst →
    Forall₂ (fun (v_elemaddr_elem : Nat) (v_elemtype_elem : elemtype) => Eleminst_ok s ((s.ELEMS)[v_elemaddr_elem]!) v_elemtype_elem) elemaddr_lst elemtype_lst →
    disjoint_ name (Map (fun (v_exportinst_elem : exportinst) => v_exportinst_elem.NAME) exportinst_lst) →
    (List.length ((Map (fun (v_globaladdr_elem : globaladdr) => externaddr.GLOBAL v_globaladdr_elem) globaladdr_lst) ++ ((Map (fun (v_memaddr_elem : memaddr) => externaddr.MEM v_memaddr_elem) memaddr_lst) ++ ((Map (fun (v_tableaddr_elem : tableaddr) => externaddr.TABLE v_tableaddr_elem) tableaddr_lst) ++ (Map (fun (v_funcaddr_elem : funcaddr) => externaddr.FUNC v_funcaddr_elem) funcaddr_lst))))) > 0 →
    Forall (fun (v_exportinst_elem : exportinst) => List.contains ((Map (fun (v_globaladdr_elem : globaladdr) => externaddr.GLOBAL v_globaladdr_elem) globaladdr_lst) ++ ((Map (fun (v_memaddr_elem : memaddr) => externaddr.MEM v_memaddr_elem) memaddr_lst) ++ ((Map (fun (v_tableaddr_elem : tableaddr) => externaddr.TABLE v_tableaddr_elem) tableaddr_lst) ++ (Map (fun (v_funcaddr_elem : funcaddr) => externaddr.FUNC v_funcaddr_elem) funcaddr_lst)))) (v_exportinst_elem.ADDR)) exportinst_lst →
    wf_store s →
    wf_moduleinst ({
      TYPES := functype_lst
      FUNCS := funcaddr_lst
      GLOBALS := globaladdr_lst
      TABLES := tableaddr_lst
      MEMS := memaddr_lst
      ELEMS := elemaddr_lst
      DATAS := dataaddr_lst
      EXPORTS := exportinst_lst : moduleinst
    }) →
    wf_context ({
      TYPES := functype_lst
      FUNCS := functype_F_lst
      GLOBALS := globaltype_lst
      TABLES := tabletype_lst
      MEMS := memtype_lst
      ELEMS := elemtype_lst
      DATAS := datatype_lst
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    Forall (fun (v_globaltype_elem : globaltype) => wf_externtype (externtype.GLOBAL v_globaltype_elem)) globaltype_lst →
    Forall (fun (functype_F_elem : functype) => wf_externtype (externtype.FUNC functype_F_elem)) functype_F_lst →
    Forall (fun (v_memtype_elem : memtype) => wf_externtype (externtype.MEM v_memtype_elem)) memtype_lst →
    Forall (fun (v_tabletype_elem : tabletype) => wf_externtype (externtype.TABLE v_tabletype_elem)) tabletype_lst →
    Moduleinst_ok s ({
      TYPES := functype_lst
      FUNCS := funcaddr_lst
      GLOBALS := globaladdr_lst
      TABLES := tableaddr_lst
      MEMS := memaddr_lst
      ELEMS := elemaddr_lst
      DATAS := dataaddr_lst
      EXPORTS := exportinst_lst : moduleinst
    }) ({
      TYPES := functype_lst
      FUNCS := functype_F_lst
      GLOBALS := globaltype_lst
      TABLES := tabletype_lst
      MEMS := memtype_lst
      ELEMS := elemtype_lst
      DATAS := datatype_lst
      LOCALS := []
      LABELS := []
      RETURN := none : context
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:292.1-292.44 -/
inductive Frame_ok : store → frame → context → Prop where
  | mk_Frame_ok (s : store) (val_lst : List val) (v_moduleinst : moduleinst) (C : context) (t_lst : List valtype) :
    Moduleinst_ok s v_moduleinst C →
    (List.length t_lst) = (List.length val_lst) →
    Forall₂ (fun (t_elem : valtype) (v_val_elem : val) => Val_ok s v_val_elem t_elem) t_lst val_lst →
    wf_store s →
    wf_context C →
    wf_frame ({
      LOCALS := val_lst
      MODULE := v_moduleinst : frame
    }) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := t_lst
      LABELS := []
      RETURN := none : context
    }) →
    Frame_ok s ({
      LOCALS := val_lst
      MODULE := v_moduleinst : frame
    }) (C ++ ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := t_lst
      LABELS := []
      RETURN := none : context
    }))


mutual
/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:68.1-69.36 -/
inductive Instr_ok2 : store → context → admininstr → functype → Prop where
  | plain (s : store) (C : context) (v_instr : instr) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instr_ok C v_instr (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_store s →
    wf_context C →
    wf_instr v_instr →
    Instr_ok2 s C (admininstr_instr v_instr) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | label (s : store) (C : context) (v_n : n) (instr'_lst : List instr) (admininstr_lst : List admininstr) (t_lst : List valtype) (t'_lst : List valtype) :
    Instrs_ok2 s C (Map (fun (instr'_elem : instr) => admininstr_instr instr'_elem) instr'_lst) (functype.mk_functype (.mk_list t'_lst) (.mk_list t_lst)) →
    Instrs_ok2 s (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t'_lst]
      RETURN := none : context
    }) ++ C) admininstr_lst (functype.mk_functype (.mk_list []) (.mk_list t_lst)) →
    wf_store s →
    wf_context C →
    wf_admininstr (admininstr.LABEL_ v_n instr'_lst admininstr_lst) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      ELEMS := []
      DATAS := []
      LOCALS := []
      LABELS := [.mk_list t'_lst]
      RETURN := none : context
    }) →
    v_n = (List.length t'_lst) →
    Instr_ok2 s C (admininstr.LABEL_ v_n instr'_lst admininstr_lst) (functype.mk_functype (.mk_list []) (.mk_list t_lst))
  | Instr_ok2_frame (s : store) (C : context) (v_n : n) (f : frame) (admininstr_lst : List admininstr) (t_lst : List valtype) (C' : context) :
    Frame_ok s f C' →
    Expr_ok2 s ({
      C' with
      RETURN := some (.mk_list t_lst)
    }) admininstr_lst (.mk_list t_lst) →
    wf_store s →
    wf_context C →
    wf_context C' →
    wf_admininstr (admininstr.FRAME_ v_n f admininstr_lst) →
    v_n = (List.length t_lst) →
    Instr_ok2 s C (admininstr.FRAME_ v_n f admininstr_lst) (functype.mk_functype (.mk_list []) (.mk_list t_lst))
  | call_addr (s : store) (C : context) (v_funcaddr : funcaddr) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Externaddr_ok s (externaddr.FUNC v_funcaddr) (externtype.FUNC (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) →
    wf_store s →
    wf_context C →
    wf_admininstr (admininstr.CALL_ADDR v_funcaddr) →
    wf_externtype (externtype.FUNC (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))) →
    Instr_ok2 s C (admininstr.CALL_ADDR v_funcaddr) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | ref (s : store) (C : context) (v_ref : ref) (rt : reftype) :
    Ref_ok s v_ref rt →
    wf_store s →
    wf_context C →
    Instr_ok2 s C (admininstr_ref v_ref) (functype.mk_functype (.mk_list []) (.mk_list [valtype_reftype rt]))
  | trap (s : store) (C : context) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    wf_store s →
    wf_context C →
    wf_admininstr admininstr.TRAP →
    Instr_ok2 s C admininstr.TRAP (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))

/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:70.1-71.36 -/
inductive Instrs_ok2 : store → context → List admininstr → functype → Prop where
  | empty (s : store) (C : context) :
    wf_store s →
    wf_context C →
    Instrs_ok2 s C [] (functype.mk_functype (.mk_list []) (.mk_list []))
  | instr (s : store) (C : context) (v_admininstr : admininstr) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instr_ok2 s C v_admininstr (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_store s →
    wf_context C →
    wf_admininstr v_admininstr →
    Instrs_ok2 s C [v_admininstr] (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst))
  | seq (s : store) (C : context) (admininstr_1_lst : List admininstr) (admininstr_2_lst : List admininstr) (t_1_lst : List valtype) (t_3_lst : List valtype) (t_2_lst : List valtype) :
    Instrs_ok2 s C admininstr_1_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instrs_ok2 s C admininstr_2_lst (functype.mk_functype (.mk_list t_2_lst) (.mk_list t_3_lst)) →
    wf_store s →
    wf_context C →
    Forall (fun (admininstr_1_elem : admininstr) => wf_admininstr admininstr_1_elem) admininstr_1_lst →
    Forall (fun (admininstr_2_elem : admininstr) => wf_admininstr admininstr_2_elem) admininstr_2_lst →
    Instrs_ok2 s C (admininstr_1_lst ++ admininstr_2_lst) (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_3_lst))
  | sub (s : store) (C : context) (admininstr_lst : List admininstr) (t'_1_lst : List valtype) (t'_2_lst : List valtype) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instrs_ok2 s C admininstr_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Resulttype_sub (.mk_list t'_1_lst) (.mk_list t_1_lst) →
    Resulttype_sub (.mk_list t_2_lst) (.mk_list t'_2_lst) →
    wf_store s →
    wf_context C →
    Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst →
    Instrs_ok2 s C admininstr_lst (functype.mk_functype (.mk_list t'_1_lst) (.mk_list t'_2_lst))
  | Instrs_ok2_frame (s : store) (C : context) (admininstr_lst : List admininstr) (t_lst : List valtype) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instrs_ok2 s C admininstr_lst (functype.mk_functype (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_store s →
    wf_context C →
    Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst →
    Instrs_ok2 s C admininstr_lst (functype.mk_functype (.mk_list (t_lst ++ t_1_lst)) (.mk_list (t_lst ++ t_2_lst)))

/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:72.1-73.36 -/
inductive Expr_ok2 : store → context → adminexpr → resulttype → Prop where
  | mk_Expr_ok2 (s : store) (C : context) (admininstr_lst : List admininstr) (t_lst : List valtype) :
    Instrs_ok2 s C admininstr_lst (functype.mk_functype (.mk_list []) (.mk_list t_lst)) →
    wf_store s →
    wf_context C →
    Forall (fun (v_admininstr_elem : admininstr) => wf_admininstr v_admininstr_elem) admininstr_lst →
    Expr_ok2 s C admininstr_lst (.mk_list t_lst)


end

/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:154.1-154.57 -/
inductive Globalinst_ok : store → globalinst → globaltype → Prop where
  | mk_Globalinst_ok (s : store) (v_mut : «mut») (t : valtype) (v_val : val) :
    Globaltype_ok (globaltype.mk_globaltype v_mut t) →
    Val_ok s v_val t →
    wf_store s →
    wf_globalinst ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := v_val : globalinst
    }) →
    Globalinst_ok s ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := v_val : globalinst
    }) (globaltype.mk_globaltype v_mut t)


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:155.1-155.48 -/
inductive Meminst_ok : store → meminst → memtype → Prop where
  | mk_Meminst_ok (s : store) (v_n : n) (m_opt : Option m) (b_lst : List byte) :
    Memtype_ok (memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt))) →
    (List.length b_lst) = (v_n * (64 * Ki)) →
    wf_store s →
    wf_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt))
      BYTES := b_lst : meminst
    }) →
    wf_memtype (memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt))) →
    Meminst_ok s ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt))
      BYTES := b_lst : meminst
    }) (memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)))


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:156.1-156.54 -/
inductive Tableinst_ok : store → tableinst → tabletype → Prop where
  | mk_Tableinst_ok (s : store) (v_n : n) (m_opt : Option m) (rt : reftype) (ref_lst : List ref) :
    Tabletype_ok (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt) →
    Forall (fun (v_ref_elem : ref) => Ref_ok s v_ref_elem rt) ref_lst →
    (List.length ref_lst) = v_n →
    wf_store s →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt
      REFS := ref_lst : tableinst
    }) →
    wf_tabletype (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt) →
    Tableinst_ok s ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt
      REFS := ref_lst : tableinst
    }) (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt)


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:157.1-157.51 -/
inductive Funcinst_ok : store → funcinst → functype → Prop where
  | mk_Funcinst_ok (s : store) (ft : functype) (v_moduleinst : moduleinst) (v_func : func) (C : context) :
    Functype_ok ft →
    Moduleinst_ok s v_moduleinst C →
    Func_ok C v_func ft →
    wf_store s →
    wf_context C →
    wf_funcinst ({
      TYPE := ft
      MODULE := v_moduleinst
      CODE := v_func : funcinst
    }) →
    Funcinst_ok s ({
      TYPE := ft
      MODULE := v_moduleinst
      CODE := v_func : funcinst
    }) ft


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:232.1-232.33 -/
inductive Store_ok : store → Prop where
  | mk_Store_ok (s : store) (globalinst_lst : List globalinst) (globaltype_lst : List globaltype) (meminst_lst : List meminst) (memtype_lst : List memtype) (tableinst_lst : List tableinst) (tabletype_lst : List tabletype) (funcinst_lst : List funcinst) (functype_lst : List functype) (datainst_lst : List datainst) (datatype_lst : List datatype) (eleminst_lst : List eleminst) (elemtype_lst : List elemtype) :
    (List.length globalinst_lst) = (List.length globaltype_lst) →
    Forall₂ (fun (v_globalinst_elem : globalinst) (v_globaltype_elem : globaltype) => Globalinst_ok s v_globalinst_elem v_globaltype_elem) globalinst_lst globaltype_lst →
    (List.length meminst_lst) = (List.length memtype_lst) →
    Forall₂ (fun (v_meminst_elem : meminst) (v_memtype_elem : memtype) => Meminst_ok s v_meminst_elem v_memtype_elem) meminst_lst memtype_lst →
    (List.length tableinst_lst) = (List.length tabletype_lst) →
    Forall₂ (fun (v_tableinst_elem : tableinst) (v_tabletype_elem : tabletype) => Tableinst_ok s v_tableinst_elem v_tabletype_elem) tableinst_lst tabletype_lst →
    (List.length funcinst_lst) = (List.length functype_lst) →
    Forall₂ (fun (v_funcinst_elem : funcinst) (v_functype_elem : functype) => Funcinst_ok s v_funcinst_elem v_functype_elem) funcinst_lst functype_lst →
    (List.length datainst_lst) = (List.length datatype_lst) →
    Forall₂ (fun (v_datainst_elem : datainst) (v_datatype_elem : datatype) => Datainst_ok s v_datainst_elem v_datatype_elem) datainst_lst datatype_lst →
    (List.length eleminst_lst) = (List.length elemtype_lst) →
    Forall₂ (fun (v_eleminst_elem : eleminst) (v_elemtype_elem : elemtype) => Eleminst_ok s v_eleminst_elem v_elemtype_elem) eleminst_lst elemtype_lst →
    s = ({
      FUNCS := funcinst_lst
      GLOBALS := globalinst_lst
      TABLES := tableinst_lst
      MEMS := meminst_lst
      ELEMS := eleminst_lst
      DATAS := datainst_lst : store
    }) →
    wf_store s →
    Forall (fun (v_memtype_elem : memtype) => wf_memtype v_memtype_elem) memtype_lst →
    Forall (fun (v_tabletype_elem : tabletype) => wf_tabletype v_tabletype_elem) tabletype_lst →
    wf_store ({
      FUNCS := funcinst_lst
      GLOBALS := globalinst_lst
      TABLES := tableinst_lst
      MEMS := meminst_lst
      ELEMS := eleminst_lst
      DATAS := datainst_lst : store
    }) →
    Store_ok s


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:248.1-248.54 -/
inductive Extend_globalinst : globalinst → globalinst → Prop where
  | mk_Extend_globalinst (v_mut : «mut») (t : valtype) (v_val : val) (val' : val) :
    (v_mut = (some r_MUT.MUT)) ∨ (v_val = val') →
    wf_globalinst ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := v_val : globalinst
    }) →
    wf_globalinst ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := val' : globalinst
    }) →
    Extend_globalinst ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := v_val : globalinst
    }) ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := val' : globalinst
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:249.1-249.45 -/
inductive Extend_meminst : meminst → meminst → Prop where
  | mk_Extend_meminst (v_n : n) (m_opt : Option m) (b_lst : List byte) (n' : n) (b'_lst : List byte) :
    v_n ≤ n' →
    (List.length b_lst) ≤ (List.length b'_lst) →
    wf_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt))
      BYTES := b_lst : meminst
    }) →
    wf_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN n') (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt))
      BYTES := b'_lst : meminst
    }) →
    Extend_meminst ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt))
      BYTES := b_lst : meminst
    }) ({
      TYPE := memtype.PAGE (limits.mk_limits (uN.mk_uN n') (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt))
      BYTES := b'_lst : meminst
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:250.1-250.51 -/
inductive Extend_tableinst : tableinst → tableinst → Prop where
  | mk_Extend_tableinst (v_n : n) (m_opt : Option m) (rt : reftype) (ref_lst : List ref) (n' : n) (ref'_lst : List ref) :
    v_n ≤ n' →
    (List.length ref_lst) ≤ (List.length ref'_lst) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt
      REFS := ref_lst : tableinst
    }) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN n') (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt
      REFS := ref'_lst : tableinst
    }) →
    Extend_tableinst ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_n) (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt
      REFS := ref_lst : tableinst
    }) ({
      TYPE := tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN n') (OMap (fun (v_m_elem : m) => uN.mk_uN v_m_elem) m_opt)) rt
      REFS := ref'_lst : tableinst
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:251.1-251.48 -/
inductive Extend_funcinst : funcinst → funcinst → Prop where
  | mk_Extend_funcinst (ft : functype) (mm : moduleinst) (fc : func) :
    wf_funcinst ({
      TYPE := ft
      MODULE := mm
      CODE := fc : funcinst
    }) →
    Extend_funcinst ({
      TYPE := ft
      MODULE := mm
      CODE := fc : funcinst
    }) ({
      TYPE := ft
      MODULE := mm
      CODE := fc : funcinst
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:252.1-252.48 -/
inductive Extend_datainst : datainst → datainst → Prop where
  | mk_Extend_datainst (b_lst : List byte) (b'_lst : List byte) :
    (b_lst = b'_lst) ∨ (b'_lst = []) →
    wf_datainst ({
      BYTES := b_lst : datainst
    }) →
    wf_datainst ({
      BYTES := b'_lst : datainst
    }) →
    Extend_datainst ({
      BYTES := b_lst : datainst
    }) ({
      BYTES := b'_lst : datainst
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:253.1-253.48 -/
inductive Extend_eleminst : eleminst → eleminst → Prop where
  | mk_Extend_eleminst (rt : reftype) (ref_lst : List ref) (ref'_lst : List ref) :
    (ref_lst = ref'_lst) ∨ (ref'_lst = []) →
    Extend_eleminst ({
      TYPE := rt
      REFS := ref_lst : eleminst
    }) ({
      TYPE := rt
      REFS := ref'_lst : eleminst
    })


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:254.1-254.39 -/
inductive Extend_store : store → store → Prop where
  | mk_Extend_store (s : store) (s' : store) :
    Forall (fun (a : Nat) => a < (List.length (s.GLOBALS))) (List.range (List.length (s.GLOBALS))) →
    Forall (fun (a : Nat) => a < (List.length (s'.GLOBALS))) (List.range (List.length (s.GLOBALS))) →
    Forall (fun (a : Nat) => Extend_globalinst ((s.GLOBALS)[a]!) ((s'.GLOBALS)[a]!)) (List.range (List.length (s.GLOBALS))) →
    Forall (fun (a : Nat) => a < (List.length (s.MEMS))) (List.range (List.length (s.MEMS))) →
    Forall (fun (a : Nat) => a < (List.length (s'.MEMS))) (List.range (List.length (s.MEMS))) →
    Forall (fun (a : Nat) => Extend_meminst ((s.MEMS)[a]!) ((s'.MEMS)[a]!)) (List.range (List.length (s.MEMS))) →
    Forall (fun (a : Nat) => a < (List.length (s.TABLES))) (List.range (List.length (s.TABLES))) →
    Forall (fun (a : Nat) => a < (List.length (s'.TABLES))) (List.range (List.length (s.TABLES))) →
    Forall (fun (a : Nat) => Extend_tableinst ((s.TABLES)[a]!) ((s'.TABLES)[a]!)) (List.range (List.length (s.TABLES))) →
    Forall (fun (a : Nat) => a < (List.length (s.FUNCS))) (List.range (List.length (s.FUNCS))) →
    Forall (fun (a : Nat) => a < (List.length (s'.FUNCS))) (List.range (List.length (s.FUNCS))) →
    Forall (fun (a : Nat) => Extend_funcinst ((s.FUNCS)[a]!) ((s'.FUNCS)[a]!)) (List.range (List.length (s.FUNCS))) →
    Forall (fun (a : Nat) => a < (List.length (s.DATAS))) (List.range (List.length (s.DATAS))) →
    Forall (fun (a : Nat) => a < (List.length (s'.DATAS))) (List.range (List.length (s.DATAS))) →
    Forall (fun (a : Nat) => Extend_datainst ((s.DATAS)[a]!) ((s'.DATAS)[a]!)) (List.range (List.length (s.DATAS))) →
    Forall (fun (a : Nat) => a < (List.length (s.ELEMS))) (List.range (List.length (s.ELEMS))) →
    Forall (fun (a : Nat) => a < (List.length (s'.ELEMS))) (List.range (List.length (s.ELEMS))) →
    Forall (fun (a : Nat) => Extend_eleminst ((s.ELEMS)[a]!) ((s'.ELEMS)[a]!)) (List.range (List.length (s.ELEMS))) →
    wf_store s →
    wf_store s' →
    Extend_store s s'


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:293.1-293.38 -/
inductive State_ok : state → context → Prop where
  | mk_State_ok (s : store) (f : frame) (C : context) :
    Store_ok s →
    Frame_ok s f C →
    wf_context C →
    wf_state (state.mk_state s f) →
    State_ok (state.mk_state s f) C


/- Inductive Relations Definition at: ../specification/wasm-2.0/B-soundness.spectec:294.1-294.43 -/
inductive Config_ok : config → resulttype → Prop where
  | mk_Config_ok (s : store) (f : frame) (admininstr_lst : List admininstr) (t_lst : List valtype) (C : context) :
    State_ok (state.mk_state s f) C →
    Expr_ok2 s C admininstr_lst (.mk_list t_lst) →
    wf_context C →
    wf_config (config.mk_config (state.mk_state s f) admininstr_lst) →
    wf_state (state.mk_state s f) →
    Config_ok (config.mk_config (state.mk_state s f) admininstr_lst) (.mk_list t_lst)

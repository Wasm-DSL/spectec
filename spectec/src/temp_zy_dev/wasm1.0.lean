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

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.14-119.17 -/
inductive MUT : Type where
  | MUT : MUT
deriving Inhabited, BEq


/- Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:7.1-7.27 -/
abbrev N : Type := Nat

/- Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:8.1-8.27 -/
abbrev M : Type := Nat

/- Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:9.1-9.27 -/
abbrev n : Type := Nat

/- Type Alias Definition at: ../specification/wasm-1.0/0-aux.spectec:10.1-10.27 -/
abbrev m : Type := Nat

/- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:15.1-15.14 -/
def Ki : Nat := 1024

/- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:21.1-21.25 -/
def min : ∀  (nat : Nat) (nat_0 : Nat) , Nat
  | i, j =>
    (if (i <= j) then i else j)


/- Recursive Definition at: ../specification/wasm-1.0/0-aux.spectec:25.1-25.21 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/0-aux.spectec:25.6-25.10 -/
inductive fun_sum : (List Nat) -> Nat -> Prop where
  | fun_sum_case_0 : fun_sum [] 0
  | fun_sum_case_1 : forall (v_n : Nat) (n'_lst : (List Nat)) (var_0 : Nat),
    (fun_sum n'_lst var_0) ->
    fun_sum ([v_n] ++ n'_lst) (v_n + var_0)


/- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:32.1-32.44 -/
def opt_ : ∀  (X : Type) (var_0 : (List X)) , (Option X)
  | X, [] =>
    none
  | X, [w] =>
    (some w)


/- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:36.1-36.45 -/
def list_ : ∀  (X : Type) (var_0 : (Option X)) , (List X)
  | X, none =>
    []
  | X, (some w) =>
    [w]


/- Recursive Definition at: ../specification/wasm-1.0/0-aux.spectec:40.1-40.59 -/
/- Auxiliary Definition at: ../specification/wasm-1.0/0-aux.spectec:40.1-40.59 -/
def concat_ : ∀  (X : Type) (var_0 : (List (List X))) , (List X)
  | X, [] =>
    []
  | X, (w_lst :: w'_lst_lst) =>
    (w_lst ++ (concat_ X w'_lst_lst))


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:6.1-6.49 -/
inductive list (X : Type 0) : Type where
  | mk_list (X_lst : (List X)) : list X
deriving Inhabited, BEq

inductive list2 (X : Type 0) : Type where
  | mk_list : forall (X_lst : (List X)), list2 X
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50 -/
inductive byte : Type where
  | mk_byte (i : Nat) : byte
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.1-15.50 -/
def proj_byte_0 : ∀  (x : byte) , Nat
  | (.mk_byte v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:15.8-15.12 -/
inductive wf_byte : byte -> Prop where
  | byte_case_0 : forall (i : Nat),
    ((i >= 0) && (i <= 255)) ->
    wf_byte (.mk_byte i)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25 -/
inductive uN : Type where
  | mk_uN (i : Nat) : uN
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.1-18.25 -/
def proj_uN_0 : ∀  (x : uN) , Nat
  | (.mk_uN v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:17.8-17.11 -/
inductive wf_uN : N -> uN -> Prop where
  | uN_case_0 : forall (v_N : N) (i : Nat),
    ((i >= 0) && (i <= ((((2 ^ v_N) : Nat) - (1 : Nat)) : Nat))) ->
    wf_uN v_N (.mk_uN i)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49 -/
inductive sN : Type where
  | mk_sN (i : Nat) : sN
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.1-20.49 -/
def proj_sN_0 : ∀  (x : sN) , Nat
  | (.mk_sN v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:19.8-19.11 -/
inductive wf_sN : N -> sN -> Prop where
  | sN_case_0 : forall (v_N : N) (i : Nat),
    ((((i >= (0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat))) && (i <= (0 - (1 : Nat)))) || (i == (0 : Nat))) || ((i >= ((1 : Nat))) && (i <= (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat) - (1 : Nat))))) ->
    wf_sN v_N (.mk_sN i)

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:21.1-22.8 -/
abbrev iN : Type := uN

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:24.1-24.20 -/
abbrev u31 : Type := uN

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:25.1-25.20 -/
abbrev u32 : Type := uN

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:26.1-26.20 -/
abbrev u64 : Type := uN

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:28.1-28.20 -/
abbrev i32 : Type := iN

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:29.1-29.20 -/
abbrev i64 : Type := iN

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:36.1-36.21 -/
def signif : ∀  (v_N : N) , Nat
  | 32 =>
    23
  | 64 =>
    52


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:40.1-40.20 -/
def expon : ∀  (v_N : N) , Nat
  | 32 =>
    8
  | 64 =>
    11


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:44.1-44.30 -/
def fun_M : ∀  (v_N : N) , Nat
  | v_N =>
    (signif v_N)


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:47.1-47.30 -/
def E : ∀  (v_N : N) , Nat
  | v_N =>
    (expon v_N)


/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:54.1-54.30 -/
abbrev exp : Type := Nat

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:55.1-59.84 -/
inductive fNmag : Type where
  | NORM (v_m : m) (v_exp : exp) : fNmag
  | SUBNORM (v_m : m) : fNmag
  | INF : fNmag
  | NAN (v_m : m) : fNmag
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:55.8-55.14 -/
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

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:50.1-52.35 -/
inductive fN : Type where
  | POS (v_fNmag : fNmag) : fN
  | NEG (v_fNmag : fNmag) : fN
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:50.8-50.11 -/
inductive wf_fN : N -> fN -> Prop where
  | fN_case_0 : forall (v_N : N) (v_fNmag : fNmag),
    (wf_fNmag v_N v_fNmag) ->
    wf_fN v_N (.POS v_fNmag)
  | fN_case_1 : forall (v_N : N) (v_fNmag : fNmag),
    (wf_fNmag v_N v_fNmag) ->
    wf_fN v_N (.NEG v_fNmag)

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:61.1-61.20 -/
abbrev f32 : Type := fN

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:62.1-62.20 -/
abbrev f64 : Type := fN

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:64.1-64.39 -/
def fzero : ∀  (v_N : N) , fN
  | v_N =>
    (.POS (.SUBNORM 0))


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:67.1-67.39 -/
def fone : ∀  (v_N : N) , fN
  | v_N =>
    (.POS (.NORM 1 (0 : Nat)))


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:70.1-70.21 -/
def canon_ : ∀  (v_N : N) , Nat
  | v_N =>
    (2 ^ ((((signif v_N) : Nat) - (1 : Nat)) : Nat))


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85 -/
inductive char : Type where
  | mk_char (i : Nat) : char
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.1-78.85 -/
def proj_char_0 : ∀  (x : char) , Nat
  | (.mk_char v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:78.8-78.12 -/
inductive wf_char : char -> Prop where
  | char_case_0 : forall (i : Nat),
    (((i >= 0) && (i <= 55295)) || ((i >= 57344) && (i <= 1114111))) ->
    wf_char (.mk_char i)

/- Recursive Definition at: ../specification/wasm-1.0/1-syntax.spectec:80.1-80.25 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:80.6-80.11 -/
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

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70 -/
inductive name : Type where
  | mk_name (char_lst : (List char)) : name
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.1-82.70 -/
def proj_name_0 : ∀  (x : name) , (List char)
  | (.mk_name v_char_list_0) =>
    (v_char_list_0)


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:82.8-82.12 -/
inductive wf_name : name -> Prop where
  | name_case_0 : forall (char_lst : (List char)) (var_0 : (List byte)),
    (fun_utf8 char_lst var_0) ->
    Forall (fun (v_char : char) => (wf_char v_char)) char_lst ->
    ((List.length var_0) < (2 ^ 32)) ->
    wf_name (.mk_name char_lst)

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:91.1-91.36 -/
abbrev idx : Type := u32

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:93.1-93.45 -/
abbrev typeidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:94.1-94.49 -/
abbrev funcidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:95.1-95.49 -/
abbrev globalidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:96.1-96.47 -/
abbrev tableidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:97.1-97.46 -/
abbrev memidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:98.1-98.47 -/
abbrev labelidx : Type := idx

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:99.1-99.47 -/
abbrev localidx : Type := idx

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:108.1-109.26 -/
inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:111.1-111.38 -/
inductive Inn : Type where
  | I32 : Inn
  | I64 : Inn
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def valtype_Inn : ∀  (var_0 : Inn) , valtype
  | .I32 =>
    .I32
  | .I64 =>
    .I64


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:112.1-112.38 -/
inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq


/- Auxiliary Definition at:  -/
def valtype_Fnn : ∀  (var_0 : Fnn) , valtype
  | .F32 =>
    .F32
  | .F64 =>
    .F64


/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:116.1-117.11 -/
abbrev resulttype : Type := (Option valtype)

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:119.1-119.18 -/
abbrev «mut» : Type := (Option MUT)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:121.1-122.17 -/
inductive limits : Type where
  | mk_limits (v_u32 : u32) (_ : (Option u32)) : limits
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:121.8-121.14 -/
inductive wf_limits : limits -> Prop where
  | limits_case_0 : forall (v_u32 : u32) (var_0 : (Option u32)),
    (wf_uN 32 v_u32) ->
    Forall (fun (var_0 : u32) => (wf_uN 32 var_0)) (Option.toList var_0) ->
    wf_limits (.mk_limits v_u32 var_0)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:123.1-124.14 -/
inductive globaltype : Type where
  | mk_globaltype (v_mut : «mut») (v_valtype : valtype) : globaltype
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:125.1-126.23 -/
inductive functype : Type where
  | mk_functype (valtype_lst : (List valtype)) (_ : (List valtype)) : functype
deriving Inhabited, BEq


/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:127.1-128.9 -/
abbrev tabletype : Type := limits

/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:129.1-130.9 -/
abbrev memtype : Type := limits

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:131.1-132.70 -/
inductive externtype : Type where
  | FUNC (v_functype : functype) : externtype
  | GLOBAL (v_globaltype : globaltype) : externtype
  | TABLE (v_tabletype : tabletype) : externtype
  | MEM (v_memtype : memtype) : externtype
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:131.8-131.18 -/
inductive wf_externtype : externtype -> Prop where
  | externtype_case_0 : forall (v_functype : functype), wf_externtype (.FUNC v_functype)
  | externtype_case_1 : forall (v_globaltype : globaltype), wf_externtype (.GLOBAL v_globaltype)
  | externtype_case_2 : forall (v_tabletype : tabletype),
    (wf_limits v_tabletype) ->
    wf_externtype (.TABLE v_tabletype)
  | externtype_case_3 : forall (v_memtype : memtype),
    (wf_limits v_memtype) ->
    wf_externtype (.MEM v_memtype)

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:144.1-144.41 -/
def size : ∀  (v_valtype : valtype) , Nat
  | .I32 =>
    32
  | .I64 =>
    64
  | .F32 =>
    32
  | .F64 =>
    64


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 -/
inductive val_ : Type where
  | mk_val__0 (v_Inn : Inn) (var_x : iN) : val_
  | mk_val__1 (v_Fnn : Fnn) (var_x : fN) : val_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.8-146.13 -/
inductive wf_val_ : valtype -> val_ -> Prop where
  | val__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : iN),
    (wf_uN (size (valtype_Inn v_Inn)) var_x) ->
    (v_valtype == (valtype_Inn v_Inn)) ->
    wf_val_ v_valtype (.mk_val__0 v_Inn var_x)
  | val__case_1 : forall (v_valtype : valtype) (v_Fnn : Fnn) (var_x : fN),
    (wf_fN (size (valtype_Fnn v_Fnn)) var_x) ->
    (v_valtype == (valtype_Fnn v_Fnn)) ->
    wf_val_ v_valtype (.mk_val__1 v_Fnn var_x)

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 -/
def proj_val__0 : ∀  (var_x : val_) , (Option iN)
  | (.mk_val__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:146.1-146.21 -/
def proj_val__1 : ∀  (var_x : val_) , (Option fN)
  | (.mk_val__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:153.1-153.42 -/
inductive sx : Type where
  | U : sx
  | S : sx
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56 -/
inductive sz : Type where
  | mk_sz (i : Nat) : sz
deriving Inhabited, BEq


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.1-154.56 -/
def proj_sz_0 : ∀  (x : sz) , Nat
  | (.mk_sz v_num_0) =>
    (v_num_0)


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:154.8-154.10 -/
inductive wf_sz : sz -> Prop where
  | sz_case_0 : forall (i : Nat),
    ((((i == 8) || (i == 16)) || (i == 32)) || (i == 64)) ->
    wf_sz (.mk_sz i)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 -/
inductive unop_Inn : Type where
  | CLZ : unop_Inn
  | CTZ : unop_Inn
  | POPCNT : unop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 -/
inductive unop_Fnn : Type where
  | ABS : unop_Fnn
  | NEG : unop_Fnn
  | SQRT : unop_Fnn
  | CEIL : unop_Fnn
  | FLOOR : unop_Fnn
  | TRUNC : unop_Fnn
  | NEAREST : unop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 -/
inductive unop_ : Type where
  | mk_unop__0 (v_Inn : Inn) (var_x : unop_Inn) : unop_
  | mk_unop__1 (v_Fnn : Fnn) (var_x : unop_Fnn) : unop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.8-156.14 -/
inductive wf_unop_ : valtype -> unop_ -> Prop where
  | unop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : unop_Inn),
    (v_valtype == (valtype_Inn v_Inn)) ->
    wf_unop_ v_valtype (.mk_unop__0 v_Inn var_x)
  | unop__case_1 : forall (v_valtype : valtype) (v_Fnn : Fnn) (var_x : unop_Fnn),
    (v_valtype == (valtype_Fnn v_Fnn)) ->
    wf_unop_ v_valtype (.mk_unop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 -/
def proj_unop__0 : ∀  (var_x : unop_) , (Option unop_Inn)
  | (.mk_unop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:156.1-156.22 -/
def proj_unop__1 : ∀  (var_x : unop_) , (Option unop_Fnn)
  | (.mk_unop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 -/
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


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 -/
inductive binop_Fnn : Type where
  | ADD : binop_Fnn
  | SUB : binop_Fnn
  | MUL : binop_Fnn
  | DIV : binop_Fnn
  | MIN : binop_Fnn
  | MAX : binop_Fnn
  | COPYSIGN : binop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 -/
inductive binop_ : Type where
  | mk_binop__0 (v_Inn : Inn) (var_x : binop_Inn) : binop_
  | mk_binop__1 (v_Fnn : Fnn) (var_x : binop_Fnn) : binop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.8-160.15 -/
inductive wf_binop_ : valtype -> binop_ -> Prop where
  | binop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : binop_Inn),
    (v_valtype == (valtype_Inn v_Inn)) ->
    wf_binop_ v_valtype (.mk_binop__0 v_Inn var_x)
  | binop__case_1 : forall (v_valtype : valtype) (v_Fnn : Fnn) (var_x : binop_Fnn),
    (v_valtype == (valtype_Fnn v_Fnn)) ->
    wf_binop_ v_valtype (.mk_binop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 -/
def proj_binop__0 : ∀  (var_x : binop_) , (Option binop_Inn)
  | (.mk_binop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:160.1-160.23 -/
def proj_binop__1 : ∀  (var_x : binop_) , (Option binop_Fnn)
  | (.mk_binop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 -/
inductive testop_Inn : Type where
  | EQZ : testop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 -/
inductive testop_ : Type where
  | mk_testop__0 (v_Inn : Inn) (var_x : testop_Inn) : testop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.8-167.16 -/
inductive wf_testop_ : valtype -> testop_ -> Prop where
  | testop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : testop_Inn),
    (v_valtype == (valtype_Inn v_Inn)) ->
    wf_testop_ v_valtype (.mk_testop__0 v_Inn var_x)

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:167.1-167.24 -/
def proj_testop__0 : ∀  (var_x : testop_) , testop_Inn
  | (.mk_testop__0 v_Inn var_x) =>
    var_x


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 -/
inductive relop_Inn : Type where
  | EQ : relop_Inn
  | NE : relop_Inn
  | LT (v_sx : sx) : relop_Inn
  | GT (v_sx : sx) : relop_Inn
  | LE (v_sx : sx) : relop_Inn
  | GE (v_sx : sx) : relop_Inn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 -/
inductive relop_Fnn : Type where
  | EQ : relop_Fnn
  | NE : relop_Fnn
  | LT : relop_Fnn
  | GT : relop_Fnn
  | LE : relop_Fnn
  | GE : relop_Fnn
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 -/
inductive relop_ : Type where
  | mk_relop__0 (v_Inn : Inn) (var_x : relop_Inn) : relop_
  | mk_relop__1 (v_Fnn : Fnn) (var_x : relop_Fnn) : relop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.8-171.15 -/
inductive wf_relop_ : valtype -> relop_ -> Prop where
  | relop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : relop_Inn),
    (v_valtype == (valtype_Inn v_Inn)) ->
    wf_relop_ v_valtype (.mk_relop__0 v_Inn var_x)
  | relop__case_1 : forall (v_valtype : valtype) (v_Fnn : Fnn) (var_x : relop_Fnn),
    (v_valtype == (valtype_Fnn v_Fnn)) ->
    wf_relop_ v_valtype (.mk_relop__1 v_Fnn var_x)

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 -/
def proj_relop__0 : ∀  (var_x : relop_) , (Option relop_Inn)
  | (.mk_relop__0 v_Inn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:171.1-171.23 -/
def proj_relop__1 : ∀  (var_x : relop_) , (Option relop_Fnn)
  | (.mk_relop__1 v_Fnn var_x) =>
    (some var_x)
  | var_x =>
    none


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:179.1-180.78 -/
inductive cvtop : Type where
  | EXTEND (v_sx : sx) : cvtop
  | WRAP : cvtop
  | CONVERT (v_sx : sx) : cvtop
  | TRUNC (v_sx : sx) : cvtop
  | PROMOTE : cvtop
  | DEMOTE : cvtop
  | REINTERPRET : cvtop
deriving Inhabited, BEq


/- Record Creation Definition at: ../specification/wasm-1.0/1-syntax.spectec:185.1-185.69 -/
structure memarg where MKmemarg ::
  ALIGN : u32
  OFFSET : u32
deriving Inhabited, BEq

def _append_memarg (arg1 arg2 : (memarg)) : memarg where
  ALIGN := arg1.ALIGN /- FIXME - Non-trivial append -/
  OFFSET := arg1.OFFSET /- FIXME - Non-trivial append -/
instance : Append memarg where
  append arg1 arg2 := _append_memarg arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:185.8-185.14 -/
inductive wf_memarg : memarg -> Prop where
  | memarg_case_ : forall (var_0 : u32) (var_1 : u32),
    (wf_uN 32 var_0) ->
    (wf_uN 32 var_1) ->
    wf_memarg { ALIGN := var_0, OFFSET := var_1 }

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 -/
inductive loadop_Inn : Type where
  | mk_loadop_Inn (v_sz : sz) (v_sx : sx) : loadop_Inn
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16 -/
inductive wf_loadop_Inn : Inn -> loadop_Inn -> Prop where
  | loadop_Inn_case_0 : forall (v_Inn : Inn) (v_sz : sz) (v_sx : sx),
    (wf_sz v_sz) ->
    ((proj_sz_0 v_sz) < (size (valtype_Inn v_Inn))) ->
    wf_loadop_Inn v_Inn (.mk_loadop_Inn v_sz v_sx)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 -/
inductive loadop_ : Type where
  | mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.8-189.16 -/
inductive wf_loadop_ : valtype -> loadop_ -> Prop where
  | loadop__case_0 : forall (v_valtype : valtype) (v_Inn : Inn) (var_x : loadop_Inn),
    (wf_loadop_Inn v_Inn var_x) ->
    (v_valtype == (valtype_Inn v_Inn)) ->
    wf_loadop_ v_valtype (.mk_loadop__0 v_Inn var_x)

/- Auxiliary Definition at: ../specification/wasm-1.0/1-syntax.spectec:189.1-189.24 -/
def proj_loadop__0 : ∀  (var_x : loadop_) , loadop_Inn
  | (.mk_loadop__0 v_Inn var_x) =>
    var_x


/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:195.1-195.52 -/
abbrev blocktype : Type := (Option valtype)

/- Recursive Definition at: ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16 -/
/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:245.1-250.16 -/
inductive instr : Type where
  | NOP : instr
  | UNREACHABLE : instr
  | DROP : instr
  | SELECT : instr
  | BLOCK (v_blocktype : blocktype) (instr_lst : (List instr)) : instr
  | LOOP (v_blocktype : blocktype) (instr_lst : (List instr)) : instr
  | IFELSE (v_blocktype : blocktype) (instr_lst : (List instr)) (_ : (List instr)) : instr
  | BR (v_labelidx : labelidx) : instr
  | BR_IF (v_labelidx : labelidx) : instr
  | BR_TABLE (labelidx_lst : (List labelidx)) (_ : labelidx) : instr
  | CALL (v_funcidx : funcidx) : instr
  | CALL_INDIRECT (v_typeidx : typeidx) : instr
  | RETURN : instr
  | CONST (v_valtype : valtype) (v_val_ : val_) : instr
  | UNOP (v_valtype : valtype) (v_unop_ : unop_) : instr
  | BINOP (v_valtype : valtype) (v_binop_ : binop_) : instr
  | TESTOP (v_valtype : valtype) (v_testop_ : testop_) : instr
  | RELOP (v_valtype : valtype) (v_relop_ : relop_) : instr
  | CVTOP (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : instr
  | LOCAL_GET (v_localidx : localidx) : instr
  | LOCAL_SET (v_localidx : localidx) : instr
  | LOCAL_TEE (v_localidx : localidx) : instr
  | GLOBAL_GET (v_globalidx : globalidx) : instr
  | GLOBAL_SET (v_globalidx : globalidx) : instr
  | LOAD (v_valtype : valtype) (loadop__opt : (Option loadop_)) (v_memarg : memarg) : instr
  | STORE (v_valtype : valtype) (sz_opt : (Option sz)) (v_memarg : memarg) : instr
  | MEMORY_SIZE : instr
  | MEMORY_GROW : instr
deriving Inhabited, BEq


/- Type Alias Definition at: ../specification/wasm-1.0/1-syntax.spectec:252.1-253.9 -/
abbrev expr : Type := (List instr)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:263.1-264.16 -/
inductive type : Type where
  | TYPE (v_functype : functype) : type
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:265.1-266.16 -/
inductive «local» : Type where
  | LOCAL (v_valtype : valtype) : «local»
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:267.1-268.27 -/
inductive func : Type where
  | FUNC (v_typeidx : typeidx) (local_lst : (List «local»)) (v_expr : expr) : func
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:267.8-267.12 -/
inductive wf_func : func -> Prop where
  | func_case_0 : forall (v_typeidx : typeidx) (local_lst : (List «local»)) (v_expr : expr),
    (wf_uN 32 v_typeidx) ->
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_func (.FUNC v_typeidx local_lst v_expr)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:269.1-270.25 -/
inductive global : Type where
  | GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:269.8-269.14 -/
inductive wf_global : global -> Prop where
  | global_case_0 : forall (v_globaltype : globaltype) (v_expr : expr),
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    wf_global (.GLOBAL v_globaltype v_expr)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:271.1-272.18 -/
inductive table : Type where
  | TABLE (v_tabletype : tabletype) : table
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:271.8-271.13 -/
inductive wf_table : table -> Prop where
  | table_case_0 : forall (v_tabletype : tabletype),
    (wf_limits v_tabletype) ->
    wf_table (.TABLE v_tabletype)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:273.1-274.17 -/
inductive mem : Type where
  | MEMORY (v_memtype : memtype) : mem
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:273.8-273.11 -/
inductive wf_mem : mem -> Prop where
  | mem_case_0 : forall (v_memtype : memtype),
    (wf_limits v_memtype) ->
    wf_mem (.MEMORY v_memtype)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:275.1-276.21 -/
inductive elem : Type where
  | ELEM (v_expr : expr) (funcidx_lst : (List funcidx)) : elem
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:275.8-275.12 -/
inductive wf_elem : elem -> Prop where
  | elem_case_0 : forall (v_expr : expr) (funcidx_lst : (List funcidx)),
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    Forall (fun (v_funcidx : funcidx) => (wf_uN 32 v_funcidx)) funcidx_lst ->
    wf_elem (.ELEM v_expr funcidx_lst)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:277.1-278.18 -/
inductive data : Type where
  | DATA (v_expr : expr) (byte_lst : (List byte)) : data
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:277.8-277.12 -/
inductive wf_data : data -> Prop where
  | data_case_0 : forall (v_expr : expr) (byte_lst : (List byte)),
    Forall (fun (v_expr : instr) => (wf_instr v_expr)) v_expr ->
    Forall (fun (v_byte : byte) => (wf_byte v_byte)) byte_lst ->
    wf_data (.DATA v_expr byte_lst)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:279.1-280.16 -/
inductive start : Type where
  | START (v_funcidx : funcidx) : start
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:279.8-279.13 -/
inductive wf_start : start -> Prop where
  | start_case_0 : forall (v_funcidx : funcidx),
    (wf_uN 32 v_funcidx) ->
    wf_start (.START v_funcidx)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:282.1-283.66 -/
inductive externidx : Type where
  | FUNC (v_funcidx : funcidx) : externidx
  | GLOBAL (v_globalidx : globalidx) : externidx
  | TABLE (v_tableidx : tableidx) : externidx
  | MEM (v_memidx : memidx) : externidx
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:282.8-282.17 -/
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

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:284.1-285.24 -/
inductive «export» : Type where
  | EXPORT (v_name : name) (v_externidx : externidx) : «export»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:284.8-284.14 -/
inductive wf_export : «export» -> Prop where
  | export_case_0 : forall (v_name : name) (v_externidx : externidx),
    (wf_name v_name) ->
    (wf_externidx v_externidx) ->
    wf_export (.EXPORT v_name v_externidx)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:286.1-287.30 -/
inductive «import» : Type where
  | IMPORT (v_name : name) (_ : name) (v_externtype : externtype) : «import»
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:286.8-286.14 -/
inductive wf_import : «import» -> Prop where
  | import_case_0 : forall (v_name : name) (v_externtype : externtype) (var_0 : name),
    (wf_name v_name) ->
    (wf_externtype v_externtype) ->
    (wf_name var_0) ->
    wf_import (.IMPORT v_name var_0 v_externtype)

/- Inductive Type Definition at: ../specification/wasm-1.0/1-syntax.spectec:289.1-290.76 -/
inductive module : Type where
  | MODULE (type_lst : (List type)) (import_lst : (List «import»)) (func_lst : (List func)) (global_lst : (List global)) (table_lst : (List table)) (mem_lst : (List mem)) (elem_lst : (List elem)) (data_lst : (List data)) (start_opt : (Option start)) (export_lst : (List «export»)) : module
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/1-syntax.spectec:289.8-289.14 -/
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

/- Recursive Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:20.1-20.64 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:20.6-20.14 -/
inductive fun_funcsxt : (List externtype) -> (List functype) -> Prop where
  | fun_funcsxt_case_0 : fun_funcsxt [] []
  | fun_funcsxt_case_1 : forall (ft : functype) (xt_lst : (List externtype)) (var_0 : (List functype)),
    (fun_funcsxt xt_lst var_0) ->
    fun_funcsxt ([(.FUNC ft)] ++ xt_lst) ([ft] ++ var_0)
  | fun_funcsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List functype)),
    (fun_funcsxt xt_lst var_0) ->
    fun_funcsxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:21.1-21.66 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:21.6-21.16 -/
inductive fun_globalsxt : (List externtype) -> (List globaltype) -> Prop where
  | fun_globalsxt_case_0 : fun_globalsxt [] []
  | fun_globalsxt_case_1 : forall (gt : globaltype) (xt_lst : (List externtype)) (var_0 : (List globaltype)),
    (fun_globalsxt xt_lst var_0) ->
    fun_globalsxt ([(.GLOBAL gt)] ++ xt_lst) ([gt] ++ var_0)
  | fun_globalsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List globaltype)),
    (fun_globalsxt xt_lst var_0) ->
    fun_globalsxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:22.1-22.65 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:22.6-22.15 -/
inductive fun_tablesxt : (List externtype) -> (List tabletype) -> Prop where
  | fun_tablesxt_case_0 : fun_tablesxt [] []
  | fun_tablesxt_case_1 : forall (tt : limits) (xt_lst : (List externtype)) (var_0 : (List tabletype)),
    (fun_tablesxt xt_lst var_0) ->
    fun_tablesxt ([(.TABLE tt)] ++ xt_lst) ([tt] ++ var_0)
  | fun_tablesxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List tabletype)),
    (fun_tablesxt xt_lst var_0) ->
    fun_tablesxt ([v_externtype] ++ xt_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:23.1-23.63 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:23.6-23.13 -/
inductive fun_memsxt : (List externtype) -> (List memtype) -> Prop where
  | fun_memsxt_case_0 : fun_memsxt [] []
  | fun_memsxt_case_1 : forall (mt : limits) (xt_lst : (List externtype)) (var_0 : (List memtype)),
    (fun_memsxt xt_lst var_0) ->
    fun_memsxt ([(.MEM mt)] ++ xt_lst) ([mt] ++ var_0)
  | fun_memsxt_case_2 : forall (v_externtype : externtype) (xt_lst : (List externtype)) (var_0 : (List memtype)),
    (fun_memsxt xt_lst var_0) ->
    fun_memsxt ([v_externtype] ++ xt_lst) var_0

/- Auxiliary Definition at: ../specification/wasm-1.0/2-syntax-aux.spectec:49.1-49.35 -/
def memarg0 : memarg := { ALIGN := (.mk_uN 0), OFFSET := (.mk_uN 0) }

/- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:7.1-7.22 -/
def nat_of_bool : ∀  (v_bool : Bool) , Nat
  | false =>
    0
  | true =>
    1


/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:11.1-11.23 -/
opaque truncz : forall (rat : Nat), Nat := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:18.6-18.14 -/
inductive fun_signed_ : N -> Nat -> Nat -> Prop where
  | fun_signed__case_0 : forall (v_N : Nat) (i : Nat),
    (i < (2 ^ (((v_N : Nat) - (1 : Nat)) : Nat))) ->
    fun_signed_ v_N i (i : Nat)
  | fun_signed__case_1 : forall (v_N : Nat) (i : Nat),
    (((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) <= i) && (i < (2 ^ v_N))) ->
    fun_signed_ v_N i ((i : Nat) - ((2 ^ v_N) : Nat))

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:22.6-22.18 -/
inductive fun_inv_signed_ : N -> Nat -> Nat -> Prop where
  | fun_inv_signed__case_0 : forall (v_N : Nat) (i : Nat),
    (((0 : Nat) <= i) && (i < ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat))) ->
    fun_inv_signed_ v_N i (i : Nat)
  | fun_inv_signed__case_1 : forall (v_N : Nat) (i : Nat),
    (((0 - ((2 ^ (((v_N : Nat) - (1 : Nat)) : Nat)) : Nat)) <= i) && (i < (0 : Nat))) ->
    fun_inv_signed_ v_N i ((i + ((2 ^ v_N) : Nat)) : Nat)

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:152.1-152.30 -/
opaque fabs_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:155.1-155.31 -/
opaque fceil_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:156.1-156.32 -/
opaque ffloor_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:158.1-158.34 -/
opaque fnearest_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:153.1-153.30 -/
opaque fneg_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:154.1-154.31 -/
opaque fsqrt_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:157.1-157.32 -/
opaque ftrunc_ : forall (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:86.1-86.29 -/
opaque iclz_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:87.1-87.29 -/
opaque ictz_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:88.1-88.32 -/
opaque ipopcnt_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:28.6-28.12 -/
inductive fun_unop_ : valtype -> unop_ -> val_ -> (List val_) -> Prop where
  | fun_unop__case_0 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (iclz_ (size (valtype_Inn .I32)) v_iN))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .CLZ) (.mk_val__0 .I32 v_iN) [(.mk_val__0 .I32 (iclz_ (size (valtype_Inn .I32)) v_iN))]
  | fun_unop__case_1 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (iclz_ (size (valtype_Inn .I64)) v_iN))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .CLZ) (.mk_val__0 .I64 v_iN) [(.mk_val__0 .I64 (iclz_ (size (valtype_Inn .I64)) v_iN))]
  | fun_unop__case_2 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (ictz_ (size (valtype_Inn .I32)) v_iN))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .CTZ) (.mk_val__0 .I32 v_iN) [(.mk_val__0 .I32 (ictz_ (size (valtype_Inn .I32)) v_iN))]
  | fun_unop__case_3 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (ictz_ (size (valtype_Inn .I64)) v_iN))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .CTZ) (.mk_val__0 .I64 v_iN) [(.mk_val__0 .I64 (ictz_ (size (valtype_Inn .I64)) v_iN))]
  | fun_unop__case_4 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (ipopcnt_ (size (valtype_Inn .I32)) v_iN))) ->
    fun_unop_ .I32 (.mk_unop__0 .I32 .POPCNT) (.mk_val__0 .I32 v_iN) [(.mk_val__0 .I32 (ipopcnt_ (size (valtype_Inn .I32)) v_iN))]
  | fun_unop__case_5 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (ipopcnt_ (size (valtype_Inn .I64)) v_iN))) ->
    fun_unop_ .I64 (.mk_unop__0 .I64 .POPCNT) (.mk_val__0 .I64 v_iN) [(.mk_val__0 .I64 (ipopcnt_ (size (valtype_Inn .I64)) v_iN))]
  | fun_unop__case_6 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fabs_ (size (valtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .ABS) (.mk_val__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fabs_ (size (valtype_Fnn .F32)) v_fN))
  | fun_unop__case_7 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fabs_ (size (valtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .ABS) (.mk_val__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fabs_ (size (valtype_Fnn .F64)) v_fN))
  | fun_unop__case_8 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fneg_ (size (valtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEG) (.mk_val__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fneg_ (size (valtype_Fnn .F32)) v_fN))
  | fun_unop__case_9 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fneg_ (size (valtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEG) (.mk_val__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fneg_ (size (valtype_Fnn .F64)) v_fN))
  | fun_unop__case_10 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fsqrt_ (size (valtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .SQRT) (.mk_val__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fsqrt_ (size (valtype_Fnn .F32)) v_fN))
  | fun_unop__case_11 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fsqrt_ (size (valtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .SQRT) (.mk_val__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fsqrt_ (size (valtype_Fnn .F64)) v_fN))
  | fun_unop__case_12 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fceil_ (size (valtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .CEIL) (.mk_val__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fceil_ (size (valtype_Fnn .F32)) v_fN))
  | fun_unop__case_13 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fceil_ (size (valtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .CEIL) (.mk_val__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fceil_ (size (valtype_Fnn .F64)) v_fN))
  | fun_unop__case_14 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (ffloor_ (size (valtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .FLOOR) (.mk_val__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (ffloor_ (size (valtype_Fnn .F32)) v_fN))
  | fun_unop__case_15 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (ffloor_ (size (valtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .FLOOR) (.mk_val__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (ffloor_ (size (valtype_Fnn .F64)) v_fN))
  | fun_unop__case_16 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (ftrunc_ (size (valtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .TRUNC) (.mk_val__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (ftrunc_ (size (valtype_Fnn .F32)) v_fN))
  | fun_unop__case_17 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (ftrunc_ (size (valtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .TRUNC) (.mk_val__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (ftrunc_ (size (valtype_Fnn .F64)) v_fN))
  | fun_unop__case_18 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fnearest_ (size (valtype_Fnn .F32)) v_fN) ->
    fun_unop_ .F32 (.mk_unop__1 .F32 .NEAREST) (.mk_val__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fnearest_ (size (valtype_Fnn .F32)) v_fN))
  | fun_unop__case_19 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fnearest_ (size (valtype_Fnn .F64)) v_fN) ->
    fun_unop_ .F64 (.mk_unop__1 .F64 .NEAREST) (.mk_val__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fnearest_ (size (valtype_Fnn .F64)) v_fN))

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:145.1-145.37 -/
opaque fadd_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:151.1-151.42 -/
opaque fcopysign_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:148.1-148.37 -/
opaque fdiv_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:150.1-150.37 -/
opaque fmax_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:149.1-149.37 -/
opaque fmin_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:147.1-147.37 -/
opaque fmul_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:146.1-146.37 -/
opaque fsub_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), (List fN) := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:73.1-73.36 -/
def iadd_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN (((proj_uN_0 i_1) + (proj_uN_0 i_2)) mod (2 ^ v_N)))


/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:79.1-79.36 -/
opaque iand_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:76.6-76.12 -/
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

/- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:75.1-75.36 -/
def imul_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN (((proj_uN_0 i_1) * (proj_uN_0 i_2)) mod (2 ^ v_N)))


/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:80.1-80.35 -/
opaque ior_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:77.6-77.12 -/
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

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:84.1-84.37 -/
opaque irotl_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:85.1-85.37 -/
opaque irotr_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:82.1-82.34 -/
opaque ishl_ : forall (v_N : N) (v_iN : iN) (v_u32 : u32), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:83.1-83.74 -/
opaque ishr_ : forall (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32), iN := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:74.1-74.36 -/
def isub_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , iN
  | v_N, i_1, i_2 =>
    (.mk_uN ((((((2 ^ v_N) + (proj_uN_0 i_1)) : Nat) - ((proj_uN_0 i_2) : Nat)) mod ((2 ^ v_N) : Nat)) : Nat))


/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:81.1-81.36 -/
opaque ixor_ : forall (v_N : N) (v_iN : iN) (v_iN_0 : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:30.6-30.13 -/
inductive fun_binop_ : valtype -> binop_ -> val_ -> val_ -> (List val_) -> Prop where
  | fun_binop__case_0 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (iadd_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ADD) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (iadd_ (size (valtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_1 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (iadd_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ADD) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (iadd_ (size (valtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_2 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (isub_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .SUB) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (isub_ (size (valtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_3 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (isub_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .SUB) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (isub_ (size (valtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_4 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (imul_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .MUL) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (imul_ (size (valtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_5 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (imul_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .MUL) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (imul_ (size (valtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (Option iN)),
    (fun_idiv_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (list_ val_ (Option.map (fun (iter_0 : iN) => (.mk_val__0 .I32 iter_0)) var_0))
  | fun_binop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (Option iN)),
    (fun_idiv_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.DIV v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (list_ val_ (Option.map (fun (iter_0 : iN) => (.mk_val__0 .I64 iter_0)) var_0))
  | fun_binop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (Option iN)),
    (fun_irem_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.REM v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (list_ val_ (Option.map (fun (iter_0 : iN) => (.mk_val__0 .I32 iter_0)) var_0))
  | fun_binop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : (Option iN)),
    (fun_irem_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    Forall (fun (iter_0 : iN) => (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 iter_0))) (Option.toList var_0) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.REM v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (list_ val_ (Option.map (fun (iter_0 : iN) => (.mk_val__0 .I64 iter_0)) var_0))
  | fun_binop__case_10 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (iand_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .AND) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (iand_ (size (valtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_11 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (iand_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .AND) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (iand_ (size (valtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_12 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (ior_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .OR) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (ior_ (size (valtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_13 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (ior_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .OR) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (ior_ (size (valtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_14 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (ixor_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .XOR) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (ixor_ (size (valtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_15 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (ixor_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .XOR) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (ixor_ (size (valtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_16 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (ishl_ (size (valtype_Inn .I32)) iN_1 (.mk_uN (proj_uN_0 iN_2))))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .SHL) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (ishl_ (size (valtype_Inn .I32)) iN_1 (.mk_uN (proj_uN_0 iN_2))))]
  | fun_binop__case_17 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (ishl_ (size (valtype_Inn .I64)) iN_1 (.mk_uN (proj_uN_0 iN_2))))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .SHL) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (ishl_ (size (valtype_Inn .I64)) iN_1 (.mk_uN (proj_uN_0 iN_2))))]
  | fun_binop__case_18 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (ishr_ (size (valtype_Inn .I32)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2))))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 (.SHR v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (ishr_ (size (valtype_Inn .I32)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2))))]
  | fun_binop__case_19 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (ishr_ (size (valtype_Inn .I64)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2))))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 (.SHR v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (ishr_ (size (valtype_Inn .I64)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2))))]
  | fun_binop__case_20 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (irotl_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ROTL) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (irotl_ (size (valtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_21 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (irotl_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ROTL) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (irotl_ (size (valtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_22 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 (irotr_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_binop_ .I32 (.mk_binop__0 .I32 .ROTR) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [(.mk_val__0 .I32 (irotr_ (size (valtype_Inn .I32)) iN_1 iN_2))]
  | fun_binop__case_23 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 (irotr_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_binop_ .I64 (.mk_binop__0 .I64 .ROTR) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [(.mk_val__0 .I64 (irotr_ (size (valtype_Inn .I64)) iN_1 iN_2))]
  | fun_binop__case_24 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fadd_ (size (valtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .ADD) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fadd_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_25 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fadd_ (size (valtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .ADD) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fadd_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_26 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fsub_ (size (valtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .SUB) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fsub_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_27 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fsub_ (size (valtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .SUB) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fsub_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_28 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fmul_ (size (valtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MUL) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fmul_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_29 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fmul_ (size (valtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MUL) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fmul_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_30 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fdiv_ (size (valtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .DIV) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fdiv_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_31 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fdiv_ (size (valtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .DIV) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fdiv_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_32 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fmin_ (size (valtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MIN) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fmin_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_33 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fmin_ (size (valtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MIN) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fmin_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_34 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fmax_ (size (valtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .MAX) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fmax_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_35 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fmax_ (size (valtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .MAX) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fmax_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_binop__case_36 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 iter_0))) (fcopysign_ (size (valtype_Fnn .F32)) fN_1 fN_2) ->
    fun_binop_ .F32 (.mk_binop__1 .F32 .COPYSIGN) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (fcopysign_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_binop__case_37 : forall (fN_1 : fN) (fN_2 : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 iter_0))) (fcopysign_ (size (valtype_Fnn .F64)) fN_1 fN_2) ->
    fun_binop_ .F64 (.mk_binop__1 .F64 .COPYSIGN) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (fcopysign_ (size (valtype_Fnn .F64)) fN_1 fN_2))

/- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:89.1-89.27 -/
def ieqz_ : ∀  (v_N : N) (v_iN : iN) , u32
  | v_N, i_1 =>
    (.mk_uN (nat_of_bool ((proj_uN_0 i_1) == 0)))


/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:32.6-32.14 -/
inductive fun_testop_ : valtype -> testop_ -> val_ -> val_ -> Prop where
  | fun_testop__case_0 : forall (v_iN : uN),
    (wf_val_ .I32 (.mk_val__0 .I32 (ieqz_ (size (valtype_Inn .I32)) v_iN))) ->
    fun_testop_ .I32 (.mk_testop__0 .I32 .EQZ) (.mk_val__0 .I32 v_iN) (.mk_val__0 .I32 (ieqz_ (size (valtype_Inn .I32)) v_iN))
  | fun_testop__case_1 : forall (v_iN : uN),
    (wf_val_ .I32 (.mk_val__0 .I32 (ieqz_ (size (valtype_Inn .I64)) v_iN))) ->
    fun_testop_ .I64 (.mk_testop__0 .I64 .EQZ) (.mk_val__0 .I64 v_iN) (.mk_val__0 .I32 (ieqz_ (size (valtype_Inn .I64)) v_iN))

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:159.1-159.33 -/
opaque feq_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:164.1-164.33 -/
opaque fge_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:162.1-162.33 -/
opaque fgt_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:163.1-163.33 -/
opaque fle_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:161.1-161.33 -/
opaque flt_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:160.1-160.33 -/
opaque fne_ : forall (v_N : N) (v_fN : fN) (v_fN_0 : fN), u32 := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:91.1-91.33 -/
def ieq_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , u32
  | v_N, i_1, i_2 =>
    (.mk_uN (nat_of_bool (i_1 == i_2)))


/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:96.6-96.11 -/
inductive fun_ige_ : N -> sx -> iN -> iN -> u32 -> Prop where
  | fun_ige__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_ige_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) >= (proj_uN_0 i_2))))
  | fun_ige__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat),
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_ige_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 >= var_1)))

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:94.6-94.11 -/
inductive fun_igt_ : N -> sx -> iN -> iN -> u32 -> Prop where
  | fun_igt__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_igt_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) > (proj_uN_0 i_2))))
  | fun_igt__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat),
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_igt_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 > var_1)))

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:95.6-95.11 -/
inductive fun_ile_ : N -> sx -> iN -> iN -> u32 -> Prop where
  | fun_ile__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_ile_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) <= (proj_uN_0 i_2))))
  | fun_ile__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat),
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_ile_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 <= var_1)))

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:93.6-93.11 -/
inductive fun_ilt_ : N -> sx -> iN -> iN -> u32 -> Prop where
  | fun_ilt__case_0 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN), fun_ilt_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) < (proj_uN_0 i_2))))
  | fun_ilt__case_1 : forall (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Nat) (var_0 : Nat),
    (fun_signed_ v_N (proj_uN_0 i_2) var_1) ->
    (fun_signed_ v_N (proj_uN_0 i_1) var_0) ->
    fun_ilt_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 < var_1)))

/- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:92.1-92.33 -/
def ine_ : ∀  (v_N : N) (v_iN : iN) (v_iN_0 : iN) , u32
  | v_N, i_1, i_2 =>
    (.mk_uN (nat_of_bool (i_1 != i_2)))


/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:34.6-34.13 -/
inductive fun_relop_ : valtype -> relop_ -> val_ -> val_ -> val_ -> Prop where
  | fun_relop__case_0 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ .I32 (.mk_val__0 .I32 (ieq_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 .EQ) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 (ieq_ (size (valtype_Inn .I32)) iN_1 iN_2))
  | fun_relop__case_1 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ .I32 (.mk_val__0 .I32 (ieq_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 .EQ) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 (ieq_ (size (valtype_Inn .I64)) iN_1 iN_2))
  | fun_relop__case_2 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ .I32 (.mk_val__0 .I32 (ine_ (size (valtype_Inn .I32)) iN_1 iN_2))) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 .NE) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 (ine_ (size (valtype_Inn .I32)) iN_1 iN_2))
  | fun_relop__case_3 : forall (iN_1 : uN) (iN_2 : uN),
    (wf_val_ .I32 (.mk_val__0 .I32 (ine_ (size (valtype_Inn .I64)) iN_1 iN_2))) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 .NE) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 (ine_ (size (valtype_Inn .I64)) iN_1 iN_2))
  | fun_relop__case_4 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN),
    (fun_ilt_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    (wf_val_ .I32 (.mk_val__0 .I32 var_0)) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 (.LT v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_5 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN),
    (fun_ilt_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    (wf_val_ .I32 (.mk_val__0 .I32 var_0)) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 (.LT v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_6 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN),
    (fun_igt_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    (wf_val_ .I32 (.mk_val__0 .I32 var_0)) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 (.GT v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_7 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN),
    (fun_igt_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    (wf_val_ .I32 (.mk_val__0 .I32 var_0)) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 (.GT v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_8 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN),
    (fun_ile_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    (wf_val_ .I32 (.mk_val__0 .I32 var_0)) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 (.LE v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_9 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN),
    (fun_ile_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    (wf_val_ .I32 (.mk_val__0 .I32 var_0)) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 (.LE v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_10 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN),
    (fun_ige_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0) ->
    (wf_val_ .I32 (.mk_val__0 .I32 var_0)) ->
    fun_relop_ .I32 (.mk_relop__0 .I32 (.GE v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_11 : forall (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN),
    (fun_ige_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0) ->
    (wf_val_ .I32 (.mk_val__0 .I32 var_0)) ->
    fun_relop_ .I64 (.mk_relop__0 .I64 (.GE v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_12 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (feq_ (size (valtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .EQ) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (feq_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_13 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (feq_ (size (valtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .EQ) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (feq_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_14 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (fne_ (size (valtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .NE) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (fne_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_15 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (fne_ (size (valtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .NE) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (fne_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_16 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (flt_ (size (valtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .LT) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (flt_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_17 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (flt_ (size (valtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .LT) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (flt_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_18 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (fgt_ (size (valtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .GT) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (fgt_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_19 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (fgt_ (size (valtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .GT) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (fgt_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_20 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (fle_ (size (valtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .LE) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (fle_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_21 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (fle_ (size (valtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .LE) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (fle_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_22 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (fge_ (size (valtype_Fnn .F32)) fN_1 fN_2))) ->
    fun_relop_ .F32 (.mk_relop__1 .F32 .GE) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (fge_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_23 : forall (fN_1 : fN) (fN_2 : fN),
    (wf_val_ .I32 (.mk_val__0 .I32 (fge_ (size (valtype_Fnn .F64)) fN_1 fN_2))) ->
    fun_relop_ .F64 (.mk_relop__1 .F64 .GE) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (fge_ (size (valtype_Fnn .F64)) fN_1 fN_2))

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:44.1-44.90 -/
opaque convert__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN), fN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:42.1-42.36 -/
opaque demote__ : forall (v_M : M) (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:40.1-40.89 -/
opaque extend__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:43.1-43.37 -/
opaque promote__ : forall (v_M : M) (v_N : N) (v_fN : fN), (List fN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:45.1-45.76 -/
opaque reinterpret__ : forall (valtype_1 : valtype) (valtype_2 : valtype) (v_val_ : val_), val_ := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:41.1-41.88 -/
opaque trunc__ : forall (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN), (Option iN) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:39.1-39.33 -/
opaque wrap__ : forall (v_M : M) (v_N : N) (v_iN : iN), iN := opaqueDef

/- Inductive Relations Definition at: ../specification/wasm-1.0/3-numerics.spectec:36.6-36.14 -/
inductive fun_cvtop__ : valtype -> valtype -> cvtop -> val_ -> (List val_) -> Prop where
  | fun_cvtop___case_0 : forall (v_sx : sx) (v_iN : uN),
    (wf_val_ .I64 (.mk_val__0 .I64 (extend__ 32 64 v_sx v_iN))) ->
    fun_cvtop__ .I32 .I64 (.EXTEND v_sx) (.mk_val__0 .I32 v_iN) [(.mk_val__0 .I64 (extend__ 32 64 v_sx v_iN))]
  | fun_cvtop___case_1 : forall (v_iN : uN),
    (wf_val_ .I32 (.mk_val__0 .I32 (wrap__ 64 32 v_iN))) ->
    fun_cvtop__ .I64 .I32 .WRAP (.mk_val__0 .I64 v_iN) [(.mk_val__0 .I32 (wrap__ 64 32 v_iN))]
  | fun_cvtop___case_2 : forall (v_sx : sx) (v_fN : fN),
    Forall (fun (iter_0 : iN) => (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 iter_0))) (Option.toList (trunc__ (size (valtype_Fnn .F32)) (size (valtype_Inn .I32)) v_sx v_fN)) ->
    fun_cvtop__ .F32 .I32 (.TRUNC v_sx) (.mk_val__1 .F32 v_fN) (list_ val_ (Option.map (fun (iter_0 : iN) => (.mk_val__0 .I32 iter_0)) (trunc__ (size (valtype_Fnn .F32)) (size (valtype_Inn .I32)) v_sx v_fN)))
  | fun_cvtop___case_3 : forall (v_sx : sx) (v_fN : fN),
    Forall (fun (iter_0 : iN) => (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 iter_0))) (Option.toList (trunc__ (size (valtype_Fnn .F64)) (size (valtype_Inn .I32)) v_sx v_fN)) ->
    fun_cvtop__ .F64 .I32 (.TRUNC v_sx) (.mk_val__1 .F64 v_fN) (list_ val_ (Option.map (fun (iter_0 : iN) => (.mk_val__0 .I32 iter_0)) (trunc__ (size (valtype_Fnn .F64)) (size (valtype_Inn .I32)) v_sx v_fN)))
  | fun_cvtop___case_4 : forall (v_sx : sx) (v_fN : fN),
    Forall (fun (iter_0 : iN) => (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 iter_0))) (Option.toList (trunc__ (size (valtype_Fnn .F32)) (size (valtype_Inn .I64)) v_sx v_fN)) ->
    fun_cvtop__ .F32 .I64 (.TRUNC v_sx) (.mk_val__1 .F32 v_fN) (list_ val_ (Option.map (fun (iter_0 : iN) => (.mk_val__0 .I64 iter_0)) (trunc__ (size (valtype_Fnn .F32)) (size (valtype_Inn .I64)) v_sx v_fN)))
  | fun_cvtop___case_5 : forall (v_sx : sx) (v_fN : fN),
    Forall (fun (iter_0 : iN) => (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 iter_0))) (Option.toList (trunc__ (size (valtype_Fnn .F64)) (size (valtype_Inn .I64)) v_sx v_fN)) ->
    fun_cvtop__ .F64 .I64 (.TRUNC v_sx) (.mk_val__1 .F64 v_fN) (list_ val_ (Option.map (fun (iter_0 : iN) => (.mk_val__0 .I64 iter_0)) (trunc__ (size (valtype_Fnn .F64)) (size (valtype_Inn .I64)) v_sx v_fN)))
  | fun_cvtop___case_6 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ .F64 (.mk_val__1 .F64 iter_0))) (promote__ 32 64 v_fN) ->
    fun_cvtop__ .F32 .F64 .PROMOTE (.mk_val__1 .F32 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F64 iter_0)) (promote__ 32 64 v_fN))
  | fun_cvtop___case_7 : forall (v_fN : fN),
    Forall (fun (iter_0 : fN) => (wf_val_ .F32 (.mk_val__1 .F32 iter_0))) (demote__ 64 32 v_fN) ->
    fun_cvtop__ .F64 .F32 .DEMOTE (.mk_val__1 .F64 v_fN) (List.map (fun (iter_0 : fN) => (.mk_val__1 .F32 iter_0)) (demote__ 64 32 v_fN))
  | fun_cvtop___case_8 : forall (v_sx : sx) (v_iN : uN),
    (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 (convert__ (size (valtype_Inn .I32)) (size (valtype_Fnn .F32)) v_sx v_iN))) ->
    fun_cvtop__ .I32 .F32 (.CONVERT v_sx) (.mk_val__0 .I32 v_iN) [(.mk_val__1 .F32 (convert__ (size (valtype_Inn .I32)) (size (valtype_Fnn .F32)) v_sx v_iN))]
  | fun_cvtop___case_9 : forall (v_sx : sx) (v_iN : uN),
    (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 (convert__ (size (valtype_Inn .I64)) (size (valtype_Fnn .F32)) v_sx v_iN))) ->
    fun_cvtop__ .I64 .F32 (.CONVERT v_sx) (.mk_val__0 .I64 v_iN) [(.mk_val__1 .F32 (convert__ (size (valtype_Inn .I64)) (size (valtype_Fnn .F32)) v_sx v_iN))]
  | fun_cvtop___case_10 : forall (v_sx : sx) (v_iN : uN),
    (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 (convert__ (size (valtype_Inn .I32)) (size (valtype_Fnn .F64)) v_sx v_iN))) ->
    fun_cvtop__ .I32 .F64 (.CONVERT v_sx) (.mk_val__0 .I32 v_iN) [(.mk_val__1 .F64 (convert__ (size (valtype_Inn .I32)) (size (valtype_Fnn .F64)) v_sx v_iN))]
  | fun_cvtop___case_11 : forall (v_sx : sx) (v_iN : uN),
    (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 (convert__ (size (valtype_Inn .I64)) (size (valtype_Fnn .F64)) v_sx v_iN))) ->
    fun_cvtop__ .I64 .F64 (.CONVERT v_sx) (.mk_val__0 .I64 v_iN) [(.mk_val__1 .F64 (convert__ (size (valtype_Inn .I64)) (size (valtype_Fnn .F64)) v_sx v_iN))]
  | fun_cvtop___case_12 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 v_iN)) ->
    ((size (valtype_Inn .I32)) == (size (valtype_Fnn .F32))) ->
    fun_cvtop__ .I32 .F32 .REINTERPRET (.mk_val__0 .I32 v_iN) [(reinterpret__ (valtype_Inn .I32) (valtype_Fnn .F32) (.mk_val__0 .I32 v_iN))]
  | fun_cvtop___case_13 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 v_iN)) ->
    ((size (valtype_Inn .I64)) == (size (valtype_Fnn .F32))) ->
    fun_cvtop__ .I64 .F32 .REINTERPRET (.mk_val__0 .I64 v_iN) [(reinterpret__ (valtype_Inn .I64) (valtype_Fnn .F32) (.mk_val__0 .I64 v_iN))]
  | fun_cvtop___case_14 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I32) (.mk_val__0 .I32 v_iN)) ->
    ((size (valtype_Inn .I32)) == (size (valtype_Fnn .F64))) ->
    fun_cvtop__ .I32 .F64 .REINTERPRET (.mk_val__0 .I32 v_iN) [(reinterpret__ (valtype_Inn .I32) (valtype_Fnn .F64) (.mk_val__0 .I32 v_iN))]
  | fun_cvtop___case_15 : forall (v_iN : uN),
    (wf_val_ (valtype_Inn .I64) (.mk_val__0 .I64 v_iN)) ->
    ((size (valtype_Inn .I64)) == (size (valtype_Fnn .F64))) ->
    fun_cvtop__ .I64 .F64 .REINTERPRET (.mk_val__0 .I64 v_iN) [(reinterpret__ (valtype_Inn .I64) (valtype_Fnn .F64) (.mk_val__0 .I64 v_iN))]
  | fun_cvtop___case_16 : forall (v_fN : fN),
    (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 v_fN)) ->
    ((size (valtype_Inn .I32)) == (size (valtype_Fnn .F32))) ->
    fun_cvtop__ .F32 .I32 .REINTERPRET (.mk_val__1 .F32 v_fN) [(reinterpret__ (valtype_Fnn .F32) (valtype_Inn .I32) (.mk_val__1 .F32 v_fN))]
  | fun_cvtop___case_17 : forall (v_fN : fN),
    (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 v_fN)) ->
    ((size (valtype_Inn .I32)) == (size (valtype_Fnn .F64))) ->
    fun_cvtop__ .F64 .I32 .REINTERPRET (.mk_val__1 .F64 v_fN) [(reinterpret__ (valtype_Fnn .F64) (valtype_Inn .I32) (.mk_val__1 .F64 v_fN))]
  | fun_cvtop___case_18 : forall (v_fN : fN),
    (wf_val_ (valtype_Fnn .F32) (.mk_val__1 .F32 v_fN)) ->
    ((size (valtype_Inn .I64)) == (size (valtype_Fnn .F32))) ->
    fun_cvtop__ .F32 .I64 .REINTERPRET (.mk_val__1 .F32 v_fN) [(reinterpret__ (valtype_Fnn .F32) (valtype_Inn .I64) (.mk_val__1 .F32 v_fN))]
  | fun_cvtop___case_19 : forall (v_fN : fN),
    (wf_val_ (valtype_Fnn .F64) (.mk_val__1 .F64 v_fN)) ->
    ((size (valtype_Inn .I64)) == (size (valtype_Fnn .F64))) ->
    fun_cvtop__ .F64 .I64 .REINTERPRET (.mk_val__1 .F64 v_fN) [(reinterpret__ (valtype_Fnn .F64) (valtype_Inn .I64) (.mk_val__1 .F64 v_fN))]

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:56.1-56.102 -/
opaque ibytes_ : forall (v_N : N) (v_iN : iN), (List byte) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:57.1-57.102 -/
opaque fbytes_ : forall (v_N : N) (v_fN : fN), (List byte) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:58.1-58.75 -/
opaque bytes_ : forall (v_valtype : valtype) (v_val_ : val_), (List byte) := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:60.1-60.75 -/
opaque inv_ibytes_ : forall (v_N : N) (var_0 : (List byte)), iN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:61.1-61.75 -/
opaque inv_fbytes_ : forall (v_N : N) (var_0 : (List byte)), fN := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:62.1-62.73 -/
opaque inv_bytes_ : forall (v_valtype : valtype) (var_0 : (List byte)), val_ := opaqueDef

/- Axiom Definition at: ../specification/wasm-1.0/3-numerics.spectec:78.1-78.29 -/
opaque inot_ : forall (v_N : N) (v_iN : iN), iN := opaqueDef

/- Auxiliary Definition at: ../specification/wasm-1.0/3-numerics.spectec:90.1-90.27 -/
def inez_ : ∀  (v_N : N) (v_iN : iN) , u32
  | v_N, i_1 =>
    (.mk_uN (nat_of_bool ((proj_uN_0 i_1) != 0)))


/- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:5.1-5.39 -/
abbrev addr : Type := Nat

/- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:6.1-6.53 -/
abbrev funcaddr : Type := addr

/- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:7.1-7.53 -/
abbrev globaladdr : Type := addr

/- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:8.1-8.51 -/
abbrev tableaddr : Type := addr

/- Type Alias Definition at: ../specification/wasm-1.0/4-runtime.spectec:9.1-9.50 -/
abbrev memaddr : Type := addr

/- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:20.1-21.70 -/
inductive externaddr : Type where
  | FUNC (v_funcaddr : funcaddr) : externaddr
  | GLOBAL (v_globaladdr : globaladdr) : externaddr
  | TABLE (v_tableaddr : tableaddr) : externaddr
  | MEM (v_memaddr : memaddr) : externaddr
deriving Inhabited, BEq


/- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:32.1-33.55 -/
inductive val : Type where
  | CONST (v_valtype : valtype) (v_val_ : val_) : val
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:32.8-32.11 -/
inductive wf_val : val -> Prop where
  | val_case_0 : forall (v_valtype : valtype) (v_val_ : val_),
    (wf_val_ v_valtype v_val_) ->
    wf_val (.CONST v_valtype v_val_)

/- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:35.1-36.22 -/
inductive result : Type where
  | _VALS (val_lst : (List val)) : result
  | TRAP : result
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:35.8-35.14 -/
inductive wf_result : result -> Prop where
  | result_case_0 : forall (val_lst : (List val)),
    Forall (fun (v_val : val) => (wf_val v_val)) val_lst ->
    wf_result (._VALS val_lst)
  | result_case_1 : wf_result .TRAP

/- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:61.1-63.22 -/
structure exportinst where MKexportinst ::
  NAME : name
  ADDR : externaddr
deriving Inhabited, BEq

def _append_exportinst (arg1 arg2 : (exportinst)) : exportinst where
  NAME := arg1.NAME /- FIXME - Non-trivial append -/
  ADDR := arg1.ADDR /- FIXME - Non-trivial append -/
instance : Append exportinst where
  append arg1 arg2 := _append_exportinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:61.8-61.18 -/
inductive wf_exportinst : exportinst -> Prop where
  | exportinst_case_ : forall (var_0 : name) (var_1 : externaddr),
    (wf_name var_0) ->
    wf_exportinst { NAME := var_0, ADDR := var_1 }

/- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:65.1-71.26 -/
structure moduleinst where MKmoduleinst ::
  TYPES : (List functype)
  FUNCS : (List funcaddr)
  GLOBALS : (List globaladdr)
  TABLES : (List tableaddr)
  MEMS : (List memaddr)
  EXPORTS : (List exportinst)
deriving Inhabited, BEq

def _append_moduleinst (arg1 arg2 : (moduleinst)) : moduleinst where
  TYPES := arg1.TYPES ++ arg2.TYPES
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  TABLES := arg1.TABLES ++ arg2.TABLES
  MEMS := arg1.MEMS ++ arg2.MEMS
  EXPORTS := arg1.EXPORTS ++ arg2.EXPORTS
instance : Append moduleinst where
  append arg1 arg2 := _append_moduleinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:65.8-65.18 -/
inductive wf_moduleinst : moduleinst -> Prop where
  | moduleinst_case_ : forall (var_0 : (List functype)) (var_1 : (List funcaddr)) (var_2 : (List globaladdr)) (var_3 : (List tableaddr)) (var_4 : (List memaddr)) (var_5 : (List exportinst)),
    Forall (fun (var_5 : exportinst) => (wf_exportinst var_5)) var_5 ->
    wf_moduleinst { TYPES := var_0, FUNCS := var_1, GLOBALS := var_2, TABLES := var_3, MEMS := var_4, EXPORTS := var_5 }

/- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:48.1-51.16 -/
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



/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:48.8-48.16 -/
inductive wf_funcinst : funcinst -> Prop where
  | funcinst_case_ : forall (var_0 : functype) (var_1 : moduleinst) (var_2 : func),
    (wf_moduleinst var_1) ->
    (wf_func var_2) ->
    wf_funcinst { TYPE := var_0, MODULE := var_1, CODE := var_2 }

/- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:52.1-54.16 -/
structure globalinst where MKglobalinst ::
  TYPE : globaltype
  VALUE : val
deriving Inhabited, BEq

def _append_globalinst (arg1 arg2 : (globalinst)) : globalinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  VALUE := arg1.VALUE /- FIXME - Non-trivial append -/
instance : Append globalinst where
  append arg1 arg2 := _append_globalinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:52.8-52.18 -/
inductive wf_globalinst : globalinst -> Prop where
  | globalinst_case_ : forall (var_0 : globaltype) (var_1 : val),
    (wf_val var_1) ->
    wf_globalinst { TYPE := var_0, VALUE := var_1 }

/- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:55.1-57.24 -/
structure tableinst where MKtableinst ::
  TYPE : tabletype
  REFS : (List (Option funcaddr))
deriving Inhabited, BEq

def _append_tableinst (arg1 arg2 : (tableinst)) : tableinst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  REFS := arg1.REFS ++ arg2.REFS
instance : Append tableinst where
  append arg1 arg2 := _append_tableinst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:55.8-55.17 -/
inductive wf_tableinst : tableinst -> Prop where
  | tableinst_case_ : forall (var_0 : tabletype) (var_1 : (List (Option funcaddr))),
    (wf_limits var_0) ->
    wf_tableinst { TYPE := var_0, REFS := var_1 }

/- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:58.1-60.18 -/
structure meminst where MKmeminst ::
  TYPE : memtype
  BYTES : (List byte)
deriving Inhabited, BEq

def _append_meminst (arg1 arg2 : (meminst)) : meminst where
  TYPE := arg1.TYPE /- FIXME - Non-trivial append -/
  BYTES := arg1.BYTES ++ arg2.BYTES
instance : Append meminst where
  append arg1 arg2 := _append_meminst arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:58.8-58.15 -/
inductive wf_meminst : meminst -> Prop where
  | meminst_case_ : forall (var_0 : memtype) (var_1 : (List byte)),
    (wf_limits var_0) ->
    Forall (fun (var_1 : byte) => (wf_byte var_1)) var_1 ->
    wf_meminst { TYPE := var_0, BYTES := var_1 }

/- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:83.1-87.20 -/
structure store where MKstore ::
  FUNCS : (List funcinst)
  GLOBALS : (List globalinst)
  TABLES : (List tableinst)
  MEMS : (List meminst)
deriving Inhabited, BEq

def _append_store (arg1 arg2 : (store)) : store where
  FUNCS := arg1.FUNCS ++ arg2.FUNCS
  GLOBALS := arg1.GLOBALS ++ arg2.GLOBALS
  TABLES := arg1.TABLES ++ arg2.TABLES
  MEMS := arg1.MEMS ++ arg2.MEMS
instance : Append store where
  append arg1 arg2 := _append_store arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:83.8-83.13 -/
inductive wf_store : store -> Prop where
  | store_case_ : forall (var_0 : (List funcinst)) (var_1 : (List globalinst)) (var_2 : (List tableinst)) (var_3 : (List meminst)),
    Forall (fun (var_0 : funcinst) => (wf_funcinst var_0)) var_0 ->
    Forall (fun (var_1 : globalinst) => (wf_globalinst var_1)) var_1 ->
    Forall (fun (var_2 : tableinst) => (wf_tableinst var_2)) var_2 ->
    Forall (fun (var_3 : meminst) => (wf_meminst var_3)) var_3 ->
    wf_store { FUNCS := var_0, GLOBALS := var_1, TABLES := var_2, MEMS := var_3 }

/- Record Creation Definition at: ../specification/wasm-1.0/4-runtime.spectec:89.1-91.24 -/
structure frame where MKframe ::
  LOCALS : (List val)
  MODULE : moduleinst
deriving Inhabited, BEq

def _append_frame (arg1 arg2 : (frame)) : frame where
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
  MODULE := arg1.MODULE ++ arg2.MODULE
instance : Append frame where
  append arg1 arg2 := _append_frame arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:89.8-89.13 -/
inductive wf_frame : frame -> Prop where
  | frame_case_ : forall (var_0 : (List val)) (var_1 : moduleinst),
    Forall (fun (var_0 : val) => (wf_val var_0)) var_0 ->
    (wf_moduleinst var_1) ->
    wf_frame { LOCALS := var_0, MODULE := var_1 }

/- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:93.1-93.47 -/
inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:93.8-93.13 -/
inductive wf_state : state -> Prop where
  | state_case_0 : forall (v_store : store) (v_frame : frame),
    (wf_store v_store) ->
    (wf_frame v_frame) ->
    wf_state (.mk_state v_store v_frame)

/- Recursive Definition at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 -/
/- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:105.1-110.9 -/
inductive admininstr : Type where
  | NOP : admininstr
  | UNREACHABLE : admininstr
  | DROP : admininstr
  | SELECT : admininstr
  | BLOCK (v_blocktype : blocktype) (instr_lst : (List instr)) : admininstr
  | LOOP (v_blocktype : blocktype) (instr_lst : (List instr)) : admininstr
  | IFELSE (v_blocktype : blocktype) (instr_lst : (List instr)) (_ : (List instr)) : admininstr
  | BR (v_labelidx : labelidx) : admininstr
  | BR_IF (v_labelidx : labelidx) : admininstr
  | BR_TABLE (labelidx_lst : (List labelidx)) (_ : labelidx) : admininstr
  | CALL (v_funcidx : funcidx) : admininstr
  | CALL_INDIRECT (v_typeidx : typeidx) : admininstr
  | RETURN : admininstr
  | CONST (v_valtype : valtype) (v_val_ : val_) : admininstr
  | UNOP (v_valtype : valtype) (v_unop_ : unop_) : admininstr
  | BINOP (v_valtype : valtype) (v_binop_ : binop_) : admininstr
  | TESTOP (v_valtype : valtype) (v_testop_ : testop_) : admininstr
  | RELOP (v_valtype : valtype) (v_relop_ : relop_) : admininstr
  | CVTOP (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : admininstr
  | LOCAL_GET (v_localidx : localidx) : admininstr
  | LOCAL_SET (v_localidx : localidx) : admininstr
  | LOCAL_TEE (v_localidx : localidx) : admininstr
  | GLOBAL_GET (v_globalidx : globalidx) : admininstr
  | GLOBAL_SET (v_globalidx : globalidx) : admininstr
  | LOAD (v_valtype : valtype) (loadop__opt : (Option loadop_)) (v_memarg : memarg) : admininstr
  | STORE (v_valtype : valtype) (sz_opt : (Option sz)) (v_memarg : memarg) : admininstr
  | MEMORY_SIZE : admininstr
  | MEMORY_GROW : admininstr
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
  | .SELECT =>
    .SELECT
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
  | (.CALL_INDIRECT x0) =>
    (.CALL_INDIRECT x0)
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
  | (.LOAD x0 x1 x2) =>
    (.LOAD x0 x1 x2)
  | (.STORE x0 x1 x2) =>
    (.STORE x0 x1 x2)
  | .MEMORY_SIZE =>
    .MEMORY_SIZE
  | .MEMORY_GROW =>
    .MEMORY_GROW


/- Auxiliary Definition at:  -/
def admininstr_val : ∀  (var_0 : val) , admininstr
  | (.CONST x0 x1) =>
    (.CONST x0 x1)


/- Inductive Type Definition at: ../specification/wasm-1.0/4-runtime.spectec:94.1-94.62 -/
inductive config : Type where
  | mk_config (v_state : state) (admininstr_lst : (List admininstr)) : config
deriving Inhabited, BEq


/- Inductive Relations Definition at: ../specification/wasm-1.0/4-runtime.spectec:94.8-94.14 -/
inductive wf_config : config -> Prop where
  | config_case_0 : forall (v_state : state) (admininstr_lst : (List admininstr)),
    (wf_state v_state) ->
    Forall (fun (v_admininstr : admininstr) => (wf_admininstr v_admininstr)) admininstr_lst ->
    wf_config (.mk_config v_state admininstr_lst)

/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:7.1-7.29 -/
def default_ : ∀  (v_valtype : valtype) , val
  | .I32 =>
    (.CONST .I32 (.mk_val__0 .I32 (.mk_uN 0)))
  | .I64 =>
    (.CONST .I64 (.mk_val__0 .I64 (.mk_uN 0)))
  | .F32 =>
    (.CONST .F32 (.mk_val__1 .F32 (fzero 32)))
  | .F64 =>
    (.CONST .F64 (.mk_val__1 .F64 (fzero 64)))


/- Recursive Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:17.1-17.63 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:17.6-17.14 -/
inductive fun_funcsxa : (List externaddr) -> (List funcaddr) -> Prop where
  | fun_funcsxa_case_0 : fun_funcsxa [] []
  | fun_funcsxa_case_1 : forall (fa : Nat) (xv_lst : (List externaddr)) (var_0 : (List funcaddr)),
    (fun_funcsxa xv_lst var_0) ->
    fun_funcsxa ([(.FUNC fa)] ++ xv_lst) ([fa] ++ var_0)
  | fun_funcsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (List externaddr)) (var_0 : (List funcaddr)),
    (fun_funcsxa xv_lst var_0) ->
    fun_funcsxa ([v_externaddr] ++ xv_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:18.1-18.65 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:18.6-18.16 -/
inductive fun_globalsxa : (List externaddr) -> (List globaladdr) -> Prop where
  | fun_globalsxa_case_0 : fun_globalsxa [] []
  | fun_globalsxa_case_1 : forall (ga : Nat) (xv_lst : (List externaddr)) (var_0 : (List globaladdr)),
    (fun_globalsxa xv_lst var_0) ->
    fun_globalsxa ([(.GLOBAL ga)] ++ xv_lst) ([ga] ++ var_0)
  | fun_globalsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (List externaddr)) (var_0 : (List globaladdr)),
    (fun_globalsxa xv_lst var_0) ->
    fun_globalsxa ([v_externaddr] ++ xv_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:19.1-19.64 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:19.6-19.15 -/
inductive fun_tablesxa : (List externaddr) -> (List tableaddr) -> Prop where
  | fun_tablesxa_case_0 : fun_tablesxa [] []
  | fun_tablesxa_case_1 : forall (ta : Nat) (xv_lst : (List externaddr)) (var_0 : (List tableaddr)),
    (fun_tablesxa xv_lst var_0) ->
    fun_tablesxa ([(.TABLE ta)] ++ xv_lst) ([ta] ++ var_0)
  | fun_tablesxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (List externaddr)) (var_0 : (List tableaddr)),
    (fun_tablesxa xv_lst var_0) ->
    fun_tablesxa ([v_externaddr] ++ xv_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:20.1-20.62 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:20.6-20.13 -/
inductive fun_memsxa : (List externaddr) -> (List memaddr) -> Prop where
  | fun_memsxa_case_0 : fun_memsxa [] []
  | fun_memsxa_case_1 : forall (ma : Nat) (xv_lst : (List externaddr)) (var_0 : (List memaddr)),
    (fun_memsxa xv_lst var_0) ->
    fun_memsxa ([(.MEM ma)] ++ xv_lst) ([ma] ++ var_0)
  | fun_memsxa_case_2 : forall (v_externaddr : externaddr) (xv_lst : (List externaddr)) (var_0 : (List memaddr)),
    (fun_memsxa xv_lst var_0) ->
    fun_memsxa ([v_externaddr] ++ xv_lst) var_0

/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:46.1-46.57 -/
def fun_store : ∀  (v_state : state) , store
  | (.mk_state s f) =>
    s


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:47.1-47.57 -/
def fun_frame : ∀  (v_state : state) , frame
  | (.mk_state s f) =>
    f


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:53.1-53.64 -/
def fun_funcaddr : ∀  (v_state : state) , (List funcaddr)
  | (.mk_state s f) =>
    ((f.MODULE).FUNCS)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:56.1-56.57 -/
def fun_funcinst : ∀  (v_state : state) , (List funcinst)
  | (.mk_state s f) =>
    (s.FUNCS)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:57.1-57.59 -/
def fun_globalinst : ∀  (v_state : state) , (List globalinst)
  | (.mk_state s f) =>
    (s.GLOBALS)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:58.1-58.58 -/
def fun_tableinst : ∀  (v_state : state) , (List tableinst)
  | (.mk_state s f) =>
    (s.TABLES)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:59.1-59.56 -/
def fun_meminst : ∀  (v_state : state) , (List meminst)
  | (.mk_state s f) =>
    (s.MEMS)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:60.1-60.58 -/
def fun_moduleinst : ∀  (v_state : state) , moduleinst
  | (.mk_state s f) =>
    (f.MODULE)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:68.1-68.66 -/
def fun_type : ∀  (v_state : state) (v_typeidx : typeidx) , functype
  | (.mk_state s f), x =>
    (((f.MODULE).TYPES)[(proj_uN_0 x)]!)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:69.1-69.66 -/
def fun_func : ∀  (v_state : state) (v_funcidx : funcidx) , funcinst
  | (.mk_state s f), x =>
    ((s.FUNCS)[(((f.MODULE).FUNCS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:70.1-70.68 -/
def fun_global : ∀  (v_state : state) (v_globalidx : globalidx) , globalinst
  | (.mk_state s f), x =>
    ((s.GLOBALS)[(((f.MODULE).GLOBALS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:71.1-71.67 -/
def fun_table : ∀  (v_state : state) (v_tableidx : tableidx) , tableinst
  | (.mk_state s f), x =>
    ((s.TABLES)[(((f.MODULE).TABLES)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:72.1-72.65 -/
def fun_mem : ∀  (v_state : state) (v_memidx : memidx) , meminst
  | (.mk_state s f), x =>
    ((s.MEMS)[(((f.MODULE).MEMS)[(proj_uN_0 x)]!)]!)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:73.1-73.67 -/
def fun_local : ∀  (v_state : state) (v_localidx : localidx) , val
  | (.mk_state s f), x =>
    ((f.LOCALS)[(proj_uN_0 x)]!)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:85.1-85.89 -/
def with_local : ∀  (v_state : state) (v_localidx : localidx) (v_val : val) , state
  | (.mk_state s f), x, v =>
    (.mk_state s (f <| LOCALS := (List.modify (f.LOCALS) (proj_uN_0 x) (fun (_ : val) => v)) |>))


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:86.1-86.96 -/
def with_global : ∀  (v_state : state) (v_globalidx : globalidx) (v_val : val) , state
  | (.mk_state s f), x, v =>
    (.mk_state (s <| GLOBALS := (list_update_func (s.GLOBALS) (((f.MODULE).GLOBALS)[(proj_uN_0 x)]!) (fun (var_1 : globalinst) => (var_1 <| VALUE := v |>))) |>) f)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:87.1-87.97 -/
def with_table : ∀  (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_funcaddr : funcaddr) , state
  | (.mk_state s f), x, i, a =>
    (.mk_state (s <| TABLES := (list_update_func (s.TABLES) (((f.MODULE).TABLES)[(proj_uN_0 x)]!) (fun (var_1 : tableinst) => (var_1 <| REFS := (List.modify (var_1.REFS) i (fun (_ : (Option funcaddr)) => (some a))) |>))) |>) f)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:88.1-88.89 -/
def with_tableinst : ∀  (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) , state
  | (.mk_state s f), x, ti =>
    (.mk_state (s <| TABLES := (List.modify (s.TABLES) (((f.MODULE).TABLES)[(proj_uN_0 x)]!) (fun (_ : tableinst) => ti)) |>) f)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:89.1-89.100 -/
def with_mem : ∀  (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0 : (List byte)) , state
  | (.mk_state s f), x, i, j, b_lst =>
    (.mk_state (s <| MEMS := (list_update_func (s.MEMS) (((f.MODULE).MEMS)[(proj_uN_0 x)]!) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (var_1.BYTES) i j b_lst) |>))) |>) f)


/- Auxiliary Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:90.1-90.87 -/
def with_meminst : ∀  (v_state : state) (v_memidx : memidx) (v_meminst : meminst) , state
  | (.mk_state s f), x, mi =>
    (.mk_state (s <| MEMS := (List.modify (s.MEMS) (((f.MODULE).MEMS)[(proj_uN_0 x)]!) (fun (_ : meminst) => mi)) |>) f)


/- Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:102.6-102.16 -/
inductive fun_growtable : tableinst -> Nat -> (Option tableinst) -> Prop where
  | fun_growtable_case_0 : forall (ti : tableinst) (v_n : Nat) (ti' : tableinst) (i : uN) (j_opt : (Option u32)) (a_lst : (List addr)) (i' : Nat),
    (ti == { TYPE := (.mk_limits i j_opt), REFS := (List.map (fun (a : addr) => (some a)) a_lst) }) ->
    (i' == ((List.length a_lst) + v_n)) ->
    (ti' == { TYPE := (.mk_limits (.mk_uN i') j_opt), REFS := ((List.map (fun (a : addr) => (some a)) a_lst) ++ (List.replicate v_n none)) }) ->
    Forall (fun (j : u32) => (i' <= (proj_uN_0 j))) (Option.toList j_opt) ->
    fun_growtable ti v_n (some ti')
  | fun_growtable_case_1 : forall (x0 : tableinst) (x1 : Nat), fun_growtable x0 x1 none

/- Inductive Relations Definition at: ../specification/wasm-1.0/5-runtime-aux.spectec:103.6-103.17 -/
inductive fun_growmemory : meminst -> Nat -> (Option meminst) -> Prop where
  | fun_growmemory_case_0 : forall (mi : meminst) (v_n : Nat) (mi' : meminst) (i : uN) (j_opt : (Option u32)) (b_lst : (List byte)) (i' : Nat),
    (mi == { TYPE := (.mk_limits i j_opt), BYTES := b_lst }) ->
    (i' == ((((List.length b_lst) : Nat) / ((64 * (Ki )) : Nat)) + (v_n : Nat))) ->
    (mi' == { TYPE := (.mk_limits (.mk_uN (i' : Nat)) j_opt), BYTES := (b_lst ++ (List.replicate (v_n * (64 * (Ki ))) (.mk_byte 0))) }) ->
    Forall (fun (j : u32) => (i' <= ((proj_uN_0 j) : Nat))) (Option.toList j_opt) ->
    fun_growmemory mi v_n (some mi')
  | fun_growmemory_case_1 : forall (x0 : meminst) (x1 : Nat), fun_growmemory x0 x1 none

/- Record Creation Definition at: ../specification/wasm-1.0/6-typing.spectec:5.1-8.62 -/
structure context where MKcontext ::
  TYPES : (List functype)
  FUNCS : (List functype)
  GLOBALS : (List globaltype)
  TABLES : (List tabletype)
  MEMS : (List memtype)
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
  LOCALS := arg1.LOCALS ++ arg2.LOCALS
  LABELS := arg1.LABELS ++ arg2.LABELS
  RETURN := arg1.RETURN ++ arg2.RETURN
instance : Append context where
  append arg1 arg2 := _append_context arg1 arg2



/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:5.8-5.15 -/
inductive wf_context : context -> Prop where
  | context_case_ : forall (var_0 : (List functype)) (var_1 : (List functype)) (var_2 : (List globaltype)) (var_3 : (List tabletype)) (var_4 : (List memtype)) (var_5 : (List valtype)) (var_6 : (List resulttype)) (var_7 : (Option resulttype)),
    Forall (fun (var_3 : tabletype) => (wf_limits var_3)) var_3 ->
    Forall (fun (var_4 : memtype) => (wf_limits var_4)) var_4 ->
    wf_context { TYPES := var_0, FUNCS := var_1, GLOBALS := var_2, TABLES := var_3, MEMS := var_4, LOCALS := var_5, LABELS := var_6, RETURN := var_7 }

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:18.1-18.66 -/
inductive Limits_ok : limits -> Nat -> Prop where
  | mk_Limits_ok : forall (v_n : n) (m_opt : (Option m)) (k : Nat),
    (v_n <= k) ->
    Forall (fun (v_m : Nat) => ((v_n <= v_m) && (v_m <= k))) (Option.toList m_opt) ->
    Limits_ok (.mk_limits (.mk_uN v_n) (Option.map (fun (v_m : m) => (.mk_uN v_m)) m_opt)) k

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:19.1-19.64 -/
inductive Functype_ok : functype -> Prop where
  | mk_Functype_ok : forall (t_1_lst : (List valtype)) (t_2_opt : (Option valtype)), Functype_ok (.mk_functype t_1_lst (Option.toList t_2_opt))

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:20.1-20.66 -/
inductive Globaltype_ok : globaltype -> Prop where
  | mk_Globaltype_ok : forall (t : valtype), Globaltype_ok (.mk_globaltype (some .MUT) t)

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:21.1-21.65 -/
inductive Tabletype_ok : tabletype -> Prop where
  | mk_Tabletype_ok : forall (v_limits : limits),
    (Limits_ok v_limits ((((2 ^ 32) : Nat) - (1 : Nat)) : Nat)) ->
    Tabletype_ok v_limits

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:22.1-22.63 -/
inductive Memtype_ok : memtype -> Prop where
  | mk_Memtype_ok : forall (v_limits : limits),
    (Limits_ok v_limits (2 ^ 16)) ->
    Memtype_ok v_limits

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:23.1-23.66 -/
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

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:70.1-70.75 -/
inductive Limits_sub : limits -> limits -> Prop where
  | mk_Limits_sub : forall (n_11 : n) (n_12 : n) (n_21 : n) (n_22 : n),
    (n_11 >= n_21) ->
    (n_12 <= n_22) ->
    Limits_sub (.mk_limits (.mk_uN n_11) (some (.mk_uN n_12))) (.mk_limits (.mk_uN n_21) (some (.mk_uN n_22)))

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:71.1-71.73 -/
inductive Functype_sub : functype -> functype -> Prop where
  | mk_Functype_sub : forall (ft : functype), Functype_sub ft ft

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:72.1-72.75 -/
inductive Globaltype_sub : globaltype -> globaltype -> Prop where
  | mk_Globaltype_sub : forall (gt : globaltype), Globaltype_sub gt gt

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:73.1-73.74 -/
inductive Tabletype_sub : tabletype -> tabletype -> Prop where
  | mk_Tabletype_sub : forall (lim_1 : limits) (lim_2 : limits),
    (Limits_sub lim_1 lim_2) ->
    Tabletype_sub lim_1 lim_2

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:74.1-74.72 -/
inductive Memtype_sub : memtype -> memtype -> Prop where
  | mk_Memtype_sub : forall (lim_1 : limits) (lim_2 : limits),
    (Limits_sub lim_1 lim_2) ->
    Memtype_sub lim_1 lim_2

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:75.1-75.75 -/
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

/- Recursive Definitions at: ../specification/wasm-1.0/6-typing.spectec:120.1-121.65 -/
mutual
/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:120.1-120.64 -/
inductive Instr_ok : context -> instr -> functype -> Prop where
  | nop : forall (C : context), Instr_ok C .NOP (.mk_functype [] [])
  | unreachable : forall (C : context) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)), Instr_ok C .UNREACHABLE (.mk_functype t_1_lst t_2_lst)
  | drop : forall (C : context) (t : valtype), Instr_ok C .DROP (.mk_functype [t] [])
  | select : forall (C : context) (t : valtype), Instr_ok C .SELECT (.mk_functype [t, t, .I32] [t])
  | block : forall (C : context) (t_opt : (Option valtype)) (instr_lst : (List instr)),
    (Instrs_ok ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], LOCALS := [], LABELS := [t_opt], RETURN := none } ++ C) instr_lst (.mk_functype [] (Option.toList t_opt))) ->
    Instr_ok C (.BLOCK t_opt instr_lst) (.mk_functype [] (Option.toList t_opt))
  | loop : forall (C : context) (t_opt : (Option valtype)) (instr_lst : (List instr)),
    (Instrs_ok ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], LOCALS := [], LABELS := [], RETURN := none } ++ C) instr_lst (.mk_functype [] [])) ->
    Instr_ok C (.LOOP t_opt instr_lst) (.mk_functype [] (Option.toList t_opt))
  | if : forall (C : context) (t_opt : (Option valtype)) (instr_1_lst : (List instr)) (instr_2_lst : (List instr)),
    (Instrs_ok ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], LOCALS := [], LABELS := [t_opt], RETURN := none } ++ C) instr_1_lst (.mk_functype [] (Option.toList t_opt))) ->
    (Instrs_ok ({ TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], LOCALS := [], LABELS := [t_opt], RETURN := none } ++ C) instr_2_lst (.mk_functype [] (Option.toList t_opt))) ->
    Instr_ok C (.IFELSE t_opt instr_1_lst instr_2_lst) (.mk_functype [.I32] (Option.toList t_opt))
  | br : forall (C : context) (l : labelidx) (t_1_lst : (List valtype)) (t_opt : (Option valtype)) (t_2_lst : (List valtype)),
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (((C.LABELS)[(proj_uN_0 l)]!) == t_opt) ->
    Instr_ok C (.BR l) (.mk_functype (t_1_lst ++ (Option.toList t_opt)) t_2_lst)
  | br_if : forall (C : context) (l : labelidx) (t_opt : (Option valtype)),
    ((proj_uN_0 l) < (List.length (C.LABELS))) ->
    (((C.LABELS)[(proj_uN_0 l)]!) == t_opt) ->
    Instr_ok C (.BR_IF l) (.mk_functype ((Option.toList t_opt) ++ [.I32]) (Option.toList t_opt))
  | br_table : forall (C : context) (l_lst : (List labelidx)) (l' : labelidx) (t_1_lst : (List valtype)) (t_opt : (Option valtype)) (t_2_lst : (List valtype)),
    ((proj_uN_0 l') < (List.length (C.LABELS))) ->
    (t_opt == ((C.LABELS)[(proj_uN_0 l')]!)) ->
    Forall (fun (l : labelidx) => ((proj_uN_0 l) < (List.length (C.LABELS)))) l_lst ->
    Forall (fun (l : labelidx) => (t_opt == ((C.LABELS)[(proj_uN_0 l)]!))) l_lst ->
    Instr_ok C (.BR_TABLE l_lst l') (.mk_functype (t_1_lst ++ ((Option.toList t_opt) ++ [.I32])) t_2_lst)
  | call : forall (C : context) (x : idx) (t_1_lst : (List valtype)) (t_2_opt : (Option valtype)),
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == (.mk_functype t_1_lst (Option.toList t_2_opt))) ->
    Instr_ok C (.CALL x) (.mk_functype t_1_lst (Option.toList t_2_opt))
  | call_indirect : forall (C : context) (x : idx) (t_1_lst : (List valtype)) (t_2_opt : (Option valtype)),
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (((C.TYPES)[(proj_uN_0 x)]!) == (.mk_functype t_1_lst (Option.toList t_2_opt))) ->
    Instr_ok C (.CALL_INDIRECT x) (.mk_functype (t_1_lst ++ [.I32]) (Option.toList t_2_opt))
  | return : forall (C : context) (t_1_lst : (List valtype)) (t_opt : (Option valtype)) (t_2_lst : (List valtype)),
    ((C.RETURN) == (some t_opt)) ->
    Instr_ok C .RETURN (.mk_functype (t_1_lst ++ (Option.toList t_opt)) t_2_lst)
  | const : forall (C : context) (t : valtype) (c_t : val_),
    (wf_val_ t c_t) ->
    Instr_ok C (.CONST t c_t) (.mk_functype [] [t])
  | unop : forall (C : context) (t : valtype) (unop_t : unop_),
    (wf_unop_ t unop_t) ->
    Instr_ok C (.UNOP t unop_t) (.mk_functype [t] [t])
  | binop : forall (C : context) (t : valtype) (binop_t : binop_),
    (wf_binop_ t binop_t) ->
    Instr_ok C (.BINOP t binop_t) (.mk_functype [t, t] [t])
  | testop : forall (C : context) (t : valtype) (testop_t : testop_),
    (wf_testop_ t testop_t) ->
    Instr_ok C (.TESTOP t testop_t) (.mk_functype [t] [.I32])
  | relop : forall (C : context) (t : valtype) (relop_t : relop_),
    (wf_relop_ t relop_t) ->
    Instr_ok C (.RELOP t relop_t) (.mk_functype [t, t] [.I32])
  | cvtop_reinterpret : forall (C : context) (nt_1 : valtype) (nt_2 : valtype),
    ((size nt_1) == (size nt_2)) ->
    Instr_ok C (.CVTOP nt_1 nt_2 .REINTERPRET) (.mk_functype [nt_2] [nt_1])
  | cvtop_convert : forall (C : context) (nt_1 : valtype) (nt_2 : valtype) (v_cvtop : cvtop), Instr_ok C (.CVTOP nt_1 nt_2 v_cvtop) (.mk_functype [nt_2] [nt_1])
  | local_get : forall (C : context) (x : idx) (t : valtype),
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == t) ->
    Instr_ok C (.LOCAL_GET x) (.mk_functype [] [t])
  | local_set : forall (C : context) (x : idx) (t : valtype),
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == t) ->
    Instr_ok C (.LOCAL_SET x) (.mk_functype [t] [])
  | local_tee : forall (C : context) (x : idx) (t : valtype),
    ((proj_uN_0 x) < (List.length (C.LOCALS))) ->
    (((C.LOCALS)[(proj_uN_0 x)]!) == t) ->
    Instr_ok C (.LOCAL_TEE x) (.mk_functype [t] [t])
  | global_get : forall (C : context) (x : idx) (t : valtype) (v_mut : «mut»),
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype v_mut t)) ->
    Instr_ok C (.GLOBAL_GET x) (.mk_functype [] [t])
  | global_set : forall (C : context) (x : idx) (t : valtype),
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype (some .MUT) t)) ->
    Instr_ok C (.GLOBAL_SET x) (.mk_functype [t] [])
  | memory_size : forall (C : context) (mt : memtype),
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    Instr_ok C .MEMORY_SIZE (.mk_functype [] [.I32])
  | memory_grow : forall (C : context) (mt : memtype),
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    Instr_ok C .MEMORY_GROW (.mk_functype [.I32] [.I32])
  | load_val : forall (C : context) (t : valtype) (v_memarg : memarg) (mt : memtype),
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= (((size t) : Nat) / (8 : Nat))) ->
    Instr_ok C (.LOAD t none v_memarg) (.mk_functype [.I32] [t])
  | load_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (v_memarg : memarg) (mt : memtype),
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= ((v_M : Nat) / (8 : Nat))) ->
    Instr_ok C (.LOAD (valtype_Inn v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_M) v_sx))) v_memarg) (.mk_functype [.I32] [(valtype_Inn v_Inn)])
  | store_val : forall (C : context) (t : valtype) (v_memarg : memarg) (mt : memtype),
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= (((size t) : Nat) / (8 : Nat))) ->
    Instr_ok C (.STORE t none v_memarg) (.mk_functype [.I32, t] [])
  | store_pack : forall (C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (mt : memtype),
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == mt) ->
    (((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Nat) <= ((v_M : Nat) / (8 : Nat))) ->
    Instr_ok C (.STORE (valtype_Inn v_Inn) (some (.mk_sz v_M)) v_memarg) (.mk_functype [.I32, (valtype_Inn v_Inn)] [])

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:121.1-121.65 -/
inductive Instrs_ok : context -> (List instr) -> functype -> Prop where
  | empty : forall (C : context), Instrs_ok C [] (.mk_functype [] [])
  | seq : forall (C : context) (instr_1 : instr) (instr_2_lst : (List instr)) (t_1_lst : (List valtype)) (t_3_lst : (List valtype)) (t_2_lst : (List valtype)),
    (Instr_ok C instr_1 (.mk_functype t_1_lst t_2_lst)) ->
    (Instrs_ok C instr_2_lst (.mk_functype t_2_lst t_3_lst)) ->
    Instrs_ok C ([instr_1] ++ instr_2_lst) (.mk_functype t_1_lst t_3_lst)
  | frame : forall (C : context) (instr_lst : (List instr)) (t_lst : (List valtype)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)),
    (Instrs_ok C instr_lst (.mk_functype t_1_lst t_2_lst)) ->
    Instrs_ok C instr_lst (.mk_functype (t_lst ++ t_1_lst) (t_lst ++ t_2_lst))

end

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:122.1-122.69 -/
inductive Expr_ok : context -> expr -> resulttype -> Prop where
  | mk_Expr_ok : forall (C : context) (instr_lst : (List instr)) (t_opt : (Option valtype)),
    (Instrs_ok C instr_lst (.mk_functype [] (Option.toList t_opt))) ->
    Expr_ok C instr_lst t_opt

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:315.1-315.79 -/
inductive Instr_const : context -> instr -> Prop where
  | const : forall (C : context) (t : valtype) (c : val_),
    (wf_val_ t c) ->
    Instr_const C (.CONST t c)
  | global_get : forall (C : context) (x : idx) (t : valtype),
    ((proj_uN_0 x) < (List.length (C.GLOBALS))) ->
    (((C.GLOBALS)[(proj_uN_0 x)]!) == (.mk_globaltype none t)) ->
    Instr_const C (.GLOBAL_GET x)

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:316.1-316.78 -/
inductive Expr_const : context -> expr -> Prop where
  | mk_Expr_const : forall (C : context) (instr_lst : (List instr)),
    Forall (fun (v_instr : instr) => (Instr_const C v_instr)) instr_lst ->
    Expr_const C instr_lst

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:317.1-317.79 -/
inductive Expr_ok_const : context -> expr -> (Option valtype) -> Prop where
  | mk_Expr_ok_const : forall (C : context) (v_expr : expr) (t_opt : (Option valtype)),
    (Expr_ok C v_expr t_opt) ->
    (Expr_const C v_expr) ->
    Expr_ok_const C v_expr t_opt

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:341.1-341.73 -/
inductive Type_ok : type -> functype -> Prop where
  | mk_Type_ok : forall (ft : functype),
    (Functype_ok ft) ->
    Type_ok (.TYPE ft) ft

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:342.1-342.73 -/
inductive Func_ok : context -> func -> functype -> Prop where
  | mk_Func_ok : forall (C : context) (x : idx) (t_lst : (List valtype)) (v_expr : expr) (t_1_lst : (List valtype)) (t_2_opt : (Option valtype)),
    ((proj_uN_0 x) < (List.length (C.TYPES))) ->
    (((C.TYPES)[(proj_uN_0 x)]!) == (.mk_functype t_1_lst (Option.toList t_2_opt))) ->
    (Expr_ok (C ++ { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], LOCALS := (t_1_lst ++ t_lst), LABELS := [t_2_opt], RETURN := (some t_2_opt) }) v_expr t_2_opt) ->
    Func_ok C (.FUNC x (List.map (fun (t : valtype) => (.LOCAL t)) t_lst) v_expr) (.mk_functype t_1_lst (Option.toList t_2_opt))

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:343.1-343.75 -/
inductive Global_ok : context -> global -> globaltype -> Prop where
  | mk_Global_ok : forall (C : context) (gt : globaltype) (v_expr : expr) (v_mut : «mut») (t : valtype),
    (Globaltype_ok gt) ->
    (gt == (.mk_globaltype v_mut t)) ->
    (Expr_ok_const C v_expr (some t)) ->
    Global_ok C (.GLOBAL gt v_expr) gt

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:344.1-344.74 -/
inductive Table_ok : context -> table -> tabletype -> Prop where
  | mk_Table_ok : forall (C : context) (tt : tabletype),
    (Tabletype_ok tt) ->
    Table_ok C (.TABLE tt) tt

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:345.1-345.72 -/
inductive Mem_ok : context -> mem -> memtype -> Prop where
  | mk_Mem_ok : forall (C : context) (mt : memtype),
    (Memtype_ok mt) ->
    Mem_ok C (.MEMORY mt) mt

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:346.1-346.73 -/
inductive Elem_ok : context -> elem -> Prop where
  | mk_Elem_ok : forall (C : context) (v_expr : expr) (x_lst : (List idx)) (lim : limits) (ft_lst : (List functype)),
    (0 < (List.length (C.TABLES))) ->
    (((C.TABLES)[0]!) == lim) ->
    (Expr_ok_const C v_expr (some .I32)) ->
    ((List.length ft_lst) == (List.length x_lst)) ->
    Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length (C.FUNCS)))) x_lst ->
    Forall₂ (fun (ft : functype) (x : idx) => (((C.FUNCS)[(proj_uN_0 x)]!) == ft)) ft_lst x_lst ->
    Elem_ok C (.ELEM v_expr x_lst)

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:347.1-347.73 -/
inductive Data_ok : context -> data -> Prop where
  | mk_Data_ok : forall (C : context) (v_expr : expr) (b_lst : (List byte)) (lim : limits),
    (0 < (List.length (C.MEMS))) ->
    (((C.MEMS)[0]!) == lim) ->
    (Expr_ok_const C v_expr (some .I32)) ->
    Data_ok C (.DATA v_expr b_lst)

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:348.1-348.74 -/
inductive Start_ok : context -> start -> Prop where
  | mk_Start_ok : forall (C : context) (x : idx),
    ((proj_uN_0 x) < (List.length (C.FUNCS))) ->
    (((C.FUNCS)[(proj_uN_0 x)]!) == (.mk_functype [] [])) ->
    Start_ok C (.START x)

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:396.1-396.80 -/
inductive Import_ok : context -> «import» -> externtype -> Prop where
  | mk_Import_ok : forall (C : context) (name_1 : name) (name_2 : name) (xt : externtype),
    (Externtype_ok xt) ->
    Import_ok C (.IMPORT name_1 name_2 xt) xt

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:398.1-398.83 -/
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

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:397.1-397.80 -/
inductive Export_ok : context -> «export» -> externtype -> Prop where
  | mk_Export_ok : forall (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype),
    (Externidx_ok C v_externidx xt) ->
    Export_ok C (.EXPORT v_name v_externidx) xt

/- Inductive Relations Definition at: ../specification/wasm-1.0/6-typing.spectec:428.1-428.62 -/
inductive Module_ok : module -> Prop where
  | mk_Module_ok : forall (type_lst : (List type)) (import_lst : (List «import»)) (func_lst : (List func)) (global_lst : (List global)) (table_lst : (List table)) (mem_lst : (List mem)) (elem_lst : (List elem)) (data_lst : (List data)) (start_opt : (Option start)) (export_lst : (List «export»)) (ft'_lst : (List functype)) (ixt_lst : (List externtype)) (C' : context) (gt_lst : (List globaltype)) (C : context) (ft_lst : (List functype)) (tt_lst : (List tabletype)) (mt_lst : (List memtype)) (xt_lst : (List externtype)) (ift_lst : (List functype)) (igt_lst : (List globaltype)) (itt_lst : (List tabletype)) (imt_lst : (List memtype)) (var_3 : (List memtype)) (var_2 : (List tabletype)) (var_1 : (List globaltype)) (var_0 : (List functype)),
    (fun_memsxt ixt_lst var_3) ->
    (fun_tablesxt ixt_lst var_2) ->
    (fun_globalsxt ixt_lst var_1) ->
    (fun_funcsxt ixt_lst var_0) ->
    ((List.length ft'_lst) == (List.length type_lst)) ->
    Forall₂ (fun (ft' : functype) (v_type : type) => (Type_ok v_type ft')) ft'_lst type_lst ->
    ((List.length import_lst) == (List.length ixt_lst)) ->
    Forall₂ (fun (v_import : «import») (ixt : externtype) => (Import_ok { TYPES := ft'_lst, FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], LOCALS := [], LABELS := [], RETURN := none } v_import ixt)) import_lst ixt_lst ->
    ((List.length global_lst) == (List.length gt_lst)) ->
    Forall₂ (fun (v_global : global) (gt : globaltype) => (Global_ok C' v_global gt)) global_lst gt_lst ->
    ((List.length ft_lst) == (List.length func_lst)) ->
    Forall₂ (fun (ft : functype) (v_func : func) => (Func_ok C v_func ft)) ft_lst func_lst ->
    ((List.length table_lst) == (List.length tt_lst)) ->
    Forall₂ (fun (v_table : table) (tt : tabletype) => (Table_ok C v_table tt)) table_lst tt_lst ->
    ((List.length mem_lst) == (List.length mt_lst)) ->
    Forall₂ (fun (v_mem : mem) (mt : memtype) => (Mem_ok C v_mem mt)) mem_lst mt_lst ->
    Forall (fun (v_elem : elem) => (Elem_ok C v_elem)) elem_lst ->
    Forall (fun (v_data : data) => (Data_ok C v_data)) data_lst ->
    Forall (fun (v_start : start) => (Start_ok C v_start)) (Option.toList start_opt) ->
    ((List.length export_lst) == (List.length xt_lst)) ->
    Forall₂ (fun (v_export : «export») (xt : externtype) => (Export_ok C v_export xt)) export_lst xt_lst ->
    ((List.length tt_lst) <= 1) ->
    ((List.length mt_lst) <= 1) ->
    (C == { TYPES := ft'_lst, FUNCS := (ift_lst ++ ft_lst), GLOBALS := (igt_lst ++ gt_lst), TABLES := (itt_lst ++ tt_lst), MEMS := (imt_lst ++ mt_lst), LOCALS := [], LABELS := [], RETURN := none }) ->
    (C' == { TYPES := ft'_lst, FUNCS := (ift_lst ++ ft_lst), GLOBALS := igt_lst, TABLES := [], MEMS := [], LOCALS := [], LABELS := [], RETURN := none }) ->
    (ift_lst == var_0) ->
    (igt_lst == var_1) ->
    (itt_lst == var_2) ->
    (imt_lst == var_3) ->
    Module_ok (.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)

/- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:6.1-6.77 -/
inductive Step_pure : (List admininstr) -> (List admininstr) -> Prop where
  | unreachable : Step_pure [.UNREACHABLE] [.TRAP]
  | nop : Step_pure [.NOP] []
  | drop : forall (v_val : val), Step_pure [(admininstr_val v_val), .DROP] []
  | select_true : forall (val_1 : val) (val_2 : val) (c : val_),
    (wf_val_ .I32 c) ->
    ((proj_val__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_val__0 c))) != 0) ->
    Step_pure [(admininstr_val val_1), (admininstr_val val_2), (.CONST .I32 c), .SELECT] [(admininstr_val val_1)]
  | select_false : forall (val_1 : val) (val_2 : val) (c : val_),
    (wf_val_ .I32 c) ->
    ((proj_val__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_val__0 c))) == 0) ->
    Step_pure [(admininstr_val val_1), (admininstr_val val_2), (.CONST .I32 c), .SELECT] [(admininstr_val val_2)]
  | if_true : forall (c : val_) (t_opt : (Option valtype)) (instr_1_lst : (List instr)) (instr_2_lst : (List instr)),
    (wf_val_ .I32 c) ->
    ((proj_val__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_val__0 c))) != 0) ->
    Step_pure [(.CONST .I32 c), (.IFELSE t_opt instr_1_lst instr_2_lst)] [(.BLOCK t_opt instr_1_lst)]
  | if_false : forall (c : val_) (t_opt : (Option valtype)) (instr_1_lst : (List instr)) (instr_2_lst : (List instr)),
    (wf_val_ .I32 c) ->
    ((proj_val__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_val__0 c))) == 0) ->
    Step_pure [(.CONST .I32 c), (.IFELSE t_opt instr_1_lst instr_2_lst)] [(.BLOCK t_opt instr_2_lst)]
  | label_vals : forall (v_n : n) (instr_lst : (List instr)) (val_lst : (List val)), Step_pure [(.LABEL_ v_n instr_lst (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
  | br_zero : forall (v_n : n) (instr'_lst : (List instr)) (val'_lst : (List val)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([(.BR (.mk_uN 0))] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))))] ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ (List.map (fun (instr' : instr) => (admininstr_instr instr')) instr'_lst))
  | br_succ : forall (v_n : n) (instr'_lst : (List instr)) (val_lst : (List val)) (l : labelidx) (instr_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([(.BR (.mk_uN ((proj_uN_0 l) + 1)))] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))))] ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [(.BR l)])
  | br_if_true : forall (c : val_) (l : labelidx),
    (wf_val_ .I32 c) ->
    ((proj_val__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_val__0 c))) != 0) ->
    Step_pure [(.CONST .I32 c), (.BR_IF l)] [(.BR l)]
  | br_if_false : forall (c : val_) (l : labelidx),
    (wf_val_ .I32 c) ->
    ((proj_val__0 c) != none) ->
    ((proj_uN_0 (Option.get! (proj_val__0 c))) == 0) ->
    Step_pure [(.CONST .I32 c), (.BR_IF l)] []
  | br_table_lt : forall (i : val_) (l_lst : (List labelidx)) (l' : labelidx),
    ((proj_uN_0 (Option.get! (proj_val__0 i))) < (List.length l_lst)) ->
    ((proj_val__0 i) != none) ->
    (wf_val_ .I32 i) ->
    Step_pure [(.CONST .I32 i), (.BR_TABLE l_lst l')] [(.BR (l_lst[(proj_uN_0 (Option.get! (proj_val__0 i)))]!))]
  | br_table_ge : forall (i : val_) (l_lst : (List labelidx)) (l' : labelidx),
    (wf_val_ .I32 i) ->
    ((proj_val__0 i) != none) ->
    ((proj_uN_0 (Option.get! (proj_val__0 i))) >= (List.length l_lst)) ->
    Step_pure [(.CONST .I32 i), (.BR_TABLE l_lst l')] [(.BR l')]
  | frame_vals : forall (v_n : n) (f : frame) (val_lst : (List val)), Step_pure [(.FRAME_ v_n f (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))] (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
  | return_frame : forall (v_n : n) (f : frame) (val'_lst : (List val)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.FRAME_ v_n f ((List.map (fun (val' : val) => (admininstr_val val')) val'_lst) ++ ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([.RETURN] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)))))] (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst)
  | return_label : forall (v_n : n) (instr'_lst : (List instr)) (val_lst : (List val)) (instr_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([.RETURN] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))))] ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [.RETURN])
  | trap_vals : forall (val_lst : (List val)) (instr_lst : (List instr)),
    ((val_lst != []) || (instr_lst != [])) ->
    Step_pure ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ ([.TRAP] ++ (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))) [.TRAP]
  | trap_label : forall (v_n : n) (instr'_lst : (List instr)), Step_pure [(.LABEL_ v_n instr'_lst [.TRAP])] [.TRAP]
  | trap_frame : forall (v_n : n) (f : frame), Step_pure [(.FRAME_ v_n f [.TRAP])] [.TRAP]
  | unop_val : forall (t : valtype) (c_1 : val_) (unop : unop_) (c : val_) (var_0 : (List val_)),
    (fun_unop_ t unop c_1 var_0) ->
    (wf_val_ t c_1) ->
    (wf_unop_ t unop) ->
    (wf_val_ t c) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.CONST t c_1), (.UNOP t unop)] [(.CONST t c)]
  | unop_trap : forall (t : valtype) (c_1 : val_) (unop : unop_) (var_0 : (List val_)),
    (fun_unop_ t unop c_1 var_0) ->
    (wf_val_ t c_1) ->
    (wf_unop_ t unop) ->
    (var_0 == []) ->
    Step_pure [(.CONST t c_1), (.UNOP t unop)] [.TRAP]
  | binop_val : forall (t : valtype) (c_1 : val_) (c_2 : val_) (binop : binop_) (c : val_) (var_0 : (List val_)),
    (fun_binop_ t binop c_1 c_2 var_0) ->
    (wf_val_ t c_1) ->
    (wf_val_ t c_2) ->
    (wf_binop_ t binop) ->
    (wf_val_ t c) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.CONST t c_1), (.CONST t c_2), (.BINOP t binop)] [(.CONST t c)]
  | binop_trap : forall (t : valtype) (c_1 : val_) (c_2 : val_) (binop : binop_) (var_0 : (List val_)),
    (fun_binop_ t binop c_1 c_2 var_0) ->
    (wf_val_ t c_1) ->
    (wf_val_ t c_2) ->
    (wf_binop_ t binop) ->
    (var_0 == []) ->
    Step_pure [(.CONST t c_1), (.CONST t c_2), (.BINOP t binop)] [.TRAP]
  | testop : forall (t : valtype) (c_1 : val_) (testop : testop_) (c : val_) (var_0 : val_),
    (fun_testop_ t testop c_1 var_0) ->
    (wf_val_ t c_1) ->
    (wf_testop_ t testop) ->
    (wf_val_ .I32 c) ->
    (c == var_0) ->
    Step_pure [(.CONST t c_1), (.TESTOP t testop)] [(.CONST .I32 c)]
  | relop : forall (t : valtype) (c_1 : val_) (c_2 : val_) (relop : relop_) (c : val_) (var_0 : val_),
    (fun_relop_ t relop c_1 c_2 var_0) ->
    (wf_val_ t c_1) ->
    (wf_val_ t c_2) ->
    (wf_relop_ t relop) ->
    (wf_val_ .I32 c) ->
    (c == var_0) ->
    Step_pure [(.CONST t c_1), (.CONST t c_2), (.RELOP t relop)] [(.CONST .I32 c)]
  | cvtop_val : forall (t_1 : valtype) (c_1 : val_) (t_2 : valtype) (v_cvtop : cvtop) (c : val_) (var_0 : (List val_)),
    (fun_cvtop__ t_1 t_2 v_cvtop c_1 var_0) ->
    (wf_val_ t_1 c_1) ->
    (wf_val_ t_2 c) ->
    ((List.length var_0) > 0) ->
    (List.contains var_0 c) ->
    Step_pure [(.CONST t_1 c_1), (.CVTOP t_2 t_1 v_cvtop)] [(.CONST t_2 c)]
  | cvtop_trap : forall (t_1 : valtype) (c_1 : val_) (t_2 : valtype) (v_cvtop : cvtop) (var_0 : (List val_)),
    (fun_cvtop__ t_1 t_2 v_cvtop c_1 var_0) ->
    (wf_val_ t_1 c_1) ->
    (var_0 == []) ->
    Step_pure [(.CONST t_1 c_1), (.CVTOP t_2 t_1 v_cvtop)] [.TRAP]
  | local_tee : forall (v_val : val) (x : idx), Step_pure [(admininstr_val v_val), (.LOCAL_TEE x)] [(admininstr_val v_val), (admininstr_val v_val), (.LOCAL_SET x)]

/- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:7.1-7.77 -/
inductive Step_read : config -> (List admininstr) -> Prop where
  | block : forall (z : state) (t_opt : (Option valtype)) (instr_lst : (List instr)) (v_n : n),
    (((t_opt == none) && (v_n == 0)) || ((t_opt != none) && (v_n == 1))) ->
    Step_read (.mk_config z [(.BLOCK t_opt instr_lst)]) [(.LABEL_ v_n [] (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))]
  | loop : forall (z : state) (t_opt : (Option valtype)) (instr_lst : (List instr)), Step_read (.mk_config z [(.LOOP t_opt instr_lst)]) [(.LABEL_ 0 [(.LOOP t_opt instr_lst)] (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))]
  | call : forall (z : state) (x : idx),
    ((proj_uN_0 x) < (List.length (fun_funcaddr z))) ->
    Step_read (.mk_config z [(.CALL x)]) [(.CALL_ADDR ((fun_funcaddr z)[(proj_uN_0 x)]!))]
  | call_indirect_call : forall (z : state) (i : val_) (x : idx) (a : addr),
    (wf_val_ .I32 i) ->
    ((proj_uN_0 (Option.get! (proj_val__0 i))) < (List.length ((fun_table z (.mk_uN 0)).REFS))) ->
    ((proj_val__0 i) != none) ->
    ((((fun_table z (.mk_uN 0)).REFS)[(proj_uN_0 (Option.get! (proj_val__0 i)))]!) == (some a)) ->
    (a < (List.length (fun_funcinst z))) ->
    ((fun_type z x) == (((fun_funcinst z)[a]!).TYPE)) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.CALL_INDIRECT x)]) [(.CALL_ADDR a)]
  | call_indirect_trap : forall (z : state) (i : val_) (x : idx) (a : addr),
    ((proj_uN_0 (Option.get! (proj_val__0 i))) < (List.length ((fun_table z (.mk_uN 0)).REFS))) ->
    ((proj_val__0 i) != none) ->
    (a < (List.length (fun_funcinst z))) ->
    (((((fun_table z (.mk_uN 0)).REFS)[(proj_uN_0 (Option.get! (proj_val__0 i)))]!) != (some a)) || ((fun_type z x) != (((fun_funcinst z)[a]!).TYPE))) ->
    (wf_val_ .I32 i) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.CALL_INDIRECT x)]) [.TRAP]
  | call_addr : forall (z : state) (val_lst : (List val)) (k : Nat) (a : addr) (v_n : n) (f : frame) (instr_lst : (List instr)) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)) (mm : moduleinst) (v_func : func) (x : idx) (t_lst : (List valtype)),
    (a < (List.length (fun_funcinst z))) ->
    (((fun_funcinst z)[a]!) == { TYPE := (.mk_functype t_1_lst t_2_lst), MODULE := mm, CODE := v_func }) ->
    (v_func == (.FUNC x (List.map (fun (t : valtype) => (.LOCAL t)) t_lst) instr_lst)) ->
    (f == { LOCALS := (val_lst ++ (List.map (fun (t : valtype) => (default_ t)) t_lst)), MODULE := mm }) ->
    Step_read (.mk_config z ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [(.CALL_ADDR a)])) [(.FRAME_ v_n f [(.LABEL_ v_n [] (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst))])]
  | local_get : forall (z : state) (x : idx), Step_read (.mk_config z [(.LOCAL_GET x)]) [(admininstr_val (fun_local z x))]
  | global_get : forall (z : state) (x : idx), Step_read (.mk_config z [(.GLOBAL_GET x)]) [(admininstr_val ((fun_global z x).VALUE))]
  | load_num_trap : forall (z : state) (i : val_) (t : valtype) (ao : memarg),
    (wf_val_ .I32 i) ->
    ((proj_val__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((size t) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.LOAD t none ao)]) [.TRAP]
  | load_num_val : forall (z : state) (i : val_) (t : valtype) (ao : memarg) (c : val_),
    (wf_val_ .I32 i) ->
    (wf_val_ t c) ->
    ((proj_val__0 i) != none) ->
    ((bytes_ t c) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((size t) : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.LOAD t none ao)]) [(.CONST t c)]
  | load_pack_trap : forall (z : state) (i : val_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg),
    (wf_val_ .I32 i) ->
    ((proj_val__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_n : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.LOAD (valtype_Inn v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_n) v_sx))) ao)]) [.TRAP]
  | load_pack_val : forall (z : state) (i : val_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) (c : iN),
    (wf_val_ .I32 i) ->
    ((proj_val__0 i) != none) ->
    ((ibytes_ v_n c) == (List.extract ((fun_mem z (.mk_uN 0)).BYTES) ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_n : Nat) / (8 : Nat)) : Nat))) ->
    Step_read (.mk_config z [(.CONST .I32 i), (.LOAD (valtype_Inn v_Inn) (some (.mk_loadop__0 v_Inn (.mk_loadop_Inn (.mk_sz v_n) v_sx))) ao)]) [(.CONST (valtype_Inn v_Inn) (.mk_val__0 v_Inn (extend__ v_n (size (valtype_Inn v_Inn)) v_sx c)))]
  | memory_size : forall (z : state) (v_n : n),
    (((v_n * 64) * (Ki )) == (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step_read (.mk_config z [.MEMORY_SIZE]) [(.CONST .I32 (.mk_val__0 .I32 (.mk_uN v_n)))]

/- Recursive Definition at: ../specification/wasm-1.0/8-reduction.spectec:5.1-5.77 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:5.1-5.77 -/
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
  | store_num_trap : forall (z : state) (i : val_) (t : valtype) (c : val_) (ao : memarg),
    (wf_val_ .I32 i) ->
    (wf_val_ t c) ->
    ((proj_val__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) + ((((size t) : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step (.mk_config z [(.CONST .I32 i), (.CONST t c), (.STORE t none ao)]) (.mk_config z [.TRAP])
  | store_num_val : forall (z : state) (i : val_) (t : valtype) (c : val_) (ao : memarg) (b_lst : (List byte)),
    ((proj_val__0 i) != none) ->
    (wf_val_ .I32 i) ->
    (wf_val_ t c) ->
    (b_lst == (bytes_ t c)) ->
    Step (.mk_config z [(.CONST .I32 i), (.CONST t c), (.STORE t none ao)]) (.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) ((((size t) : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | store_pack_trap : forall (z : state) (i : val_) (v_Inn : Inn) (c : val_) (v_n : n) (ao : memarg),
    (wf_val_ .I32 i) ->
    (wf_val_ (valtype_Inn v_Inn) c) ->
    ((proj_val__0 i) != none) ->
    ((((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) + (((v_n : Nat) / (8 : Nat)) : Nat)) > (List.length ((fun_mem z (.mk_uN 0)).BYTES))) ->
    Step (.mk_config z [(.CONST .I32 i), (.CONST (valtype_Inn v_Inn) c), (.STORE (valtype_Inn v_Inn) (some (.mk_sz v_n)) ao)]) (.mk_config z [.TRAP])
  | store_pack_val : forall (z : state) (i : val_) (v_Inn : Inn) (c : val_) (v_n : n) (ao : memarg) (b_lst : (List byte)),
    ((proj_val__0 i) != none) ->
    (wf_val_ .I32 i) ->
    (wf_val_ (valtype_Inn v_Inn) c) ->
    ((proj_val__0 c) != none) ->
    (b_lst == (ibytes_ v_n (wrap__ (size (valtype_Inn v_Inn)) v_n (Option.get! (proj_val__0 c))))) ->
    Step (.mk_config z [(.CONST .I32 i), (.CONST (valtype_Inn v_Inn) c), (.STORE (valtype_Inn v_Inn) (some (.mk_sz v_n)) ao)]) (.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) (((v_n : Nat) / (8 : Nat)) : Nat) b_lst) [])
  | memory_grow_succeed : forall (z : state) (v_n : n) (mi : meminst) (var_0 : (Option meminst)),
    (fun_growmemory (fun_mem z (.mk_uN 0)) v_n var_0) ->
    (var_0 != none) ->
    ((Option.get! var_0) == mi) ->
    Step (.mk_config z [(.CONST .I32 (.mk_val__0 .I32 (.mk_uN v_n))), .MEMORY_GROW]) (.mk_config (with_meminst z (.mk_uN 0) mi) [(.CONST .I32 (.mk_val__0 .I32 (.mk_uN ((((List.length ((fun_mem z (.mk_uN 0)).BYTES)) : Nat) / ((64 * (Ki )) : Nat)) : Nat))))])
  | memory_grow_fail : forall (z : state) (v_n : n) (var_0 : Nat),
    (fun_inv_signed_ 32 (0 - (1 : Nat)) var_0) ->
    Step (.mk_config z [(.CONST .I32 (.mk_val__0 .I32 (.mk_uN v_n))), .MEMORY_GROW]) (.mk_config z [(.CONST .I32 (.mk_val__0 .I32 (.mk_uN var_0)))])

/- Recursive Definition at: ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:8.1-8.77 -/
inductive Steps : config -> config -> Prop where
  | refl : forall (z : state) (admininstr_lst : (List admininstr)), Steps (.mk_config z admininstr_lst) (.mk_config z admininstr_lst)
  | trans : forall (z : state) (admininstr_lst : (List admininstr)) (z'' : state) (admininstr''_lst : (List admininstr)) (z' : state) (admininstr'_lst : (List admininstr)),
    (Step (.mk_config z admininstr_lst) (.mk_config z' admininstr'_lst)) ->
    (Steps (.mk_config z' admininstr'_lst) (.mk_config z'' admininstr''_lst)) ->
    Steps (.mk_config z admininstr_lst) (.mk_config z'' admininstr''_lst)

/- Inductive Relations Definition at: ../specification/wasm-1.0/8-reduction.spectec:29.1-29.83 -/
inductive Eval_expr : state -> expr -> state -> (List val) -> Prop where
  | mk_Eval_expr : forall (z : state) (instr_lst : (List instr)) (z' : state) (val_lst : (List val)),
    (Steps (.mk_config z (List.map (fun (v_instr : instr) => (admininstr_instr v_instr)) instr_lst)) (.mk_config z' (List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst))) ->
    Eval_expr z instr_lst z' val_lst

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:5.1-5.36 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:5.6-5.12 -/
inductive fun_funcs : (List externaddr) -> (List funcaddr) -> Prop where
  | fun_funcs_case_0 : fun_funcs [] []
  | fun_funcs_case_1 : forall (fa : Nat) (externaddr'_lst : (List externaddr)) (var_0 : (List funcaddr)),
    (fun_funcs externaddr'_lst var_0) ->
    fun_funcs ([(.FUNC fa)] ++ externaddr'_lst) ([fa] ++ var_0)
  | fun_funcs_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (List externaddr)) (var_0 : (List funcaddr)),
    (fun_funcs externaddr'_lst var_0) ->
    fun_funcs ([v_externaddr] ++ externaddr'_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:11.1-11.40 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:11.6-11.14 -/
inductive fun_globals : (List externaddr) -> (List globaladdr) -> Prop where
  | fun_globals_case_0 : fun_globals [] []
  | fun_globals_case_1 : forall (ga : Nat) (externaddr'_lst : (List externaddr)) (var_0 : (List globaladdr)),
    (fun_globals externaddr'_lst var_0) ->
    fun_globals ([(.GLOBAL ga)] ++ externaddr'_lst) ([ga] ++ var_0)
  | fun_globals_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (List externaddr)) (var_0 : (List globaladdr)),
    (fun_globals externaddr'_lst var_0) ->
    fun_globals ([v_externaddr] ++ externaddr'_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:17.1-17.38 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:17.6-17.13 -/
inductive fun_tables : (List externaddr) -> (List tableaddr) -> Prop where
  | fun_tables_case_0 : fun_tables [] []
  | fun_tables_case_1 : forall (ta : Nat) (externaddr'_lst : (List externaddr)) (var_0 : (List tableaddr)),
    (fun_tables externaddr'_lst var_0) ->
    fun_tables ([(.TABLE ta)] ++ externaddr'_lst) ([ta] ++ var_0)
  | fun_tables_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (List externaddr)) (var_0 : (List tableaddr)),
    (fun_tables externaddr'_lst var_0) ->
    fun_tables ([v_externaddr] ++ externaddr'_lst) var_0

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:23.1-23.34 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:23.6-23.11 -/
inductive fun_mems : (List externaddr) -> (List memaddr) -> Prop where
  | fun_mems_case_0 : fun_mems [] []
  | fun_mems_case_1 : forall (ma : Nat) (externaddr'_lst : (List externaddr)) (var_0 : (List memaddr)),
    (fun_mems externaddr'_lst var_0) ->
    fun_mems ([(.MEM ma)] ++ externaddr'_lst) ([ma] ++ var_0)
  | fun_mems_case_2 : forall (v_externaddr : externaddr) (externaddr'_lst : (List externaddr)) (var_0 : (List memaddr)),
    (fun_mems externaddr'_lst var_0) ->
    fun_mems ([v_externaddr] ++ externaddr'_lst) var_0

/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:36.6-36.16 -/
inductive fun_allocfunc : store -> moduleinst -> func -> store × funcaddr -> Prop where
  | fun_allocfunc_case_0 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (fi : funcinst) (x : uN) (local_lst : (List «local»)) (v_expr : (List instr)),
    ((proj_uN_0 x) < (List.length (v_moduleinst.TYPES))) ->
    (fi == { TYPE := ((v_moduleinst.TYPES)[(proj_uN_0 x)]!), MODULE := v_moduleinst, CODE := v_func }) ->
    (v_func == (.FUNC x local_lst v_expr)) ->
    fun_allocfunc s v_moduleinst v_func ((s <| FUNCS := ((FUNCS s) ++ [fi]) |>), (List.length (s.FUNCS)))

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:41.1-41.63 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:41.6-41.17 -/
inductive fun_allocfuncs : store -> moduleinst -> (List func) -> store × (List funcaddr) -> Prop where
  | fun_allocfuncs_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_allocfuncs s v_moduleinst [] (s, [])
  | fun_allocfuncs_case_1 : forall (s : store) (v_moduleinst : moduleinst) (v_func : func) (func'_lst : (List func)) (s_2 : store) (fa : Nat) (fa'_lst : (List funcaddr)) (s_1 : store) (var_1 : store × (List funcaddr)) (var_0 : store × funcaddr),
    (fun_allocfuncs s_1 v_moduleinst func'_lst var_1) ->
    (fun_allocfunc s v_moduleinst v_func var_0) ->
    ((s_1, fa) == var_0) ->
    ((s_2, fa'_lst) == var_1) ->
    fun_allocfuncs s v_moduleinst ([v_func] ++ func'_lst) (s_2, ([fa] ++ fa'_lst))

/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:47.6-47.18 -/
inductive fun_allocglobal : store -> globaltype -> val -> store × globaladdr -> Prop where
  | fun_allocglobal_case_0 : forall (s : store) (v_globaltype : globaltype) (v_val : val) (gi : globalinst),
    (gi == { TYPE := v_globaltype, VALUE := v_val }) ->
    fun_allocglobal s v_globaltype v_val ((s <| GLOBALS := ((GLOBALS s) ++ [gi]) |>), (List.length (s.GLOBALS)))

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:51.1-51.67 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:51.6-51.19 -/
inductive fun_allocglobals : store -> (List globaltype) -> (List val) -> store × (List globaladdr) -> Prop where
  | fun_allocglobals_case_0 : forall (s : store), fun_allocglobals s [] [] (s, [])
  | fun_allocglobals_case_1 : forall (s : store) (v_globaltype : globaltype) (globaltype'_lst : (List globaltype)) (v_val : val) (val'_lst : (List val)) (s_2 : store) (ga : Nat) (ga'_lst : (List globaladdr)) (s_1 : store) (var_1 : store × (List globaladdr)) (var_0 : store × globaladdr),
    (fun_allocglobals s_1 globaltype'_lst val'_lst var_1) ->
    (fun_allocglobal s v_globaltype v_val var_0) ->
    ((s_1, ga) == var_0) ->
    ((s_2, ga'_lst) == var_1) ->
    fun_allocglobals s ([v_globaltype] ++ globaltype'_lst) ([v_val] ++ val'_lst) (s_2, ([ga] ++ ga'_lst))

/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:57.6-57.17 -/
inductive fun_alloctable : store -> tabletype -> store × tableaddr -> Prop where
  | fun_alloctable_case_0 : forall (s : store) (i : uN) (j_opt : (Option u32)) (ti : tableinst),
    (ti == { TYPE := (.mk_limits i j_opt), REFS := (List.replicate (proj_uN_0 i) none) }) ->
    fun_alloctable s (.mk_limits i j_opt) ((s <| TABLES := ((TABLES s) ++ [ti]) |>), (List.length (s.TABLES)))

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:61.1-61.58 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:61.6-61.18 -/
inductive fun_alloctables : store -> (List tabletype) -> store × (List tableaddr) -> Prop where
  | fun_alloctables_case_0 : forall (s : store), fun_alloctables s [] (s, [])
  | fun_alloctables_case_1 : forall (s : store) (v_tabletype : limits) (tabletype'_lst : (List tabletype)) (s_2 : store) (ta : Nat) (ta'_lst : (List tableaddr)) (s_1 : store) (var_1 : store × (List tableaddr)) (var_0 : store × tableaddr),
    (fun_alloctables s_1 tabletype'_lst var_1) ->
    (fun_alloctable s v_tabletype var_0) ->
    ((s_1, ta) == var_0) ->
    ((s_2, ta'_lst) == var_1) ->
    fun_alloctables s ([v_tabletype] ++ tabletype'_lst) (s_2, ([ta] ++ ta'_lst))

/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:67.6-67.15 -/
inductive fun_allocmem : store -> memtype -> store × memaddr -> Prop where
  | fun_allocmem_case_0 : forall (s : store) (i : uN) (j_opt : (Option u32)) (mi : meminst),
    (mi == { TYPE := (.mk_limits i j_opt), BYTES := (List.replicate ((proj_uN_0 i) * (64 * (Ki ))) (.mk_byte 0)) }) ->
    fun_allocmem s (.mk_limits i j_opt) ((s <| MEMS := ((MEMS s) ++ [mi]) |>), (List.length (s.MEMS)))

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:71.1-71.52 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:71.6-71.16 -/
inductive fun_allocmems : store -> (List memtype) -> store × (List memaddr) -> Prop where
  | fun_allocmems_case_0 : forall (s : store), fun_allocmems s [] (s, [])
  | fun_allocmems_case_1 : forall (s : store) (v_memtype : limits) (memtype'_lst : (List memtype)) (s_2 : store) (ma : Nat) (ma'_lst : (List memaddr)) (s_1 : store) (var_1 : store × (List memaddr)) (var_0 : store × memaddr),
    (fun_allocmems s_1 memtype'_lst var_1) ->
    (fun_allocmem s v_memtype var_0) ->
    ((s_1, ma) == var_0) ->
    ((s_2, ma'_lst) == var_1) ->
    fun_allocmems s ([v_memtype] ++ memtype'_lst) (s_2, ([ma] ++ ma'_lst))

/- Auxiliary Definition at: ../specification/wasm-1.0/9-module.spectec:80.1-80.83 -/
def instexport : ∀  (var_0 : (List funcaddr)) (var_1 : (List globaladdr)) (var_2 : (List tableaddr)) (var_3 : (List memaddr)) (v_export : «export») , exportinst
  | fa_lst, ga_lst, ta_lst, ma_lst, (.EXPORT v_name (.FUNC x)) =>
    { NAME := v_name, ADDR := (.FUNC (fa_lst[(proj_uN_0 x)]!)) }
  | fa_lst, ga_lst, ta_lst, ma_lst, (.EXPORT v_name (.GLOBAL x)) =>
    { NAME := v_name, ADDR := (.GLOBAL (ga_lst[(proj_uN_0 x)]!)) }
  | fa_lst, ga_lst, ta_lst, ma_lst, (.EXPORT v_name (.TABLE x)) =>
    { NAME := v_name, ADDR := (.TABLE (ta_lst[(proj_uN_0 x)]!)) }
  | fa_lst, ga_lst, ta_lst, ma_lst, (.EXPORT v_name (.MEM x)) =>
    { NAME := v_name, ADDR := (.MEM (ma_lst[(proj_uN_0 x)]!)) }


/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:87.6-87.18 -/
inductive fun_allocmodule : store -> module -> (List externaddr) -> (List val) -> store × moduleinst -> Prop where
  | fun_allocmodule_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (List externaddr)) (val_lst : (List val)) (s_4 : store) (v_moduleinst : moduleinst) (ft_lst : (List functype)) (import_lst : (List «import»)) (func_lst : (List func)) (n_func : Nat) (globaltype_lst : (List globaltype)) (expr_1_lst : (List expr)) (n_global : Nat) (tabletype_lst : (List tabletype)) (n_table : Nat) (memtype_lst : (List memtype)) (n_mem : Nat) (elem_lst : (List elem)) (data_lst : (List data)) (start_opt : (Option start)) (export_lst : (List «export»)) (fa_ex_lst : (List funcaddr)) (ga_ex_lst : (List globaladdr)) (ta_ex_lst : (List tableaddr)) (ma_ex_lst : (List memaddr)) (fa_lst : (List funcaddr)) (i_func_lst : (List Nat)) (ga_lst : (List globaladdr)) (i_global_lst : (List Nat)) (ta_lst : (List tableaddr)) (i_table_lst : (List Nat)) (ma_lst : (List memaddr)) (i_mem_lst : (List Nat)) (xi_lst : (List exportinst)) (s_1 : store) (s_2 : store) (s_3 : store) (var_7 : store × (List memaddr)) (var_6 : store × (List tableaddr)) (var_5 : store × (List globaladdr)) (var_4 : store × (List funcaddr)) (var_3 : (List memaddr)) (var_2 : (List tableaddr)) (var_1 : (List globaladdr)) (var_0 : (List funcaddr)),
    (fun_allocmems s_3 memtype_lst var_7) ->
    (fun_alloctables s_2 tabletype_lst var_6) ->
    (fun_allocglobals s_1 globaltype_lst val_lst var_5) ->
    (fun_allocfuncs s v_moduleinst func_lst var_4) ->
    (fun_mems externaddr_lst var_3) ->
    (fun_tables externaddr_lst var_2) ->
    (fun_globals externaddr_lst var_1) ->
    (fun_funcs externaddr_lst var_0) ->
    (v_module == (.MODULE (List.map (fun (ft : functype) => (.TYPE ft)) ft_lst) import_lst func_lst (List.zipWith (fun (expr_1 : expr) (v_globaltype : globaltype) => (.GLOBAL v_globaltype expr_1)) expr_1_lst globaltype_lst) (List.map (fun (v_tabletype : tabletype) => (.TABLE v_tabletype)) tabletype_lst) (List.map (fun (v_memtype : memtype) => (.MEMORY v_memtype)) memtype_lst) elem_lst data_lst start_opt export_lst)) ->
    (fa_ex_lst == var_0) ->
    (ga_ex_lst == var_1) ->
    (ta_ex_lst == var_2) ->
    (ma_ex_lst == var_3) ->
    (fa_lst == (List.map (fun (i_func : Nat) => ((List.length (s.FUNCS)) + i_func)) i_func_lst)) ->
    (ga_lst == (List.map (fun (i_global : Nat) => ((List.length (s.GLOBALS)) + i_global)) i_global_lst)) ->
    (ta_lst == (List.map (fun (i_table : Nat) => ((List.length (s.TABLES)) + i_table)) i_table_lst)) ->
    (ma_lst == (List.map (fun (i_mem : Nat) => ((List.length (s.MEMS)) + i_mem)) i_mem_lst)) ->
    (xi_lst == (List.map (fun (v_export : «export») => (instexport (fa_ex_lst ++ fa_lst) (ga_ex_lst ++ ga_lst) (ta_ex_lst ++ ta_lst) (ma_ex_lst ++ ma_lst) v_export)) export_lst)) ->
    (v_moduleinst == { TYPES := ft_lst, FUNCS := (fa_ex_lst ++ fa_lst), GLOBALS := (ga_ex_lst ++ ga_lst), TABLES := (ta_ex_lst ++ ta_lst), MEMS := (ma_ex_lst ++ ma_lst), EXPORTS := xi_lst }) ->
    ((s_1, fa_lst) == var_4) ->
    ((s_2, ga_lst) == var_5) ->
    ((s_3, ta_lst) == var_6) ->
    ((s_4, ma_lst) == var_7) ->
    fun_allocmodule s v_module externaddr_lst val_lst (s_4, v_moduleinst)

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:128.1-128.61 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:128.6-128.15 -/
inductive fun_initelem : store -> moduleinst -> (List u32) -> (List (List funcaddr)) -> store -> Prop where
  | fun_initelem_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_initelem s v_moduleinst [] [] s
  | fun_initelem_case_1 : forall (s : store) (v_moduleinst : moduleinst) (i : uN) (i'_lst : (List u32)) (a_lst : (List addr)) (a'_lst_lst : (List (List addr))) (s_2 : store) (s_1 : store) (var_0 : store),
    (fun_initelem s_1 v_moduleinst i'_lst a'_lst_lst var_0) ->
    (0 < (List.length (v_moduleinst.TABLES))) ->
    (s_1 == (s <| TABLES := (list_update_func (s.TABLES) ((v_moduleinst.TABLES)[0]!) (fun (var_1 : tableinst) => (var_1 <| REFS := (list_slice_update (var_1.REFS) (proj_uN_0 i) (List.length a_lst) (List.map (fun (a : addr) => (some a)) a_lst)) |>))) |>)) ->
    (s_2 == var_0) ->
    fun_initelem s v_moduleinst ([i] ++ i'_lst) ([a_lst] ++ a'_lst_lst) s_2

/- Recursive Definition at: ../specification/wasm-1.0/9-module.spectec:134.1-134.57 -/
/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:134.6-134.15 -/
inductive fun_initdata : store -> moduleinst -> (List u32) -> (List (List byte)) -> store -> Prop where
  | fun_initdata_case_0 : forall (s : store) (v_moduleinst : moduleinst), fun_initdata s v_moduleinst [] [] s
  | fun_initdata_case_1 : forall (s : store) (v_moduleinst : moduleinst) (i : uN) (i'_lst : (List u32)) (b_lst : (List byte)) (b'_lst_lst : (List (List byte))) (s_2 : store) (s_1 : store) (var_0 : store),
    (fun_initdata s_1 v_moduleinst i'_lst b'_lst_lst var_0) ->
    (0 < (List.length (v_moduleinst.MEMS))) ->
    (s_1 == (s <| MEMS := (list_update_func (s.MEMS) ((v_moduleinst.MEMS)[0]!) (fun (var_1 : meminst) => (var_1 <| BYTES := (list_slice_update (var_1.BYTES) (proj_uN_0 i) (List.length b_lst) b_lst) |>))) |>)) ->
    (s_2 == var_0) ->
    fun_initdata s v_moduleinst ([i] ++ i'_lst) ([b_lst] ++ b'_lst_lst) s_2

/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:140.6-140.18 -/
inductive fun_instantiate : store -> module -> (List externaddr) -> config -> Prop where
  | fun_instantiate_case_0 : forall (s : store) (v_module : module) (externaddr_lst : (List externaddr)) (s_3 : store) (f : frame) (x'_opt : (Option idx)) (type_lst : (List type)) (import_lst : (List «import»)) (func_lst : (List func)) (global_lst : (List global)) (table_lst : (List table)) (mem_lst : (List mem)) (elem_lst : (List elem)) (data_lst : (List data)) (start_opt : (Option start)) (export_lst : (List «export»)) (functype_lst : (List functype)) (globaltype_lst : (List globaltype)) (expr_G_lst : (List expr)) (expr_E_lst : (List expr)) (x_lst_lst : (List (List idx))) (expr_D_lst : (List expr)) (b_lst_lst : (List (List byte))) (n_F : Nat) (moduleinst_init : moduleinst) (i_F_lst : (List Nat)) (f_init : frame) (z : state) (val_lst : (List val)) (i_E_lst : (List val_)) (i_D_lst : (List val_)) (s_1 : store) (v_moduleinst : moduleinst) (s_2 : store) (var_4 : store) (var_3 : store) (var_2 : store × moduleinst) (var_1 : (List globaladdr)) (var_0 : (List funcaddr)),
    Forall (fun (i_D : val_) => ((proj_val__0 i_D) != none)) i_D_lst ->
    (fun_initdata s_2 v_moduleinst (List.map (fun (i_D : val_) => (Option.get! (proj_val__0 i_D))) i_D_lst) b_lst_lst var_4) ->
    Forall (fun (i_E : val_) => ((proj_val__0 i_E) != none)) i_E_lst ->
    Forall (fun (x_lst : (List idx)) => Forall (fun (x : idx) => ((proj_uN_0 x) < (List.length (v_moduleinst.FUNCS)))) x_lst) x_lst_lst ->
    (fun_initelem s_1 v_moduleinst (List.map (fun (i_E : val_) => (Option.get! (proj_val__0 i_E))) i_E_lst) (List.map (fun (x_lst : (List idx)) => (List.map (fun (x : idx) => ((v_moduleinst.FUNCS)[(proj_uN_0 x)]!)) x_lst)) x_lst_lst) var_3) ->
    (fun_allocmodule s v_module externaddr_lst val_lst var_2) ->
    (fun_globals externaddr_lst var_1) ->
    (fun_funcs externaddr_lst var_0) ->
    Forall (fun (i_E : val_) => (wf_val_ .I32 i_E)) i_E_lst ->
    Forall (fun (i_D : val_) => (wf_val_ .I32 i_D)) i_D_lst ->
    (v_module == (.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)) ->
    (type_lst == (List.map (fun (v_functype : functype) => (.TYPE v_functype)) functype_lst)) ->
    (global_lst == (List.zipWith (fun (expr_G : expr) (v_globaltype : globaltype) => (.GLOBAL v_globaltype expr_G)) expr_G_lst globaltype_lst)) ->
    (elem_lst == (List.zipWith (fun (expr_E : expr) (x_lst : (List idx)) => (.ELEM expr_E x_lst)) expr_E_lst x_lst_lst)) ->
    (data_lst == (List.zipWith (fun (b_lst : (List byte)) (expr_D : expr) => (.DATA expr_D b_lst)) b_lst_lst expr_D_lst)) ->
    (start_opt == (Option.map (fun (x' : idx) => (.START x')) x'_opt)) ->
    (n_F == (List.length func_lst)) ->
    (moduleinst_init == { TYPES := functype_lst, FUNCS := (var_0 ++ (List.map (fun (i_F : Nat) => ((List.length (s.FUNCS)) + i_F)) i_F_lst)), GLOBALS := var_1, TABLES := [], MEMS := [], EXPORTS := [] }) ->
    (f_init == { LOCALS := [], MODULE := moduleinst_init }) ->
    (z == (.mk_state s f_init)) ->
    ((List.length expr_G_lst) == (List.length val_lst)) ->
    Forall₂ (fun (expr_G : expr) (v_val : val) => (Eval_expr z expr_G z [v_val])) expr_G_lst val_lst ->
    ((List.length expr_E_lst) == (List.length i_E_lst)) ->
    Forall₂ (fun (expr_E : expr) (i_E : val_) => (Eval_expr z expr_E z [(.CONST .I32 i_E)])) expr_E_lst i_E_lst ->
    ((List.length expr_D_lst) == (List.length i_D_lst)) ->
    Forall₂ (fun (expr_D : expr) (i_D : val_) => (Eval_expr z expr_D z [(.CONST .I32 i_D)])) expr_D_lst i_D_lst ->
    ((s_1, v_moduleinst) == var_2) ->
    (s_2 == var_3) ->
    (s_3 == var_4) ->
    (f == { LOCALS := [], MODULE := v_moduleinst }) ->
    fun_instantiate s v_module externaddr_lst (.mk_config (.mk_state s_3 f) (Option.toList (Option.map (fun (x' : idx) => (.CALL x')) x'_opt)))

/- Inductive Relations Definition at: ../specification/wasm-1.0/9-module.spectec:169.6-169.13 -/
inductive fun_invoke : store -> funcaddr -> (List val) -> config -> Prop where
  | fun_invoke_case_0 : forall (s : store) (fa : Nat) (val_lst : (List val)) (v_n : Nat) (f : frame) (t_1_lst : (List valtype)) (t_2_lst : (List valtype)),
    (f == { LOCALS := [], MODULE := { TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], EXPORTS := [] } }) ->
    (fa < (List.length (fun_funcinst (.mk_state s f)))) ->
    ((((fun_funcinst (.mk_state s f))[fa]!).TYPE) == (.mk_functype t_1_lst t_2_lst)) ->
    fun_invoke s fa val_lst (.mk_config (.mk_state s f) ((List.map (fun (v_val : val) => (admininstr_val v_val)) val_lst) ++ [(.CALL_ADDR fa)]))

/- Type Alias Definition at: ../specification/wasm-1.0/A-binary.spectec:483.1-483.43 -/
abbrev startopt : Type := (List start)

/- Type Alias Definition at: ../specification/wasm-1.0/A-binary.spectec:500.1-500.29 -/
abbrev code : Type := (List «local») × expr

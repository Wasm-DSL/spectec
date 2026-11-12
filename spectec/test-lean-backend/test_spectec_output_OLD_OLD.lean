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

abbrev N : Type := Nat

abbrev M : Type := Nat

abbrev K : Type := Nat

abbrev n : Type := Nat

abbrev m : Type := Nat

def min (nat : Nat) (nat_0 : Nat) : Nat :=
  if
    nat ≤ nat_0
  then
    nat
  else
    nat_0

inductive fun_sum : List Nat → Nat → Prop where
  | fun_sum_case_0 : fun_sum [] 0
  | fun_sum_case_1 (v_n : Nat) (n'_lst : List n) (var_0 : Nat) :
    fun_sum n'_lst var_0 →
    fun_sum ([v_n] ++ n'_lst) (v_n + var_0)


inductive fun_prod : List Nat → Nat → Prop where
  | fun_prod_case_0 : fun_prod [] 1
  | fun_prod_case_1 (v_n : Nat) (n'_lst : List n) (var_0 : Nat) :
    fun_prod n'_lst var_0 →
    fun_prod ([v_n] ++ n'_lst) (v_n * var_0)


def opt_ (X : Type) (var_0_lst : List X) : Option (Option X) :=
  match var_0_lst with
  | [] => some none
  | [w] => some (some w)
  | _ => none

def concat_ (X : Type) (var_0_lst_lst : List (List X)) : List X :=
  match var_0_lst_lst with
  | [] => []
  | w_lst :: w'_lst_lst => w_lst ++ (concat_ X w'_lst_lst)

def concatn_ (X : Type) (var_0_lst_lst : List (List X)) (nat : Nat) : List X :=
  match var_0_lst_lst with
  | [] => []
  | w_lst :: w'_lst_lst => nat = (List.length w_lst) → Forall (fun w'_lst_2_elem => nat = (List.length w'_lst_2_elem)) w'_lst_lst → w_lst ++ (concatn_ X w'_lst_lst nat)

def concatopt_ (X : Type) (var_0_opt_lst : List (Option X)) : List X :=
  match var_0_opt_lst with
  | [] => []
  | w_opt :: w'_opt_lst => (Option.toList w_opt) ++ (concat_ X (Map (fun w'_opt_elem => Option.toList w'_opt_elem) w'_opt_lst))

opaque inv_concat_ (X : Type) (var_0_lst : List X) : List (List X) := by
  first
     | exact Inhabited.default
     | intros ; assumption


opaque inv_concatn_ (X : Type) (nat : Nat) (var_0_lst : List X) : List (List X) := by
  first
     | exact Inhabited.default
     | intros ; assumption


def disjoint_ (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => true
  | w :: w'_lst => (! (List.contains w'_lst w)) && (disjoint_ X w'_lst)

def setminus1_ (X : Type) [BEq X] (X_0 : X) (var_0_lst : List X) : List X :=
  match var_0_lst with
  | [] => [X_0]
  | w_1 :: w'_lst => if
    X_0 == w_1
  then
    []
  else
    setminus1_ X X_0 w'_lst

def setminus_ (X : Type) [BEq X] (var_0_lst : List X) (var_1_lst : List X) : List X :=
  match var_0_lst with
  | [] => []
  | w_1 :: w'_lst => (setminus1_ X w_1 var_1_lst) ++ (setminus_ X w'_lst var_1_lst)

def setproduct2_ (X : Type) (X_0 : X) (var_0_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst_lst with
  | [] => []
  | w'_lst :: w_lst_lst => [[X_0] ++ w'_lst] ++ (setproduct2_ X X_0 w_lst_lst)

def setproduct1_ (X : Type) (var_0_lst : List X) (var_1_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst with
  | [] => []
  | w_1 :: w'_lst => (setproduct2_ X w_1 var_1_lst_lst) ++ (setproduct1_ X w'_lst var_1_lst_lst)

def setproduct_ (X : Type) (var_0_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst_lst with
  | [] => [[]]
  | w_1_lst :: w_lst_lst => setproduct1_ X w_1_lst (setproduct_ X w_lst_lst)

opaque ND  : Bool := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive bit : Type where
  | mk_bit (i : Nat) : bit
deriving Inhabited, BEq

inductive wf_bit : bit → Prop where
  | bit_case_0 (i : Nat) :
    (i = 0) ∨ (i = 1) →
    wf_bit (bit.mk_bit i)


inductive byte : Type where
  | mk_byte (i : Nat) : byte
deriving Inhabited, BEq

inductive wf_byte : byte → Prop where
  | byte_case_0 (i : Nat) :
    (i ≥ 0) ∧ (i ≤ 255) →
    wf_byte (byte.mk_byte i)


inductive uN : Type where
  | mk_uN (i : Nat) : uN
deriving Inhabited, BEq

def proj_uN_0 (x : uN) : Nat :=
  match x with
  | uN.mk_uN v_num_0 => (v_num_0)

inductive wf_uN : N → uN → Prop where
  | uN_case_0 (v_N : N) (i : Nat) :
    (i ≥ 0) ∧ (i ≤ (Int.toNat (((2 ^ v_N) : Int) - (1 : Int)))) →
    wf_uN v_N (uN.mk_uN i)


inductive sN : Type where
  | mk_sN (i : Int) : sN
deriving Inhabited, BEq

inductive wf_sN : N → sN → Prop where
  | sN_case_0 (v_N : N) (i : Int) :
    (((i ≥ (- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int))) ∧ (i ≤ (- (1 : Int)))) ∨ (i = (0 : Int))) ∨ ((i ≥ (1 : Int)) ∧ (i ≤ (((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int)))) →
    wf_sN v_N (sN.mk_sN i)


abbrev iN : Type := uN

abbrev u8 : Type := uN

abbrev u16 : Type := uN

abbrev u31 : Type := uN

abbrev u32 : Type := uN

abbrev u64 : Type := uN

abbrev s33 : Type := sN

abbrev i32 : Type := iN

abbrev i64 : Type := iN

abbrev i128 : Type := iN

def signif (v_N : N) : Option Nat :=
  match v_N with
  | 32 => some 23
  | 64 => some 52
  | _ => none

def expon (v_N : N) : Option Nat :=
  match v_N with
  | 32 => some 8
  | 64 => some 11
  | _ => none

def fun_M (v_N : N) : Nat :=
  Option.get! (signif v_N)

def E (v_N : N) : Nat :=
  Option.get! (expon v_N)

abbrev exp : Type := Int

inductive fNmag : Type where
  | NORM (v_m : m) (v_exp : exp) : fNmag
  | SUBNORM (v_m : m) : fNmag
  | INF : fNmag
  | NAN (v_m : m) : fNmag
deriving Inhabited, BEq

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


inductive fN : Type where
  | POS (_ : fNmag) : fN
  | NEG (_ : fNmag) : fN
deriving Inhabited, BEq

inductive wf_fN : N → fN → Prop where
  | fN_case_0 (v_N : N) (var_0 : fNmag) :
    wf_fNmag v_N var_0 →
    wf_fN v_N (fN.POS var_0)
  | fN_case_1 (v_N : N) (var_0 : fNmag) :
    wf_fNmag v_N var_0 →
    wf_fN v_N (fN.NEG var_0)


abbrev f32 : Type := fN

abbrev f64 : Type := fN

def fzero (v_N : N) : fN :=
  fN.POS (fNmag.SUBNORM 0)

inductive fzero_is_wf : N → fN → Prop where
  | fzero_is_wf_0 (v_N : N) (ret_val : fN) :
    ret_val = (fzero v_N) →
    wf_fN v_N ret_val →
    fzero_is_wf v_N ret_val


def fnat (v_N : N) (nat : Nat) : fN :=
  fN.POS (fNmag.NORM nat (0 : Int))

inductive fnat_is_wf : N → Nat → fN → Prop where
  | fnat_is_wf_0 (v_N : N) (nat : Nat) (ret_val : fN) :
    ret_val = (fnat v_N nat) →
    wf_fN v_N ret_val →
    fnat_is_wf v_N nat ret_val


def fone (v_N : N) : fN :=
  fN.POS (fNmag.NORM 1 (0 : Int))

inductive fone_is_wf : N → fN → Prop where
  | fone_is_wf_0 (v_N : N) (ret_val : fN) :
    ret_val = (fone v_N) →
    wf_fN v_N ret_val →
    fone_is_wf v_N ret_val


def canon_ (v_N : N) : Nat :=
  2 ^ (Int.toNat (((Option.get! (signif v_N)) : Int) - (1 : Int)))

abbrev vN : Type := uN

abbrev v128 : Type := vN

inductive list (X : Type) : Type where
  | mk_list (X_lst : List X) : list X
deriving Inhabited, BEq

def proj_list_0 (X : Type) (x : list X) : List X :=
  match x with
  | list.mk_list v_X_list_0 => (v_X_list_0)

inductive char : Type where
  | mk_char (i : Nat) : char
deriving Inhabited, BEq

inductive wf_char : char → Prop where
  | char_case_0 (i : Nat) :
    ((i ≥ 0) ∧ (i ≤ 55295)) ∨ ((i ≥ 57344) ∧ (i ≤ 1114111)) →
    wf_char (char.mk_char i)


opaque utf8 (var_0_lst : List char) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive utf8_is_wf : List char → List byte → Prop where
  | utf8_is_wf_0 (var_0_lst : List char) (ret_val_lst : List byte) :
    Forall (fun var_0_elem => wf_char var_0_elem) var_0_lst →
    ret_val_lst = (utf8 var_0_lst) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    utf8_is_wf var_0_lst ret_val_lst


inductive name : Type where
  | mk_name (char_lst : List char) : name
deriving Inhabited, BEq

inductive wf_name : name → Prop where
  | name_case_0 (char_lst : List char) :
    Forall (fun v_char_elem => wf_char v_char_elem) char_lst →
    (List.length (utf8 char_lst)) < (2 ^ 32) →
    wf_name (name.mk_name char_lst)


abbrev idx : Type := u32

abbrev laneidx : Type := u8

abbrev typeidx : Type := idx

abbrev funcidx : Type := idx

abbrev globalidx : Type := idx

abbrev tableidx : Type := idx

abbrev memidx : Type := idx

abbrev tagidx : Type := idx

abbrev elemidx : Type := idx

abbrev dataidx : Type := idx

abbrev labelidx : Type := idx

abbrev localidx : Type := idx

abbrev fieldidx : Type := idx

inductive externidx : Type where
  | FUNC (v_funcidx : funcidx) : externidx
  | GLOBAL (v_globalidx : globalidx) : externidx
  | TABLE (v_tableidx : tableidx) : externidx
  | MEM (v_memidx : memidx) : externidx
  | TAG (v_tagidx : tagidx) : externidx
deriving Inhabited, BEq

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
  | externidx_case_4 (v_tagidx : tagidx) :
    wf_uN 32 v_tagidx →
    wf_externidx (externidx.TAG v_tagidx)


inductive fun_funcsxx : List externidx → List typeidx → Prop where
  | fun_funcsxx_case_0 : fun_funcsxx [] []
  | fun_funcsxx_case_1 (x : uN) (xx_lst : List externidx) (var_0 : List typeidx) :
    fun_funcsxx xx_lst var_0 →
    fun_funcsxx ([externidx.FUNC x] ++ xx_lst) ([x] ++ var_0)
  | fun_funcsxx_case_2 (v_externidx : externidx) (xx_lst : List externidx) (var_0 : List typeidx) :
    fun_funcsxx xx_lst var_0 →
    fun_funcsxx ([v_externidx] ++ xx_lst) var_0


inductive funcsxx_is_wf : List externidx → List typeidx → Prop where
  | funcsxx_is_wf_0 (var_0_lst : List externidx) (ret_val_lst : List typeidx) (var_0 : List typeidx) :
    fun_funcsxx var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externidx var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    funcsxx_is_wf var_0_lst ret_val_lst


inductive fun_globalsxx : List externidx → List globalidx → Prop where
  | fun_globalsxx_case_0 : fun_globalsxx [] []
  | fun_globalsxx_case_1 (x : uN) (xx_lst : List externidx) (var_0 : List globalidx) :
    fun_globalsxx xx_lst var_0 →
    fun_globalsxx ([externidx.GLOBAL x] ++ xx_lst) ([x] ++ var_0)
  | fun_globalsxx_case_2 (v_externidx : externidx) (xx_lst : List externidx) (var_0 : List globalidx) :
    fun_globalsxx xx_lst var_0 →
    fun_globalsxx ([v_externidx] ++ xx_lst) var_0


inductive globalsxx_is_wf : List externidx → List globalidx → Prop where
  | globalsxx_is_wf_0 (var_0_lst : List externidx) (ret_val_lst : List globalidx) (var_0 : List globalidx) :
    fun_globalsxx var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externidx var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    globalsxx_is_wf var_0_lst ret_val_lst


inductive fun_tablesxx : List externidx → List tableidx → Prop where
  | fun_tablesxx_case_0 : fun_tablesxx [] []
  | fun_tablesxx_case_1 (x : uN) (xx_lst : List externidx) (var_0 : List tableidx) :
    fun_tablesxx xx_lst var_0 →
    fun_tablesxx ([externidx.TABLE x] ++ xx_lst) ([x] ++ var_0)
  | fun_tablesxx_case_2 (v_externidx : externidx) (xx_lst : List externidx) (var_0 : List tableidx) :
    fun_tablesxx xx_lst var_0 →
    fun_tablesxx ([v_externidx] ++ xx_lst) var_0


inductive tablesxx_is_wf : List externidx → List tableidx → Prop where
  | tablesxx_is_wf_0 (var_0_lst : List externidx) (ret_val_lst : List tableidx) (var_0 : List tableidx) :
    fun_tablesxx var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externidx var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    tablesxx_is_wf var_0_lst ret_val_lst


inductive fun_memsxx : List externidx → List memidx → Prop where
  | fun_memsxx_case_0 : fun_memsxx [] []
  | fun_memsxx_case_1 (x : uN) (xx_lst : List externidx) (var_0 : List memidx) :
    fun_memsxx xx_lst var_0 →
    fun_memsxx ([externidx.MEM x] ++ xx_lst) ([x] ++ var_0)
  | fun_memsxx_case_2 (v_externidx : externidx) (xx_lst : List externidx) (var_0 : List memidx) :
    fun_memsxx xx_lst var_0 →
    fun_memsxx ([v_externidx] ++ xx_lst) var_0


inductive memsxx_is_wf : List externidx → List memidx → Prop where
  | memsxx_is_wf_0 (var_0_lst : List externidx) (ret_val_lst : List memidx) (var_0 : List memidx) :
    fun_memsxx var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externidx var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    memsxx_is_wf var_0_lst ret_val_lst


inductive fun_tagsxx : List externidx → List tagidx → Prop where
  | fun_tagsxx_case_0 : fun_tagsxx [] []
  | fun_tagsxx_case_1 (x : uN) (xx_lst : List externidx) (var_0 : List tagidx) :
    fun_tagsxx xx_lst var_0 →
    fun_tagsxx ([externidx.TAG x] ++ xx_lst) ([x] ++ var_0)
  | fun_tagsxx_case_2 (v_externidx : externidx) (xx_lst : List externidx) (var_0 : List tagidx) :
    fun_tagsxx xx_lst var_0 →
    fun_tagsxx ([v_externidx] ++ xx_lst) var_0


inductive tagsxx_is_wf : List externidx → List tagidx → Prop where
  | tagsxx_is_wf_0 (var_0_lst : List externidx) (ret_val_lst : List tagidx) (var_0 : List tagidx) :
    fun_tagsxx var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externidx var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    tagsxx_is_wf var_0_lst ret_val_lst


structure free where
  MKfree ::
  TYPES : List typeidx
  FUNCS : List funcidx
  GLOBALS : List globalidx
  TABLES : List tableidx
  MEMS : List memidx
  ELEMS : List elemidx
  DATAS : List dataidx
  LOCALS : List localidx
  LABELS : List labelidx
  TAGS : List tagidx
deriving Inhabited, BEq

def append_free (arg1 arg2 : free) : free where
  TYPES := (arg1.TYPES) ++ (arg2.TYPES)
  FUNCS := (arg1.FUNCS) ++ (arg2.FUNCS)
  GLOBALS := (arg1.GLOBALS) ++ (arg2.GLOBALS)
  TABLES := (arg1.TABLES) ++ (arg2.TABLES)
  MEMS := (arg1.MEMS) ++ (arg2.MEMS)
  ELEMS := (arg1.ELEMS) ++ (arg2.ELEMS)
  DATAS := (arg1.DATAS) ++ (arg2.DATAS)
  LOCALS := (arg1.LOCALS) ++ (arg2.LOCALS)
  LABELS := (arg1.LABELS) ++ (arg2.LABELS)
  TAGS := (arg1.TAGS) ++ (arg2.TAGS)

instance  : Append free where
  append := append_free

inductive wf_free : free → Prop where
  | free_case_ (var_0_lst : List typeidx) (var_1_lst : List funcidx) (var_2_lst : List globalidx) (var_3_lst : List tableidx) (var_4_lst : List memidx) (var_5_lst : List elemidx) (var_6_lst : List dataidx) (var_7_lst : List localidx) (var_8_lst : List labelidx) (var_9_lst : List tagidx) :
    Forall (fun var_0_elem => wf_uN 32 var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_uN 32 var_1_elem) var_1_lst →
    Forall (fun var_2_elem => wf_uN 32 var_2_elem) var_2_lst →
    Forall (fun var_3_elem => wf_uN 32 var_3_elem) var_3_lst →
    Forall (fun var_4_elem => wf_uN 32 var_4_elem) var_4_lst →
    Forall (fun var_5_elem => wf_uN 32 var_5_elem) var_5_lst →
    Forall (fun var_6_elem => wf_uN 32 var_6_elem) var_6_lst →
    Forall (fun var_7_elem => wf_uN 32 var_7_elem) var_7_lst →
    Forall (fun var_8_elem => wf_uN 32 var_8_elem) var_8_lst →
    Forall (fun var_9_elem => wf_uN 32 var_9_elem) var_9_lst →
    wf_free ({
      TYPES := var_0_lst
      FUNCS := var_1_lst
      GLOBALS := var_2_lst
      TABLES := var_3_lst
      MEMS := var_4_lst
      ELEMS := var_5_lst
      DATAS := var_6_lst
      LOCALS := var_7_lst
      LABELS := var_8_lst
      TAGS := var_9_lst : free
    })


def free_opt (var_0_opt : Option free) : free :=
  match var_0_opt with
  | none => {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }
  | some v_free => v_free

inductive free_opt_is_wf : Option free → free → Prop where
  | free_opt_is_wf_0 (var_0_opt : Option free) (ret_val : free) :
    Forall (fun var_0_elem => wf_free var_0_elem) (Option.toList var_0_opt) →
    ret_val = (free_opt var_0_opt) →
    wf_free ret_val →
    free_opt_is_wf var_0_opt ret_val


inductive fun_free_list : List free → free → Prop where
  | fun_free_list_case_0 : fun_free_list [] ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_list_case_1 (v_free : free) (free'_lst : List free) (var_0 : free) :
    fun_free_list free'_lst var_0 →
    fun_free_list ([v_free] ++ free'_lst) (v_free ++ var_0)


inductive free_list_is_wf : List free → free → Prop where
  | free_list_is_wf_0 (var_0_lst : List free) (ret_val : free) (var_0 : free) :
    fun_free_list var_0_lst var_0 →
    Forall (fun var_0_elem => wf_free var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_free ret_val →
    free_list_is_wf var_0_lst ret_val


def free_typeidx (v_typeidx : typeidx) : free :=
  {
    TYPES := [v_typeidx]
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_typeidx_is_wf : typeidx → free → Prop where
  | free_typeidx_is_wf_0 (v_typeidx : typeidx) (ret_val : free) :
    wf_uN 32 v_typeidx →
    ret_val = (free_typeidx v_typeidx) →
    wf_free ret_val →
    free_typeidx_is_wf v_typeidx ret_val


def free_funcidx (v_funcidx : funcidx) : free :=
  {
    TYPES := []
    FUNCS := [v_funcidx]
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_funcidx_is_wf : funcidx → free → Prop where
  | free_funcidx_is_wf_0 (v_funcidx : funcidx) (ret_val : free) :
    wf_uN 32 v_funcidx →
    ret_val = (free_funcidx v_funcidx) →
    wf_free ret_val →
    free_funcidx_is_wf v_funcidx ret_val


def free_globalidx (v_globalidx : globalidx) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := [v_globalidx]
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_globalidx_is_wf : globalidx → free → Prop where
  | free_globalidx_is_wf_0 (v_globalidx : globalidx) (ret_val : free) :
    wf_uN 32 v_globalidx →
    ret_val = (free_globalidx v_globalidx) →
    wf_free ret_val →
    free_globalidx_is_wf v_globalidx ret_val


def free_tableidx (v_tableidx : tableidx) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := [v_tableidx]
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_tableidx_is_wf : tableidx → free → Prop where
  | free_tableidx_is_wf_0 (v_tableidx : tableidx) (ret_val : free) :
    wf_uN 32 v_tableidx →
    ret_val = (free_tableidx v_tableidx) →
    wf_free ret_val →
    free_tableidx_is_wf v_tableidx ret_val


def free_memidx (v_memidx : memidx) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := [v_memidx]
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_memidx_is_wf : memidx → free → Prop where
  | free_memidx_is_wf_0 (v_memidx : memidx) (ret_val : free) :
    wf_uN 32 v_memidx →
    ret_val = (free_memidx v_memidx) →
    wf_free ret_val →
    free_memidx_is_wf v_memidx ret_val


def free_elemidx (v_elemidx : elemidx) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := [v_elemidx]
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_elemidx_is_wf : elemidx → free → Prop where
  | free_elemidx_is_wf_0 (v_elemidx : elemidx) (ret_val : free) :
    wf_uN 32 v_elemidx →
    ret_val = (free_elemidx v_elemidx) →
    wf_free ret_val →
    free_elemidx_is_wf v_elemidx ret_val


def free_dataidx (v_dataidx : dataidx) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := [v_dataidx]
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_dataidx_is_wf : dataidx → free → Prop where
  | free_dataidx_is_wf_0 (v_dataidx : dataidx) (ret_val : free) :
    wf_uN 32 v_dataidx →
    ret_val = (free_dataidx v_dataidx) →
    wf_free ret_val →
    free_dataidx_is_wf v_dataidx ret_val


def free_localidx (v_localidx : localidx) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := [v_localidx]
    LABELS := []
    TAGS := [] : free
  }

inductive free_localidx_is_wf : localidx → free → Prop where
  | free_localidx_is_wf_0 (v_localidx : localidx) (ret_val : free) :
    wf_uN 32 v_localidx →
    ret_val = (free_localidx v_localidx) →
    wf_free ret_val →
    free_localidx_is_wf v_localidx ret_val


def free_labelidx (v_labelidx : labelidx) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := [v_labelidx]
    TAGS := [] : free
  }

inductive free_labelidx_is_wf : labelidx → free → Prop where
  | free_labelidx_is_wf_0 (v_labelidx : labelidx) (ret_val : free) :
    wf_uN 32 v_labelidx →
    ret_val = (free_labelidx v_labelidx) →
    wf_free ret_val →
    free_labelidx_is_wf v_labelidx ret_val


def free_tagidx (v_tagidx : tagidx) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [v_tagidx] : free
  }

inductive free_tagidx_is_wf : tagidx → free → Prop where
  | free_tagidx_is_wf_0 (v_tagidx : tagidx) (ret_val : free) :
    wf_uN 32 v_tagidx →
    ret_val = (free_tagidx v_tagidx) →
    wf_free ret_val →
    free_tagidx_is_wf v_tagidx ret_val


def free_externidx (v_externidx : externidx) : free :=
  match v_externidx with
  | externidx.FUNC v_funcidx => free_funcidx v_funcidx
  | externidx.GLOBAL v_globalidx => free_globalidx v_globalidx
  | externidx.TABLE v_tableidx => free_tableidx v_tableidx
  | externidx.MEM v_memidx => free_memidx v_memidx
  | externidx.TAG v_tagidx => free_tagidx v_tagidx

inductive free_externidx_is_wf : externidx → free → Prop where
  | free_externidx_is_wf_0 (v_externidx : externidx) (ret_val : free) :
    wf_externidx v_externidx →
    ret_val = (free_externidx v_externidx) →
    wf_free ret_val →
    free_externidx_is_wf v_externidx ret_val


inductive null : Type where
  | NULL : null
deriving Inhabited, BEq

inductive addrtype : Type where
  | I32 : addrtype
  | I64 : addrtype
deriving Inhabited, BEq

inductive numtype : Type where
  | I32 : numtype
  | I64 : numtype
  | F32 : numtype
  | F64 : numtype
deriving Inhabited, BEq

def numtype_addrtype (var_0 : addrtype) : numtype :=
  match var_0 with
  | addrtype.I32 => numtype.I32
  | addrtype.I64 => numtype.I64

inductive vectype : Type where
  | V128 : vectype
deriving Inhabited, BEq

inductive consttype : Type where
  | I32 : consttype
  | I64 : consttype
  | F32 : consttype
  | F64 : consttype
  | V128 : consttype
deriving Inhabited, BEq

def consttype_numtype (var_0 : numtype) : consttype :=
  match var_0 with
  | numtype.I32 => consttype.I32
  | numtype.I64 => consttype.I64
  | numtype.F32 => consttype.F32
  | numtype.F64 => consttype.F64

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

inductive «mut» : Type where
  | MUT : «mut»
deriving Inhabited, BEq

inductive final : Type where
  | FINAL : final
deriving Inhabited, BEq

mutual
inductive typeuse : Type where
  | _IDX (v_typeidx : typeidx) : typeuse
  | _DEF (v_rectype : rectype) (v_n : n) : typeuse
  | REC (v_n : n) : typeuse
deriving Inhabited, BEq
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
  | _DEF (v_rectype : rectype) (v_n : n) : heaptype
  | REC (v_n : n) : heaptype
deriving Inhabited, BEq
inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
  | V128 : valtype
  | REF (null_opt : Option null) (v_heaptype : heaptype) : valtype
  | BOT : valtype
deriving Inhabited, BEq
inductive storagetype : Type where
  | I32 : storagetype
  | I64 : storagetype
  | F32 : storagetype
  | F64 : storagetype
  | V128 : storagetype
  | REF (null_opt : Option null) (v_heaptype : heaptype) : storagetype
  | BOT : storagetype
  | I8 : storagetype
  | I16 : storagetype
deriving Inhabited, BEq
inductive fieldtype : Type where
  | mk_fieldtype (mut_opt : Option «mut») (v_storagetype : storagetype) : fieldtype
deriving Inhabited, BEq
inductive comptype : Type where
  | STRUCT (_ : list fieldtype) : comptype
  | ARRAY (v_fieldtype : fieldtype) : comptype
  | FUNC (v_resulttype_0 : list valtype) (v_resulttype_1 : list valtype) : comptype
deriving Inhabited, BEq
inductive subtype : Type where
  | SUB (final_opt : Option final) (typeuse_lst : List typeuse) (v_comptype : comptype) : subtype
deriving Inhabited, BEq
inductive rectype : Type where
  | REC (_ : list subtype) : rectype
deriving Inhabited, BEq

end

abbrev resulttype : Type := list valtype

def heaptype_absheaptype (var_0 : absheaptype) : heaptype :=
  match var_0 with
  | absheaptype.ANY => heaptype.ANY
  | absheaptype.EQ => heaptype.EQ
  | absheaptype.I31 => heaptype.I31
  | absheaptype.STRUCT => heaptype.STRUCT
  | absheaptype.ARRAY => heaptype.ARRAY
  | absheaptype.NONE => heaptype.NONE
  | absheaptype.FUNC => heaptype.FUNC
  | absheaptype.NOFUNC => heaptype.NOFUNC
  | absheaptype.EXN => heaptype.EXN
  | absheaptype.NOEXN => heaptype.NOEXN
  | absheaptype.EXTERN => heaptype.EXTERN
  | absheaptype.NOEXTERN => heaptype.NOEXTERN
  | absheaptype.BOT => heaptype.BOT

def valtype_addrtype (var_0 : addrtype) : valtype :=
  match var_0 with
  | addrtype.I32 => valtype.I32
  | addrtype.I64 => valtype.I64

def storagetype_consttype (var_0 : consttype) : storagetype :=
  match var_0 with
  | consttype.I32 => storagetype.I32
  | consttype.I64 => storagetype.I64
  | consttype.F32 => storagetype.F32
  | consttype.F64 => storagetype.F64
  | consttype.V128 => storagetype.V128

def storagetype_numtype (var_0 : numtype) : storagetype :=
  match var_0 with
  | numtype.I32 => storagetype.I32
  | numtype.I64 => storagetype.I64
  | numtype.F32 => storagetype.F32
  | numtype.F64 => storagetype.F64

def valtype_numtype (var_0 : numtype) : valtype :=
  match var_0 with
  | numtype.I32 => valtype.I32
  | numtype.I64 => valtype.I64
  | numtype.F32 => valtype.F32
  | numtype.F64 => valtype.F64

def heaptype_typeuse (var_0 : typeuse) : heaptype :=
  match var_0 with
  | typeuse._IDX x0 => heaptype._IDX x0
  | typeuse._DEF x0 x1 => heaptype._DEF x0 x1
  | typeuse.REC x0 => heaptype.REC x0

def storagetype_valtype (var_0 : valtype) : storagetype :=
  match var_0 with
  | valtype.I32 => storagetype.I32
  | valtype.I64 => storagetype.I64
  | valtype.F32 => storagetype.F32
  | valtype.F64 => storagetype.F64
  | valtype.V128 => storagetype.V128
  | valtype.REF x0 x1 => storagetype.REF x0 x1
  | valtype.BOT => storagetype.BOT

def storagetype_vectype (var_0 : vectype) : storagetype :=
  match var_0 with
  | vectype.V128 => storagetype.V128

def valtype_vectype (var_0 : vectype) : valtype :=
  match var_0 with
  | vectype.V128 => valtype.V128

mutual
inductive wf_typeuse : typeuse → Prop where
  | typeuse_case_0 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_typeuse (typeuse._IDX v_typeidx)
  | typeuse_case_1 (v_rectype : rectype) (v_n : n) : wf_typeuse (typeuse._DEF v_rectype v_n)
  | typeuse_case_2 (v_n : n) : wf_typeuse (typeuse.REC v_n)

inductive wf_heaptype : heaptype → Prop where
  | heaptype_case_0 : wf_heaptype heaptype.ANY
  | heaptype_case_1 : wf_heaptype heaptype.EQ
  | heaptype_case_2 : wf_heaptype heaptype.I31
  | heaptype_case_3 : wf_heaptype heaptype.STRUCT
  | heaptype_case_4 : wf_heaptype heaptype.ARRAY
  | heaptype_case_5 : wf_heaptype heaptype.NONE
  | heaptype_case_6 : wf_heaptype heaptype.FUNC
  | heaptype_case_7 : wf_heaptype heaptype.NOFUNC
  | heaptype_case_8 : wf_heaptype heaptype.EXN
  | heaptype_case_9 : wf_heaptype heaptype.NOEXN
  | heaptype_case_10 : wf_heaptype heaptype.EXTERN
  | heaptype_case_11 : wf_heaptype heaptype.NOEXTERN
  | heaptype_case_12 : wf_heaptype heaptype.BOT
  | heaptype_case_13 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_heaptype (heaptype._IDX v_typeidx)
  | heaptype_case_14 (v_rectype : rectype) (v_n : n) : wf_heaptype (heaptype._DEF v_rectype v_n)
  | heaptype_case_15 (v_n : n) : wf_heaptype (heaptype.REC v_n)

inductive wf_valtype : valtype → Prop where
  | valtype_case_0 : wf_valtype valtype.I32
  | valtype_case_1 : wf_valtype valtype.I64
  | valtype_case_2 : wf_valtype valtype.F32
  | valtype_case_3 : wf_valtype valtype.F64
  | valtype_case_4 : wf_valtype valtype.V128
  | valtype_case_5 (null_opt : Option null) (v_heaptype : heaptype) :
    wf_heaptype v_heaptype →
    wf_valtype (valtype.REF null_opt v_heaptype)
  | valtype_case_6 : wf_valtype valtype.BOT

inductive wf_storagetype : storagetype → Prop where
  | storagetype_case_0 : wf_storagetype storagetype.I32
  | storagetype_case_1 : wf_storagetype storagetype.I64
  | storagetype_case_2 : wf_storagetype storagetype.F32
  | storagetype_case_3 : wf_storagetype storagetype.F64
  | storagetype_case_4 : wf_storagetype storagetype.V128
  | storagetype_case_5 (null_opt : Option null) (v_heaptype : heaptype) :
    wf_heaptype v_heaptype →
    wf_storagetype (storagetype.REF null_opt v_heaptype)
  | storagetype_case_6 : wf_storagetype storagetype.BOT
  | storagetype_case_7 : wf_storagetype storagetype.I8
  | storagetype_case_8 : wf_storagetype storagetype.I16

inductive wf_fieldtype : fieldtype → Prop where
  | fieldtype_case_0 (mut_opt : Option «mut») (v_storagetype : storagetype) :
    wf_storagetype v_storagetype →
    wf_fieldtype (fieldtype.mk_fieldtype mut_opt v_storagetype)

inductive wf_comptype : comptype → Prop where
  | comptype_case_0 (var_0 : list fieldtype) : wf_comptype (comptype.STRUCT var_0)
  | comptype_case_1 (v_fieldtype : fieldtype) :
    wf_fieldtype v_fieldtype →
    wf_comptype (comptype.ARRAY v_fieldtype)
  | comptype_case_2 (v_resulttype : resulttype) (resulttype_0 : resulttype) : wf_comptype (comptype.FUNC v_resulttype resulttype_0)

inductive wf_subtype : subtype → Prop where
  | subtype_case_0 (final_opt : Option final) (typeuse_lst : List typeuse) (v_comptype : comptype) :
    Forall (fun v_typeuse_elem => wf_typeuse v_typeuse_elem) typeuse_lst →
    wf_comptype v_comptype →
    wf_subtype (subtype.SUB final_opt typeuse_lst v_comptype)


end

inductive deftype : Type where
  | _DEF (v_rectype : rectype) (v_n : n) : deftype
deriving Inhabited, BEq

def heaptype_deftype (var_0 : deftype) : heaptype :=
  match var_0 with
  | deftype._DEF x0 x1 => heaptype._DEF x0 x1

def typeuse_deftype (var_0 : deftype) : typeuse :=
  match var_0 with
  | deftype._DEF x0 x1 => typeuse._DEF x0 x1

inductive typevar : Type where
  | _IDX (v_typeidx : typeidx) : typevar
  | REC (v_n : n) : typevar
deriving Inhabited, BEq

def typeuse_typevar (var_0 : typevar) : typeuse :=
  match var_0 with
  | typevar._IDX x0 => typeuse._IDX x0
  | typevar.REC x0 => typeuse.REC x0

inductive wf_typevar : typevar → Prop where
  | typevar_case_0 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_typevar (typevar._IDX v_typeidx)
  | typevar_case_1 (v_n : n) : wf_typevar (typevar.REC v_n)


inductive reftype : Type where
  | REF (null_opt : Option null) (v_heaptype : heaptype) : reftype
deriving Inhabited, BEq

def storagetype_reftype (var_0 : reftype) : storagetype :=
  match var_0 with
  | reftype.REF x0 x1 => storagetype.REF x0 x1

def valtype_reftype (var_0 : reftype) : valtype :=
  match var_0 with
  | reftype.REF x0 x1 => valtype.REF x0 x1

inductive wf_reftype : reftype → Prop where
  | reftype_case_0 (null_opt : Option null) (v_heaptype : heaptype) :
    wf_heaptype v_heaptype →
    wf_reftype (reftype.REF null_opt v_heaptype)


abbrev Inn : Type := addrtype

inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq

def numtype_Fnn (var_0 : Fnn) : numtype :=
  match var_0 with
  | Fnn.F32 => numtype.F32
  | Fnn.F64 => numtype.F64

abbrev Vnn : Type := vectype

inductive Cnn : Type where
  | I32 : Cnn
  | I64 : Cnn
  | F32 : Cnn
  | F64 : Cnn
  | V128 : Cnn
deriving Inhabited, BEq

def storagetype_Cnn (var_0 : Cnn) : storagetype :=
  match var_0 with
  | Cnn.I32 => storagetype.I32
  | Cnn.I64 => storagetype.I64
  | Cnn.F32 => storagetype.F32
  | Cnn.F64 => storagetype.F64
  | Cnn.V128 => storagetype.V128

def ANYREF : reftype :=
  reftype.REF (some null.NULL) heaptype.ANY

inductive ANYREF_is_wf : reftype → Prop where
  | ANYREF_is_wf_0 (ret_val : reftype) :
    ret_val = ANYREF →
    wf_reftype ret_val →
    ANYREF_is_wf ret_val


def EQREF : reftype :=
  reftype.REF (some null.NULL) heaptype.EQ

inductive EQREF_is_wf : reftype → Prop where
  | EQREF_is_wf_0 (ret_val : reftype) :
    ret_val = EQREF →
    wf_reftype ret_val →
    EQREF_is_wf ret_val


def I31REF : reftype :=
  reftype.REF (some null.NULL) heaptype.I31

inductive I31REF_is_wf : reftype → Prop where
  | I31REF_is_wf_0 (ret_val : reftype) :
    ret_val = I31REF →
    wf_reftype ret_val →
    I31REF_is_wf ret_val


def STRUCTREF : reftype :=
  reftype.REF (some null.NULL) heaptype.STRUCT

inductive STRUCTREF_is_wf : reftype → Prop where
  | STRUCTREF_is_wf_0 (ret_val : reftype) :
    ret_val = STRUCTREF →
    wf_reftype ret_val →
    STRUCTREF_is_wf ret_val


def ARRAYREF : reftype :=
  reftype.REF (some null.NULL) heaptype.ARRAY

inductive ARRAYREF_is_wf : reftype → Prop where
  | ARRAYREF_is_wf_0 (ret_val : reftype) :
    ret_val = ARRAYREF →
    wf_reftype ret_val →
    ARRAYREF_is_wf ret_val


def FUNCREF : reftype :=
  reftype.REF (some null.NULL) heaptype.FUNC

inductive FUNCREF_is_wf : reftype → Prop where
  | FUNCREF_is_wf_0 (ret_val : reftype) :
    ret_val = FUNCREF →
    wf_reftype ret_val →
    FUNCREF_is_wf ret_val


def EXNREF : reftype :=
  reftype.REF (some null.NULL) heaptype.EXN

inductive EXNREF_is_wf : reftype → Prop where
  | EXNREF_is_wf_0 (ret_val : reftype) :
    ret_val = EXNREF →
    wf_reftype ret_val →
    EXNREF_is_wf ret_val


def EXTERNREF : reftype :=
  reftype.REF (some null.NULL) heaptype.EXTERN

inductive EXTERNREF_is_wf : reftype → Prop where
  | EXTERNREF_is_wf_0 (ret_val : reftype) :
    ret_val = EXTERNREF →
    wf_reftype ret_val →
    EXTERNREF_is_wf ret_val


def NULLREF : reftype :=
  reftype.REF (some null.NULL) heaptype.NONE

inductive NULLREF_is_wf : reftype → Prop where
  | NULLREF_is_wf_0 (ret_val : reftype) :
    ret_val = NULLREF →
    wf_reftype ret_val →
    NULLREF_is_wf ret_val


def NULLFUNCREF : reftype :=
  reftype.REF (some null.NULL) heaptype.NOFUNC

inductive NULLFUNCREF_is_wf : reftype → Prop where
  | NULLFUNCREF_is_wf_0 (ret_val : reftype) :
    ret_val = NULLFUNCREF →
    wf_reftype ret_val →
    NULLFUNCREF_is_wf ret_val


def NULLEXNREF : reftype :=
  reftype.REF (some null.NULL) heaptype.NOEXN

inductive NULLEXNREF_is_wf : reftype → Prop where
  | NULLEXNREF_is_wf_0 (ret_val : reftype) :
    ret_val = NULLEXNREF →
    wf_reftype ret_val →
    NULLEXNREF_is_wf ret_val


def NULLEXTERNREF : reftype :=
  reftype.REF (some null.NULL) heaptype.NOEXTERN

inductive NULLEXTERNREF_is_wf : reftype → Prop where
  | NULLEXTERNREF_is_wf_0 (ret_val : reftype) :
    ret_val = NULLEXTERNREF →
    wf_reftype ret_val →
    NULLEXTERNREF_is_wf ret_val


inductive packtype : Type where
  | I8 : packtype
  | I16 : packtype
deriving Inhabited, BEq

def storagetype_packtype (var_0 : packtype) : storagetype :=
  match var_0 with
  | packtype.I8 => storagetype.I8
  | packtype.I16 => storagetype.I16

inductive lanetype : Type where
  | I32 : lanetype
  | I64 : lanetype
  | F32 : lanetype
  | F64 : lanetype
  | I8 : lanetype
  | I16 : lanetype
deriving Inhabited, BEq

def lanetype_Fnn (var_0 : Fnn) : lanetype :=
  match var_0 with
  | Fnn.F32 => lanetype.F32
  | Fnn.F64 => lanetype.F64

def lanetype_addrtype (var_0 : addrtype) : lanetype :=
  match var_0 with
  | addrtype.I32 => lanetype.I32
  | addrtype.I64 => lanetype.I64

def lanetype_numtype (var_0 : numtype) : lanetype :=
  match var_0 with
  | numtype.I32 => lanetype.I32
  | numtype.I64 => lanetype.I64
  | numtype.F32 => lanetype.F32
  | numtype.F64 => lanetype.F64

def lanetype_packtype (var_0 : packtype) : lanetype :=
  match var_0 with
  | packtype.I8 => lanetype.I8
  | packtype.I16 => lanetype.I16

abbrev Pnn : Type := packtype

inductive Jnn : Type where
  | I32 : Jnn
  | I64 : Jnn
  | I8 : Jnn
  | I16 : Jnn
deriving Inhabited, BEq

def lanetype_Jnn (var_0 : Jnn) : lanetype :=
  match var_0 with
  | Jnn.I32 => lanetype.I32
  | Jnn.I64 => lanetype.I64
  | Jnn.I8 => lanetype.I8
  | Jnn.I16 => lanetype.I16

def Jnn_addrtype (var_0 : addrtype) : Jnn :=
  match var_0 with
  | addrtype.I32 => Jnn.I32
  | addrtype.I64 => Jnn.I64

abbrev Lnn : Type := lanetype

inductive limits : Type where
  | mk_limits (v_u64 : u64) (u64_opt : Option u64) : limits
deriving Inhabited, BEq

inductive wf_limits : limits → Prop where
  | limits_case_0 (v_u64 : u64) (u64_opt : Option u64) :
    wf_uN 64 v_u64 →
    Forall (fun v_u64_elem => wf_uN 64 v_u64_elem) (Option.toList u64_opt) →
    wf_limits (limits.mk_limits v_u64 u64_opt)


abbrev tagtype : Type := typeuse

inductive globaltype : Type where
  | mk_globaltype (mut_opt : Option «mut») (v_valtype : valtype) : globaltype
deriving Inhabited, BEq

inductive wf_globaltype : globaltype → Prop where
  | globaltype_case_0 (mut_opt : Option «mut») (v_valtype : valtype) :
    wf_valtype v_valtype →
    wf_globaltype (globaltype.mk_globaltype mut_opt v_valtype)


inductive memtype : Type where
  | PAGE (v_addrtype : addrtype) (v_limits : limits) : memtype
deriving Inhabited, BEq

inductive wf_memtype : memtype → Prop where
  | memtype_case_0 (v_addrtype : addrtype) (v_limits : limits) :
    wf_limits v_limits →
    wf_memtype (memtype.PAGE v_addrtype v_limits)


inductive tabletype : Type where
  | mk_tabletype (v_addrtype : addrtype) (v_limits : limits) (v_reftype : reftype) : tabletype
deriving Inhabited, BEq

inductive wf_tabletype : tabletype → Prop where
  | tabletype_case_0 (v_addrtype : addrtype) (v_limits : limits) (v_reftype : reftype) :
    wf_limits v_limits →
    wf_reftype v_reftype →
    wf_tabletype (tabletype.mk_tabletype v_addrtype v_limits v_reftype)


inductive datatype : Type where
  | OK : datatype
deriving Inhabited, BEq

abbrev elemtype : Type := reftype

inductive externtype : Type where
  | TAG (v_tagtype : tagtype) : externtype
  | GLOBAL (v_globaltype : globaltype) : externtype
  | MEM (v_memtype : memtype) : externtype
  | TABLE (v_tabletype : tabletype) : externtype
  | FUNC (v_typeuse : typeuse) : externtype
deriving Inhabited, BEq

inductive wf_externtype : externtype → Prop where
  | externtype_case_0 (v_tagtype : tagtype) :
    wf_typeuse v_tagtype →
    wf_externtype (externtype.TAG v_tagtype)
  | externtype_case_1 (v_globaltype : globaltype) :
    wf_globaltype v_globaltype →
    wf_externtype (externtype.GLOBAL v_globaltype)
  | externtype_case_2 (v_memtype : memtype) :
    wf_memtype v_memtype →
    wf_externtype (externtype.MEM v_memtype)
  | externtype_case_3 (v_tabletype : tabletype) :
    wf_tabletype v_tabletype →
    wf_externtype (externtype.TABLE v_tabletype)
  | externtype_case_4 (v_typeuse : typeuse) :
    wf_typeuse v_typeuse →
    wf_externtype (externtype.FUNC v_typeuse)


inductive moduletype : Type where
  | mk_moduletype (externtype_lst_0 : List externtype) (externtype_lst_1 : List externtype) : moduletype
deriving Inhabited, BEq

inductive wf_moduletype : moduletype → Prop where
  | moduletype_case_0 (externtype_lst : List externtype) (externtype_lst_0_lst : List externtype) :
    Forall (fun v_externtype_elem => wf_externtype v_externtype_elem) externtype_lst →
    Forall (fun externtype_lst_0_elem => wf_externtype externtype_lst_0_elem) externtype_lst_0_lst →
    wf_moduletype (moduletype.mk_moduletype externtype_lst externtype_lst_0_lst)


def IN (v_N : N) : Option Inn :=
  match v_N with
  | 32 => some addrtype.I32
  | 64 => some addrtype.I64
  | _ => none

def FN (v_N : N) : Option Fnn :=
  match v_N with
  | 32 => some Fnn.F32
  | 64 => some Fnn.F64
  | _ => none

def JN (v_N : N) : Option Jnn :=
  match v_N with
  | 8 => some Jnn.I8
  | 16 => some Jnn.I16
  | 32 => some Jnn.I32
  | 64 => some Jnn.I64
  | _ => none

def size (v_numtype : numtype) : Nat :=
  match v_numtype with
  | numtype.I32 => 32
  | numtype.I64 => 64
  | numtype.F32 => 32
  | numtype.F64 => 64

def vsize (v_vectype : vectype) : Nat :=
  match v_vectype with
  | vectype.V128 => 128

def psize (v_packtype : packtype) : Nat :=
  match v_packtype with
  | packtype.I8 => 8
  | packtype.I16 => 16

def lsize (v_lanetype : lanetype) : Nat :=
  match v_lanetype with
  | lanetype.I32 => size numtype.I32
  | lanetype.I64 => size numtype.I64
  | lanetype.F32 => size numtype.F32
  | lanetype.F64 => size numtype.F64
  | lanetype.I8 => psize packtype.I8
  | lanetype.I16 => psize packtype.I16

def zsize (v_storagetype : storagetype) : Option Nat :=
  match v_storagetype with
  | storagetype.I32 => some (size numtype.I32)
  | storagetype.I64 => some (size numtype.I64)
  | storagetype.F32 => some (size numtype.F32)
  | storagetype.F64 => some (size numtype.F64)
  | storagetype.V128 => some (vsize vectype.V128)
  | storagetype.I8 => some (psize packtype.I8)
  | storagetype.I16 => some (psize packtype.I16)
  | _ => none

def isize (v_Inn : Inn) : Nat :=
  size (numtype_addrtype v_Inn)

def jsize (v_Jnn : Jnn) : Nat :=
  lsize (lanetype_Jnn v_Jnn)

def fsize (v_Fnn : Fnn) : Nat :=
  size (numtype_Fnn v_Fnn)

def inv_isize (nat : Nat) : Option Inn :=
  match nat with
  | 32 => some addrtype.I32
  | 64 => some addrtype.I64
  | _ => none

def inv_jsize (nat : Nat) : Option Jnn :=
  match nat with
  | 8 => some Jnn.I8
  | 16 => some Jnn.I16
  | _ => OMap (fun iter_val_1_elem => Jnn_addrtype iter_val_1_elem) (inv_isize nat)

def inv_fsize (nat : Nat) : Option Fnn :=
  match nat with
  | 32 => some Fnn.F32
  | 64 => some Fnn.F64
  | _ => none

def sizenn (v_numtype : numtype) : Nat :=
  size v_numtype

def sizenn1 (v_numtype : numtype) : Nat :=
  size v_numtype

def sizenn2 (v_numtype : numtype) : Nat :=
  size v_numtype

def vsizenn (v_vectype : vectype) : Nat :=
  vsize v_vectype

def psizenn (v_packtype : packtype) : Nat :=
  psize v_packtype

def lsizenn (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

def lsizenn1 (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

def lsizenn2 (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

def jsizenn (v_Jnn : Jnn) : Nat :=
  lsize (lanetype_Jnn v_Jnn)

def inv_jsizenn (nat : Nat) : Option Jnn :=
  inv_jsize nat

def lunpack (v_lanetype : lanetype) : numtype :=
  match v_lanetype with
  | lanetype.I32 => numtype.I32
  | lanetype.I64 => numtype.I64
  | lanetype.F32 => numtype.F32
  | lanetype.F64 => numtype.F64
  | lanetype.I8 => numtype.I32
  | lanetype.I16 => numtype.I32

def unpack (v_storagetype : storagetype) : valtype :=
  match v_storagetype with
  | storagetype.BOT => valtype.BOT
  | storagetype.REF null_opt v_heaptype => valtype.REF null_opt v_heaptype
  | storagetype.V128 => valtype.V128
  | storagetype.F64 => valtype.F64
  | storagetype.F32 => valtype.F32
  | storagetype.I64 => valtype.I64
  | storagetype.I32 => valtype.I32
  | storagetype.I8 => valtype.I32
  | storagetype.I16 => valtype.I32

inductive unpack_is_wf : storagetype → valtype → Prop where
  | unpack_is_wf_0 (v_storagetype : storagetype) (ret_val : valtype) :
    wf_storagetype v_storagetype →
    ret_val = (unpack v_storagetype) →
    wf_valtype ret_val →
    unpack_is_wf v_storagetype ret_val


def nunpack (v_storagetype : storagetype) : Option numtype :=
  match v_storagetype with
  | storagetype.I32 => some numtype.I32
  | storagetype.I64 => some numtype.I64
  | storagetype.F32 => some numtype.F32
  | storagetype.F64 => some numtype.F64
  | storagetype.I8 => some numtype.I32
  | storagetype.I16 => some numtype.I32
  | _ => none

def vunpack (v_storagetype : storagetype) : Option vectype :=
  match v_storagetype with
  | storagetype.V128 => some vectype.V128
  | _ => none

def cunpack (v_storagetype : storagetype) : Option consttype :=
  match v_storagetype with
  | storagetype.I32 => some consttype.I32
  | storagetype.I64 => some consttype.I64
  | storagetype.F32 => some consttype.F32
  | storagetype.F64 => some consttype.F64
  | storagetype.V128 => some consttype.V128
  | storagetype.I8 => some consttype.I32
  | storagetype.I16 => some consttype.I32
  -- | storagetype.I32 => some (consttype_numtype (lunpack lanetype.I32))
  -- | storagetype.I64 => some (consttype_numtype (lunpack lanetype.I64))
  -- | storagetype.F32 => some (consttype_numtype (lunpack lanetype.F32))
  -- | storagetype.F64 => some (consttype_numtype (lunpack lanetype.F64))
  -- | storagetype.I8 => some (consttype_numtype (lunpack lanetype.I8))
  -- | storagetype.I16 => some (consttype_numtype (lunpack lanetype.I16))
  | _ => none

def minat (v_addrtype : addrtype) (addrtype_0 : addrtype) : addrtype :=
  if
    (size (numtype_addrtype v_addrtype)) ≤ (size (numtype_addrtype addrtype_0))
  then
    v_addrtype
  else
    addrtype_0

def diffrt (v_reftype : reftype) (reftype_0 : reftype) : reftype :=
  match v_reftype, reftype_0 with
  | reftype.REF null_1_opt ht_1, reftype.REF (some null.NULL) ht_2 => reftype.REF none ht_1
  | reftype.REF null_1_opt ht_1, reftype.REF none ht_2 => reftype.REF null_1_opt ht_1

inductive diffrt_is_wf : reftype → reftype → reftype → Prop where
  | diffrt_is_wf_0 (v_reftype : reftype) (reftype_0 : reftype) (ret_val : reftype) :
    wf_reftype v_reftype →
    wf_reftype reftype_0 →
    ret_val = (diffrt v_reftype reftype_0) →
    wf_reftype ret_val →
    diffrt_is_wf v_reftype reftype_0 ret_val


def as_deftype (v_typeuse : typeuse) : Option deftype :=
  match v_typeuse with
  | typeuse._DEF v_rectype v_n => some (deftype._DEF v_rectype v_n)
  | _ => none

inductive fun_tagsxt : List externtype → List tagtype → Prop where
  | fun_tagsxt_case_0 : fun_tagsxt [] []
  | fun_tagsxt_case_1 (jt : typeuse) (xt_lst : List externtype) (var_0 : List tagtype) :
    fun_tagsxt xt_lst var_0 →
    fun_tagsxt ([externtype.TAG jt] ++ xt_lst) ([jt] ++ var_0)
  | fun_tagsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List tagtype) :
    fun_tagsxt xt_lst var_0 →
    fun_tagsxt ([v_externtype] ++ xt_lst) var_0


inductive tagsxt_is_wf : List externtype → List tagtype → Prop where
  | tagsxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List tagtype) (var_0 : List tagtype) :
    fun_tagsxt var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externtype var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_typeuse ret_val_elem) ret_val_lst →
    tagsxt_is_wf var_0_lst ret_val_lst


inductive fun_globalsxt : List externtype → List globaltype → Prop where
  | fun_globalsxt_case_0 : fun_globalsxt [] []
  | fun_globalsxt_case_1 (gt : globaltype) (xt_lst : List externtype) (var_0 : List globaltype) :
    fun_globalsxt xt_lst var_0 →
    fun_globalsxt ([externtype.GLOBAL gt] ++ xt_lst) ([gt] ++ var_0)
  | fun_globalsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List globaltype) :
    fun_globalsxt xt_lst var_0 →
    fun_globalsxt ([v_externtype] ++ xt_lst) var_0


inductive globalsxt_is_wf : List externtype → List globaltype → Prop where
  | globalsxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List globaltype) (var_0 : List globaltype) :
    fun_globalsxt var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externtype var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_globaltype ret_val_elem) ret_val_lst →
    globalsxt_is_wf var_0_lst ret_val_lst


inductive fun_memsxt : List externtype → List memtype → Prop where
  | fun_memsxt_case_0 : fun_memsxt [] []
  | fun_memsxt_case_1 (mt : memtype) (xt_lst : List externtype) (var_0 : List memtype) :
    fun_memsxt xt_lst var_0 →
    fun_memsxt ([externtype.MEM mt] ++ xt_lst) ([mt] ++ var_0)
  | fun_memsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List memtype) :
    fun_memsxt xt_lst var_0 →
    fun_memsxt ([v_externtype] ++ xt_lst) var_0


inductive memsxt_is_wf : List externtype → List memtype → Prop where
  | memsxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List memtype) (var_0 : List memtype) :
    fun_memsxt var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externtype var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_memtype ret_val_elem) ret_val_lst →
    memsxt_is_wf var_0_lst ret_val_lst


inductive fun_tablesxt : List externtype → List tabletype → Prop where
  | fun_tablesxt_case_0 : fun_tablesxt [] []
  | fun_tablesxt_case_1 (tt : tabletype) (xt_lst : List externtype) (var_0 : List tabletype) :
    fun_tablesxt xt_lst var_0 →
    fun_tablesxt ([externtype.TABLE tt] ++ xt_lst) ([tt] ++ var_0)
  | fun_tablesxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List tabletype) :
    fun_tablesxt xt_lst var_0 →
    fun_tablesxt ([v_externtype] ++ xt_lst) var_0


inductive tablesxt_is_wf : List externtype → List tabletype → Prop where
  | tablesxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List tabletype) (var_0 : List tabletype) :
    fun_tablesxt var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externtype var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_tabletype ret_val_elem) ret_val_lst →
    tablesxt_is_wf var_0_lst ret_val_lst


inductive fun_funcsxt : List externtype → List deftype → Prop where
  | fun_funcsxt_case_0 : fun_funcsxt [] []
  | fun_funcsxt_case_1 (v_rectype : rectype) (v_n : n) (xt_lst : List externtype) (var_0 : List deftype) :
    fun_funcsxt xt_lst var_0 →
    fun_funcsxt ([externtype.FUNC (typeuse._DEF v_rectype v_n)] ++ xt_lst) ([deftype._DEF v_rectype v_n] ++ var_0)
  | fun_funcsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List deftype) :
    fun_funcsxt xt_lst var_0 →
    fun_funcsxt ([v_externtype] ++ xt_lst) var_0


inductive fun_subst_typevar_before_fun_subst_typevar_case_2 : typevar → List typevar → List typeuse → Prop where
  | fun_subst_typevar_case_1 (tv : typevar) (tv_1 : typevar) (tv'_lst : List typevar) (tu_1 : typeuse) (tu'_lst : List typeuse) (var_0 : Option typeuse) : fun_subst_typevar_before_fun_subst_typevar_case_2 tv ([tv_1] ++ tv'_lst) ([tu_1] ++ tu'_lst)
  | fun_subst_typevar_case_0 (tv : typevar) : fun_subst_typevar_before_fun_subst_typevar_case_2 tv [] []


inductive fun_subst_typevar : typevar → List typevar → List typeuse → Option typeuse → Prop where
  | fun_subst_typevar_case_0 (tv : typevar) : fun_subst_typevar tv [] [] (some (typeuse_typevar tv))
  | fun_subst_typevar_case_1 (tv : typevar) (tv_1 : typevar) (tv'_lst : List typevar) (tu_1 : typeuse) (tu'_lst : List typeuse) (var_0 : Option typeuse) :
    fun_subst_typevar tv tv'_lst tu'_lst var_0 →
    fun_subst_typevar tv ([tv_1] ++ tv'_lst) ([tu_1] ++ tu'_lst) (OMap (fun iter_val_2_elem => if
      tv == tv_1
    then
      tu_1
    else
      iter_val_2_elem) var_0)
  | fun_subst_typevar_case_2 (x0 : typevar) (x1 : List typevar) (x2 : List typeuse) :
    ¬ fun_subst_typevar_before_fun_subst_typevar_case_2 x0 x1 x2 →
    fun_subst_typevar x0 x1 x2 none


inductive subst_typevar_is_wf : typevar → List typevar → List typeuse → typeuse → Prop where
  | subst_typevar_is_wf_0 (v_typevar : typevar) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : typeuse) (var_0 : Option typeuse) :
    fun_subst_typevar v_typevar var_0_lst var_1_lst var_0 →
    wf_typevar v_typevar →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    var_0 ≠ none →
    ret_val = (Option.get! var_0) →
    wf_typeuse ret_val →
    subst_typevar_is_wf v_typevar var_0_lst var_1_lst ret_val


def minus_recs (var_0_lst : List typevar) (var_1_lst : List typeuse) : Option (List typevar × List typeuse) :=
  match var_0_lst, var_1_lst with
  | [], [] => some (([], []))
  | (typevar.REC v_n) :: tv_lst, tu_1 :: tu_lst => minus_recs tv_lst tu_lst
  | (typevar._IDX x) :: tv_lst, tu_1 :: tu_lst => let (tv'_lst, tu'_lst) := Option.get! (minus_recs tv_lst tu_lst)
  some (([typevar._IDX x] ++ tv'_lst, [tu_1] ++ tu'_lst))
  | _, _ => none

inductive minus_recs_is_wf : List typevar → List typeuse → List typevar × List typeuse → Prop where
  | minus_recs_is_wf_0 (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : List typevar × List typeuse) :
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    (minus_recs var_0_lst var_1_lst) ≠ none →
    ret_val = (Option.get! (minus_recs var_0_lst var_1_lst)) →
    Forall (fun iter_elem => wf_typevar iter_elem) (ret_val.1) →
    Forall (fun iter_elem => wf_typeuse iter_elem) (ret_val.2) →
    minus_recs_is_wf var_0_lst var_1_lst ret_val


def subst_packtype (v_packtype : packtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) : packtype :=
  v_packtype

def subst_numtype (v_numtype : numtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) : numtype :=
  v_numtype

def subst_vectype (v_vectype : vectype) (var_0_lst : List typevar) (var_1_lst : List typeuse) : vectype :=
  v_vectype

mutual
inductive fun_subst_typeuse : typeuse → List typevar → List typeuse → typeuse → Prop where
  | fun_subst_typeuse_case_0 (v_n : n) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : Option typeuse) :
    var_0 ≠ none →
    fun_subst_typevar (typevar.REC v_n) tv_lst tu_lst var_0 →
    fun_subst_typeuse (typeuse.REC v_n) tv_lst tu_lst (Option.get! var_0)
  | fun_subst_typeuse_case_1 (v_typeidx : typeidx) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : Option typeuse) :
    var_0 ≠ none →
    fun_subst_typevar (typevar._IDX v_typeidx) tv_lst tu_lst var_0 →
    fun_subst_typeuse (typeuse._IDX v_typeidx) tv_lst tu_lst (Option.get! var_0)
  | fun_subst_typeuse_case_2 (v_rectype : rectype) (v_n : n) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : deftype) :
    fun_subst_deftype (deftype._DEF v_rectype v_n) tv_lst tu_lst var_0 →
    fun_subst_typeuse (typeuse._DEF v_rectype v_n) tv_lst tu_lst (typeuse_deftype var_0)

inductive fun_subst_heaptype : heaptype → List typevar → List typeuse → heaptype → Prop where
  | fun_subst_heaptype_case_0 (v_n : n) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : Option typeuse) :
    var_0 ≠ none →
    fun_subst_typevar (typevar.REC v_n) tv_lst tu_lst var_0 →
    fun_subst_heaptype (heaptype.REC v_n) tv_lst tu_lst (heaptype_typeuse (Option.get! var_0))
  | fun_subst_heaptype_case_1 (v_typeidx : typeidx) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : Option typeuse) :
    var_0 ≠ none →
    fun_subst_typevar (typevar._IDX v_typeidx) tv_lst tu_lst var_0 →
    fun_subst_heaptype (heaptype._IDX v_typeidx) tv_lst tu_lst (heaptype_typeuse (Option.get! var_0))
  | fun_subst_heaptype_case_2 (v_rectype : rectype) (v_n : n) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : deftype) :
    fun_subst_deftype (deftype._DEF v_rectype v_n) tv_lst tu_lst var_0 →
    fun_subst_heaptype (heaptype._DEF v_rectype v_n) tv_lst tu_lst (heaptype_deftype var_0)
  | fun_subst_heaptype_case_3 (ht : heaptype) (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_heaptype ht tv_lst tu_lst ht

inductive fun_subst_reftype : reftype → List typevar → List typeuse → reftype → Prop where
  | fun_subst_reftype_case_0 (null_opt : Option null) (ht : heaptype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : heaptype) :
    fun_subst_heaptype ht tv_lst tu_lst var_0 →
    fun_subst_reftype (reftype.REF null_opt ht) tv_lst tu_lst (reftype.REF null_opt var_0)

inductive fun_subst_valtype : valtype → List typevar → List typeuse → valtype → Prop where
  | fun_subst_valtype_case_0 (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_valtype valtype.I32 tv_lst tu_lst (valtype_numtype (subst_numtype numtype.I32 tv_lst tu_lst))
  | fun_subst_valtype_case_1 (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_valtype valtype.I64 tv_lst tu_lst (valtype_numtype (subst_numtype numtype.I64 tv_lst tu_lst))
  | fun_subst_valtype_case_2 (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_valtype valtype.F32 tv_lst tu_lst (valtype_numtype (subst_numtype numtype.F32 tv_lst tu_lst))
  | fun_subst_valtype_case_3 (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_valtype valtype.F64 tv_lst tu_lst (valtype_numtype (subst_numtype numtype.F64 tv_lst tu_lst))
  | fun_subst_valtype_case_4 (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_valtype valtype.V128 tv_lst tu_lst (valtype_vectype (subst_vectype vectype.V128 tv_lst tu_lst))
  | fun_subst_valtype_case_5 (null_opt : Option null) (v_heaptype : heaptype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : reftype) :
    fun_subst_reftype (reftype.REF null_opt v_heaptype) tv_lst tu_lst var_0 →
    fun_subst_valtype (valtype.REF null_opt v_heaptype) tv_lst tu_lst (valtype_reftype var_0)
  | fun_subst_valtype_case_6 (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_valtype valtype.BOT tv_lst tu_lst valtype.BOT

inductive fun_subst_storagetype : storagetype → List typevar → List typeuse → storagetype → Prop where
  | fun_subst_storagetype_case_0 (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : valtype) :
    fun_subst_valtype valtype.BOT tv_lst tu_lst var_0 →
    fun_subst_storagetype storagetype.BOT tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_1 (null_opt : Option null) (v_heaptype : heaptype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : valtype) :
    fun_subst_valtype (valtype.REF null_opt v_heaptype) tv_lst tu_lst var_0 →
    fun_subst_storagetype (storagetype.REF null_opt v_heaptype) tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_2 (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : valtype) :
    fun_subst_valtype valtype.V128 tv_lst tu_lst var_0 →
    fun_subst_storagetype storagetype.V128 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_3 (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : valtype) :
    fun_subst_valtype valtype.F64 tv_lst tu_lst var_0 →
    fun_subst_storagetype storagetype.F64 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_4 (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : valtype) :
    fun_subst_valtype valtype.F32 tv_lst tu_lst var_0 →
    fun_subst_storagetype storagetype.F32 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_5 (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : valtype) :
    fun_subst_valtype valtype.I64 tv_lst tu_lst var_0 →
    fun_subst_storagetype storagetype.I64 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_6 (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : valtype) :
    fun_subst_valtype valtype.I32 tv_lst tu_lst var_0 →
    fun_subst_storagetype storagetype.I32 tv_lst tu_lst (storagetype_valtype var_0)
  | fun_subst_storagetype_case_7 (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_storagetype storagetype.I8 tv_lst tu_lst (storagetype_packtype (subst_packtype packtype.I8 tv_lst tu_lst))
  | fun_subst_storagetype_case_8 (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_storagetype storagetype.I16 tv_lst tu_lst (storagetype_packtype (subst_packtype packtype.I16 tv_lst tu_lst))

inductive fun_subst_fieldtype : fieldtype → List typevar → List typeuse → fieldtype → Prop where
  | fun_subst_fieldtype_case_0 (mut_opt : Option «mut») (zt : storagetype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : storagetype) :
    fun_subst_storagetype zt tv_lst tu_lst var_0 →
    fun_subst_fieldtype (fieldtype.mk_fieldtype mut_opt zt) tv_lst tu_lst (fieldtype.mk_fieldtype mut_opt var_0)

inductive fun_subst_comptype : comptype → List typevar → List typeuse → comptype → Prop where
  | fun_subst_comptype_case_0 (ft_lst : List fieldtype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0_lst : List fieldtype) :
    (List.length var_0_lst) = (List.length ft_lst) →
    Forall₂ (fun var_0_elem ft_elem => fun_subst_fieldtype ft_elem tv_lst tu_lst var_0_elem) var_0_lst ft_lst →
    fun_subst_comptype (comptype.STRUCT (list.mk_list ft_lst)) tv_lst tu_lst (comptype.STRUCT (list.mk_list var_0_lst))
  | fun_subst_comptype_case_1 (ft : fieldtype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : fieldtype) :
    fun_subst_fieldtype ft tv_lst tu_lst var_0 →
    fun_subst_comptype (comptype.ARRAY ft) tv_lst tu_lst (comptype.ARRAY var_0)
  | fun_subst_comptype_case_2 (t_1_lst : List valtype) (t_2_lst : List valtype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_1_lst : List valtype) (var_0_lst : List valtype) :
    (List.length var_1_lst) = (List.length t_2_lst) →
    Forall₂ (fun var_1_elem t_2_elem => fun_subst_valtype t_2_elem tv_lst tu_lst var_1_elem) var_1_lst t_2_lst →
    (List.length var_0_lst) = (List.length t_1_lst) →
    Forall₂ (fun var_0_elem t_1_elem => fun_subst_valtype t_1_elem tv_lst tu_lst var_0_elem) var_0_lst t_1_lst →
    fun_subst_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) tv_lst tu_lst (comptype.FUNC (.mk_list var_0_lst) (.mk_list var_1_lst))

inductive fun_subst_subtype : subtype → List typevar → List typeuse → subtype → Prop where
  | fun_subst_subtype_case_0 (final_opt : Option final) (tu'_lst : List typeuse) (ct : comptype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_1 : comptype) (var_0_lst : List typeuse) :
    fun_subst_comptype ct tv_lst tu_lst var_1 →
    (List.length var_0_lst) = (List.length tu'_lst) →
    Forall₂ (fun var_0_elem tu'_elem => fun_subst_typeuse tu'_elem tv_lst tu_lst var_0_elem) var_0_lst tu'_lst →
    fun_subst_subtype (subtype.SUB final_opt tu'_lst ct) tv_lst tu_lst (subtype.SUB final_opt var_0_lst var_1)

inductive fun_subst_rectype : rectype → List typevar → List typeuse → rectype → Prop where
  | fun_subst_rectype_case_0 (st_lst : List subtype) (tv_lst : List typevar) (tu_lst : List typeuse) (tv'_lst : List typevar) (tu'_lst : List typeuse) (var_0_lst : List subtype) :
    (List.length var_0_lst) = (List.length st_lst) →
    Forall₂ (fun var_0_elem st_elem => fun_subst_subtype st_elem tv'_lst tu'_lst var_0_elem) var_0_lst st_lst →
    (minus_recs tv_lst tu_lst) ≠ none →
    ((tv'_lst, tu'_lst)) = (Option.get! (minus_recs tv_lst tu_lst)) →
    fun_subst_rectype (rectype.REC (list.mk_list st_lst)) tv_lst tu_lst (rectype.REC (list.mk_list var_0_lst))

inductive fun_subst_deftype : deftype → List typevar → List typeuse → deftype → Prop where
  | fun_subst_deftype_case_0 (qt : rectype) (i : Nat) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : rectype) :
    fun_subst_rectype qt tv_lst tu_lst var_0 →
    fun_subst_deftype (deftype._DEF qt i) tv_lst tu_lst (deftype._DEF var_0 i)


end

mutual
inductive subst_typeuse_is_wf : typeuse → List typevar → List typeuse → typeuse → Prop where
  | subst_typeuse_is_wf_0 (v_typeuse : typeuse) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : typeuse) (var_0 : typeuse) :
    fun_subst_typeuse v_typeuse var_0_lst var_1_lst var_0 →
    wf_typeuse v_typeuse →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_typeuse ret_val →
    subst_typeuse_is_wf v_typeuse var_0_lst var_1_lst ret_val

inductive subst_heaptype_is_wf : heaptype → List typevar → List typeuse → heaptype → Prop where
  | subst_heaptype_is_wf_0 (v_heaptype : heaptype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : heaptype) (var_0 : heaptype) :
    fun_subst_heaptype v_heaptype var_0_lst var_1_lst var_0 →
    wf_heaptype v_heaptype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_heaptype ret_val →
    subst_heaptype_is_wf v_heaptype var_0_lst var_1_lst ret_val

inductive subst_reftype_is_wf : reftype → List typevar → List typeuse → reftype → Prop where
  | subst_reftype_is_wf_0 (v_reftype : reftype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : reftype) (var_0 : reftype) :
    fun_subst_reftype v_reftype var_0_lst var_1_lst var_0 →
    wf_reftype v_reftype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_reftype ret_val →
    subst_reftype_is_wf v_reftype var_0_lst var_1_lst ret_val

inductive subst_valtype_is_wf : valtype → List typevar → List typeuse → valtype → Prop where
  | subst_valtype_is_wf_0 (v_valtype : valtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : valtype) (var_0 : valtype) :
    fun_subst_valtype v_valtype var_0_lst var_1_lst var_0 →
    wf_valtype v_valtype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_valtype ret_val →
    subst_valtype_is_wf v_valtype var_0_lst var_1_lst ret_val

inductive subst_storagetype_is_wf : storagetype → List typevar → List typeuse → storagetype → Prop where
  | subst_storagetype_is_wf_0 (v_storagetype : storagetype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : storagetype) (var_0 : storagetype) :
    fun_subst_storagetype v_storagetype var_0_lst var_1_lst var_0 →
    wf_storagetype v_storagetype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_storagetype ret_val →
    subst_storagetype_is_wf v_storagetype var_0_lst var_1_lst ret_val

inductive subst_fieldtype_is_wf : fieldtype → List typevar → List typeuse → fieldtype → Prop where
  | subst_fieldtype_is_wf_0 (v_fieldtype : fieldtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : fieldtype) (var_0 : fieldtype) :
    fun_subst_fieldtype v_fieldtype var_0_lst var_1_lst var_0 →
    wf_fieldtype v_fieldtype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_fieldtype ret_val →
    subst_fieldtype_is_wf v_fieldtype var_0_lst var_1_lst ret_val

inductive subst_comptype_is_wf : comptype → List typevar → List typeuse → comptype → Prop where
  | subst_comptype_is_wf_0 (v_comptype : comptype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : comptype) (var_0 : comptype) :
    fun_subst_comptype v_comptype var_0_lst var_1_lst var_0 →
    wf_comptype v_comptype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_comptype ret_val →
    subst_comptype_is_wf v_comptype var_0_lst var_1_lst ret_val

inductive subst_subtype_is_wf : subtype → List typevar → List typeuse → subtype → Prop where
  | subst_subtype_is_wf_0 (v_subtype : subtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : subtype) (var_0 : subtype) :
    fun_subst_subtype v_subtype var_0_lst var_1_lst var_0 →
    wf_subtype v_subtype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_subtype ret_val →
    subst_subtype_is_wf v_subtype var_0_lst var_1_lst ret_val


end

def subst_addrtype (v_addrtype : addrtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) : addrtype :=
  v_addrtype

inductive fun_subst_tagtype : tagtype → List typevar → List typeuse → tagtype → Prop where
  | fun_subst_tagtype_case_0 (tu' : typeuse) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : tagtype) :
    fun_subst_typeuse tu' tv_lst tu_lst var_0 →
    fun_subst_tagtype tu' tv_lst tu_lst var_0


inductive subst_tagtype_is_wf : tagtype → List typevar → List typeuse → tagtype → Prop where
  | subst_tagtype_is_wf_0 (v_tagtype : tagtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : tagtype) (var_0 : tagtype) :
    fun_subst_tagtype v_tagtype var_0_lst var_1_lst var_0 →
    wf_typeuse v_tagtype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_typeuse ret_val →
    subst_tagtype_is_wf v_tagtype var_0_lst var_1_lst ret_val


inductive fun_subst_globaltype : globaltype → List typevar → List typeuse → globaltype → Prop where
  | fun_subst_globaltype_case_0 (mut_opt : Option «mut») (t : valtype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : valtype) :
    fun_subst_valtype t tv_lst tu_lst var_0 →
    fun_subst_globaltype (globaltype.mk_globaltype mut_opt t) tv_lst tu_lst (globaltype.mk_globaltype mut_opt var_0)


inductive subst_globaltype_is_wf : globaltype → List typevar → List typeuse → globaltype → Prop where
  | subst_globaltype_is_wf_0 (v_globaltype : globaltype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : globaltype) (var_0 : globaltype) :
    fun_subst_globaltype v_globaltype var_0_lst var_1_lst var_0 →
    wf_globaltype v_globaltype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_globaltype ret_val →
    subst_globaltype_is_wf v_globaltype var_0_lst var_1_lst ret_val


def subst_memtype (v_memtype : memtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) : memtype :=
  match v_memtype with
  | memtype.PAGE «at» lim => memtype.PAGE «at» lim

inductive subst_memtype_is_wf : memtype → List typevar → List typeuse → memtype → Prop where
  | subst_memtype_is_wf_0 (v_memtype : memtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : memtype) :
    wf_memtype v_memtype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = (subst_memtype v_memtype var_0_lst var_1_lst) →
    wf_memtype ret_val →
    subst_memtype_is_wf v_memtype var_0_lst var_1_lst ret_val


inductive fun_subst_tabletype : tabletype → List typevar → List typeuse → tabletype → Prop where
  | fun_subst_tabletype_case_0 («at» : addrtype) (lim : limits) (rt : reftype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : reftype) :
    fun_subst_reftype rt tv_lst tu_lst var_0 →
    fun_subst_tabletype (tabletype.mk_tabletype «at» lim rt) tv_lst tu_lst (tabletype.mk_tabletype «at» lim var_0)


inductive subst_tabletype_is_wf : tabletype → List typevar → List typeuse → tabletype → Prop where
  | subst_tabletype_is_wf_0 (v_tabletype : tabletype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : tabletype) (var_0 : tabletype) :
    fun_subst_tabletype v_tabletype var_0_lst var_1_lst var_0 →
    wf_tabletype v_tabletype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_tabletype ret_val →
    subst_tabletype_is_wf v_tabletype var_0_lst var_1_lst ret_val


inductive fun_subst_externtype : externtype → List typevar → List typeuse → externtype → Prop where
  | fun_subst_externtype_case_0 (jt : typeuse) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : tagtype) :
    fun_subst_tagtype jt tv_lst tu_lst var_0 →
    fun_subst_externtype (externtype.TAG jt) tv_lst tu_lst (externtype.TAG var_0)
  | fun_subst_externtype_case_1 (gt : globaltype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : globaltype) :
    fun_subst_globaltype gt tv_lst tu_lst var_0 →
    fun_subst_externtype (externtype.GLOBAL gt) tv_lst tu_lst (externtype.GLOBAL var_0)
  | fun_subst_externtype_case_2 (tt : tabletype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : tabletype) :
    fun_subst_tabletype tt tv_lst tu_lst var_0 →
    fun_subst_externtype (externtype.TABLE tt) tv_lst tu_lst (externtype.TABLE var_0)
  | fun_subst_externtype_case_3 (mt : memtype) (tv_lst : List typevar) (tu_lst : List typeuse) : fun_subst_externtype (externtype.MEM mt) tv_lst tu_lst (externtype.MEM (subst_memtype mt tv_lst tu_lst))
  | fun_subst_externtype_case_4 (tu' : typeuse) (tv_lst : List typevar) (tu_lst : List typeuse) (var_0 : typeuse) :
    fun_subst_typeuse tu' tv_lst tu_lst var_0 →
    fun_subst_externtype (externtype.FUNC tu') tv_lst tu_lst (externtype.FUNC var_0)


inductive subst_externtype_is_wf : externtype → List typevar → List typeuse → externtype → Prop where
  | subst_externtype_is_wf_0 (v_externtype : externtype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : externtype) (var_0 : externtype) :
    fun_subst_externtype v_externtype var_0_lst var_1_lst var_0 →
    wf_externtype v_externtype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_externtype ret_val →
    subst_externtype_is_wf v_externtype var_0_lst var_1_lst ret_val


inductive fun_subst_moduletype : moduletype → List typevar → List typeuse → moduletype → Prop where
  | fun_subst_moduletype_case_0 (xt_1_lst : List externtype) (xt_2_lst : List externtype) (tv_lst : List typevar) (tu_lst : List typeuse) (var_1_lst : List externtype) (var_0_lst : List externtype) :
    (List.length var_1_lst) = (List.length xt_2_lst) →
    Forall₂ (fun var_1_elem xt_2_elem => fun_subst_externtype xt_2_elem tv_lst tu_lst var_1_elem) var_1_lst xt_2_lst →
    (List.length var_0_lst) = (List.length xt_1_lst) →
    Forall₂ (fun var_0_elem xt_1_elem => fun_subst_externtype xt_1_elem tv_lst tu_lst var_0_elem) var_0_lst xt_1_lst →
    fun_subst_moduletype (moduletype.mk_moduletype xt_1_lst xt_2_lst) tv_lst tu_lst (moduletype.mk_moduletype var_0_lst var_1_lst)


inductive subst_moduletype_is_wf : moduletype → List typevar → List typeuse → moduletype → Prop where
  | subst_moduletype_is_wf_0 (v_moduletype : moduletype) (var_0_lst : List typevar) (var_1_lst : List typeuse) (ret_val : moduletype) (var_0 : moduletype) :
    fun_subst_moduletype v_moduletype var_0_lst var_1_lst var_0 →
    wf_moduletype v_moduletype →
    Forall (fun var_0_elem => wf_typevar var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    ret_val = var_0 →
    wf_moduletype ret_val →
    subst_moduletype_is_wf v_moduletype var_0_lst var_1_lst ret_val


inductive fun_subst_all_valtype : valtype → List typeuse → valtype → Prop where
  | fun_subst_all_valtype_case_0 (t : valtype) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) (var_0 : valtype) :
    fun_subst_valtype t (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst var_0 →
    v_n = (List.length tu_lst) →
    fun_subst_all_valtype t tu_lst var_0


inductive subst_all_valtype_is_wf : valtype → List typeuse → valtype → Prop where
  | subst_all_valtype_is_wf_0 (v_valtype : valtype) (var_0_lst : List typeuse) (ret_val : valtype) (var_0 : valtype) :
    fun_subst_all_valtype v_valtype var_0_lst var_0 →
    wf_valtype v_valtype →
    Forall (fun var_0_elem => wf_typeuse var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_valtype ret_val →
    subst_all_valtype_is_wf v_valtype var_0_lst ret_val


inductive fun_subst_all_reftype : reftype → List typeuse → reftype → Prop where
  | fun_subst_all_reftype_case_0 (rt : reftype) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) (var_0 : reftype) :
    fun_subst_reftype rt (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst var_0 →
    v_n = (List.length tu_lst) →
    fun_subst_all_reftype rt tu_lst var_0


inductive subst_all_reftype_is_wf : reftype → List typeuse → reftype → Prop where
  | subst_all_reftype_is_wf_0 (v_reftype : reftype) (var_0_lst : List typeuse) (ret_val : reftype) (var_0 : reftype) :
    fun_subst_all_reftype v_reftype var_0_lst var_0 →
    wf_reftype v_reftype →
    Forall (fun var_0_elem => wf_typeuse var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_reftype ret_val →
    subst_all_reftype_is_wf v_reftype var_0_lst ret_val


inductive fun_subst_all_deftype : deftype → List typeuse → deftype → Prop where
  | fun_subst_all_deftype_case_0 (dt : deftype) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) (var_0 : deftype) :
    fun_subst_deftype dt (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst var_0 →
    v_n = (List.length tu_lst) →
    fun_subst_all_deftype dt tu_lst var_0


inductive fun_subst_all_tagtype : tagtype → List typeuse → tagtype → Prop where
  | fun_subst_all_tagtype_case_0 (jt : typeuse) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) (var_0 : tagtype) :
    fun_subst_tagtype jt (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst var_0 →
    v_n = (List.length tu_lst) →
    fun_subst_all_tagtype jt tu_lst var_0


inductive subst_all_tagtype_is_wf : tagtype → List typeuse → tagtype → Prop where
  | subst_all_tagtype_is_wf_0 (v_tagtype : tagtype) (var_0_lst : List typeuse) (ret_val : tagtype) (var_0 : tagtype) :
    fun_subst_all_tagtype v_tagtype var_0_lst var_0 →
    wf_typeuse v_tagtype →
    Forall (fun var_0_elem => wf_typeuse var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_typeuse ret_val →
    subst_all_tagtype_is_wf v_tagtype var_0_lst ret_val


inductive fun_subst_all_globaltype : globaltype → List typeuse → globaltype → Prop where
  | fun_subst_all_globaltype_case_0 (gt : globaltype) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) (var_0 : globaltype) :
    fun_subst_globaltype gt (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst var_0 →
    v_n = (List.length tu_lst) →
    fun_subst_all_globaltype gt tu_lst var_0


inductive subst_all_globaltype_is_wf : globaltype → List typeuse → globaltype → Prop where
  | subst_all_globaltype_is_wf_0 (v_globaltype : globaltype) (var_0_lst : List typeuse) (ret_val : globaltype) (var_0 : globaltype) :
    fun_subst_all_globaltype v_globaltype var_0_lst var_0 →
    wf_globaltype v_globaltype →
    Forall (fun var_0_elem => wf_typeuse var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_globaltype ret_val →
    subst_all_globaltype_is_wf v_globaltype var_0_lst ret_val


inductive fun_subst_all_memtype : memtype → List typeuse → memtype → Prop where
  | fun_subst_all_memtype_case_0 (mt : memtype) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) :
    v_n = (List.length tu_lst) →
    fun_subst_all_memtype mt tu_lst (subst_memtype mt (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst)


inductive subst_all_memtype_is_wf : memtype → List typeuse → memtype → Prop where
  | subst_all_memtype_is_wf_0 (v_memtype : memtype) (var_0_lst : List typeuse) (ret_val : memtype) (var_0 : memtype) :
    fun_subst_all_memtype v_memtype var_0_lst var_0 →
    wf_memtype v_memtype →
    Forall (fun var_0_elem => wf_typeuse var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_memtype ret_val →
    subst_all_memtype_is_wf v_memtype var_0_lst ret_val


inductive fun_subst_all_tabletype : tabletype → List typeuse → tabletype → Prop where
  | fun_subst_all_tabletype_case_0 (tt : tabletype) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) (var_0 : tabletype) :
    fun_subst_tabletype tt (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst var_0 →
    v_n = (List.length tu_lst) →
    fun_subst_all_tabletype tt tu_lst var_0


inductive subst_all_tabletype_is_wf : tabletype → List typeuse → tabletype → Prop where
  | subst_all_tabletype_is_wf_0 (v_tabletype : tabletype) (var_0_lst : List typeuse) (ret_val : tabletype) (var_0 : tabletype) :
    fun_subst_all_tabletype v_tabletype var_0_lst var_0 →
    wf_tabletype v_tabletype →
    Forall (fun var_0_elem => wf_typeuse var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_tabletype ret_val →
    subst_all_tabletype_is_wf v_tabletype var_0_lst ret_val


inductive fun_subst_all_externtype : externtype → List typeuse → externtype → Prop where
  | fun_subst_all_externtype_case_0 (xt : externtype) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) (var_0 : externtype) :
    fun_subst_externtype xt (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst var_0 →
    v_n = (List.length tu_lst) →
    fun_subst_all_externtype xt tu_lst var_0


inductive subst_all_externtype_is_wf : externtype → List typeuse → externtype → Prop where
  | subst_all_externtype_is_wf_0 (v_externtype : externtype) (var_0_lst : List typeuse) (ret_val : externtype) (var_0 : externtype) :
    fun_subst_all_externtype v_externtype var_0_lst var_0 →
    wf_externtype v_externtype →
    Forall (fun var_0_elem => wf_typeuse var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_externtype ret_val →
    subst_all_externtype_is_wf v_externtype var_0_lst ret_val


inductive fun_subst_all_moduletype : moduletype → List typeuse → moduletype → Prop where
  | fun_subst_all_moduletype_case_0 (mmt : moduletype) (v_n : Nat) (tu_lst : List typeuse) (i : Nat) (var_0 : moduletype) :
    fun_subst_moduletype mmt (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN i))) tu_lst var_0 →
    v_n = (List.length tu_lst) →
    fun_subst_all_moduletype mmt tu_lst var_0


inductive subst_all_moduletype_is_wf : moduletype → List typeuse → moduletype → Prop where
  | subst_all_moduletype_is_wf_0 (v_moduletype : moduletype) (var_0_lst : List typeuse) (ret_val : moduletype) (var_0 : moduletype) :
    fun_subst_all_moduletype v_moduletype var_0_lst var_0 →
    wf_moduletype v_moduletype →
    Forall (fun var_0_elem => wf_typeuse var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_moduletype ret_val →
    subst_all_moduletype_is_wf v_moduletype var_0_lst ret_val


inductive fun_subst_all_deftypes : List deftype → List typeuse → List deftype → Prop where
  | fun_subst_all_deftypes_case_0 (tu_lst : List typeuse) : fun_subst_all_deftypes [] tu_lst []
  | fun_subst_all_deftypes_case_1 (dt_1 : deftype) (dt_lst : List deftype) (tu_lst : List typeuse) (var_1 : List deftype) (var_0 : deftype) :
    fun_subst_all_deftypes dt_lst tu_lst var_1 →
    fun_subst_all_deftype dt_1 tu_lst var_0 →
    fun_subst_all_deftypes ([dt_1] ++ dt_lst) tu_lst ([var_0] ++ var_1)


inductive fun_rollrt : typeidx → rectype → rectype → Prop where
  | fun_rollrt_case_0 (x : uN) (v_rectype : rectype) (i : Nat) (v_n : Nat) (subtype_lst : List subtype) (var_0_lst : List subtype) :
    Forall₂ (fun var_0_elem v_subtype_elem => fun_subst_subtype v_subtype_elem (List.range v_n |>.map (fun i => typevar._IDX (uN.mk_uN ((proj_uN_0 x) + i)))) (List.range v_n |>.map (fun i => typeuse.REC i)) var_0_elem) var_0_lst subtype_lst →
    v_rectype = (rectype.REC (list.mk_list subtype_lst)) →
    fun_rollrt x v_rectype (rectype.REC (list.mk_list var_0_lst))


inductive fun_unrollrt : rectype → rectype → Prop where
  | fun_unrollrt_case_0 (v_rectype : rectype) (i : Nat) (v_n : Nat) (subtype_lst : List subtype) (var_0_lst : List subtype) :
    Forall₂ (fun var_0_elem v_subtype_elem => fun_subst_subtype v_subtype_elem (List.range v_n |>.map (fun i => typevar.REC i)) (List.range v_n |>.map (fun i => typeuse._DEF v_rectype i)) var_0_elem) var_0_lst subtype_lst →
    v_rectype = (rectype.REC (list.mk_list subtype_lst)) →
    fun_unrollrt v_rectype (rectype.REC (list.mk_list var_0_lst))


inductive fun_rolldt : typeidx → rectype → List deftype → Prop where
  | fun_rolldt_case_0 (x : uN) (v_rectype : rectype) (v_n : Nat) (subtype_lst : List subtype) (var_0 : rectype) :
    fun_rollrt x v_rectype var_0 →
    var_0 = (rectype.REC (list.mk_list subtype_lst)) →
    fun_rolldt x v_rectype (List.range v_n |>.map (fun i => deftype._DEF (rectype.REC (list.mk_list subtype_lst)) i))


inductive fun_unrolldt : deftype → subtype → Prop where
  | fun_unrolldt_case_0 (v_rectype : rectype) (i : Nat) (subtype_lst : List subtype) (var_0 : rectype) :
    i < (List.length subtype_lst) →
    fun_unrollrt v_rectype var_0 →
    (rectype.REC (list.mk_list subtype_lst)) = var_0 →
    fun_unrolldt (deftype._DEF v_rectype i) ((subtype_lst)[i]!)


inductive unrolldt_is_wf : deftype → subtype → Prop where
  | unrolldt_is_wf_0 (v_deftype : deftype) (ret_val : subtype) (var_0 : subtype) :
    fun_unrolldt v_deftype var_0 →
    ret_val = var_0 →
    wf_subtype ret_val →
    unrolldt_is_wf v_deftype ret_val


def free_addrtype (v_addrtype : addrtype) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_addrtype_is_wf : addrtype → free → Prop where
  | free_addrtype_is_wf_0 (v_addrtype : addrtype) (ret_val : free) :
    ret_val = (free_addrtype v_addrtype) →
    wf_free ret_val →
    free_addrtype_is_wf v_addrtype ret_val


def free_numtype (v_numtype : numtype) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_numtype_is_wf : numtype → free → Prop where
  | free_numtype_is_wf_0 (v_numtype : numtype) (ret_val : free) :
    ret_val = (free_numtype v_numtype) →
    wf_free ret_val →
    free_numtype_is_wf v_numtype ret_val


def free_packtype (v_packtype : packtype) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_packtype_is_wf : packtype → free → Prop where
  | free_packtype_is_wf_0 (v_packtype : packtype) (ret_val : free) :
    ret_val = (free_packtype v_packtype) →
    wf_free ret_val →
    free_packtype_is_wf v_packtype ret_val


def free_lanetype (v_lanetype : lanetype) : free :=
  match v_lanetype with
  | lanetype.I32 => free_numtype numtype.I32
  | lanetype.I64 => free_numtype numtype.I64
  | lanetype.F32 => free_numtype numtype.F32
  | lanetype.F64 => free_numtype numtype.F64
  | lanetype.I8 => free_packtype packtype.I8
  | lanetype.I16 => free_packtype packtype.I16

inductive free_lanetype_is_wf : lanetype → free → Prop where
  | free_lanetype_is_wf_0 (v_lanetype : lanetype) (ret_val : free) :
    ret_val = (free_lanetype v_lanetype) →
    wf_free ret_val →
    free_lanetype_is_wf v_lanetype ret_val


def free_vectype (v_vectype : vectype) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_vectype_is_wf : vectype → free → Prop where
  | free_vectype_is_wf_0 (v_vectype : vectype) (ret_val : free) :
    ret_val = (free_vectype v_vectype) →
    wf_free ret_val →
    free_vectype_is_wf v_vectype ret_val


def free_consttype (v_consttype : consttype) : free :=
  match v_consttype with
  | consttype.I32 => free_numtype numtype.I32
  | consttype.I64 => free_numtype numtype.I64
  | consttype.F32 => free_numtype numtype.F32
  | consttype.F64 => free_numtype numtype.F64
  | consttype.V128 => free_vectype vectype.V128

inductive free_consttype_is_wf : consttype → free → Prop where
  | free_consttype_is_wf_0 (v_consttype : consttype) (ret_val : free) :
    ret_val = (free_consttype v_consttype) →
    wf_free ret_val →
    free_consttype_is_wf v_consttype ret_val


def free_absheaptype (v_absheaptype : absheaptype) : free :=
  {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_absheaptype_is_wf : absheaptype → free → Prop where
  | free_absheaptype_is_wf_0 (v_absheaptype : absheaptype) (ret_val : free) :
    ret_val = (free_absheaptype v_absheaptype) →
    wf_free ret_val →
    free_absheaptype_is_wf v_absheaptype ret_val


def free_typevar (v_typevar : typevar) : free :=
  match v_typevar with
  | typevar._IDX v_typeidx => free_typeidx v_typeidx
  | typevar.REC v_n => {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_typevar_is_wf : typevar → free → Prop where
  | free_typevar_is_wf_0 (v_typevar : typevar) (ret_val : free) :
    wf_typevar v_typevar →
    ret_val = (free_typevar v_typevar) →
    wf_free ret_val →
    free_typevar_is_wf v_typevar ret_val


mutual
inductive fun_free_heaptype : heaptype → free → Prop where
  | fun_free_heaptype_case_0 : fun_free_heaptype heaptype.ANY (free_absheaptype absheaptype.ANY)
  | fun_free_heaptype_case_1 : fun_free_heaptype heaptype.EQ (free_absheaptype absheaptype.EQ)
  | fun_free_heaptype_case_2 : fun_free_heaptype heaptype.I31 (free_absheaptype absheaptype.I31)
  | fun_free_heaptype_case_3 : fun_free_heaptype heaptype.STRUCT (free_absheaptype absheaptype.STRUCT)
  | fun_free_heaptype_case_4 : fun_free_heaptype heaptype.ARRAY (free_absheaptype absheaptype.ARRAY)
  | fun_free_heaptype_case_5 : fun_free_heaptype heaptype.NONE (free_absheaptype absheaptype.NONE)
  | fun_free_heaptype_case_6 : fun_free_heaptype heaptype.FUNC (free_absheaptype absheaptype.FUNC)
  | fun_free_heaptype_case_7 : fun_free_heaptype heaptype.NOFUNC (free_absheaptype absheaptype.NOFUNC)
  | fun_free_heaptype_case_8 : fun_free_heaptype heaptype.EXN (free_absheaptype absheaptype.EXN)
  | fun_free_heaptype_case_9 : fun_free_heaptype heaptype.NOEXN (free_absheaptype absheaptype.NOEXN)
  | fun_free_heaptype_case_10 : fun_free_heaptype heaptype.EXTERN (free_absheaptype absheaptype.EXTERN)
  | fun_free_heaptype_case_11 : fun_free_heaptype heaptype.NOEXTERN (free_absheaptype absheaptype.NOEXTERN)
  | fun_free_heaptype_case_12 : fun_free_heaptype heaptype.BOT (free_absheaptype absheaptype.BOT)
  | fun_free_heaptype_case_13 (n_0 : n) (var_0 : free) :
    fun_free_typeuse (typeuse.REC n_0) var_0 →
    fun_free_heaptype (heaptype.REC n_0) var_0
  | fun_free_heaptype_case_14 (v_rectype : rectype) (v_n : n) (var_0 : free) :
    fun_free_typeuse (typeuse._DEF v_rectype v_n) var_0 →
    fun_free_heaptype (heaptype._DEF v_rectype v_n) var_0
  | fun_free_heaptype_case_15 (v_typeidx : typeidx) (var_0 : free) :
    fun_free_typeuse (typeuse._IDX v_typeidx) var_0 →
    fun_free_heaptype (heaptype._IDX v_typeidx) var_0

inductive fun_free_reftype : reftype → free → Prop where
  | fun_free_reftype_case_0 (null_opt : Option null) (v_heaptype : heaptype) (var_0 : free) :
    fun_free_heaptype v_heaptype var_0 →
    fun_free_reftype (reftype.REF null_opt v_heaptype) var_0

inductive fun_free_typeuse : typeuse → free → Prop where
  | fun_free_typeuse_case_0 (v_n : n) : fun_free_typeuse (typeuse.REC v_n) (free_typevar (typevar.REC v_n))
  | fun_free_typeuse_case_1 (v_typeidx : typeidx) : fun_free_typeuse (typeuse._IDX v_typeidx) (free_typevar (typevar._IDX v_typeidx))
  | fun_free_typeuse_case_2 (v_rectype : rectype) (v_n : n) (var_0 : free) :
    fun_free_deftype (deftype._DEF v_rectype v_n) var_0 →
    fun_free_typeuse (typeuse._DEF v_rectype v_n) var_0

inductive fun_free_valtype : valtype → free → Prop where
  | fun_free_valtype_case_0 : fun_free_valtype valtype.I32 (free_numtype numtype.I32)
  | fun_free_valtype_case_1 : fun_free_valtype valtype.I64 (free_numtype numtype.I64)
  | fun_free_valtype_case_2 : fun_free_valtype valtype.F32 (free_numtype numtype.F32)
  | fun_free_valtype_case_3 : fun_free_valtype valtype.F64 (free_numtype numtype.F64)
  | fun_free_valtype_case_4 : fun_free_valtype valtype.V128 (free_vectype vectype.V128)
  | fun_free_valtype_case_5 (null_opt : Option null) (v_heaptype : heaptype) (var_0 : free) :
    fun_free_reftype (reftype.REF null_opt v_heaptype) var_0 →
    fun_free_valtype (valtype.REF null_opt v_heaptype) var_0
  | fun_free_valtype_case_6 : fun_free_valtype valtype.BOT ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })

inductive fun_free_resulttype : resulttype → free → Prop where
  | fun_free_resulttype_case_0 (valtype_lst : List valtype) (var_1_lst : List free) (var_0 : free) :
    (List.length var_1_lst) = (List.length valtype_lst) →
    Forall₂ (fun var_1_elem v_valtype_elem => fun_free_valtype v_valtype_elem var_1_elem) var_1_lst valtype_lst →
    fun_free_list var_1_lst var_0 →
    fun_free_resulttype (.mk_list valtype_lst) var_0

inductive fun_free_storagetype : storagetype → free → Prop where
  | fun_free_storagetype_case_0 (var_0 : free) :
    fun_free_valtype valtype.BOT var_0 →
    fun_free_storagetype storagetype.BOT var_0
  | fun_free_storagetype_case_1 (null_opt : Option null) (v_heaptype : heaptype) (var_0 : free) :
    fun_free_valtype (valtype.REF null_opt v_heaptype) var_0 →
    fun_free_storagetype (storagetype.REF null_opt v_heaptype) var_0
  | fun_free_storagetype_case_2 (var_0 : free) :
    fun_free_valtype valtype.V128 var_0 →
    fun_free_storagetype storagetype.V128 var_0
  | fun_free_storagetype_case_3 (var_0 : free) :
    fun_free_valtype valtype.F64 var_0 →
    fun_free_storagetype storagetype.F64 var_0
  | fun_free_storagetype_case_4 (var_0 : free) :
    fun_free_valtype valtype.F32 var_0 →
    fun_free_storagetype storagetype.F32 var_0
  | fun_free_storagetype_case_5 (var_0 : free) :
    fun_free_valtype valtype.I64 var_0 →
    fun_free_storagetype storagetype.I64 var_0
  | fun_free_storagetype_case_6 (var_0 : free) :
    fun_free_valtype valtype.I32 var_0 →
    fun_free_storagetype storagetype.I32 var_0
  | fun_free_storagetype_case_7 : fun_free_storagetype storagetype.I8 (free_packtype packtype.I8)
  | fun_free_storagetype_case_8 : fun_free_storagetype storagetype.I16 (free_packtype packtype.I16)

inductive fun_free_fieldtype : fieldtype → free → Prop where
  | fun_free_fieldtype_case_0 (mut_opt : Option «mut») (v_storagetype : storagetype) (var_0 : free) :
    fun_free_storagetype v_storagetype var_0 →
    fun_free_fieldtype (fieldtype.mk_fieldtype mut_opt v_storagetype) var_0

inductive fun_free_comptype : comptype → free → Prop where
  | fun_free_comptype_case_0 (fieldtype_lst : List fieldtype) (var_1_lst : List free) (var_0 : free) :
    (List.length var_1_lst) = (List.length fieldtype_lst) →
    Forall₂ (fun var_1_elem v_fieldtype_elem => fun_free_fieldtype v_fieldtype_elem var_1_elem) var_1_lst fieldtype_lst →
    fun_free_list var_1_lst var_0 →
    fun_free_comptype (comptype.STRUCT (list.mk_list fieldtype_lst)) var_0
  | fun_free_comptype_case_1 (v_fieldtype : fieldtype) (var_0 : free) :
    fun_free_fieldtype v_fieldtype var_0 →
    fun_free_comptype (comptype.ARRAY v_fieldtype) var_0
  | fun_free_comptype_case_2 (resulttype_1 : list valtype) (resulttype_2 : list valtype) (var_1 : free) (var_0 : free) :
    fun_free_resulttype resulttype_2 var_1 →
    fun_free_resulttype resulttype_1 var_0 →
    fun_free_comptype (comptype.FUNC resulttype_1 resulttype_2) (var_0 ++ var_1)

inductive fun_free_subtype : subtype → free → Prop where
  | fun_free_subtype_case_0 (final_opt : Option final) (typeuse_lst : List typeuse) (v_comptype : comptype) (var_2 : free) (var_1_lst : List free) (var_0 : free) :
    fun_free_comptype v_comptype var_2 →
    (List.length var_1_lst) = (List.length typeuse_lst) →
    Forall₂ (fun var_1_elem v_typeuse_elem => fun_free_typeuse v_typeuse_elem var_1_elem) var_1_lst typeuse_lst →
    fun_free_list var_1_lst var_0 →
    fun_free_subtype (subtype.SUB final_opt typeuse_lst v_comptype) (var_0 ++ var_2)

inductive fun_free_rectype : rectype → free → Prop where
  | fun_free_rectype_case_0 (subtype_lst : List subtype) (var_1_lst : List free) (var_0 : free) :
    (List.length var_1_lst) = (List.length subtype_lst) →
    Forall₂ (fun var_1_elem v_subtype_elem => fun_free_subtype v_subtype_elem var_1_elem) var_1_lst subtype_lst →
    fun_free_list var_1_lst var_0 →
    fun_free_rectype (rectype.REC (list.mk_list subtype_lst)) var_0

inductive fun_free_deftype : deftype → free → Prop where
  | fun_free_deftype_case_0 (v_rectype : rectype) (v_n : Nat) (var_0 : free) :
    fun_free_rectype v_rectype var_0 →
    fun_free_deftype (deftype._DEF v_rectype v_n) var_0


end

mutual
inductive free_heaptype_is_wf : heaptype → free → Prop where
  | free_heaptype_is_wf_0 (v_heaptype : heaptype) (ret_val : free) (var_0 : free) :
    fun_free_heaptype v_heaptype var_0 →
    wf_heaptype v_heaptype →
    ret_val = var_0 →
    wf_free ret_val →
    free_heaptype_is_wf v_heaptype ret_val

inductive free_reftype_is_wf : reftype → free → Prop where
  | free_reftype_is_wf_0 (v_reftype : reftype) (ret_val : free) (var_0 : free) :
    fun_free_reftype v_reftype var_0 →
    wf_reftype v_reftype →
    ret_val = var_0 →
    wf_free ret_val →
    free_reftype_is_wf v_reftype ret_val

inductive free_typeuse_is_wf : typeuse → free → Prop where
  | free_typeuse_is_wf_0 (v_typeuse : typeuse) (ret_val : free) (var_0 : free) :
    fun_free_typeuse v_typeuse var_0 →
    wf_typeuse v_typeuse →
    ret_val = var_0 →
    wf_free ret_val →
    free_typeuse_is_wf v_typeuse ret_val

inductive free_valtype_is_wf : valtype → free → Prop where
  | free_valtype_is_wf_0 (v_valtype : valtype) (ret_val : free) (var_0 : free) :
    fun_free_valtype v_valtype var_0 →
    wf_valtype v_valtype →
    ret_val = var_0 →
    wf_free ret_val →
    free_valtype_is_wf v_valtype ret_val

inductive free_resulttype_is_wf : resulttype → free → Prop where
  | free_resulttype_is_wf_0 (v_resulttype : resulttype) (ret_val : free) (var_0 : free) :
    fun_free_resulttype v_resulttype var_0 →
    ret_val = var_0 →
    wf_free ret_val →
    free_resulttype_is_wf v_resulttype ret_val

inductive free_storagetype_is_wf : storagetype → free → Prop where
  | free_storagetype_is_wf_0 (v_storagetype : storagetype) (ret_val : free) (var_0 : free) :
    fun_free_storagetype v_storagetype var_0 →
    wf_storagetype v_storagetype →
    ret_val = var_0 →
    wf_free ret_val →
    free_storagetype_is_wf v_storagetype ret_val

inductive free_fieldtype_is_wf : fieldtype → free → Prop where
  | free_fieldtype_is_wf_0 (v_fieldtype : fieldtype) (ret_val : free) (var_0 : free) :
    fun_free_fieldtype v_fieldtype var_0 →
    wf_fieldtype v_fieldtype →
    ret_val = var_0 →
    wf_free ret_val →
    free_fieldtype_is_wf v_fieldtype ret_val

inductive free_comptype_is_wf : comptype → free → Prop where
  | free_comptype_is_wf_0 (v_comptype : comptype) (ret_val : free) (var_0 : free) :
    fun_free_comptype v_comptype var_0 →
    wf_comptype v_comptype →
    ret_val = var_0 →
    wf_free ret_val →
    free_comptype_is_wf v_comptype ret_val

inductive free_subtype_is_wf : subtype → free → Prop where
  | free_subtype_is_wf_0 (v_subtype : subtype) (ret_val : free) (var_0 : free) :
    fun_free_subtype v_subtype var_0 →
    wf_subtype v_subtype →
    ret_val = var_0 →
    wf_free ret_val →
    free_subtype_is_wf v_subtype ret_val

inductive free_rectype_is_wf : rectype → free → Prop where
  | free_rectype_is_wf_0 (v_rectype : rectype) (ret_val : free) (var_0 : free) :
    fun_free_rectype v_rectype var_0 →
    ret_val = var_0 →
    wf_free ret_val →
    free_rectype_is_wf v_rectype ret_val

inductive free_deftype_is_wf : deftype → free → Prop where
  | free_deftype_is_wf_0 (v_deftype : deftype) (ret_val : free) (var_0 : free) :
    fun_free_deftype v_deftype var_0 →
    ret_val = var_0 →
    wf_free ret_val →
    free_deftype_is_wf v_deftype ret_val


end

inductive fun_free_tagtype : tagtype → free → Prop where
  | fun_free_tagtype_case_0 (v_rectype : rectype) (v_n : n) (var_0 : free) :
    fun_free_deftype (deftype._DEF v_rectype v_n) var_0 →
    fun_free_tagtype (typeuse._DEF v_rectype v_n) var_0


inductive free_tagtype_is_wf : tagtype → free → Prop where
  | free_tagtype_is_wf_0 (v_tagtype : tagtype) (ret_val : free) (var_0 : free) :
    fun_free_tagtype v_tagtype var_0 →
    wf_typeuse v_tagtype →
    ret_val = var_0 →
    wf_free ret_val →
    free_tagtype_is_wf v_tagtype ret_val


inductive fun_free_globaltype : globaltype → free → Prop where
  | fun_free_globaltype_case_0 (mut_opt : Option «mut») (v_valtype : valtype) (var_0 : free) :
    fun_free_valtype v_valtype var_0 →
    fun_free_globaltype (globaltype.mk_globaltype mut_opt v_valtype) var_0


inductive free_globaltype_is_wf : globaltype → free → Prop where
  | free_globaltype_is_wf_0 (v_globaltype : globaltype) (ret_val : free) (var_0 : free) :
    fun_free_globaltype v_globaltype var_0 →
    wf_globaltype v_globaltype →
    ret_val = var_0 →
    wf_free ret_val →
    free_globaltype_is_wf v_globaltype ret_val


def free_memtype (v_memtype : memtype) : free :=
  match v_memtype with
  | memtype.PAGE v_addrtype v_limits => free_addrtype v_addrtype

inductive free_memtype_is_wf : memtype → free → Prop where
  | free_memtype_is_wf_0 (v_memtype : memtype) (ret_val : free) :
    wf_memtype v_memtype →
    ret_val = (free_memtype v_memtype) →
    wf_free ret_val →
    free_memtype_is_wf v_memtype ret_val


inductive fun_free_tabletype : tabletype → free → Prop where
  | fun_free_tabletype_case_0 (v_addrtype : addrtype) (v_limits : limits) (v_reftype : reftype) (var_0 : free) :
    fun_free_reftype v_reftype var_0 →
    fun_free_tabletype (tabletype.mk_tabletype v_addrtype v_limits v_reftype) ((free_addrtype v_addrtype) ++ var_0)


inductive free_tabletype_is_wf : tabletype → free → Prop where
  | free_tabletype_is_wf_0 (v_tabletype : tabletype) (ret_val : free) (var_0 : free) :
    fun_free_tabletype v_tabletype var_0 →
    wf_tabletype v_tabletype →
    ret_val = var_0 →
    wf_free ret_val →
    free_tabletype_is_wf v_tabletype ret_val


def free_datatype (v_datatype : datatype) : free :=
  match v_datatype with
  | datatype.OK => {
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  }

inductive free_datatype_is_wf : datatype → free → Prop where
  | free_datatype_is_wf_0 (v_datatype : datatype) (ret_val : free) :
    ret_val = (free_datatype v_datatype) →
    wf_free ret_val →
    free_datatype_is_wf v_datatype ret_val


inductive fun_free_elemtype : elemtype → free → Prop where
  | fun_free_elemtype_case_0 (v_reftype : reftype) (var_0 : free) :
    fun_free_reftype v_reftype var_0 →
    fun_free_elemtype v_reftype var_0


inductive free_elemtype_is_wf : elemtype → free → Prop where
  | free_elemtype_is_wf_0 (v_elemtype : elemtype) (ret_val : free) (var_0 : free) :
    fun_free_elemtype v_elemtype var_0 →
    wf_reftype v_elemtype →
    ret_val = var_0 →
    wf_free ret_val →
    free_elemtype_is_wf v_elemtype ret_val


inductive fun_free_externtype : externtype → free → Prop where
  | fun_free_externtype_case_0 (v_tagtype : typeuse) (var_0 : free) :
    fun_free_tagtype v_tagtype var_0 →
    fun_free_externtype (externtype.TAG v_tagtype) var_0
  | fun_free_externtype_case_1 (v_globaltype : globaltype) (var_0 : free) :
    fun_free_globaltype v_globaltype var_0 →
    fun_free_externtype (externtype.GLOBAL v_globaltype) var_0
  | fun_free_externtype_case_2 (v_memtype : memtype) : fun_free_externtype (externtype.MEM v_memtype) (free_memtype v_memtype)
  | fun_free_externtype_case_3 (v_tabletype : tabletype) (var_0 : free) :
    fun_free_tabletype v_tabletype var_0 →
    fun_free_externtype (externtype.TABLE v_tabletype) var_0
  | fun_free_externtype_case_4 (v_typeuse : typeuse) (var_0 : free) :
    fun_free_typeuse v_typeuse var_0 →
    fun_free_externtype (externtype.FUNC v_typeuse) var_0


inductive free_externtype_is_wf : externtype → free → Prop where
  | free_externtype_is_wf_0 (v_externtype : externtype) (ret_val : free) (var_0 : free) :
    fun_free_externtype v_externtype var_0 →
    wf_externtype v_externtype →
    ret_val = var_0 →
    wf_free ret_val →
    free_externtype_is_wf v_externtype ret_val


inductive fun_free_moduletype : moduletype → free → Prop where
  | fun_free_moduletype_case_0 (externtype_1_lst : List externtype) (externtype_2_lst : List externtype) (var_3_lst : List free) (var_2 : free) (var_1_lst : List free) (var_0 : free) :
    (List.length var_3_lst) = (List.length externtype_2_lst) →
    Forall₂ (fun var_3_elem externtype_2_elem => fun_free_externtype externtype_2_elem var_3_elem) var_3_lst externtype_2_lst →
    fun_free_list var_3_lst var_2 →
    (List.length var_1_lst) = (List.length externtype_1_lst) →
    Forall₂ (fun var_1_elem externtype_1_elem => fun_free_externtype externtype_1_elem var_1_elem) var_1_lst externtype_1_lst →
    fun_free_list var_1_lst var_0 →
    fun_free_moduletype (moduletype.mk_moduletype externtype_1_lst externtype_2_lst) (var_0 ++ var_2)


inductive free_moduletype_is_wf : moduletype → free → Prop where
  | free_moduletype_is_wf_0 (v_moduletype : moduletype) (ret_val : free) (var_0 : free) :
    fun_free_moduletype v_moduletype var_0 →
    wf_moduletype v_moduletype →
    ret_val = var_0 →
    wf_free ret_val →
    free_moduletype_is_wf v_moduletype ret_val


inductive num_ : Type where
  | mk_num__0 (v_Inn : Inn) (var_x : iN) : num_
  | mk_num__1 (v_Fnn : Fnn) (var_x : fN) : num_
deriving Inhabited, BEq

inductive wf_num_ : numtype → num_ → Prop where
  | num__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : iN) :
    wf_uN (size (numtype_addrtype v_Inn)) var_x →
    v_numtype = (numtype_addrtype v_Inn) →
    wf_num_ v_numtype (num_.mk_num__0 v_Inn var_x)
  | num__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : fN) :
    wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x →
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_num_ v_numtype (num_.mk_num__1 v_Fnn var_x)


def proj_num__0 (var_x : num_) : Option iN :=
  match var_x with
  | num_.mk_num__0 v_Inn var_x => some var_x
  | _ => none

def proj_num__1 (var_x : num_) : Option fN :=
  match var_x with
  | num_.mk_num__1 v_Fnn var_x => some var_x
  | _ => none

abbrev pack_ : Type := iN

inductive lane_ : Type where
  | mk_lane__0 (v_numtype : numtype) (var_x : num_) : lane_
  | mk_lane__1 (v_packtype : packtype) (var_x : pack_) : lane_
  | mk_lane__2 (v_Jnn : Jnn) (var_x : iN) : lane_
deriving Inhabited, BEq

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


def proj_lane__0 (var_x : lane_) : Option num_ :=
  match var_x with
  | lane_.mk_lane__0 v_numtype var_x => some var_x
  | _ => none

def proj_lane__1 (var_x : lane_) : Option pack_ :=
  match var_x with
  | lane_.mk_lane__1 v_packtype var_x => some var_x
  | _ => none

def proj_lane__2 (var_x : lane_) : Option iN :=
  match var_x with
  | lane_.mk_lane__2 v_Jnn var_x => some var_x
  | _ => none

abbrev vec_ : Type := vN

inductive lit_ : Type where
  | mk_lit__0 (v_numtype : numtype) (var_x : num_) : lit_
  | mk_lit__1 (v_vectype : vectype) (var_x : vec_) : lit_
  | mk_lit__2 (v_packtype : packtype) (var_x : pack_) : lit_
deriving Inhabited, BEq

inductive wf_lit_ : storagetype → lit_ → Prop where
  | lit__case_0 (v_storagetype : storagetype) (v_numtype : numtype) (var_x : num_) :
    wf_num_ v_numtype var_x →
    v_storagetype = (storagetype_numtype v_numtype) →
    wf_lit_ v_storagetype (lit_.mk_lit__0 v_numtype var_x)
  | lit__case_1 (v_storagetype : storagetype) (v_vectype : vectype) (var_x : vec_) :
    wf_uN (vsize v_vectype) var_x →
    v_storagetype = (storagetype_vectype v_vectype) →
    wf_lit_ v_storagetype (lit_.mk_lit__1 v_vectype var_x)
  | lit__case_2 (v_storagetype : storagetype) (v_packtype : packtype) (var_x : pack_) :
    wf_uN (psize v_packtype) var_x →
    v_storagetype = (storagetype_packtype v_packtype) →
    wf_lit_ v_storagetype (lit_.mk_lit__2 v_packtype var_x)


def proj_lit__0 (var_x : lit_) : Option num_ :=
  match var_x with
  | lit_.mk_lit__0 v_numtype var_x => some var_x
  | _ => none

def proj_lit__1 (var_x : lit_) : Option vec_ :=
  match var_x with
  | lit_.mk_lit__1 v_vectype var_x => some var_x
  | _ => none

def proj_lit__2 (var_x : lit_) : Option pack_ :=
  match var_x with
  | lit_.mk_lit__2 v_packtype var_x => some var_x
  | _ => none

inductive sz : Type where
  | mk_sz (i : Nat) : sz
deriving Inhabited, BEq

def proj_sz_0 (x : sz) : Nat :=
  match x with
  | sz.mk_sz v_num_0 => (v_num_0)

inductive wf_sz : sz → Prop where
  | sz_case_0 (i : Nat) :
    (((i = 8) ∨ (i = 16)) ∨ (i = 32)) ∨ (i = 64) →
    wf_sz (sz.mk_sz i)


inductive sx : Type where
  | U : sx
  | S : sx
deriving Inhabited, BEq

inductive unop_Inn : Type where
  | CLZ : unop_Inn
  | CTZ : unop_Inn
  | POPCNT : unop_Inn
  | EXTEND (v_sz : sz) : unop_Inn
deriving Inhabited, BEq

inductive wf_unop_Inn : Inn → unop_Inn → Prop where
  | unop_Inn_case_0 (v_Inn : Inn) : wf_unop_Inn v_Inn unop_Inn.CLZ
  | unop_Inn_case_1 (v_Inn : Inn) : wf_unop_Inn v_Inn unop_Inn.CTZ
  | unop_Inn_case_2 (v_Inn : Inn) : wf_unop_Inn v_Inn unop_Inn.POPCNT
  | unop_Inn_case_3 (v_Inn : Inn) (v_sz : sz) :
    wf_sz v_sz →
    (proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn)) →
    wf_unop_Inn v_Inn (unop_Inn.EXTEND v_sz)


inductive unop_Fnn : Type where
  | ABS : unop_Fnn
  | NEG : unop_Fnn
  | SQRT : unop_Fnn
  | CEIL : unop_Fnn
  | FLOOR : unop_Fnn
  | TRUNC : unop_Fnn
  | NEAREST : unop_Fnn
deriving Inhabited, BEq

inductive unop_ : Type where
  | mk_unop__0 (v_Inn : Inn) (var_x : unop_Inn) : unop_
  | mk_unop__1 (v_Fnn : Fnn) (var_x : unop_Fnn) : unop_
deriving Inhabited, BEq

inductive wf_unop_ : numtype → unop_ → Prop where
  | unop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : unop_Inn) :
    wf_unop_Inn v_Inn var_x →
    v_numtype = (numtype_addrtype v_Inn) →
    wf_unop_ v_numtype (unop_.mk_unop__0 v_Inn var_x)
  | unop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : unop_Fnn) :
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_unop_ v_numtype (unop_.mk_unop__1 v_Fnn var_x)


def proj_unop__0 (var_x : unop_) : Option unop_Inn :=
  match var_x with
  | unop_.mk_unop__0 v_Inn var_x => some var_x
  | _ => none

def proj_unop__1 (var_x : unop_) : Option unop_Fnn :=
  match var_x with
  | unop_.mk_unop__1 v_Fnn var_x => some var_x
  | _ => none

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

inductive binop_Fnn : Type where
  | ADD : binop_Fnn
  | SUB : binop_Fnn
  | MUL : binop_Fnn
  | DIV : binop_Fnn
  | MIN : binop_Fnn
  | MAX : binop_Fnn
  | COPYSIGN : binop_Fnn
deriving Inhabited, BEq

inductive binop_ : Type where
  | mk_binop__0 (v_Inn : Inn) (var_x : binop_Inn) : binop_
  | mk_binop__1 (v_Fnn : Fnn) (var_x : binop_Fnn) : binop_
deriving Inhabited, BEq

inductive wf_binop_ : numtype → binop_ → Prop where
  | binop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : binop_Inn) :
    v_numtype = (numtype_addrtype v_Inn) →
    wf_binop_ v_numtype (binop_.mk_binop__0 v_Inn var_x)
  | binop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : binop_Fnn) :
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_binop_ v_numtype (binop_.mk_binop__1 v_Fnn var_x)


def proj_binop__0 (var_x : binop_) : Option binop_Inn :=
  match var_x with
  | binop_.mk_binop__0 v_Inn var_x => some var_x
  | _ => none

def proj_binop__1 (var_x : binop_) : Option binop_Fnn :=
  match var_x with
  | binop_.mk_binop__1 v_Fnn var_x => some var_x
  | _ => none

inductive testop_Inn : Type where
  | EQZ : testop_Inn
deriving Inhabited, BEq

inductive testop_ : Type where
  | mk_testop__0 (v_Inn : Inn) (var_x : testop_Inn) : testop_
deriving Inhabited, BEq

inductive wf_testop_ : numtype → testop_ → Prop where
  | testop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : testop_Inn) :
    v_numtype = (numtype_addrtype v_Inn) →
    wf_testop_ v_numtype (testop_.mk_testop__0 v_Inn var_x)


def proj_testop__0 (var_x : testop_) : testop_Inn :=
  match var_x with
  | testop_.mk_testop__0 v_Inn var_x => var_x

inductive relop_Inn : Type where
  | EQ : relop_Inn
  | NE : relop_Inn
  | LT (v_sx : sx) : relop_Inn
  | GT (v_sx : sx) : relop_Inn
  | LE (v_sx : sx) : relop_Inn
  | GE (v_sx : sx) : relop_Inn
deriving Inhabited, BEq

inductive relop_Fnn : Type where
  | EQ : relop_Fnn
  | NE : relop_Fnn
  | LT : relop_Fnn
  | GT : relop_Fnn
  | LE : relop_Fnn
  | GE : relop_Fnn
deriving Inhabited, BEq

inductive relop_ : Type where
  | mk_relop__0 (v_Inn : Inn) (var_x : relop_Inn) : relop_
  | mk_relop__1 (v_Fnn : Fnn) (var_x : relop_Fnn) : relop_
deriving Inhabited, BEq

inductive wf_relop_ : numtype → relop_ → Prop where
  | relop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : relop_Inn) :
    v_numtype = (numtype_addrtype v_Inn) →
    wf_relop_ v_numtype (relop_.mk_relop__0 v_Inn var_x)
  | relop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : relop_Fnn) :
    v_numtype = (numtype_Fnn v_Fnn) →
    wf_relop_ v_numtype (relop_.mk_relop__1 v_Fnn var_x)


def proj_relop__0 (var_x : relop_) : Option relop_Inn :=
  match var_x with
  | relop_.mk_relop__0 v_Inn var_x => some var_x
  | _ => none

def proj_relop__1 (var_x : relop_) : Option relop_Fnn :=
  match var_x with
  | relop_.mk_relop__1 v_Fnn var_x => some var_x
  | _ => none

inductive cvtop__Inn_1_Inn_2 : Type where
  | EXTEND (v_sx : sx) : cvtop__Inn_1_Inn_2
  | WRAP : cvtop__Inn_1_Inn_2
deriving Inhabited, BEq

inductive wf_cvtop__Inn_1_Inn_2 : Inn → Inn → cvtop__Inn_1_Inn_2 → Prop where
  | cvtop__Inn_1_Inn_2_case_0 (Inn_1 : Inn) (Inn_2 : Inn) (v_sx : sx) :
    (sizenn1 (numtype_addrtype Inn_1)) < (sizenn2 (numtype_addrtype Inn_2)) →
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 (cvtop__Inn_1_Inn_2.EXTEND v_sx)
  | cvtop__Inn_1_Inn_2_case_1 (Inn_1 : Inn) (Inn_2 : Inn) :
    (sizenn1 (numtype_addrtype Inn_1)) > (sizenn2 (numtype_addrtype Inn_2)) →
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 cvtop__Inn_1_Inn_2.WRAP


inductive cvtop__Inn_1_Fnn_2 : Type where
  | CONVERT (v_sx : sx) : cvtop__Inn_1_Fnn_2
  | REINTERPRET : cvtop__Inn_1_Fnn_2
deriving Inhabited, BEq

inductive wf_cvtop__Inn_1_Fnn_2 : Inn → Fnn → cvtop__Inn_1_Fnn_2 → Prop where
  | cvtop__Inn_1_Fnn_2_case_0 (Inn_1 : Inn) (Fnn_2 : Fnn) (v_sx : sx) : wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)
  | cvtop__Inn_1_Fnn_2_case_1 (Inn_1 : Inn) (Fnn_2 : Fnn) :
    (sizenn1 (numtype_addrtype Inn_1)) = (sizenn2 (numtype_Fnn Fnn_2)) →
    wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 cvtop__Inn_1_Fnn_2.REINTERPRET


inductive cvtop__Fnn_1_Inn_2 : Type where
  | TRUNC (v_sx : sx) : cvtop__Fnn_1_Inn_2
  | TRUNC_SAT (v_sx : sx) : cvtop__Fnn_1_Inn_2
  | REINTERPRET : cvtop__Fnn_1_Inn_2
deriving Inhabited, BEq

inductive wf_cvtop__Fnn_1_Inn_2 : Fnn → Inn → cvtop__Fnn_1_Inn_2 → Prop where
  | cvtop__Fnn_1_Inn_2_case_0 (Fnn_1 : Fnn) (Inn_2 : Inn) (v_sx : sx) : wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)
  | cvtop__Fnn_1_Inn_2_case_1 (Fnn_1 : Fnn) (Inn_2 : Inn) (v_sx : sx) : wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)
  | cvtop__Fnn_1_Inn_2_case_2 (Fnn_1 : Fnn) (Inn_2 : Inn) :
    (sizenn1 (numtype_Fnn Fnn_1)) = (sizenn2 (numtype_addrtype Inn_2)) →
    wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 cvtop__Fnn_1_Inn_2.REINTERPRET


inductive cvtop__Fnn_1_Fnn_2 : Type where
  | PROMOTE : cvtop__Fnn_1_Fnn_2
  | DEMOTE : cvtop__Fnn_1_Fnn_2
deriving Inhabited, BEq

inductive wf_cvtop__Fnn_1_Fnn_2 : Fnn → Fnn → cvtop__Fnn_1_Fnn_2 → Prop where
  | cvtop__Fnn_1_Fnn_2_case_0 (Fnn_1 : Fnn) (Fnn_2 : Fnn) :
    (sizenn1 (numtype_Fnn Fnn_1)) < (sizenn2 (numtype_Fnn Fnn_2)) →
    wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 cvtop__Fnn_1_Fnn_2.PROMOTE
  | cvtop__Fnn_1_Fnn_2_case_1 (Fnn_1 : Fnn) (Fnn_2 : Fnn) :
    (sizenn1 (numtype_Fnn Fnn_1)) > (sizenn2 (numtype_Fnn Fnn_2)) →
    wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 cvtop__Fnn_1_Fnn_2.DEMOTE


inductive cvtop__ : Type where
  | mk_cvtop___0 (Inn_1 : Inn) (Inn_2 : Inn) (var_x : cvtop__Inn_1_Inn_2) : cvtop__
  | mk_cvtop___1 (Inn_1 : Inn) (Fnn_2 : Fnn) (var_x : cvtop__Inn_1_Fnn_2) : cvtop__
  | mk_cvtop___2 (Fnn_1 : Fnn) (Inn_2 : Inn) (var_x : cvtop__Fnn_1_Inn_2) : cvtop__
  | mk_cvtop___3 (Fnn_1 : Fnn) (Fnn_2 : Fnn) (var_x : cvtop__Fnn_1_Fnn_2) : cvtop__
deriving Inhabited, BEq

inductive wf_cvtop__ : numtype → numtype → cvtop__ → Prop where
  | cvtop___case_0 (numtype_1 : numtype) (numtype_2 : numtype) (Inn_1 : Inn) (Inn_2 : Inn) (var_x : cvtop__Inn_1_Inn_2) :
    wf_cvtop__Inn_1_Inn_2 Inn_1 Inn_2 var_x →
    numtype_1 = (numtype_addrtype Inn_1) →
    numtype_2 = (numtype_addrtype Inn_2) →
    wf_cvtop__ numtype_1 numtype_2 (cvtop__.mk_cvtop___0 Inn_1 Inn_2 var_x)
  | cvtop___case_1 (numtype_1 : numtype) (numtype_2 : numtype) (Inn_1 : Inn) (Fnn_2 : Fnn) (var_x : cvtop__Inn_1_Fnn_2) :
    wf_cvtop__Inn_1_Fnn_2 Inn_1 Fnn_2 var_x →
    numtype_1 = (numtype_addrtype Inn_1) →
    numtype_2 = (numtype_Fnn Fnn_2) →
    wf_cvtop__ numtype_1 numtype_2 (cvtop__.mk_cvtop___1 Inn_1 Fnn_2 var_x)
  | cvtop___case_2 (numtype_1 : numtype) (numtype_2 : numtype) (Fnn_1 : Fnn) (Inn_2 : Inn) (var_x : cvtop__Fnn_1_Inn_2) :
    wf_cvtop__Fnn_1_Inn_2 Fnn_1 Inn_2 var_x →
    numtype_1 = (numtype_Fnn Fnn_1) →
    numtype_2 = (numtype_addrtype Inn_2) →
    wf_cvtop__ numtype_1 numtype_2 (cvtop__.mk_cvtop___2 Fnn_1 Inn_2 var_x)
  | cvtop___case_3 (numtype_1 : numtype) (numtype_2 : numtype) (Fnn_1 : Fnn) (Fnn_2 : Fnn) (var_x : cvtop__Fnn_1_Fnn_2) :
    wf_cvtop__Fnn_1_Fnn_2 Fnn_1 Fnn_2 var_x →
    numtype_1 = (numtype_Fnn Fnn_1) →
    numtype_2 = (numtype_Fnn Fnn_2) →
    wf_cvtop__ numtype_1 numtype_2 (cvtop__.mk_cvtop___3 Fnn_1 Fnn_2 var_x)


def proj_cvtop___0 (var_x : cvtop__) : Option cvtop__Inn_1_Inn_2 :=
  match var_x with
  | cvtop__.mk_cvtop___0 Inn_1 Inn_2 var_x => some var_x
  | _ => none

def proj_cvtop___1 (var_x : cvtop__) : Option cvtop__Inn_1_Fnn_2 :=
  match var_x with
  | cvtop__.mk_cvtop___1 Inn_1 Fnn_2 var_x => some var_x
  | _ => none

def proj_cvtop___2 (var_x : cvtop__) : Option cvtop__Fnn_1_Inn_2 :=
  match var_x with
  | cvtop__.mk_cvtop___2 Fnn_1 Inn_2 var_x => some var_x
  | _ => none

def proj_cvtop___3 (var_x : cvtop__) : Option cvtop__Fnn_1_Fnn_2 :=
  match var_x with
  | cvtop__.mk_cvtop___3 Fnn_1 Fnn_2 var_x => some var_x
  | _ => none

inductive dim : Type where
  | mk_dim (i : Nat) : dim
deriving Inhabited, BEq

def proj_dim_0 (x : dim) : Nat :=
  match x with
  | dim.mk_dim v_num_0 => (v_num_0)

inductive wf_dim : dim → Prop where
  | dim_case_0 (i : Nat) :
    ((((i = 1) ∨ (i = 2)) ∨ (i = 4)) ∨ (i = 8)) ∨ (i = 16) →
    wf_dim (dim.mk_dim i)


inductive shape : Type where
  | X (v_lanetype : lanetype) (v_dim : dim) : shape
deriving Inhabited, BEq

inductive wf_shape : shape → Prop where
  | shape_case_0 (v_lanetype : lanetype) (v_dim : dim) :
    wf_dim v_dim →
    ((lsize v_lanetype) * (proj_dim_0 v_dim)) = 128 →
    wf_shape (shape.X v_lanetype v_dim)


def fun_dim (v_shape : shape) : dim :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => dim.mk_dim v_N

inductive dim_is_wf : shape → dim → Prop where
  | dim_is_wf_0 (v_shape : shape) (ret_val : dim) :
    wf_shape v_shape →
    ret_val = (fun_dim v_shape) →
    wf_dim ret_val →
    dim_is_wf v_shape ret_val


def fun_lanetype (v_shape : shape) : lanetype :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => v_Lnn

def unpackshape (v_shape : shape) : numtype :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => lunpack v_Lnn

inductive ishape : Type where
  | mk_ishape (v_shape : shape) : ishape
deriving Inhabited, BEq

def proj_ishape_0 (x : ishape) : shape :=
  match x with
  | ishape.mk_ishape v_shape_0 => (v_shape_0)

inductive wf_ishape : ishape → Prop where
  | ishape_case_0 (v_Jnn : Jnn) (v_shape : shape) :
    wf_shape v_shape →
    (fun_lanetype v_shape) = (lanetype_Jnn v_Jnn) →
    wf_ishape (ishape.mk_ishape v_shape)


inductive bshape : Type where
  | mk_bshape (v_shape : shape) : bshape
deriving Inhabited, BEq

def proj_bshape_0 (x : bshape) : shape :=
  match x with
  | bshape.mk_bshape v_shape_0 => (v_shape_0)

inductive wf_bshape : bshape → Prop where
  | bshape_case_0 (v_shape : shape) :
    wf_shape v_shape →
    (fun_lanetype v_shape) = lanetype.I8 →
    wf_bshape (bshape.mk_bshape v_shape)


inductive zero : Type where
  | ZERO : zero
deriving Inhabited, BEq

inductive half : Type where
  | LOW : half
  | HIGH : half
deriving Inhabited, BEq

inductive vvunop : Type where
  | NOT : vvunop
deriving Inhabited, BEq

inductive vvbinop : Type where
  | AND : vvbinop
  | ANDNOT : vvbinop
  | OR : vvbinop
  | XOR : vvbinop
deriving Inhabited, BEq

inductive vvternop : Type where
  | BITSELECT : vvternop
deriving Inhabited, BEq

inductive vvtestop : Type where
  | ANY_TRUE : vvtestop
deriving Inhabited, BEq

inductive vunop_Jnn_M : Type where
  | ABS : vunop_Jnn_M
  | NEG : vunop_Jnn_M
  | POPCNT : vunop_Jnn_M
deriving Inhabited, BEq

inductive wf_vunop_Jnn_M : Jnn → M → vunop_Jnn_M → Prop where
  | vunop_Jnn_M_case_0 (v_Jnn : Jnn) (v_M : M) : wf_vunop_Jnn_M v_Jnn v_M vunop_Jnn_M.ABS
  | vunop_Jnn_M_case_1 (v_Jnn : Jnn) (v_M : M) : wf_vunop_Jnn_M v_Jnn v_M vunop_Jnn_M.NEG
  | vunop_Jnn_M_case_2 (v_Jnn : Jnn) (v_M : M) :
    (lsizenn (lanetype_Jnn v_Jnn)) = 8 →
    wf_vunop_Jnn_M v_Jnn v_M vunop_Jnn_M.POPCNT


inductive vunop_Fnn_M : Type where
  | ABS : vunop_Fnn_M
  | NEG : vunop_Fnn_M
  | SQRT : vunop_Fnn_M
  | CEIL : vunop_Fnn_M
  | FLOOR : vunop_Fnn_M
  | TRUNC : vunop_Fnn_M
  | NEAREST : vunop_Fnn_M
deriving Inhabited, BEq

inductive vunop_ : Type where
  | mk_vunop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vunop_Jnn_M) : vunop_
  | mk_vunop__1 (v_Fnn : Fnn) (v_M : M) (var_x : vunop_Fnn_M) : vunop_
deriving Inhabited, BEq

inductive wf_vunop_ : shape → vunop_ → Prop where
  | vunop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vunop_Jnn_M) :
    wf_vunop_Jnn_M v_Jnn v_M var_x →
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_vunop_ v_shape (vunop_.mk_vunop__0 v_Jnn v_M var_x)
  | vunop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_M : M) (var_x : vunop_Fnn_M) :
    v_shape = (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_M)) →
    wf_vunop_ v_shape (vunop_.mk_vunop__1 v_Fnn v_M var_x)


def proj_vunop__0 (var_x : vunop_) : Option vunop_Jnn_M :=
  match var_x with
  | vunop_.mk_vunop__0 v_Jnn v_M var_x => some var_x
  | _ => none

def proj_vunop__1 (var_x : vunop_) : Option vunop_Fnn_M :=
  match var_x with
  | vunop_.mk_vunop__1 v_Fnn v_M var_x => some var_x
  | _ => none

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

inductive wf_vbinop_Jnn_M : Jnn → M → vbinop_Jnn_M → Prop where
  | vbinop_Jnn_M_case_0 (v_Jnn : Jnn) (v_M : M) : wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M.ADD
  | vbinop_Jnn_M_case_1 (v_Jnn : Jnn) (v_M : M) : wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M.SUB
  | vbinop_Jnn_M_case_2 (v_Jnn : Jnn) (v_M : M) (v_sx : sx) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_M v_Jnn v_M (vbinop_Jnn_M.ADD_SAT v_sx)
  | vbinop_Jnn_M_case_3 (v_Jnn : Jnn) (v_M : M) (v_sx : sx) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_M v_Jnn v_M (vbinop_Jnn_M.SUB_SAT v_sx)
  | vbinop_Jnn_M_case_4 (v_Jnn : Jnn) (v_M : M) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≥ 16 →
    wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M.MUL
  | vbinop_Jnn_M_case_5 (v_Jnn : Jnn) (v_M : M) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M.AVGRU
  | vbinop_Jnn_M_case_6 (v_Jnn : Jnn) (v_M : M) :
    (lsizenn (lanetype_Jnn v_Jnn)) = 16 →
    wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M.Q15MULR_SATS
  | vbinop_Jnn_M_case_7 (v_Jnn : Jnn) (v_M : M) :
    (lsizenn (lanetype_Jnn v_Jnn)) = 16 →
    wf_vbinop_Jnn_M v_Jnn v_M vbinop_Jnn_M.RELAXED_Q15MULRS
  | vbinop_Jnn_M_case_8 (v_Jnn : Jnn) (v_M : M) (v_sx : sx) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 32 →
    wf_vbinop_Jnn_M v_Jnn v_M (vbinop_Jnn_M.MIN v_sx)
  | vbinop_Jnn_M_case_9 (v_Jnn : Jnn) (v_M : M) (v_sx : sx) :
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 32 →
    wf_vbinop_Jnn_M v_Jnn v_M (vbinop_Jnn_M.MAX v_sx)


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

inductive vbinop_ : Type where
  | mk_vbinop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vbinop_Jnn_M) : vbinop_
  | mk_vbinop__1 (v_Fnn : Fnn) (v_M : M) (var_x : vbinop_Fnn_M) : vbinop_
deriving Inhabited, BEq

inductive wf_vbinop_ : shape → vbinop_ → Prop where
  | vbinop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vbinop_Jnn_M) :
    wf_vbinop_Jnn_M v_Jnn v_M var_x →
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_vbinop_ v_shape (vbinop_.mk_vbinop__0 v_Jnn v_M var_x)
  | vbinop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_M : M) (var_x : vbinop_Fnn_M) :
    v_shape = (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_M)) →
    wf_vbinop_ v_shape (vbinop_.mk_vbinop__1 v_Fnn v_M var_x)


def proj_vbinop__0 (var_x : vbinop_) : Option vbinop_Jnn_M :=
  match var_x with
  | vbinop_.mk_vbinop__0 v_Jnn v_M var_x => some var_x
  | _ => none

def proj_vbinop__1 (var_x : vbinop_) : Option vbinop_Fnn_M :=
  match var_x with
  | vbinop_.mk_vbinop__1 v_Fnn v_M var_x => some var_x
  | _ => none

inductive vternop_Jnn_M : Type where
  | RELAXED_LANESELECT : vternop_Jnn_M
deriving Inhabited, BEq

inductive vternop_Fnn_M : Type where
  | RELAXED_MADD : vternop_Fnn_M
  | RELAXED_NMADD : vternop_Fnn_M
deriving Inhabited, BEq

inductive vternop_ : Type where
  | mk_vternop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vternop_Jnn_M) : vternop_
  | mk_vternop__1 (v_Fnn : Fnn) (v_M : M) (var_x : vternop_Fnn_M) : vternop_
deriving Inhabited, BEq

inductive wf_vternop_ : shape → vternop_ → Prop where
  | vternop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vternop_Jnn_M) :
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_vternop_ v_shape (vternop_.mk_vternop__0 v_Jnn v_M var_x)
  | vternop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_M : M) (var_x : vternop_Fnn_M) :
    v_shape = (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_M)) →
    wf_vternop_ v_shape (vternop_.mk_vternop__1 v_Fnn v_M var_x)


def proj_vternop__0 (var_x : vternop_) : Option vternop_Jnn_M :=
  match var_x with
  | vternop_.mk_vternop__0 v_Jnn v_M var_x => some var_x
  | _ => none

def proj_vternop__1 (var_x : vternop_) : Option vternop_Fnn_M :=
  match var_x with
  | vternop_.mk_vternop__1 v_Fnn v_M var_x => some var_x
  | _ => none

inductive vtestop_Jnn_M : Type where
  | ALL_TRUE : vtestop_Jnn_M
deriving Inhabited, BEq

inductive vtestop_ : Type where
  | mk_vtestop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vtestop_Jnn_M) : vtestop_
deriving Inhabited, BEq

inductive wf_vtestop_ : shape → vtestop_ → Prop where
  | vtestop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vtestop_Jnn_M) :
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_vtestop_ v_shape (vtestop_.mk_vtestop__0 v_Jnn v_M var_x)


def proj_vtestop__0 (var_x : vtestop_) : vtestop_Jnn_M :=
  match var_x with
  | vtestop_.mk_vtestop__0 v_Jnn v_M var_x => var_x

inductive vrelop_Jnn_M : Type where
  | EQ : vrelop_Jnn_M
  | NE : vrelop_Jnn_M
  | LT (v_sx : sx) : vrelop_Jnn_M
  | GT (v_sx : sx) : vrelop_Jnn_M
  | LE (v_sx : sx) : vrelop_Jnn_M
  | GE (v_sx : sx) : vrelop_Jnn_M
deriving Inhabited, BEq

inductive wf_vrelop_Jnn_M : Jnn → M → vrelop_Jnn_M → Prop where
  | vrelop_Jnn_M_case_0 (v_Jnn : Jnn) (v_M : M) : wf_vrelop_Jnn_M v_Jnn v_M vrelop_Jnn_M.EQ
  | vrelop_Jnn_M_case_1 (v_Jnn : Jnn) (v_M : M) : wf_vrelop_Jnn_M v_Jnn v_M vrelop_Jnn_M.NE
  | vrelop_Jnn_M_case_2 (v_Jnn : Jnn) (v_M : M) (v_sx : sx) :
    ((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = sx.S) →
    wf_vrelop_Jnn_M v_Jnn v_M (vrelop_Jnn_M.LT v_sx)
  | vrelop_Jnn_M_case_3 (v_Jnn : Jnn) (v_M : M) (v_sx : sx) :
    ((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = sx.S) →
    wf_vrelop_Jnn_M v_Jnn v_M (vrelop_Jnn_M.GT v_sx)
  | vrelop_Jnn_M_case_4 (v_Jnn : Jnn) (v_M : M) (v_sx : sx) :
    ((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = sx.S) →
    wf_vrelop_Jnn_M v_Jnn v_M (vrelop_Jnn_M.LE v_sx)
  | vrelop_Jnn_M_case_5 (v_Jnn : Jnn) (v_M : M) (v_sx : sx) :
    ((lsizenn (lanetype_Jnn v_Jnn)) ≠ 64) ∨ (v_sx = sx.S) →
    wf_vrelop_Jnn_M v_Jnn v_M (vrelop_Jnn_M.GE v_sx)


inductive vrelop_Fnn_M : Type where
  | EQ : vrelop_Fnn_M
  | NE : vrelop_Fnn_M
  | LT : vrelop_Fnn_M
  | GT : vrelop_Fnn_M
  | LE : vrelop_Fnn_M
  | GE : vrelop_Fnn_M
deriving Inhabited, BEq

inductive vrelop_ : Type where
  | mk_vrelop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vrelop_Jnn_M) : vrelop_
  | mk_vrelop__1 (v_Fnn : Fnn) (v_M : M) (var_x : vrelop_Fnn_M) : vrelop_
deriving Inhabited, BEq

inductive wf_vrelop_ : shape → vrelop_ → Prop where
  | vrelop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_M : M) (var_x : vrelop_Jnn_M) :
    wf_vrelop_Jnn_M v_Jnn v_M var_x →
    v_shape = (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M)) →
    wf_vrelop_ v_shape (vrelop_.mk_vrelop__0 v_Jnn v_M var_x)
  | vrelop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_M : M) (var_x : vrelop_Fnn_M) :
    v_shape = (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_M)) →
    wf_vrelop_ v_shape (vrelop_.mk_vrelop__1 v_Fnn v_M var_x)


def proj_vrelop__0 (var_x : vrelop_) : Option vrelop_Jnn_M :=
  match var_x with
  | vrelop_.mk_vrelop__0 v_Jnn v_M var_x => some var_x
  | _ => none

def proj_vrelop__1 (var_x : vrelop_) : Option vrelop_Fnn_M :=
  match var_x with
  | vrelop_.mk_vrelop__1 v_Fnn v_M var_x => some var_x
  | _ => none

inductive vshiftop_Jnn_M : Type where
  | SHL : vshiftop_Jnn_M
  | SHR (v_sx : sx) : vshiftop_Jnn_M
deriving Inhabited, BEq

inductive vshiftop_ : Type where
  | mk_vshiftop__0 (v_Jnn : Jnn) (v_M : M) (var_x : vshiftop_Jnn_M) : vshiftop_
deriving Inhabited, BEq

inductive wf_vshiftop_ : ishape → vshiftop_ → Prop where
  | vshiftop__case_0 (v_ishape : ishape) (v_Jnn : Jnn) (v_M : M) (var_x : vshiftop_Jnn_M) :
    v_ishape = (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vshiftop_ v_ishape (vshiftop_.mk_vshiftop__0 v_Jnn v_M var_x)


def proj_vshiftop__0 (var_x : vshiftop_) : vshiftop_Jnn_M :=
  match var_x with
  | vshiftop_.mk_vshiftop__0 v_Jnn v_M var_x => var_x

inductive vswizzlop_M : Type where
  | SWIZZLE : vswizzlop_M
  | RELAXED_SWIZZLE : vswizzlop_M
deriving Inhabited, BEq

inductive vswizzlop_ : Type where
  | mk_vswizzlop__0 (v_M : M) (var_x : vswizzlop_M) : vswizzlop_
deriving Inhabited, BEq

inductive wf_vswizzlop_ : bshape → vswizzlop_ → Prop where
  | vswizzlop__case_0 (v_bshape : bshape) (v_M : M) (var_x : vswizzlop_M) :
    v_bshape = (bshape.mk_bshape (shape.X lanetype.I8 (dim.mk_dim v_M))) →
    wf_vswizzlop_ v_bshape (vswizzlop_.mk_vswizzlop__0 v_M var_x)


def proj_vswizzlop__0 (var_x : vswizzlop_) : vswizzlop_M :=
  match var_x with
  | vswizzlop_.mk_vswizzlop__0 v_M var_x => var_x

inductive vextunop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTADD_PAIRWISE (v_sx : sx) : vextunop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq

inductive wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 : Jnn → M → Jnn → M → vextunop__Jnn_1_M_1_Jnn_2_M_2 → Prop where
  | vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_sx : sx) :
    (16 ≤ (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) ∧ (((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) ≤ 32)) →
    wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)


inductive vextunop__ : Type where
  | mk_vextunop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2) : vextunop__
deriving Inhabited, BEq

inductive wf_vextunop__ : ishape → ishape → vextunop__ → Prop where
  | vextunop___case_0 (ishape_1 : ishape) (ishape_2 : ishape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2) :
    wf_vextunop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x →
    ishape_1 = (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim M_1))) →
    ishape_2 = (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim M_2))) →
    wf_vextunop__ ishape_1 ishape_2 (vextunop__.mk_vextunop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)


def proj_vextunop___0 (var_x : vextunop__) : vextunop__Jnn_1_M_1_Jnn_2_M_2 :=
  match var_x with
  | vextunop__.mk_vextunop___0 Jnn_1 M_1 Jnn_2 M_2 var_x => var_x

inductive vextbinop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTMUL (v_half : half) (v_sx : sx) : vextbinop__Jnn_1_M_1_Jnn_2_M_2
  | DOTS : vextbinop__Jnn_1_M_1_Jnn_2_M_2
  | RELAXED_DOTS : vextbinop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq

inductive wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 : Jnn → M → Jnn → M → vextbinop__Jnn_1_M_1_Jnn_2_M_2 → Prop where
  | vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_half : half) (v_sx : sx) :
    ((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) ≥ 16) →
    wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)
  | vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) :
    ((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32) →
    wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS
  | vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) :
    ((2 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 16) →
    wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS


inductive vextbinop__ : Type where
  | mk_vextbinop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextbinop__Jnn_1_M_1_Jnn_2_M_2) : vextbinop__
deriving Inhabited, BEq

inductive wf_vextbinop__ : ishape → ishape → vextbinop__ → Prop where
  | vextbinop___case_0 (ishape_1 : ishape) (ishape_2 : ishape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextbinop__Jnn_1_M_1_Jnn_2_M_2) :
    wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x →
    ishape_1 = (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim M_1))) →
    ishape_2 = (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim M_2))) →
    wf_vextbinop__ ishape_1 ishape_2 (vextbinop__.mk_vextbinop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)


def proj_vextbinop___0 (var_x : vextbinop__) : vextbinop__Jnn_1_M_1_Jnn_2_M_2 :=
  match var_x with
  | vextbinop__.mk_vextbinop___0 Jnn_1 M_1 Jnn_2 M_2 var_x => var_x

inductive vextternop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | RELAXED_DOT_ADDS : vextternop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq

inductive wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 : Jnn → M → Jnn → M → vextternop__Jnn_1_M_1_Jnn_2_M_2 → Prop where
  | vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) :
    ((4 * (lsizenn1 (lanetype_Jnn Jnn_1))) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32) →
    wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS


inductive vextternop__ : Type where
  | mk_vextternop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextternop__Jnn_1_M_1_Jnn_2_M_2) : vextternop__
deriving Inhabited, BEq

inductive wf_vextternop__ : ishape → ishape → vextternop__ → Prop where
  | vextternop___case_0 (ishape_1 : ishape) (ishape_2 : ishape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vextternop__Jnn_1_M_1_Jnn_2_M_2) :
    wf_vextternop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x →
    ishape_1 = (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim M_1))) →
    ishape_2 = (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim M_2))) →
    wf_vextternop__ ishape_1 ishape_2 (vextternop__.mk_vextternop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)


def proj_vextternop___0 (var_x : vextternop__) : vextternop__Jnn_1_M_1_Jnn_2_M_2 :=
  match var_x with
  | vextternop__.mk_vextternop___0 Jnn_1 M_1 Jnn_2 M_2 var_x => var_x

inductive vcvtop__Jnn_1_M_1_Jnn_2_M_2 : Type where
  | EXTEND (v_half : half) (v_sx : sx) : vcvtop__Jnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq

inductive wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 : Jnn → M → Jnn → M → vcvtop__Jnn_1_M_1_Jnn_2_M_2 → Prop where
  | vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_half : half) (v_sx : sx) :
    (lsizenn2 (lanetype_Jnn Jnn_2)) = (2 * (lsizenn1 (lanetype_Jnn Jnn_1))) →
    wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)


inductive vcvtop__Jnn_1_M_1_Fnn_2_M_2 : Type where
  | CONVERT (half_opt : Option half) (v_sx : sx) : vcvtop__Jnn_1_M_1_Fnn_2_M_2
deriving Inhabited, BEq

inductive wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 : Jnn → M → Fnn → M → vcvtop__Jnn_1_M_1_Fnn_2_M_2 → Prop where
  | vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0 (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (half_opt : Option half) (v_sx : sx) :
    ((((sizenn2 (numtype_Fnn Fnn_2)) = (lsizenn1 (lanetype_Jnn Jnn_1))) ∧ ((lsizenn1 (lanetype_Jnn Jnn_1)) = 32)) ∧ (half_opt = none)) ∨ (((sizenn2 (numtype_Fnn Fnn_2)) = (2 * (lsizenn1 (lanetype_Jnn Jnn_1)))) ∧ (half_opt = (some half.LOW))) →
    wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 Jnn_1 M_1 Fnn_2 M_2 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)


inductive vcvtop__Fnn_1_M_1_Jnn_2_M_2 : Type where
  | TRUNC_SAT (v_sx : sx) (zero_opt : Option zero) : vcvtop__Fnn_1_M_1_Jnn_2_M_2
  | RELAXED_TRUNC (v_sx : sx) (zero_opt : Option zero) : vcvtop__Fnn_1_M_1_Jnn_2_M_2
deriving Inhabited, BEq

inductive wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 : Fnn → M → Jnn → M → vcvtop__Fnn_1_M_1_Jnn_2_M_2 → Prop where
  | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0 (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_sx : sx) (zero_opt : Option zero) :
    ((((sizenn1 (numtype_Fnn Fnn_1)) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32)) ∧ (zero_opt = none)) ∨ (((sizenn1 (numtype_Fnn Fnn_1)) = (2 * (lsizenn2 (lanetype_Jnn Jnn_2)))) ∧ (zero_opt = (some zero.ZERO))) →
    wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)
  | vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_1 (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (v_sx : sx) (zero_opt : Option zero) :
    ((((sizenn1 (numtype_Fnn Fnn_1)) = (lsizenn2 (lanetype_Jnn Jnn_2))) ∧ ((lsizenn2 (lanetype_Jnn Jnn_2)) = 32)) ∧ (zero_opt = none)) ∨ (((sizenn1 (numtype_Fnn Fnn_1)) = (2 * (lsizenn2 (lanetype_Jnn Jnn_2)))) ∧ (zero_opt = (some zero.ZERO))) →
    wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)


inductive vcvtop__Fnn_1_M_1_Fnn_2_M_2 : Type where
  | DEMOTE (v_zero : zero) : vcvtop__Fnn_1_M_1_Fnn_2_M_2
  | PROMOTELOW : vcvtop__Fnn_1_M_1_Fnn_2_M_2
deriving Inhabited, BEq

inductive wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 : Fnn → M → Fnn → M → vcvtop__Fnn_1_M_1_Fnn_2_M_2 → Prop where
  | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (v_zero : zero) :
    (sizenn1 (numtype_Fnn Fnn_1)) = (2 * (sizenn2 (numtype_Fnn Fnn_2))) →
    wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)
  | vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) :
    (2 * (sizenn1 (numtype_Fnn Fnn_1))) = (sizenn2 (numtype_Fnn Fnn_2)) →
    wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW


inductive vcvtop__ : Type where
  | mk_vcvtop___0 (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Jnn_2_M_2) : vcvtop__
  | mk_vcvtop___1 (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Fnn_2_M_2) : vcvtop__
  | mk_vcvtop___2 (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Jnn_2_M_2) : vcvtop__
  | mk_vcvtop___3 (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Fnn_2_M_2) : vcvtop__
deriving Inhabited, BEq

inductive wf_vcvtop__ : shape → shape → vcvtop__ → Prop where
  | vcvtop___case_0 (shape_1 : shape) (shape_2 : shape) (Jnn_1 : Jnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Jnn_2_M_2) :
    wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2 Jnn_1 M_1 Jnn_2 M_2 var_x →
    shape_1 = (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim M_1)) →
    shape_2 = (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim M_2)) →
    wf_vcvtop__ shape_1 shape_2 (vcvtop__.mk_vcvtop___0 Jnn_1 M_1 Jnn_2 M_2 var_x)
  | vcvtop___case_1 (shape_1 : shape) (shape_2 : shape) (Jnn_1 : Jnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Jnn_1_M_1_Fnn_2_M_2) :
    wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2 Jnn_1 M_1 Fnn_2 M_2 var_x →
    shape_1 = (shape.X (lanetype_Jnn Jnn_1) (dim.mk_dim M_1)) →
    shape_2 = (shape.X (lanetype_Fnn Fnn_2) (dim.mk_dim M_2)) →
    wf_vcvtop__ shape_1 shape_2 (vcvtop__.mk_vcvtop___1 Jnn_1 M_1 Fnn_2 M_2 var_x)
  | vcvtop___case_2 (shape_1 : shape) (shape_2 : shape) (Fnn_1 : Fnn) (M_1 : M) (Jnn_2 : Jnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Jnn_2_M_2) :
    wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2 Fnn_1 M_1 Jnn_2 M_2 var_x →
    shape_1 = (shape.X (lanetype_Fnn Fnn_1) (dim.mk_dim M_1)) →
    shape_2 = (shape.X (lanetype_Jnn Jnn_2) (dim.mk_dim M_2)) →
    wf_vcvtop__ shape_1 shape_2 (vcvtop__.mk_vcvtop___2 Fnn_1 M_1 Jnn_2 M_2 var_x)
  | vcvtop___case_3 (shape_1 : shape) (shape_2 : shape) (Fnn_1 : Fnn) (M_1 : M) (Fnn_2 : Fnn) (M_2 : M) (var_x : vcvtop__Fnn_1_M_1_Fnn_2_M_2) :
    wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2 Fnn_1 M_1 Fnn_2 M_2 var_x →
    shape_1 = (shape.X (lanetype_Fnn Fnn_1) (dim.mk_dim M_1)) →
    shape_2 = (shape.X (lanetype_Fnn Fnn_2) (dim.mk_dim M_2)) →
    wf_vcvtop__ shape_1 shape_2 (vcvtop__.mk_vcvtop___3 Fnn_1 M_1 Fnn_2 M_2 var_x)


def proj_vcvtop___0 (var_x : vcvtop__) : Option vcvtop__Jnn_1_M_1_Jnn_2_M_2 :=
  match var_x with
  | vcvtop__.mk_vcvtop___0 Jnn_1 M_1 Jnn_2 M_2 var_x => some var_x
  | _ => none

def proj_vcvtop___1 (var_x : vcvtop__) : Option vcvtop__Jnn_1_M_1_Fnn_2_M_2 :=
  match var_x with
  | vcvtop__.mk_vcvtop___1 Jnn_1 M_1 Fnn_2 M_2 var_x => some var_x
  | _ => none

def proj_vcvtop___2 (var_x : vcvtop__) : Option vcvtop__Fnn_1_M_1_Jnn_2_M_2 :=
  match var_x with
  | vcvtop__.mk_vcvtop___2 Fnn_1 M_1 Jnn_2 M_2 var_x => some var_x
  | _ => none

def proj_vcvtop___3 (var_x : vcvtop__) : Option vcvtop__Fnn_1_M_1_Fnn_2_M_2 :=
  match var_x with
  | vcvtop__.mk_vcvtop___3 Fnn_1 M_1 Fnn_2 M_2 var_x => some var_x
  | _ => none

structure memarg where
  MKmemarg ::
  ALIGN : u32
  OFFSET : u64
deriving Inhabited, BEq

inductive wf_memarg : memarg → Prop where
  | memarg_case_ (var_0 : u32) (var_1 : u64) :
    wf_uN 32 var_0 →
    wf_uN 64 var_1 →
    wf_memarg ({
      ALIGN := var_0
      OFFSET := var_1 : memarg
    })


inductive loadop_Inn : Type where
  | mk_loadop_Inn (v_sz : sz) (v_sx : sx) : loadop_Inn
deriving Inhabited, BEq

inductive wf_loadop_Inn : Inn → loadop_Inn → Prop where
  | loadop_Inn_case_0 (v_Inn : Inn) (v_sz : sz) (v_sx : sx) :
    wf_sz v_sz →
    (proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn)) →
    wf_loadop_Inn v_Inn (loadop_Inn.mk_loadop_Inn v_sz v_sx)


inductive loadop_ : Type where
  | mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq

inductive wf_loadop_ : numtype → loadop_ → Prop where
  | loadop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : loadop_Inn) :
    wf_loadop_Inn v_Inn var_x →
    v_numtype = (numtype_addrtype v_Inn) →
    wf_loadop_ v_numtype (loadop_.mk_loadop__0 v_Inn var_x)


def proj_loadop__0 (var_x : loadop_) : loadop_Inn :=
  match var_x with
  | loadop_.mk_loadop__0 v_Inn var_x => var_x

inductive storeop_Inn : Type where
  | mk_storeop_Inn (v_sz : sz) : storeop_Inn
deriving Inhabited, BEq

inductive wf_storeop_Inn : Inn → storeop_Inn → Prop where
  | storeop_Inn_case_0 (v_Inn : Inn) (v_sz : sz) :
    wf_sz v_sz →
    (proj_sz_0 v_sz) < (sizenn (numtype_addrtype v_Inn)) →
    wf_storeop_Inn v_Inn (storeop_Inn.mk_storeop_Inn v_sz)


inductive storeop_ : Type where
  | mk_storeop__0 (v_Inn : Inn) (var_x : storeop_Inn) : storeop_
deriving Inhabited, BEq

inductive wf_storeop_ : numtype → storeop_ → Prop where
  | storeop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : storeop_Inn) :
    wf_storeop_Inn v_Inn var_x →
    v_numtype = (numtype_addrtype v_Inn) →
    wf_storeop_ v_numtype (storeop_.mk_storeop__0 v_Inn var_x)


def proj_storeop__0 (var_x : storeop_) : storeop_Inn :=
  match var_x with
  | storeop_.mk_storeop__0 v_Inn var_x => var_x

inductive vloadop_ : Type where
  | SHAPEX_ (v_sz : sz) (v_M : M) (v_sx : sx) : vloadop_
  | SPLAT (v_sz : sz) : vloadop_
  | ZERO (v_sz : sz) : vloadop_
deriving Inhabited, BEq

inductive wf_vloadop_ : vectype → vloadop_ → Prop where
  | vloadop__case_0 (v_vectype : vectype) (v_sz : sz) (v_M : M) (v_sx : sx) :
    wf_sz v_sz →
    (((proj_sz_0 v_sz) * v_M) : Rat) = (((vsize v_vectype) : Rat) / (2 : Rat)) →
    wf_vloadop_ v_vectype (vloadop_.SHAPEX_ v_sz v_M v_sx)
  | vloadop__case_1 (v_vectype : vectype) (v_sz : sz) :
    wf_sz v_sz →
    wf_vloadop_ v_vectype (vloadop_.SPLAT v_sz)
  | vloadop__case_2 (v_vectype : vectype) (v_sz : sz) :
    wf_sz v_sz →
    (proj_sz_0 v_sz) ≥ 32 →
    wf_vloadop_ v_vectype (vloadop_.ZERO v_sz)


inductive blocktype : Type where
  | _RESULT (valtype_opt : Option valtype) : blocktype
  | _IDX (v_typeidx : typeidx) : blocktype
deriving Inhabited, BEq

inductive wf_blocktype : blocktype → Prop where
  | blocktype_case_0 (valtype_opt : Option valtype) :
    Forall (fun v_valtype_elem => wf_valtype v_valtype_elem) (Option.toList valtype_opt) →
    wf_blocktype (blocktype._RESULT valtype_opt)
  | blocktype_case_1 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_blocktype (blocktype._IDX v_typeidx)


abbrev addr : Type := Nat

abbrev arrayaddr : Type := addr

inductive «catch» : Type where
  | CATCH (v_tagidx : tagidx) (v_labelidx : labelidx) : «catch»
  | CATCH_REF (v_tagidx : tagidx) (v_labelidx : labelidx) : «catch»
  | CATCH_ALL (v_labelidx : labelidx) : «catch»
  | CATCH_ALL_REF (v_labelidx : labelidx) : «catch»
deriving Inhabited, BEq

inductive wf_catch : «catch» → Prop where
  | catch_case_0 (v_tagidx : tagidx) (v_labelidx : labelidx) :
    wf_uN 32 v_tagidx →
    wf_uN 32 v_labelidx →
    wf_catch (catch.CATCH v_tagidx v_labelidx)
  | catch_case_1 (v_tagidx : tagidx) (v_labelidx : labelidx) :
    wf_uN 32 v_tagidx →
    wf_uN 32 v_labelidx →
    wf_catch (catch.CATCH_REF v_tagidx v_labelidx)
  | catch_case_2 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_catch (catch.CATCH_ALL v_labelidx)
  | catch_case_3 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_catch (catch.CATCH_ALL_REF v_labelidx)


abbrev exnaddr : Type := addr

abbrev dataaddr : Type := addr

abbrev elemaddr : Type := addr

abbrev funcaddr : Type := addr

abbrev globaladdr : Type := addr

abbrev memaddr : Type := addr

abbrev tableaddr : Type := addr

abbrev tagaddr : Type := addr

inductive externaddr : Type where
  | TAG (v_tagaddr : tagaddr) : externaddr
  | GLOBAL (v_globaladdr : globaladdr) : externaddr
  | MEM (v_memaddr : memaddr) : externaddr
  | TABLE (v_tableaddr : tableaddr) : externaddr
  | FUNC (v_funcaddr : funcaddr) : externaddr
deriving Inhabited, BEq

structure exportinst where
  MKexportinst ::
  NAME : name
  ADDR : externaddr
deriving Inhabited, BEq

inductive wf_exportinst : exportinst → Prop where
  | exportinst_case_ (var_0 : name) (var_1 : externaddr) :
    wf_name var_0 →
    wf_exportinst ({
      NAME := var_0
      ADDR := var_1 : exportinst
    })


structure moduleinst where
  MKmoduleinst ::
  TYPES : List deftype
  TAGS : List tagaddr
  GLOBALS : List globaladdr
  MEMS : List memaddr
  TABLES : List tableaddr
  FUNCS : List funcaddr
  DATAS : List dataaddr
  ELEMS : List elemaddr
  EXPORTS : List exportinst
deriving Inhabited, BEq

inductive wf_moduleinst : moduleinst → Prop where
  | moduleinst_case_ (var_0_lst : List deftype) (var_1_lst : List tagaddr) (var_2_lst : List globaladdr) (var_3_lst : List memaddr) (var_4_lst : List tableaddr) (var_5_lst : List funcaddr) (var_6_lst : List dataaddr) (var_7_lst : List elemaddr) (var_8_lst : List exportinst) :
    Forall (fun var_8_elem => wf_exportinst var_8_elem) var_8_lst →
    wf_moduleinst ({
      TYPES := var_0_lst
      TAGS := var_1_lst
      GLOBALS := var_2_lst
      MEMS := var_3_lst
      TABLES := var_4_lst
      FUNCS := var_5_lst
      DATAS := var_6_lst
      ELEMS := var_7_lst
      EXPORTS := var_8_lst : moduleinst
    })


abbrev hostaddr : Type := addr

abbrev structaddr : Type := addr

inductive ref : Type where
  | REF_I31_NUM (v_u31 : u31) : ref
  | REF_NULL_ADDR : ref
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : ref
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : ref
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : ref
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : ref
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : ref
  | REF_EXTERN (v_ref : ref) : ref
deriving Inhabited, BEq

inductive wf_ref : ref → Prop where
  | ref_case_0 (v_u31 : u31) :
    wf_uN 31 v_u31 →
    wf_ref (ref.REF_I31_NUM v_u31)
  | ref_case_1 : wf_ref ref.REF_NULL_ADDR
  | ref_case_2 (v_structaddr : structaddr) : wf_ref (ref.REF_STRUCT_ADDR v_structaddr)
  | ref_case_3 (v_arrayaddr : arrayaddr) : wf_ref (ref.REF_ARRAY_ADDR v_arrayaddr)
  | ref_case_4 (v_funcaddr : funcaddr) : wf_ref (ref.REF_FUNC_ADDR v_funcaddr)
  | ref_case_5 (v_exnaddr : exnaddr) : wf_ref (ref.REF_EXN_ADDR v_exnaddr)
  | ref_case_6 (v_hostaddr : hostaddr) : wf_ref (ref.REF_HOST_ADDR v_hostaddr)
  | ref_case_7 (v_ref : ref) : wf_ref (ref.REF_EXTERN v_ref)


inductive val : Type where
  | CONST (v_numtype : numtype) (_ : num_) : val
  | VCONST (v_vectype : vectype) (_ : vec_) : val
  | REF_I31_NUM (v_u31 : u31) : val
  | REF_NULL_ADDR : val
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : val
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : val
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : val
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : val
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : val
  | REF_EXTERN (v_ref : ref) : val
deriving Inhabited, BEq

def val_ref (var_0 : ref) : val :=
  match var_0 with
  | ref.REF_I31_NUM x0 => val.REF_I31_NUM x0
  | ref.REF_NULL_ADDR => val.REF_NULL_ADDR
  | ref.REF_STRUCT_ADDR x0 => val.REF_STRUCT_ADDR x0
  | ref.REF_ARRAY_ADDR x0 => val.REF_ARRAY_ADDR x0
  | ref.REF_FUNC_ADDR x0 => val.REF_FUNC_ADDR x0
  | ref.REF_EXN_ADDR x0 => val.REF_EXN_ADDR x0
  | ref.REF_HOST_ADDR x0 => val.REF_HOST_ADDR x0
  | ref.REF_EXTERN x0 => val.REF_EXTERN x0

inductive wf_val : val → Prop where
  | val_case_0 (v_numtype : numtype) (var_0 : num_) :
    wf_num_ v_numtype var_0 →
    wf_val (val.CONST v_numtype var_0)
  | val_case_1 (v_vectype : vectype) (var_0 : vec_) :
    wf_uN (vsize v_vectype) var_0 →
    wf_val (val.VCONST v_vectype var_0)
  | val_case_2 (v_u31 : u31) :
    wf_uN 31 v_u31 →
    wf_val (val.REF_I31_NUM v_u31)
  | val_case_3 : wf_val val.REF_NULL_ADDR
  | val_case_4 (v_structaddr : structaddr) : wf_val (val.REF_STRUCT_ADDR v_structaddr)
  | val_case_5 (v_arrayaddr : arrayaddr) : wf_val (val.REF_ARRAY_ADDR v_arrayaddr)
  | val_case_6 (v_funcaddr : funcaddr) : wf_val (val.REF_FUNC_ADDR v_funcaddr)
  | val_case_7 (v_exnaddr : exnaddr) : wf_val (val.REF_EXN_ADDR v_exnaddr)
  | val_case_8 (v_hostaddr : hostaddr) : wf_val (val.REF_HOST_ADDR v_hostaddr)
  | val_case_9 (v_ref : ref) :
    wf_ref v_ref →
    wf_val (val.REF_EXTERN v_ref)


structure frame where
  MKframe ::
  LOCALS : List (Option val)
  MODULE : moduleinst
deriving Inhabited, BEq

inductive wf_frame : frame → Prop where
  | frame_case_ (var_0_opt_lst : List (Option val)) (var_1 : moduleinst) :
    Forall (fun var_0_opt_elem => Forall (fun var_0_elem => wf_val var_0_elem) (Option.toList var_0_opt_elem)) var_0_opt_lst →
    wf_moduleinst var_1 →
    wf_frame ({
      LOCALS := var_0_opt_lst
      MODULE := var_1 : frame
    })


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
  | BR_ON_NULL (v_labelidx : labelidx) : instr
  | BR_ON_NON_NULL (v_labelidx : labelidx) : instr
  | BR_ON_CAST (v_labelidx : labelidx) (v_reftype_0 : reftype) (v_reftype_1 : reftype) : instr
  | BR_ON_CAST_FAIL (v_labelidx : labelidx) (v_reftype_0 : reftype) (v_reftype_1 : reftype) : instr
  | CALL (v_funcidx : funcidx) : instr
  | CALL_REF (v_typeuse : typeuse) : instr
  | CALL_INDIRECT (v_tableidx : tableidx) (v_typeuse : typeuse) : instr
  | RETURN : instr
  | RETURN_CALL (v_funcidx : funcidx) : instr
  | RETURN_CALL_REF (v_typeuse : typeuse) : instr
  | RETURN_CALL_INDIRECT (v_tableidx : tableidx) (v_typeuse : typeuse) : instr
  | THROW (v_tagidx : tagidx) : instr
  | THROW_REF : instr
  | TRY_TABLE (v_blocktype : blocktype) (_ : list «catch») (instr_lst : List instr) : instr
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
  | LOAD (v_numtype : numtype) (_ : Option loadop_) (v_memidx : memidx) (v_memarg : memarg) : instr
  | STORE (v_numtype : numtype) (_ : Option storeop_) (v_memidx : memidx) (v_memarg : memarg) : instr
  | VLOAD (v_vectype : vectype) (_ : Option vloadop_) (v_memidx : memidx) (v_memarg : memarg) : instr
  | VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memidx : memidx) (v_memarg : memarg) (v_laneidx : laneidx) : instr
  | VSTORE (v_vectype : vectype) (v_memidx : memidx) (v_memarg : memarg) : instr
  | VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memidx : memidx) (v_memarg : memarg) (v_laneidx : laneidx) : instr
  | MEMORY_SIZE (v_memidx : memidx) : instr
  | MEMORY_GROW (v_memidx : memidx) : instr
  | MEMORY_FILL (v_memidx : memidx) : instr
  | MEMORY_COPY (v_memidx_0 : memidx) (v_memidx_1 : memidx) : instr
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
  | STRUCT_GET (sx_opt : Option sx) (v_typeidx : typeidx) (v_fieldidx : fieldidx) : instr
  | STRUCT_SET (v_typeidx : typeidx) (v_fieldidx : fieldidx) : instr
  | ARRAY_NEW (v_typeidx : typeidx) : instr
  | ARRAY_NEW_DEFAULT (v_typeidx : typeidx) : instr
  | ARRAY_NEW_FIXED (v_typeidx : typeidx) (v_u32 : u32) : instr
  | ARRAY_NEW_DATA (v_typeidx : typeidx) (v_dataidx : dataidx) : instr
  | ARRAY_NEW_ELEM (v_typeidx : typeidx) (v_elemidx : elemidx) : instr
  | ARRAY_GET (sx_opt : Option sx) (v_typeidx : typeidx) : instr
  | ARRAY_SET (v_typeidx : typeidx) : instr
  | ARRAY_LEN : instr
  | ARRAY_FILL (v_typeidx : typeidx) : instr
  | ARRAY_COPY (v_typeidx_0 : typeidx) (v_typeidx_1 : typeidx) : instr
  | ARRAY_INIT_DATA (v_typeidx : typeidx) (v_dataidx : dataidx) : instr
  | ARRAY_INIT_ELEM (v_typeidx : typeidx) (v_elemidx : elemidx) : instr
  | EXTERN_CONVERT_ANY : instr
  | ANY_CONVERT_EXTERN : instr
  | CONST (v_numtype : numtype) (_ : num_) : instr
  | UNOP (v_numtype : numtype) (_ : unop_) : instr
  | BINOP (v_numtype : numtype) (_ : binop_) : instr
  | TESTOP (v_numtype : numtype) (_ : testop_) : instr
  | RELOP (v_numtype : numtype) (_ : relop_) : instr
  | CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (_ : cvtop__) : instr
  | VCONST (v_vectype : vectype) (_ : vec_) : instr
  | VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : instr
  | VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : instr
  | VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : instr
  | VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : instr
  | VUNOP (v_shape : shape) (_ : vunop_) : instr
  | VBINOP (v_shape : shape) (_ : vbinop_) : instr
  | VTERNOP (v_shape : shape) (_ : vternop_) : instr
  | VTESTOP (v_shape : shape) (_ : vtestop_) : instr
  | VRELOP (v_shape : shape) (_ : vrelop_) : instr
  | VSHIFTOP (v_ishape : ishape) (_ : vshiftop_) : instr
  | VBITMASK (v_ishape : ishape) : instr
  | VSWIZZLOP (v_bshape : bshape) (_ : vswizzlop_) : instr
  | VSHUFFLE (v_bshape : bshape) (laneidx_lst : List laneidx) : instr
  | VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextunop__) : instr
  | VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextbinop__) : instr
  | VEXTTERNOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextternop__) : instr
  | VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : instr
  | VCVTOP (shape_1 : shape) (shape_2 : shape) (_ : vcvtop__) : instr
  | VSPLAT (v_shape : shape) : instr
  | VEXTRACT_LANE (v_shape : shape) (sx_opt : Option sx) (v_laneidx : laneidx) : instr
  | VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : instr
  | REF_I31_NUM (v_u31 : u31) : instr
  | REF_NULL_ADDR : instr
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : instr
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : instr
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : instr
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : instr
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : instr
  | REF_EXTERN (v_ref : ref) : instr
  | LABEL_ (v_n : n) (instr_lst_0 : List instr) (instr_lst_1 : List instr) : instr
  | FRAME_ (v_n : n) (v_frame : frame) (instr_lst : List instr) : instr
  | HANDLER_ (v_n : n) (catch_lst : List «catch») (instr_lst : List instr) : instr
  | TRAP : instr
deriving Inhabited, BEq

inductive wf_instr : instr → Prop where
  | instr_case_0 : wf_instr instr.NOP
  | instr_case_1 : wf_instr instr.UNREACHABLE
  | instr_case_2 : wf_instr instr.DROP
  | instr_case_3 (valtype_lst_opt : Option (List valtype)) :
    Forall (fun valtype_lst_elem => Forall (fun v_valtype_elem => wf_valtype v_valtype_elem) valtype_lst_elem) (Option.toList valtype_lst_opt) →
    wf_instr (instr.SELECT valtype_lst_opt)
  | instr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.BLOCK v_blocktype instr_lst)
  | instr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.LOOP v_blocktype instr_lst)
  | instr_case_6 (v_blocktype : blocktype) (instr_lst : List instr) (instr_lst_0_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    Forall (fun instr_lst_0_elem => wf_instr instr_lst_0_elem) instr_lst_0_lst →
    wf_instr (instr.IFELSE v_blocktype instr_lst instr_lst_0_lst)
  | instr_case_7 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR v_labelidx)
  | instr_case_8 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_IF v_labelidx)
  | instr_case_9 (labelidx_lst : List labelidx) (v_labelidx : labelidx) :
    Forall (fun v_labelidx_elem => wf_uN 32 v_labelidx_elem) labelidx_lst →
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_TABLE labelidx_lst v_labelidx)
  | instr_case_10 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_ON_NULL v_labelidx)
  | instr_case_11 (v_labelidx : labelidx) :
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_ON_NON_NULL v_labelidx)
  | instr_case_12 (v_labelidx : labelidx) (v_reftype : reftype) (reftype_0 : reftype) :
    wf_uN 32 v_labelidx →
    wf_reftype v_reftype →
    wf_reftype reftype_0 →
    wf_instr (instr.BR_ON_CAST v_labelidx v_reftype reftype_0)
  | instr_case_13 (v_labelidx : labelidx) (v_reftype : reftype) (reftype_0 : reftype) :
    wf_uN 32 v_labelidx →
    wf_reftype v_reftype →
    wf_reftype reftype_0 →
    wf_instr (instr.BR_ON_CAST_FAIL v_labelidx v_reftype reftype_0)
  | instr_case_14 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_instr (instr.CALL v_funcidx)
  | instr_case_15 (v_typeuse : typeuse) :
    wf_typeuse v_typeuse →
    wf_instr (instr.CALL_REF v_typeuse)
  | instr_case_16 (v_tableidx : tableidx) (v_typeuse : typeuse) :
    wf_uN 32 v_tableidx →
    wf_typeuse v_typeuse →
    wf_instr (instr.CALL_INDIRECT v_tableidx v_typeuse)
  | instr_case_17 : wf_instr instr.RETURN
  | instr_case_18 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_instr (instr.RETURN_CALL v_funcidx)
  | instr_case_19 (v_typeuse : typeuse) :
    wf_typeuse v_typeuse →
    wf_instr (instr.RETURN_CALL_REF v_typeuse)
  | instr_case_20 (v_tableidx : tableidx) (v_typeuse : typeuse) :
    wf_uN 32 v_tableidx →
    wf_typeuse v_typeuse →
    wf_instr (instr.RETURN_CALL_INDIRECT v_tableidx v_typeuse)
  | instr_case_21 (v_tagidx : tagidx) :
    wf_uN 32 v_tagidx →
    wf_instr (instr.THROW v_tagidx)
  | instr_case_22 : wf_instr instr.THROW_REF
  | instr_case_23 (v_blocktype : blocktype) (var_0 : list «catch») (instr_lst : List instr) :
    wf_blocktype v_blocktype →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.TRY_TABLE v_blocktype var_0 instr_lst)
  | instr_case_24 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_GET v_localidx)
  | instr_case_25 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_SET v_localidx)
  | instr_case_26 (v_localidx : localidx) :
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_TEE v_localidx)
  | instr_case_27 (v_globalidx : globalidx) :
    wf_uN 32 v_globalidx →
    wf_instr (instr.GLOBAL_GET v_globalidx)
  | instr_case_28 (v_globalidx : globalidx) :
    wf_uN 32 v_globalidx →
    wf_instr (instr.GLOBAL_SET v_globalidx)
  | instr_case_29 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_GET v_tableidx)
  | instr_case_30 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_SET v_tableidx)
  | instr_case_31 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_SIZE v_tableidx)
  | instr_case_32 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_GROW v_tableidx)
  | instr_case_33 (v_tableidx : tableidx) :
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_FILL v_tableidx)
  | instr_case_34 (v_tableidx : tableidx) (tableidx_0 : tableidx) :
    wf_uN 32 v_tableidx →
    wf_uN 32 tableidx_0 →
    wf_instr (instr.TABLE_COPY v_tableidx tableidx_0)
  | instr_case_35 (v_tableidx : tableidx) (v_elemidx : elemidx) :
    wf_uN 32 v_tableidx →
    wf_uN 32 v_elemidx →
    wf_instr (instr.TABLE_INIT v_tableidx v_elemidx)
  | instr_case_36 (v_elemidx : elemidx) :
    wf_uN 32 v_elemidx →
    wf_instr (instr.ELEM_DROP v_elemidx)
  | instr_case_37 (v_numtype : numtype) (var_0_opt : Option loadop_) (v_memidx : memidx) (v_memarg : memarg) :
    Forall (fun var_0_elem => wf_loadop_ v_numtype var_0_elem) (Option.toList var_0_opt) →
    wf_uN 32 v_memidx →
    wf_memarg v_memarg →
    wf_instr (instr.LOAD v_numtype var_0_opt v_memidx v_memarg)
  | instr_case_38 (v_numtype : numtype) (var_0_opt : Option storeop_) (v_memidx : memidx) (v_memarg : memarg) :
    Forall (fun var_0_elem => wf_storeop_ v_numtype var_0_elem) (Option.toList var_0_opt) →
    wf_uN 32 v_memidx →
    wf_memarg v_memarg →
    wf_instr (instr.STORE v_numtype var_0_opt v_memidx v_memarg)
  | instr_case_39 (v_vectype : vectype) (var_0_opt : Option vloadop_) (v_memidx : memidx) (v_memarg : memarg) :
    Forall (fun var_0_elem => wf_vloadop_ v_vectype var_0_elem) (Option.toList var_0_opt) →
    wf_uN 32 v_memidx →
    wf_memarg v_memarg →
    wf_instr (instr.VLOAD v_vectype var_0_opt v_memidx v_memarg)
  | instr_case_40 (v_vectype : vectype) (v_sz : sz) (v_memidx : memidx) (v_memarg : memarg) (v_laneidx : laneidx) :
    wf_sz v_sz →
    wf_uN 32 v_memidx →
    wf_memarg v_memarg →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VLOAD_LANE v_vectype v_sz v_memidx v_memarg v_laneidx)
  | instr_case_41 (v_vectype : vectype) (v_memidx : memidx) (v_memarg : memarg) :
    wf_uN 32 v_memidx →
    wf_memarg v_memarg →
    wf_instr (instr.VSTORE v_vectype v_memidx v_memarg)
  | instr_case_42 (v_vectype : vectype) (v_sz : sz) (v_memidx : memidx) (v_memarg : memarg) (v_laneidx : laneidx) :
    wf_sz v_sz →
    wf_uN 32 v_memidx →
    wf_memarg v_memarg →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VSTORE_LANE v_vectype v_sz v_memidx v_memarg v_laneidx)
  | instr_case_43 (v_memidx : memidx) :
    wf_uN 32 v_memidx →
    wf_instr (instr.MEMORY_SIZE v_memidx)
  | instr_case_44 (v_memidx : memidx) :
    wf_uN 32 v_memidx →
    wf_instr (instr.MEMORY_GROW v_memidx)
  | instr_case_45 (v_memidx : memidx) :
    wf_uN 32 v_memidx →
    wf_instr (instr.MEMORY_FILL v_memidx)
  | instr_case_46 (v_memidx : memidx) (memidx_0 : memidx) :
    wf_uN 32 v_memidx →
    wf_uN 32 memidx_0 →
    wf_instr (instr.MEMORY_COPY v_memidx memidx_0)
  | instr_case_47 (v_memidx : memidx) (v_dataidx : dataidx) :
    wf_uN 32 v_memidx →
    wf_uN 32 v_dataidx →
    wf_instr (instr.MEMORY_INIT v_memidx v_dataidx)
  | instr_case_48 (v_dataidx : dataidx) :
    wf_uN 32 v_dataidx →
    wf_instr (instr.DATA_DROP v_dataidx)
  | instr_case_49 (v_heaptype : heaptype) :
    wf_heaptype v_heaptype →
    wf_instr (instr.REF_NULL v_heaptype)
  | instr_case_50 : wf_instr instr.REF_IS_NULL
  | instr_case_51 : wf_instr instr.REF_AS_NON_NULL
  | instr_case_52 : wf_instr instr.REF_EQ
  | instr_case_53 (v_reftype : reftype) :
    wf_reftype v_reftype →
    wf_instr (instr.REF_TEST v_reftype)
  | instr_case_54 (v_reftype : reftype) :
    wf_reftype v_reftype →
    wf_instr (instr.REF_CAST v_reftype)
  | instr_case_55 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_instr (instr.REF_FUNC v_funcidx)
  | instr_case_56 : wf_instr instr.REF_I31
  | instr_case_57 (v_sx : sx) : wf_instr (instr.I31_GET v_sx)
  | instr_case_58 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_instr (instr.STRUCT_NEW v_typeidx)
  | instr_case_59 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_instr (instr.STRUCT_NEW_DEFAULT v_typeidx)
  | instr_case_60 (sx_opt : Option sx) (v_typeidx : typeidx) (v_fieldidx : fieldidx) :
    wf_uN 32 v_typeidx →
    wf_uN 32 v_fieldidx →
    wf_instr (instr.STRUCT_GET sx_opt v_typeidx v_fieldidx)
  | instr_case_61 (v_typeidx : typeidx) (v_fieldidx : fieldidx) :
    wf_uN 32 v_typeidx →
    wf_uN 32 v_fieldidx →
    wf_instr (instr.STRUCT_SET v_typeidx v_fieldidx)
  | instr_case_62 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_instr (instr.ARRAY_NEW v_typeidx)
  | instr_case_63 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_instr (instr.ARRAY_NEW_DEFAULT v_typeidx)
  | instr_case_64 (v_typeidx : typeidx) (v_u32 : u32) :
    wf_uN 32 v_typeidx →
    wf_uN 32 v_u32 →
    wf_instr (instr.ARRAY_NEW_FIXED v_typeidx v_u32)
  | instr_case_65 (v_typeidx : typeidx) (v_dataidx : dataidx) :
    wf_uN 32 v_typeidx →
    wf_uN 32 v_dataidx →
    wf_instr (instr.ARRAY_NEW_DATA v_typeidx v_dataidx)
  | instr_case_66 (v_typeidx : typeidx) (v_elemidx : elemidx) :
    wf_uN 32 v_typeidx →
    wf_uN 32 v_elemidx →
    wf_instr (instr.ARRAY_NEW_ELEM v_typeidx v_elemidx)
  | instr_case_67 (sx_opt : Option sx) (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_instr (instr.ARRAY_GET sx_opt v_typeidx)
  | instr_case_68 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_instr (instr.ARRAY_SET v_typeidx)
  | instr_case_69 : wf_instr instr.ARRAY_LEN
  | instr_case_70 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_instr (instr.ARRAY_FILL v_typeidx)
  | instr_case_71 (v_typeidx : typeidx) (typeidx_0 : typeidx) :
    wf_uN 32 v_typeidx →
    wf_uN 32 typeidx_0 →
    wf_instr (instr.ARRAY_COPY v_typeidx typeidx_0)
  | instr_case_72 (v_typeidx : typeidx) (v_dataidx : dataidx) :
    wf_uN 32 v_typeidx →
    wf_uN 32 v_dataidx →
    wf_instr (instr.ARRAY_INIT_DATA v_typeidx v_dataidx)
  | instr_case_73 (v_typeidx : typeidx) (v_elemidx : elemidx) :
    wf_uN 32 v_typeidx →
    wf_uN 32 v_elemidx →
    wf_instr (instr.ARRAY_INIT_ELEM v_typeidx v_elemidx)
  | instr_case_74 : wf_instr instr.EXTERN_CONVERT_ANY
  | instr_case_75 : wf_instr instr.ANY_CONVERT_EXTERN
  | instr_case_76 (v_numtype : numtype) (var_0 : num_) :
    wf_num_ v_numtype var_0 →
    wf_instr (instr.CONST v_numtype var_0)
  | instr_case_77 (v_numtype : numtype) (var_0 : unop_) :
    wf_unop_ v_numtype var_0 →
    wf_instr (instr.UNOP v_numtype var_0)
  | instr_case_78 (v_numtype : numtype) (var_0 : binop_) :
    wf_binop_ v_numtype var_0 →
    wf_instr (instr.BINOP v_numtype var_0)
  | instr_case_79 (v_numtype : numtype) (var_0 : testop_) :
    wf_testop_ v_numtype var_0 →
    wf_instr (instr.TESTOP v_numtype var_0)
  | instr_case_80 (v_numtype : numtype) (var_0 : relop_) :
    wf_relop_ v_numtype var_0 →
    wf_instr (instr.RELOP v_numtype var_0)
  | instr_case_81 (numtype_1 : numtype) (numtype_2 : numtype) (var_0 : cvtop__) :
    wf_cvtop__ numtype_2 numtype_1 var_0 →
    wf_instr (instr.CVTOP numtype_1 numtype_2 var_0)
  | instr_case_82 (v_vectype : vectype) (var_0 : vec_) :
    wf_uN (vsize v_vectype) var_0 →
    wf_instr (instr.VCONST v_vectype var_0)
  | instr_case_83 (v_vectype : vectype) (v_vvunop : vvunop) : wf_instr (instr.VVUNOP v_vectype v_vvunop)
  | instr_case_84 (v_vectype : vectype) (v_vvbinop : vvbinop) : wf_instr (instr.VVBINOP v_vectype v_vvbinop)
  | instr_case_85 (v_vectype : vectype) (v_vvternop : vvternop) : wf_instr (instr.VVTERNOP v_vectype v_vvternop)
  | instr_case_86 (v_vectype : vectype) (v_vvtestop : vvtestop) : wf_instr (instr.VVTESTOP v_vectype v_vvtestop)
  | instr_case_87 (v_shape : shape) (var_0 : vunop_) :
    wf_shape v_shape →
    wf_vunop_ v_shape var_0 →
    wf_instr (instr.VUNOP v_shape var_0)
  | instr_case_88 (v_shape : shape) (var_0 : vbinop_) :
    wf_shape v_shape →
    wf_vbinop_ v_shape var_0 →
    wf_instr (instr.VBINOP v_shape var_0)
  | instr_case_89 (v_shape : shape) (var_0 : vternop_) :
    wf_shape v_shape →
    wf_vternop_ v_shape var_0 →
    wf_instr (instr.VTERNOP v_shape var_0)
  | instr_case_90 (v_shape : shape) (var_0 : vtestop_) :
    wf_shape v_shape →
    wf_vtestop_ v_shape var_0 →
    wf_instr (instr.VTESTOP v_shape var_0)
  | instr_case_91 (v_shape : shape) (var_0 : vrelop_) :
    wf_shape v_shape →
    wf_vrelop_ v_shape var_0 →
    wf_instr (instr.VRELOP v_shape var_0)
  | instr_case_92 (v_ishape : ishape) (var_0 : vshiftop_) :
    wf_ishape v_ishape →
    wf_vshiftop_ v_ishape var_0 →
    wf_instr (instr.VSHIFTOP v_ishape var_0)
  | instr_case_93 (v_ishape : ishape) :
    wf_ishape v_ishape →
    wf_instr (instr.VBITMASK v_ishape)
  | instr_case_94 (v_bshape : bshape) (var_0 : vswizzlop_) :
    wf_bshape v_bshape →
    wf_vswizzlop_ v_bshape var_0 →
    wf_instr (instr.VSWIZZLOP v_bshape var_0)
  | instr_case_95 (v_bshape : bshape) (laneidx_lst : List laneidx) :
    wf_bshape v_bshape →
    Forall (fun v_laneidx_elem => wf_uN 8 v_laneidx_elem) laneidx_lst →
    (dim.mk_dim (List.length laneidx_lst)) = (fun_dim (proj_bshape_0 v_bshape)) →
    wf_instr (instr.VSHUFFLE v_bshape laneidx_lst)
  | instr_case_96 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextunop__) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextunop__ ishape_2 ishape_1 var_0 →
    wf_instr (instr.VEXTUNOP ishape_1 ishape_2 var_0)
  | instr_case_97 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextbinop__) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextbinop__ ishape_2 ishape_1 var_0 →
    wf_instr (instr.VEXTBINOP ishape_1 ishape_2 var_0)
  | instr_case_98 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextternop__) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextternop__ ishape_2 ishape_1 var_0 →
    wf_instr (instr.VEXTTERNOP ishape_1 ishape_2 var_0)
  | instr_case_99 (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) :
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    ((lsize (fun_lanetype (proj_ishape_0 ishape_2))) = (2 * (lsize (fun_lanetype (proj_ishape_0 ishape_1))))) ∧ ((2 * (lsize (fun_lanetype (proj_ishape_0 ishape_1)))) ≤ 32) →
    wf_instr (instr.VNARROW ishape_1 ishape_2 v_sx)
  | instr_case_100 (shape_1 : shape) (shape_2 : shape) (var_0 : vcvtop__) :
    wf_shape shape_1 →
    wf_shape shape_2 →
    wf_vcvtop__ shape_2 shape_1 var_0 →
    wf_instr (instr.VCVTOP shape_1 shape_2 var_0)
  | instr_case_101 (v_shape : shape) :
    wf_shape v_shape →
    wf_instr (instr.VSPLAT v_shape)
  | instr_case_102 (v_shape : shape) (sx_opt : Option sx) (v_laneidx : laneidx) :
    wf_shape v_shape →
    wf_uN 8 v_laneidx →
    (List.length [lanetype.I32, lanetype.I64, lanetype.F32, lanetype.F64]) > 0 →
    ((sx_opt = none) ↔ (List.contains [lanetype.I32, lanetype.I64, lanetype.F32, lanetype.F64] (fun_lanetype v_shape))) →
    wf_instr (instr.VEXTRACT_LANE v_shape sx_opt v_laneidx)
  | instr_case_103 (v_shape : shape) (v_laneidx : laneidx) :
    wf_shape v_shape →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VREPLACE_LANE v_shape v_laneidx)
  | instr_case_104 (v_u31 : u31) :
    wf_uN 31 v_u31 →
    wf_instr (instr.REF_I31_NUM v_u31)
  | instr_case_105 : wf_instr instr.REF_NULL_ADDR
  | instr_case_106 (v_structaddr : structaddr) : wf_instr (instr.REF_STRUCT_ADDR v_structaddr)
  | instr_case_107 (v_arrayaddr : arrayaddr) : wf_instr (instr.REF_ARRAY_ADDR v_arrayaddr)
  | instr_case_108 (v_funcaddr : funcaddr) : wf_instr (instr.REF_FUNC_ADDR v_funcaddr)
  | instr_case_109 (v_exnaddr : exnaddr) : wf_instr (instr.REF_EXN_ADDR v_exnaddr)
  | instr_case_110 (v_hostaddr : hostaddr) : wf_instr (instr.REF_HOST_ADDR v_hostaddr)
  | instr_case_111 (v_ref : ref) :
    wf_ref v_ref →
    wf_instr (instr.REF_EXTERN v_ref)
  | instr_case_112 (v_n : n) (instr_lst : List instr) (instr_lst_0_lst : List instr) :
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    Forall (fun instr_lst_0_elem => wf_instr instr_lst_0_elem) instr_lst_0_lst →
    wf_instr (instr.LABEL_ v_n instr_lst instr_lst_0_lst)
  | instr_case_113 (v_n : n) (v_frame : frame) (instr_lst : List instr) :
    wf_frame v_frame →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.FRAME_ v_n v_frame instr_lst)
  | instr_case_114 (v_n : n) (catch_lst : List «catch») (instr_lst : List instr) :
    Forall (fun v_catch_elem => wf_catch v_catch_elem) catch_lst →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.HANDLER_ v_n catch_lst instr_lst)
  | instr_case_115 : wf_instr instr.TRAP


abbrev expr : Type := List instr

def memarg0 : memarg :=
  {
    ALIGN := uN.mk_uN 0
    OFFSET := uN.mk_uN 0 : memarg
  }

inductive memarg0_is_wf : memarg → Prop where
  | memarg0_is_wf_0 (ret_val : memarg) :
    ret_val = memarg0 →
    wf_memarg ret_val →
    memarg0_is_wf ret_val


def const (v_consttype : consttype) (v_lit_ : lit_) : instr :=
  match v_consttype, v_lit_ with
  | consttype.I32, lit_.mk_lit__0 numtype.I32 c => instr.CONST numtype.I32 c
  | consttype.I64, lit_.mk_lit__0 numtype.I64 c => instr.CONST numtype.I64 c
  | consttype.F32, lit_.mk_lit__0 numtype.F32 c => instr.CONST numtype.F32 c
  | consttype.F64, lit_.mk_lit__0 numtype.F64 c => instr.CONST numtype.F64 c
  | consttype.V128, lit_.mk_lit__1 vectype.V128 c => instr.VCONST vectype.V128 c
  | _, _ => Inhabited.default

inductive const_is_wf : consttype → lit_ → instr → Prop where
  | const_is_wf_0 (v_consttype : consttype) (v_lit_ : lit_) (ret_val : instr) :
    wf_lit_ (storagetype_consttype v_consttype) v_lit_ →
    ret_val = (const v_consttype v_lit_) →
    wf_instr ret_val →
    const_is_wf v_consttype v_lit_ ret_val


def free_shape (v_shape : shape) : free :=
  match v_shape with
  | shape.X v_lanetype v_dim => free_lanetype v_lanetype

inductive free_shape_is_wf : shape → free → Prop where
  | free_shape_is_wf_0 (v_shape : shape) (ret_val : free) :
    wf_shape v_shape →
    ret_val = (free_shape v_shape) →
    wf_free ret_val →
    free_shape_is_wf v_shape ret_val


inductive fun_free_blocktype : blocktype → free → Prop where
  | fun_free_blocktype_case_0 (valtype_opt : Option valtype) (var_0_opt : Option free) :
    ((var_0_opt = none) ↔ (valtype_opt = none)) →
    Forall₂ (fun var_0_elem v_valtype_elem => fun_free_valtype v_valtype_elem var_0_elem) (Option.toList var_0_opt) (Option.toList valtype_opt) →
    fun_free_blocktype (blocktype._RESULT valtype_opt) (free_opt var_0_opt)
  | fun_free_blocktype_case_1 (v_typeidx : uN) : fun_free_blocktype (blocktype._IDX v_typeidx) (free_typeidx v_typeidx)


inductive free_blocktype_is_wf : blocktype → free → Prop where
  | free_blocktype_is_wf_0 (v_blocktype : blocktype) (ret_val : free) (var_0 : free) :
    fun_free_blocktype v_blocktype var_0 →
    wf_blocktype v_blocktype →
    ret_val = var_0 →
    wf_free ret_val →
    free_blocktype_is_wf v_blocktype ret_val


def free_catch (v_catch : «catch») : free :=
  match v_catch with
  | catch.CATCH v_tagidx v_labelidx => (free_tagidx v_tagidx) ++ (free_labelidx v_labelidx)
  | catch.CATCH_REF v_tagidx v_labelidx => (free_tagidx v_tagidx) ++ (free_labelidx v_labelidx)
  | catch.CATCH_ALL v_labelidx => free_labelidx v_labelidx
  | catch.CATCH_ALL_REF v_labelidx => free_labelidx v_labelidx

inductive free_catch_is_wf : «catch» → free → Prop where
  | free_catch_is_wf_0 (v_catch : «catch») (ret_val : free) :
    wf_catch v_catch →
    ret_val = (free_catch v_catch) →
    wf_free ret_val →
    free_catch_is_wf v_catch ret_val


inductive fun_shift_labelidxs : List labelidx → List labelidx → Prop where
  | fun_shift_labelidxs_case_0 : fun_shift_labelidxs [] []
  | fun_shift_labelidxs_case_1 (labelidx'_lst : List labelidx) (var_0 : List labelidx) :
    fun_shift_labelidxs labelidx'_lst var_0 →
    fun_shift_labelidxs ([uN.mk_uN 0] ++ labelidx'_lst) var_0
  | fun_shift_labelidxs_case_2 (v_labelidx : uN) (labelidx'_lst : List labelidx) (var_0 : List labelidx) :
    fun_shift_labelidxs labelidx'_lst var_0 →
    fun_shift_labelidxs ([v_labelidx] ++ labelidx'_lst) ([uN.mk_uN (Int.toNat (((proj_uN_0 v_labelidx) : Int) - (1 : Int)))] ++ var_0)


inductive shift_labelidxs_is_wf : List labelidx → List labelidx → Prop where
  | shift_labelidxs_is_wf_0 (var_0_lst : List labelidx) (ret_val_lst : List labelidx) (var_0 : List labelidx) :
    fun_shift_labelidxs var_0_lst var_0 →
    Forall (fun var_0_elem => wf_uN 32 var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    shift_labelidxs_is_wf var_0_lst ret_val_lst


mutual
inductive fun_free_instr : instr → free → Prop where
  | fun_free_instr_case_0 : fun_free_instr instr.NOP ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_1 : fun_free_instr instr.UNREACHABLE ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_2 : fun_free_instr instr.DROP ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_3 (valtype_lst_opt : Option (List valtype)) (var_1_lst_opt : Option (List free)) (var_0_opt : Option free) :
    ((var_1_lst_opt = none) ↔ (valtype_lst_opt = none)) →
    Forall₂ (fun var_1_lst_elem valtype_lst_elem => (List.length var_1_lst_elem) = (List.length valtype_lst_elem)) (Option.toList var_1_lst_opt) (Option.toList valtype_lst_opt) →
    Forall₂ (fun var_1_lst_elem valtype_lst_elem => Forall₂ (fun var_1_elem v_valtype_elem => fun_free_valtype v_valtype_elem var_1_elem) var_1_lst_elem valtype_lst_elem) (Option.toList var_1_lst_opt) (Option.toList valtype_lst_opt) →
    ((var_1_lst_opt = none) ↔ (var_0_opt = none)) →
    Forall₂ (fun var_1_lst_elem var_0_elem => fun_free_list var_1_lst_elem var_0_elem) (Option.toList var_1_lst_opt) (Option.toList var_0_opt) →
    fun_free_instr (instr.SELECT valtype_lst_opt) (free_opt var_0_opt)
  | fun_free_instr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) (var_1 : free) (var_0 : free) :
    fun_free_block instr_lst var_1 →
    fun_free_blocktype v_blocktype var_0 →
    fun_free_instr (instr.BLOCK v_blocktype instr_lst) (var_0 ++ var_1)
  | fun_free_instr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) (var_1 : free) (var_0 : free) :
    fun_free_block instr_lst var_1 →
    fun_free_blocktype v_blocktype var_0 →
    fun_free_instr (instr.LOOP v_blocktype instr_lst) (var_0 ++ var_1)
  | fun_free_instr_case_6 (v_blocktype : blocktype) (instr_1_lst : List instr) (instr_2_lst : List instr) (var_2 : free) (var_1 : free) (var_0 : free) :
    fun_free_block instr_2_lst var_2 →
    fun_free_block instr_1_lst var_1 →
    fun_free_blocktype v_blocktype var_0 →
    fun_free_instr (instr.IFELSE v_blocktype instr_1_lst instr_2_lst) ((var_0 ++ var_1) ++ var_2)
  | fun_free_instr_case_7 (v_labelidx : uN) : fun_free_instr (instr.BR v_labelidx) (free_labelidx v_labelidx)
  | fun_free_instr_case_8 (v_labelidx : uN) : fun_free_instr (instr.BR_IF v_labelidx) (free_labelidx v_labelidx)
  | fun_free_instr_case_9 (labelidx_lst : List labelidx) (labelidx' : uN) (var_0 : free) :
    fun_free_list (Map (fun v_labelidx_elem => free_labelidx v_labelidx_elem) labelidx_lst) var_0 →
    fun_free_instr (instr.BR_TABLE labelidx_lst labelidx') (var_0 ++ (free_labelidx labelidx'))
  | fun_free_instr_case_10 (v_labelidx : uN) : fun_free_instr (instr.BR_ON_NULL v_labelidx) (free_labelidx v_labelidx)
  | fun_free_instr_case_11 (v_labelidx : uN) : fun_free_instr (instr.BR_ON_NON_NULL v_labelidx) (free_labelidx v_labelidx)
  | fun_free_instr_case_12 (v_labelidx : uN) (reftype_1 : reftype) (reftype_2 : reftype) (var_1 : free) (var_0 : free) :
    fun_free_reftype reftype_2 var_1 →
    fun_free_reftype reftype_1 var_0 →
    fun_free_instr (instr.BR_ON_CAST v_labelidx reftype_1 reftype_2) (((free_labelidx v_labelidx) ++ var_0) ++ var_1)
  | fun_free_instr_case_13 (v_labelidx : uN) (reftype_1 : reftype) (reftype_2 : reftype) (var_1 : free) (var_0 : free) :
    fun_free_reftype reftype_2 var_1 →
    fun_free_reftype reftype_1 var_0 →
    fun_free_instr (instr.BR_ON_CAST_FAIL v_labelidx reftype_1 reftype_2) (((free_labelidx v_labelidx) ++ var_0) ++ var_1)
  | fun_free_instr_case_14 (v_funcidx : uN) : fun_free_instr (instr.CALL v_funcidx) (free_funcidx v_funcidx)
  | fun_free_instr_case_15 (v_typeuse : typeuse) (var_0 : free) :
    fun_free_typeuse v_typeuse var_0 →
    fun_free_instr (instr.CALL_REF v_typeuse) var_0
  | fun_free_instr_case_16 (v_tableidx : uN) (v_typeuse : typeuse) (var_0 : free) :
    fun_free_typeuse v_typeuse var_0 →
    fun_free_instr (instr.CALL_INDIRECT v_tableidx v_typeuse) ((free_tableidx v_tableidx) ++ var_0)
  | fun_free_instr_case_17 : fun_free_instr instr.RETURN ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_18 (v_funcidx : uN) : fun_free_instr (instr.RETURN_CALL v_funcidx) (free_funcidx v_funcidx)
  | fun_free_instr_case_19 (v_typeuse : typeuse) (var_0 : free) :
    fun_free_typeuse v_typeuse var_0 →
    fun_free_instr (instr.RETURN_CALL_REF v_typeuse) var_0
  | fun_free_instr_case_20 (v_tableidx : uN) (v_typeuse : typeuse) (var_0 : free) :
    fun_free_typeuse v_typeuse var_0 →
    fun_free_instr (instr.RETURN_CALL_INDIRECT v_tableidx v_typeuse) ((free_tableidx v_tableidx) ++ var_0)
  | fun_free_instr_case_21 (v_tagidx : uN) : fun_free_instr (instr.THROW v_tagidx) (free_tagidx v_tagidx)
  | fun_free_instr_case_22 : fun_free_instr instr.THROW_REF ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_23 (v_blocktype : blocktype) (catch_lst : List «catch») (instr_lst : List instr) (var_3_lst : List free) (var_2 : free) (var_1 : free) (var_0 : free) :
    (List.length var_3_lst) = (List.length instr_lst) →
    Forall₂ (fun var_3_elem v_instr_elem => fun_free_instr v_instr_elem var_3_elem) var_3_lst instr_lst →
    fun_free_list var_3_lst var_2 →
    fun_free_list (Map (fun v_catch_elem => free_catch v_catch_elem) catch_lst) var_1 →
    fun_free_blocktype v_blocktype var_0 →
    fun_free_instr (instr.TRY_TABLE v_blocktype (list.mk_list catch_lst) instr_lst) ((var_0 ++ var_1) ++ var_2)
  | fun_free_instr_case_24 (v_numtype : numtype) (numlit : num_) : fun_free_instr (instr.CONST v_numtype numlit) (free_numtype v_numtype)
  | fun_free_instr_case_25 (v_numtype : numtype) (unop : unop_) : fun_free_instr (instr.UNOP v_numtype unop) (free_numtype v_numtype)
  | fun_free_instr_case_26 (v_numtype : numtype) (binop : binop_) : fun_free_instr (instr.BINOP v_numtype binop) (free_numtype v_numtype)
  | fun_free_instr_case_27 (v_numtype : numtype) (testop : testop_) : fun_free_instr (instr.TESTOP v_numtype testop) (free_numtype v_numtype)
  | fun_free_instr_case_28 (v_numtype : numtype) (relop : relop_) : fun_free_instr (instr.RELOP v_numtype relop) (free_numtype v_numtype)
  | fun_free_instr_case_29 (numtype_1 : numtype) (numtype_2 : numtype) (cvtop : cvtop__) : fun_free_instr (instr.CVTOP numtype_1 numtype_2 cvtop) ((free_numtype numtype_1) ++ (free_numtype numtype_2))
  | fun_free_instr_case_30 (v_vectype : vectype) (veclit : uN) : fun_free_instr (instr.VCONST v_vectype veclit) (free_vectype v_vectype)
  | fun_free_instr_case_31 (v_vectype : vectype) (v_vvunop : vvunop) : fun_free_instr (instr.VVUNOP v_vectype v_vvunop) (free_vectype v_vectype)
  | fun_free_instr_case_32 (v_vectype : vectype) (v_vvbinop : vvbinop) : fun_free_instr (instr.VVBINOP v_vectype v_vvbinop) (free_vectype v_vectype)
  | fun_free_instr_case_33 (v_vectype : vectype) (v_vvternop : vvternop) : fun_free_instr (instr.VVTERNOP v_vectype v_vvternop) (free_vectype v_vectype)
  | fun_free_instr_case_34 (v_vectype : vectype) (v_vvtestop : vvtestop) : fun_free_instr (instr.VVTESTOP v_vectype v_vvtestop) (free_vectype v_vectype)
  | fun_free_instr_case_35 (v_shape : shape) (vunop : vunop_) : fun_free_instr (instr.VUNOP v_shape vunop) (free_shape v_shape)
  | fun_free_instr_case_36 (v_shape : shape) (vbinop : vbinop_) : fun_free_instr (instr.VBINOP v_shape vbinop) (free_shape v_shape)
  | fun_free_instr_case_37 (v_shape : shape) (vternop : vternop_) : fun_free_instr (instr.VTERNOP v_shape vternop) (free_shape v_shape)
  | fun_free_instr_case_38 (v_shape : shape) (vtestop : vtestop_) : fun_free_instr (instr.VTESTOP v_shape vtestop) (free_shape v_shape)
  | fun_free_instr_case_39 (v_shape : shape) (vrelop : vrelop_) : fun_free_instr (instr.VRELOP v_shape vrelop) (free_shape v_shape)
  | fun_free_instr_case_40 (v_ishape : ishape) (vshiftop : vshiftop_) : fun_free_instr (instr.VSHIFTOP v_ishape vshiftop) (free_shape (proj_ishape_0 v_ishape))
  | fun_free_instr_case_41 (v_ishape : ishape) : fun_free_instr (instr.VBITMASK v_ishape) (free_shape (proj_ishape_0 v_ishape))
  | fun_free_instr_case_42 (v_bshape : bshape) (vswizzlop : vswizzlop_) : fun_free_instr (instr.VSWIZZLOP v_bshape vswizzlop) (free_shape (proj_bshape_0 v_bshape))
  | fun_free_instr_case_43 (v_bshape : bshape) (laneidx_lst : List laneidx) : fun_free_instr (instr.VSHUFFLE v_bshape laneidx_lst) (free_shape (proj_bshape_0 v_bshape))
  | fun_free_instr_case_44 (ishape_1 : ishape) (ishape_2 : ishape) (vextunop : vextunop__) : fun_free_instr (instr.VEXTUNOP ishape_1 ishape_2 vextunop) ((free_shape (proj_ishape_0 ishape_1)) ++ (free_shape (proj_ishape_0 ishape_2)))
  | fun_free_instr_case_45 (ishape_1 : ishape) (ishape_2 : ishape) (vextbinop : vextbinop__) : fun_free_instr (instr.VEXTBINOP ishape_1 ishape_2 vextbinop) ((free_shape (proj_ishape_0 ishape_1)) ++ (free_shape (proj_ishape_0 ishape_2)))
  | fun_free_instr_case_46 (ishape_1 : ishape) (ishape_2 : ishape) (vextternop : vextternop__) : fun_free_instr (instr.VEXTTERNOP ishape_1 ishape_2 vextternop) ((free_shape (proj_ishape_0 ishape_1)) ++ (free_shape (proj_ishape_0 ishape_2)))
  | fun_free_instr_case_47 (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : fun_free_instr (instr.VNARROW ishape_1 ishape_2 v_sx) ((free_shape (proj_ishape_0 ishape_1)) ++ (free_shape (proj_ishape_0 ishape_2)))
  | fun_free_instr_case_48 (shape_1 : shape) (shape_2 : shape) (vcvtop : vcvtop__) : fun_free_instr (instr.VCVTOP shape_1 shape_2 vcvtop) ((free_shape shape_1) ++ (free_shape shape_2))
  | fun_free_instr_case_49 (v_shape : shape) : fun_free_instr (instr.VSPLAT v_shape) (free_shape v_shape)
  | fun_free_instr_case_50 (v_shape : shape) (sx_opt : Option sx) (v_laneidx : uN) : fun_free_instr (instr.VEXTRACT_LANE v_shape sx_opt v_laneidx) (free_shape v_shape)
  | fun_free_instr_case_51 (v_shape : shape) (v_laneidx : uN) : fun_free_instr (instr.VREPLACE_LANE v_shape v_laneidx) (free_shape v_shape)
  | fun_free_instr_case_52 (v_heaptype : heaptype) (var_0 : free) :
    fun_free_heaptype v_heaptype var_0 →
    fun_free_instr (instr.REF_NULL v_heaptype) var_0
  | fun_free_instr_case_53 : fun_free_instr instr.REF_IS_NULL ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_54 : fun_free_instr instr.REF_AS_NON_NULL ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_55 : fun_free_instr instr.REF_EQ ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_56 (v_reftype : reftype) (var_0 : free) :
    fun_free_reftype v_reftype var_0 →
    fun_free_instr (instr.REF_TEST v_reftype) var_0
  | fun_free_instr_case_57 (v_reftype : reftype) (var_0 : free) :
    fun_free_reftype v_reftype var_0 →
    fun_free_instr (instr.REF_CAST v_reftype) var_0
  | fun_free_instr_case_58 (v_funcidx : uN) : fun_free_instr (instr.REF_FUNC v_funcidx) (free_funcidx v_funcidx)
  | fun_free_instr_case_59 : fun_free_instr instr.REF_I31 ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_60 (v_sx : sx) : fun_free_instr (instr.I31_GET v_sx) ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_61 (v_typeidx : uN) : fun_free_instr (instr.STRUCT_NEW v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_62 (v_typeidx : uN) : fun_free_instr (instr.STRUCT_NEW_DEFAULT v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_63 (sx_opt : Option sx) (v_typeidx : uN) (v_u32 : uN) : fun_free_instr (instr.STRUCT_GET sx_opt v_typeidx v_u32) (free_typeidx v_typeidx)
  | fun_free_instr_case_64 (v_typeidx : uN) (v_u32 : uN) : fun_free_instr (instr.STRUCT_SET v_typeidx v_u32) (free_typeidx v_typeidx)
  | fun_free_instr_case_65 (v_typeidx : uN) : fun_free_instr (instr.ARRAY_NEW v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_66 (v_typeidx : uN) : fun_free_instr (instr.ARRAY_NEW_DEFAULT v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_67 (v_typeidx : uN) (v_u32 : uN) : fun_free_instr (instr.ARRAY_NEW_FIXED v_typeidx v_u32) (free_typeidx v_typeidx)
  | fun_free_instr_case_68 (v_typeidx : uN) (v_dataidx : uN) : fun_free_instr (instr.ARRAY_NEW_DATA v_typeidx v_dataidx) ((free_typeidx v_typeidx) ++ (free_dataidx v_dataidx))
  | fun_free_instr_case_69 (v_typeidx : uN) (v_elemidx : uN) : fun_free_instr (instr.ARRAY_NEW_ELEM v_typeidx v_elemidx) ((free_typeidx v_typeidx) ++ (free_elemidx v_elemidx))
  | fun_free_instr_case_70 (sx_opt : Option sx) (v_typeidx : uN) : fun_free_instr (instr.ARRAY_GET sx_opt v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_71 (v_typeidx : uN) : fun_free_instr (instr.ARRAY_SET v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_72 : fun_free_instr instr.ARRAY_LEN ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_73 (v_typeidx : uN) : fun_free_instr (instr.ARRAY_FILL v_typeidx) (free_typeidx v_typeidx)
  | fun_free_instr_case_74 (typeidx_1 : uN) (typeidx_2 : uN) : fun_free_instr (instr.ARRAY_COPY typeidx_1 typeidx_2) ((free_typeidx typeidx_1) ++ (free_typeidx typeidx_2))
  | fun_free_instr_case_75 (v_typeidx : uN) (v_dataidx : uN) : fun_free_instr (instr.ARRAY_INIT_DATA v_typeidx v_dataidx) ((free_typeidx v_typeidx) ++ (free_dataidx v_dataidx))
  | fun_free_instr_case_76 (v_typeidx : uN) (v_elemidx : uN) : fun_free_instr (instr.ARRAY_INIT_ELEM v_typeidx v_elemidx) ((free_typeidx v_typeidx) ++ (free_elemidx v_elemidx))
  | fun_free_instr_case_77 : fun_free_instr instr.EXTERN_CONVERT_ANY ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_78 : fun_free_instr instr.ANY_CONVERT_EXTERN ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_instr_case_79 (v_localidx : uN) : fun_free_instr (instr.LOCAL_GET v_localidx) (free_localidx v_localidx)
  | fun_free_instr_case_80 (v_localidx : uN) : fun_free_instr (instr.LOCAL_SET v_localidx) (free_localidx v_localidx)
  | fun_free_instr_case_81 (v_localidx : uN) : fun_free_instr (instr.LOCAL_TEE v_localidx) (free_localidx v_localidx)
  | fun_free_instr_case_82 (v_globalidx : uN) : fun_free_instr (instr.GLOBAL_GET v_globalidx) (free_globalidx v_globalidx)
  | fun_free_instr_case_83 (v_globalidx : uN) : fun_free_instr (instr.GLOBAL_SET v_globalidx) (free_globalidx v_globalidx)
  | fun_free_instr_case_84 (v_tableidx : uN) : fun_free_instr (instr.TABLE_GET v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_85 (v_tableidx : uN) : fun_free_instr (instr.TABLE_SET v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_86 (v_tableidx : uN) : fun_free_instr (instr.TABLE_SIZE v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_87 (v_tableidx : uN) : fun_free_instr (instr.TABLE_GROW v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_88 (v_tableidx : uN) : fun_free_instr (instr.TABLE_FILL v_tableidx) (free_tableidx v_tableidx)
  | fun_free_instr_case_89 (tableidx_1 : uN) (tableidx_2 : uN) : fun_free_instr (instr.TABLE_COPY tableidx_1 tableidx_2) ((free_tableidx tableidx_1) ++ (free_tableidx tableidx_2))
  | fun_free_instr_case_90 (v_tableidx : uN) (v_elemidx : uN) : fun_free_instr (instr.TABLE_INIT v_tableidx v_elemidx) ((free_tableidx v_tableidx) ++ (free_elemidx v_elemidx))
  | fun_free_instr_case_91 (v_elemidx : uN) : fun_free_instr (instr.ELEM_DROP v_elemidx) (free_elemidx v_elemidx)
  | fun_free_instr_case_92 (v_numtype : numtype) (loadop_opt : Option loadop_) (v_memidx : uN) (v_memarg : memarg) : fun_free_instr (instr.LOAD v_numtype loadop_opt v_memidx v_memarg) ((free_numtype v_numtype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_93 (v_numtype : numtype) (storeop_opt : Option storeop_) (v_memidx : uN) (v_memarg : memarg) : fun_free_instr (instr.STORE v_numtype storeop_opt v_memidx v_memarg) ((free_numtype v_numtype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_94 (v_vectype : vectype) (vloadop_opt : Option vloadop_) (v_memidx : uN) (v_memarg : memarg) : fun_free_instr (instr.VLOAD v_vectype vloadop_opt v_memidx v_memarg) ((free_vectype v_vectype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_95 (v_vectype : vectype) (v_sz : sz) (v_memidx : uN) (v_memarg : memarg) (v_laneidx : uN) : fun_free_instr (instr.VLOAD_LANE v_vectype v_sz v_memidx v_memarg v_laneidx) ((free_vectype v_vectype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_96 (v_vectype : vectype) (v_memidx : uN) (v_memarg : memarg) : fun_free_instr (instr.VSTORE v_vectype v_memidx v_memarg) ((free_vectype v_vectype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_97 (v_vectype : vectype) (v_sz : sz) (v_memidx : uN) (v_memarg : memarg) (v_laneidx : uN) : fun_free_instr (instr.VSTORE_LANE v_vectype v_sz v_memidx v_memarg v_laneidx) ((free_vectype v_vectype) ++ (free_memidx v_memidx))
  | fun_free_instr_case_98 (v_memidx : uN) : fun_free_instr (instr.MEMORY_SIZE v_memidx) (free_memidx v_memidx)
  | fun_free_instr_case_99 (v_memidx : uN) : fun_free_instr (instr.MEMORY_GROW v_memidx) (free_memidx v_memidx)
  | fun_free_instr_case_100 (v_memidx : uN) : fun_free_instr (instr.MEMORY_FILL v_memidx) (free_memidx v_memidx)
  | fun_free_instr_case_101 (memidx_1 : uN) (memidx_2 : uN) : fun_free_instr (instr.MEMORY_COPY memidx_1 memidx_2) ((free_memidx memidx_1) ++ (free_memidx memidx_2))
  | fun_free_instr_case_102 (v_memidx : uN) (v_dataidx : uN) : fun_free_instr (instr.MEMORY_INIT v_memidx v_dataidx) ((free_memidx v_memidx) ++ (free_dataidx v_dataidx))
  | fun_free_instr_case_103 (v_dataidx : uN) : fun_free_instr (instr.DATA_DROP v_dataidx) (free_dataidx v_dataidx)

inductive fun_free_block : List instr → free → Prop where
  | fun_free_block_case_0 (instr_lst : List instr) (v_free : free) (var_2_lst : List free) (var_1 : free) (var_0 : List labelidx) :
    (List.length var_2_lst) = (List.length instr_lst) →
    Forall₂ (fun var_2_elem instr_5_elem => fun_free_instr instr_5_elem var_2_elem) var_2_lst instr_lst →
    fun_free_list var_2_lst var_1 →
    fun_shift_labelidxs (v_free.LABELS) var_0 →
    v_free = var_1 →
    fun_free_block instr_lst ({
      v_free with
      LABELS := var_0
    })


end

mutual
inductive free_instr_is_wf : instr → free → Prop where
  | free_instr_is_wf_0 (v_instr : instr) (ret_val : free) (var_0 : free) :
    fun_free_instr v_instr var_0 →
    wf_instr v_instr →
    ret_val = var_0 →
    wf_free ret_val →
    free_instr_is_wf v_instr ret_val

inductive free_block_is_wf : List instr → free → Prop where
  | free_block_is_wf_0 (var_0_lst : List instr) (ret_val : free) (var_0 : free) :
    fun_free_block var_0_lst var_0 →
    Forall (fun var_0_elem => wf_instr var_0_elem) var_0_lst →
    ret_val = var_0 →
    wf_free ret_val →
    free_block_is_wf var_0_lst ret_val


end

inductive fun_free_expr : expr → free → Prop where
  | fun_free_expr_case_0 (instr_lst : List instr) (var_1_lst : List free) (var_0 : free) :
    (List.length var_1_lst) = (List.length instr_lst) →
    Forall₂ (fun var_1_elem v_instr_elem => fun_free_instr v_instr_elem var_1_elem) var_1_lst instr_lst →
    fun_free_list var_1_lst var_0 →
    fun_free_expr instr_lst var_0


inductive free_expr_is_wf : expr → free → Prop where
  | free_expr_is_wf_0 (v_expr : expr) (ret_val : free) (var_0 : free) :
    fun_free_expr v_expr var_0 →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    ret_val = var_0 →
    wf_free ret_val →
    free_expr_is_wf v_expr ret_val


inductive elemmode : Type where
  | ACTIVE (v_tableidx : tableidx) (v_expr : expr) : elemmode
  | PASSIVE : elemmode
  | DECLARE : elemmode
deriving Inhabited, BEq

inductive wf_elemmode : elemmode → Prop where
  | elemmode_case_0 (v_tableidx : tableidx) (v_expr : expr) :
    wf_uN 32 v_tableidx →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_elemmode (elemmode.ACTIVE v_tableidx v_expr)
  | elemmode_case_1 : wf_elemmode elemmode.PASSIVE
  | elemmode_case_2 : wf_elemmode elemmode.DECLARE


inductive datamode : Type where
  | ACTIVE (v_memidx : memidx) (v_expr : expr) : datamode
  | PASSIVE : datamode
deriving Inhabited, BEq

inductive wf_datamode : datamode → Prop where
  | datamode_case_0 (v_memidx : memidx) (v_expr : expr) :
    wf_uN 32 v_memidx →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_datamode (datamode.ACTIVE v_memidx v_expr)
  | datamode_case_1 : wf_datamode datamode.PASSIVE


inductive type : Type where
  | TYPE (v_rectype : rectype) : type
deriving Inhabited, BEq

inductive tag : Type where
  | TAG (v_tagtype : tagtype) : tag
deriving Inhabited, BEq

inductive wf_tag : tag → Prop where
  | tag_case_0 (v_tagtype : tagtype) :
    wf_typeuse v_tagtype →
    wf_tag (tag.TAG v_tagtype)


inductive global : Type where
  | GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global
deriving Inhabited, BEq

inductive wf_global : global → Prop where
  | global_case_0 (v_globaltype : globaltype) (v_expr : expr) :
    wf_globaltype v_globaltype →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_global (global.GLOBAL v_globaltype v_expr)


inductive mem : Type where
  | MEMORY (v_memtype : memtype) : mem
deriving Inhabited, BEq

inductive wf_mem : mem → Prop where
  | mem_case_0 (v_memtype : memtype) :
    wf_memtype v_memtype →
    wf_mem (mem.MEMORY v_memtype)


inductive table : Type where
  | TABLE (v_tabletype : tabletype) (v_expr : expr) : table
deriving Inhabited, BEq

inductive wf_table : table → Prop where
  | table_case_0 (v_tabletype : tabletype) (v_expr : expr) :
    wf_tabletype v_tabletype →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_table (table.TABLE v_tabletype v_expr)


inductive data : Type where
  | DATA (byte_lst : List byte) (v_datamode : datamode) : data
deriving Inhabited, BEq

inductive wf_data : data → Prop where
  | data_case_0 (byte_lst : List byte) (v_datamode : datamode) :
    Forall (fun v_byte_elem => wf_byte v_byte_elem) byte_lst →
    wf_datamode v_datamode →
    wf_data (data.DATA byte_lst v_datamode)


inductive «local» : Type where
  | LOCAL (v_valtype : valtype) : «local»
deriving Inhabited, BEq

inductive wf_local : «local» → Prop where
  | local_case_0 (v_valtype : valtype) :
    wf_valtype v_valtype →
    wf_local (local.LOCAL v_valtype)


inductive func : Type where
  | FUNC (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) : func
deriving Inhabited, BEq

inductive wf_func : func → Prop where
  | func_case_0 (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) :
    wf_uN 32 v_typeidx →
    Forall (fun v_local_elem => wf_local v_local_elem) local_lst →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_func (func.FUNC v_typeidx local_lst v_expr)


inductive elem : Type where
  | ELEM (v_reftype : reftype) (expr_lst : List expr) (v_elemmode : elemmode) : elem
deriving Inhabited, BEq

inductive wf_elem : elem → Prop where
  | elem_case_0 (v_reftype : reftype) (expr_lst : List expr) (v_elemmode : elemmode) :
    wf_reftype v_reftype →
    Forall (fun v_expr_elem => Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr_elem) expr_lst →
    wf_elemmode v_elemmode →
    wf_elem (elem.ELEM v_reftype expr_lst v_elemmode)


inductive start : Type where
  | START (v_funcidx : funcidx) : start
deriving Inhabited, BEq

inductive wf_start : start → Prop where
  | start_case_0 (v_funcidx : funcidx) :
    wf_uN 32 v_funcidx →
    wf_start (start.START v_funcidx)


inductive «import» : Type where
  | IMPORT (v_name_0 : name) (v_name_1 : name) (v_externtype : externtype) : «import»
deriving Inhabited, BEq

inductive wf_import : «import» → Prop where
  | import_case_0 (v_name : name) (name_0 : name) (v_externtype : externtype) :
    wf_name v_name →
    wf_name name_0 →
    wf_externtype v_externtype →
    wf_import (import.IMPORT v_name name_0 v_externtype)


inductive «export» : Type where
  | EXPORT (v_name : name) (v_externidx : externidx) : «export»
deriving Inhabited, BEq

inductive wf_export : «export» → Prop where
  | export_case_0 (v_name : name) (v_externidx : externidx) :
    wf_name v_name →
    wf_externidx v_externidx →
    wf_export (export.EXPORT v_name v_externidx)


inductive module : Type where
  | MODULE (__0 : list type) (__1 : list «import») (__2 : list tag) (__3 : list global) (__4 : list mem) (__5 : list table) (__6 : list func) (__7 : list data) (__8 : list elem) (start_opt : Option start) (__9 : list «export») : module
deriving Inhabited, BEq

inductive wf_module : module → Prop where
  | module_case_0 (var_0 : list type) (var_1 : list «import») (var_2 : list tag) (var_3 : list global) (var_4 : list mem) (var_5 : list table) (var_6 : list func) (var_7 : list data) (var_8 : list elem) (start_opt : Option start) (var_9 : list «export») :
    Forall (fun v_start_elem => wf_start v_start_elem) (Option.toList start_opt) →
    wf_module (module.MODULE var_0 var_1 var_2 var_3 var_4 var_5 var_6 var_7 var_8 start_opt var_9)


inductive fun_free_type : type → free → Prop where
  | fun_free_type_case_0 (v_rectype : rectype) (var_0 : free) :
    fun_free_rectype v_rectype var_0 →
    fun_free_type (type.TYPE v_rectype) var_0


inductive free_type_is_wf : type → free → Prop where
  | free_type_is_wf_0 (v_type : type) (ret_val : free) (var_0 : free) :
    fun_free_type v_type var_0 →
    ret_val = var_0 →
    wf_free ret_val →
    free_type_is_wf v_type ret_val


inductive fun_free_tag : tag → free → Prop where
  | fun_free_tag_case_0 (v_tagtype : typeuse) (var_0 : free) :
    fun_free_tagtype v_tagtype var_0 →
    fun_free_tag (tag.TAG v_tagtype) var_0


inductive free_tag_is_wf : tag → free → Prop where
  | free_tag_is_wf_0 (v_tag : tag) (ret_val : free) (var_0 : free) :
    fun_free_tag v_tag var_0 →
    wf_tag v_tag →
    ret_val = var_0 →
    wf_free ret_val →
    free_tag_is_wf v_tag ret_val


inductive fun_free_global : global → free → Prop where
  | fun_free_global_case_0 (v_globaltype : globaltype) (v_expr : List instr) (var_1 : free) (var_0 : free) :
    fun_free_expr v_expr var_1 →
    fun_free_globaltype v_globaltype var_0 →
    fun_free_global (global.GLOBAL v_globaltype v_expr) (var_0 ++ var_1)


inductive free_global_is_wf : global → free → Prop where
  | free_global_is_wf_0 (v_global : global) (ret_val : free) (var_0 : free) :
    fun_free_global v_global var_0 →
    wf_global v_global →
    ret_val = var_0 →
    wf_free ret_val →
    free_global_is_wf v_global ret_val


def free_mem (v_mem : mem) : free :=
  match v_mem with
  | mem.MEMORY v_memtype => free_memtype v_memtype

inductive free_mem_is_wf : mem → free → Prop where
  | free_mem_is_wf_0 (v_mem : mem) (ret_val : free) :
    wf_mem v_mem →
    ret_val = (free_mem v_mem) →
    wf_free ret_val →
    free_mem_is_wf v_mem ret_val


inductive fun_free_table : table → free → Prop where
  | fun_free_table_case_0 (v_tabletype : tabletype) (v_expr : List instr) (var_1 : free) (var_0 : free) :
    fun_free_expr v_expr var_1 →
    fun_free_tabletype v_tabletype var_0 →
    fun_free_table (table.TABLE v_tabletype v_expr) (var_0 ++ var_1)


inductive free_table_is_wf : table → free → Prop where
  | free_table_is_wf_0 (v_table : table) (ret_val : free) (var_0 : free) :
    fun_free_table v_table var_0 →
    wf_table v_table →
    ret_val = var_0 →
    wf_free ret_val →
    free_table_is_wf v_table ret_val


inductive fun_free_local : «local» → free → Prop where
  | fun_free_local_case_0 (t : valtype) (var_0 : free) :
    fun_free_valtype t var_0 →
    fun_free_local (local.LOCAL t) var_0


inductive free_local_is_wf : «local» → free → Prop where
  | free_local_is_wf_0 (v_local : «local») (ret_val : free) (var_0 : free) :
    fun_free_local v_local var_0 →
    wf_local v_local →
    ret_val = var_0 →
    wf_free ret_val →
    free_local_is_wf v_local ret_val


inductive fun_free_func : func → free → Prop where
  | fun_free_func_case_0 (v_typeidx : uN) (local_lst : List «local») (v_expr : List instr) (var_2 : free) (var_1_lst : List free) (var_0 : free) :
    fun_free_block v_expr var_2 →
    (List.length var_1_lst) = (List.length local_lst) →
    Forall₂ (fun var_1_elem v_local_elem => fun_free_local v_local_elem var_1_elem) var_1_lst local_lst →
    fun_free_list var_1_lst var_0 →
    fun_free_func (func.FUNC v_typeidx local_lst v_expr) (((free_typeidx v_typeidx) ++ var_0) ++ ({
      var_2 with
      LOCALS := []
    }))


inductive free_func_is_wf : func → free → Prop where
  | free_func_is_wf_0 (v_func : func) (ret_val : free) (var_0 : free) :
    fun_free_func v_func var_0 →
    wf_func v_func →
    ret_val = var_0 →
    wf_free ret_val →
    free_func_is_wf v_func ret_val


inductive fun_free_datamode : datamode → free → Prop where
  | fun_free_datamode_case_0 (v_memidx : uN) (v_expr : List instr) (var_0 : free) :
    fun_free_expr v_expr var_0 →
    fun_free_datamode (datamode.ACTIVE v_memidx v_expr) ((free_memidx v_memidx) ++ var_0)
  | fun_free_datamode_case_1 : fun_free_datamode datamode.PASSIVE ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })


inductive free_datamode_is_wf : datamode → free → Prop where
  | free_datamode_is_wf_0 (v_datamode : datamode) (ret_val : free) (var_0 : free) :
    fun_free_datamode v_datamode var_0 →
    wf_datamode v_datamode →
    ret_val = var_0 →
    wf_free ret_val →
    free_datamode_is_wf v_datamode ret_val


inductive fun_free_data : data → free → Prop where
  | fun_free_data_case_0 (byte_lst : List byte) (v_datamode : datamode) (var_0 : free) :
    fun_free_datamode v_datamode var_0 →
    fun_free_data (data.DATA byte_lst v_datamode) var_0


inductive free_data_is_wf : data → free → Prop where
  | free_data_is_wf_0 (v_data : data) (ret_val : free) (var_0 : free) :
    fun_free_data v_data var_0 →
    wf_data v_data →
    ret_val = var_0 →
    wf_free ret_val →
    free_data_is_wf v_data ret_val


inductive fun_free_elemmode : elemmode → free → Prop where
  | fun_free_elemmode_case_0 (v_tableidx : uN) (v_expr : List instr) (var_0 : free) :
    fun_free_expr v_expr var_0 →
    fun_free_elemmode (elemmode.ACTIVE v_tableidx v_expr) ((free_tableidx v_tableidx) ++ var_0)
  | fun_free_elemmode_case_1 : fun_free_elemmode elemmode.PASSIVE ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })
  | fun_free_elemmode_case_2 : fun_free_elemmode elemmode.DECLARE ({
    TYPES := []
    FUNCS := []
    GLOBALS := []
    TABLES := []
    MEMS := []
    ELEMS := []
    DATAS := []
    LOCALS := []
    LABELS := []
    TAGS := [] : free
  })


inductive free_elemmode_is_wf : elemmode → free → Prop where
  | free_elemmode_is_wf_0 (v_elemmode : elemmode) (ret_val : free) (var_0 : free) :
    fun_free_elemmode v_elemmode var_0 →
    wf_elemmode v_elemmode →
    ret_val = var_0 →
    wf_free ret_val →
    free_elemmode_is_wf v_elemmode ret_val


inductive fun_free_elem : elem → free → Prop where
  | fun_free_elem_case_0 (v_reftype : reftype) (expr_lst : List expr) (v_elemmode : elemmode) (var_3 : free) (var_2_lst : List free) (var_1 : free) (var_0 : free) :
    fun_free_elemmode v_elemmode var_3 →
    (List.length var_2_lst) = (List.length expr_lst) →
    Forall₂ (fun var_2_elem v_expr_elem => fun_free_expr v_expr_elem var_2_elem) var_2_lst expr_lst →
    fun_free_list var_2_lst var_1 →
    fun_free_reftype v_reftype var_0 →
    fun_free_elem (elem.ELEM v_reftype expr_lst v_elemmode) ((var_0 ++ var_1) ++ var_3)


inductive free_elem_is_wf : elem → free → Prop where
  | free_elem_is_wf_0 (v_elem : elem) (ret_val : free) (var_0 : free) :
    fun_free_elem v_elem var_0 →
    wf_elem v_elem →
    ret_val = var_0 →
    wf_free ret_val →
    free_elem_is_wf v_elem ret_val


def free_start (v_start : start) : free :=
  match v_start with
  | start.START v_funcidx => free_funcidx v_funcidx

inductive free_start_is_wf : start → free → Prop where
  | free_start_is_wf_0 (v_start : start) (ret_val : free) :
    wf_start v_start →
    ret_val = (free_start v_start) →
    wf_free ret_val →
    free_start_is_wf v_start ret_val


inductive fun_free_import : «import» → free → Prop where
  | fun_free_import_case_0 (name_1 : name) (name_2 : name) (v_externtype : externtype) (var_0 : free) :
    fun_free_externtype v_externtype var_0 →
    fun_free_import (import.IMPORT name_1 name_2 v_externtype) var_0


inductive free_import_is_wf : «import» → free → Prop where
  | free_import_is_wf_0 (v_import : «import») (ret_val : free) (var_0 : free) :
    fun_free_import v_import var_0 →
    wf_import v_import →
    ret_val = var_0 →
    wf_free ret_val →
    free_import_is_wf v_import ret_val


def free_export (v_export : «export») : free :=
  match v_export with
  | export.EXPORT v_name v_externidx => free_externidx v_externidx

inductive free_export_is_wf : «export» → free → Prop where
  | free_export_is_wf_0 (v_export : «export») (ret_val : free) :
    wf_export v_export →
    ret_val = (free_export v_export) →
    wf_free ret_val →
    free_export_is_wf v_export ret_val


inductive fun_free_module : module → free → Prop where
  | fun_free_module_case_0 (type_lst : List type) (import_lst : List «import») (tag_lst : List tag) (global_lst : List global) (mem_lst : List mem) (table_lst : List table) (func_lst : List func) (data_lst : List data) (elem_lst : List elem) (start_opt : Option start) (export_lst : List «export») (var_17 : free) (var_16_lst : List free) (var_15 : free) (var_14_lst : List free) (var_13 : free) (var_12_lst : List free) (var_11 : free) (var_10_lst : List free) (var_9 : free) (var_8_lst : List free) (var_7 : free) (var_6 : free) (var_5_lst : List free) (var_4 : free) (var_3_lst : List free) (var_2 : free) (var_1_lst : List free) (var_0 : free) :
    fun_free_list (Map (fun v_export_elem => free_export v_export_elem) export_lst) var_17 →
    (List.length var_16_lst) = (List.length import_lst) →
    Forall₂ (fun var_16_elem v_import_elem => fun_free_import v_import_elem var_16_elem) var_16_lst import_lst →
    fun_free_list var_16_lst var_15 →
    (List.length var_14_lst) = (List.length elem_lst) →
    Forall₂ (fun var_14_elem v_elem_elem => fun_free_elem v_elem_elem var_14_elem) var_14_lst elem_lst →
    fun_free_list var_14_lst var_13 →
    (List.length var_12_lst) = (List.length data_lst) →
    Forall₂ (fun var_12_elem v_data_elem => fun_free_data v_data_elem var_12_elem) var_12_lst data_lst →
    fun_free_list var_12_lst var_11 →
    (List.length var_10_lst) = (List.length func_lst) →
    Forall₂ (fun var_10_elem v_func_elem => fun_free_func v_func_elem var_10_elem) var_10_lst func_lst →
    fun_free_list var_10_lst var_9 →
    (List.length var_8_lst) = (List.length table_lst) →
    Forall₂ (fun var_8_elem v_table_elem => fun_free_table v_table_elem var_8_elem) var_8_lst table_lst →
    fun_free_list var_8_lst var_7 →
    fun_free_list (Map (fun v_mem_elem => free_mem v_mem_elem) mem_lst) var_6 →
    (List.length var_5_lst) = (List.length global_lst) →
    Forall₂ (fun var_5_elem v_global_elem => fun_free_global v_global_elem var_5_elem) var_5_lst global_lst →
    fun_free_list var_5_lst var_4 →
    (List.length var_3_lst) = (List.length tag_lst) →
    Forall₂ (fun var_3_elem v_tag_elem => fun_free_tag v_tag_elem var_3_elem) var_3_lst tag_lst →
    fun_free_list var_3_lst var_2 →
    (List.length var_1_lst) = (List.length type_lst) →
    Forall₂ (fun var_1_elem v_type_elem => fun_free_type v_type_elem var_1_elem) var_1_lst type_lst →
    fun_free_list var_1_lst var_0 →
    fun_free_module (module.MODULE (list.mk_list type_lst) (list.mk_list import_lst) (list.mk_list tag_lst) (list.mk_list global_lst) (list.mk_list mem_lst) (list.mk_list table_lst) (list.mk_list func_lst) (list.mk_list data_lst) (list.mk_list elem_lst) start_opt (list.mk_list export_lst)) ((((((((((var_0 ++ var_2) ++ var_4) ++ var_6) ++ var_7) ++ var_9) ++ var_11) ++ var_13) ++ (free_opt (OMap (fun v_start_elem => free_start v_start_elem) start_opt))) ++ var_15) ++ var_17)


inductive free_module_is_wf : module → free → Prop where
  | free_module_is_wf_0 (v_module : module) (ret_val : free) (var_0 : free) :
    fun_free_module v_module var_0 →
    wf_module v_module →
    ret_val = var_0 →
    wf_free ret_val →
    free_module_is_wf v_module ret_val


inductive fun_funcidx_module : module → List funcidx → Prop where
  | fun_funcidx_module_case_0 (v_module : module) (var_0 : free) :
    fun_free_module v_module var_0 →
    fun_funcidx_module v_module (var_0.FUNCS)


inductive funcidx_module_is_wf : module → List funcidx → Prop where
  | funcidx_module_is_wf_0 (v_module : module) (ret_val_lst : List funcidx) (var_0 : List funcidx) :
    fun_funcidx_module v_module var_0 →
    wf_module v_module →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    funcidx_module_is_wf v_module ret_val_lst


inductive fun_dataidx_funcs : List func → List dataidx → Prop where
  | fun_dataidx_funcs_case_0 (func_lst : List func) (var_1_lst : List free) (var_0 : free) :
    (List.length var_1_lst) = (List.length func_lst) →
    Forall₂ (fun var_1_elem v_func_elem => fun_free_func v_func_elem var_1_elem) var_1_lst func_lst →
    fun_free_list var_1_lst var_0 →
    fun_dataidx_funcs func_lst (var_0.DATAS)


inductive dataidx_funcs_is_wf : List func → List dataidx → Prop where
  | dataidx_funcs_is_wf_0 (var_0_lst : List func) (ret_val_lst : List dataidx) (var_0 : List dataidx) :
    fun_dataidx_funcs var_0_lst var_0 →
    Forall (fun var_0_elem => wf_func var_0_elem) var_0_lst →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    dataidx_funcs_is_wf var_0_lst ret_val_lst


inductive init : Type where
  | SET : init
  | UNSET : init
deriving Inhabited, BEq

inductive localtype : Type where
  | mk_localtype (v_init : init) (v_valtype : valtype) : localtype
deriving Inhabited, BEq

inductive wf_localtype : localtype → Prop where
  | localtype_case_0 (v_init : init) (v_valtype : valtype) :
    wf_valtype v_valtype →
    wf_localtype (localtype.mk_localtype v_init v_valtype)


inductive instrtype : Type where
  | mk_instrtype (v_resulttype_0 : resulttype) (localidx_lst : List localidx) (v_resulttype_1 : resulttype) : instrtype
deriving Inhabited, BEq

inductive wf_instrtype : instrtype → Prop where
  | instrtype_case_0 (v_resulttype : resulttype) (localidx_lst : List localidx) (resulttype_0 : resulttype) :
    Forall (fun v_localidx_elem => wf_uN 32 v_localidx_elem) localidx_lst →
    wf_instrtype (instrtype.mk_instrtype v_resulttype localidx_lst resulttype_0)


structure context where
  MKcontext ::
  TYPES : List deftype
  TAGS : List tagtype
  GLOBALS : List globaltype
  MEMS : List memtype
  TABLES : List tabletype
  FUNCS : List deftype
  DATAS : List datatype
  ELEMS : List elemtype
  LOCALS : List localtype
  LABELS : List resulttype
  RETURN : Option resulttype
  REFS : List funcidx
  RECS : List subtype
deriving Inhabited, BEq

def append_context (arg1 arg2 : context) : context where
  TYPES := (arg1.TYPES) ++ (arg2.TYPES)
  TAGS := (arg1.TAGS) ++ (arg2.TAGS)
  GLOBALS := (arg1.GLOBALS) ++ (arg2.GLOBALS)
  MEMS := (arg1.MEMS) ++ (arg2.MEMS)
  TABLES := (arg1.TABLES) ++ (arg2.TABLES)
  FUNCS := (arg1.FUNCS) ++ (arg2.FUNCS)
  DATAS := (arg1.DATAS) ++ (arg2.DATAS)
  ELEMS := (arg1.ELEMS) ++ (arg2.ELEMS)
  LOCALS := (arg1.LOCALS) ++ (arg2.LOCALS)
  LABELS := (arg1.LABELS) ++ (arg2.LABELS)
  RETURN := Option.orElse (arg1.RETURN) (fun _ => arg2.RETURN)
  REFS := (arg1.REFS) ++ (arg2.REFS)
  RECS := (arg1.RECS) ++ (arg2.RECS)

instance  : Append context where
  append := append_context

inductive wf_context : context → Prop where
  | context_case_ (var_0_lst : List deftype) (var_1_lst : List tagtype) (var_2_lst : List globaltype) (var_3_lst : List memtype) (var_4_lst : List tabletype) (var_5_lst : List deftype) (var_6_lst : List datatype) (var_7_lst : List elemtype) (var_8_lst : List localtype) (var_9_lst : List resulttype) (var_10_opt : Option resulttype) (var_11_lst : List funcidx) (var_12_lst : List subtype) :
    Forall (fun var_1_elem => wf_typeuse var_1_elem) var_1_lst →
    Forall (fun var_2_elem => wf_globaltype var_2_elem) var_2_lst →
    Forall (fun var_3_elem => wf_memtype var_3_elem) var_3_lst →
    Forall (fun var_4_elem => wf_tabletype var_4_elem) var_4_lst →
    Forall (fun var_7_elem => wf_reftype var_7_elem) var_7_lst →
    Forall (fun var_8_elem => wf_localtype var_8_elem) var_8_lst →
    Forall (fun var_11_elem => wf_uN 32 var_11_elem) var_11_lst →
    Forall (fun var_12_elem => wf_subtype var_12_elem) var_12_lst →
    wf_context ({
      TYPES := var_0_lst
      TAGS := var_1_lst
      GLOBALS := var_2_lst
      MEMS := var_3_lst
      TABLES := var_4_lst
      FUNCS := var_5_lst
      DATAS := var_6_lst
      ELEMS := var_7_lst
      LOCALS := var_8_lst
      LABELS := var_9_lst
      RETURN := var_10_opt
      REFS := var_11_lst
      RECS := var_12_lst : context
    })


inductive fun_with_locals_before_fun_with_locals_case_2 : context → List localidx → List localtype → Prop where
  | fun_with_locals_case_1 (C : context) (x_1 : uN) (x_lst : List idx) (lct_1 : localtype) (lct_lst : List localtype) (var_0 : Option context) : fun_with_locals_before_fun_with_locals_case_2 C ([x_1] ++ x_lst) ([lct_1] ++ lct_lst)
  | fun_with_locals_case_0 (C : context) : fun_with_locals_before_fun_with_locals_case_2 C [] []


inductive fun_with_locals : context → List localidx → List localtype → Option context → Prop where
  | fun_with_locals_case_0 (C : context) : fun_with_locals C [] [] (some C)
  | fun_with_locals_case_1 (C : context) (x_1 : uN) (x_lst : List idx) (lct_1 : localtype) (lct_lst : List localtype) (var_0 : Option context) :
    fun_with_locals ({
      C with
      LOCALS := List.modify (C.LOCALS) (proj_uN_0 x_1) (fun elem_1 => lct_1)
    }) x_lst lct_lst var_0 →
    fun_with_locals C ([x_1] ++ x_lst) ([lct_1] ++ lct_lst) var_0
  | fun_with_locals_case_2 (x0 : context) (x1 : List localidx) (x2 : List localtype) :
    ¬ fun_with_locals_before_fun_with_locals_case_2 x0 x1 x2 →
    fun_with_locals x0 x1 x2 none


inductive with_locals_is_wf : context → List localidx → List localtype → context → Prop where
  | with_locals_is_wf_0 (v_context : context) (var_0_lst : List localidx) (var_1_lst : List localtype) (ret_val : context) (var_0 : Option context) :
    fun_with_locals v_context var_0_lst var_1_lst var_0 →
    wf_context v_context →
    Forall (fun var_0_elem => wf_uN 32 var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_localtype var_1_elem) var_1_lst →
    var_0 ≠ none →
    ret_val = (Option.get! var_0) →
    wf_context ret_val →
    with_locals_is_wf v_context var_0_lst var_1_lst ret_val


inductive fun_clos_deftypes : List deftype → List deftype → Prop where
  | fun_clos_deftypes_case_0 : fun_clos_deftypes [] []
  | fun_clos_deftypes_case_1 (dt_lst : List deftype) (dt_n : deftype) (dt'_lst : List deftype) (var_1 : List deftype) (var_0 : deftype) :
    fun_clos_deftypes dt_lst var_1 →
    fun_subst_all_deftype dt_n (Map (fun dt'_elem => typeuse_deftype dt'_elem) dt'_lst) var_0 →
    dt'_lst = var_1 →
    fun_clos_deftypes (dt_lst ++ [dt_n]) (dt'_lst ++ [var_0])


inductive fun_clos_valtype : context → valtype → valtype → Prop where
  | fun_clos_valtype_case_0 (C : context) (t : valtype) (dt_lst : List deftype) (var_1 : List deftype) (var_0 : valtype) :
    fun_clos_deftypes (C.TYPES) var_1 →
    fun_subst_all_valtype t (Map (fun dt_elem => typeuse_deftype dt_elem) dt_lst) var_0 →
    dt_lst = var_1 →
    fun_clos_valtype C t var_0


inductive clos_valtype_is_wf : context → valtype → valtype → Prop where
  | clos_valtype_is_wf_0 (v_context : context) (v_valtype : valtype) (ret_val : valtype) (var_0 : valtype) :
    fun_clos_valtype v_context v_valtype var_0 →
    wf_context v_context →
    wf_valtype v_valtype →
    ret_val = var_0 →
    wf_valtype ret_val →
    clos_valtype_is_wf v_context v_valtype ret_val


inductive fun_clos_deftype : context → deftype → deftype → Prop where
  | fun_clos_deftype_case_0 (C : context) (dt : deftype) (dt'_lst : List deftype) (var_1 : List deftype) (var_0 : deftype) :
    fun_clos_deftypes (C.TYPES) var_1 →
    fun_subst_all_deftype dt (Map (fun dt'_elem => typeuse_deftype dt'_elem) dt'_lst) var_0 →
    dt'_lst = var_1 →
    fun_clos_deftype C dt var_0


inductive fun_clos_tagtype : context → tagtype → tagtype → Prop where
  | fun_clos_tagtype_case_0 (C : context) (jt : typeuse) (dt_lst : List deftype) (var_1 : List deftype) (var_0 : tagtype) :
    fun_clos_deftypes (C.TYPES) var_1 →
    fun_subst_all_tagtype jt (Map (fun dt_elem => typeuse_deftype dt_elem) dt_lst) var_0 →
    dt_lst = var_1 →
    fun_clos_tagtype C jt var_0


inductive clos_tagtype_is_wf : context → tagtype → tagtype → Prop where
  | clos_tagtype_is_wf_0 (v_context : context) (v_tagtype : tagtype) (ret_val : tagtype) (var_0 : tagtype) :
    fun_clos_tagtype v_context v_tagtype var_0 →
    wf_context v_context →
    wf_typeuse v_tagtype →
    ret_val = var_0 →
    wf_typeuse ret_val →
    clos_tagtype_is_wf v_context v_tagtype ret_val


inductive fun_clos_externtype : context → externtype → externtype → Prop where
  | fun_clos_externtype_case_0 (C : context) (xt : externtype) (dt_lst : List deftype) (var_1 : List deftype) (var_0 : externtype) :
    fun_clos_deftypes (C.TYPES) var_1 →
    fun_subst_all_externtype xt (Map (fun dt_elem => typeuse_deftype dt_elem) dt_lst) var_0 →
    dt_lst = var_1 →
    fun_clos_externtype C xt var_0


inductive clos_externtype_is_wf : context → externtype → externtype → Prop where
  | clos_externtype_is_wf_0 (v_context : context) (v_externtype : externtype) (ret_val : externtype) (var_0 : externtype) :
    fun_clos_externtype v_context v_externtype var_0 →
    wf_context v_context →
    wf_externtype v_externtype →
    ret_val = var_0 →
    wf_externtype ret_val →
    clos_externtype_is_wf v_context v_externtype ret_val


inductive fun_clos_moduletype : context → moduletype → moduletype → Prop where
  | fun_clos_moduletype_case_0 (C : context) (mmt : moduletype) (dt_lst : List deftype) (var_1 : List deftype) (var_0 : moduletype) :
    fun_clos_deftypes (C.TYPES) var_1 →
    fun_subst_all_moduletype mmt (Map (fun dt_elem => typeuse_deftype dt_elem) dt_lst) var_0 →
    dt_lst = var_1 →
    fun_clos_moduletype C mmt var_0


inductive clos_moduletype_is_wf : context → moduletype → moduletype → Prop where
  | clos_moduletype_is_wf_0 (v_context : context) (v_moduletype : moduletype) (ret_val : moduletype) (var_0 : moduletype) :
    fun_clos_moduletype v_context v_moduletype var_0 →
    wf_context v_context →
    wf_moduletype v_moduletype →
    ret_val = var_0 →
    wf_moduletype ret_val →
    clos_moduletype_is_wf v_context v_moduletype ret_val


inductive Numtype_ok : context → numtype → Prop where
  | mk_Numtype_ok (C : context) (v_numtype : numtype) :
    wf_context C →
    Numtype_ok C v_numtype


inductive Vectype_ok : context → vectype → Prop where
  | mk_Vectype_ok (C : context) (v_vectype : vectype) :
    wf_context C →
    Vectype_ok C v_vectype


inductive oktypenat : Type where
  | OK (_ : Nat) : oktypenat
deriving Inhabited, BEq

inductive Packtype_ok : context → packtype → Prop where
  | mk_Packtype_ok (C : context) (v_packtype : packtype) :
    wf_context C →
    Packtype_ok C v_packtype


inductive Packtype_sub : context → packtype → packtype → Prop where
  | mk_Packtype_sub (C : context) (v_packtype : packtype) :
    wf_context C →
    Packtype_sub C v_packtype v_packtype


inductive Numtype_sub : context → numtype → numtype → Prop where
  | mk_Numtype_sub (C : context) (v_numtype : numtype) :
    wf_context C →
    Numtype_sub C v_numtype v_numtype


inductive Expand : deftype → comptype → Prop where
  | mk_Expand (v_deftype : deftype) (v_comptype : comptype) (final_opt : Option final) (typeuse_lst : List typeuse) (var_0 : subtype) :
    fun_unrolldt v_deftype var_0 →
    var_0 = (subtype.SUB final_opt typeuse_lst v_comptype) →
    wf_subtype var_0 →
    wf_subtype (subtype.SUB final_opt typeuse_lst v_comptype) →
    Expand v_deftype v_comptype


inductive Vectype_sub : context → vectype → vectype → Prop where
  | mk_Vectype_sub (C : context) (v_vectype : vectype) :
    wf_context C →
    Vectype_sub C v_vectype v_vectype


def before (v_typeuse : typeuse) (nat : Nat) : Bool :=
  match v_typeuse with
  | typeuse.REC j => j < nat
  | _ => true

inductive fun_unrollht_ : context → heaptype → subtype → Prop where
  | fun_unrollht__case_0 (v_rectype : rectype) (v_n : n) (C : context) (var_0 : subtype) :
    fun_unrolldt (deftype._DEF v_rectype v_n) var_0 →
    fun_unrollht_ C (heaptype._DEF v_rectype v_n) var_0
  | fun_unrollht__case_1 (C : context) (v_typeidx : uN) (var_0 : subtype) :
    (proj_uN_0 v_typeidx) < (List.length (C.TYPES)) →
    fun_unrolldt ((C.TYPES)[proj_uN_0 v_typeidx]!) var_0 →
    fun_unrollht_ C (heaptype._IDX v_typeidx) var_0
  | fun_unrollht__case_2 (C : context) (i : Nat) :
    i < (List.length (C.RECS)) →
    fun_unrollht_ C (heaptype.REC i) ((C.RECS)[i]!)


inductive unrollht__is_wf : context → heaptype → subtype → Prop where
  | unrollht__is_wf_0 (v_context : context) (v_heaptype : heaptype) (ret_val : subtype) (var_0 : subtype) :
    fun_unrollht_ v_context v_heaptype var_0 →
    wf_context v_context →
    wf_heaptype v_heaptype →
    ret_val = var_0 →
    wf_subtype ret_val →
    unrollht__is_wf v_context v_heaptype ret_val


mutual
inductive Heaptype_ok : context → heaptype → Prop where
  | abs (C : context) (v_absheaptype : absheaptype) :
    wf_context C →
    Heaptype_ok C (heaptype_absheaptype v_absheaptype)
  | typeuse (C : context) (v_typeuse : typeuse) :
    Typeuse_ok C v_typeuse →
    wf_context C →
    wf_typeuse v_typeuse →
    Heaptype_ok C (heaptype_typeuse v_typeuse)
  | bot (C : context) :
    wf_context C →
    wf_heaptype heaptype.BOT →
    Heaptype_ok C heaptype.BOT

inductive Reftype_ok : context → reftype → Prop where
  | mk_Reftype_ok (C : context) (v_heaptype : heaptype) :
    Heaptype_ok C v_heaptype →
    wf_context C →
    wf_reftype (reftype.REF (some null.NULL) v_heaptype) →
    Reftype_ok C (reftype.REF (some null.NULL) v_heaptype)

inductive Valtype_ok : context → valtype → Prop where
  | num (C : context) (v_numtype : numtype) :
    Numtype_ok C v_numtype →
    wf_context C →
    Valtype_ok C (valtype_numtype v_numtype)
  | vec (C : context) (v_vectype : vectype) :
    Vectype_ok C v_vectype →
    wf_context C →
    Valtype_ok C (valtype_vectype v_vectype)
  | ref (C : context) (v_reftype : reftype) :
    Reftype_ok C v_reftype →
    wf_context C →
    wf_reftype v_reftype →
    Valtype_ok C (valtype_reftype v_reftype)
  | bot (C : context) :
    wf_context C →
    wf_valtype valtype.BOT →
    Valtype_ok C valtype.BOT

inductive Typeuse_ok : context → typeuse → Prop where
  | typeidx (C : context) (v_typeidx : typeidx) (dt : deftype) :
    (proj_uN_0 v_typeidx) < (List.length (C.TYPES)) →
    ((C.TYPES)[proj_uN_0 v_typeidx]!) = dt →
    wf_context C →
    wf_typeuse (typeuse._IDX v_typeidx) →
    Typeuse_ok C (typeuse._IDX v_typeidx)
  | rec_ (C : context) (i : n) (st : subtype) :
    i < (List.length (C.RECS)) →
    ((C.RECS)[i]!) = st →
    wf_context C →
    wf_subtype st →
    wf_typeuse (typeuse.REC i) →
    Typeuse_ok C (typeuse.REC i)
  | deftype (C : context) (v_deftype : deftype) :
    Deftype_ok C v_deftype →
    wf_context C →
    Typeuse_ok C (typeuse_deftype v_deftype)

inductive Resulttype_ok : context → resulttype → Prop where
  | mk_Resulttype_ok (C : context) (t_lst : List valtype) :
    Forall (fun t_elem => Valtype_ok C t_elem) t_lst →
    wf_context C →
    Forall (fun t_elem => wf_valtype t_elem) t_lst →
    Resulttype_ok C (.mk_list t_lst)

inductive Fieldtype_ok : context → fieldtype → Prop where
  | mk_Fieldtype_ok (C : context) (v_storagetype : storagetype) :
    Storagetype_ok C v_storagetype →
    wf_context C →
    wf_fieldtype (fieldtype.mk_fieldtype (some mut.MUT) v_storagetype) →
    Fieldtype_ok C (fieldtype.mk_fieldtype (some mut.MUT) v_storagetype)

inductive Storagetype_ok : context → storagetype → Prop where
  | val (C : context) (v_valtype : valtype) :
    Valtype_ok C v_valtype →
    wf_context C →
    wf_valtype v_valtype →
    Storagetype_ok C (storagetype_valtype v_valtype)
  | pack (C : context) (v_packtype : packtype) :
    Packtype_ok C v_packtype →
    wf_context C →
    Storagetype_ok C (storagetype_packtype v_packtype)

inductive Comptype_ok : context → comptype → Prop where
  | struct (C : context) (fieldtype_lst : List fieldtype) :
    Forall (fun v_fieldtype_elem => Fieldtype_ok C v_fieldtype_elem) fieldtype_lst →
    wf_context C →
    wf_comptype (comptype.STRUCT (list.mk_list fieldtype_lst)) →
    Comptype_ok C (comptype.STRUCT (list.mk_list fieldtype_lst))
  | array (C : context) (v_fieldtype : fieldtype) :
    Fieldtype_ok C v_fieldtype →
    wf_context C →
    wf_comptype (comptype.ARRAY v_fieldtype) →
    Comptype_ok C (comptype.ARRAY v_fieldtype)
  | func (C : context) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Resulttype_ok C (.mk_list t_1_lst) →
    Resulttype_ok C (.mk_list t_2_lst) →
    wf_context C →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Comptype_ok C (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))

inductive Subtype_ok2 : context → subtype → oktypenat → Prop where
  | mk_Subtype_ok2 (C : context) (typeuse_lst : List typeuse) (v_comptype : comptype) (i : Nat) (comptype'_lst : List comptype) (typeuse'_lst_lst : List (List typeuse)) (var_0_lst : List subtype) :
    (List.length var_0_lst) = (List.length typeuse_lst) →
    Forall₂ (fun var_0_elem v_typeuse_elem => fun_unrollht_ C (heaptype_typeuse v_typeuse_elem) var_0_elem) var_0_lst typeuse_lst →
    (List.length typeuse_lst) ≤ 1 →
    Forall (fun v_typeuse_elem => Typeuse_ok C v_typeuse_elem) typeuse_lst →
    Forall (fun v_typeuse_elem => before v_typeuse_elem i) typeuse_lst →
    (List.length var_0_lst) = (List.length comptype'_lst) →
    (List.length var_0_lst) = (List.length typeuse'_lst_lst) →
    Forall₃ (fun var_0_elem comptype'_elem typeuse'_lst_elem => var_0_elem = (subtype.SUB none typeuse'_lst_elem comptype'_elem)) var_0_lst comptype'_lst typeuse'_lst_lst →
    Comptype_ok C v_comptype →
    Forall (fun comptype'_elem => Comptype_sub C v_comptype comptype'_elem) comptype'_lst →
    wf_context C →
    Forall (fun var_0_elem => wf_subtype var_0_elem) var_0_lst →
    wf_subtype (subtype.SUB (some final.FINAL) typeuse_lst v_comptype) →
    (List.length comptype'_lst) = (List.length typeuse'_lst_lst) →
    Forall₂ (fun comptype'_elem typeuse'_lst_elem => wf_subtype (subtype.SUB none typeuse'_lst_elem comptype'_elem)) comptype'_lst typeuse'_lst_lst →
    Subtype_ok2 C (subtype.SUB (some final.FINAL) typeuse_lst v_comptype) (oktypenat.OK i)

inductive Rectype_ok2 : context → rectype → oktypenat → Prop where
  | empty (C : context) (i : Nat) :
    wf_context C →
    Rectype_ok2 C (rectype.REC (list.mk_list [])) (oktypenat.OK i)
  | cons (C : context) (subtype_1 : subtype) (subtype_lst : List subtype) (i : Nat) :
    Subtype_ok2 C subtype_1 (oktypenat.OK i) →
    Rectype_ok2 C (rectype.REC (list.mk_list subtype_lst)) (oktypenat.OK (i + 1)) →
    wf_context C →
    wf_subtype subtype_1 →
    Forall (fun v_subtype_elem => wf_subtype v_subtype_elem) subtype_lst →
    Rectype_ok2 C (rectype.REC (list.mk_list ([subtype_1] ++ subtype_lst))) (oktypenat.OK i)

inductive Deftype_ok : context → deftype → Prop where
  | mk_Deftype_ok (C : context) (v_rectype : rectype) (i : n) (v_n : n) (subtype_lst : List subtype) :
    Rectype_ok2 (({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := subtype_lst : context
    }) ++ C) v_rectype (oktypenat.OK 0) →
    v_rectype = (rectype.REC (list.mk_list subtype_lst)) →
    i < v_n →
    wf_context C →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := subtype_lst : context
    }) →
    v_n = (List.length subtype_lst) →
    Deftype_ok C (deftype._DEF v_rectype i)

inductive Comptype_sub : context → comptype → comptype → Prop where
  | struct (C : context) (ft_1_lst : List fieldtype) (ft'_1_lst : List fieldtype) (ft_2_lst : List fieldtype) :
    (List.length ft_1_lst) = (List.length ft_2_lst) →
    Forall₂ (fun ft_1_elem ft_2_elem => Fieldtype_sub C ft_1_elem ft_2_elem) ft_1_lst ft_2_lst →
    wf_context C →
    wf_comptype (comptype.STRUCT (list.mk_list (ft_1_lst ++ ft'_1_lst))) →
    wf_comptype (comptype.STRUCT (list.mk_list ft_2_lst)) →
    Comptype_sub C (comptype.STRUCT (list.mk_list (ft_1_lst ++ ft'_1_lst))) (comptype.STRUCT (list.mk_list ft_2_lst))
  | array (C : context) (ft_1 : fieldtype) (ft_2 : fieldtype) :
    Fieldtype_sub C ft_1 ft_2 →
    wf_context C →
    wf_comptype (comptype.ARRAY ft_1) →
    wf_comptype (comptype.ARRAY ft_2) →
    Comptype_sub C (comptype.ARRAY ft_1) (comptype.ARRAY ft_2)
  | func (C : context) (t_11_lst : List valtype) (t_12_lst : List valtype) (t_21_lst : List valtype) (t_22_lst : List valtype) :
    Resulttype_sub C (.mk_list t_21_lst) (.mk_list t_11_lst) →
    Resulttype_sub C (.mk_list t_12_lst) (.mk_list t_22_lst) →
    wf_context C →
    wf_comptype (comptype.FUNC (.mk_list t_11_lst) (.mk_list t_12_lst)) →
    wf_comptype (comptype.FUNC (.mk_list t_21_lst) (.mk_list t_22_lst)) →
    Comptype_sub C (comptype.FUNC (.mk_list t_11_lst) (.mk_list t_12_lst)) (comptype.FUNC (.mk_list t_21_lst) (.mk_list t_22_lst))

inductive Deftype_sub : context → deftype → deftype → Prop where
  | refl (C : context) (deftype_1 : deftype) (deftype_2 : deftype) (var_1 : deftype) (var_0 : deftype) :
    fun_clos_deftype C deftype_2 var_1 →
    fun_clos_deftype C deftype_1 var_0 →
    var_0 = var_1 →
    wf_context C →
    Deftype_sub C deftype_1 deftype_2
  | super (C : context) (deftype_1 : deftype) (deftype_2 : deftype) (final_opt : Option final) (typeuse_lst : List typeuse) (ct : comptype) (i : Nat) (var_0 : subtype) :
    fun_unrolldt deftype_1 var_0 →
    var_0 = (subtype.SUB final_opt typeuse_lst ct) →
    i < (List.length typeuse_lst) →
    Heaptype_sub C (heaptype_typeuse ((typeuse_lst)[i]!)) (heaptype_deftype deftype_2) →
    wf_context C →
    wf_subtype var_0 →
    wf_subtype (subtype.SUB final_opt typeuse_lst ct) →
    Deftype_sub C deftype_1 deftype_2

inductive Heaptype_sub : context → heaptype → heaptype → Prop where
  | refl (C : context) (v_heaptype : heaptype) :
    wf_context C →
    wf_heaptype v_heaptype →
    Heaptype_sub C v_heaptype v_heaptype
  | trans (C : context) (heaptype_1 : heaptype) (heaptype_2 : heaptype) (heaptype' : heaptype) :
    Heaptype_ok C heaptype' →
    Heaptype_sub C heaptype_1 heaptype' →
    Heaptype_sub C heaptype' heaptype_2 →
    wf_context C →
    wf_heaptype heaptype_1 →
    wf_heaptype heaptype_2 →
    wf_heaptype heaptype' →
    Heaptype_sub C heaptype_1 heaptype_2
  | eq_any (C : context) :
    wf_context C →
    wf_heaptype heaptype.EQ →
    wf_heaptype heaptype.ANY →
    Heaptype_sub C heaptype.EQ heaptype.ANY
  | i31_eq (C : context) :
    wf_context C →
    wf_heaptype heaptype.I31 →
    wf_heaptype heaptype.EQ →
    Heaptype_sub C heaptype.I31 heaptype.EQ
  | struct_eq (C : context) :
    wf_context C →
    wf_heaptype heaptype.STRUCT →
    wf_heaptype heaptype.EQ →
    Heaptype_sub C heaptype.STRUCT heaptype.EQ
  | array_eq (C : context) :
    wf_context C →
    wf_heaptype heaptype.ARRAY →
    wf_heaptype heaptype.EQ →
    Heaptype_sub C heaptype.ARRAY heaptype.EQ
  | struct (C : context) (v_deftype : deftype) (fieldtype_lst : List fieldtype) :
    Expand v_deftype (comptype.STRUCT (list.mk_list fieldtype_lst)) →
    wf_context C →
    wf_heaptype heaptype.STRUCT →
    wf_comptype (comptype.STRUCT (list.mk_list fieldtype_lst)) →
    Heaptype_sub C (heaptype_deftype v_deftype) heaptype.STRUCT
  | array (C : context) (v_deftype : deftype) (v_fieldtype : fieldtype) :
    Expand v_deftype (comptype.ARRAY v_fieldtype) →
    wf_context C →
    wf_heaptype heaptype.ARRAY →
    wf_comptype (comptype.ARRAY v_fieldtype) →
    Heaptype_sub C (heaptype_deftype v_deftype) heaptype.ARRAY
  | func (C : context) (v_deftype : deftype) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Expand v_deftype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_heaptype heaptype.FUNC →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Heaptype_sub C (heaptype_deftype v_deftype) heaptype.FUNC
  | def (C : context) (deftype_1 : deftype) (deftype_2 : deftype) :
    Deftype_sub C deftype_1 deftype_2 →
    wf_context C →
    Heaptype_sub C (heaptype_deftype deftype_1) (heaptype_deftype deftype_2)
  | typeidx_l (C : context) (v_typeidx : typeidx) (v_heaptype : heaptype) :
    (proj_uN_0 v_typeidx) < (List.length (C.TYPES)) →
    Heaptype_sub C (heaptype_deftype ((C.TYPES)[proj_uN_0 v_typeidx]!)) v_heaptype →
    wf_context C →
    wf_heaptype v_heaptype →
    wf_heaptype (heaptype._IDX v_typeidx) →
    Heaptype_sub C (heaptype._IDX v_typeidx) v_heaptype
  | typeidx_r (C : context) (v_heaptype : heaptype) (v_typeidx : typeidx) :
    (proj_uN_0 v_typeidx) < (List.length (C.TYPES)) →
    Heaptype_sub C v_heaptype (heaptype_deftype ((C.TYPES)[proj_uN_0 v_typeidx]!)) →
    wf_context C →
    wf_heaptype v_heaptype →
    wf_heaptype (heaptype._IDX v_typeidx) →
    Heaptype_sub C v_heaptype (heaptype._IDX v_typeidx)
  | rec_struct (C : context) (i : n) (final_opt : Option final) (fieldtype_lst : List fieldtype) :
    i < (List.length (C.RECS)) →
    ((C.RECS)[i]!) = (subtype.SUB final_opt [] (comptype.STRUCT (list.mk_list fieldtype_lst))) →
    wf_context C →
    wf_heaptype (heaptype.REC i) →
    wf_heaptype heaptype.STRUCT →
    wf_subtype (subtype.SUB final_opt [] (comptype.STRUCT (list.mk_list fieldtype_lst))) →
    Heaptype_sub C (heaptype.REC i) heaptype.STRUCT
  | rec_array (C : context) (i : n) (final_opt : Option final) (v_fieldtype : fieldtype) :
    i < (List.length (C.RECS)) →
    ((C.RECS)[i]!) = (subtype.SUB final_opt [] (comptype.ARRAY v_fieldtype)) →
    wf_context C →
    wf_heaptype (heaptype.REC i) →
    wf_heaptype heaptype.ARRAY →
    wf_subtype (subtype.SUB final_opt [] (comptype.ARRAY v_fieldtype)) →
    Heaptype_sub C (heaptype.REC i) heaptype.ARRAY
  | rec_func (C : context) (i : n) (final_opt : Option final) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    i < (List.length (C.RECS)) →
    ((C.RECS)[i]!) = (subtype.SUB final_opt [] (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) →
    wf_context C →
    wf_heaptype (heaptype.REC i) →
    wf_heaptype heaptype.FUNC →
    wf_subtype (subtype.SUB final_opt [] (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst))) →
    Heaptype_sub C (heaptype.REC i) heaptype.FUNC
  | rec_sub (C : context) (i : n) (typeuse_lst : List typeuse) (j : Nat) (final_opt : Option final) (ct : comptype) :
    j < (List.length typeuse_lst) →
    i < (List.length (C.RECS)) →
    ((C.RECS)[i]!) = (subtype.SUB final_opt typeuse_lst ct) →
    wf_context C →
    wf_heaptype (heaptype.REC i) →
    wf_subtype (subtype.SUB final_opt typeuse_lst ct) →
    Heaptype_sub C (heaptype.REC i) (heaptype_typeuse ((typeuse_lst)[j]!))
  | none (C : context) (v_heaptype : heaptype) :
    Heaptype_sub C v_heaptype heaptype.ANY →
    v_heaptype ≠ heaptype.BOT →
    wf_context C →
    wf_heaptype v_heaptype →
    wf_heaptype heaptype.NONE →
    wf_heaptype heaptype.ANY →
    wf_heaptype heaptype.BOT →
    Heaptype_sub C heaptype.NONE v_heaptype
  | nofunc (C : context) (v_heaptype : heaptype) :
    Heaptype_sub C v_heaptype heaptype.FUNC →
    v_heaptype ≠ heaptype.BOT →
    wf_context C →
    wf_heaptype v_heaptype →
    wf_heaptype heaptype.NOFUNC →
    wf_heaptype heaptype.FUNC →
    wf_heaptype heaptype.BOT →
    Heaptype_sub C heaptype.NOFUNC v_heaptype
  | noexn (C : context) (v_heaptype : heaptype) :
    Heaptype_sub C v_heaptype heaptype.EXN →
    v_heaptype ≠ heaptype.BOT →
    wf_context C →
    wf_heaptype v_heaptype →
    wf_heaptype heaptype.NOEXN →
    wf_heaptype heaptype.EXN →
    wf_heaptype heaptype.BOT →
    Heaptype_sub C heaptype.NOEXN v_heaptype
  | noextern (C : context) (v_heaptype : heaptype) :
    Heaptype_sub C v_heaptype heaptype.EXTERN →
    v_heaptype ≠ heaptype.BOT →
    wf_context C →
    wf_heaptype v_heaptype →
    wf_heaptype heaptype.NOEXTERN →
    wf_heaptype heaptype.EXTERN →
    wf_heaptype heaptype.BOT →
    Heaptype_sub C heaptype.NOEXTERN v_heaptype
  | bot (C : context) (v_heaptype : heaptype) :
    wf_context C →
    wf_heaptype v_heaptype →
    wf_heaptype heaptype.BOT →
    Heaptype_sub C heaptype.BOT v_heaptype

inductive Reftype_sub : context → reftype → reftype → Prop where
  | nonnull (C : context) (ht_1 : heaptype) (ht_2 : heaptype) :
    Heaptype_sub C ht_1 ht_2 →
    wf_context C →
    wf_reftype (reftype.REF none ht_1) →
    wf_reftype (reftype.REF none ht_2) →
    Reftype_sub C (reftype.REF none ht_1) (reftype.REF none ht_2)
  | null (C : context) (ht_1 : heaptype) (ht_2 : heaptype) :
    Heaptype_sub C ht_1 ht_2 →
    wf_context C →
    wf_reftype (reftype.REF (some null.NULL) ht_1) →
    wf_reftype (reftype.REF (some null.NULL) ht_2) →
    Reftype_sub C (reftype.REF (some null.NULL) ht_1) (reftype.REF (some null.NULL) ht_2)

inductive Valtype_sub : context → valtype → valtype → Prop where
  | num (C : context) (numtype_1 : numtype) (numtype_2 : numtype) :
    Numtype_sub C numtype_1 numtype_2 →
    wf_context C →
    Valtype_sub C (valtype_numtype numtype_1) (valtype_numtype numtype_2)
  | vec (C : context) (vectype_1 : vectype) (vectype_2 : vectype) :
    Vectype_sub C vectype_1 vectype_2 →
    wf_context C →
    Valtype_sub C (valtype_vectype vectype_1) (valtype_vectype vectype_2)
  | ref (C : context) (reftype_1 : reftype) (reftype_2 : reftype) :
    Reftype_sub C reftype_1 reftype_2 →
    wf_context C →
    wf_reftype reftype_1 →
    wf_reftype reftype_2 →
    Valtype_sub C (valtype_reftype reftype_1) (valtype_reftype reftype_2)
  | bot (C : context) (v_valtype : valtype) :
    wf_context C →
    wf_valtype v_valtype →
    wf_valtype valtype.BOT →
    Valtype_sub C valtype.BOT v_valtype

inductive Resulttype_sub : context → resulttype → resulttype → Prop where
  | mk_Resulttype_sub (C : context) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (List.length t_1_lst) = (List.length t_2_lst) →
    Forall₂ (fun t_1_elem t_2_elem => Valtype_sub C t_1_elem t_2_elem) t_1_lst t_2_lst →
    wf_context C →
    Forall (fun t_1_elem => wf_valtype t_1_elem) t_1_lst →
    Forall (fun t_2_elem => wf_valtype t_2_elem) t_2_lst →
    Resulttype_sub C (.mk_list t_1_lst) (.mk_list t_2_lst)

inductive Storagetype_sub : context → storagetype → storagetype → Prop where
  | val (C : context) (valtype_1 : valtype) (valtype_2 : valtype) :
    Valtype_sub C valtype_1 valtype_2 →
    wf_context C →
    wf_valtype valtype_1 →
    wf_valtype valtype_2 →
    Storagetype_sub C (storagetype_valtype valtype_1) (storagetype_valtype valtype_2)
  | pack (C : context) (packtype_1 : packtype) (packtype_2 : packtype) :
    Packtype_sub C packtype_1 packtype_2 →
    wf_context C →
    Storagetype_sub C (storagetype_packtype packtype_1) (storagetype_packtype packtype_2)

inductive Fieldtype_sub : context → fieldtype → fieldtype → Prop where
  | const (C : context) (zt_1 : storagetype) (zt_2 : storagetype) :
    Storagetype_sub C zt_1 zt_2 →
    wf_context C →
    wf_fieldtype (fieldtype.mk_fieldtype none zt_1) →
    wf_fieldtype (fieldtype.mk_fieldtype none zt_2) →
    Fieldtype_sub C (fieldtype.mk_fieldtype none zt_1) (fieldtype.mk_fieldtype none zt_2)
  | var (C : context) (zt_1 : storagetype) (zt_2 : storagetype) :
    Storagetype_sub C zt_1 zt_2 →
    Storagetype_sub C zt_2 zt_1 →
    wf_context C →
    wf_fieldtype (fieldtype.mk_fieldtype (some mut.MUT) zt_1) →
    wf_fieldtype (fieldtype.mk_fieldtype (some mut.MUT) zt_2) →
    Fieldtype_sub C (fieldtype.mk_fieldtype (some mut.MUT) zt_1) (fieldtype.mk_fieldtype (some mut.MUT) zt_2)


end

inductive Localtype_ok : context → localtype → Prop where
  | mk_Localtype_ok (C : context) (v_init : init) (t : valtype) :
    Valtype_ok C t →
    wf_context C →
    wf_localtype (localtype.mk_localtype v_init t) →
    Localtype_ok C (localtype.mk_localtype v_init t)


inductive Instrtype_ok : context → instrtype → Prop where
  | mk_Instrtype_ok (C : context) (t_1_lst : List valtype) (x_lst : List idx) (t_2_lst : List valtype) (lct_lst : List localtype) :
    Resulttype_ok C (.mk_list t_1_lst) →
    Resulttype_ok C (.mk_list t_2_lst) →
    (List.length lct_lst) = (List.length x_lst) →
    Forall (fun x_elem => (proj_uN_0 x_elem) < (List.length (C.LOCALS))) x_lst →
    Forall₂ (fun lct_elem x_elem => ((C.LOCALS)[proj_uN_0 x_elem]!) = lct_elem) lct_lst x_lst →
    wf_context C →
    Forall (fun lct_elem => wf_localtype lct_elem) lct_lst →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst))


inductive Expand_use : typeuse → context → comptype → Prop where
  | deftype (v_deftype : deftype) (C : context) (v_comptype : comptype) :
    Expand v_deftype v_comptype →
    wf_context C →
    wf_comptype v_comptype →
    Expand_use (typeuse_deftype v_deftype) C v_comptype
  | typeidx (v_typeidx : typeidx) (C : context) (v_comptype : comptype) :
    (proj_uN_0 v_typeidx) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 v_typeidx]!) v_comptype →
    wf_context C →
    wf_comptype v_comptype →
    wf_typeuse (typeuse._IDX v_typeidx) →
    Expand_use (typeuse._IDX v_typeidx) C v_comptype


inductive oktypeidx : Type where
  | OK (v_typeidx : typeidx) : oktypeidx
deriving Inhabited, BEq

inductive wf_oktypeidx : oktypeidx → Prop where
  | oktypeidx_case_0 (v_typeidx : typeidx) :
    wf_uN 32 v_typeidx →
    wf_oktypeidx (oktypeidx.OK v_typeidx)


inductive Subtype_ok : context → subtype → oktypeidx → Prop where
  | mk_Subtype_ok (C : context) (x_lst : List idx) (v_comptype : comptype) (x_0 : idx) (comptype'_lst : List comptype) (yy_lst_lst : List (List typeuse)) (var_0_lst : List subtype) :
    (List.length var_0_lst) = (List.length x_lst) →
    Forall (fun x_elem => (proj_uN_0 x_elem) < (List.length (C.TYPES))) x_lst →
    Forall₂ (fun var_0_elem x_elem => fun_unrolldt ((C.TYPES)[proj_uN_0 x_elem]!) var_0_elem) var_0_lst x_lst →
    (List.length x_lst) ≤ 1 →
    Forall (fun x_elem => (proj_uN_0 x_elem) < (proj_uN_0 x_0)) x_lst →
    (List.length var_0_lst) = (List.length comptype'_lst) →
    (List.length var_0_lst) = (List.length yy_lst_lst) →
    Forall₃ (fun var_0_elem comptype'_elem yy_lst_elem => var_0_elem = (subtype.SUB none yy_lst_elem comptype'_elem)) var_0_lst comptype'_lst yy_lst_lst →
    Comptype_ok C v_comptype →
    Forall (fun comptype'_elem => Comptype_sub C v_comptype comptype'_elem) comptype'_lst →
    wf_context C →
    Forall (fun var_0_elem => wf_subtype var_0_elem) var_0_lst →
    wf_subtype (subtype.SUB (some final.FINAL) (Map (fun x_elem => typeuse._IDX x_elem) x_lst) v_comptype) →
    wf_oktypeidx (oktypeidx.OK x_0) →
    (List.length comptype'_lst) = (List.length yy_lst_lst) →
    Forall₂ (fun comptype'_elem yy_lst_elem => wf_subtype (subtype.SUB none yy_lst_elem comptype'_elem)) comptype'_lst yy_lst_lst →
    Subtype_ok C (subtype.SUB (some final.FINAL) (Map (fun x_elem => typeuse._IDX x_elem) x_lst) v_comptype) (oktypeidx.OK x_0)


inductive Rectype_ok : context → rectype → oktypeidx → Prop where
  | empty (C : context) (x : idx) :
    wf_context C →
    wf_oktypeidx (oktypeidx.OK x) →
    Rectype_ok C (rectype.REC (list.mk_list [])) (oktypeidx.OK x)
  | cons (C : context) (subtype_1 : subtype) (subtype_lst : List subtype) (x : idx) :
    Subtype_ok C subtype_1 (oktypeidx.OK x) →
    Rectype_ok C (rectype.REC (list.mk_list subtype_lst)) (oktypeidx.OK (uN.mk_uN ((proj_uN_0 x) + 1))) →
    wf_context C →
    wf_subtype subtype_1 →
    Forall (fun v_subtype_elem => wf_subtype v_subtype_elem) subtype_lst →
    wf_oktypeidx (oktypeidx.OK x) →
    wf_oktypeidx (oktypeidx.OK (uN.mk_uN ((proj_uN_0 x) + 1))) →
    Rectype_ok C (rectype.REC (list.mk_list ([subtype_1] ++ subtype_lst))) (oktypeidx.OK x)


inductive Limits_ok : context → limits → Nat → Prop where
  | mk_Limits_ok (C : context) (v_n : n) (m_opt : Option m) (k : Nat) :
    v_n ≤ k →
    Forall (fun v_m_elem => (v_n ≤ v_m_elem) ∧ (v_m_elem ≤ k)) (Option.toList m_opt) →
    wf_context C →
    wf_limits (limits.mk_limits (uN.mk_uN v_n) (OMap (fun v_m_elem => uN.mk_uN v_m_elem) m_opt)) →
    Limits_ok C (limits.mk_limits (uN.mk_uN v_n) (OMap (fun v_m_elem => uN.mk_uN v_m_elem) m_opt)) k


inductive Tagtype_ok : context → tagtype → Prop where
  | mk_Tagtype_ok (C : context) (v_typeuse : typeuse) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Typeuse_ok C v_typeuse →
    Expand_use v_typeuse C (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_typeuse v_typeuse →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Tagtype_ok C v_typeuse


inductive Globaltype_ok : context → globaltype → Prop where
  | mk_Globaltype_ok (C : context) (t : valtype) :
    Valtype_ok C t →
    wf_context C →
    wf_globaltype (globaltype.mk_globaltype (some mut.MUT) t) →
    Globaltype_ok C (globaltype.mk_globaltype (some mut.MUT) t)


inductive Memtype_ok : context → memtype → Prop where
  | mk_Memtype_ok (C : context) (v_addrtype : addrtype) (v_limits : limits) :
    Limits_ok C v_limits (2 ^ (Int.toNat (((size (numtype_addrtype v_addrtype)) : Int) - (16 : Int)))) →
    wf_context C →
    wf_memtype (memtype.PAGE v_addrtype v_limits) →
    Memtype_ok C (memtype.PAGE v_addrtype v_limits)


inductive Tabletype_ok : context → tabletype → Prop where
  | mk_Tabletype_ok (C : context) (v_addrtype : addrtype) (v_limits : limits) (v_reftype : reftype) :
    Limits_ok C v_limits (Int.toNat (((2 ^ (size (numtype_addrtype v_addrtype))) : Int) - (1 : Int))) →
    Reftype_ok C v_reftype →
    wf_context C →
    wf_tabletype (tabletype.mk_tabletype v_addrtype v_limits v_reftype) →
    Tabletype_ok C (tabletype.mk_tabletype v_addrtype v_limits v_reftype)


inductive Externtype_ok : context → externtype → Prop where
  | tag (C : context) (v_tagtype : tagtype) :
    Tagtype_ok C v_tagtype →
    wf_context C →
    wf_externtype (externtype.TAG v_tagtype) →
    Externtype_ok C (externtype.TAG v_tagtype)
  | global (C : context) (v_globaltype : globaltype) :
    Globaltype_ok C v_globaltype →
    wf_context C →
    wf_externtype (externtype.GLOBAL v_globaltype) →
    Externtype_ok C (externtype.GLOBAL v_globaltype)
  | mem (C : context) (v_memtype : memtype) :
    Memtype_ok C v_memtype →
    wf_context C →
    wf_externtype (externtype.MEM v_memtype) →
    Externtype_ok C (externtype.MEM v_memtype)
  | table (C : context) (v_tabletype : tabletype) :
    Tabletype_ok C v_tabletype →
    wf_context C →
    wf_externtype (externtype.TABLE v_tabletype) →
    Externtype_ok C (externtype.TABLE v_tabletype)
  | func (C : context) (v_typeuse : typeuse) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Typeuse_ok C v_typeuse →
    Expand_use v_typeuse C (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_externtype (externtype.FUNC v_typeuse) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Externtype_ok C (externtype.FUNC v_typeuse)


inductive Instrtype_sub : context → instrtype → instrtype → Prop where
  | mk_Instrtype_sub (C : context) (t_11_lst : List valtype) (x_1_lst : List idx) (t_12_lst : List valtype) (t_21_lst : List valtype) (x_2_lst : List idx) (t_22_lst : List valtype) (x_lst : List idx) (t_lst : List valtype) :
    Resulttype_sub C (.mk_list t_21_lst) (.mk_list t_11_lst) →
    Resulttype_sub C (.mk_list t_12_lst) (.mk_list t_22_lst) →
    x_lst = (setminus_ localidx x_2_lst x_1_lst) →
    (List.length t_lst) = (List.length x_lst) →
    Forall (fun x_elem => (proj_uN_0 x_elem) < (List.length (C.LOCALS))) x_lst →
    Forall₂ (fun t_elem x_elem => ((C.LOCALS)[proj_uN_0 x_elem]!) = (localtype.mk_localtype init.SET t_elem)) t_lst x_lst →
    wf_context C →
    Forall (fun x_elem => wf_uN 32 x_elem) x_lst →
    Forall (fun iter_elem => wf_uN 32 iter_elem) (setminus_ localidx x_2_lst x_1_lst) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_11_lst) x_1_lst (.mk_list t_12_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_21_lst) x_2_lst (.mk_list t_22_lst)) →
    Forall (fun t_elem => wf_localtype (localtype.mk_localtype init.SET t_elem)) t_lst →
    Instrtype_sub C (instrtype.mk_instrtype (.mk_list t_11_lst) x_1_lst (.mk_list t_12_lst)) (instrtype.mk_instrtype (.mk_list t_21_lst) x_2_lst (.mk_list t_22_lst))


inductive Limits_sub : context → limits → limits → Prop where
  | max (C : context) (n_1 : n) (m_1 : m) (n_2 : n) (m_2_opt : Option m) :
    n_1 ≥ n_2 →
    Forall (fun m_2_elem => m_1 ≤ m_2_elem) (Option.toList m_2_opt) →
    wf_context C →
    wf_limits (limits.mk_limits (uN.mk_uN n_1) (some (uN.mk_uN m_1))) →
    wf_limits (limits.mk_limits (uN.mk_uN n_2) (OMap (fun m_2_elem => uN.mk_uN m_2_elem) m_2_opt)) →
    Limits_sub C (limits.mk_limits (uN.mk_uN n_1) (some (uN.mk_uN m_1))) (limits.mk_limits (uN.mk_uN n_2) (OMap (fun m_2_elem => uN.mk_uN m_2_elem) m_2_opt))
  | eps (C : context) (n_1 : n) (n_2 : n) :
    n_1 ≥ n_2 →
    wf_context C →
    wf_limits (limits.mk_limits (uN.mk_uN n_1) none) →
    wf_limits (limits.mk_limits (uN.mk_uN n_2) none) →
    Limits_sub C (limits.mk_limits (uN.mk_uN n_1) none) (limits.mk_limits (uN.mk_uN n_2) none)


inductive Tagtype_sub : context → tagtype → tagtype → Prop where
  | mk_Tagtype_sub (C : context) (deftype_1 : deftype) (deftype_2 : deftype) :
    Deftype_sub C deftype_1 deftype_2 →
    Deftype_sub C deftype_2 deftype_1 →
    wf_context C →
    Tagtype_sub C (typeuse_deftype deftype_1) (typeuse_deftype deftype_2)


inductive Globaltype_sub : context → globaltype → globaltype → Prop where
  | const (C : context) (valtype_1 : valtype) (valtype_2 : valtype) :
    Valtype_sub C valtype_1 valtype_2 →
    wf_context C →
    wf_globaltype (globaltype.mk_globaltype none valtype_1) →
    wf_globaltype (globaltype.mk_globaltype none valtype_2) →
    Globaltype_sub C (globaltype.mk_globaltype none valtype_1) (globaltype.mk_globaltype none valtype_2)
  | var (C : context) (valtype_1 : valtype) (valtype_2 : valtype) :
    Valtype_sub C valtype_1 valtype_2 →
    Valtype_sub C valtype_2 valtype_1 →
    wf_context C →
    wf_globaltype (globaltype.mk_globaltype (some mut.MUT) valtype_1) →
    wf_globaltype (globaltype.mk_globaltype (some mut.MUT) valtype_2) →
    Globaltype_sub C (globaltype.mk_globaltype (some mut.MUT) valtype_1) (globaltype.mk_globaltype (some mut.MUT) valtype_2)


inductive Memtype_sub : context → memtype → memtype → Prop where
  | mk_Memtype_sub (C : context) (v_addrtype : addrtype) (limits_1 : limits) (limits_2 : limits) :
    Limits_sub C limits_1 limits_2 →
    wf_context C →
    wf_memtype (memtype.PAGE v_addrtype limits_1) →
    wf_memtype (memtype.PAGE v_addrtype limits_2) →
    Memtype_sub C (memtype.PAGE v_addrtype limits_1) (memtype.PAGE v_addrtype limits_2)


inductive Tabletype_sub : context → tabletype → tabletype → Prop where
  | mk_Tabletype_sub (C : context) (v_addrtype : addrtype) (limits_1 : limits) (reftype_1 : reftype) (limits_2 : limits) (reftype_2 : reftype) :
    Limits_sub C limits_1 limits_2 →
    Reftype_sub C reftype_1 reftype_2 →
    Reftype_sub C reftype_2 reftype_1 →
    wf_context C →
    wf_tabletype (tabletype.mk_tabletype v_addrtype limits_1 reftype_1) →
    wf_tabletype (tabletype.mk_tabletype v_addrtype limits_2 reftype_2) →
    Tabletype_sub C (tabletype.mk_tabletype v_addrtype limits_1 reftype_1) (tabletype.mk_tabletype v_addrtype limits_2 reftype_2)


inductive Externtype_sub : context → externtype → externtype → Prop where
  | tag (C : context) (tagtype_1 : tagtype) (tagtype_2 : tagtype) :
    Tagtype_sub C tagtype_1 tagtype_2 →
    wf_context C →
    wf_externtype (externtype.TAG tagtype_1) →
    wf_externtype (externtype.TAG tagtype_2) →
    Externtype_sub C (externtype.TAG tagtype_1) (externtype.TAG tagtype_2)
  | global (C : context) (globaltype_1 : globaltype) (globaltype_2 : globaltype) :
    Globaltype_sub C globaltype_1 globaltype_2 →
    wf_context C →
    wf_externtype (externtype.GLOBAL globaltype_1) →
    wf_externtype (externtype.GLOBAL globaltype_2) →
    Externtype_sub C (externtype.GLOBAL globaltype_1) (externtype.GLOBAL globaltype_2)
  | mem (C : context) (memtype_1 : memtype) (memtype_2 : memtype) :
    Memtype_sub C memtype_1 memtype_2 →
    wf_context C →
    wf_externtype (externtype.MEM memtype_1) →
    wf_externtype (externtype.MEM memtype_2) →
    Externtype_sub C (externtype.MEM memtype_1) (externtype.MEM memtype_2)
  | table (C : context) (tabletype_1 : tabletype) (tabletype_2 : tabletype) :
    Tabletype_sub C tabletype_1 tabletype_2 →
    wf_context C →
    wf_externtype (externtype.TABLE tabletype_1) →
    wf_externtype (externtype.TABLE tabletype_2) →
    Externtype_sub C (externtype.TABLE tabletype_1) (externtype.TABLE tabletype_2)
  | func (C : context) (deftype_1 : deftype) (deftype_2 : deftype) :
    Deftype_sub C deftype_1 deftype_2 →
    wf_context C →
    wf_externtype (externtype.FUNC (typeuse_deftype deftype_1)) →
    wf_externtype (externtype.FUNC (typeuse_deftype deftype_2)) →
    Externtype_sub C (externtype.FUNC (typeuse_deftype deftype_1)) (externtype.FUNC (typeuse_deftype deftype_2))


inductive Blocktype_ok : context → blocktype → instrtype → Prop where
  | valtype (C : context) (valtype_opt : Option valtype) :
    Forall (fun v_valtype_elem => Valtype_ok C v_valtype_elem) (Option.toList valtype_opt) →
    wf_context C →
    wf_blocktype (blocktype._RESULT valtype_opt) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list (Option.toList valtype_opt))) →
    Blocktype_ok C (blocktype._RESULT valtype_opt) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list (Option.toList valtype_opt)))
  | typeidx (C : context) (v_typeidx : typeidx) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (proj_uN_0 v_typeidx) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 v_typeidx]!) (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_blocktype (blocktype._IDX v_typeidx) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Blocktype_ok C (blocktype._IDX v_typeidx) (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))


inductive Catch_ok : context → «catch» → Prop where
  | «catch» (C : context) (x : idx) (l : labelidx) (t_lst : List valtype) :
    (as_deftype ((C.TAGS)[proj_uN_0 x]!)) ≠ none →
    (proj_uN_0 x) < (List.length (C.TAGS)) →
    Expand (Option.get! (as_deftype ((C.TAGS)[proj_uN_0 x]!))) (comptype.FUNC (.mk_list t_lst) (.mk_list [])) →
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    Resulttype_sub C (.mk_list t_lst) ((C.LABELS)[proj_uN_0 l]!) →
    wf_context C →
    wf_catch (catch.CATCH x l) →
    wf_comptype (comptype.FUNC (.mk_list t_lst) (.mk_list [])) →
    Catch_ok C (catch.CATCH x l)
  | catch_ref (C : context) (x : idx) (l : labelidx) (t_lst : List valtype) :
    (as_deftype ((C.TAGS)[proj_uN_0 x]!)) ≠ none →
    (proj_uN_0 x) < (List.length (C.TAGS)) →
    Expand (Option.get! (as_deftype ((C.TAGS)[proj_uN_0 x]!))) (comptype.FUNC (.mk_list t_lst) (.mk_list [])) →
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    Resulttype_sub C (.mk_list (t_lst ++ [valtype.REF none heaptype.EXN])) ((C.LABELS)[proj_uN_0 l]!) →
    wf_context C →
    wf_catch (catch.CATCH_REF x l) →
    wf_comptype (comptype.FUNC (.mk_list t_lst) (.mk_list [])) →
    Catch_ok C (catch.CATCH_REF x l)
  | catch_all (C : context) (l : labelidx) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    Resulttype_sub C (.mk_list []) ((C.LABELS)[proj_uN_0 l]!) →
    wf_context C →
    wf_catch (catch.CATCH_ALL l) →
    Catch_ok C (catch.CATCH_ALL l)
  | catch_all_ref (C : context) (l : labelidx) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    Resulttype_sub C (.mk_list [valtype.REF none heaptype.EXN]) ((C.LABELS)[proj_uN_0 l]!) →
    wf_context C →
    wf_catch (catch.CATCH_ALL_REF l) →
    Catch_ok C (catch.CATCH_ALL_REF l)


def default_ (v_valtype : valtype) : Option (Option val) :=
  match v_valtype with
  | valtype.I32 => some (some (val.CONST (numtype_addrtype addrtype.I32) (num_.mk_num__0 addrtype.I32 (uN.mk_uN 0))))
  | valtype.I64 => some (some (val.CONST (numtype_addrtype addrtype.I64) (num_.mk_num__0 addrtype.I64 (uN.mk_uN 0))))
  | valtype.F32 => some (some (val.CONST (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 (fzero (size (numtype_Fnn Fnn.F32))))))
  | valtype.F64 => some (some (val.CONST (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 (fzero (size (numtype_Fnn Fnn.F64))))))
  | valtype.V128 => some (some (val.VCONST vectype.V128 (uN.mk_uN 0)))
  | valtype.REF (some null.NULL) ht => some (some val.REF_NULL_ADDR)
  | valtype.REF none ht => some none
  | _ => none

inductive default__is_wf : valtype → Option val → Prop where
  | default__is_wf_0 (v_valtype : valtype) (ret_val_opt : Option val) :
    wf_valtype v_valtype →
    (default_ v_valtype) ≠ none →
    ret_val_opt = (Option.get! (default_ v_valtype)) →
    Forall (fun ret_val_elem => wf_val ret_val_elem) (Option.toList ret_val_opt) →
    default__is_wf v_valtype ret_val_opt


inductive Defaultable : valtype → Prop where
  | mk_Defaultable (t : valtype) :
    (default_ t) ≠ none →
    (Option.get! (default_ t)) ≠ none →
    wf_valtype t →
    Forall (fun iter_elem => wf_val iter_elem) (Option.toList (Option.get! (default_ t))) →
    Defaultable t


inductive Memarg_ok : memarg → addrtype → N → Prop where
  | mk_Memarg_ok (v_n : n) (v_m : m) («at» : addrtype) (v_N : N) :
    ((2 ^ v_n) : Rat) ≤ ((v_N : Rat) / (8 : Rat)) →
    v_m < (2 ^ (size (numtype_addrtype «at»))) →
    wf_memarg ({
      ALIGN := uN.mk_uN v_n
      OFFSET := uN.mk_uN v_m : memarg
    }) →
    Memarg_ok ({
      ALIGN := uN.mk_uN v_n
      OFFSET := uN.mk_uN v_m : memarg
    }) «at» v_N


def is_packtype (v_storagetype : storagetype) : Bool :=
  v_storagetype != (storagetype_valtype (unpack v_storagetype))

mutual
inductive Instr_ok : context → instr → instrtype → Prop where
  | nop (C : context) :
    wf_context C →
    wf_instr instr.NOP →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [])) →
    Instr_ok C instr.NOP (instrtype.mk_instrtype (.mk_list []) [] (.mk_list []))
  | unreachable (C : context) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr instr.UNREACHABLE →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instr_ok C instr.UNREACHABLE (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | drop (C : context) (t : valtype) :
    Valtype_ok C t →
    wf_context C →
    wf_instr instr.DROP →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [t]) [] (.mk_list [])) →
    Instr_ok C instr.DROP (instrtype.mk_instrtype (.mk_list [t]) [] (.mk_list []))
  | select_expl (C : context) (t : valtype) :
    Valtype_ok C t →
    wf_context C →
    wf_instr (instr.SELECT (some [t])) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [t, t, valtype.I32]) [] (.mk_list [t])) →
    Instr_ok C (instr.SELECT (some [t])) (instrtype.mk_instrtype (.mk_list [t, t, valtype.I32]) [] (.mk_list [t]))
  | select_impl (C : context) (t : valtype) (t' : valtype) (v_numtype : numtype) (v_vectype : vectype) :
    Valtype_ok C t →
    Valtype_sub C t t' →
    (t' = (valtype_numtype v_numtype)) ∨ (t' = (valtype_vectype v_vectype)) →
    wf_context C →
    wf_valtype t' →
    wf_instr (instr.SELECT none) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [t, t, valtype.I32]) [] (.mk_list [t])) →
    Instr_ok C (instr.SELECT none) (instrtype.mk_instrtype (.mk_list [t, t, valtype.I32]) [] (.mk_list [t]))
  | block (C : context) (bt : blocktype) (instr_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) (x_lst : List idx) :
    Blocktype_ok C bt (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) ++ C) instr_lst (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.BLOCK bt instr_lst) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    Instr_ok C (instr.BLOCK bt instr_lst) (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | loop (C : context) (bt : blocktype) (instr_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) (x_lst : List idx) :
    Blocktype_ok C bt (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_1_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) ++ C) instr_lst (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.LOOP bt instr_lst) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_1_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    Instr_ok C (instr.LOOP bt instr_lst) (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | if (C : context) (bt : blocktype) (instr_1_lst : List instr) (instr_2_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) (x_1_lst : List idx) (x_2_lst : List idx) :
    Blocktype_ok C bt (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) ++ C) instr_1_lst (instrtype.mk_instrtype (.mk_list t_1_lst) x_1_lst (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) ++ C) instr_2_lst (instrtype.mk_instrtype (.mk_list t_1_lst) x_2_lst (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.IFELSE bt instr_1_lst instr_2_lst) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_1_lst ++ [valtype.I32])) [] (.mk_list t_2_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) x_1_lst (.mk_list t_2_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) x_2_lst (.mk_list t_2_lst)) →
    Instr_ok C (instr.IFELSE bt instr_1_lst instr_2_lst) (instrtype.mk_instrtype (.mk_list (t_1_lst ++ [valtype.I32])) [] (.mk_list t_2_lst))
  | br (C : context) (l : labelidx) (t_1_lst : List valtype) (t_lst : List valtype) (t_2_lst : List valtype) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    (proj_list_0 valtype ((C.LABELS)[proj_uN_0 l]!)) = t_lst →
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.BR l) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instr_ok C (instr.BR l) (instrtype.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst))
  | br_if (C : context) (l : labelidx) (t_lst : List valtype) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    (proj_list_0 valtype ((C.LABELS)[proj_uN_0 l]!)) = t_lst →
    wf_context C →
    wf_instr (instr.BR_IF l) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype.I32])) [] (.mk_list t_lst)) →
    Instr_ok C (instr.BR_IF l) (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype.I32])) [] (.mk_list t_lst))
  | br_table (C : context) (l_lst : List labelidx) (l' : labelidx) (t_1_lst : List valtype) (t_lst : List valtype) (t_2_lst : List valtype) :
    Forall (fun l_elem => (proj_uN_0 l_elem) < (List.length (C.LABELS))) l_lst →
    Forall (fun l_elem => Resulttype_sub C (.mk_list t_lst) ((C.LABELS)[proj_uN_0 l_elem]!)) l_lst →
    (proj_uN_0 l') < (List.length (C.LABELS)) →
    Resulttype_sub C (.mk_list t_lst) ((C.LABELS)[proj_uN_0 l']!) →
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list (t_1_lst ++ (t_lst ++ [valtype.I32]))) [] (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.BR_TABLE l_lst l') →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_1_lst ++ (t_lst ++ [valtype.I32]))) [] (.mk_list t_2_lst)) →
    Instr_ok C (instr.BR_TABLE l_lst l') (instrtype.mk_instrtype (.mk_list (t_1_lst ++ (t_lst ++ [valtype.I32]))) [] (.mk_list t_2_lst))
  | br_on_null (C : context) (l : labelidx) (t_lst : List valtype) (ht : heaptype) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    (proj_list_0 valtype ((C.LABELS)[proj_uN_0 l]!)) = t_lst →
    Heaptype_ok C ht →
    wf_context C →
    wf_instr (instr.BR_ON_NULL l) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype.REF (some null.NULL) ht])) [] (.mk_list (t_lst ++ [valtype.REF none ht]))) →
    Instr_ok C (instr.BR_ON_NULL l) (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype.REF (some null.NULL) ht])) [] (.mk_list (t_lst ++ [valtype.REF none ht])))
  | br_on_non_null (C : context) (l : labelidx) (t_lst : List valtype) (ht : heaptype) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    ((C.LABELS)[proj_uN_0 l]!) = (.mk_list (t_lst ++ [valtype.REF (some null.NULL) ht])) →
    wf_context C →
    wf_instr (instr.BR_ON_NON_NULL l) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype.REF (some null.NULL) ht])) [] (.mk_list t_lst)) →
    Instr_ok C (instr.BR_ON_NON_NULL l) (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype.REF (some null.NULL) ht])) [] (.mk_list t_lst))
  | br_on_cast (C : context) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (t_lst : List valtype) (rt : reftype) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    ((C.LABELS)[proj_uN_0 l]!) = (.mk_list (t_lst ++ [valtype_reftype rt])) →
    Reftype_ok C rt_1 →
    Reftype_ok C rt_2 →
    Reftype_sub C rt_2 rt_1 →
    Reftype_sub C rt_2 rt →
    wf_context C →
    wf_reftype rt →
    wf_instr (instr.BR_ON_CAST l rt_1 rt_2) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype_reftype rt_1])) [] (.mk_list (t_lst ++ [valtype_reftype (diffrt rt_1 rt_2)]))) →
    Instr_ok C (instr.BR_ON_CAST l rt_1 rt_2) (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype_reftype rt_1])) [] (.mk_list (t_lst ++ [valtype_reftype (diffrt rt_1 rt_2)])))
  | br_on_cast_fail (C : context) (l : labelidx) (rt_1 : reftype) (rt_2 : reftype) (t_lst : List valtype) (rt : reftype) :
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    ((C.LABELS)[proj_uN_0 l]!) = (.mk_list (t_lst ++ [valtype_reftype rt])) →
    Reftype_ok C rt_1 →
    Reftype_ok C rt_2 →
    Reftype_sub C rt_2 rt_1 →
    Reftype_sub C (diffrt rt_1 rt_2) rt →
    wf_context C →
    wf_reftype rt →
    wf_reftype (diffrt rt_1 rt_2) →
    wf_instr (instr.BR_ON_CAST_FAIL l rt_1 rt_2) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype_reftype rt_1])) [] (.mk_list (t_lst ++ [valtype_reftype rt_2]))) →
    Instr_ok C (instr.BR_ON_CAST_FAIL l rt_1 rt_2) (instrtype.mk_instrtype (.mk_list (t_lst ++ [valtype_reftype rt_1])) [] (.mk_list (t_lst ++ [valtype_reftype rt_2])))
  | call (C : context) (x : idx) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    Expand ((C.FUNCS)[proj_uN_0 x]!) (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.CALL x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instr_ok C (instr.CALL x) (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | call_ref (C : context) (x : idx) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.CALL_REF (typeuse._IDX x)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_1_lst ++ [valtype.REF (some null.NULL) (heaptype._IDX x)])) [] (.mk_list t_2_lst)) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instr_ok C (instr.CALL_REF (typeuse._IDX x)) (instrtype.mk_instrtype (.mk_list (t_1_lst ++ [valtype.REF (some null.NULL) (heaptype._IDX x)])) [] (.mk_list t_2_lst))
  | call_indirect (C : context) (x : idx) (y : idx) (t_1_lst : List valtype) («at» : addrtype) (t_2_lst : List valtype) (lim : limits) (rt : reftype) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt) →
    Reftype_sub C rt (reftype.REF (some null.NULL) heaptype.FUNC) →
    (proj_uN_0 y) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 y]!) (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.CALL_INDIRECT x (typeuse._IDX y)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_1_lst ++ [valtype_addrtype «at»])) [] (.mk_list t_2_lst)) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt) →
    wf_reftype (reftype.REF (some null.NULL) heaptype.FUNC) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    Instr_ok C (instr.CALL_INDIRECT x (typeuse._IDX y)) (instrtype.mk_instrtype (.mk_list (t_1_lst ++ [valtype_addrtype «at»])) [] (.mk_list t_2_lst))
  | return (C : context) (t_1_lst : List valtype) (t_lst : List valtype) (t_2_lst : List valtype) :
    (C.RETURN) = (some (.mk_list t_lst)) →
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr instr.RETURN →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instr_ok C instr.RETURN (instrtype.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst))
  | return_call (C : context) (x : idx) (t_3_lst : List valtype) (t_1_lst : List valtype) (t_4_lst : List valtype) (t_2_lst : List valtype) (t'_2_lst : List valtype) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    Expand ((C.FUNCS)[proj_uN_0 x]!) (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    (C.RETURN) = (some (.mk_list t'_2_lst)) →
    Resulttype_sub C (.mk_list t_2_lst) (.mk_list t'_2_lst) →
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst)) →
    wf_context C →
    Forall (fun t'_2_elem => wf_valtype t'_2_elem) t'_2_lst →
    wf_instr (instr.RETURN_CALL x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_3_lst ++ t_1_lst)) [] (.mk_list t_4_lst)) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst)) →
    Instr_ok C (instr.RETURN_CALL x) (instrtype.mk_instrtype (.mk_list (t_3_lst ++ t_1_lst)) [] (.mk_list t_4_lst))
  | return_call_ref (C : context) (x : idx) (t_3_lst : List valtype) (t_1_lst : List valtype) (t_4_lst : List valtype) (t_2_lst : List valtype) (t'_2_lst : List valtype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    (C.RETURN) = (some (.mk_list t'_2_lst)) →
    Resulttype_sub C (.mk_list t_2_lst) (.mk_list t'_2_lst) →
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst)) →
    wf_context C →
    Forall (fun t'_2_elem => wf_valtype t'_2_elem) t'_2_lst →
    wf_instr (instr.RETURN_CALL_REF (typeuse._IDX x)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_3_lst ++ (t_1_lst ++ [valtype.REF (some null.NULL) (heaptype._IDX x)]))) [] (.mk_list t_4_lst)) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst)) →
    Instr_ok C (instr.RETURN_CALL_REF (typeuse._IDX x)) (instrtype.mk_instrtype (.mk_list (t_3_lst ++ (t_1_lst ++ [valtype.REF (some null.NULL) (heaptype._IDX x)]))) [] (.mk_list t_4_lst))
  | return_call_indirect (C : context) (x : idx) (y : idx) (t_3_lst : List valtype) (t_1_lst : List valtype) («at» : addrtype) (t_4_lst : List valtype) (lim : limits) (rt : reftype) (t_2_lst : List valtype) (t'_2_lst : List valtype) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt) →
    Reftype_sub C rt (reftype.REF (some null.NULL) heaptype.FUNC) →
    (proj_uN_0 y) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 y]!) (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    (C.RETURN) = (some (.mk_list t'_2_lst)) →
    Resulttype_sub C (.mk_list t_2_lst) (.mk_list t'_2_lst) →
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst)) →
    wf_context C →
    Forall (fun t'_2_elem => wf_valtype t'_2_elem) t'_2_lst →
    wf_instr (instr.RETURN_CALL_INDIRECT x (typeuse._IDX y)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_3_lst ++ (t_1_lst ++ [valtype_addrtype «at»]))) [] (.mk_list t_4_lst)) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt) →
    wf_reftype (reftype.REF (some null.NULL) heaptype.FUNC) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_3_lst) [] (.mk_list t_4_lst)) →
    Instr_ok C (instr.RETURN_CALL_INDIRECT x (typeuse._IDX y)) (instrtype.mk_instrtype (.mk_list (t_3_lst ++ (t_1_lst ++ [valtype_addrtype «at»]))) [] (.mk_list t_4_lst))
  | throw (C : context) (x : idx) (t_1_lst : List valtype) (t_lst : List valtype) (t_2_lst : List valtype) :
    (as_deftype ((C.TAGS)[proj_uN_0 x]!)) ≠ none →
    (proj_uN_0 x) < (List.length (C.TAGS)) →
    Expand (Option.get! (as_deftype ((C.TAGS)[proj_uN_0 x]!))) (comptype.FUNC (.mk_list t_lst) (.mk_list [])) →
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr (instr.THROW x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst)) →
    wf_comptype (comptype.FUNC (.mk_list t_lst) (.mk_list [])) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instr_ok C (instr.THROW x) (instrtype.mk_instrtype (.mk_list (t_1_lst ++ t_lst)) [] (.mk_list t_2_lst))
  | throw_ref (C : context) (t_1_lst : List valtype) (t_2_lst : List valtype) :
    Instrtype_ok C (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context C →
    wf_instr instr.THROW_REF →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_1_lst ++ [valtype.REF (some null.NULL) heaptype.EXN])) [] (.mk_list t_2_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instr_ok C instr.THROW_REF (instrtype.mk_instrtype (.mk_list (t_1_lst ++ [valtype.REF (some null.NULL) heaptype.EXN])) [] (.mk_list t_2_lst))
  | try_table (C : context) (bt : blocktype) (catch_lst : List «catch») (instr_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) (x_lst : List idx) :
    Blocktype_ok C bt (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    Instrs_ok (({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) ++ C) instr_lst (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    Forall (fun v_catch_elem => Catch_ok C v_catch_elem) catch_lst →
    wf_context C →
    wf_instr (instr.TRY_TABLE bt (list.mk_list catch_lst) instr_lst) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst)) →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := [.mk_list t_2_lst]
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    Instr_ok C (instr.TRY_TABLE bt (list.mk_list catch_lst) instr_lst) (instrtype.mk_instrtype (.mk_list t_1_lst) [] (.mk_list t_2_lst))
  | ref_null (C : context) (ht : heaptype) :
    Heaptype_ok C ht →
    wf_context C →
    wf_instr (instr.REF_NULL ht) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype.REF (some null.NULL) ht])) →
    Instr_ok C (instr.REF_NULL ht) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype.REF (some null.NULL) ht]))
  | ref_func (C : context) (x : idx) (dt : deftype) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) = dt →
    (List.length (C.REFS)) > 0 →
    List.contains (C.REFS) x →
    wf_context C →
    wf_instr (instr.REF_FUNC x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype.REF none (heaptype_deftype dt)])) →
    Instr_ok C (instr.REF_FUNC x) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype.REF none (heaptype_deftype dt)]))
  | ref_i31 (C : context) :
    wf_context C →
    wf_instr instr.REF_I31 →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.I32]) [] (.mk_list [valtype.REF none heaptype.I31])) →
    Instr_ok C instr.REF_I31 (instrtype.mk_instrtype (.mk_list [valtype.I32]) [] (.mk_list [valtype.REF none heaptype.I31]))
  | ref_is_null (C : context) (ht : heaptype) :
    Heaptype_ok C ht →
    wf_context C →
    wf_instr instr.REF_IS_NULL →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) ht]) [] (.mk_list [valtype.I32])) →
    Instr_ok C instr.REF_IS_NULL (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) ht]) [] (.mk_list [valtype.I32]))
  | ref_as_non_null (C : context) (ht : heaptype) :
    Heaptype_ok C ht →
    wf_context C →
    wf_instr instr.REF_AS_NON_NULL →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) ht]) [] (.mk_list [valtype.REF none ht])) →
    Instr_ok C instr.REF_AS_NON_NULL (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) ht]) [] (.mk_list [valtype.REF none ht]))
  | ref_eq (C : context) :
    wf_context C →
    wf_instr instr.REF_EQ →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) heaptype.EQ, valtype.REF (some null.NULL) heaptype.EQ]) [] (.mk_list [valtype.I32])) →
    Instr_ok C instr.REF_EQ (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) heaptype.EQ, valtype.REF (some null.NULL) heaptype.EQ]) [] (.mk_list [valtype.I32]))
  | ref_test (C : context) (rt : reftype) (rt' : reftype) :
    Reftype_ok C rt →
    Reftype_ok C rt' →
    Reftype_sub C rt rt' →
    wf_context C →
    wf_instr (instr.REF_TEST rt) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_reftype rt']) [] (.mk_list [valtype.I32])) →
    Instr_ok C (instr.REF_TEST rt) (instrtype.mk_instrtype (.mk_list [valtype_reftype rt']) [] (.mk_list [valtype.I32]))
  | ref_cast (C : context) (rt : reftype) (rt' : reftype) :
    Reftype_ok C rt →
    Reftype_ok C rt' →
    Reftype_sub C rt rt' →
    wf_context C →
    wf_instr (instr.REF_CAST rt) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_reftype rt']) [] (.mk_list [valtype_reftype rt])) →
    Instr_ok C (instr.REF_CAST rt) (instrtype.mk_instrtype (.mk_list [valtype_reftype rt']) [] (.mk_list [valtype_reftype rt]))
  | i31_get (C : context) (v_sx : sx) :
    wf_context C →
    wf_instr (instr.I31_GET v_sx) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) heaptype.I31]) [] (.mk_list [valtype.I32])) →
    Instr_ok C (instr.I31_GET v_sx) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) heaptype.I31]) [] (.mk_list [valtype.I32]))
  | struct_new (C : context) (x : idx) (zt_lst : List storagetype) (mut_opt_lst : List (Option «mut»)) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.STRUCT (list.mk_list (Map₂ (fun mut_opt_elem zt_elem => fieldtype.mk_fieldtype mut_opt_elem zt_elem) mut_opt_lst zt_lst))) →
    wf_context C →
    wf_instr (instr.STRUCT_NEW x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (Map (fun zt_elem => unpack zt_elem) zt_lst)) [] (.mk_list [valtype.REF none (heaptype._IDX x)])) →
    wf_comptype (comptype.STRUCT (list.mk_list (Map₂ (fun mut_opt_elem zt_elem => fieldtype.mk_fieldtype mut_opt_elem zt_elem) mut_opt_lst zt_lst))) →
    Instr_ok C (instr.STRUCT_NEW x) (instrtype.mk_instrtype (.mk_list (Map (fun zt_elem => unpack zt_elem) zt_lst)) [] (.mk_list [valtype.REF none (heaptype._IDX x)]))
  | struct_new_default (C : context) (x : idx) (mut_opt_lst : List (Option «mut»)) (zt_lst : List storagetype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.STRUCT (list.mk_list (Map₂ (fun mut_opt_elem zt_elem => fieldtype.mk_fieldtype mut_opt_elem zt_elem) mut_opt_lst zt_lst))) →
    Forall (fun zt_elem => Defaultable (unpack zt_elem)) zt_lst →
    wf_context C →
    Forall (fun zt_elem => wf_valtype (unpack zt_elem)) zt_lst →
    wf_instr (instr.STRUCT_NEW_DEFAULT x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype.REF none (heaptype._IDX x)])) →
    wf_comptype (comptype.STRUCT (list.mk_list (Map₂ (fun mut_opt_elem zt_elem => fieldtype.mk_fieldtype mut_opt_elem zt_elem) mut_opt_lst zt_lst))) →
    Instr_ok C (instr.STRUCT_NEW_DEFAULT x) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype.REF none (heaptype._IDX x)]))
  | struct_get (C : context) (sx_opt : Option sx) (x : idx) (i : fieldidx) (zt : storagetype) (ft_lst : List fieldtype) (mut_opt : Option «mut») :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.STRUCT (list.mk_list ft_lst)) →
    (proj_uN_0 i) < (List.length ft_lst) →
    ((ft_lst)[proj_uN_0 i]!) = (fieldtype.mk_fieldtype mut_opt zt) →
    ((sx_opt ≠ none) ↔ (is_packtype zt)) →
    wf_context C →
    wf_instr (instr.STRUCT_GET sx_opt x i) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x)]) [] (.mk_list [unpack zt])) →
    wf_comptype (comptype.STRUCT (list.mk_list ft_lst)) →
    wf_fieldtype (fieldtype.mk_fieldtype mut_opt zt) →
    Instr_ok C (instr.STRUCT_GET sx_opt x i) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x)]) [] (.mk_list [unpack zt]))
  | struct_set (C : context) (x : idx) (i : fieldidx) (zt : storagetype) (ft_lst : List fieldtype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.STRUCT (list.mk_list ft_lst)) →
    (proj_uN_0 i) < (List.length ft_lst) →
    ((ft_lst)[proj_uN_0 i]!) = (fieldtype.mk_fieldtype (some mut.MUT) zt) →
    wf_context C →
    wf_instr (instr.STRUCT_SET x i) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), unpack zt]) [] (.mk_list [])) →
    wf_comptype (comptype.STRUCT (list.mk_list ft_lst)) →
    wf_fieldtype (fieldtype.mk_fieldtype (some mut.MUT) zt) →
    Instr_ok C (instr.STRUCT_SET x i) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), unpack zt]) [] (.mk_list []))
  | array_new (C : context) (x : idx) (zt : storagetype) (mut_opt : Option «mut») :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    wf_context C →
    wf_instr (instr.ARRAY_NEW x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [unpack zt, valtype.I32]) [] (.mk_list [valtype.REF none (heaptype._IDX x)])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    Instr_ok C (instr.ARRAY_NEW x) (instrtype.mk_instrtype (.mk_list [unpack zt, valtype.I32]) [] (.mk_list [valtype.REF none (heaptype._IDX x)]))
  | array_new_default (C : context) (x : idx) (mut_opt : Option «mut») (zt : storagetype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    Defaultable (unpack zt) →
    wf_context C →
    wf_valtype (unpack zt) →
    wf_instr (instr.ARRAY_NEW_DEFAULT x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.I32]) [] (.mk_list [valtype.REF none (heaptype._IDX x)])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    Instr_ok C (instr.ARRAY_NEW_DEFAULT x) (instrtype.mk_instrtype (.mk_list [valtype.I32]) [] (.mk_list [valtype.REF none (heaptype._IDX x)]))
  | array_new_fixed (C : context) (x : idx) (v_n : n) (zt : storagetype) (mut_opt : Option «mut») :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    wf_context C →
    wf_instr (instr.ARRAY_NEW_FIXED x (uN.mk_uN v_n)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (List.replicate v_n (unpack zt))) [] (.mk_list [valtype.REF none (heaptype._IDX x)])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    Instr_ok C (instr.ARRAY_NEW_FIXED x (uN.mk_uN v_n)) (instrtype.mk_instrtype (.mk_list (List.replicate v_n (unpack zt))) [] (.mk_list [valtype.REF none (heaptype._IDX x)]))
  | array_new_elem (C : context) (x : idx) (y : idx) (mut_opt : Option «mut») (rt : reftype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt (storagetype_reftype rt))) →
    (proj_uN_0 y) < (List.length (C.ELEMS)) →
    Reftype_sub C ((C.ELEMS)[proj_uN_0 y]!) rt →
    wf_context C →
    wf_instr (instr.ARRAY_NEW_ELEM x y) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.I32, valtype.I32]) [] (.mk_list [valtype.REF none (heaptype._IDX x)])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt (storagetype_reftype rt))) →
    Instr_ok C (instr.ARRAY_NEW_ELEM x y) (instrtype.mk_instrtype (.mk_list [valtype.I32, valtype.I32]) [] (.mk_list [valtype.REF none (heaptype._IDX x)]))
  | array_new_data (C : context) (x : idx) (y : idx) (mut_opt : Option «mut») (zt : storagetype) (v_numtype : numtype) (v_vectype : vectype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    ((unpack zt) = (valtype_numtype v_numtype)) ∨ ((unpack zt) = (valtype_vectype v_vectype)) →
    (proj_uN_0 y) < (List.length (C.DATAS)) →
    ((C.DATAS)[proj_uN_0 y]!) = datatype.OK →
    wf_context C →
    wf_valtype (unpack zt) →
    wf_instr (instr.ARRAY_NEW_DATA x y) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.I32, valtype.I32]) [] (.mk_list [valtype.REF none (heaptype._IDX x)])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    Instr_ok C (instr.ARRAY_NEW_DATA x y) (instrtype.mk_instrtype (.mk_list [valtype.I32, valtype.I32]) [] (.mk_list [valtype.REF none (heaptype._IDX x)]))
  | array_get (C : context) (sx_opt : Option sx) (x : idx) (zt : storagetype) (mut_opt : Option «mut») :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    ((sx_opt ≠ none) ↔ (is_packtype zt)) →
    wf_context C →
    wf_instr (instr.ARRAY_GET sx_opt x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32]) [] (.mk_list [unpack zt])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt)) →
    Instr_ok C (instr.ARRAY_GET sx_opt x) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32]) [] (.mk_list [unpack zt]))
  | array_set (C : context) (x : idx) (zt : storagetype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt)) →
    wf_context C →
    wf_instr (instr.ARRAY_SET x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32, unpack zt]) [] (.mk_list [])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt)) →
    Instr_ok C (instr.ARRAY_SET x) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32, unpack zt]) [] (.mk_list []))
  | array_len (C : context) :
    wf_context C →
    wf_instr instr.ARRAY_LEN →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) heaptype.ARRAY]) [] (.mk_list [valtype.I32])) →
    Instr_ok C instr.ARRAY_LEN (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) heaptype.ARRAY]) [] (.mk_list [valtype.I32]))
  | array_fill (C : context) (x : idx) (zt : storagetype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt)) →
    wf_context C →
    wf_instr (instr.ARRAY_FILL x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32, unpack zt, valtype.I32]) [] (.mk_list [])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt)) →
    Instr_ok C (instr.ARRAY_FILL x) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32, unpack zt, valtype.I32]) [] (.mk_list []))
  | array_copy (C : context) (x_1 : idx) (x_2 : idx) (zt_1 : storagetype) (mut_opt : Option «mut») (zt_2 : storagetype) :
    (proj_uN_0 x_1) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x_1]!) (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt_1)) →
    (proj_uN_0 x_2) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x_2]!) (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt_2)) →
    Storagetype_sub C zt_2 zt_1 →
    wf_context C →
    wf_instr (instr.ARRAY_COPY x_1 x_2) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x_1), valtype.I32, valtype.REF (some null.NULL) (heaptype._IDX x_2), valtype.I32, valtype.I32]) [] (.mk_list [])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt_1)) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype mut_opt zt_2)) →
    Instr_ok C (instr.ARRAY_COPY x_1 x_2) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x_1), valtype.I32, valtype.REF (some null.NULL) (heaptype._IDX x_2), valtype.I32, valtype.I32]) [] (.mk_list []))
  | array_init_elem (C : context) (x : idx) (y : idx) (zt : storagetype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt)) →
    (proj_uN_0 y) < (List.length (C.ELEMS)) →
    Storagetype_sub C (storagetype_reftype ((C.ELEMS)[proj_uN_0 y]!)) zt →
    wf_context C →
    wf_instr (instr.ARRAY_INIT_ELEM x y) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32, valtype.I32, valtype.I32]) [] (.mk_list [])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt)) →
    Instr_ok C (instr.ARRAY_INIT_ELEM x y) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32, valtype.I32, valtype.I32]) [] (.mk_list []))
  | array_init_data (C : context) (x : idx) (y : idx) (zt : storagetype) (v_numtype : numtype) (v_vectype : vectype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt)) →
    ((unpack zt) = (valtype_numtype v_numtype)) ∨ ((unpack zt) = (valtype_vectype v_vectype)) →
    (proj_uN_0 y) < (List.length (C.DATAS)) →
    ((C.DATAS)[proj_uN_0 y]!) = datatype.OK →
    wf_context C →
    wf_valtype (unpack zt) →
    wf_instr (instr.ARRAY_INIT_DATA x y) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32, valtype.I32, valtype.I32]) [] (.mk_list [])) →
    wf_comptype (comptype.ARRAY (fieldtype.mk_fieldtype (some mut.MUT) zt)) →
    Instr_ok C (instr.ARRAY_INIT_DATA x y) (instrtype.mk_instrtype (.mk_list [valtype.REF (some null.NULL) (heaptype._IDX x), valtype.I32, valtype.I32, valtype.I32]) [] (.mk_list []))
  | extern_convert_any (C : context) (null_1_opt : Option null) (null_2_opt : Option null) :
    null_1_opt = null_2_opt →
    wf_context C →
    wf_instr instr.EXTERN_CONVERT_ANY →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF null_1_opt heaptype.ANY]) [] (.mk_list [valtype.REF null_2_opt heaptype.EXTERN])) →
    Instr_ok C instr.EXTERN_CONVERT_ANY (instrtype.mk_instrtype (.mk_list [valtype.REF null_1_opt heaptype.ANY]) [] (.mk_list [valtype.REF null_2_opt heaptype.EXTERN]))
  | any_convert_extern (C : context) (null_1_opt : Option null) (null_2_opt : Option null) :
    null_1_opt = null_2_opt →
    wf_context C →
    wf_instr instr.ANY_CONVERT_EXTERN →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.REF null_1_opt heaptype.EXTERN]) [] (.mk_list [valtype.REF null_2_opt heaptype.ANY])) →
    Instr_ok C instr.ANY_CONVERT_EXTERN (instrtype.mk_instrtype (.mk_list [valtype.REF null_1_opt heaptype.EXTERN]) [] (.mk_list [valtype.REF null_2_opt heaptype.ANY]))
  | local_get (C : context) (x : idx) (t : valtype) :
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) = (localtype.mk_localtype init.SET t) →
    wf_context C →
    wf_instr (instr.LOCAL_GET x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [t])) →
    wf_localtype (localtype.mk_localtype init.SET t) →
    Instr_ok C (instr.LOCAL_GET x) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [t]))
  | local_set (C : context) (x : idx) (t : valtype) (v_init : init) :
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) = (localtype.mk_localtype v_init t) →
    wf_context C →
    wf_instr (instr.LOCAL_SET x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [t]) [x] (.mk_list [])) →
    wf_localtype (localtype.mk_localtype v_init t) →
    Instr_ok C (instr.LOCAL_SET x) (instrtype.mk_instrtype (.mk_list [t]) [x] (.mk_list []))
  | local_tee (C : context) (x : idx) (t : valtype) (v_init : init) :
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) = (localtype.mk_localtype v_init t) →
    wf_context C →
    wf_instr (instr.LOCAL_TEE x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [t]) [x] (.mk_list [t])) →
    wf_localtype (localtype.mk_localtype v_init t) →
    Instr_ok C (instr.LOCAL_TEE x) (instrtype.mk_instrtype (.mk_list [t]) [x] (.mk_list [t]))
  | global_get (C : context) (x : idx) (t : valtype) (mut_opt : Option «mut») :
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) = (globaltype.mk_globaltype mut_opt t) →
    wf_context C →
    wf_instr (instr.GLOBAL_GET x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [t])) →
    wf_globaltype (globaltype.mk_globaltype mut_opt t) →
    Instr_ok C (instr.GLOBAL_GET x) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [t]))
  | global_set (C : context) (x : idx) (t : valtype) :
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) = (globaltype.mk_globaltype (some mut.MUT) t) →
    wf_context C →
    wf_instr (instr.GLOBAL_SET x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [t]) [] (.mk_list [])) →
    wf_globaltype (globaltype.mk_globaltype (some mut.MUT) t) →
    Instr_ok C (instr.GLOBAL_SET x) (instrtype.mk_instrtype (.mk_list [t]) [] (.mk_list []))
  | table_get (C : context) (x : idx) («at» : addrtype) (rt : reftype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_GET x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype_reftype rt])) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt) →
    Instr_ok C (instr.TABLE_GET x) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype_reftype rt]))
  | table_set (C : context) (x : idx) («at» : addrtype) (rt : reftype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_SET x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype_reftype rt]) [] (.mk_list [])) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt) →
    Instr_ok C (instr.TABLE_SET x) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype_reftype rt]) [] (.mk_list []))
  | table_size (C : context) (x : idx) («at» : addrtype) (lim : limits) (rt : reftype) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_SIZE x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype_addrtype «at»])) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt) →
    Instr_ok C (instr.TABLE_SIZE x) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype_addrtype «at»]))
  | table_grow (C : context) (x : idx) (rt : reftype) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_GROW x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_reftype rt, valtype_addrtype «at»]) [] (.mk_list [valtype_addrtype «at»])) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt) →
    Instr_ok C (instr.TABLE_GROW x) (instrtype.mk_instrtype (.mk_list [valtype_reftype rt, valtype_addrtype «at»]) [] (.mk_list [valtype_addrtype «at»]))
  | table_fill (C : context) (x : idx) («at» : addrtype) (rt : reftype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt) →
    wf_context C →
    wf_instr (instr.TABLE_FILL x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype_reftype rt, valtype_addrtype «at»]) [] (.mk_list [])) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt) →
    Instr_ok C (instr.TABLE_FILL x) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype_reftype rt, valtype_addrtype «at»]) [] (.mk_list []))
  | table_copy (C : context) (x_1 : idx) (x_2 : idx) (at_1 : addrtype) (at_2 : addrtype) (lim_1 : limits) (rt_1 : reftype) (lim_2 : limits) (rt_2 : reftype) :
    (proj_uN_0 x_1) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x_1]!) = (tabletype.mk_tabletype at_1 lim_1 rt_1) →
    (proj_uN_0 x_2) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x_2]!) = (tabletype.mk_tabletype at_2 lim_2 rt_2) →
    Reftype_sub C rt_2 rt_1 →
    wf_context C →
    wf_instr (instr.TABLE_COPY x_1 x_2) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype at_1, valtype_addrtype at_2, valtype_addrtype (minat at_1 at_2)]) [] (.mk_list [])) →
    wf_tabletype (tabletype.mk_tabletype at_1 lim_1 rt_1) →
    wf_tabletype (tabletype.mk_tabletype at_2 lim_2 rt_2) →
    Instr_ok C (instr.TABLE_COPY x_1 x_2) (instrtype.mk_instrtype (.mk_list [valtype_addrtype at_1, valtype_addrtype at_2, valtype_addrtype (minat at_1 at_2)]) [] (.mk_list []))
  | table_init (C : context) (x : idx) (y : idx) («at» : addrtype) (lim : limits) (rt_1 : reftype) (rt_2 : reftype) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt_1) →
    (proj_uN_0 y) < (List.length (C.ELEMS)) →
    ((C.ELEMS)[proj_uN_0 y]!) = rt_2 →
    Reftype_sub C rt_2 rt_1 →
    wf_context C →
    wf_reftype rt_2 →
    wf_instr (instr.TABLE_INIT x y) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.I32, valtype.I32]) [] (.mk_list [])) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt_1) →
    Instr_ok C (instr.TABLE_INIT x y) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.I32, valtype.I32]) [] (.mk_list []))
  | elem_drop (C : context) (x : idx) (rt : reftype) :
    (proj_uN_0 x) < (List.length (C.ELEMS)) →
    ((C.ELEMS)[proj_uN_0 x]!) = rt →
    wf_context C →
    wf_reftype rt →
    wf_instr (instr.ELEM_DROP x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [])) →
    Instr_ok C (instr.ELEM_DROP x) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list []))
  | memory_size (C : context) (x : idx) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    wf_context C →
    wf_instr (instr.MEMORY_SIZE x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype_addrtype «at»])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.MEMORY_SIZE x) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype_addrtype «at»]))
  | memory_grow (C : context) (x : idx) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    wf_context C →
    wf_instr (instr.MEMORY_GROW x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype_addrtype «at»])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.MEMORY_GROW x) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype_addrtype «at»]))
  | memory_fill (C : context) (x : idx) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    wf_context C →
    wf_instr (instr.MEMORY_FILL x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.I32, valtype_addrtype «at»]) [] (.mk_list [])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.MEMORY_FILL x) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.I32, valtype_addrtype «at»]) [] (.mk_list []))
  | memory_copy (C : context) (x_1 : idx) (x_2 : idx) (at_1 : addrtype) (at_2 : addrtype) (lim_1 : limits) (lim_2 : limits) :
    (proj_uN_0 x_1) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x_1]!) = (memtype.PAGE at_1 lim_1) →
    (proj_uN_0 x_2) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x_2]!) = (memtype.PAGE at_2 lim_2) →
    wf_context C →
    wf_instr (instr.MEMORY_COPY x_1 x_2) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype at_1, valtype_addrtype at_2, valtype_addrtype (minat at_1 at_2)]) [] (.mk_list [])) →
    wf_memtype (memtype.PAGE at_1 lim_1) →
    wf_memtype (memtype.PAGE at_2 lim_2) →
    Instr_ok C (instr.MEMORY_COPY x_1 x_2) (instrtype.mk_instrtype (.mk_list [valtype_addrtype at_1, valtype_addrtype at_2, valtype_addrtype (minat at_1 at_2)]) [] (.mk_list []))
  | memory_init (C : context) (x : idx) (y : idx) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    (proj_uN_0 y) < (List.length (C.DATAS)) →
    ((C.DATAS)[proj_uN_0 y]!) = datatype.OK →
    wf_context C →
    wf_instr (instr.MEMORY_INIT x y) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.I32, valtype.I32]) [] (.mk_list [])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.MEMORY_INIT x y) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.I32, valtype.I32]) [] (.mk_list []))
  | data_drop (C : context) (x : idx) :
    (proj_uN_0 x) < (List.length (C.DATAS)) →
    ((C.DATAS)[proj_uN_0 x]!) = datatype.OK →
    wf_context C →
    wf_instr (instr.DATA_DROP x) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [])) →
    Instr_ok C (instr.DATA_DROP x) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list []))
  | load_val (C : context) (nt : numtype) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» (size nt) →
    wf_context C →
    wf_instr (instr.LOAD nt none x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype_numtype nt])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.LOAD nt none x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype_numtype nt]))
  | load_pack (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» v_M →
    wf_context C →
    wf_instr (instr.LOAD (numtype_addrtype v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_M) v_sx))) x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype_addrtype v_Inn])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.LOAD (numtype_addrtype v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_M) v_sx))) x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype_addrtype v_Inn]))
  | store_val (C : context) (nt : numtype) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» (size nt) →
    wf_context C →
    wf_instr (instr.STORE nt none x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype_numtype nt]) [] (.mk_list [])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.STORE nt none x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype_numtype nt]) [] (.mk_list []))
  | store_pack (C : context) (v_Inn : Inn) (v_M : M) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» v_M →
    wf_context C →
    wf_instr (instr.STORE (numtype_addrtype v_Inn) (some (storeop_.mk_storeop__0 v_Inn (storeop_Inn.mk_storeop_Inn (sz.mk_sz v_M)))) x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype_addrtype v_Inn]) [] (.mk_list [])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.STORE (numtype_addrtype v_Inn) (some (storeop_.mk_storeop__0 v_Inn (storeop_Inn.mk_storeop_Inn (sz.mk_sz v_M)))) x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype_addrtype v_Inn]) [] (.mk_list []))
  | vload_val (C : context) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» (vsize vectype.V128) →
    wf_context C →
    wf_instr (instr.VLOAD vectype.V128 none x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype.V128])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.VLOAD vectype.V128 none x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype.V128]))
  | vload_pack (C : context) (v_M : M) (v_N : N) (v_sx : sx) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» (v_M * v_N) →
    wf_context C →
    wf_instr (instr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx)) x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype.V128])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.VLOAD vectype.V128 (some (vloadop_.SHAPEX_ (sz.mk_sz v_M) v_N v_sx)) x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype.V128]))
  | vload_splat (C : context) (v_N : N) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» v_N →
    wf_context C →
    wf_instr (instr.VLOAD vectype.V128 (some (vloadop_.SPLAT (sz.mk_sz v_N))) x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype.V128])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.VLOAD vectype.V128 (some (vloadop_.SPLAT (sz.mk_sz v_N))) x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype.V128]))
  | vload_zero (C : context) (v_N : N) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» v_N →
    wf_context C →
    wf_instr (instr.VLOAD vectype.V128 (some (vloadop_.ZERO (sz.mk_sz v_N))) x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype.V128])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.VLOAD vectype.V128 (some (vloadop_.ZERO (sz.mk_sz v_N))) x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at»]) [] (.mk_list [valtype.V128]))
  | vload_lane (C : context) (v_N : N) (x : idx) (v_memarg : memarg) (i : laneidx) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» v_N →
    ((proj_uN_0 i) : Rat) < ((128 : Rat) / (v_N : Rat)) →
    wf_context C →
    wf_instr (instr.VLOAD_LANE vectype.V128 (sz.mk_sz v_N) x v_memarg i) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.V128]) [] (.mk_list [valtype.V128])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.VLOAD_LANE vectype.V128 (sz.mk_sz v_N) x v_memarg i) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.V128]) [] (.mk_list [valtype.V128]))
  | vstore (C : context) (x : idx) (v_memarg : memarg) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» (vsize vectype.V128) →
    wf_context C →
    wf_instr (instr.VSTORE vectype.V128 x v_memarg) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.V128]) [] (.mk_list [])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.VSTORE vectype.V128 x v_memarg) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.V128]) [] (.mk_list []))
  | vstore_lane (C : context) (v_N : N) (x : idx) (v_memarg : memarg) (i : laneidx) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Memarg_ok v_memarg «at» v_N →
    ((proj_uN_0 i) : Rat) < ((128 : Rat) / (v_N : Rat)) →
    wf_context C →
    wf_instr (instr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) x v_memarg i) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.V128]) [] (.mk_list [])) →
    wf_memtype (memtype.PAGE «at» lim) →
    Instr_ok C (instr.VSTORE_LANE vectype.V128 (sz.mk_sz v_N) x v_memarg i) (instrtype.mk_instrtype (.mk_list [valtype_addrtype «at», valtype.V128]) [] (.mk_list []))
  | const (C : context) (nt : numtype) (c_nt : num_) :
    wf_context C →
    wf_instr (instr.CONST nt c_nt) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype_numtype nt])) →
    Instr_ok C (instr.CONST nt c_nt) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype_numtype nt]))
  | unop (C : context) (nt : numtype) (unop_nt : unop_) :
    wf_context C →
    wf_instr (instr.UNOP nt unop_nt) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_numtype nt]) [] (.mk_list [valtype_numtype nt])) →
    Instr_ok C (instr.UNOP nt unop_nt) (instrtype.mk_instrtype (.mk_list [valtype_numtype nt]) [] (.mk_list [valtype_numtype nt]))
  | binop (C : context) (nt : numtype) (binop_nt : binop_) :
    wf_context C →
    wf_instr (instr.BINOP nt binop_nt) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_numtype nt, valtype_numtype nt]) [] (.mk_list [valtype_numtype nt])) →
    Instr_ok C (instr.BINOP nt binop_nt) (instrtype.mk_instrtype (.mk_list [valtype_numtype nt, valtype_numtype nt]) [] (.mk_list [valtype_numtype nt]))
  | testop (C : context) (nt : numtype) (testop_nt : testop_) :
    wf_context C →
    wf_instr (instr.TESTOP nt testop_nt) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_numtype nt]) [] (.mk_list [valtype.I32])) →
    Instr_ok C (instr.TESTOP nt testop_nt) (instrtype.mk_instrtype (.mk_list [valtype_numtype nt]) [] (.mk_list [valtype.I32]))
  | relop (C : context) (nt : numtype) (relop_nt : relop_) :
    wf_context C →
    wf_instr (instr.RELOP nt relop_nt) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_numtype nt, valtype_numtype nt]) [] (.mk_list [valtype.I32])) →
    Instr_ok C (instr.RELOP nt relop_nt) (instrtype.mk_instrtype (.mk_list [valtype_numtype nt, valtype_numtype nt]) [] (.mk_list [valtype.I32]))
  | cvtop (C : context) (nt_1 : numtype) (nt_2 : numtype) (cvtop : cvtop__) :
    wf_context C →
    wf_instr (instr.CVTOP nt_1 nt_2 cvtop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_numtype nt_2]) [] (.mk_list [valtype_numtype nt_1])) →
    Instr_ok C (instr.CVTOP nt_1 nt_2 cvtop) (instrtype.mk_instrtype (.mk_list [valtype_numtype nt_2]) [] (.mk_list [valtype_numtype nt_1]))
  | vconst (C : context) (c : vec_) :
    wf_context C →
    wf_instr (instr.VCONST vectype.V128 c) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VCONST vectype.V128 c) (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [valtype.V128]))
  | vvunop (C : context) (v_vvunop : vvunop) :
    wf_context C →
    wf_instr (instr.VVUNOP vectype.V128 v_vvunop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VVUNOP vectype.V128 v_vvunop) (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.V128]))
  | vvbinop (C : context) (v_vvbinop : vvbinop) :
    wf_context C →
    wf_instr (instr.VVBINOP vectype.V128 v_vvbinop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VVBINOP vectype.V128 v_vvbinop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vvternop (C : context) (v_vvternop : vvternop) :
    wf_context C →
    wf_instr (instr.VVTERNOP vectype.V128 v_vvternop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VVTERNOP vectype.V128 v_vvternop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vvtestop (C : context) (v_vvtestop : vvtestop) :
    wf_context C →
    wf_instr (instr.VVTESTOP vectype.V128 v_vvtestop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.I32])) →
    Instr_ok C (instr.VVTESTOP vectype.V128 v_vvtestop) (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.I32]))
  | vunop (C : context) (sh : shape) (vunop : vunop_) :
    wf_context C →
    wf_instr (instr.VUNOP sh vunop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VUNOP sh vunop) (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.V128]))
  | vbinop (C : context) (sh : shape) (vbinop : vbinop_) :
    wf_context C →
    wf_instr (instr.VBINOP sh vbinop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VBINOP sh vbinop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vternop (C : context) (sh : shape) (vternop : vternop_) :
    wf_context C →
    wf_instr (instr.VTERNOP sh vternop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VTERNOP sh vternop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vtestop (C : context) (sh : shape) (vtestop : vtestop_) :
    wf_context C →
    wf_instr (instr.VTESTOP sh vtestop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.I32])) →
    Instr_ok C (instr.VTESTOP sh vtestop) (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.I32]))
  | vrelop (C : context) (sh : shape) (vrelop : vrelop_) :
    wf_context C →
    wf_instr (instr.VRELOP sh vrelop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VRELOP sh vrelop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vshiftop (C : context) (sh : ishape) (vshiftop : vshiftop_) :
    wf_context C →
    wf_instr (instr.VSHIFTOP sh vshiftop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.I32]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VSHIFTOP sh vshiftop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.I32]) [] (.mk_list [valtype.V128]))
  | vbitmask (C : context) (sh : ishape) :
    wf_context C →
    wf_instr (instr.VBITMASK sh) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.I32])) →
    Instr_ok C (instr.VBITMASK sh) (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.I32]))
  | vswizzlop (C : context) (sh : bshape) (vswizzlop : vswizzlop_) :
    wf_context C →
    wf_instr (instr.VSWIZZLOP sh vswizzlop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VSWIZZLOP sh vswizzlop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vshuffle (C : context) (sh : bshape) (i_lst : List laneidx) :
    Forall (fun i_elem => (proj_uN_0 i_elem) < (2 * (proj_dim_0 (fun_dim (proj_bshape_0 sh))))) i_lst →
    wf_context C →
    wf_dim (fun_dim (proj_bshape_0 sh)) →
    wf_instr (instr.VSHUFFLE sh i_lst) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VSHUFFLE sh i_lst) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vsplat (C : context) (sh : shape) :
    wf_context C →
    wf_instr (instr.VSPLAT sh) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype_numtype (unpackshape sh)]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VSPLAT sh) (instrtype.mk_instrtype (.mk_list [valtype_numtype (unpackshape sh)]) [] (.mk_list [valtype.V128]))
  | vextract_lane (C : context) (sh : shape) (sx_opt : Option sx) (i : laneidx) :
    (proj_uN_0 i) < (proj_dim_0 (fun_dim sh)) →
    wf_context C →
    wf_dim (fun_dim sh) →
    wf_instr (instr.VEXTRACT_LANE sh sx_opt i) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype_numtype (unpackshape sh)])) →
    Instr_ok C (instr.VEXTRACT_LANE sh sx_opt i) (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype_numtype (unpackshape sh)]))
  | vreplace_lane (C : context) (sh : shape) (i : laneidx) :
    (proj_uN_0 i) < (proj_dim_0 (fun_dim sh)) →
    wf_context C →
    wf_dim (fun_dim sh) →
    wf_instr (instr.VREPLACE_LANE sh i) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype_numtype (unpackshape sh)]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VREPLACE_LANE sh i) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype_numtype (unpackshape sh)]) [] (.mk_list [valtype.V128]))
  | vextunop (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextunop : vextunop__) :
    wf_context C →
    wf_instr (instr.VEXTUNOP sh_1 sh_2 vextunop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VEXTUNOP sh_1 sh_2 vextunop) (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.V128]))
  | vextbinop (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextbinop : vextbinop__) :
    wf_context C →
    wf_instr (instr.VEXTBINOP sh_1 sh_2 vextbinop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VEXTBINOP sh_1 sh_2 vextbinop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vextternop (C : context) (sh_1 : ishape) (sh_2 : ishape) (vextternop : vextternop__) :
    wf_context C →
    wf_instr (instr.VEXTTERNOP sh_1 sh_2 vextternop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VEXTTERNOP sh_1 sh_2 vextternop) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vnarrow (C : context) (sh_1 : ishape) (sh_2 : ishape) (v_sx : sx) :
    wf_context C →
    wf_instr (instr.VNARROW sh_1 sh_2 v_sx) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VNARROW sh_1 sh_2 v_sx) (instrtype.mk_instrtype (.mk_list [valtype.V128, valtype.V128]) [] (.mk_list [valtype.V128]))
  | vcvtop (C : context) (sh_1 : shape) (sh_2 : shape) (vcvtop : vcvtop__) :
    wf_context C →
    wf_instr (instr.VCVTOP sh_1 sh_2 vcvtop) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.V128])) →
    Instr_ok C (instr.VCVTOP sh_1 sh_2 vcvtop) (instrtype.mk_instrtype (.mk_list [valtype.V128]) [] (.mk_list [valtype.V128]))

inductive Instrs_ok : context → List instr → instrtype → Prop where
  | empty (C : context) :
    wf_context C →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list [])) →
    Instrs_ok C [] (instrtype.mk_instrtype (.mk_list []) [] (.mk_list []))
  | seq (C : context) (instr_1 : instr) (instr_2_lst : List instr) (t_1_lst : List valtype) (x_1_lst : List idx) (x_2_lst : List idx) (t_3_lst : List valtype) (t_2_lst : List valtype) (init_lst : List init) (t_lst : List valtype) (var_0 : Option context) :
    fun_with_locals C x_1_lst (Map (fun t_elem => localtype.mk_localtype init.SET t_elem) t_lst) var_0 →
    Instr_ok C instr_1 (instrtype.mk_instrtype (.mk_list t_1_lst) x_1_lst (.mk_list t_2_lst)) →
    (List.length init_lst) = (List.length t_lst) →
    (List.length init_lst) = (List.length x_1_lst) →
    Forall (fun x_1_elem => (proj_uN_0 x_1_elem) < (List.length (C.LOCALS))) x_1_lst →
    Forall₃ (fun v_init_elem t_elem x_1_elem => ((C.LOCALS)[proj_uN_0 x_1_elem]!) = (localtype.mk_localtype v_init_elem t_elem)) init_lst t_lst x_1_lst →
    var_0 ≠ none →
    Instrs_ok (Option.get! var_0) instr_2_lst (instrtype.mk_instrtype (.mk_list t_2_lst) x_2_lst (.mk_list t_3_lst)) →
    wf_context C →
    wf_instr instr_1 →
    Forall (fun instr_2_elem => wf_instr instr_2_elem) instr_2_lst →
    wf_context (Option.get! var_0) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) (x_1_lst ++ x_2_lst) (.mk_list t_3_lst)) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) x_1_lst (.mk_list t_2_lst)) →
    Forall₂ (fun v_init_elem t_elem => wf_localtype (localtype.mk_localtype v_init_elem t_elem)) init_lst t_lst →
    Forall (fun t_elem => wf_localtype (localtype.mk_localtype init.SET t_elem)) t_lst →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_2_lst) x_2_lst (.mk_list t_3_lst)) →
    Instrs_ok C ([instr_1] ++ instr_2_lst) (instrtype.mk_instrtype (.mk_list t_1_lst) (x_1_lst ++ x_2_lst) (.mk_list t_3_lst))
  | sub (C : context) (instr_lst : List instr) (it' : instrtype) (it : instrtype) :
    Instrs_ok C instr_lst it →
    Instrtype_sub C it it' →
    Instrtype_ok C it' →
    wf_context C →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instrtype it' →
    wf_instrtype it →
    Instrs_ok C instr_lst it'
  | frame (C : context) (instr_lst : List instr) (t_lst : List valtype) (t_1_lst : List valtype) (x_lst : List idx) (t_2_lst : List valtype) :
    Instrs_ok C instr_lst (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    Resulttype_ok C (.mk_list t_lst) →
    wf_context C →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instrtype (instrtype.mk_instrtype (.mk_list (t_lst ++ t_1_lst)) x_lst (.mk_list (t_lst ++ t_2_lst))) →
    wf_instrtype (instrtype.mk_instrtype (.mk_list t_1_lst) x_lst (.mk_list t_2_lst)) →
    Instrs_ok C instr_lst (instrtype.mk_instrtype (.mk_list (t_lst ++ t_1_lst)) x_lst (.mk_list (t_lst ++ t_2_lst)))


end

inductive Expr_ok : context → expr → resulttype → Prop where
  | mk_Expr_ok (C : context) (instr_lst : List instr) (t_lst : List valtype) :
    Instrs_ok C instr_lst (instrtype.mk_instrtype (.mk_list []) [] (.mk_list t_lst)) →
    wf_context C →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instrtype (instrtype.mk_instrtype (.mk_list []) [] (.mk_list t_lst)) →
    Expr_ok C instr_lst (.mk_list t_lst)


inductive Nondefaultable : valtype → Prop where
  | mk_Nondefaultable (t : valtype) :
    (default_ t) ≠ none →
    (Option.get! (default_ t)) = none →
    wf_valtype t →
    Forall (fun iter_elem => wf_val iter_elem) (Option.toList (Option.get! (default_ t))) →
    Nondefaultable t


inductive Instr_const : context → instr → Prop where
  | const (C : context) (nt : numtype) (c_nt : num_) :
    wf_context C →
    wf_instr (instr.CONST nt c_nt) →
    Instr_const C (instr.CONST nt c_nt)
  | vconst (C : context) (vt : vectype) (c_vt : vec_) :
    wf_context C →
    wf_instr (instr.VCONST vt c_vt) →
    Instr_const C (instr.VCONST vt c_vt)
  | ref_null (C : context) (ht : heaptype) :
    wf_context C →
    wf_instr (instr.REF_NULL ht) →
    Instr_const C (instr.REF_NULL ht)
  | ref_i31 (C : context) :
    wf_context C →
    wf_instr instr.REF_I31 →
    Instr_const C instr.REF_I31
  | ref_func (C : context) (x : idx) :
    wf_context C →
    wf_instr (instr.REF_FUNC x) →
    Instr_const C (instr.REF_FUNC x)
  | struct_new (C : context) (x : idx) :
    wf_context C →
    wf_instr (instr.STRUCT_NEW x) →
    Instr_const C (instr.STRUCT_NEW x)
  | struct_new_default (C : context) (x : idx) :
    wf_context C →
    wf_instr (instr.STRUCT_NEW_DEFAULT x) →
    Instr_const C (instr.STRUCT_NEW_DEFAULT x)
  | array_new (C : context) (x : idx) :
    wf_context C →
    wf_instr (instr.ARRAY_NEW x) →
    Instr_const C (instr.ARRAY_NEW x)
  | array_new_default (C : context) (x : idx) :
    wf_context C →
    wf_instr (instr.ARRAY_NEW_DEFAULT x) →
    Instr_const C (instr.ARRAY_NEW_DEFAULT x)
  | array_new_fixed (C : context) (x : idx) (v_n : n) :
    wf_context C →
    wf_instr (instr.ARRAY_NEW_FIXED x (uN.mk_uN v_n)) →
    Instr_const C (instr.ARRAY_NEW_FIXED x (uN.mk_uN v_n))
  | any_convert_extern (C : context) :
    wf_context C →
    wf_instr instr.ANY_CONVERT_EXTERN →
    Instr_const C instr.ANY_CONVERT_EXTERN
  | extern_convert_any (C : context) :
    wf_context C →
    wf_instr instr.EXTERN_CONVERT_ANY →
    Instr_const C instr.EXTERN_CONVERT_ANY
  | global_get (C : context) (x : idx) (t : valtype) :
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) = (globaltype.mk_globaltype none t) →
    wf_context C →
    wf_instr (instr.GLOBAL_GET x) →
    wf_globaltype (globaltype.mk_globaltype none t) →
    Instr_const C (instr.GLOBAL_GET x)
  | binop (C : context) (v_Inn : Inn) (binop : binop_) :
    (List.length [addrtype.I32, addrtype.I64]) > 0 →
    List.contains [addrtype.I32, addrtype.I64] v_Inn →
    (List.length [binop_.mk_binop__0 v_Inn binop_Inn.ADD, binop_.mk_binop__0 v_Inn binop_Inn.SUB, binop_.mk_binop__0 v_Inn binop_Inn.MUL]) > 0 →
    List.contains [binop_.mk_binop__0 v_Inn binop_Inn.ADD, binop_.mk_binop__0 v_Inn binop_Inn.SUB, binop_.mk_binop__0 v_Inn binop_Inn.MUL] binop →
    wf_context C →
    wf_instr (instr.BINOP (numtype_addrtype v_Inn) binop) →
    wf_binop_ (numtype_addrtype v_Inn) (binop_.mk_binop__0 v_Inn binop_Inn.ADD) →
    wf_binop_ (numtype_addrtype v_Inn) (binop_.mk_binop__0 v_Inn binop_Inn.SUB) →
    wf_binop_ (numtype_addrtype v_Inn) (binop_.mk_binop__0 v_Inn binop_Inn.MUL) →
    Instr_const C (instr.BINOP (numtype_addrtype v_Inn) binop)


inductive Expr_const : context → expr → Prop where
  | mk_Expr_const (C : context) (instr_lst : List instr) :
    Forall (fun v_instr_elem => Instr_const C v_instr_elem) instr_lst →
    wf_context C →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    Expr_const C instr_lst


inductive Expr_ok_const : context → expr → valtype → Prop where
  | mk_Expr_ok_const (C : context) (v_expr : expr) (t : valtype) :
    Expr_ok C v_expr (.mk_list [t]) →
    Expr_const C v_expr →
    wf_context C →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_valtype t →
    Expr_ok_const C v_expr t


inductive Type_ok : context → type → List deftype → Prop where
  | mk_Type_ok (C : context) (v_rectype : rectype) (dt_lst : List deftype) (x : idx) (var_0 : List deftype) :
    fun_rolldt x v_rectype var_0 →
    (proj_uN_0 x) = (List.length (C.TYPES)) →
    dt_lst = var_0 →
    Rectype_ok (C ++ ({
      TYPES := dt_lst
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    })) v_rectype (oktypeidx.OK x) →
    wf_context C →
    wf_context ({
      TYPES := dt_lst
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    wf_oktypeidx (oktypeidx.OK x) →
    Type_ok C (type.TYPE v_rectype) dt_lst


inductive Tag_ok : context → tag → tagtype → Prop where
  | mk_Tag_ok (C : context) (v_tagtype : tagtype) (var_0 : tagtype) :
    fun_clos_tagtype C v_tagtype var_0 →
    Tagtype_ok C v_tagtype →
    wf_context C →
    wf_typeuse var_0 →
    wf_tag (tag.TAG v_tagtype) →
    Tag_ok C (tag.TAG v_tagtype) var_0


inductive Global_ok : context → global → globaltype → Prop where
  | mk_Global_ok (C : context) (v_globaltype : globaltype) (v_expr : expr) (t : valtype) :
    Globaltype_ok C v_globaltype →
    v_globaltype = (globaltype.mk_globaltype (some mut.MUT) t) →
    Expr_ok_const C v_expr t →
    wf_context C →
    wf_global (global.GLOBAL v_globaltype v_expr) →
    wf_globaltype (globaltype.mk_globaltype (some mut.MUT) t) →
    Global_ok C (global.GLOBAL v_globaltype v_expr) v_globaltype


inductive Mem_ok : context → mem → memtype → Prop where
  | mk_Mem_ok (C : context) (v_memtype : memtype) :
    Memtype_ok C v_memtype →
    wf_context C →
    wf_mem (mem.MEMORY v_memtype) →
    Mem_ok C (mem.MEMORY v_memtype) v_memtype


inductive Table_ok : context → table → tabletype → Prop where
  | mk_Table_ok (C : context) (v_tabletype : tabletype) (v_expr : expr) («at» : addrtype) (lim : limits) (rt : reftype) :
    Tabletype_ok C v_tabletype →
    v_tabletype = (tabletype.mk_tabletype «at» lim rt) →
    Expr_ok_const C v_expr (valtype_reftype rt) →
    wf_context C →
    wf_table (table.TABLE v_tabletype v_expr) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt) →
    Table_ok C (table.TABLE v_tabletype v_expr) v_tabletype


inductive Local_ok : context → «local» → localtype → Prop where
  | set (C : context) (t : valtype) :
    Defaultable t →
    wf_context C →
    wf_local (local.LOCAL t) →
    wf_localtype (localtype.mk_localtype init.SET t) →
    Local_ok C (local.LOCAL t) (localtype.mk_localtype init.SET t)
  | unset (C : context) (t : valtype) :
    Nondefaultable t →
    wf_context C →
    wf_local (local.LOCAL t) →
    wf_localtype (localtype.mk_localtype init.UNSET t) →
    Local_ok C (local.LOCAL t) (localtype.mk_localtype init.UNSET t)


inductive Func_ok : context → func → deftype → Prop where
  | mk_Func_ok (C : context) (x : idx) (local_lst : List «local») (v_expr : expr) (t_1_lst : List valtype) (t_2_lst : List valtype) (lct_lst : List localtype) :
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    Expand ((C.TYPES)[proj_uN_0 x]!) (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    (List.length lct_lst) = (List.length local_lst) →
    Forall₂ (fun lct_elem v_local_elem => Local_ok C v_local_elem lct_elem) lct_lst local_lst →
    Expr_ok (C ++ ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := (Map (fun t_1_elem => localtype.mk_localtype init.SET t_1_elem) t_1_lst) ++ lct_lst
      LABELS := [.mk_list t_2_lst]
      RETURN := some (.mk_list t_2_lst)
      REFS := []
      RECS := [] : context
    })) v_expr (.mk_list t_2_lst) →
    wf_context C →
    wf_func (func.FUNC x local_lst v_expr) →
    wf_comptype (comptype.FUNC (.mk_list t_1_lst) (.mk_list t_2_lst)) →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := (Map (fun t_1_elem => localtype.mk_localtype init.SET t_1_elem) t_1_lst) ++ lct_lst
      LABELS := [.mk_list t_2_lst]
      RETURN := some (.mk_list t_2_lst)
      REFS := []
      RECS := [] : context
    }) →
    Func_ok C (func.FUNC x local_lst v_expr) ((C.TYPES)[proj_uN_0 x]!)


inductive Datamode_ok : context → datamode → datatype → Prop where
  | passive (C : context) :
    wf_context C →
    wf_datamode datamode.PASSIVE →
    Datamode_ok C datamode.PASSIVE datatype.OK
  | active (C : context) (x : idx) (v_expr : expr) («at» : addrtype) (lim : limits) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = (memtype.PAGE «at» lim) →
    Expr_ok_const C v_expr (valtype_addrtype «at») →
    wf_context C →
    wf_datamode (datamode.ACTIVE x v_expr) →
    wf_memtype (memtype.PAGE «at» lim) →
    Datamode_ok C (datamode.ACTIVE x v_expr) datatype.OK


inductive Data_ok : context → data → datatype → Prop where
  | mk_Data_ok (C : context) (b_lst : List byte) (v_datamode : datamode) :
    Datamode_ok C v_datamode datatype.OK →
    wf_context C →
    wf_data (data.DATA b_lst v_datamode) →
    Data_ok C (data.DATA b_lst v_datamode) datatype.OK


inductive Elemmode_ok : context → elemmode → elemtype → Prop where
  | passive (C : context) (rt : reftype) :
    wf_context C →
    wf_reftype rt →
    wf_elemmode elemmode.PASSIVE →
    Elemmode_ok C elemmode.PASSIVE rt
  | declare (C : context) (rt : reftype) :
    wf_context C →
    wf_reftype rt →
    wf_elemmode elemmode.DECLARE →
    Elemmode_ok C elemmode.DECLARE rt
  | active (C : context) (x : idx) (v_expr : expr) (rt : reftype) («at» : addrtype) (lim : limits) (rt' : reftype) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = (tabletype.mk_tabletype «at» lim rt') →
    Reftype_sub C rt rt' →
    Expr_ok_const C v_expr (valtype_addrtype «at») →
    wf_context C →
    wf_reftype rt →
    wf_elemmode (elemmode.ACTIVE x v_expr) →
    wf_tabletype (tabletype.mk_tabletype «at» lim rt') →
    Elemmode_ok C (elemmode.ACTIVE x v_expr) rt


inductive Elem_ok : context → elem → elemtype → Prop where
  | mk_Elem_ok (C : context) (v_elemtype : elemtype) (expr_lst : List expr) (v_elemmode : elemmode) :
    Reftype_ok C v_elemtype →
    Forall (fun v_expr_elem => Expr_ok_const C v_expr_elem (valtype_reftype v_elemtype)) expr_lst →
    Elemmode_ok C v_elemmode v_elemtype →
    wf_context C →
    wf_elem (elem.ELEM v_elemtype expr_lst v_elemmode) →
    Elem_ok C (elem.ELEM v_elemtype expr_lst v_elemmode) v_elemtype


inductive Start_ok : context → start → Prop where
  | mk_Start_ok (C : context) (x : idx) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    Expand ((C.FUNCS)[proj_uN_0 x]!) (comptype.FUNC (.mk_list []) (.mk_list [])) →
    wf_context C →
    wf_start (start.START x) →
    wf_comptype (comptype.FUNC (.mk_list []) (.mk_list [])) →
    Start_ok C (start.START x)


inductive Import_ok : context → «import» → externtype → Prop where
  | mk_Import_ok (C : context) (name_1 : name) (name_2 : name) (xt : externtype) (var_0 : externtype) :
    fun_clos_externtype C xt var_0 →
    Externtype_ok C xt →
    wf_context C →
    wf_externtype var_0 →
    wf_import (import.IMPORT name_1 name_2 xt) →
    Import_ok C (import.IMPORT name_1 name_2 xt) var_0


inductive Externidx_ok : context → externidx → externtype → Prop where
  | tag (C : context) (x : idx) (jt : tagtype) :
    (proj_uN_0 x) < (List.length (C.TAGS)) →
    ((C.TAGS)[proj_uN_0 x]!) = jt →
    wf_context C →
    wf_externidx (externidx.TAG x) →
    wf_externtype (externtype.TAG jt) →
    Externidx_ok C (externidx.TAG x) (externtype.TAG jt)
  | global (C : context) (x : idx) (gt : globaltype) :
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) = gt →
    wf_context C →
    wf_externidx (externidx.GLOBAL x) →
    wf_externtype (externtype.GLOBAL gt) →
    Externidx_ok C (externidx.GLOBAL x) (externtype.GLOBAL gt)
  | mem (C : context) (x : idx) (mt : memtype) :
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) = mt →
    wf_context C →
    wf_externidx (externidx.MEM x) →
    wf_externtype (externtype.MEM mt) →
    Externidx_ok C (externidx.MEM x) (externtype.MEM mt)
  | table (C : context) (x : idx) (tt : tabletype) :
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) = tt →
    wf_context C →
    wf_externidx (externidx.TABLE x) →
    wf_externtype (externtype.TABLE tt) →
    Externidx_ok C (externidx.TABLE x) (externtype.TABLE tt)
  | func (C : context) (x : idx) (dt : deftype) :
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) = dt →
    wf_context C →
    wf_externidx (externidx.FUNC x) →
    wf_externtype (externtype.FUNC (typeuse_deftype dt)) →
    Externidx_ok C (externidx.FUNC x) (externtype.FUNC (typeuse_deftype dt))


inductive Export_ok : context → «export» → name → externtype → Prop where
  | mk_Export_ok (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype) :
    Externidx_ok C v_externidx xt →
    wf_context C →
    wf_externtype xt →
    wf_export (export.EXPORT v_name v_externidx) →
    Export_ok C (export.EXPORT v_name v_externidx) v_name xt


inductive Globals_ok : context → List global → List globaltype → Prop where
  | empty (C : context) :
    wf_context C →
    Globals_ok C [] []
  | cons (C : context) (global_1 : global) (global_lst : List global) (gt_1 : globaltype) (gt_lst : List globaltype) :
    Global_ok C global_1 gt_1 →
    Globals_ok (C ++ ({
      TYPES := []
      TAGS := []
      GLOBALS := [gt_1]
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    })) global_lst gt_lst →
    wf_context C →
    wf_global global_1 →
    Forall (fun v_global_elem => wf_global v_global_elem) global_lst →
    Forall (fun gt_elem => wf_globaltype gt_elem) gt_lst →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := [gt_1]
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    Globals_ok C ([global_1] ++ global_lst) ([gt_1] ++ gt_lst)


inductive Types_ok : context → List type → List deftype → Prop where
  | empty (C : context) :
    wf_context C →
    Types_ok C [] []
  | cons (C : context) (type_1 : type) (type_lst : List type) (dt_1_lst : List deftype) (dt_lst : List deftype) :
    Type_ok C type_1 dt_1_lst →
    Types_ok (C ++ ({
      TYPES := dt_1_lst
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    })) type_lst dt_lst →
    wf_context C →
    wf_context ({
      TYPES := dt_1_lst
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    Types_ok C ([type_1] ++ type_lst) (dt_1_lst ++ dt_lst)


inductive nonfuncs : Type where
  | mk_nonfuncs (global_lst : List global) (mem_lst : List mem) (table_lst : List table) (elem_lst : List elem) (start_opt : Option start) (export_lst : List «export») : nonfuncs
deriving Inhabited, BEq

inductive wf_nonfuncs : nonfuncs → Prop where
  | nonfuncs_case_0 (global_lst : List global) (mem_lst : List mem) (table_lst : List table) (elem_lst : List elem) (start_opt : Option start) (export_lst : List «export») :
    Forall (fun v_global_elem => wf_global v_global_elem) global_lst →
    Forall (fun v_mem_elem => wf_mem v_mem_elem) mem_lst →
    Forall (fun v_table_elem => wf_table v_table_elem) table_lst →
    Forall (fun v_elem_elem => wf_elem v_elem_elem) elem_lst →
    Forall (fun v_start_elem => wf_start v_start_elem) (Option.toList start_opt) →
    Forall (fun v_export_elem => wf_export v_export_elem) export_lst →
    wf_nonfuncs (nonfuncs.mk_nonfuncs global_lst mem_lst table_lst elem_lst start_opt export_lst)


inductive fun_funcidx_nonfuncs : nonfuncs → List funcidx → Prop where
  | fun_funcidx_nonfuncs_case_0 (global_lst : List global) (mem_lst : List mem) (table_lst : List table) (elem_lst : List elem) (start_opt : Option start) (export_lst : List «export») (var_0 : List funcidx) :
    fun_funcidx_module (module.MODULE (list.mk_list []) (list.mk_list []) (list.mk_list []) (list.mk_list global_lst) (list.mk_list mem_lst) (list.mk_list table_lst) (list.mk_list []) (list.mk_list []) (list.mk_list elem_lst) start_opt (list.mk_list export_lst)) var_0 →
    fun_funcidx_nonfuncs (nonfuncs.mk_nonfuncs global_lst mem_lst table_lst elem_lst start_opt export_lst) var_0


inductive funcidx_nonfuncs_is_wf : nonfuncs → List funcidx → Prop where
  | funcidx_nonfuncs_is_wf_0 (v_nonfuncs : nonfuncs) (ret_val_lst : List funcidx) (var_0 : List funcidx) :
    fun_funcidx_nonfuncs v_nonfuncs var_0 →
    wf_nonfuncs v_nonfuncs →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    funcidx_nonfuncs_is_wf v_nonfuncs ret_val_lst


inductive Module_ok : module → moduletype → Prop where
  | mk_Module_ok (type_lst : List type) (import_lst : List «import») (tag_lst : List tag) (global_lst : List global) (mem_lst : List mem) (table_lst : List table) (func_lst : List func) (data_lst : List data) (elem_lst : List elem) (start_opt : Option start) (export_lst : List «export») (C : context) (xt_I_lst : List externtype) (xt_E_lst : List externtype) (dt'_lst : List deftype) (C' : context) (jt_lst : List tagtype) (gt_lst : List globaltype) (mt_lst : List memtype) (tt_lst : List tabletype) (dt_lst : List deftype) (ok_lst : List datatype) (rt_lst : List reftype) (nm_lst : List name) (jt_I_lst : List tagtype) (mt_I_lst : List memtype) (tt_I_lst : List tabletype) (gt_I_lst : List globaltype) (dt_I_lst : List deftype) (x_lst : List idx) (var_6 : List deftype) (var_5 : List tabletype) (var_4 : List memtype) (var_3 : List globaltype) (var_2 : List tagtype) (var_1 : List funcidx) (var_0 : moduletype) :
    fun_funcsxt xt_I_lst var_6 →
    fun_tablesxt xt_I_lst var_5 →
    fun_memsxt xt_I_lst var_4 →
    fun_globalsxt xt_I_lst var_3 →
    fun_tagsxt xt_I_lst var_2 →
    fun_funcidx_nonfuncs (nonfuncs.mk_nonfuncs global_lst mem_lst table_lst elem_lst start_opt export_lst) var_1 →
    fun_clos_moduletype C (moduletype.mk_moduletype xt_I_lst xt_E_lst) var_0 →
    Types_ok ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) type_lst dt'_lst →
    (List.length import_lst) = (List.length xt_I_lst) →
    Forall₂ (fun v_import_elem xt_I_elem => Import_ok ({
      TYPES := dt'_lst
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) v_import_elem xt_I_elem) import_lst xt_I_lst →
    (List.length jt_lst) = (List.length tag_lst) →
    Forall₂ (fun jt_elem v_tag_elem => Tag_ok C' v_tag_elem jt_elem) jt_lst tag_lst →
    Globals_ok C' global_lst gt_lst →
    (List.length mem_lst) = (List.length mt_lst) →
    Forall₂ (fun v_mem_elem mt_elem => Mem_ok C' v_mem_elem mt_elem) mem_lst mt_lst →
    (List.length table_lst) = (List.length tt_lst) →
    Forall₂ (fun v_table_elem tt_elem => Table_ok C' v_table_elem tt_elem) table_lst tt_lst →
    (List.length dt_lst) = (List.length func_lst) →
    Forall₂ (fun dt_elem v_func_elem => Func_ok C v_func_elem dt_elem) dt_lst func_lst →
    (List.length data_lst) = (List.length ok_lst) →
    Forall₂ (fun v_data_elem ok_elem => Data_ok C v_data_elem ok_elem) data_lst ok_lst →
    (List.length elem_lst) = (List.length rt_lst) →
    Forall₂ (fun v_elem_elem rt_elem => Elem_ok C v_elem_elem rt_elem) elem_lst rt_lst →
    Forall (fun v_start_elem => Start_ok C v_start_elem) (Option.toList start_opt) →
    (List.length export_lst) = (List.length nm_lst) →
    (List.length export_lst) = (List.length xt_E_lst) →
    Forall₃ (fun v_export_elem nm_elem xt_E_elem => Export_ok C v_export_elem nm_elem xt_E_elem) export_lst nm_lst xt_E_lst →
    disjoint_ name nm_lst →
    C = (C' ++ ({
      TYPES := []
      TAGS := jt_I_lst ++ jt_lst
      GLOBALS := gt_lst
      MEMS := mt_I_lst ++ mt_lst
      TABLES := tt_I_lst ++ tt_lst
      FUNCS := []
      DATAS := ok_lst
      ELEMS := rt_lst
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    })) →
    C' = ({
      TYPES := dt'_lst
      TAGS := []
      GLOBALS := gt_I_lst
      MEMS := []
      TABLES := []
      FUNCS := dt_I_lst ++ dt_lst
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := x_lst
      RECS := [] : context
    }) →
    x_lst = var_1 →
    jt_I_lst = var_2 →
    gt_I_lst = var_3 →
    mt_I_lst = var_4 →
    tt_I_lst = var_5 →
    dt_I_lst = var_6 →
    wf_context C →
    wf_context C' →
    Forall (fun nm_elem => wf_name nm_elem) nm_lst →
    wf_moduletype var_0 →
    Forall (fun iter_elem => wf_uN 32 iter_elem) var_1 →
    Forall (fun iter_elem => wf_typeuse iter_elem) var_2 →
    Forall (fun iter_elem => wf_globaltype iter_elem) var_3 →
    Forall (fun iter_elem => wf_memtype iter_elem) var_4 →
    Forall (fun iter_elem => wf_tabletype iter_elem) var_5 →
    wf_module (module.MODULE (list.mk_list type_lst) (list.mk_list import_lst) (list.mk_list tag_lst) (list.mk_list global_lst) (list.mk_list mem_lst) (list.mk_list table_lst) (list.mk_list func_lst) (list.mk_list data_lst) (list.mk_list elem_lst) start_opt (list.mk_list export_lst)) →
    wf_moduletype (moduletype.mk_moduletype xt_I_lst xt_E_lst) →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    wf_context ({
      TYPES := dt'_lst
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    wf_context ({
      TYPES := []
      TAGS := jt_I_lst ++ jt_lst
      GLOBALS := gt_lst
      MEMS := mt_I_lst ++ mt_lst
      TABLES := tt_I_lst ++ tt_lst
      FUNCS := []
      DATAS := ok_lst
      ELEMS := rt_lst
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    wf_context ({
      TYPES := dt'_lst
      TAGS := []
      GLOBALS := gt_I_lst
      MEMS := []
      TABLES := []
      FUNCS := dt_I_lst ++ dt_lst
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := x_lst
      RECS := [] : context
    }) →
    wf_nonfuncs (nonfuncs.mk_nonfuncs global_lst mem_lst table_lst elem_lst start_opt export_lst) →
    Module_ok (module.MODULE (list.mk_list type_lst) (list.mk_list import_lst) (list.mk_list tag_lst) (list.mk_list global_lst) (list.mk_list mem_lst) (list.mk_list table_lst) (list.mk_list func_lst) (list.mk_list data_lst) (list.mk_list elem_lst) start_opt (list.mk_list export_lst)) var_0


inductive relaxed2 : Type where
  | mk_relaxed2 (i : Nat) : relaxed2
deriving Inhabited, BEq

def proj_relaxed2_0 (x : relaxed2) : Nat :=
  match x with
  | relaxed2.mk_relaxed2 v_num_0 => (v_num_0)

inductive wf_relaxed2 : relaxed2 → Prop where
  | relaxed2_case_0 (i : Nat) :
    (i = 0) ∨ (i = 1) →
    wf_relaxed2 (relaxed2.mk_relaxed2 i)


inductive relaxed4 : Type where
  | mk_relaxed4 (i : Nat) : relaxed4
deriving Inhabited, BEq

def proj_relaxed4_0 (x : relaxed4) : Nat :=
  match x with
  | relaxed4.mk_relaxed4 v_num_0 => (v_num_0)

inductive wf_relaxed4 : relaxed4 → Prop where
  | relaxed4_case_0 (i : Nat) :
    (((i = 0) ∨ (i = 1)) ∨ (i = 2)) ∨ (i = 3) →
    wf_relaxed4 (relaxed4.mk_relaxed4 i)


def fun_relaxed2 (v_relaxed2 : relaxed2) (r_X : Type) [Inhabited r_X] (X_0 : r_X) (X_1 : r_X) : r_X :=
  if
    ND
  then
    ([X_0, X_1])[proj_relaxed2_0 v_relaxed2]!
  else
    ([X_0, X_1])[0]!

def fun_relaxed4 (v_relaxed4 : relaxed4) (r_X : Type) [Inhabited r_X] (X_0 : r_X) (X_1 : r_X) (X_2 : r_X) (X_3 : r_X) : r_X :=
  if
    ND
  then
    ([X_0, X_1, X_2, X_3])[proj_relaxed4_0 v_relaxed4]!
  else
    ([X_0, X_1, X_2, X_3])[0]!

opaque R_fmadd  : relaxed2 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_fmadd_is_wf : relaxed2 → Prop where
  | R_fmadd_is_wf_0 (ret_val : relaxed2) :
    ret_val = R_fmadd →
    wf_relaxed2 ret_val →
    R_fmadd_is_wf ret_val


opaque R_fmin  : relaxed4 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_fmin_is_wf : relaxed4 → Prop where
  | R_fmin_is_wf_0 (ret_val : relaxed4) :
    ret_val = R_fmin →
    wf_relaxed4 ret_val →
    R_fmin_is_wf ret_val


opaque R_fmax  : relaxed4 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_fmax_is_wf : relaxed4 → Prop where
  | R_fmax_is_wf_0 (ret_val : relaxed4) :
    ret_val = R_fmax →
    wf_relaxed4 ret_val →
    R_fmax_is_wf ret_val


opaque R_idot  : relaxed2 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_idot_is_wf : relaxed2 → Prop where
  | R_idot_is_wf_0 (ret_val : relaxed2) :
    ret_val = R_idot →
    wf_relaxed2 ret_val →
    R_idot_is_wf ret_val


opaque R_iq15mulr  : relaxed2 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_iq15mulr_is_wf : relaxed2 → Prop where
  | R_iq15mulr_is_wf_0 (ret_val : relaxed2) :
    ret_val = R_iq15mulr →
    wf_relaxed2 ret_val →
    R_iq15mulr_is_wf ret_val


opaque R_trunc_u  : relaxed4 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_trunc_u_is_wf : relaxed4 → Prop where
  | R_trunc_u_is_wf_0 (ret_val : relaxed4) :
    ret_val = R_trunc_u →
    wf_relaxed4 ret_val →
    R_trunc_u_is_wf ret_val


opaque R_trunc_s  : relaxed2 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_trunc_s_is_wf : relaxed2 → Prop where
  | R_trunc_s_is_wf_0 (ret_val : relaxed2) :
    ret_val = R_trunc_s →
    wf_relaxed2 ret_val →
    R_trunc_s_is_wf ret_val


opaque R_swizzle  : relaxed2 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_swizzle_is_wf : relaxed2 → Prop where
  | R_swizzle_is_wf_0 (ret_val : relaxed2) :
    ret_val = R_swizzle →
    wf_relaxed2 ret_val →
    R_swizzle_is_wf ret_val


opaque R_laneselect  : relaxed2 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive R_laneselect_is_wf : relaxed2 → Prop where
  | R_laneselect_is_wf_0 (ret_val : relaxed2) :
    ret_val = R_laneselect →
    wf_relaxed2 ret_val →
    R_laneselect_is_wf ret_val


opaque s33_to_u32 (v_s33 : s33) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive s33_to_u32_is_wf : s33 → u32 → Prop where
  | s33_to_u32_is_wf_0 (v_s33 : s33) (ret_val : u32) :
    wf_sN 33 v_s33 →
    ret_val = (s33_to_u32 v_s33) →
    wf_uN 32 ret_val →
    s33_to_u32_is_wf v_s33 ret_val


opaque ibits_ (v_N : N) (v_iN : iN) : List bit := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ibits__is_wf : N → iN → List bit → Prop where
  | ibits__is_wf_0 (v_N : N) (v_iN : iN) (ret_val_lst : List bit) :
    wf_uN v_N v_iN →
    ret_val_lst = (ibits_ v_N v_iN) →
    Forall (fun ret_val_elem => wf_bit ret_val_elem) ret_val_lst →
    ibits__is_wf v_N v_iN ret_val_lst


opaque fbits_ (v_N : N) (v_fN : fN) : List bit := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fbits__is_wf : N → fN → List bit → Prop where
  | fbits__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List bit) :
    wf_fN v_N v_fN →
    ret_val_lst = (fbits_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_bit ret_val_elem) ret_val_lst →
    fbits__is_wf v_N v_fN ret_val_lst


opaque ibytes_ (v_N : N) (v_iN : iN) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ibytes__is_wf : N → iN → List byte → Prop where
  | ibytes__is_wf_0 (v_N : N) (v_iN : iN) (ret_val_lst : List byte) :
    wf_uN v_N v_iN →
    ret_val_lst = (ibytes_ v_N v_iN) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    ibytes__is_wf v_N v_iN ret_val_lst


opaque fbytes_ (v_N : N) (v_fN : fN) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fbytes__is_wf : N → fN → List byte → Prop where
  | fbytes__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List byte) :
    wf_fN v_N v_fN →
    ret_val_lst = (fbytes_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    fbytes__is_wf v_N v_fN ret_val_lst


opaque nbytes_ (v_numtype : numtype) (v_num_ : num_) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive nbytes__is_wf : numtype → num_ → List byte → Prop where
  | nbytes__is_wf_0 (v_numtype : numtype) (v_num_ : num_) (ret_val_lst : List byte) :
    wf_num_ v_numtype v_num_ →
    ret_val_lst = (nbytes_ v_numtype v_num_) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    nbytes__is_wf v_numtype v_num_ ret_val_lst


opaque vbytes_ (v_vectype : vectype) (v_vec_ : vec_) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive vbytes__is_wf : vectype → vec_ → List byte → Prop where
  | vbytes__is_wf_0 (v_vectype : vectype) (v_vec_ : vec_) (ret_val_lst : List byte) :
    wf_uN (vsize v_vectype) v_vec_ →
    ret_val_lst = (vbytes_ v_vectype v_vec_) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    vbytes__is_wf v_vectype v_vec_ ret_val_lst


opaque zbytes_ (v_storagetype : storagetype) (v_lit_ : lit_) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive zbytes__is_wf : storagetype → lit_ → List byte → Prop where
  | zbytes__is_wf_0 (v_storagetype : storagetype) (v_lit_ : lit_) (ret_val_lst : List byte) :
    wf_storagetype v_storagetype →
    wf_lit_ v_storagetype v_lit_ →
    ret_val_lst = (zbytes_ v_storagetype v_lit_) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    zbytes__is_wf v_storagetype v_lit_ ret_val_lst


opaque cbytes_ (v_Cnn : Cnn) (v_lit_ : lit_) : List byte := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive cbytes__is_wf : Cnn → lit_ → List byte → Prop where
  | cbytes__is_wf_0 (v_Cnn : Cnn) (v_lit_ : lit_) (ret_val_lst : List byte) :
    wf_lit_ (storagetype_Cnn v_Cnn) v_lit_ →
    ret_val_lst = (cbytes_ v_Cnn v_lit_) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    cbytes__is_wf v_Cnn v_lit_ ret_val_lst


opaque inv_ibits_ (v_N : N) (var_0_lst : List bit) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_ibits__is_wf : N → List bit → iN → Prop where
  | inv_ibits__is_wf_0 (v_N : N) (var_0_lst : List bit) (ret_val : iN) :
    Forall (fun var_0_elem => wf_bit var_0_elem) var_0_lst →
    ret_val = (inv_ibits_ v_N var_0_lst) →
    wf_uN v_N ret_val →
    inv_ibits__is_wf v_N var_0_lst ret_val


opaque inv_fbits_ (v_N : N) (var_0_lst : List bit) : fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_fbits__is_wf : N → List bit → fN → Prop where
  | inv_fbits__is_wf_0 (v_N : N) (var_0_lst : List bit) (ret_val : fN) :
    Forall (fun var_0_elem => wf_bit var_0_elem) var_0_lst →
    ret_val = (inv_fbits_ v_N var_0_lst) →
    wf_fN v_N ret_val →
    inv_fbits__is_wf v_N var_0_lst ret_val


opaque inv_ibytes_ (v_N : N) (var_0_lst : List byte) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_ibytes__is_wf : N → List byte → iN → Prop where
  | inv_ibytes__is_wf_0 (v_N : N) (var_0_lst : List byte) (ret_val : iN) :
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val = (inv_ibytes_ v_N var_0_lst) →
    wf_uN v_N ret_val →
    inv_ibytes__is_wf v_N var_0_lst ret_val


opaque inv_fbytes_ (v_N : N) (var_0_lst : List byte) : fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_fbytes__is_wf : N → List byte → fN → Prop where
  | inv_fbytes__is_wf_0 (v_N : N) (var_0_lst : List byte) (ret_val : fN) :
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val = (inv_fbytes_ v_N var_0_lst) →
    wf_fN v_N ret_val →
    inv_fbytes__is_wf v_N var_0_lst ret_val


opaque inv_nbytes_ (v_numtype : numtype) (var_0_lst : List byte) : num_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_nbytes__is_wf : numtype → List byte → num_ → Prop where
  | inv_nbytes__is_wf_0 (v_numtype : numtype) (var_0_lst : List byte) (ret_val : num_) :
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val = (inv_nbytes_ v_numtype var_0_lst) →
    wf_num_ v_numtype ret_val →
    inv_nbytes__is_wf v_numtype var_0_lst ret_val


opaque inv_vbytes_ (v_vectype : vectype) (var_0_lst : List byte) : vec_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_vbytes__is_wf : vectype → List byte → vec_ → Prop where
  | inv_vbytes__is_wf_0 (v_vectype : vectype) (var_0_lst : List byte) (ret_val : vec_) :
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val = (inv_vbytes_ v_vectype var_0_lst) →
    wf_uN (vsize v_vectype) ret_val →
    inv_vbytes__is_wf v_vectype var_0_lst ret_val


opaque inv_zbytes_ (v_storagetype : storagetype) (var_0_lst : List byte) : lit_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_zbytes__is_wf : storagetype → List byte → lit_ → Prop where
  | inv_zbytes__is_wf_0 (v_storagetype : storagetype) (var_0_lst : List byte) (ret_val : lit_) :
    wf_storagetype v_storagetype →
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val = (inv_zbytes_ v_storagetype var_0_lst) →
    wf_lit_ v_storagetype ret_val →
    inv_zbytes__is_wf v_storagetype var_0_lst ret_val


opaque inv_cbytes_ (v_Cnn : Cnn) (var_0_lst : List byte) : lit_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_cbytes__is_wf : Cnn → List byte → lit_ → Prop where
  | inv_cbytes__is_wf_0 (v_Cnn : Cnn) (var_0_lst : List byte) (ret_val : lit_) :
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val = (inv_cbytes_ v_Cnn var_0_lst) →
    wf_lit_ (storagetype_Cnn v_Cnn) ret_val →
    inv_cbytes__is_wf v_Cnn var_0_lst ret_val


inductive fun_signed_ : N → Nat → Int → Prop where
  | fun_signed__case_0 (v_N : Nat) (i : Nat) :
    i < (2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) →
    fun_signed_ v_N i (i : Int)
  | fun_signed__case_1 (v_N : Nat) (i : Nat) :
    ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) ≤ i) ∧ (i < (2 ^ v_N)) →
    fun_signed_ v_N i ((i : Int) - ((2 ^ v_N) : Int))


inductive fun_inv_signed_ : N → Int → Nat → Prop where
  | fun_inv_signed__case_0 (v_N : Nat) (i : Int) :
    ((0 : Int) ≤ i) ∧ (i < ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) →
    fun_inv_signed_ v_N i (Int.toNat i)
  | fun_inv_signed__case_1 (v_N : Nat) (i : Int) :
    ((- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) ≤ i) ∧ (i < (0 : Int)) →
    fun_inv_signed_ v_N i (Int.toNat (i + ((2 ^ v_N) : Int)))


def fun_sx (v_storagetype : storagetype) : Option (Option sx) :=
  match v_storagetype with
  | storagetype.I32 => some none
  | storagetype.I64 => some none
  | storagetype.F32 => some none
  | storagetype.F64 => some none
  | storagetype.V128 => some none
  | storagetype.I8 => some (some sx.S)
  | storagetype.I16 => some (some sx.S)
  | _ => none

def fun_zero (v_lanetype : lanetype) : lane_ :=
  match v_lanetype with
  | lanetype.I32 => lane_.mk_lane__2 Jnn.I32 (uN.mk_uN 0)
  | lanetype.I64 => lane_.mk_lane__2 Jnn.I64 (uN.mk_uN 0)
  | lanetype.I8 => lane_.mk_lane__2 Jnn.I8 (uN.mk_uN 0)
  | lanetype.I16 => lane_.mk_lane__2 Jnn.I16 (uN.mk_uN 0)
  | lanetype.F32 => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 (fzero (size (numtype_Fnn Fnn.F32))))
  | lanetype.F64 => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 (fzero (size (numtype_Fnn Fnn.F64))))

inductive zero_is_wf : lanetype → lane_ → Prop where
  | zero_is_wf_0 (v_lanetype : lanetype) (ret_val : lane_) :
    ret_val = (fun_zero v_lanetype) →
    wf_lane_ v_lanetype ret_val →
    zero_is_wf v_lanetype ret_val


def nat_of_bool (v_bool : Bool) : Nat :=
  match v_bool with
  | false => 0
  | true => 1

opaque truncz (rat : Rat) : Int := by
  first
     | exact Inhabited.default
     | intros ; assumption


opaque ceilz (rat : Rat) : Int := by
  first
     | exact Inhabited.default
     | intros ; assumption


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

def ineg_ (v_N : N) (v_iN : iN) : iN :=
  uN.mk_uN (Int.toNat ((((2 ^ v_N) : Int) - ((proj_uN_0 v_iN) : Int)) % ((2 ^ v_N) : Int)))

inductive ineg__is_wf : N → iN → iN → Prop where
  | ineg__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    ret_val = (ineg_ v_N v_iN) →
    wf_uN v_N ret_val →
    ineg__is_wf v_N v_iN ret_val


def iabs_ (v_N : N) (v_iN : iN) : iN :=
  fun_signed_ v_N (proj_uN_0 v_iN) var_0 → if
    var_0 ≥ (0 : Int)
  then
    v_iN
  else
    ineg_ v_N v_iN

inductive iabs__is_wf : N → iN → iN → Prop where
  | iabs__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    ret_val = (iabs_ v_N v_iN) →
    wf_uN v_N ret_val →
    iabs__is_wf v_N v_iN ret_val


opaque iclz_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iclz__is_wf : N → iN → iN → Prop where
  | iclz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    ret_val = (iclz_ v_N v_iN) →
    wf_uN v_N ret_val →
    iclz__is_wf v_N v_iN ret_val


opaque ictz_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ictz__is_wf : N → iN → iN → Prop where
  | ictz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    ret_val = (ictz_ v_N v_iN) →
    wf_uN v_N ret_val →
    ictz__is_wf v_N v_iN ret_val


opaque ipopcnt_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ipopcnt__is_wf : N → iN → iN → Prop where
  | ipopcnt__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    ret_val = (ipopcnt_ v_N v_iN) →
    wf_uN v_N ret_val →
    ipopcnt__is_wf v_N v_iN ret_val


inductive fun_iextend_ : N → M → sx → iN → iN → Prop where
  | fun_iextend__case_0 (v_N : Nat) (v_M : Nat) (i : uN) : fun_iextend_ v_N v_M sx.U i (uN.mk_uN ((proj_uN_0 i) % (2 ^ v_M)))
  | fun_iextend__case_1 (v_N : Nat) (v_M : Nat) (i : uN) (var_1 : Int) (var_0 : Nat) :
    fun_signed_ v_M ((proj_uN_0 i) % (2 ^ v_M)) var_1 →
    fun_inv_signed_ v_N var_1 var_0 →
    fun_iextend_ v_N v_M sx.S i (uN.mk_uN var_0)


inductive iextend__is_wf : N → M → sx → iN → iN → Prop where
  | iextend__is_wf_0 (v_N : N) (v_M : M) (v_sx : sx) (v_iN : iN) (ret_val : iN) (var_0 : iN) :
    fun_iextend_ v_N v_M v_sx v_iN var_0 →
    wf_uN v_N v_iN →
    ret_val = var_0 →
    wf_uN v_N ret_val →
    iextend__is_wf v_N v_M v_sx v_iN ret_val


def iadd_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  uN.mk_uN (((proj_uN_0 v_iN) + (proj_uN_0 iN_0)) % (2 ^ v_N))

inductive iadd__is_wf : N → iN → iN → iN → Prop where
  | iadd__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (iadd_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    iadd__is_wf v_N v_iN iN_0 ret_val


def isub_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  uN.mk_uN (Int.toNat (((((2 ^ v_N) + (proj_uN_0 v_iN)) : Int) - ((proj_uN_0 iN_0) : Int)) % ((2 ^ v_N) : Int)))

inductive isub__is_wf : N → iN → iN → iN → Prop where
  | isub__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (isub_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    isub__is_wf v_N v_iN iN_0 ret_val


def imul_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  uN.mk_uN (((proj_uN_0 v_iN) * (proj_uN_0 iN_0)) % (2 ^ v_N))

inductive imul__is_wf : N → iN → iN → iN → Prop where
  | imul__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (imul_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    imul__is_wf v_N v_iN iN_0 ret_val


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


inductive idiv__is_wf : N → sx → iN → iN → Option iN → Prop where
  | idiv__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : Option iN) (var_0 : Option iN) :
    fun_idiv_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val_opt = var_0 →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    idiv__is_wf v_N v_sx v_iN iN_0 ret_val_opt


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


inductive irem__is_wf : N → sx → iN → iN → Option iN → Prop where
  | irem__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : Option iN) (var_0 : Option iN) :
    fun_irem_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val_opt = var_0 →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    irem__is_wf v_N v_sx v_iN iN_0 ret_val_opt


def imin_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN :=
  match v_sx with
  | sx.U => (proj_uN_0 v_iN) ≤ (proj_uN_0 iN_0) → v_iN
  | sx.U => (proj_uN_0 v_iN) > (proj_uN_0 iN_0) → iN_0
  | sx.S => fun_signed_ v_N (proj_uN_0 iN_0) var_1 → fun_signed_ v_N (proj_uN_0 v_iN) var_0 → if
    var_0 ≤ var_1
  then
    v_iN
  else
    iN_0

inductive imin__is_wf : N → sx → iN → iN → iN → Prop where
  | imin__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (imin_ v_N v_sx v_iN iN_0) →
    wf_uN v_N ret_val →
    imin__is_wf v_N v_sx v_iN iN_0 ret_val


def imax_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN :=
  match v_sx with
  | sx.U => (proj_uN_0 v_iN) ≥ (proj_uN_0 iN_0) → v_iN
  | sx.U => (proj_uN_0 v_iN) < (proj_uN_0 iN_0) → iN_0
  | sx.S => fun_signed_ v_N (proj_uN_0 iN_0) var_1 → fun_signed_ v_N (proj_uN_0 v_iN) var_0 → if
    var_0 ≥ var_1
  then
    v_iN
  else
    iN_0

inductive imax__is_wf : N → sx → iN → iN → iN → Prop where
  | imax__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (imax_ v_N v_sx v_iN iN_0) →
    wf_uN v_N ret_val →
    imax__is_wf v_N v_sx v_iN iN_0 ret_val


def iadd_sat_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN :=
  match v_sx with
  | sx.U => uN.mk_uN (sat_u_ v_N (((proj_uN_0 v_iN) + (proj_uN_0 iN_0)) : Int))
  | sx.S => fun_signed_ v_N (proj_uN_0 iN_0) var_2 → fun_signed_ v_N (proj_uN_0 v_iN) var_1 → fun_inv_signed_ v_N (sat_s_ v_N (var_1 + var_2)) var_0 → uN.mk_uN var_0

inductive iadd_sat__is_wf : N → sx → iN → iN → iN → Prop where
  | iadd_sat__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (iadd_sat_ v_N v_sx v_iN iN_0) →
    wf_uN v_N ret_val →
    iadd_sat__is_wf v_N v_sx v_iN iN_0 ret_val


def isub_sat_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN :=
  match v_sx with
  | sx.U => uN.mk_uN (sat_u_ v_N (((proj_uN_0 v_iN) : Int) - ((proj_uN_0 iN_0) : Int)))
  | sx.S => fun_signed_ v_N (proj_uN_0 iN_0) var_2 → fun_signed_ v_N (proj_uN_0 v_iN) var_1 → fun_inv_signed_ v_N (sat_s_ v_N (var_1 - var_2)) var_0 → uN.mk_uN var_0

inductive isub_sat__is_wf : N → sx → iN → iN → iN → Prop where
  | isub_sat__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (isub_sat_ v_N v_sx v_iN iN_0) →
    wf_uN v_N ret_val →
    isub_sat__is_wf v_N v_sx v_iN iN_0 ret_val


opaque iq15mulr_sat_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iq15mulr_sat__is_wf : N → sx → iN → iN → iN → Prop where
  | iq15mulr_sat__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (iq15mulr_sat_ v_N v_sx v_iN iN_0) →
    wf_uN v_N ret_val →
    iq15mulr_sat__is_wf v_N v_sx v_iN iN_0 ret_val


opaque irelaxed_q15mulr_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : List iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irelaxed_q15mulr__is_wf : N → sx → iN → iN → List iN → Prop where
  | irelaxed_q15mulr__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_lst : List iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val_lst = (irelaxed_q15mulr_ v_N v_sx v_iN iN_0) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) ret_val_lst →
    irelaxed_q15mulr__is_wf v_N v_sx v_iN iN_0 ret_val_lst


opaque iavgr_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iavgr__is_wf : N → sx → iN → iN → iN → Prop where
  | iavgr__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (iavgr_ v_N v_sx v_iN iN_0) →
    wf_uN v_N ret_val →
    iavgr__is_wf v_N v_sx v_iN iN_0 ret_val


opaque inot_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inot__is_wf : N → iN → iN → Prop where
  | inot__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    ret_val = (inot_ v_N v_iN) →
    wf_uN v_N ret_val →
    inot__is_wf v_N v_iN ret_val


opaque irev_ (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irev__is_wf : N → iN → iN → Prop where
  | irev__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    ret_val = (irev_ v_N v_iN) →
    wf_uN v_N ret_val →
    irev__is_wf v_N v_iN ret_val


opaque iand_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iand__is_wf : N → iN → iN → iN → Prop where
  | iand__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (iand_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    iand__is_wf v_N v_iN iN_0 ret_val


opaque iandnot_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iandnot__is_wf : N → iN → iN → iN → Prop where
  | iandnot__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (iandnot_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    iandnot__is_wf v_N v_iN iN_0 ret_val


opaque ior_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ior__is_wf : N → iN → iN → iN → Prop where
  | ior__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (ior_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    ior__is_wf v_N v_iN iN_0 ret_val


opaque ixor_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ixor__is_wf : N → iN → iN → iN → Prop where
  | ixor__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (ixor_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    ixor__is_wf v_N v_iN iN_0 ret_val


opaque ishl_ (v_N : N) (v_iN : iN) (v_u32 : u32) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ishl__is_wf : N → iN → u32 → iN → Prop where
  | ishl__is_wf_0 (v_N : N) (v_iN : iN) (v_u32 : u32) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN 32 v_u32 →
    ret_val = (ishl_ v_N v_iN v_u32) →
    wf_uN v_N ret_val →
    ishl__is_wf v_N v_iN v_u32 ret_val


opaque ishr_ (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ishr__is_wf : N → sx → iN → u32 → iN → Prop where
  | ishr__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN 32 v_u32 →
    ret_val = (ishr_ v_N v_sx v_iN v_u32) →
    wf_uN v_N ret_val →
    ishr__is_wf v_N v_sx v_iN v_u32 ret_val


opaque irotl_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irotl__is_wf : N → iN → iN → iN → Prop where
  | irotl__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (irotl_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    irotl__is_wf v_N v_iN iN_0 ret_val


opaque irotr_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irotr__is_wf : N → iN → iN → iN → Prop where
  | irotr__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (irotr_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    irotr__is_wf v_N v_iN iN_0 ret_val


opaque ibitselect_ (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ibitselect__is_wf : N → iN → iN → iN → iN → Prop where
  | ibitselect__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) (ret_val : iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    wf_uN v_N iN_1 →
    ret_val = (ibitselect_ v_N v_iN iN_0 iN_1) →
    wf_uN v_N ret_val →
    ibitselect__is_wf v_N v_iN iN_0 iN_1 ret_val


opaque irelaxed_laneselect_ (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) : List iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irelaxed_laneselect__is_wf : N → iN → iN → iN → List iN → Prop where
  | irelaxed_laneselect__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) (ret_val_lst : List iN) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    wf_uN v_N iN_1 →
    ret_val_lst = (irelaxed_laneselect_ v_N v_iN iN_0 iN_1) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) ret_val_lst →
    irelaxed_laneselect__is_wf v_N v_iN iN_0 iN_1 ret_val_lst


def ieqz_ (v_N : N) (v_iN : iN) : u32 :=
  uN.mk_uN (nat_of_bool ((proj_uN_0 v_iN) == 0))

inductive ieqz__is_wf : N → iN → u32 → Prop where
  | ieqz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : u32) :
    wf_uN v_N v_iN →
    ret_val = (ieqz_ v_N v_iN) →
    wf_uN 32 ret_val →
    ieqz__is_wf v_N v_iN ret_val


def inez_ (v_N : N) (v_iN : iN) : u32 :=
  uN.mk_uN (nat_of_bool ((proj_uN_0 v_iN) != 0))

inductive inez__is_wf : N → iN → u32 → Prop where
  | inez__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : u32) :
    wf_uN v_N v_iN →
    ret_val = (inez_ v_N v_iN) →
    wf_uN 32 ret_val →
    inez__is_wf v_N v_iN ret_val


def ieq_ (v_N : N) (v_iN : iN) (iN_0 : iN) : u32 :=
  uN.mk_uN (nat_of_bool (v_iN == iN_0))

inductive ieq__is_wf : N → iN → iN → u32 → Prop where
  | ieq__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (ieq_ v_N v_iN iN_0) →
    wf_uN 32 ret_val →
    ieq__is_wf v_N v_iN iN_0 ret_val


def ine_ (v_N : N) (v_iN : iN) (iN_0 : iN) : u32 :=
  uN.mk_uN (nat_of_bool (v_iN != iN_0))

inductive ine__is_wf : N → iN → iN → u32 → Prop where
  | ine__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (ine_ v_N v_iN iN_0) →
    wf_uN 32 ret_val →
    ine__is_wf v_N v_iN iN_0 ret_val


def ilt_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : u32 :=
  match v_sx with
  | sx.U => uN.mk_uN (nat_of_bool ((proj_uN_0 v_iN) < (proj_uN_0 iN_0)))
  | sx.S => fun_signed_ v_N (proj_uN_0 iN_0) var_1 → fun_signed_ v_N (proj_uN_0 v_iN) var_0 → uN.mk_uN (nat_of_bool (var_0 < var_1))

inductive ilt__is_wf : N → sx → iN → iN → u32 → Prop where
  | ilt__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (ilt_ v_N v_sx v_iN iN_0) →
    wf_uN 32 ret_val →
    ilt__is_wf v_N v_sx v_iN iN_0 ret_val


def igt_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : u32 :=
  match v_sx with
  | sx.U => uN.mk_uN (nat_of_bool ((proj_uN_0 v_iN) > (proj_uN_0 iN_0)))
  | sx.S => fun_signed_ v_N (proj_uN_0 iN_0) var_1 → fun_signed_ v_N (proj_uN_0 v_iN) var_0 → uN.mk_uN (nat_of_bool (var_0 > var_1))

inductive igt__is_wf : N → sx → iN → iN → u32 → Prop where
  | igt__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (igt_ v_N v_sx v_iN iN_0) →
    wf_uN 32 ret_val →
    igt__is_wf v_N v_sx v_iN iN_0 ret_val


def ile_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : u32 :=
  match v_sx with
  | sx.U => uN.mk_uN (nat_of_bool ((proj_uN_0 v_iN) ≤ (proj_uN_0 iN_0)))
  | sx.S => fun_signed_ v_N (proj_uN_0 iN_0) var_1 → fun_signed_ v_N (proj_uN_0 v_iN) var_0 → uN.mk_uN (nat_of_bool (var_0 ≤ var_1))

inductive ile__is_wf : N → sx → iN → iN → u32 → Prop where
  | ile__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (ile_ v_N v_sx v_iN iN_0) →
    wf_uN 32 ret_val →
    ile__is_wf v_N v_sx v_iN iN_0 ret_val


def ige_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : u32 :=
  match v_sx with
  | sx.U => uN.mk_uN (nat_of_bool ((proj_uN_0 v_iN) ≥ (proj_uN_0 iN_0)))
  | sx.S => fun_signed_ v_N (proj_uN_0 iN_0) var_1 → fun_signed_ v_N (proj_uN_0 v_iN) var_0 → uN.mk_uN (nat_of_bool (var_0 ≥ var_1))

inductive ige__is_wf : N → sx → iN → iN → u32 → Prop where
  | ige__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) :
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val = (ige_ v_N v_sx v_iN iN_0) →
    wf_uN 32 ret_val →
    ige__is_wf v_N v_sx v_iN iN_0 ret_val


opaque fabs_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fabs__is_wf : N → fN → List fN → Prop where
  | fabs__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    ret_val_lst = (fabs_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fabs__is_wf v_N v_fN ret_val_lst


opaque fneg_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fneg__is_wf : N → fN → List fN → Prop where
  | fneg__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    ret_val_lst = (fneg_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fneg__is_wf v_N v_fN ret_val_lst


opaque fsqrt_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fsqrt__is_wf : N → fN → List fN → Prop where
  | fsqrt__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    ret_val_lst = (fsqrt_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fsqrt__is_wf v_N v_fN ret_val_lst


opaque fceil_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fceil__is_wf : N → fN → List fN → Prop where
  | fceil__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    ret_val_lst = (fceil_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fceil__is_wf v_N v_fN ret_val_lst


opaque ffloor_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ffloor__is_wf : N → fN → List fN → Prop where
  | ffloor__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    ret_val_lst = (ffloor_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    ffloor__is_wf v_N v_fN ret_val_lst


opaque ftrunc_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ftrunc__is_wf : N → fN → List fN → Prop where
  | ftrunc__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    ret_val_lst = (ftrunc_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    ftrunc__is_wf v_N v_fN ret_val_lst


opaque fnearest_ (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fnearest__is_wf : N → fN → List fN → Prop where
  | fnearest__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    ret_val_lst = (fnearest_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fnearest__is_wf v_N v_fN ret_val_lst


opaque fadd_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fadd__is_wf : N → fN → fN → List fN → Prop where
  | fadd__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fadd_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fadd__is_wf v_N v_fN fN_0 ret_val_lst


opaque fsub_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fsub__is_wf : N → fN → fN → List fN → Prop where
  | fsub__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fsub_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fsub__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmul_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmul__is_wf : N → fN → fN → List fN → Prop where
  | fmul__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fmul_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fmul__is_wf v_N v_fN fN_0 ret_val_lst


opaque fdiv_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fdiv__is_wf : N → fN → fN → List fN → Prop where
  | fdiv__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fdiv_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fdiv__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmin_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmin__is_wf : N → fN → fN → List fN → Prop where
  | fmin__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fmin_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fmin__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmax_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmax__is_wf : N → fN → fN → List fN → Prop where
  | fmax__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fmax_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fmax__is_wf v_N v_fN fN_0 ret_val_lst


opaque fpmin_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fpmin__is_wf : N → fN → fN → List fN → Prop where
  | fpmin__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fpmin_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fpmin__is_wf v_N v_fN fN_0 ret_val_lst


opaque fpmax_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fpmax__is_wf : N → fN → fN → List fN → Prop where
  | fpmax__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fpmax_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fpmax__is_wf v_N v_fN fN_0 ret_val_lst


opaque frelaxed_min_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive frelaxed_min__is_wf : N → fN → fN → List fN → Prop where
  | frelaxed_min__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (frelaxed_min_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    frelaxed_min__is_wf v_N v_fN fN_0 ret_val_lst


opaque frelaxed_max_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive frelaxed_max__is_wf : N → fN → fN → List fN → Prop where
  | frelaxed_max__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (frelaxed_max_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    frelaxed_max__is_wf v_N v_fN fN_0 ret_val_lst


opaque fcopysign_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fcopysign__is_wf : N → fN → fN → List fN → Prop where
  | fcopysign__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst = (fcopysign_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fcopysign__is_wf v_N v_fN fN_0 ret_val_lst


opaque feq_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive feq__is_wf : N → fN → fN → u32 → Prop where
  | feq__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val = (feq_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    feq__is_wf v_N v_fN fN_0 ret_val


opaque fne_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fne__is_wf : N → fN → fN → u32 → Prop where
  | fne__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val = (fne_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    fne__is_wf v_N v_fN fN_0 ret_val


opaque flt_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive flt__is_wf : N → fN → fN → u32 → Prop where
  | flt__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val = (flt_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    flt__is_wf v_N v_fN fN_0 ret_val


opaque fgt_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fgt__is_wf : N → fN → fN → u32 → Prop where
  | fgt__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val = (fgt_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    fgt__is_wf v_N v_fN fN_0 ret_val


opaque fle_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fle__is_wf : N → fN → fN → u32 → Prop where
  | fle__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val = (fle_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    fle__is_wf v_N v_fN fN_0 ret_val


opaque fge_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fge__is_wf : N → fN → fN → u32 → Prop where
  | fge__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val = (fge_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    fge__is_wf v_N v_fN fN_0 ret_val


opaque frelaxed_madd_ (v_N : N) (v_fN : fN) (fN_0 : fN) (fN_1 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive frelaxed_madd__is_wf : N → fN → fN → fN → List fN → Prop where
  | frelaxed_madd__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (fN_1 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    wf_fN v_N fN_1 →
    ret_val_lst = (frelaxed_madd_ v_N v_fN fN_0 fN_1) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    frelaxed_madd__is_wf v_N v_fN fN_0 fN_1 ret_val_lst


opaque frelaxed_nmadd_ (v_N : N) (v_fN : fN) (fN_0 : fN) (fN_1 : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive frelaxed_nmadd__is_wf : N → fN → fN → fN → List fN → Prop where
  | frelaxed_nmadd__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (fN_1 : fN) (ret_val_lst : List fN) :
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    wf_fN v_N fN_1 →
    ret_val_lst = (frelaxed_nmadd_ v_N v_fN fN_0 fN_1) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    frelaxed_nmadd__is_wf v_N v_fN fN_0 fN_1 ret_val_lst


opaque wrap__ (v_M : M) (v_N : N) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive wrap___is_wf : M → N → iN → iN → Prop where
  | wrap___is_wf_0 (v_M : M) (v_N : N) (v_iN : iN) (ret_val : iN) :
    wf_uN v_M v_iN →
    ret_val = (wrap__ v_M v_N v_iN) →
    wf_uN v_N ret_val →
    wrap___is_wf v_M v_N v_iN ret_val


opaque extend__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive extend___is_wf : M → N → sx → iN → iN → Prop where
  | extend___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN) :
    wf_uN v_M v_iN →
    ret_val = (extend__ v_M v_N v_sx v_iN) →
    wf_uN v_N ret_val →
    extend___is_wf v_M v_N v_sx v_iN ret_val


opaque trunc__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive trunc___is_wf : M → N → sx → fN → Option iN → Prop where
  | trunc___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) :
    wf_fN v_M v_fN →
    ret_val_opt = (trunc__ v_M v_N v_sx v_fN) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    trunc___is_wf v_M v_N v_sx v_fN ret_val_opt


opaque trunc_sat__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive trunc_sat___is_wf : M → N → sx → fN → Option iN → Prop where
  | trunc_sat___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) :
    wf_fN v_M v_fN →
    ret_val_opt = (trunc_sat__ v_M v_N v_sx v_fN) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    trunc_sat___is_wf v_M v_N v_sx v_fN ret_val_opt


opaque relaxed_trunc__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive relaxed_trunc___is_wf : M → N → sx → fN → Option iN → Prop where
  | relaxed_trunc___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) :
    wf_fN v_M v_fN →
    ret_val_opt = (relaxed_trunc__ v_M v_N v_sx v_fN) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    relaxed_trunc___is_wf v_M v_N v_sx v_fN ret_val_opt


opaque demote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive demote___is_wf : M → N → fN → List fN → Prop where
  | demote___is_wf_0 (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_M v_fN →
    ret_val_lst = (demote__ v_M v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    demote___is_wf v_M v_N v_fN ret_val_lst


opaque promote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive promote___is_wf : M → N → fN → List fN → Prop where
  | promote___is_wf_0 (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) :
    wf_fN v_M v_fN →
    ret_val_lst = (promote__ v_M v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    promote___is_wf v_M v_N v_fN ret_val_lst


opaque convert__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : fN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive convert___is_wf : M → N → sx → iN → fN → Prop where
  | convert___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : fN) :
    wf_uN v_M v_iN →
    ret_val = (convert__ v_M v_N v_sx v_iN) →
    wf_fN v_N ret_val →
    convert___is_wf v_M v_N v_sx v_iN ret_val


opaque narrow__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive narrow___is_wf : M → N → sx → iN → iN → Prop where
  | narrow___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN) :
    wf_uN v_M v_iN →
    ret_val = (narrow__ v_M v_N v_sx v_iN) →
    wf_uN v_N ret_val →
    narrow___is_wf v_M v_N v_sx v_iN ret_val


opaque reinterpret__ (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) : num_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive reinterpret___is_wf : numtype → numtype → num_ → num_ → Prop where
  | reinterpret___is_wf_0 (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) (ret_val : num_) :
    wf_num_ numtype_1 v_num_ →
    ret_val = (reinterpret__ numtype_1 numtype_2 v_num_) →
    wf_num_ numtype_2 ret_val →
    reinterpret___is_wf numtype_1 numtype_2 v_num_ ret_val


def lpacknum_ (v_lanetype : lanetype) (v_num_ : num_) : lane_ :=
  match v_lanetype, v_num_ with
  | lanetype.I32, _ => lane_.mk_lane__0 numtype.I32 v_num_
  | lanetype.I64, _ => lane_.mk_lane__0 numtype.I64 v_num_
  | lanetype.F32, _ => lane_.mk_lane__0 numtype.F32 v_num_
  | lanetype.F64, _ => lane_.mk_lane__0 numtype.F64 v_num_
  | lanetype.I8, num_.mk_num__0 addrtype.I32 c => lane_.mk_lane__1 packtype.I8 (wrap__ (size (lunpack (lanetype_packtype packtype.I8))) (psize packtype.I8) c)
  | lanetype.I16, num_.mk_num__0 addrtype.I32 c => lane_.mk_lane__1 packtype.I16 (wrap__ (size (lunpack (lanetype_packtype packtype.I16))) (psize packtype.I16) c)
  | _, _ => Inhabited.default

inductive lpacknum__is_wf : lanetype → num_ → lane_ → Prop where
  | lpacknum__is_wf_0 (v_lanetype : lanetype) (v_num_ : num_) (ret_val : lane_) :
    wf_num_ (lunpack v_lanetype) v_num_ →
    ret_val = (lpacknum_ v_lanetype v_num_) →
    wf_lane_ v_lanetype ret_val →
    lpacknum__is_wf v_lanetype v_num_ ret_val


def cpacknum_ (v_storagetype : storagetype) (v_lit_ : lit_) : lit_ :=
  match v_storagetype, v_lit_ with
  | storagetype.I32, _ => v_lit_
  | storagetype.I64, _ => v_lit_
  | storagetype.F32, _ => v_lit_
  | storagetype.F64, _ => v_lit_
  | storagetype.V128, _ => v_lit_
  | storagetype.I8, lit_.mk_lit__0 numtype.I32 (num_.mk_num__0 addrtype.I32 c) => lit_.mk_lit__2 packtype.I8 (wrap__ (size (lunpack (lanetype_packtype packtype.I8))) (psize packtype.I8) c)
  | storagetype.I16, lit_.mk_lit__0 numtype.I32 (num_.mk_num__0 addrtype.I32 c) => lit_.mk_lit__2 packtype.I16 (wrap__ (size (lunpack (lanetype_packtype packtype.I16))) (psize packtype.I16) c)
  | _, _ => Inhabited.default

inductive cpacknum__is_wf : storagetype → lit_ → lit_ → Prop where
  | cpacknum__is_wf_0 (v_storagetype : storagetype) (v_lit_ : lit_) (ret_val : lit_) :
    wf_storagetype v_storagetype →
    (cunpack v_storagetype) ≠ none →
    wf_lit_ (storagetype_consttype (Option.get! (cunpack v_storagetype))) v_lit_ →
    ret_val = (cpacknum_ v_storagetype v_lit_) →
    wf_lit_ v_storagetype ret_val →
    cpacknum__is_wf v_storagetype v_lit_ ret_val


def lunpacknum_ (v_lanetype : lanetype) (v_lane_ : lane_) : num_ :=
  match v_lanetype, v_lane_ with
  | lanetype.I32, lane_.mk_lane__0 numtype.I32 c => c
  | lanetype.I64, lane_.mk_lane__0 numtype.I64 c => c
  | lanetype.F32, lane_.mk_lane__0 numtype.F32 c => c
  | lanetype.F64, lane_.mk_lane__0 numtype.F64 c => c
  | lanetype.I8, lane_.mk_lane__1 packtype.I8 c => num_.mk_num__0 addrtype.I32 (extend__ (psize packtype.I8) (size (lunpack (lanetype_packtype packtype.I8))) sx.U c)
  | lanetype.I16, lane_.mk_lane__1 packtype.I16 c => num_.mk_num__0 addrtype.I32 (extend__ (psize packtype.I16) (size (lunpack (lanetype_packtype packtype.I16))) sx.U c)
  | _, _ => Inhabited.default

inductive lunpacknum__is_wf : lanetype → lane_ → num_ → Prop where
  | lunpacknum__is_wf_0 (v_lanetype : lanetype) (v_lane_ : lane_) (ret_val : num_) :
    wf_lane_ v_lanetype v_lane_ →
    ret_val = (lunpacknum_ v_lanetype v_lane_) →
    wf_num_ (lunpack v_lanetype) ret_val →
    lunpacknum__is_wf v_lanetype v_lane_ ret_val


def cunpacknum_ (v_storagetype : storagetype) (v_lit_ : lit_) : lit_ :=
  match v_storagetype, v_lit_ with
  | storagetype.I32, _ => v_lit_
  | storagetype.I64, _ => v_lit_
  | storagetype.F32, _ => v_lit_
  | storagetype.F64, _ => v_lit_
  | storagetype.V128, _ => v_lit_
  | storagetype.I8, lit_.mk_lit__2 packtype.I8 c => lit_.mk_lit__0 numtype.I32 (num_.mk_num__0 addrtype.I32 (extend__ (psize packtype.I8) (size (lunpack (lanetype_packtype packtype.I8))) sx.U c))
  | storagetype.I16, lit_.mk_lit__2 packtype.I16 c => lit_.mk_lit__0 numtype.I32 (num_.mk_num__0 addrtype.I32 (extend__ (psize packtype.I16) (size (lunpack (lanetype_packtype packtype.I16))) sx.U c))
  | _, _ => Inhabited.default

inductive cunpacknum__is_wf : storagetype → lit_ → lit_ → Prop where
  | cunpacknum__is_wf_0 (v_storagetype : storagetype) (v_lit_ : lit_) (ret_val : lit_) :
    wf_storagetype v_storagetype →
    wf_lit_ v_storagetype v_lit_ →
    ret_val = (cunpacknum_ v_storagetype v_lit_) →
    (cunpack v_storagetype) ≠ none →
    wf_lit_ (storagetype_consttype (Option.get! (cunpack v_storagetype))) ret_val →
    cunpacknum__is_wf v_storagetype v_lit_ ret_val


inductive fun_unop_ : numtype → unop_ → num_ → List num_ → Prop where
  | fun_unop__case_0 (i : uN) : fun_unop_ numtype.I32 (unop_.mk_unop__0 addrtype.I32 unop_Inn.CLZ) (num_.mk_num__0 addrtype.I32 i) [num_.mk_num__0 addrtype.I32 (iclz_ (sizenn (numtype_addrtype addrtype.I32)) i)]
  | fun_unop__case_1 (i : uN) : fun_unop_ numtype.I64 (unop_.mk_unop__0 addrtype.I64 unop_Inn.CLZ) (num_.mk_num__0 addrtype.I64 i) [num_.mk_num__0 addrtype.I64 (iclz_ (sizenn (numtype_addrtype addrtype.I64)) i)]
  | fun_unop__case_2 (i : uN) : fun_unop_ numtype.I32 (unop_.mk_unop__0 addrtype.I32 unop_Inn.CTZ) (num_.mk_num__0 addrtype.I32 i) [num_.mk_num__0 addrtype.I32 (ictz_ (sizenn (numtype_addrtype addrtype.I32)) i)]
  | fun_unop__case_3 (i : uN) : fun_unop_ numtype.I64 (unop_.mk_unop__0 addrtype.I64 unop_Inn.CTZ) (num_.mk_num__0 addrtype.I64 i) [num_.mk_num__0 addrtype.I64 (ictz_ (sizenn (numtype_addrtype addrtype.I64)) i)]
  | fun_unop__case_4 (i : uN) : fun_unop_ numtype.I32 (unop_.mk_unop__0 addrtype.I32 unop_Inn.POPCNT) (num_.mk_num__0 addrtype.I32 i) [num_.mk_num__0 addrtype.I32 (ipopcnt_ (sizenn (numtype_addrtype addrtype.I32)) i)]
  | fun_unop__case_5 (i : uN) : fun_unop_ numtype.I64 (unop_.mk_unop__0 addrtype.I64 unop_Inn.POPCNT) (num_.mk_num__0 addrtype.I64 i) [num_.mk_num__0 addrtype.I64 (ipopcnt_ (sizenn (numtype_addrtype addrtype.I64)) i)]
  | fun_unop__case_6 (v_M : Nat) (i : uN) (var_0 : uN) :
    fun_iextend_ (sizenn (numtype_addrtype addrtype.I32)) v_M sx.S i var_0 →
    fun_unop_ numtype.I32 (unop_.mk_unop__0 addrtype.I32 (unop_Inn.EXTEND (sz.mk_sz v_M))) (num_.mk_num__0 addrtype.I32 i) [num_.mk_num__0 addrtype.I32 var_0]
  | fun_unop__case_7 (v_M : Nat) (i : uN) (var_0 : uN) :
    fun_iextend_ (sizenn (numtype_addrtype addrtype.I64)) v_M sx.S i var_0 →
    fun_unop_ numtype.I64 (unop_.mk_unop__0 addrtype.I64 (unop_Inn.EXTEND (sz.mk_sz v_M))) (num_.mk_num__0 addrtype.I64 i) [num_.mk_num__0 addrtype.I64 var_0]
  | fun_unop__case_8 (f : fN) : fun_unop_ numtype.F32 (unop_.mk_unop__1 Fnn.F32 unop_Fnn.ABS) (num_.mk_num__1 Fnn.F32 f) (Map (fun iter_0_1_elem => num_.mk_num__1 Fnn.F32 iter_0_1_elem) (fabs_ (sizenn (numtype_Fnn Fnn.F32)) f))
  | fun_unop__case_9 (f : fN) : fun_unop_ numtype.F64 (unop_.mk_unop__1 Fnn.F64 unop_Fnn.ABS) (num_.mk_num__1 Fnn.F64 f) (Map (fun iter_0_2_elem => num_.mk_num__1 Fnn.F64 iter_0_2_elem) (fabs_ (sizenn (numtype_Fnn Fnn.F64)) f))
  | fun_unop__case_10 (f : fN) : fun_unop_ numtype.F32 (unop_.mk_unop__1 Fnn.F32 unop_Fnn.NEG) (num_.mk_num__1 Fnn.F32 f) (Map (fun iter_0_3_elem => num_.mk_num__1 Fnn.F32 iter_0_3_elem) (fneg_ (sizenn (numtype_Fnn Fnn.F32)) f))
  | fun_unop__case_11 (f : fN) : fun_unop_ numtype.F64 (unop_.mk_unop__1 Fnn.F64 unop_Fnn.NEG) (num_.mk_num__1 Fnn.F64 f) (Map (fun iter_0_4_elem => num_.mk_num__1 Fnn.F64 iter_0_4_elem) (fneg_ (sizenn (numtype_Fnn Fnn.F64)) f))
  | fun_unop__case_12 (f : fN) : fun_unop_ numtype.F32 (unop_.mk_unop__1 Fnn.F32 unop_Fnn.SQRT) (num_.mk_num__1 Fnn.F32 f) (Map (fun iter_0_5_elem => num_.mk_num__1 Fnn.F32 iter_0_5_elem) (fsqrt_ (sizenn (numtype_Fnn Fnn.F32)) f))
  | fun_unop__case_13 (f : fN) : fun_unop_ numtype.F64 (unop_.mk_unop__1 Fnn.F64 unop_Fnn.SQRT) (num_.mk_num__1 Fnn.F64 f) (Map (fun iter_0_6_elem => num_.mk_num__1 Fnn.F64 iter_0_6_elem) (fsqrt_ (sizenn (numtype_Fnn Fnn.F64)) f))
  | fun_unop__case_14 (f : fN) : fun_unop_ numtype.F32 (unop_.mk_unop__1 Fnn.F32 unop_Fnn.CEIL) (num_.mk_num__1 Fnn.F32 f) (Map (fun iter_0_7_elem => num_.mk_num__1 Fnn.F32 iter_0_7_elem) (fceil_ (sizenn (numtype_Fnn Fnn.F32)) f))
  | fun_unop__case_15 (f : fN) : fun_unop_ numtype.F64 (unop_.mk_unop__1 Fnn.F64 unop_Fnn.CEIL) (num_.mk_num__1 Fnn.F64 f) (Map (fun iter_0_8_elem => num_.mk_num__1 Fnn.F64 iter_0_8_elem) (fceil_ (sizenn (numtype_Fnn Fnn.F64)) f))
  | fun_unop__case_16 (f : fN) : fun_unop_ numtype.F32 (unop_.mk_unop__1 Fnn.F32 unop_Fnn.FLOOR) (num_.mk_num__1 Fnn.F32 f) (Map (fun iter_0_9_elem => num_.mk_num__1 Fnn.F32 iter_0_9_elem) (ffloor_ (sizenn (numtype_Fnn Fnn.F32)) f))
  | fun_unop__case_17 (f : fN) : fun_unop_ numtype.F64 (unop_.mk_unop__1 Fnn.F64 unop_Fnn.FLOOR) (num_.mk_num__1 Fnn.F64 f) (Map (fun iter_0_10_elem => num_.mk_num__1 Fnn.F64 iter_0_10_elem) (ffloor_ (sizenn (numtype_Fnn Fnn.F64)) f))
  | fun_unop__case_18 (f : fN) : fun_unop_ numtype.F32 (unop_.mk_unop__1 Fnn.F32 unop_Fnn.TRUNC) (num_.mk_num__1 Fnn.F32 f) (Map (fun iter_0_11_elem => num_.mk_num__1 Fnn.F32 iter_0_11_elem) (ftrunc_ (sizenn (numtype_Fnn Fnn.F32)) f))
  | fun_unop__case_19 (f : fN) : fun_unop_ numtype.F64 (unop_.mk_unop__1 Fnn.F64 unop_Fnn.TRUNC) (num_.mk_num__1 Fnn.F64 f) (Map (fun iter_0_12_elem => num_.mk_num__1 Fnn.F64 iter_0_12_elem) (ftrunc_ (sizenn (numtype_Fnn Fnn.F64)) f))
  | fun_unop__case_20 (f : fN) : fun_unop_ numtype.F32 (unop_.mk_unop__1 Fnn.F32 unop_Fnn.NEAREST) (num_.mk_num__1 Fnn.F32 f) (Map (fun iter_0_13_elem => num_.mk_num__1 Fnn.F32 iter_0_13_elem) (fnearest_ (sizenn (numtype_Fnn Fnn.F32)) f))
  | fun_unop__case_21 (f : fN) : fun_unop_ numtype.F64 (unop_.mk_unop__1 Fnn.F64 unop_Fnn.NEAREST) (num_.mk_num__1 Fnn.F64 f) (Map (fun iter_0_14_elem => num_.mk_num__1 Fnn.F64 iter_0_14_elem) (fnearest_ (sizenn (numtype_Fnn Fnn.F64)) f))


inductive unop__is_wf : numtype → unop_ → num_ → List num_ → Prop where
  | unop__is_wf_0 (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) (ret_val_lst : List num_) (var_0 : List num_) :
    fun_unop_ v_numtype v_unop_ v_num_ var_0 →
    wf_unop_ v_numtype v_unop_ →
    wf_num_ v_numtype v_num_ →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_num_ v_numtype ret_val_elem) ret_val_lst →
    unop__is_wf v_numtype v_unop_ v_num_ ret_val_lst


inductive fun_binop_ : numtype → binop_ → num_ → num_ → List num_ → Prop where
  | fun_binop__case_0 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.ADD) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (iadd_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2)]
  | fun_binop__case_1 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.ADD) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (iadd_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2)]
  | fun_binop__case_2 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.SUB) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (isub_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2)]
  | fun_binop__case_3 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.SUB) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (isub_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2)]
  | fun_binop__case_4 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.MUL) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (imul_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2)]
  | fun_binop__case_5 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.MUL) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (imul_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2)]
  | fun_binop__case_6 (v_sx : sx) (i_1 : uN) (i_2 : uN) (var_0 : Option iN) :
    fun_idiv_ (sizenn (numtype_addrtype addrtype.I32)) v_sx i_1 i_2 var_0 →
    fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 (binop_Inn.DIV v_sx)) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) (Map (fun iter_0_15_elem => num_.mk_num__0 addrtype.I32 iter_0_15_elem) (Option.toList var_0))
  | fun_binop__case_7 (v_sx : sx) (i_1 : uN) (i_2 : uN) (var_0 : Option iN) :
    fun_idiv_ (sizenn (numtype_addrtype addrtype.I64)) v_sx i_1 i_2 var_0 →
    fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 (binop_Inn.DIV v_sx)) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) (Map (fun iter_0_16_elem => num_.mk_num__0 addrtype.I64 iter_0_16_elem) (Option.toList var_0))
  | fun_binop__case_8 (v_sx : sx) (i_1 : uN) (i_2 : uN) (var_0 : Option iN) :
    fun_irem_ (sizenn (numtype_addrtype addrtype.I32)) v_sx i_1 i_2 var_0 →
    fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 (binop_Inn.REM v_sx)) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) (Map (fun iter_0_17_elem => num_.mk_num__0 addrtype.I32 iter_0_17_elem) (Option.toList var_0))
  | fun_binop__case_9 (v_sx : sx) (i_1 : uN) (i_2 : uN) (var_0 : Option iN) :
    fun_irem_ (sizenn (numtype_addrtype addrtype.I64)) v_sx i_1 i_2 var_0 →
    fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 (binop_Inn.REM v_sx)) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) (Map (fun iter_0_18_elem => num_.mk_num__0 addrtype.I64 iter_0_18_elem) (Option.toList var_0))
  | fun_binop__case_10 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.AND) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (iand_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2)]
  | fun_binop__case_11 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.AND) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (iand_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2)]
  | fun_binop__case_12 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.OR) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (ior_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2)]
  | fun_binop__case_13 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.OR) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (ior_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2)]
  | fun_binop__case_14 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.XOR) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (ixor_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2)]
  | fun_binop__case_15 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.XOR) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (ixor_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2)]
  | fun_binop__case_16 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.SHL) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (ishl_ (sizenn (numtype_addrtype addrtype.I32)) i_1 (uN.mk_uN (proj_uN_0 i_2)))]
  | fun_binop__case_17 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.SHL) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (ishl_ (sizenn (numtype_addrtype addrtype.I64)) i_1 (uN.mk_uN (proj_uN_0 i_2)))]
  | fun_binop__case_18 (v_sx : sx) (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 (binop_Inn.SHR v_sx)) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (ishr_ (sizenn (numtype_addrtype addrtype.I32)) v_sx i_1 (uN.mk_uN (proj_uN_0 i_2)))]
  | fun_binop__case_19 (v_sx : sx) (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 (binop_Inn.SHR v_sx)) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (ishr_ (sizenn (numtype_addrtype addrtype.I64)) v_sx i_1 (uN.mk_uN (proj_uN_0 i_2)))]
  | fun_binop__case_20 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.ROTL) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (irotl_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2)]
  | fun_binop__case_21 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.ROTL) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (irotl_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2)]
  | fun_binop__case_22 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 addrtype.I32 binop_Inn.ROTR) (num_.mk_num__0 addrtype.I32 i_1) (num_.mk_num__0 addrtype.I32 i_2) [num_.mk_num__0 addrtype.I32 (irotr_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2)]
  | fun_binop__case_23 (i_1 : uN) (i_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 addrtype.I64 binop_Inn.ROTR) (num_.mk_num__0 addrtype.I64 i_1) (num_.mk_num__0 addrtype.I64 i_2) [num_.mk_num__0 addrtype.I64 (irotr_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2)]
  | fun_binop__case_24 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.ADD) (num_.mk_num__1 Fnn.F32 f_1) (num_.mk_num__1 Fnn.F32 f_2) (Map (fun iter_0_19_elem => num_.mk_num__1 Fnn.F32 iter_0_19_elem) (fadd_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2))
  | fun_binop__case_25 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.ADD) (num_.mk_num__1 Fnn.F64 f_1) (num_.mk_num__1 Fnn.F64 f_2) (Map (fun iter_0_20_elem => num_.mk_num__1 Fnn.F64 iter_0_20_elem) (fadd_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2))
  | fun_binop__case_26 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.SUB) (num_.mk_num__1 Fnn.F32 f_1) (num_.mk_num__1 Fnn.F32 f_2) (Map (fun iter_0_21_elem => num_.mk_num__1 Fnn.F32 iter_0_21_elem) (fsub_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2))
  | fun_binop__case_27 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.SUB) (num_.mk_num__1 Fnn.F64 f_1) (num_.mk_num__1 Fnn.F64 f_2) (Map (fun iter_0_22_elem => num_.mk_num__1 Fnn.F64 iter_0_22_elem) (fsub_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2))
  | fun_binop__case_28 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MUL) (num_.mk_num__1 Fnn.F32 f_1) (num_.mk_num__1 Fnn.F32 f_2) (Map (fun iter_0_23_elem => num_.mk_num__1 Fnn.F32 iter_0_23_elem) (fmul_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2))
  | fun_binop__case_29 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MUL) (num_.mk_num__1 Fnn.F64 f_1) (num_.mk_num__1 Fnn.F64 f_2) (Map (fun iter_0_24_elem => num_.mk_num__1 Fnn.F64 iter_0_24_elem) (fmul_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2))
  | fun_binop__case_30 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.DIV) (num_.mk_num__1 Fnn.F32 f_1) (num_.mk_num__1 Fnn.F32 f_2) (Map (fun iter_0_25_elem => num_.mk_num__1 Fnn.F32 iter_0_25_elem) (fdiv_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2))
  | fun_binop__case_31 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.DIV) (num_.mk_num__1 Fnn.F64 f_1) (num_.mk_num__1 Fnn.F64 f_2) (Map (fun iter_0_26_elem => num_.mk_num__1 Fnn.F64 iter_0_26_elem) (fdiv_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2))
  | fun_binop__case_32 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MIN) (num_.mk_num__1 Fnn.F32 f_1) (num_.mk_num__1 Fnn.F32 f_2) (Map (fun iter_0_27_elem => num_.mk_num__1 Fnn.F32 iter_0_27_elem) (fmin_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2))
  | fun_binop__case_33 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MIN) (num_.mk_num__1 Fnn.F64 f_1) (num_.mk_num__1 Fnn.F64 f_2) (Map (fun iter_0_28_elem => num_.mk_num__1 Fnn.F64 iter_0_28_elem) (fmin_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2))
  | fun_binop__case_34 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MAX) (num_.mk_num__1 Fnn.F32 f_1) (num_.mk_num__1 Fnn.F32 f_2) (Map (fun iter_0_29_elem => num_.mk_num__1 Fnn.F32 iter_0_29_elem) (fmax_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2))
  | fun_binop__case_35 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MAX) (num_.mk_num__1 Fnn.F64 f_1) (num_.mk_num__1 Fnn.F64 f_2) (Map (fun iter_0_30_elem => num_.mk_num__1 Fnn.F64 iter_0_30_elem) (fmax_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2))
  | fun_binop__case_36 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.COPYSIGN) (num_.mk_num__1 Fnn.F32 f_1) (num_.mk_num__1 Fnn.F32 f_2) (Map (fun iter_0_31_elem => num_.mk_num__1 Fnn.F32 iter_0_31_elem) (fcopysign_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2))
  | fun_binop__case_37 (f_1 : fN) (f_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.COPYSIGN) (num_.mk_num__1 Fnn.F64 f_1) (num_.mk_num__1 Fnn.F64 f_2) (Map (fun iter_0_32_elem => num_.mk_num__1 Fnn.F64 iter_0_32_elem) (fcopysign_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2))


inductive binop__is_wf : numtype → binop_ → num_ → num_ → List num_ → Prop where
  | binop__is_wf_0 (v_numtype : numtype) (v_binop_ : binop_) (v_num_ : num_) (num__0 : num_) (ret_val_lst : List num_) (var_0 : List num_) :
    fun_binop_ v_numtype v_binop_ v_num_ num__0 var_0 →
    wf_binop_ v_numtype v_binop_ →
    wf_num_ v_numtype v_num_ →
    wf_num_ v_numtype num__0 →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_num_ v_numtype ret_val_elem) ret_val_lst →
    binop__is_wf v_numtype v_binop_ v_num_ num__0 ret_val_lst


def fun_testop_ (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) : u32 :=
  match v_numtype, v_testop_, v_num_ with
  | numtype.I32, testop_.mk_testop__0 addrtype.I32 testop_Inn.EQZ, num_.mk_num__0 addrtype.I32 i => ieqz_ (sizenn (numtype_addrtype addrtype.I32)) i
  | numtype.I64, testop_.mk_testop__0 addrtype.I64 testop_Inn.EQZ, num_.mk_num__0 addrtype.I64 i => ieqz_ (sizenn (numtype_addrtype addrtype.I64)) i
  | _, _, _ => Inhabited.default

inductive testop__is_wf : numtype → testop_ → num_ → u32 → Prop where
  | testop__is_wf_0 (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) (ret_val : u32) :
    wf_testop_ v_numtype v_testop_ →
    wf_num_ v_numtype v_num_ →
    ret_val = (fun_testop_ v_numtype v_testop_ v_num_) →
    wf_uN 32 ret_val →
    testop__is_wf v_numtype v_testop_ v_num_ ret_val


def fun_relop_ (v_numtype : numtype) (v_relop_ : relop_) (v_num_ : num_) (num__0 : num_) : u32 :=
  match v_numtype, v_relop_, v_num_, num__0 with
  | numtype.I32, relop_.mk_relop__0 addrtype.I32 relop_Inn.EQ, num_.mk_num__0 addrtype.I32 i_1, num_.mk_num__0 addrtype.I32 i_2 => ieq_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2
  | numtype.I64, relop_.mk_relop__0 addrtype.I64 relop_Inn.EQ, num_.mk_num__0 addrtype.I64 i_1, num_.mk_num__0 addrtype.I64 i_2 => ieq_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2
  | numtype.I32, relop_.mk_relop__0 addrtype.I32 relop_Inn.NE, num_.mk_num__0 addrtype.I32 i_1, num_.mk_num__0 addrtype.I32 i_2 => ine_ (sizenn (numtype_addrtype addrtype.I32)) i_1 i_2
  | numtype.I64, relop_.mk_relop__0 addrtype.I64 relop_Inn.NE, num_.mk_num__0 addrtype.I64 i_1, num_.mk_num__0 addrtype.I64 i_2 => ine_ (sizenn (numtype_addrtype addrtype.I64)) i_1 i_2
  | numtype.I32, relop_.mk_relop__0 addrtype.I32 (relop_Inn.LT v_sx), num_.mk_num__0 addrtype.I32 i_1, num_.mk_num__0 addrtype.I32 i_2 => ilt_ (sizenn (numtype_addrtype addrtype.I32)) v_sx i_1 i_2
  | numtype.I64, relop_.mk_relop__0 addrtype.I64 (relop_Inn.LT v_sx), num_.mk_num__0 addrtype.I64 i_1, num_.mk_num__0 addrtype.I64 i_2 => ilt_ (sizenn (numtype_addrtype addrtype.I64)) v_sx i_1 i_2
  | numtype.I32, relop_.mk_relop__0 addrtype.I32 (relop_Inn.GT v_sx), num_.mk_num__0 addrtype.I32 i_1, num_.mk_num__0 addrtype.I32 i_2 => igt_ (sizenn (numtype_addrtype addrtype.I32)) v_sx i_1 i_2
  | numtype.I64, relop_.mk_relop__0 addrtype.I64 (relop_Inn.GT v_sx), num_.mk_num__0 addrtype.I64 i_1, num_.mk_num__0 addrtype.I64 i_2 => igt_ (sizenn (numtype_addrtype addrtype.I64)) v_sx i_1 i_2
  | numtype.I32, relop_.mk_relop__0 addrtype.I32 (relop_Inn.LE v_sx), num_.mk_num__0 addrtype.I32 i_1, num_.mk_num__0 addrtype.I32 i_2 => ile_ (sizenn (numtype_addrtype addrtype.I32)) v_sx i_1 i_2
  | numtype.I64, relop_.mk_relop__0 addrtype.I64 (relop_Inn.LE v_sx), num_.mk_num__0 addrtype.I64 i_1, num_.mk_num__0 addrtype.I64 i_2 => ile_ (sizenn (numtype_addrtype addrtype.I64)) v_sx i_1 i_2
  | numtype.I32, relop_.mk_relop__0 addrtype.I32 (relop_Inn.GE v_sx), num_.mk_num__0 addrtype.I32 i_1, num_.mk_num__0 addrtype.I32 i_2 => ige_ (sizenn (numtype_addrtype addrtype.I32)) v_sx i_1 i_2
  | numtype.I64, relop_.mk_relop__0 addrtype.I64 (relop_Inn.GE v_sx), num_.mk_num__0 addrtype.I64 i_1, num_.mk_num__0 addrtype.I64 i_2 => ige_ (sizenn (numtype_addrtype addrtype.I64)) v_sx i_1 i_2
  | numtype.F32, relop_.mk_relop__1 Fnn.F32 relop_Fnn.EQ, num_.mk_num__1 Fnn.F32 f_1, num_.mk_num__1 Fnn.F32 f_2 => feq_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2
  | numtype.F64, relop_.mk_relop__1 Fnn.F64 relop_Fnn.EQ, num_.mk_num__1 Fnn.F64 f_1, num_.mk_num__1 Fnn.F64 f_2 => feq_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2
  | numtype.F32, relop_.mk_relop__1 Fnn.F32 relop_Fnn.NE, num_.mk_num__1 Fnn.F32 f_1, num_.mk_num__1 Fnn.F32 f_2 => fne_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2
  | numtype.F64, relop_.mk_relop__1 Fnn.F64 relop_Fnn.NE, num_.mk_num__1 Fnn.F64 f_1, num_.mk_num__1 Fnn.F64 f_2 => fne_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2
  | numtype.F32, relop_.mk_relop__1 Fnn.F32 relop_Fnn.LT, num_.mk_num__1 Fnn.F32 f_1, num_.mk_num__1 Fnn.F32 f_2 => flt_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2
  | numtype.F64, relop_.mk_relop__1 Fnn.F64 relop_Fnn.LT, num_.mk_num__1 Fnn.F64 f_1, num_.mk_num__1 Fnn.F64 f_2 => flt_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2
  | numtype.F32, relop_.mk_relop__1 Fnn.F32 relop_Fnn.GT, num_.mk_num__1 Fnn.F32 f_1, num_.mk_num__1 Fnn.F32 f_2 => fgt_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2
  | numtype.F64, relop_.mk_relop__1 Fnn.F64 relop_Fnn.GT, num_.mk_num__1 Fnn.F64 f_1, num_.mk_num__1 Fnn.F64 f_2 => fgt_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2
  | numtype.F32, relop_.mk_relop__1 Fnn.F32 relop_Fnn.LE, num_.mk_num__1 Fnn.F32 f_1, num_.mk_num__1 Fnn.F32 f_2 => fle_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2
  | numtype.F64, relop_.mk_relop__1 Fnn.F64 relop_Fnn.LE, num_.mk_num__1 Fnn.F64 f_1, num_.mk_num__1 Fnn.F64 f_2 => fle_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2
  | numtype.F32, relop_.mk_relop__1 Fnn.F32 relop_Fnn.GE, num_.mk_num__1 Fnn.F32 f_1, num_.mk_num__1 Fnn.F32 f_2 => fge_ (sizenn (numtype_Fnn Fnn.F32)) f_1 f_2
  | numtype.F64, relop_.mk_relop__1 Fnn.F64 relop_Fnn.GE, num_.mk_num__1 Fnn.F64 f_1, num_.mk_num__1 Fnn.F64 f_2 => fge_ (sizenn (numtype_Fnn Fnn.F64)) f_1 f_2
  | _, _, _, _ => Inhabited.default

inductive relop__is_wf : numtype → relop_ → num_ → num_ → u32 → Prop where
  | relop__is_wf_0 (v_numtype : numtype) (v_relop_ : relop_) (v_num_ : num_) (num__0 : num_) (ret_val : u32) :
    wf_relop_ v_numtype v_relop_ →
    wf_num_ v_numtype v_num_ →
    wf_num_ v_numtype num__0 →
    ret_val = (fun_relop_ v_numtype v_relop_ v_num_ num__0) →
    wf_uN 32 ret_val →
    relop__is_wf v_numtype v_relop_ v_num_ num__0 ret_val


inductive fun_cvtop__ : numtype → numtype → cvtop__ → num_ → List num_ → Prop where
  | fun_cvtop___case_0 (v_sx : sx) (i_1 : uN) : fun_cvtop__ numtype.I32 numtype.I32 (cvtop__.mk_cvtop___0 addrtype.I32 addrtype.I32 (cvtop__Inn_1_Inn_2.EXTEND v_sx)) (num_.mk_num__0 addrtype.I32 i_1) [num_.mk_num__0 addrtype.I32 (extend__ (sizenn1 (numtype_addrtype addrtype.I32)) (sizenn2 (numtype_addrtype addrtype.I32)) v_sx i_1)]
  | fun_cvtop___case_1 (v_sx : sx) (i_1 : uN) : fun_cvtop__ numtype.I64 numtype.I32 (cvtop__.mk_cvtop___0 addrtype.I64 addrtype.I32 (cvtop__Inn_1_Inn_2.EXTEND v_sx)) (num_.mk_num__0 addrtype.I64 i_1) [num_.mk_num__0 addrtype.I32 (extend__ (sizenn1 (numtype_addrtype addrtype.I64)) (sizenn2 (numtype_addrtype addrtype.I32)) v_sx i_1)]
  | fun_cvtop___case_2 (v_sx : sx) (i_1 : uN) : fun_cvtop__ numtype.I32 numtype.I64 (cvtop__.mk_cvtop___0 addrtype.I32 addrtype.I64 (cvtop__Inn_1_Inn_2.EXTEND v_sx)) (num_.mk_num__0 addrtype.I32 i_1) [num_.mk_num__0 addrtype.I64 (extend__ (sizenn1 (numtype_addrtype addrtype.I32)) (sizenn2 (numtype_addrtype addrtype.I64)) v_sx i_1)]
  | fun_cvtop___case_3 (v_sx : sx) (i_1 : uN) : fun_cvtop__ numtype.I64 numtype.I64 (cvtop__.mk_cvtop___0 addrtype.I64 addrtype.I64 (cvtop__Inn_1_Inn_2.EXTEND v_sx)) (num_.mk_num__0 addrtype.I64 i_1) [num_.mk_num__0 addrtype.I64 (extend__ (sizenn1 (numtype_addrtype addrtype.I64)) (sizenn2 (numtype_addrtype addrtype.I64)) v_sx i_1)]
  | fun_cvtop___case_4 (i_1 : uN) : fun_cvtop__ numtype.I32 numtype.I32 (cvtop__.mk_cvtop___0 addrtype.I32 addrtype.I32 cvtop__Inn_1_Inn_2.WRAP) (num_.mk_num__0 addrtype.I32 i_1) [num_.mk_num__0 addrtype.I32 (wrap__ (sizenn1 (numtype_addrtype addrtype.I32)) (sizenn2 (numtype_addrtype addrtype.I32)) i_1)]
  | fun_cvtop___case_5 (i_1 : uN) : fun_cvtop__ numtype.I64 numtype.I32 (cvtop__.mk_cvtop___0 addrtype.I64 addrtype.I32 cvtop__Inn_1_Inn_2.WRAP) (num_.mk_num__0 addrtype.I64 i_1) [num_.mk_num__0 addrtype.I32 (wrap__ (sizenn1 (numtype_addrtype addrtype.I64)) (sizenn2 (numtype_addrtype addrtype.I32)) i_1)]
  | fun_cvtop___case_6 (i_1 : uN) : fun_cvtop__ numtype.I32 numtype.I64 (cvtop__.mk_cvtop___0 addrtype.I32 addrtype.I64 cvtop__Inn_1_Inn_2.WRAP) (num_.mk_num__0 addrtype.I32 i_1) [num_.mk_num__0 addrtype.I64 (wrap__ (sizenn1 (numtype_addrtype addrtype.I32)) (sizenn2 (numtype_addrtype addrtype.I64)) i_1)]
  | fun_cvtop___case_7 (i_1 : uN) : fun_cvtop__ numtype.I64 numtype.I64 (cvtop__.mk_cvtop___0 addrtype.I64 addrtype.I64 cvtop__Inn_1_Inn_2.WRAP) (num_.mk_num__0 addrtype.I64 i_1) [num_.mk_num__0 addrtype.I64 (wrap__ (sizenn1 (numtype_addrtype addrtype.I64)) (sizenn2 (numtype_addrtype addrtype.I64)) i_1)]
  | fun_cvtop___case_8 (v_sx : sx) (f_1 : fN) : fun_cvtop__ numtype.F32 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F32 addrtype.I32 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)) (num_.mk_num__1 Fnn.F32 f_1) (Map (fun iter_0_33_elem => num_.mk_num__0 addrtype.I32 iter_0_33_elem) (Option.toList (trunc__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_addrtype addrtype.I32)) v_sx f_1)))
  | fun_cvtop___case_9 (v_sx : sx) (f_1 : fN) : fun_cvtop__ numtype.F64 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F64 addrtype.I32 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)) (num_.mk_num__1 Fnn.F64 f_1) (Map (fun iter_0_34_elem => num_.mk_num__0 addrtype.I32 iter_0_34_elem) (Option.toList (trunc__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_addrtype addrtype.I32)) v_sx f_1)))
  | fun_cvtop___case_10 (v_sx : sx) (f_1 : fN) : fun_cvtop__ numtype.F32 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F32 addrtype.I64 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)) (num_.mk_num__1 Fnn.F32 f_1) (Map (fun iter_0_35_elem => num_.mk_num__0 addrtype.I64 iter_0_35_elem) (Option.toList (trunc__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_addrtype addrtype.I64)) v_sx f_1)))
  | fun_cvtop___case_11 (v_sx : sx) (f_1 : fN) : fun_cvtop__ numtype.F64 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F64 addrtype.I64 (cvtop__Fnn_1_Inn_2.TRUNC v_sx)) (num_.mk_num__1 Fnn.F64 f_1) (Map (fun iter_0_36_elem => num_.mk_num__0 addrtype.I64 iter_0_36_elem) (Option.toList (trunc__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_addrtype addrtype.I64)) v_sx f_1)))
  | fun_cvtop___case_12 (v_sx : sx) (f_1 : fN) : fun_cvtop__ numtype.F32 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F32 addrtype.I32 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)) (num_.mk_num__1 Fnn.F32 f_1) (Map (fun iter_0_37_elem => num_.mk_num__0 addrtype.I32 iter_0_37_elem) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_addrtype addrtype.I32)) v_sx f_1)))
  | fun_cvtop___case_13 (v_sx : sx) (f_1 : fN) : fun_cvtop__ numtype.F64 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F64 addrtype.I32 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)) (num_.mk_num__1 Fnn.F64 f_1) (Map (fun iter_0_38_elem => num_.mk_num__0 addrtype.I32 iter_0_38_elem) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_addrtype addrtype.I32)) v_sx f_1)))
  | fun_cvtop___case_14 (v_sx : sx) (f_1 : fN) : fun_cvtop__ numtype.F32 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F32 addrtype.I64 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)) (num_.mk_num__1 Fnn.F32 f_1) (Map (fun iter_0_39_elem => num_.mk_num__0 addrtype.I64 iter_0_39_elem) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_addrtype addrtype.I64)) v_sx f_1)))
  | fun_cvtop___case_15 (v_sx : sx) (f_1 : fN) : fun_cvtop__ numtype.F64 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F64 addrtype.I64 (cvtop__Fnn_1_Inn_2.TRUNC_SAT v_sx)) (num_.mk_num__1 Fnn.F64 f_1) (Map (fun iter_0_40_elem => num_.mk_num__0 addrtype.I64 iter_0_40_elem) (Option.toList (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_addrtype addrtype.I64)) v_sx f_1)))
  | fun_cvtop___case_16 (v_sx : sx) (i_1 : uN) : fun_cvtop__ numtype.I32 numtype.F32 (cvtop__.mk_cvtop___1 addrtype.I32 Fnn.F32 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)) (num_.mk_num__0 addrtype.I32 i_1) [num_.mk_num__1 Fnn.F32 (convert__ (sizenn1 (numtype_addrtype addrtype.I32)) (sizenn2 (numtype_Fnn Fnn.F32)) v_sx i_1)]
  | fun_cvtop___case_17 (v_sx : sx) (i_1 : uN) : fun_cvtop__ numtype.I64 numtype.F32 (cvtop__.mk_cvtop___1 addrtype.I64 Fnn.F32 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)) (num_.mk_num__0 addrtype.I64 i_1) [num_.mk_num__1 Fnn.F32 (convert__ (sizenn1 (numtype_addrtype addrtype.I64)) (sizenn2 (numtype_Fnn Fnn.F32)) v_sx i_1)]
  | fun_cvtop___case_18 (v_sx : sx) (i_1 : uN) : fun_cvtop__ numtype.I32 numtype.F64 (cvtop__.mk_cvtop___1 addrtype.I32 Fnn.F64 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)) (num_.mk_num__0 addrtype.I32 i_1) [num_.mk_num__1 Fnn.F64 (convert__ (sizenn1 (numtype_addrtype addrtype.I32)) (sizenn2 (numtype_Fnn Fnn.F64)) v_sx i_1)]
  | fun_cvtop___case_19 (v_sx : sx) (i_1 : uN) : fun_cvtop__ numtype.I64 numtype.F64 (cvtop__.mk_cvtop___1 addrtype.I64 Fnn.F64 (cvtop__Inn_1_Fnn_2.CONVERT v_sx)) (num_.mk_num__0 addrtype.I64 i_1) [num_.mk_num__1 Fnn.F64 (convert__ (sizenn1 (numtype_addrtype addrtype.I64)) (sizenn2 (numtype_Fnn Fnn.F64)) v_sx i_1)]
  | fun_cvtop___case_20 (f_1 : fN) : fun_cvtop__ numtype.F32 numtype.F32 (cvtop__.mk_cvtop___3 Fnn.F32 Fnn.F32 cvtop__Fnn_1_Fnn_2.PROMOTE) (num_.mk_num__1 Fnn.F32 f_1) (Map (fun iter_0_41_elem => num_.mk_num__1 Fnn.F32 iter_0_41_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F32)) f_1))
  | fun_cvtop___case_21 (f_1 : fN) : fun_cvtop__ numtype.F64 numtype.F32 (cvtop__.mk_cvtop___3 Fnn.F64 Fnn.F32 cvtop__Fnn_1_Fnn_2.PROMOTE) (num_.mk_num__1 Fnn.F64 f_1) (Map (fun iter_0_42_elem => num_.mk_num__1 Fnn.F32 iter_0_42_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F32)) f_1))
  | fun_cvtop___case_22 (f_1 : fN) : fun_cvtop__ numtype.F32 numtype.F64 (cvtop__.mk_cvtop___3 Fnn.F32 Fnn.F64 cvtop__Fnn_1_Fnn_2.PROMOTE) (num_.mk_num__1 Fnn.F32 f_1) (Map (fun iter_0_43_elem => num_.mk_num__1 Fnn.F64 iter_0_43_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F64)) f_1))
  | fun_cvtop___case_23 (f_1 : fN) : fun_cvtop__ numtype.F64 numtype.F64 (cvtop__.mk_cvtop___3 Fnn.F64 Fnn.F64 cvtop__Fnn_1_Fnn_2.PROMOTE) (num_.mk_num__1 Fnn.F64 f_1) (Map (fun iter_0_44_elem => num_.mk_num__1 Fnn.F64 iter_0_44_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F64)) f_1))
  | fun_cvtop___case_24 (f_1 : fN) : fun_cvtop__ numtype.F32 numtype.F32 (cvtop__.mk_cvtop___3 Fnn.F32 Fnn.F32 cvtop__Fnn_1_Fnn_2.DEMOTE) (num_.mk_num__1 Fnn.F32 f_1) (Map (fun iter_0_45_elem => num_.mk_num__1 Fnn.F32 iter_0_45_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F32)) f_1))
  | fun_cvtop___case_25 (f_1 : fN) : fun_cvtop__ numtype.F64 numtype.F32 (cvtop__.mk_cvtop___3 Fnn.F64 Fnn.F32 cvtop__Fnn_1_Fnn_2.DEMOTE) (num_.mk_num__1 Fnn.F64 f_1) (Map (fun iter_0_46_elem => num_.mk_num__1 Fnn.F32 iter_0_46_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F32)) f_1))
  | fun_cvtop___case_26 (f_1 : fN) : fun_cvtop__ numtype.F32 numtype.F64 (cvtop__.mk_cvtop___3 Fnn.F32 Fnn.F64 cvtop__Fnn_1_Fnn_2.DEMOTE) (num_.mk_num__1 Fnn.F32 f_1) (Map (fun iter_0_47_elem => num_.mk_num__1 Fnn.F64 iter_0_47_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F64)) f_1))
  | fun_cvtop___case_27 (f_1 : fN) : fun_cvtop__ numtype.F64 numtype.F64 (cvtop__.mk_cvtop___3 Fnn.F64 Fnn.F64 cvtop__Fnn_1_Fnn_2.DEMOTE) (num_.mk_num__1 Fnn.F64 f_1) (Map (fun iter_0_48_elem => num_.mk_num__1 Fnn.F64 iter_0_48_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F64)) f_1))
  | fun_cvtop___case_28 (i_1 : uN) :
    (size (numtype_addrtype addrtype.I32)) = (size (numtype_Fnn Fnn.F32)) →
    fun_cvtop__ numtype.I32 numtype.F32 (cvtop__.mk_cvtop___1 addrtype.I32 Fnn.F32 cvtop__Inn_1_Fnn_2.REINTERPRET) (num_.mk_num__0 addrtype.I32 i_1) [reinterpret__ (numtype_addrtype addrtype.I32) (numtype_Fnn Fnn.F32) (num_.mk_num__0 addrtype.I32 i_1)]
  | fun_cvtop___case_29 (i_1 : uN) :
    (size (numtype_addrtype addrtype.I64)) = (size (numtype_Fnn Fnn.F32)) →
    fun_cvtop__ numtype.I64 numtype.F32 (cvtop__.mk_cvtop___1 addrtype.I64 Fnn.F32 cvtop__Inn_1_Fnn_2.REINTERPRET) (num_.mk_num__0 addrtype.I64 i_1) [reinterpret__ (numtype_addrtype addrtype.I64) (numtype_Fnn Fnn.F32) (num_.mk_num__0 addrtype.I64 i_1)]
  | fun_cvtop___case_30 (i_1 : uN) :
    (size (numtype_addrtype addrtype.I32)) = (size (numtype_Fnn Fnn.F64)) →
    fun_cvtop__ numtype.I32 numtype.F64 (cvtop__.mk_cvtop___1 addrtype.I32 Fnn.F64 cvtop__Inn_1_Fnn_2.REINTERPRET) (num_.mk_num__0 addrtype.I32 i_1) [reinterpret__ (numtype_addrtype addrtype.I32) (numtype_Fnn Fnn.F64) (num_.mk_num__0 addrtype.I32 i_1)]
  | fun_cvtop___case_31 (i_1 : uN) :
    (size (numtype_addrtype addrtype.I64)) = (size (numtype_Fnn Fnn.F64)) →
    fun_cvtop__ numtype.I64 numtype.F64 (cvtop__.mk_cvtop___1 addrtype.I64 Fnn.F64 cvtop__Inn_1_Fnn_2.REINTERPRET) (num_.mk_num__0 addrtype.I64 i_1) [reinterpret__ (numtype_addrtype addrtype.I64) (numtype_Fnn Fnn.F64) (num_.mk_num__0 addrtype.I64 i_1)]
  | fun_cvtop___case_32 (f_1 : fN) :
    (size (numtype_Fnn Fnn.F32)) = (size (numtype_addrtype addrtype.I32)) →
    fun_cvtop__ numtype.F32 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F32 addrtype.I32 cvtop__Fnn_1_Inn_2.REINTERPRET) (num_.mk_num__1 Fnn.F32 f_1) [reinterpret__ (numtype_Fnn Fnn.F32) (numtype_addrtype addrtype.I32) (num_.mk_num__1 Fnn.F32 f_1)]
  | fun_cvtop___case_33 (f_1 : fN) :
    (size (numtype_Fnn Fnn.F64)) = (size (numtype_addrtype addrtype.I32)) →
    fun_cvtop__ numtype.F64 numtype.I32 (cvtop__.mk_cvtop___2 Fnn.F64 addrtype.I32 cvtop__Fnn_1_Inn_2.REINTERPRET) (num_.mk_num__1 Fnn.F64 f_1) [reinterpret__ (numtype_Fnn Fnn.F64) (numtype_addrtype addrtype.I32) (num_.mk_num__1 Fnn.F64 f_1)]
  | fun_cvtop___case_34 (f_1 : fN) :
    (size (numtype_Fnn Fnn.F32)) = (size (numtype_addrtype addrtype.I64)) →
    fun_cvtop__ numtype.F32 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F32 addrtype.I64 cvtop__Fnn_1_Inn_2.REINTERPRET) (num_.mk_num__1 Fnn.F32 f_1) [reinterpret__ (numtype_Fnn Fnn.F32) (numtype_addrtype addrtype.I64) (num_.mk_num__1 Fnn.F32 f_1)]
  | fun_cvtop___case_35 (f_1 : fN) :
    (size (numtype_Fnn Fnn.F64)) = (size (numtype_addrtype addrtype.I64)) →
    fun_cvtop__ numtype.F64 numtype.I64 (cvtop__.mk_cvtop___2 Fnn.F64 addrtype.I64 cvtop__Fnn_1_Inn_2.REINTERPRET) (num_.mk_num__1 Fnn.F64 f_1) [reinterpret__ (numtype_Fnn Fnn.F64) (numtype_addrtype addrtype.I64) (num_.mk_num__1 Fnn.F64 f_1)]


inductive cvtop___is_wf : numtype → numtype → cvtop__ → num_ → List num_ → Prop where
  | cvtop___is_wf_0 (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop__ : cvtop__) (v_num_ : num_) (ret_val_lst : List num_) (var_0 : List num_) :
    fun_cvtop__ numtype_1 numtype_2 v_cvtop__ v_num_ var_0 →
    wf_cvtop__ numtype_1 numtype_2 v_cvtop__ →
    wf_num_ numtype_1 v_num_ →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_num_ numtype_2 ret_val_elem) ret_val_lst →
    cvtop___is_wf numtype_1 numtype_2 v_cvtop__ v_num_ ret_val_lst


opaque lanes_ (v_shape : shape) (v_vec_ : vec_) : List lane_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive lanes__is_wf : shape → vec_ → List lane_ → Prop where
  | lanes__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (ret_val_lst : List lane_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    ret_val_lst = (lanes_ v_shape v_vec_) →
    Forall (fun ret_val_elem => wf_lane_ (fun_lanetype v_shape) ret_val_elem) ret_val_lst →
    lanes__is_wf v_shape v_vec_ ret_val_lst


opaque inv_lanes_ (v_shape : shape) (var_0_lst : List lane_) : vec_ := by
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_lanes__is_wf : shape → List lane_ → vec_ → Prop where
  | inv_lanes__is_wf_0 (v_shape : shape) (var_0_lst : List lane_) (ret_val : vec_) :
    wf_shape v_shape →
    Forall (fun var_0_elem => wf_lane_ (fun_lanetype v_shape) var_0_elem) var_0_lst →
    ret_val = (inv_lanes_ v_shape var_0_lst) →
    wf_uN 128 ret_val →
    inv_lanes__is_wf v_shape var_0_lst ret_val


inductive fun_zeroop : shape → shape → vcvtop__ → Option zero → Prop where
  | fun_zeroop_case_0 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_1 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_2 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_3 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_4 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_5 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_6 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_7 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_8 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_9 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_10 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_11 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_12 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_13 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_14 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_15 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) none
  | fun_zeroop_case_16 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I32 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_17 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I64 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_18 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I8 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_19 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I16 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_20 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I32 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_21 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I64 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_22 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I8 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_23 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I16 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) none
  | fun_zeroop_case_24 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_25 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_26 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_27 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_28 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_29 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_30 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_31 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) zero_opt
  | fun_zeroop_case_32 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_33 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_34 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_35 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_36 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_37 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_38 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_39 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) zero_opt
  | fun_zeroop_case_40 (M_1 : Nat) (M_2 : Nat) (v_zero : zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)) (some v_zero)
  | fun_zeroop_case_41 (M_1 : Nat) (M_2 : Nat) (v_zero : zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)) (some v_zero)
  | fun_zeroop_case_42 (M_1 : Nat) (M_2 : Nat) (v_zero : zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)) (some v_zero)
  | fun_zeroop_case_43 (M_1 : Nat) (M_2 : Nat) (v_zero : zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)) (some v_zero)
  | fun_zeroop_case_44 (M_1 : Nat) (M_2 : Nat) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F32 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) none
  | fun_zeroop_case_45 (M_1 : Nat) (M_2 : Nat) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F32 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) none
  | fun_zeroop_case_46 (M_1 : Nat) (M_2 : Nat) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F64 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) none
  | fun_zeroop_case_47 (M_1 : Nat) (M_2 : Nat) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_zeroop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F64 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) none


inductive fun_halfop : shape → shape → vcvtop__ → Option half → Prop where
  | fun_halfop_case_0 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_1 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_2 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_3 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_4 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_5 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_6 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_7 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_8 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_9 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_10 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_11 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_12 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_13 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_14 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_15 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (some v_half)
  | fun_halfop_case_16 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I32 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_17 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I64 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_18 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I8 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_19 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I16 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_20 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I32 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_21 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I64 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_22 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I8 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_23 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I16 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) half_opt
  | fun_halfop_case_24 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_25 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_26 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_27 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_28 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_29 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_30 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_31 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) none
  | fun_halfop_case_32 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_33 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_34 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_35 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_36 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_37 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I8 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_38 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_39 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I16 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) none
  | fun_halfop_case_40 (M_1 : Nat) (M_2 : Nat) (v_zero : zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)) none
  | fun_halfop_case_41 (M_1 : Nat) (M_2 : Nat) (v_zero : zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)) none
  | fun_halfop_case_42 (M_1 : Nat) (M_2 : Nat) (v_zero : zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)) none
  | fun_halfop_case_43 (M_1 : Nat) (M_2 : Nat) (v_zero : zero) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE v_zero)) none
  | fun_halfop_case_44 (M_1 : Nat) (M_2 : Nat) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F32 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) (some half.LOW)
  | fun_halfop_case_45 (M_1 : Nat) (M_2 : Nat) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F32 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) (some half.LOW)
  | fun_halfop_case_46 (M_1 : Nat) (M_2 : Nat) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F64 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) (some half.LOW)
  | fun_halfop_case_47 (M_1 : Nat) (M_2 : Nat) (M_1_0 : Nat) (M_2_0 : Nat) :
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_halfop (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F64 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) (some half.LOW)


def fun_half (v_half : half) (nat : Nat) (nat_0 : Nat) : Nat :=
  match v_half with
  | half.LOW => nat
  | half.HIGH => nat_0

def iswizzle_lane_ (v_N : N) (var_0_lst : List iN) (v_iN : iN) : iN :=
  if
    (proj_uN_0 v_iN) < (List.length var_0_lst)
  then
    (var_0_lst)[proj_uN_0 v_iN]!
  else
    uN.mk_uN 0

inductive iswizzle_lane__is_wf : N → List iN → iN → iN → Prop where
  | iswizzle_lane__is_wf_0 (v_N : N) (var_0_lst : List iN) (v_iN : iN) (ret_val : iN) :
    Forall (fun var_0_elem => wf_uN v_N var_0_elem) var_0_lst →
    wf_uN v_N v_iN →
    ret_val = (iswizzle_lane_ v_N var_0_lst v_iN) →
    wf_uN v_N ret_val →
    iswizzle_lane__is_wf v_N var_0_lst v_iN ret_val


def irelaxed_swizzle_lane_ (v_N : N) (var_0_lst : List iN) (v_iN : iN) : iN :=
  fun_signed_ v_N (proj_uN_0 v_iN) var_0 → if
    (proj_uN_0 v_iN) < (List.length var_0_lst)
  then
    (var_0_lst)[proj_uN_0 v_iN]!
  else
    if
      var_0 < (0 : Int)
    then
      uN.mk_uN 0
    else
      fun_relaxed2 R_swizzle iN (uN.mk_uN 0) ((var_0_lst)[(proj_uN_0 v_iN) % (List.length var_0_lst)]!)

inductive irelaxed_swizzle_lane__is_wf : N → List iN → iN → iN → Prop where
  | irelaxed_swizzle_lane__is_wf_0 (v_N : N) (var_0_lst : List iN) (v_iN : iN) (ret_val : iN) :
    Forall (fun var_0_elem => wf_uN v_N var_0_elem) var_0_lst →
    wf_uN v_N v_iN →
    ret_val = (irelaxed_swizzle_lane_ v_N var_0_lst v_iN) →
    wf_uN v_N ret_val →
    irelaxed_swizzle_lane__is_wf v_N var_0_lst v_iN ret_val


def ivunop_ (v_shape : shape) (f_ : N → iN → iN) (v_vec_ : vec_) : Option (List vec_) :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_2_elem => f_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 c_1_2_elem))) c_1_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun c_4_elem => lane_.mk_lane__2 Jnn.I32 c_4_elem) c_lst)]
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_4_elem => f_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 c_1_4_elem))) c_1_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun c_6_elem => lane_.mk_lane__2 Jnn.I64 c_6_elem) c_lst)]
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_6_elem => f_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 c_1_6_elem))) c_1_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun c_8_elem => lane_.mk_lane__2 Jnn.I8 c_8_elem) c_lst)]
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_8_elem => f_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 c_1_8_elem))) c_1_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun c_10_elem => lane_.mk_lane__2 Jnn.I16 c_10_elem) c_lst)]
  | _ => none

inductive ivunop__is_wf (f_ : N → iN → iN) : shape → vec_ → List vec_ → Prop where
  | ivunop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (ret_val_lst : List vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    (ivunop_ v_shape f_ v_vec_) ≠ none →
    ret_val_lst = (Option.get! (ivunop_ v_shape f_ v_vec_)) →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    ivunop__is_wf f_ v_shape v_vec_ ret_val_lst


def fvunop_ (v_shape : shape) (f_ : N → fN → List fN) (v_vec_ : vec_) : Option (List vec_) :=
  match v_shape with
  | shape.X lanetype.F32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v_vec_
  let c_lst_lst := setproduct_ lane_ (Map (fun c_1_10_elem => Map (fun iter_0_49_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_49_elem)) (f_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_10_elem)))))) c_1_lst)
  Forall (fun c_1_11_elem => Forall (fun iter_0_50_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_50_elem))) (f_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_11_elem)))))) c_1_lst → some (Map (fun c_lst_2_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) c_lst_2_elem) c_lst_lst)
  | shape.X lanetype.F64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v_vec_
  let c_lst_lst := setproduct_ lane_ (Map (fun c_1_13_elem => Map (fun iter_0_51_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_51_elem)) (f_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_13_elem)))))) c_1_lst)
  Forall (fun c_1_14_elem => Forall (fun iter_0_52_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_52_elem))) (f_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_14_elem)))))) c_1_lst → some (Map (fun c_lst_4_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) c_lst_4_elem) c_lst_lst)
  | _ => none

inductive fvunop__is_wf (f_ : N → fN → List fN) : shape → vec_ → List vec_ → Prop where
  | fvunop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (ret_val_lst : List vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    (fvunop_ v_shape f_ v_vec_) ≠ none →
    ret_val_lst = (Option.get! (fvunop_ v_shape f_ v_vec_)) →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    fvunop__is_wf f_ v_shape v_vec_ ret_val_lst


def ivbinop_ (v_shape : shape) (f_ : N → iN → iN → iN) (v_vec_ : vec_) (vec__0 : vec_) : Option (List vec_) :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_16_elem c_2_2_elem => f_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 c_1_16_elem)) (Option.get! (proj_lane__2 c_2_2_elem))) c_1_lst c_2_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun c_16_elem => lane_.mk_lane__2 Jnn.I32 c_16_elem) c_lst)]
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_18_elem c_2_4_elem => f_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 c_1_18_elem)) (Option.get! (proj_lane__2 c_2_4_elem))) c_1_lst c_2_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun c_18_elem => lane_.mk_lane__2 Jnn.I64 c_18_elem) c_lst)]
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_20_elem c_2_6_elem => f_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 c_1_20_elem)) (Option.get! (proj_lane__2 c_2_6_elem))) c_1_lst c_2_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun c_20_elem => lane_.mk_lane__2 Jnn.I8 c_20_elem) c_lst)]
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_22_elem c_2_8_elem => f_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 c_1_22_elem)) (Option.get! (proj_lane__2 c_2_8_elem))) c_1_lst c_2_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun c_22_elem => lane_.mk_lane__2 Jnn.I16 c_22_elem) c_lst)]
  | _ => none

inductive ivbinop__is_wf (f_ : N → iN → iN → iN) : shape → vec_ → vec_ → List vec_ → Prop where
  | ivbinop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : List vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (ivbinop_ v_shape f_ v_vec_ vec__0) ≠ none →
    ret_val_lst = (Option.get! (ivbinop_ v_shape f_ v_vec_ vec__0)) →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    ivbinop__is_wf f_ v_shape v_vec_ vec__0 ret_val_lst


def ivbinopsx_ (v_shape : shape) (f_ : N → sx → iN → iN → iN) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) : Option (List vec_) :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_24_elem c_2_10_elem => f_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_24_elem)) (Option.get! (proj_lane__2 c_2_10_elem))) c_1_lst c_2_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun c_24_elem => lane_.mk_lane__2 Jnn.I32 c_24_elem) c_lst)]
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_26_elem c_2_12_elem => f_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_26_elem)) (Option.get! (proj_lane__2 c_2_12_elem))) c_1_lst c_2_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun c_26_elem => lane_.mk_lane__2 Jnn.I64 c_26_elem) c_lst)]
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_28_elem c_2_14_elem => f_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_28_elem)) (Option.get! (proj_lane__2 c_2_14_elem))) c_1_lst c_2_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun c_28_elem => lane_.mk_lane__2 Jnn.I8 c_28_elem) c_lst)]
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_30_elem c_2_16_elem => f_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_30_elem)) (Option.get! (proj_lane__2 c_2_16_elem))) c_1_lst c_2_lst
  some [inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun c_30_elem => lane_.mk_lane__2 Jnn.I16 c_30_elem) c_lst)]
  | _ => none

inductive ivbinopsx__is_wf (f_ : N → sx → iN → iN → iN) : shape → sx → vec_ → vec_ → List vec_ → Prop where
  | ivbinopsx__is_wf_0 (v_shape : shape) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : List vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (ivbinopsx_ v_shape f_ v_sx v_vec_ vec__0) ≠ none →
    ret_val_lst = (Option.get! (ivbinopsx_ v_shape f_ v_sx v_vec_ vec__0)) →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    ivbinopsx__is_wf f_ v_shape v_sx v_vec_ vec__0 ret_val_lst


def ivbinopsxnd_ (v_shape : shape) (f_ : N → sx → iN → iN → List iN) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) : Option (List vec_) :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__0
  let c_lst_lst := setproduct_ lane_ (Map₂ (fun c_1_32_elem c_2_18_elem => Map (fun iter_0_53_elem => lane_.mk_lane__2 Jnn.I32 iter_0_53_elem) (f_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_32_elem)) (Option.get! (proj_lane__2 c_2_18_elem)))) c_1_lst c_2_lst)
  Forall₂ (fun c_1_33_elem c_2_19_elem => Forall (fun iter_0_54_elem => wf_lane_ (lanetype_Jnn Jnn.I32) (lane_.mk_lane__2 Jnn.I32 iter_0_54_elem)) (f_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_33_elem)) (Option.get! (proj_lane__2 c_2_19_elem)))) c_1_lst c_2_lst → some (Map (fun c_lst_6_elem => inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) c_lst_6_elem) c_lst_lst)
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__0
  let c_lst_lst := setproduct_ lane_ (Map₂ (fun c_1_35_elem c_2_21_elem => Map (fun iter_0_55_elem => lane_.mk_lane__2 Jnn.I64 iter_0_55_elem) (f_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_35_elem)) (Option.get! (proj_lane__2 c_2_21_elem)))) c_1_lst c_2_lst)
  Forall₂ (fun c_1_36_elem c_2_22_elem => Forall (fun iter_0_56_elem => wf_lane_ (lanetype_Jnn Jnn.I64) (lane_.mk_lane__2 Jnn.I64 iter_0_56_elem)) (f_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_36_elem)) (Option.get! (proj_lane__2 c_2_22_elem)))) c_1_lst c_2_lst → some (Map (fun c_lst_8_elem => inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) c_lst_8_elem) c_lst_lst)
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__0
  let c_lst_lst := setproduct_ lane_ (Map₂ (fun c_1_38_elem c_2_24_elem => Map (fun iter_0_57_elem => lane_.mk_lane__2 Jnn.I8 iter_0_57_elem) (f_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_38_elem)) (Option.get! (proj_lane__2 c_2_24_elem)))) c_1_lst c_2_lst)
  Forall₂ (fun c_1_39_elem c_2_25_elem => Forall (fun iter_0_58_elem => wf_lane_ (lanetype_Jnn Jnn.I8) (lane_.mk_lane__2 Jnn.I8 iter_0_58_elem)) (f_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_39_elem)) (Option.get! (proj_lane__2 c_2_25_elem)))) c_1_lst c_2_lst → some (Map (fun c_lst_10_elem => inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) c_lst_10_elem) c_lst_lst)
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__0
  let c_lst_lst := setproduct_ lane_ (Map₂ (fun c_1_41_elem c_2_27_elem => Map (fun iter_0_59_elem => lane_.mk_lane__2 Jnn.I16 iter_0_59_elem) (f_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_41_elem)) (Option.get! (proj_lane__2 c_2_27_elem)))) c_1_lst c_2_lst)
  Forall₂ (fun c_1_42_elem c_2_28_elem => Forall (fun iter_0_60_elem => wf_lane_ (lanetype_Jnn Jnn.I16) (lane_.mk_lane__2 Jnn.I16 iter_0_60_elem)) (f_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_42_elem)) (Option.get! (proj_lane__2 c_2_28_elem)))) c_1_lst c_2_lst → some (Map (fun c_lst_12_elem => inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) c_lst_12_elem) c_lst_lst)
  | _ => none

inductive ivbinopsxnd__is_wf (f_ : N → sx → iN → iN → List iN) : shape → sx → vec_ → vec_ → List vec_ → Prop where
  | ivbinopsxnd__is_wf_0 (v_shape : shape) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : List vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (ivbinopsxnd_ v_shape f_ v_sx v_vec_ vec__0) ≠ none →
    ret_val_lst = (Option.get! (ivbinopsxnd_ v_shape f_ v_sx v_vec_ vec__0)) →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    ivbinopsxnd__is_wf f_ v_shape v_sx v_vec_ vec__0 ret_val_lst


def fvbinop_ (v_shape : shape) (f_ : N → fN → fN → List fN) (v_vec_ : vec_) (vec__0 : vec_) : Option (List vec_) :=
  match v_shape with
  | shape.X lanetype.F32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) vec__0
  let c_lst_lst := setproduct_ lane_ (Map₂ (fun c_1_44_elem c_2_30_elem => Map (fun iter_0_61_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_61_elem)) (f_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_44_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_30_elem)))))) c_1_lst c_2_lst)
  Forall₂ (fun c_1_45_elem c_2_31_elem => Forall (fun iter_0_62_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_62_elem))) (f_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_45_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_31_elem)))))) c_1_lst c_2_lst → some (Map (fun c_lst_14_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) c_lst_14_elem) c_lst_lst)
  | shape.X lanetype.F64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) vec__0
  let c_lst_lst := setproduct_ lane_ (Map₂ (fun c_1_47_elem c_2_33_elem => Map (fun iter_0_63_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_63_elem)) (f_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_47_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_33_elem)))))) c_1_lst c_2_lst)
  Forall₂ (fun c_1_48_elem c_2_34_elem => Forall (fun iter_0_64_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_64_elem))) (f_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_48_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_34_elem)))))) c_1_lst c_2_lst → some (Map (fun c_lst_16_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) c_lst_16_elem) c_lst_lst)
  | _ => none

inductive fvbinop__is_wf (f_ : N → fN → fN → List fN) : shape → vec_ → vec_ → List vec_ → Prop where
  | fvbinop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : List vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (fvbinop_ v_shape f_ v_vec_ vec__0) ≠ none →
    ret_val_lst = (Option.get! (fvbinop_ v_shape f_ v_vec_ vec__0)) →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    fvbinop__is_wf f_ v_shape v_vec_ vec__0 ret_val_lst


def ivternopnd_ (v_shape : shape) (f_ : N → iN → iN → iN → List iN) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) : Option (List vec_) :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__0
  let c_3_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__1
  let c_lst_lst := setproduct_ lane_ (Map₃ (fun c_1_50_elem c_2_36_elem c_3_2_elem => Map (fun iter_0_65_elem => lane_.mk_lane__2 Jnn.I32 iter_0_65_elem) (f_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 c_1_50_elem)) (Option.get! (proj_lane__2 c_2_36_elem)) (Option.get! (proj_lane__2 c_3_2_elem)))) c_1_lst c_2_lst c_3_lst)
  Forall₃ (fun c_1_51_elem c_2_37_elem c_3_3_elem => Forall (fun iter_0_66_elem => wf_lane_ (lanetype_Jnn Jnn.I32) (lane_.mk_lane__2 Jnn.I32 iter_0_66_elem)) (f_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 c_1_51_elem)) (Option.get! (proj_lane__2 c_2_37_elem)) (Option.get! (proj_lane__2 c_3_3_elem)))) c_1_lst c_2_lst c_3_lst → some (Map (fun c_lst_18_elem => inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) c_lst_18_elem) c_lst_lst)
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__0
  let c_3_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__1
  let c_lst_lst := setproduct_ lane_ (Map₃ (fun c_1_53_elem c_2_39_elem c_3_5_elem => Map (fun iter_0_67_elem => lane_.mk_lane__2 Jnn.I64 iter_0_67_elem) (f_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 c_1_53_elem)) (Option.get! (proj_lane__2 c_2_39_elem)) (Option.get! (proj_lane__2 c_3_5_elem)))) c_1_lst c_2_lst c_3_lst)
  Forall₃ (fun c_1_54_elem c_2_40_elem c_3_6_elem => Forall (fun iter_0_68_elem => wf_lane_ (lanetype_Jnn Jnn.I64) (lane_.mk_lane__2 Jnn.I64 iter_0_68_elem)) (f_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 c_1_54_elem)) (Option.get! (proj_lane__2 c_2_40_elem)) (Option.get! (proj_lane__2 c_3_6_elem)))) c_1_lst c_2_lst c_3_lst → some (Map (fun c_lst_20_elem => inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) c_lst_20_elem) c_lst_lst)
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__0
  let c_3_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__1
  let c_lst_lst := setproduct_ lane_ (Map₃ (fun c_1_56_elem c_2_42_elem c_3_8_elem => Map (fun iter_0_69_elem => lane_.mk_lane__2 Jnn.I8 iter_0_69_elem) (f_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 c_1_56_elem)) (Option.get! (proj_lane__2 c_2_42_elem)) (Option.get! (proj_lane__2 c_3_8_elem)))) c_1_lst c_2_lst c_3_lst)
  Forall₃ (fun c_1_57_elem c_2_43_elem c_3_9_elem => Forall (fun iter_0_70_elem => wf_lane_ (lanetype_Jnn Jnn.I8) (lane_.mk_lane__2 Jnn.I8 iter_0_70_elem)) (f_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 c_1_57_elem)) (Option.get! (proj_lane__2 c_2_43_elem)) (Option.get! (proj_lane__2 c_3_9_elem)))) c_1_lst c_2_lst c_3_lst → some (Map (fun c_lst_22_elem => inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) c_lst_22_elem) c_lst_lst)
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__0
  let c_3_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__1
  let c_lst_lst := setproduct_ lane_ (Map₃ (fun c_1_59_elem c_2_45_elem c_3_11_elem => Map (fun iter_0_71_elem => lane_.mk_lane__2 Jnn.I16 iter_0_71_elem) (f_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 c_1_59_elem)) (Option.get! (proj_lane__2 c_2_45_elem)) (Option.get! (proj_lane__2 c_3_11_elem)))) c_1_lst c_2_lst c_3_lst)
  Forall₃ (fun c_1_60_elem c_2_46_elem c_3_12_elem => Forall (fun iter_0_72_elem => wf_lane_ (lanetype_Jnn Jnn.I16) (lane_.mk_lane__2 Jnn.I16 iter_0_72_elem)) (f_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 c_1_60_elem)) (Option.get! (proj_lane__2 c_2_46_elem)) (Option.get! (proj_lane__2 c_3_12_elem)))) c_1_lst c_2_lst c_3_lst → some (Map (fun c_lst_24_elem => inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) c_lst_24_elem) c_lst_lst)
  | _ => none

inductive ivternopnd__is_wf (f_ : N → iN → iN → iN → List iN) : shape → vec_ → vec_ → vec_ → List vec_ → Prop where
  | ivternopnd__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val_lst : List vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    wf_uN 128 vec__1 →
    (ivternopnd_ v_shape f_ v_vec_ vec__0 vec__1) ≠ none →
    ret_val_lst = (Option.get! (ivternopnd_ v_shape f_ v_vec_ vec__0 vec__1)) →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    ivternopnd__is_wf f_ v_shape v_vec_ vec__0 vec__1 ret_val_lst


def fvternop_ (v_shape : shape) (f_ : N → fN → fN → fN → List fN) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) : Option (List vec_) :=
  match v_shape with
  | shape.X lanetype.F32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) vec__0
  let c_3_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) vec__1
  let c_lst_lst := setproduct_ lane_ (Map₃ (fun c_1_62_elem c_2_48_elem c_3_14_elem => Map (fun iter_0_73_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_73_elem)) (f_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_62_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_48_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_3_14_elem)))))) c_1_lst c_2_lst c_3_lst)
  Forall₃ (fun c_1_63_elem c_2_49_elem c_3_15_elem => Forall (fun iter_0_74_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_74_elem))) (f_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_63_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_49_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_3_15_elem)))))) c_1_lst c_2_lst c_3_lst → some (Map (fun c_lst_26_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) c_lst_26_elem) c_lst_lst)
  | shape.X lanetype.F64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) vec__0
  let c_3_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) vec__1
  let c_lst_lst := setproduct_ lane_ (Map₃ (fun c_1_65_elem c_2_51_elem c_3_17_elem => Map (fun iter_0_75_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_75_elem)) (f_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_65_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_51_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_3_17_elem)))))) c_1_lst c_2_lst c_3_lst)
  Forall₃ (fun c_1_66_elem c_2_52_elem c_3_18_elem => Forall (fun iter_0_76_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_76_elem))) (f_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_66_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_52_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_3_18_elem)))))) c_1_lst c_2_lst c_3_lst → some (Map (fun c_lst_28_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) c_lst_28_elem) c_lst_lst)
  | _ => none

inductive fvternop__is_wf (f_ : N → fN → fN → fN → List fN) : shape → vec_ → vec_ → vec_ → List vec_ → Prop where
  | fvternop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val_lst : List vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    wf_uN 128 vec__1 →
    (fvternop_ v_shape f_ v_vec_ vec__0 vec__1) ≠ none →
    ret_val_lst = (Option.get! (fvternop_ v_shape f_ v_vec_ vec__0 vec__1)) →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    fvternop__is_wf f_ v_shape v_vec_ vec__0 vec__1 ret_val_lst


def ivrelop_ (v_shape : shape) (f_ : N → iN → iN → u32) (v_vec_ : vec_) (vec__0 : vec_) : Option vec_ :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_68_elem c_2_54_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 c_1_68_elem)) (Option.get! (proj_lane__2 c_2_54_elem)))))) c_1_lst c_2_lst
  Forall₂ (fun c_1_69_elem c_2_55_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 c_1_69_elem)) (Option.get! (proj_lane__2 c_2_55_elem)))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun c_56_elem => lane_.mk_lane__2 Jnn.I32 c_56_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_71_elem c_2_57_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 c_1_71_elem)) (Option.get! (proj_lane__2 c_2_57_elem)))))) c_1_lst c_2_lst
  Forall₂ (fun c_1_72_elem c_2_58_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 c_1_72_elem)) (Option.get! (proj_lane__2 c_2_58_elem)))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun c_58_elem => lane_.mk_lane__2 Jnn.I64 c_58_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_74_elem c_2_60_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 c_1_74_elem)) (Option.get! (proj_lane__2 c_2_60_elem)))))) c_1_lst c_2_lst
  Forall₂ (fun c_1_75_elem c_2_61_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 c_1_75_elem)) (Option.get! (proj_lane__2 c_2_61_elem)))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun c_60_elem => lane_.mk_lane__2 Jnn.I8 c_60_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_77_elem c_2_63_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 c_1_77_elem)) (Option.get! (proj_lane__2 c_2_63_elem)))))) c_1_lst c_2_lst
  Forall₂ (fun c_1_78_elem c_2_64_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 c_1_78_elem)) (Option.get! (proj_lane__2 c_2_64_elem)))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun c_62_elem => lane_.mk_lane__2 Jnn.I16 c_62_elem) c_lst))
  | _ => none

inductive ivrelop__is_wf (f_ : N → iN → iN → u32) : shape → vec_ → vec_ → vec_ → Prop where
  | ivrelop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (ivrelop_ v_shape f_ v_vec_ vec__0) ≠ none →
    ret_val = (Option.get! (ivrelop_ v_shape f_ v_vec_ vec__0)) →
    wf_uN 128 ret_val →
    ivrelop__is_wf f_ v_shape v_vec_ vec__0 ret_val


def ivrelopsx_ (v_shape : shape) (f_ : N → sx → iN → iN → u32) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) : Option vec_ :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_80_elem c_2_66_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_80_elem)) (Option.get! (proj_lane__2 c_2_66_elem)))))) c_1_lst c_2_lst
  Forall₂ (fun c_1_81_elem c_2_67_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_81_elem)) (Option.get! (proj_lane__2 c_2_67_elem)))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun c_64_elem => lane_.mk_lane__2 Jnn.I32 c_64_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_83_elem c_2_69_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_83_elem)) (Option.get! (proj_lane__2 c_2_69_elem)))))) c_1_lst c_2_lst
  Forall₂ (fun c_1_84_elem c_2_70_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_84_elem)) (Option.get! (proj_lane__2 c_2_70_elem)))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun c_66_elem => lane_.mk_lane__2 Jnn.I64 c_66_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_86_elem c_2_72_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_86_elem)) (Option.get! (proj_lane__2 c_2_72_elem)))))) c_1_lst c_2_lst
  Forall₂ (fun c_1_87_elem c_2_73_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_87_elem)) (Option.get! (proj_lane__2 c_2_73_elem)))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun c_68_elem => lane_.mk_lane__2 Jnn.I8 c_68_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_89_elem c_2_75_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_89_elem)) (Option.get! (proj_lane__2 c_2_75_elem)))))) c_1_lst c_2_lst
  Forall₂ (fun c_1_90_elem c_2_76_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_90_elem)) (Option.get! (proj_lane__2 c_2_76_elem)))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun c_70_elem => lane_.mk_lane__2 Jnn.I16 c_70_elem) c_lst))
  | _ => none

inductive ivrelopsx__is_wf (f_ : N → sx → iN → iN → u32) : shape → sx → vec_ → vec_ → vec_ → Prop where
  | ivrelopsx__is_wf_0 (v_shape : shape) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (ivrelopsx_ v_shape f_ v_sx v_vec_ vec__0) ≠ none →
    ret_val = (Option.get! (ivrelopsx_ v_shape f_ v_sx v_vec_ vec__0)) →
    wf_uN 128 ret_val →
    ivrelopsx__is_wf f_ v_shape v_sx v_vec_ vec__0 ret_val


def fvrelop_ (v_shape : shape) (f_ : N → fN → fN → u32) (v_vec_ : vec_) (vec__0 : vec_) : Option vec_ :=
  match v_shape with
  | shape.X lanetype.F32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_92_elem c_2_78_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (uN.mk_uN (proj_uN_0 (f_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_92_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_78_elem)))))))) c_1_lst c_2_lst
  (isize v_Inn) = (fsize Fnn.F32) → wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) → Forall₂ (fun c_1_93_elem c_2_79_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_93_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_79_elem)))))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_addrtype v_Inn) (dim.mk_dim v_M)) (Map (fun c_72_elem => lane_.mk_lane__0 (numtype_addrtype v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 c_72_elem)))) c_lst))
  | shape.X lanetype.F64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) vec__0
  let c_lst := Map₂ (fun c_1_95_elem c_2_81_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (uN.mk_uN (proj_uN_0 (f_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_95_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_81_elem)))))))) c_1_lst c_2_lst
  (isize v_Inn) = (fsize Fnn.F64) → wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) → Forall₂ (fun c_1_96_elem c_2_82_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (f_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_1_96_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 c_2_82_elem)))))))) c_1_lst c_2_lst → some (inv_lanes_ (shape.X (lanetype_addrtype v_Inn) (dim.mk_dim v_M)) (Map (fun c_74_elem => lane_.mk_lane__0 (numtype_addrtype v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 c_74_elem)))) c_lst))
  | _ => none

inductive fvrelop__is_wf (f_ : N → fN → fN → u32) : shape → vec_ → vec_ → vec_ → Prop where
  | fvrelop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (fvrelop_ v_shape f_ v_vec_ vec__0) ≠ none →
    ret_val = (Option.get! (fvrelop_ v_shape f_ v_vec_ vec__0)) →
    wf_uN 128 ret_val →
    fvrelop__is_wf f_ v_shape v_vec_ vec__0 ret_val


def ivshiftop_ (v_shape : shape) (f_ : N → iN → u32 → iN) (v_vec_ : vec_) (v_u32 : u32) : Option vec_ :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_98_elem => f_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 c_1_98_elem)) v_u32) c_1_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun c_76_elem => lane_.mk_lane__2 Jnn.I32 c_76_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_100_elem => f_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 c_1_100_elem)) v_u32) c_1_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun c_78_elem => lane_.mk_lane__2 Jnn.I64 c_78_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_102_elem => f_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 c_1_102_elem)) v_u32) c_1_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun c_80_elem => lane_.mk_lane__2 Jnn.I8 c_80_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_104_elem => f_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 c_1_104_elem)) v_u32) c_1_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun c_82_elem => lane_.mk_lane__2 Jnn.I16 c_82_elem) c_lst))
  | _ => none

inductive ivshiftop__is_wf (f_ : N → iN → u32 → iN) : shape → vec_ → u32 → vec_ → Prop where
  | ivshiftop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (v_u32 : u32) (ret_val : vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 32 v_u32 →
    (ivshiftop_ v_shape f_ v_vec_ v_u32) ≠ none →
    ret_val = (Option.get! (ivshiftop_ v_shape f_ v_vec_ v_u32)) →
    wf_uN 128 ret_val →
    ivshiftop__is_wf f_ v_shape v_vec_ v_u32 ret_val


def ivshiftopsx_ (v_shape : shape) (f_ : N → sx → iN → u32 → iN) (v_sx : sx) (v_vec_ : vec_) (v_u32 : u32) : Option vec_ :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_106_elem => f_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_106_elem)) v_u32) c_1_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun c_84_elem => lane_.mk_lane__2 Jnn.I32 c_84_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_108_elem => f_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_108_elem)) v_u32) c_1_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun c_86_elem => lane_.mk_lane__2 Jnn.I64 c_86_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_110_elem => f_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_110_elem)) v_u32) c_1_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun c_88_elem => lane_.mk_lane__2 Jnn.I8 c_88_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_lst := Map (fun c_1_112_elem => f_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_112_elem)) v_u32) c_1_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun c_90_elem => lane_.mk_lane__2 Jnn.I16 c_90_elem) c_lst))
  | _ => none

inductive ivshiftopsx__is_wf (f_ : N → sx → iN → u32 → iN) : shape → sx → vec_ → u32 → vec_ → Prop where
  | ivshiftopsx__is_wf_0 (v_shape : shape) (v_sx : sx) (v_vec_ : vec_) (v_u32 : u32) (ret_val : vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 32 v_u32 →
    (ivshiftopsx_ v_shape f_ v_sx v_vec_ v_u32) ≠ none →
    ret_val = (Option.get! (ivshiftopsx_ v_shape f_ v_sx v_vec_ v_u32)) →
    wf_uN 128 ret_val →
    ivshiftopsx__is_wf f_ v_shape v_sx v_vec_ v_u32 ret_val


inductive fun_ivbitmaskop_ : shape → vec_ → u32 → Prop where
  | fun_ivbitmaskop__case_0 (v_M : Nat) (v_1 : uN) (c : uN) (c_1_lst : List lane_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_1) →
    Forall (fun c_1_114_elem => (proj_lane__2 c_1_114_elem) ≠ none) c_1_lst →
    (ibits_ 32 c) = ((Map (fun c_1_114_elem => bit.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (Option.get! (proj_lane__2 c_1_114_elem)) (uN.mk_uN 0)))) c_1_lst) ++ (List.replicate (Int.toNat ((32 : Int) - (v_M : Int))) (bit.mk_bit 0))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun c_1_115_elem => (proj_lane__2 c_1_115_elem) ≠ none) c_1_lst →
    Forall (fun c_1_115_elem => wf_bit (bit.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (Option.get! (proj_lane__2 c_1_115_elem)) (uN.mk_uN 0))))) c_1_lst →
    wf_bit (bit.mk_bit 0) →
    fun_ivbitmaskop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) v_1 (irev_ 32 c)
  | fun_ivbitmaskop__case_1 (v_M : Nat) (v_1 : uN) (c : uN) (c_1_lst : List lane_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_1) →
    Forall (fun c_1_117_elem => (proj_lane__2 c_1_117_elem) ≠ none) c_1_lst →
    (ibits_ 32 c) = ((Map (fun c_1_117_elem => bit.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (Option.get! (proj_lane__2 c_1_117_elem)) (uN.mk_uN 0)))) c_1_lst) ++ (List.replicate (Int.toNat ((32 : Int) - (v_M : Int))) (bit.mk_bit 0))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun c_1_118_elem => (proj_lane__2 c_1_118_elem) ≠ none) c_1_lst →
    Forall (fun c_1_118_elem => wf_bit (bit.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (Option.get! (proj_lane__2 c_1_118_elem)) (uN.mk_uN 0))))) c_1_lst →
    wf_bit (bit.mk_bit 0) →
    fun_ivbitmaskop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) v_1 (irev_ 32 c)
  | fun_ivbitmaskop__case_2 (v_M : Nat) (v_1 : uN) (c : uN) (c_1_lst : List lane_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_1) →
    Forall (fun c_1_120_elem => (proj_lane__2 c_1_120_elem) ≠ none) c_1_lst →
    (ibits_ 32 c) = ((Map (fun c_1_120_elem => bit.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (Option.get! (proj_lane__2 c_1_120_elem)) (uN.mk_uN 0)))) c_1_lst) ++ (List.replicate (Int.toNat ((32 : Int) - (v_M : Int))) (bit.mk_bit 0))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun c_1_121_elem => (proj_lane__2 c_1_121_elem) ≠ none) c_1_lst →
    Forall (fun c_1_121_elem => wf_bit (bit.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (Option.get! (proj_lane__2 c_1_121_elem)) (uN.mk_uN 0))))) c_1_lst →
    wf_bit (bit.mk_bit 0) →
    fun_ivbitmaskop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) v_1 (irev_ 32 c)
  | fun_ivbitmaskop__case_3 (v_M : Nat) (v_1 : uN) (c : uN) (c_1_lst : List lane_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_1) →
    Forall (fun c_1_123_elem => (proj_lane__2 c_1_123_elem) ≠ none) c_1_lst →
    (ibits_ 32 c) = ((Map (fun c_1_123_elem => bit.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (Option.get! (proj_lane__2 c_1_123_elem)) (uN.mk_uN 0)))) c_1_lst) ++ (List.replicate (Int.toNat ((32 : Int) - (v_M : Int))) (bit.mk_bit 0))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun c_1_124_elem => (proj_lane__2 c_1_124_elem) ≠ none) c_1_lst →
    Forall (fun c_1_124_elem => wf_bit (bit.mk_bit (proj_uN_0 (ilt_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (Option.get! (proj_lane__2 c_1_124_elem)) (uN.mk_uN 0))))) c_1_lst →
    wf_bit (bit.mk_bit 0) →
    fun_ivbitmaskop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) v_1 (irev_ 32 c)


inductive ivbitmaskop__is_wf : shape → vec_ → u32 → Prop where
  | ivbitmaskop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (ret_val : u32) (var_0 : u32) :
    fun_ivbitmaskop_ v_shape v_vec_ var_0 →
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    ret_val = var_0 →
    wf_uN 32 ret_val →
    ivbitmaskop__is_wf v_shape v_vec_ ret_val


def ivswizzlop_ (v_shape : shape) (f_ : N → List iN → iN → iN) (v_vec_ : vec_) (vec__0 : vec_) : Option vec_ :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__0
  let c_lst := Map (fun c_2_84_elem => f_ (lsizenn (lanetype_Jnn Jnn.I32)) (Map (fun c_1_126_elem => Option.get! (proj_lane__2 c_1_126_elem)) c_1_lst) (Option.get! (proj_lane__2 c_2_84_elem))) c_2_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun c_92_elem => lane_.mk_lane__2 Jnn.I32 c_92_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__0
  let c_lst := Map (fun c_2_86_elem => f_ (lsizenn (lanetype_Jnn Jnn.I64)) (Map (fun c_1_128_elem => Option.get! (proj_lane__2 c_1_128_elem)) c_1_lst) (Option.get! (proj_lane__2 c_2_86_elem))) c_2_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun c_94_elem => lane_.mk_lane__2 Jnn.I64 c_94_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__0
  let c_lst := Map (fun c_2_88_elem => f_ (lsizenn (lanetype_Jnn Jnn.I8)) (Map (fun c_1_130_elem => Option.get! (proj_lane__2 c_1_130_elem)) c_1_lst) (Option.get! (proj_lane__2 c_2_88_elem))) c_2_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun c_96_elem => lane_.mk_lane__2 Jnn.I8 c_96_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__0
  let c_lst := Map (fun c_2_90_elem => f_ (lsizenn (lanetype_Jnn Jnn.I16)) (Map (fun c_1_132_elem => Option.get! (proj_lane__2 c_1_132_elem)) c_1_lst) (Option.get! (proj_lane__2 c_2_90_elem))) c_2_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun c_98_elem => lane_.mk_lane__2 Jnn.I16 c_98_elem) c_lst))
  | _ => none

inductive ivswizzlop__is_wf (f_ : N → List iN → iN → iN) : shape → vec_ → vec_ → vec_ → Prop where
  | ivswizzlop__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) :
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (ivswizzlop_ v_shape f_ v_vec_ vec__0) ≠ none →
    ret_val = (Option.get! (ivswizzlop_ v_shape f_ v_vec_ vec__0)) →
    wf_uN 128 ret_val →
    ivswizzlop__is_wf f_ v_shape v_vec_ vec__0 ret_val


def ivshufflop_ (v_shape : shape) (var_0_lst : List laneidx) (v_vec_ : vec_) (vec__0 : vec_) : Option vec_ :=
  match v_shape with
  | shape.X lanetype.I32 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) vec__0
  let c_lst := Map (fun i_42250_elem => (c_1_lst ++ c_2_lst)[proj_uN_0 i_42250_elem]!) var_0_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) c_lst)
  | shape.X lanetype.I64 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) vec__0
  let c_lst := Map (fun i_42256_elem => (c_1_lst ++ c_2_lst)[proj_uN_0 i_42256_elem]!) var_0_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) c_lst)
  | shape.X lanetype.I8 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) vec__0
  let c_lst := Map (fun i_42262_elem => (c_1_lst ++ c_2_lst)[proj_uN_0 i_42262_elem]!) var_0_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) c_lst)
  | shape.X lanetype.I16 (dim.mk_dim v_M) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v_vec_
  let c_2_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) vec__0
  let c_lst := Map (fun i_42268_elem => (c_1_lst ++ c_2_lst)[proj_uN_0 i_42268_elem]!) var_0_lst
  some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) c_lst)
  | _ => none

inductive ivshufflop__is_wf : shape → List laneidx → vec_ → vec_ → vec_ → Prop where
  | ivshufflop__is_wf_0 (v_shape : shape) (var_0_lst : List laneidx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) :
    wf_shape v_shape →
    Forall (fun var_0_elem => wf_uN 8 var_0_elem) var_0_lst →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (ivshufflop_ v_shape var_0_lst v_vec_ vec__0) ≠ none →
    ret_val = (Option.get! (ivshufflop_ v_shape var_0_lst v_vec_ vec__0)) →
    wf_uN 128 ret_val →
    ivshufflop__is_wf v_shape var_0_lst v_vec_ vec__0 ret_val


def vvunop_ (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) : List vec_ :=
  match v_vvunop with
  | vvunop.NOT => [inot_ (vsizenn v_vectype) v_vec_]

inductive vvunop__is_wf : vectype → vvunop → vec_ → List vec_ → Prop where
  | vvunop__is_wf_0 (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) (ret_val_lst : List vec_) :
    wf_uN (vsize v_vectype) v_vec_ →
    ret_val_lst = (vvunop_ v_vectype v_vvunop v_vec_) →
    Forall (fun ret_val_elem => wf_uN (vsize v_vectype) ret_val_elem) ret_val_lst →
    vvunop__is_wf v_vectype v_vvunop v_vec_ ret_val_lst


def vvbinop_ (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) : List vec_ :=
  match v_vvbinop with
  | vvbinop.AND => [iand_ (vsizenn v_vectype) v_vec_ vec__0]
  | vvbinop.ANDNOT => [iandnot_ (vsizenn v_vectype) v_vec_ vec__0]
  | vvbinop.OR => [ior_ (vsizenn v_vectype) v_vec_ vec__0]
  | vvbinop.XOR => [ixor_ (vsizenn v_vectype) v_vec_ vec__0]

inductive vvbinop__is_wf : vectype → vvbinop → vec_ → vec_ → List vec_ → Prop where
  | vvbinop__is_wf_0 (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : List vec_) :
    wf_uN (vsize v_vectype) v_vec_ →
    wf_uN (vsize v_vectype) vec__0 →
    ret_val_lst = (vvbinop_ v_vectype v_vvbinop v_vec_ vec__0) →
    Forall (fun ret_val_elem => wf_uN (vsize v_vectype) ret_val_elem) ret_val_lst →
    vvbinop__is_wf v_vectype v_vvbinop v_vec_ vec__0 ret_val_lst


def vvternop_ (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) : List vec_ :=
  match v_vvternop with
  | vvternop.BITSELECT => [ibitselect_ (vsizenn v_vectype) v_vec_ vec__0 vec__1]

inductive vvternop__is_wf : vectype → vvternop → vec_ → vec_ → vec_ → List vec_ → Prop where
  | vvternop__is_wf_0 (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val_lst : List vec_) :
    wf_uN (vsize v_vectype) v_vec_ →
    wf_uN (vsize v_vectype) vec__0 →
    wf_uN (vsize v_vectype) vec__1 →
    ret_val_lst = (vvternop_ v_vectype v_vvternop v_vec_ vec__0 vec__1) →
    Forall (fun ret_val_elem => wf_uN (vsize v_vectype) ret_val_elem) ret_val_lst →
    vvternop__is_wf v_vectype v_vvternop v_vec_ vec__0 vec__1 ret_val_lst


inductive fun_vunop_ : shape → vunop_ → vec_ → List vec_ → Prop where
  | fun_vunop__case_0 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fabs_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_M.ABS) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fabs_ v))
  | fun_vunop__case_1 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fabs_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_M.ABS) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fabs_ v))
  | fun_vunop__case_2 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fneg_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_M.NEG) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fneg_ v))
  | fun_vunop__case_3 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fneg_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_M.NEG) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fneg_ v))
  | fun_vunop__case_4 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fsqrt_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_M.SQRT) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fsqrt_ v))
  | fun_vunop__case_5 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fsqrt_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_M.SQRT) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fsqrt_ v))
  | fun_vunop__case_6 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fceil_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_M.CEIL) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fceil_ v))
  | fun_vunop__case_7 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fceil_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_M.CEIL) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fceil_ v))
  | fun_vunop__case_8 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) ffloor_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_M.FLOOR) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) ffloor_ v))
  | fun_vunop__case_9 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) ffloor_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_M.FLOOR) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) ffloor_ v))
  | fun_vunop__case_10 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) ftrunc_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_M.TRUNC) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) ftrunc_ v))
  | fun_vunop__case_11 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) ftrunc_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_M.TRUNC) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) ftrunc_ v))
  | fun_vunop__case_12 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fnearest_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_M.NEAREST) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fnearest_ v))
  | fun_vunop__case_13 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fnearest_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_M.NEAREST) v (Option.get! (fvunop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fnearest_ v))
  | fun_vunop__case_14 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iabs_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_M.ABS) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iabs_ v))
  | fun_vunop__case_15 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iabs_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_M.ABS) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iabs_ v))
  | fun_vunop__case_16 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iabs_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_M.ABS) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iabs_ v))
  | fun_vunop__case_17 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iabs_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_M.ABS) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iabs_ v))
  | fun_vunop__case_18 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ineg_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_M.NEG) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ineg_ v))
  | fun_vunop__case_19 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ineg_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_M.NEG) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ineg_ v))
  | fun_vunop__case_20 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ineg_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_M.NEG) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ineg_ v))
  | fun_vunop__case_21 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ineg_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_M.NEG) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ineg_ v))
  | fun_vunop__case_22 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ipopcnt_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_M.POPCNT) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ipopcnt_ v))
  | fun_vunop__case_23 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ipopcnt_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_M.POPCNT) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ipopcnt_ v))
  | fun_vunop__case_24 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ipopcnt_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_M.POPCNT) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ipopcnt_ v))
  | fun_vunop__case_25 (v_M : Nat) (v : uN) (M_0 : Nat) :
    (ivunop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ipopcnt_ v) ≠ none →
    v_M = M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_M.POPCNT) v (Option.get! (ivunop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ipopcnt_ v))


inductive vunop__is_wf : shape → vunop_ → vec_ → List vec_ → Prop where
  | vunop__is_wf_0 (v_shape : shape) (v_vunop_ : vunop_) (v_vec_ : vec_) (ret_val_lst : List vec_) (var_0 : List vec_) :
    fun_vunop_ v_shape v_vunop_ v_vec_ var_0 →
    wf_shape v_shape →
    wf_vunop_ v_shape v_vunop_ →
    wf_uN 128 v_vec_ →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    vunop__is_wf v_shape v_vunop_ v_vec_ ret_val_lst


inductive fun_vbinop_ : shape → vbinop_ → vec_ → vec_ → List vec_ → Prop where
  | fun_vbinop__case_0 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iadd_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_M.ADD) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iadd_ v_1 v_2))
  | fun_vbinop__case_1 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iadd_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_M.ADD) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iadd_ v_1 v_2))
  | fun_vbinop__case_2 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iadd_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_M.ADD) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iadd_ v_1 v_2))
  | fun_vbinop__case_3 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iadd_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_M.ADD) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iadd_ v_1 v_2))
  | fun_vbinop__case_4 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) isub_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_M.SUB) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) isub_ v_1 v_2))
  | fun_vbinop__case_5 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) isub_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_M.SUB) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) isub_ v_1 v_2))
  | fun_vbinop__case_6 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) isub_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_M.SUB) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) isub_ v_1 v_2))
  | fun_vbinop__case_7 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) isub_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_M.SUB) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) isub_ v_1 v_2))
  | fun_vbinop__case_8 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) imul_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_M.MUL) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) imul_ v_1 v_2))
  | fun_vbinop__case_9 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) imul_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_M.MUL) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) imul_ v_1 v_2))
  | fun_vbinop__case_10 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) imul_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_M.MUL) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) imul_ v_1 v_2))
  | fun_vbinop__case_11 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) imul_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_M.MUL) v_1 v_2 (Option.get! (ivbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) imul_ v_1 v_2))
  | fun_vbinop__case_12 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_M.ADD_SAT v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2))
  | fun_vbinop__case_13 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_M.ADD_SAT v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2))
  | fun_vbinop__case_14 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_M.ADD_SAT v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2))
  | fun_vbinop__case_15 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_M.ADD_SAT v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iadd_sat_ v_sx v_1 v_2))
  | fun_vbinop__case_16 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) isub_sat_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_M.SUB_SAT v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) isub_sat_ v_sx v_1 v_2))
  | fun_vbinop__case_17 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) isub_sat_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_M.SUB_SAT v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) isub_sat_ v_sx v_1 v_2))
  | fun_vbinop__case_18 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) isub_sat_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_M.SUB_SAT v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) isub_sat_ v_sx v_1 v_2))
  | fun_vbinop__case_19 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) isub_sat_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_M.SUB_SAT v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) isub_sat_ v_sx v_1 v_2))
  | fun_vbinop__case_20 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) imin_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_M.MIN v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) imin_ v_sx v_1 v_2))
  | fun_vbinop__case_21 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) imin_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_M.MIN v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) imin_ v_sx v_1 v_2))
  | fun_vbinop__case_22 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) imin_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_M.MIN v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) imin_ v_sx v_1 v_2))
  | fun_vbinop__case_23 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) imin_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_M.MIN v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) imin_ v_sx v_1 v_2))
  | fun_vbinop__case_24 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) imax_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_M.MAX v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) imax_ v_sx v_1 v_2))
  | fun_vbinop__case_25 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) imax_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_M.MAX v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) imax_ v_sx v_1 v_2))
  | fun_vbinop__case_26 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) imax_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_M.MAX v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) imax_ v_sx v_1 v_2))
  | fun_vbinop__case_27 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) imax_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_M.MAX v_sx)) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) imax_ v_sx v_1 v_2))
  | fun_vbinop__case_28 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iavgr_ sx.U v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_M.AVGRU) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iavgr_ sx.U v_1 v_2))
  | fun_vbinop__case_29 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iavgr_ sx.U v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_M.AVGRU) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iavgr_ sx.U v_1 v_2))
  | fun_vbinop__case_30 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iavgr_ sx.U v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_M.AVGRU) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iavgr_ sx.U v_1 v_2))
  | fun_vbinop__case_31 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iavgr_ sx.U v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_M.AVGRU) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iavgr_ sx.U v_1 v_2))
  | fun_vbinop__case_32 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iq15mulr_sat_ sx.S v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_M.Q15MULR_SATS) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) iq15mulr_sat_ sx.S v_1 v_2))
  | fun_vbinop__case_33 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iq15mulr_sat_ sx.S v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_M.Q15MULR_SATS) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) iq15mulr_sat_ sx.S v_1 v_2))
  | fun_vbinop__case_34 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iq15mulr_sat_ sx.S v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_M.Q15MULR_SATS) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) iq15mulr_sat_ sx.S v_1 v_2))
  | fun_vbinop__case_35 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iq15mulr_sat_ sx.S v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_M.Q15MULR_SATS) v_1 v_2 (Option.get! (ivbinopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) iq15mulr_sat_ sx.S v_1 v_2))
  | fun_vbinop__case_36 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsxnd_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) irelaxed_q15mulr_ sx.S v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_M.RELAXED_Q15MULRS) v_1 v_2 (Option.get! (ivbinopsxnd_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) irelaxed_q15mulr_ sx.S v_1 v_2))
  | fun_vbinop__case_37 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsxnd_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) irelaxed_q15mulr_ sx.S v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_M.RELAXED_Q15MULRS) v_1 v_2 (Option.get! (ivbinopsxnd_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) irelaxed_q15mulr_ sx.S v_1 v_2))
  | fun_vbinop__case_38 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsxnd_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) irelaxed_q15mulr_ sx.S v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_M.RELAXED_Q15MULRS) v_1 v_2 (Option.get! (ivbinopsxnd_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) irelaxed_q15mulr_ sx.S v_1 v_2))
  | fun_vbinop__case_39 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivbinopsxnd_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) irelaxed_q15mulr_ sx.S v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_M.RELAXED_Q15MULRS) v_1 v_2 (Option.get! (ivbinopsxnd_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) irelaxed_q15mulr_ sx.S v_1 v_2))
  | fun_vbinop__case_40 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fadd_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.ADD) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fadd_ v_1 v_2))
  | fun_vbinop__case_41 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fadd_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.ADD) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fadd_ v_1 v_2))
  | fun_vbinop__case_42 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fsub_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.SUB) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fsub_ v_1 v_2))
  | fun_vbinop__case_43 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fsub_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.SUB) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fsub_ v_1 v_2))
  | fun_vbinop__case_44 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fmul_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.MUL) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fmul_ v_1 v_2))
  | fun_vbinop__case_45 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fmul_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.MUL) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fmul_ v_1 v_2))
  | fun_vbinop__case_46 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fdiv_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.DIV) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fdiv_ v_1 v_2))
  | fun_vbinop__case_47 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fdiv_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.DIV) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fdiv_ v_1 v_2))
  | fun_vbinop__case_48 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fmin_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.MIN) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fmin_ v_1 v_2))
  | fun_vbinop__case_49 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fmin_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.MIN) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fmin_ v_1 v_2))
  | fun_vbinop__case_50 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fmax_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.MAX) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fmax_ v_1 v_2))
  | fun_vbinop__case_51 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fmax_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.MAX) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fmax_ v_1 v_2))
  | fun_vbinop__case_52 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fpmin_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.PMIN) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fpmin_ v_1 v_2))
  | fun_vbinop__case_53 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fpmin_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.PMIN) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fpmin_ v_1 v_2))
  | fun_vbinop__case_54 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fpmax_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.PMAX) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fpmax_ v_1 v_2))
  | fun_vbinop__case_55 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fpmax_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.PMAX) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fpmax_ v_1 v_2))
  | fun_vbinop__case_56 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) frelaxed_min_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.RELAXED_MIN) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) frelaxed_min_ v_1 v_2))
  | fun_vbinop__case_57 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) frelaxed_min_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.RELAXED_MIN) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) frelaxed_min_ v_1 v_2))
  | fun_vbinop__case_58 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) frelaxed_max_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_M.RELAXED_MAX) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) frelaxed_max_ v_1 v_2))
  | fun_vbinop__case_59 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) frelaxed_max_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_M.RELAXED_MAX) v_1 v_2 (Option.get! (fvbinop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) frelaxed_max_ v_1 v_2))


inductive vbinop__is_wf : shape → vbinop_ → vec_ → vec_ → List vec_ → Prop where
  | vbinop__is_wf_0 (v_shape : shape) (v_vbinop_ : vbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : List vec_) (var_0 : List vec_) :
    fun_vbinop_ v_shape v_vbinop_ v_vec_ vec__0 var_0 →
    wf_shape v_shape →
    wf_vbinop_ v_shape v_vbinop_ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    vbinop__is_wf v_shape v_vbinop_ v_vec_ vec__0 ret_val_lst


inductive fun_vternop_ : shape → vternop_ → vec_ → vec_ → vec_ → List vec_ → Prop where
  | fun_vternop__case_0 (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN) (M_0 : Nat) :
    (ivternopnd_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3) ≠ none →
    v_M = M_0 →
    fun_vternop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vternop_.mk_vternop__0 Jnn.I32 M_0 vternop_Jnn_M.RELAXED_LANESELECT) v_1 v_2 v_3 (Option.get! (ivternopnd_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3))
  | fun_vternop__case_1 (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN) (M_0 : Nat) :
    (ivternopnd_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3) ≠ none →
    v_M = M_0 →
    fun_vternop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vternop_.mk_vternop__0 Jnn.I64 M_0 vternop_Jnn_M.RELAXED_LANESELECT) v_1 v_2 v_3 (Option.get! (ivternopnd_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3))
  | fun_vternop__case_2 (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN) (M_0 : Nat) :
    (ivternopnd_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3) ≠ none →
    v_M = M_0 →
    fun_vternop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vternop_.mk_vternop__0 Jnn.I8 M_0 vternop_Jnn_M.RELAXED_LANESELECT) v_1 v_2 v_3 (Option.get! (ivternopnd_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3))
  | fun_vternop__case_3 (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN) (M_0 : Nat) :
    (ivternopnd_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3) ≠ none →
    v_M = M_0 →
    fun_vternop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vternop_.mk_vternop__0 Jnn.I16 M_0 vternop_Jnn_M.RELAXED_LANESELECT) v_1 v_2 v_3 (Option.get! (ivternopnd_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) irelaxed_laneselect_ v_1 v_2 v_3))
  | fun_vternop__case_4 (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN) (M_0 : Nat) :
    (fvternop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) frelaxed_madd_ v_1 v_2 v_3) ≠ none →
    v_M = M_0 →
    fun_vternop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vternop_.mk_vternop__1 Fnn.F32 M_0 vternop_Fnn_M.RELAXED_MADD) v_1 v_2 v_3 (Option.get! (fvternop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) frelaxed_madd_ v_1 v_2 v_3))
  | fun_vternop__case_5 (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN) (M_0 : Nat) :
    (fvternop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) frelaxed_madd_ v_1 v_2 v_3) ≠ none →
    v_M = M_0 →
    fun_vternop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vternop_.mk_vternop__1 Fnn.F64 M_0 vternop_Fnn_M.RELAXED_MADD) v_1 v_2 v_3 (Option.get! (fvternop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) frelaxed_madd_ v_1 v_2 v_3))
  | fun_vternop__case_6 (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN) (M_0 : Nat) :
    (fvternop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) frelaxed_nmadd_ v_1 v_2 v_3) ≠ none →
    v_M = M_0 →
    fun_vternop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vternop_.mk_vternop__1 Fnn.F32 M_0 vternop_Fnn_M.RELAXED_NMADD) v_1 v_2 v_3 (Option.get! (fvternop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) frelaxed_nmadd_ v_1 v_2 v_3))
  | fun_vternop__case_7 (v_M : Nat) (v_1 : uN) (v_2 : uN) (v_3 : uN) (M_0 : Nat) :
    (fvternop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) frelaxed_nmadd_ v_1 v_2 v_3) ≠ none →
    v_M = M_0 →
    fun_vternop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vternop_.mk_vternop__1 Fnn.F64 M_0 vternop_Fnn_M.RELAXED_NMADD) v_1 v_2 v_3 (Option.get! (fvternop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) frelaxed_nmadd_ v_1 v_2 v_3))


inductive vternop__is_wf : shape → vternop_ → vec_ → vec_ → vec_ → List vec_ → Prop where
  | vternop__is_wf_0 (v_shape : shape) (v_vternop_ : vternop_) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val_lst : List vec_) (var_0 : List vec_) :
    fun_vternop_ v_shape v_vternop_ v_vec_ vec__0 vec__1 var_0 →
    wf_shape v_shape →
    wf_vternop_ v_shape v_vternop_ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    wf_uN 128 vec__1 →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    vternop__is_wf v_shape v_vternop_ v_vec_ vec__0 vec__1 ret_val_lst


inductive fun_vrelop_ : shape → vrelop_ → vec_ → vec_ → vec_ → Prop where
  | fun_vrelop__case_0 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ieq_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 vrelop_Jnn_M.EQ) v_1 v_2 (Option.get! (ivrelop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ieq_ v_1 v_2))
  | fun_vrelop__case_1 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ieq_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 vrelop_Jnn_M.EQ) v_1 v_2 (Option.get! (ivrelop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ieq_ v_1 v_2))
  | fun_vrelop__case_2 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ieq_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 vrelop_Jnn_M.EQ) v_1 v_2 (Option.get! (ivrelop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ieq_ v_1 v_2))
  | fun_vrelop__case_3 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ieq_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 vrelop_Jnn_M.EQ) v_1 v_2 (Option.get! (ivrelop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ieq_ v_1 v_2))
  | fun_vrelop__case_4 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ine_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 vrelop_Jnn_M.NE) v_1 v_2 (Option.get! (ivrelop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ine_ v_1 v_2))
  | fun_vrelop__case_5 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ine_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 vrelop_Jnn_M.NE) v_1 v_2 (Option.get! (ivrelop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ine_ v_1 v_2))
  | fun_vrelop__case_6 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ine_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 vrelop_Jnn_M.NE) v_1 v_2 (Option.get! (ivrelop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ine_ v_1 v_2))
  | fun_vrelop__case_7 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ine_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 vrelop_Jnn_M.NE) v_1 v_2 (Option.get! (ivrelop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ine_ v_1 v_2))
  | fun_vrelop__case_8 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ilt_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_M.LT v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ilt_ v_sx v_1 v_2))
  | fun_vrelop__case_9 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ilt_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_M.LT v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ilt_ v_sx v_1 v_2))
  | fun_vrelop__case_10 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ilt_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_M.LT v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ilt_ v_sx v_1 v_2))
  | fun_vrelop__case_11 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ilt_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_M.LT v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ilt_ v_sx v_1 v_2))
  | fun_vrelop__case_12 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) igt_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_M.GT v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) igt_ v_sx v_1 v_2))
  | fun_vrelop__case_13 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) igt_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_M.GT v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) igt_ v_sx v_1 v_2))
  | fun_vrelop__case_14 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) igt_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_M.GT v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) igt_ v_sx v_1 v_2))
  | fun_vrelop__case_15 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) igt_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_M.GT v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) igt_ v_sx v_1 v_2))
  | fun_vrelop__case_16 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ile_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_M.LE v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ile_ v_sx v_1 v_2))
  | fun_vrelop__case_17 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ile_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_M.LE v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ile_ v_sx v_1 v_2))
  | fun_vrelop__case_18 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ile_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_M.LE v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ile_ v_sx v_1 v_2))
  | fun_vrelop__case_19 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ile_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_M.LE v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ile_ v_sx v_1 v_2))
  | fun_vrelop__case_20 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ige_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_M.GE v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ige_ v_sx v_1 v_2))
  | fun_vrelop__case_21 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ige_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_M.GE v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ige_ v_sx v_1 v_2))
  | fun_vrelop__case_22 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ige_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_M.GE v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ige_ v_sx v_1 v_2))
  | fun_vrelop__case_23 (v_M : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ige_ v_sx v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_M.GE v_sx)) v_1 v_2 (Option.get! (ivrelopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ige_ v_sx v_1 v_2))
  | fun_vrelop__case_24 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) feq_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_M.EQ) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) feq_ v_1 v_2))
  | fun_vrelop__case_25 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) feq_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_M.EQ) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) feq_ v_1 v_2))
  | fun_vrelop__case_26 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fne_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_M.NE) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fne_ v_1 v_2))
  | fun_vrelop__case_27 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fne_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_M.NE) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fne_ v_1 v_2))
  | fun_vrelop__case_28 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) flt_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_M.LT) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) flt_ v_1 v_2))
  | fun_vrelop__case_29 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) flt_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_M.LT) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) flt_ v_1 v_2))
  | fun_vrelop__case_30 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fgt_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_M.GT) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fgt_ v_1 v_2))
  | fun_vrelop__case_31 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fgt_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_M.GT) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fgt_ v_1 v_2))
  | fun_vrelop__case_32 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fle_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_M.LE) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fle_ v_1 v_2))
  | fun_vrelop__case_33 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fle_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_M.LE) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fle_ v_1 v_2))
  | fun_vrelop__case_34 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fge_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_M.GE) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) fge_ v_1 v_2))
  | fun_vrelop__case_35 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fge_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_M.GE) v_1 v_2 (Option.get! (fvrelop_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) fge_ v_1 v_2))


inductive vrelop__is_wf : shape → vrelop_ → vec_ → vec_ → vec_ → Prop where
  | vrelop__is_wf_0 (v_shape : shape) (v_vrelop_ : vrelop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_) :
    fun_vrelop_ v_shape v_vrelop_ v_vec_ vec__0 var_0 →
    wf_shape v_shape →
    wf_vrelop_ v_shape v_vrelop_ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    ret_val = var_0 →
    wf_uN 128 ret_val →
    vrelop__is_wf v_shape v_vrelop_ v_vec_ vec__0 ret_val


inductive fun_lcvtop__ : shape → shape → vcvtop__ → lane_ → List lane_ → Prop where
  | fun_lcvtop___case_0 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I32 c_1) [lane_.mk_lane__2 Jnn.I32 c]
  | fun_lcvtop___case_1 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I64 c_1) [lane_.mk_lane__2 Jnn.I32 c]
  | fun_lcvtop___case_2 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I8 c_1) [lane_.mk_lane__2 Jnn.I32 c]
  | fun_lcvtop___case_3 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I32 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I16 c_1) [lane_.mk_lane__2 Jnn.I32 c]
  | fun_lcvtop___case_4 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I32 c_1) [lane_.mk_lane__2 Jnn.I64 c]
  | fun_lcvtop___case_5 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I64 c_1) [lane_.mk_lane__2 Jnn.I64 c]
  | fun_lcvtop___case_6 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I8 c_1) [lane_.mk_lane__2 Jnn.I64 c]
  | fun_lcvtop___case_7 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I64 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I16 c_1) [lane_.mk_lane__2 Jnn.I64 c]
  | fun_lcvtop___case_8 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I32 c_1) [lane_.mk_lane__2 Jnn.I8 c]
  | fun_lcvtop___case_9 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I64 c_1) [lane_.mk_lane__2 Jnn.I8 c]
  | fun_lcvtop___case_10 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I8 c_1) [lane_.mk_lane__2 Jnn.I8 c]
  | fun_lcvtop___case_11 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I8 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I16 c_1) [lane_.mk_lane__2 Jnn.I8 c]
  | fun_lcvtop___case_12 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I32 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I32 c_1) [lane_.mk_lane__2 Jnn.I16 c]
  | fun_lcvtop___case_13 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I64 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I64 c_1) [lane_.mk_lane__2 Jnn.I16 c]
  | fun_lcvtop___case_14 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I8 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I8 c_1) [lane_.mk_lane__2 Jnn.I16 c]
  | fun_lcvtop___case_15 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : iN) :
    c = (extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___0 Jnn.I16 M_1_0 Jnn.I16 M_2_0 (vcvtop__Jnn_1_M_1_Jnn_2_M_2.EXTEND v_half v_sx)) (lane_.mk_lane__2 Jnn.I16 c_1) [lane_.mk_lane__2 Jnn.I16 c]
  | fun_lcvtop___case_16 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : fN) :
    c = (convert__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Fnn Fnn.F32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I32 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) (lane_.mk_lane__2 Jnn.I32 c_1) [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 c)]
  | fun_lcvtop___case_17 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : fN) :
    c = (convert__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Fnn Fnn.F32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I64 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) (lane_.mk_lane__2 Jnn.I64 c_1) [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 c)]
  | fun_lcvtop___case_18 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : fN) :
    c = (convert__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Fnn Fnn.F32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I8 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) (lane_.mk_lane__2 Jnn.I8 c_1) [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 c)]
  | fun_lcvtop___case_19 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : fN) :
    c = (convert__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Fnn Fnn.F32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I16 M_1_0 Fnn.F32 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) (lane_.mk_lane__2 Jnn.I16 c_1) [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 c)]
  | fun_lcvtop___case_20 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : fN) :
    c = (convert__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Fnn Fnn.F64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I32 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) (lane_.mk_lane__2 Jnn.I32 c_1) [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 c)]
  | fun_lcvtop___case_21 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : fN) :
    c = (convert__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Fnn Fnn.F64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I64 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) (lane_.mk_lane__2 Jnn.I64 c_1) [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 c)]
  | fun_lcvtop___case_22 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : fN) :
    c = (convert__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Fnn Fnn.F64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I8 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) (lane_.mk_lane__2 Jnn.I8 c_1) [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 c)]
  | fun_lcvtop___case_23 (M_1 : Nat) (M_2 : Nat) (half_opt : Option half) (v_sx : sx) (c_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) (c : fN) :
    c = (convert__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Fnn Fnn.F64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___1 Jnn.I16 M_1_0 Fnn.F64 M_2_0 (vcvtop__Jnn_1_M_1_Fnn_2_M_2.CONVERT half_opt v_sx)) (lane_.mk_lane__2 Jnn.I16 c_1) [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 c)]
  | fun_lcvtop___case_24 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_opt : Option iN) :
    c_opt = (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_addrtype addrtype.I32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) (lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 c_1)) (Option.toList (OMap (fun c_108_elem => lane_.mk_lane__0 (numtype_addrtype addrtype.I32) (num_.mk_num__0 addrtype.I32 c_108_elem)) c_opt))
  | fun_lcvtop___case_25 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_opt : Option iN) :
    c_opt = (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_addrtype addrtype.I64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) (lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 c_1)) (Option.toList (OMap (fun c_110_elem => lane_.mk_lane__0 (numtype_addrtype addrtype.I64) (num_.mk_num__0 addrtype.I64 c_110_elem)) c_opt))
  | fun_lcvtop___case_26 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_opt : Option iN) :
    c_opt = (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_addrtype addrtype.I32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) (lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 c_1)) (Option.toList (OMap (fun c_112_elem => lane_.mk_lane__0 (numtype_addrtype addrtype.I32) (num_.mk_num__0 addrtype.I32 c_112_elem)) c_opt))
  | fun_lcvtop___case_27 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_opt : Option iN) :
    c_opt = (trunc_sat__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_addrtype addrtype.I64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.TRUNC_SAT v_sx zero_opt)) (lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 c_1)) (Option.toList (OMap (fun c_114_elem => lane_.mk_lane__0 (numtype_addrtype addrtype.I64) (num_.mk_num__0 addrtype.I64 c_114_elem)) c_opt))
  | fun_lcvtop___case_28 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_opt : Option iN) :
    c_opt = (relaxed_trunc__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_addrtype addrtype.I32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) (lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 c_1)) (Option.toList (OMap (fun c_116_elem => lane_.mk_lane__0 (numtype_addrtype addrtype.I32) (num_.mk_num__0 addrtype.I32 c_116_elem)) c_opt))
  | fun_lcvtop___case_29 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_opt : Option iN) :
    c_opt = (relaxed_trunc__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_addrtype addrtype.I64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F32 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) (lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 c_1)) (Option.toList (OMap (fun c_118_elem => lane_.mk_lane__0 (numtype_addrtype addrtype.I64) (num_.mk_num__0 addrtype.I64 c_118_elem)) c_opt))
  | fun_lcvtop___case_30 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_opt : Option iN) :
    c_opt = (relaxed_trunc__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_addrtype addrtype.I32)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I32 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) (lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 c_1)) (Option.toList (OMap (fun c_120_elem => lane_.mk_lane__0 (numtype_addrtype addrtype.I32) (num_.mk_num__0 addrtype.I32 c_120_elem)) c_opt))
  | fun_lcvtop___case_31 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (zero_opt : Option zero) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_opt : Option iN) :
    c_opt = (relaxed_trunc__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_addrtype addrtype.I64)) v_sx c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___2 Fnn.F64 M_1_0 Jnn.I64 M_2_0 (vcvtop__Fnn_1_M_1_Jnn_2_M_2.RELAXED_TRUNC v_sx zero_opt)) (lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 c_1)) (Option.toList (OMap (fun c_122_elem => lane_.mk_lane__0 (numtype_addrtype addrtype.I64) (num_.mk_num__0 addrtype.I64 c_122_elem)) c_opt))
  | fun_lcvtop___case_32 (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_lst : List fN) :
    c_lst = (demote__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Fnn Fnn.F32)) c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE zero.ZERO)) (lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 c_1)) (Map (fun c_124_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 c_124_elem)) c_lst)
  | fun_lcvtop___case_33 (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_lst : List fN) :
    c_lst = (demote__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Fnn Fnn.F64)) c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE zero.ZERO)) (lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 c_1)) (Map (fun c_126_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 c_126_elem)) c_lst)
  | fun_lcvtop___case_34 (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_lst : List fN) :
    c_lst = (demote__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Fnn Fnn.F32)) c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F32 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE zero.ZERO)) (lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 c_1)) (Map (fun c_128_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 c_128_elem)) c_lst)
  | fun_lcvtop___case_35 (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_lst : List fN) :
    c_lst = (demote__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Fnn Fnn.F64)) c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F64 M_2_0 (vcvtop__Fnn_1_M_1_Fnn_2_M_2.DEMOTE zero.ZERO)) (lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 c_1)) (Map (fun c_130_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 c_130_elem)) c_lst)
  | fun_lcvtop___case_36 (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_lst : List fN) :
    c_lst = (promote__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Fnn Fnn.F32)) c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F32 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) (lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 c_1)) (Map (fun c_132_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 c_132_elem)) c_lst)
  | fun_lcvtop___case_37 (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_lst : List fN) :
    c_lst = (promote__ (lsizenn1 (lanetype_Fnn Fnn.F32)) (lsizenn2 (lanetype_Fnn Fnn.F64)) c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F32 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F32 M_1_0 Fnn.F64 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) (lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 c_1)) (Map (fun c_134_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 c_134_elem)) c_lst)
  | fun_lcvtop___case_38 (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_lst : List fN) :
    c_lst = (promote__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Fnn Fnn.F32)) c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F32 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F32 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) (lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 c_1)) (Map (fun c_136_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 c_136_elem)) c_lst)
  | fun_lcvtop___case_39 (M_1 : Nat) (M_2 : Nat) (c_1 : fN) (M_1_0 : Nat) (M_2_0 : Nat) (c_lst : List fN) :
    c_lst = (promote__ (lsizenn1 (lanetype_Fnn Fnn.F64)) (lsizenn2 (lanetype_Fnn Fnn.F64)) c_1) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_lcvtop__ (shape.X lanetype.F64 (dim.mk_dim M_1)) (shape.X lanetype.F64 (dim.mk_dim M_2)) (vcvtop__.mk_vcvtop___3 Fnn.F64 M_1_0 Fnn.F64 M_2_0 vcvtop__Fnn_1_M_1_Fnn_2_M_2.PROMOTELOW) (lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 c_1)) (Map (fun c_138_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 c_138_elem)) c_lst)


inductive lcvtop___is_wf : shape → shape → vcvtop__ → lane_ → List lane_ → Prop where
  | lcvtop___is_wf_0 (shape_1 : shape) (shape_2 : shape) (v_vcvtop__ : vcvtop__) (v_lane_ : lane_) (ret_val_lst : List lane_) (var_0 : List lane_) :
    fun_lcvtop__ shape_1 shape_2 v_vcvtop__ v_lane_ var_0 →
    wf_shape shape_1 →
    wf_shape shape_2 →
    wf_vcvtop__ shape_1 shape_2 v_vcvtop__ →
    wf_lane_ (fun_lanetype shape_1) v_lane_ →
    ret_val_lst = var_0 →
    Forall (fun ret_val_elem => wf_lane_ (fun_lanetype shape_2) ret_val_elem) ret_val_lst →
    lcvtop___is_wf shape_1 shape_2 v_vcvtop__ v_lane_ ret_val_lst


inductive fun_vcvtop__ : shape → shape → vcvtop__ → vec_ → vec_ → Prop where
  | fun_vcvtop___case_0 (Lnn_1 : lanetype) (v_M : Nat) (Lnn_2 : lanetype) (vcvtop : vcvtop__) (v_1 : uN) (v : uN) (M_0 : Nat) (c_1_lst : List lane_) (c_lst_lst : List (List lane_)) (var_2_lst : List (List lane_)) (var_1 : Option zero) (var_0 : Option half) :
    (List.length var_2_lst) = (List.length c_1_lst) →
    Forall₂ (fun var_2_elem c_1_142_elem => fun_lcvtop__ (shape.X Lnn_1 (dim.mk_dim v_M)) (shape.X Lnn_2 (dim.mk_dim v_M)) vcvtop c_1_142_elem var_2_elem) var_2_lst c_1_lst →
    fun_zeroop (shape.X Lnn_1 (dim.mk_dim v_M)) (shape.X Lnn_2 (dim.mk_dim v_M)) vcvtop var_1 →
    fun_halfop (shape.X Lnn_1 (dim.mk_dim v_M)) (shape.X Lnn_2 (dim.mk_dim v_M)) vcvtop var_0 →
    (var_0 = none) ∧ (var_1 = none) →
    c_1_lst = (lanes_ (shape.X Lnn_1 (dim.mk_dim v_M)) v_1) →
    c_lst_lst = (setproduct_ lane_ var_2_lst) →
    (List.length (Map (fun c_lst_30_elem => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim v_M)) c_lst_30_elem) c_lst_lst)) > 0 →
    List.contains (Map (fun c_lst_30_elem => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim v_M)) c_lst_30_elem) c_lst_lst) v →
    wf_shape (shape.X Lnn_1 (dim.mk_dim v_M)) →
    wf_shape (shape.X Lnn_2 (dim.mk_dim v_M)) →
    v_M = M_0 →
    fun_vcvtop__ (shape.X Lnn_1 (dim.mk_dim v_M)) (shape.X Lnn_2 (dim.mk_dim M_0)) vcvtop v_1 v
  | fun_vcvtop___case_1 (Lnn_1 : lanetype) (M_1 : Nat) (Lnn_2 : lanetype) (M_2 : Nat) (vcvtop : vcvtop__) (v_1 : uN) (v : uN) (v_half : half) (c_1_lst : List lane_) (c_lst_lst : List (List lane_)) (var_1_lst : List (List lane_)) (var_0 : Option half) :
    (List.length var_1_lst) = (List.length c_1_lst) →
    Forall₂ (fun var_1_elem c_1_144_elem => fun_lcvtop__ (shape.X Lnn_1 (dim.mk_dim M_1)) (shape.X Lnn_2 (dim.mk_dim M_2)) vcvtop c_1_144_elem var_1_elem) var_1_lst c_1_lst →
    fun_halfop (shape.X Lnn_1 (dim.mk_dim M_1)) (shape.X Lnn_2 (dim.mk_dim M_2)) vcvtop var_0 →
    var_0 = (some v_half) →
    c_1_lst = (List.take M_2 (List.drop (fun_half v_half 0 M_2) (lanes_ (shape.X Lnn_1 (dim.mk_dim M_1)) v_1))) →
    c_lst_lst = (setproduct_ lane_ var_1_lst) →
    (List.length (Map (fun c_lst_32_elem => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim M_2)) c_lst_32_elem) c_lst_lst)) > 0 →
    List.contains (Map (fun c_lst_32_elem => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim M_2)) c_lst_32_elem) c_lst_lst) v →
    wf_shape (shape.X Lnn_1 (dim.mk_dim M_1)) →
    wf_shape (shape.X Lnn_2 (dim.mk_dim M_2)) →
    fun_vcvtop__ (shape.X Lnn_1 (dim.mk_dim M_1)) (shape.X Lnn_2 (dim.mk_dim M_2)) vcvtop v_1 v
  | fun_vcvtop___case_2 (Lnn_1 : lanetype) (M_1 : Nat) (Lnn_2 : lanetype) (M_2 : Nat) (vcvtop : vcvtop__) (v_1 : uN) (v : uN) (c_1_lst : List lane_) (c_lst_lst : List (List lane_)) (var_1_lst : List (List lane_)) (var_0 : Option zero) :
    (List.length var_1_lst) = (List.length c_1_lst) →
    Forall₂ (fun var_1_elem c_1_146_elem => fun_lcvtop__ (shape.X Lnn_1 (dim.mk_dim M_1)) (shape.X Lnn_2 (dim.mk_dim M_2)) vcvtop c_1_146_elem var_1_elem) var_1_lst c_1_lst →
    fun_zeroop (shape.X Lnn_1 (dim.mk_dim M_1)) (shape.X Lnn_2 (dim.mk_dim M_2)) vcvtop var_0 →
    var_0 = (some zero.ZERO) →
    c_1_lst = (lanes_ (shape.X Lnn_1 (dim.mk_dim M_1)) v_1) →
    c_lst_lst = (setproduct_ lane_ (var_1_lst ++ (List.replicate M_1 [fun_zero Lnn_2]))) →
    (List.length (Map (fun c_lst_34_elem => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim M_2)) c_lst_34_elem) c_lst_lst)) > 0 →
    List.contains (Map (fun c_lst_34_elem => inv_lanes_ (shape.X Lnn_2 (dim.mk_dim M_2)) c_lst_34_elem) c_lst_lst) v →
    wf_shape (shape.X Lnn_1 (dim.mk_dim M_1)) →
    wf_shape (shape.X Lnn_2 (dim.mk_dim M_2)) →
    fun_vcvtop__ (shape.X Lnn_1 (dim.mk_dim M_1)) (shape.X Lnn_2 (dim.mk_dim M_2)) vcvtop v_1 v


inductive vcvtop___is_wf : shape → shape → vcvtop__ → vec_ → vec_ → Prop where
  | vcvtop___is_wf_0 (shape_1 : shape) (shape_2 : shape) (v_vcvtop__ : vcvtop__) (v_vec_ : vec_) (ret_val : vec_) (var_0 : vec_) :
    fun_vcvtop__ shape_1 shape_2 v_vcvtop__ v_vec_ var_0 →
    wf_shape shape_1 →
    wf_shape shape_2 →
    wf_vcvtop__ shape_1 shape_2 v_vcvtop__ →
    wf_uN 128 v_vec_ →
    ret_val = var_0 →
    wf_uN 128 ret_val →
    vcvtop___is_wf shape_1 shape_2 v_vcvtop__ v_vec_ ret_val


inductive fun_vshiftop_ : ishape → vshiftop_ → vec_ → u32 → vec_ → Prop where
  | fun_vshiftop__case_0 (v_M : Nat) (v : uN) (i : uN) (M_0 : Nat) :
    (ivshiftop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ishl_ v i) ≠ none →
    v_M = M_0 →
    fun_vshiftop_ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim v_M))) (vshiftop_.mk_vshiftop__0 Jnn.I32 M_0 vshiftop_Jnn_M.SHL) v i (Option.get! (ivshiftop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ishl_ v i))
  | fun_vshiftop__case_1 (v_M : Nat) (v : uN) (i : uN) (M_0 : Nat) :
    (ivshiftop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ishl_ v i) ≠ none →
    v_M = M_0 →
    fun_vshiftop_ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim v_M))) (vshiftop_.mk_vshiftop__0 Jnn.I64 M_0 vshiftop_Jnn_M.SHL) v i (Option.get! (ivshiftop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ishl_ v i))
  | fun_vshiftop__case_2 (v_M : Nat) (v : uN) (i : uN) (M_0 : Nat) :
    (ivshiftop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ishl_ v i) ≠ none →
    v_M = M_0 →
    fun_vshiftop_ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim v_M))) (vshiftop_.mk_vshiftop__0 Jnn.I8 M_0 vshiftop_Jnn_M.SHL) v i (Option.get! (ivshiftop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ishl_ v i))
  | fun_vshiftop__case_3 (v_M : Nat) (v : uN) (i : uN) (M_0 : Nat) :
    (ivshiftop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ishl_ v i) ≠ none →
    v_M = M_0 →
    fun_vshiftop_ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim v_M))) (vshiftop_.mk_vshiftop__0 Jnn.I16 M_0 vshiftop_Jnn_M.SHL) v i (Option.get! (ivshiftop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ishl_ v i))
  | fun_vshiftop__case_4 (v_M : Nat) (v_sx : sx) (v : uN) (i : uN) (M_0 : Nat) :
    (ivshiftopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ishr_ v_sx v i) ≠ none →
    v_M = M_0 →
    fun_vshiftop_ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim v_M))) (vshiftop_.mk_vshiftop__0 Jnn.I32 M_0 (vshiftop_Jnn_M.SHR v_sx)) v i (Option.get! (ivshiftopsx_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) ishr_ v_sx v i))
  | fun_vshiftop__case_5 (v_M : Nat) (v_sx : sx) (v : uN) (i : uN) (M_0 : Nat) :
    (ivshiftopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ishr_ v_sx v i) ≠ none →
    v_M = M_0 →
    fun_vshiftop_ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim v_M))) (vshiftop_.mk_vshiftop__0 Jnn.I64 M_0 (vshiftop_Jnn_M.SHR v_sx)) v i (Option.get! (ivshiftopsx_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) ishr_ v_sx v i))
  | fun_vshiftop__case_6 (v_M : Nat) (v_sx : sx) (v : uN) (i : uN) (M_0 : Nat) :
    (ivshiftopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ishr_ v_sx v i) ≠ none →
    v_M = M_0 →
    fun_vshiftop_ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim v_M))) (vshiftop_.mk_vshiftop__0 Jnn.I8 M_0 (vshiftop_Jnn_M.SHR v_sx)) v i (Option.get! (ivshiftopsx_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) ishr_ v_sx v i))
  | fun_vshiftop__case_7 (v_M : Nat) (v_sx : sx) (v : uN) (i : uN) (M_0 : Nat) :
    (ivshiftopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ishr_ v_sx v i) ≠ none →
    v_M = M_0 →
    fun_vshiftop_ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim v_M))) (vshiftop_.mk_vshiftop__0 Jnn.I16 M_0 (vshiftop_Jnn_M.SHR v_sx)) v i (Option.get! (ivshiftopsx_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) ishr_ v_sx v i))


inductive vshiftop__is_wf : ishape → vshiftop_ → vec_ → u32 → vec_ → Prop where
  | vshiftop__is_wf_0 (v_ishape : ishape) (v_vshiftop_ : vshiftop_) (v_vec_ : vec_) (v_u32 : u32) (ret_val : vec_) (var_0 : vec_) :
    fun_vshiftop_ v_ishape v_vshiftop_ v_vec_ v_u32 var_0 →
    wf_ishape v_ishape →
    wf_vshiftop_ v_ishape v_vshiftop_ →
    wf_uN 128 v_vec_ →
    wf_uN 32 v_u32 →
    ret_val = var_0 →
    wf_uN 128 ret_val →
    vshiftop__is_wf v_ishape v_vshiftop_ v_vec_ v_u32 ret_val


inductive fun_vbitmaskop_ : ishape → vec_ → u32 → Prop where
  | fun_vbitmaskop__case_0 (v_M : Nat) (v : uN) (var_0 : u32) :
    fun_ivbitmaskop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v var_0 →
    fun_vbitmaskop_ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim v_M))) v var_0
  | fun_vbitmaskop__case_1 (v_M : Nat) (v : uN) (var_0 : u32) :
    fun_ivbitmaskop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v var_0 →
    fun_vbitmaskop_ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim v_M))) v var_0
  | fun_vbitmaskop__case_2 (v_M : Nat) (v : uN) (var_0 : u32) :
    fun_ivbitmaskop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v var_0 →
    fun_vbitmaskop_ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim v_M))) v var_0
  | fun_vbitmaskop__case_3 (v_M : Nat) (v : uN) (var_0 : u32) :
    fun_ivbitmaskop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v var_0 →
    fun_vbitmaskop_ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim v_M))) v var_0


inductive vbitmaskop__is_wf : ishape → vec_ → u32 → Prop where
  | vbitmaskop__is_wf_0 (v_ishape : ishape) (v_vec_ : vec_) (ret_val : u32) (var_0 : u32) :
    fun_vbitmaskop_ v_ishape v_vec_ var_0 →
    wf_ishape v_ishape →
    wf_uN 128 v_vec_ →
    ret_val = var_0 →
    wf_uN 32 ret_val →
    vbitmaskop__is_wf v_ishape v_vec_ ret_val


inductive fun_vswizzlop_ : bshape → vswizzlop_ → vec_ → vec_ → vec_ → Prop where
  | fun_vswizzlop__case_0 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivswizzlop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) iswizzle_lane_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vswizzlop_ (bshape.mk_bshape (shape.X lanetype.I8 (dim.mk_dim v_M))) (vswizzlop_.mk_vswizzlop__0 M_0 vswizzlop_M.SWIZZLE) v_1 v_2 (Option.get! (ivswizzlop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) iswizzle_lane_ v_1 v_2))
  | fun_vswizzlop__case_1 (v_M : Nat) (v_1 : uN) (v_2 : uN) (M_0 : Nat) :
    (ivswizzlop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) irelaxed_swizzle_lane_ v_1 v_2) ≠ none →
    v_M = M_0 →
    fun_vswizzlop_ (bshape.mk_bshape (shape.X lanetype.I8 (dim.mk_dim v_M))) (vswizzlop_.mk_vswizzlop__0 M_0 vswizzlop_M.RELAXED_SWIZZLE) v_1 v_2 (Option.get! (ivswizzlop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) irelaxed_swizzle_lane_ v_1 v_2))


inductive vswizzlop__is_wf : bshape → vswizzlop_ → vec_ → vec_ → vec_ → Prop where
  | vswizzlop__is_wf_0 (v_bshape : bshape) (v_vswizzlop_ : vswizzlop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_) :
    fun_vswizzlop_ v_bshape v_vswizzlop_ v_vec_ vec__0 var_0 →
    wf_bshape v_bshape →
    wf_vswizzlop_ v_bshape v_vswizzlop_ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    ret_val = var_0 →
    wf_uN 128 ret_val →
    vswizzlop__is_wf v_bshape v_vswizzlop_ v_vec_ vec__0 ret_val


def vshufflop_ (v_bshape : bshape) (var_0_lst : List laneidx) (v_vec_ : vec_) (vec__0 : vec_) : Option vec_ :=
  match v_bshape with
  | bshape.mk_bshape (shape.X lanetype.I8 (dim.mk_dim v_M)) => ivshufflop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) var_0_lst v_vec_ vec__0
  | _ => none

inductive vshufflop__is_wf : bshape → List laneidx → vec_ → vec_ → vec_ → Prop where
  | vshufflop__is_wf_0 (v_bshape : bshape) (var_0_lst : List laneidx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) :
    wf_bshape v_bshape →
    Forall (fun var_0_elem => wf_uN 8 var_0_elem) var_0_lst →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (vshufflop_ v_bshape var_0_lst v_vec_ vec__0) ≠ none →
    ret_val = (Option.get! (vshufflop_ v_bshape var_0_lst v_vec_ vec__0)) →
    wf_uN 128 ret_val →
    vshufflop__is_wf v_bshape var_0_lst v_vec_ vec__0 ret_val


inductive fun_vnarrowop__ : shape → shape → sx → vec_ → vec_ → vec_ → Prop where
  | fun_vnarrowop___case_0 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_148_elem => (proj_lane__2 c_1_148_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_148_elem => narrow__ (lsize (lanetype_Jnn Jnn.I32)) (lsize (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_148_elem))) c_1_lst) →
    Forall (fun c_2_100_elem => (proj_lane__2 c_2_100_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_100_elem => narrow__ (lsize (lanetype_Jnn Jnn.I32)) (lsize (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_2_100_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ((Map (fun c'_1_2_elem => lane_.mk_lane__2 Jnn.I32 c'_1_2_elem) c'_1_lst) ++ (Map (fun c'_2_2_elem => lane_.mk_lane__2 Jnn.I32 c'_2_2_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) →
    Forall (fun c'_1_3_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I32 c'_1_3_elem)) c'_1_lst →
    Forall (fun c'_2_3_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I32 c'_2_3_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_1 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_150_elem => (proj_lane__2 c_1_150_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_150_elem => narrow__ (lsize (lanetype_Jnn Jnn.I64)) (lsize (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_150_elem))) c_1_lst) →
    Forall (fun c_2_102_elem => (proj_lane__2 c_2_102_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_102_elem => narrow__ (lsize (lanetype_Jnn Jnn.I64)) (lsize (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_2_102_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ((Map (fun c'_1_5_elem => lane_.mk_lane__2 Jnn.I32 c'_1_5_elem) c'_1_lst) ++ (Map (fun c'_2_5_elem => lane_.mk_lane__2 Jnn.I32 c'_2_5_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) →
    Forall (fun c'_1_6_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I32 c'_1_6_elem)) c'_1_lst →
    Forall (fun c'_2_6_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I32 c'_2_6_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_2 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_152_elem => (proj_lane__2 c_1_152_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_152_elem => narrow__ (lsize (lanetype_Jnn Jnn.I8)) (lsize (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_152_elem))) c_1_lst) →
    Forall (fun c_2_104_elem => (proj_lane__2 c_2_104_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_104_elem => narrow__ (lsize (lanetype_Jnn Jnn.I8)) (lsize (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_2_104_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ((Map (fun c'_1_8_elem => lane_.mk_lane__2 Jnn.I32 c'_1_8_elem) c'_1_lst) ++ (Map (fun c'_2_8_elem => lane_.mk_lane__2 Jnn.I32 c'_2_8_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) →
    Forall (fun c'_1_9_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I32 c'_1_9_elem)) c'_1_lst →
    Forall (fun c'_2_9_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I32 c'_2_9_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_3 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_154_elem => (proj_lane__2 c_1_154_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_154_elem => narrow__ (lsize (lanetype_Jnn Jnn.I16)) (lsize (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_154_elem))) c_1_lst) →
    Forall (fun c_2_106_elem => (proj_lane__2 c_2_106_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_106_elem => narrow__ (lsize (lanetype_Jnn Jnn.I16)) (lsize (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_2_106_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ((Map (fun c'_1_11_elem => lane_.mk_lane__2 Jnn.I32 c'_1_11_elem) c'_1_lst) ++ (Map (fun c'_2_11_elem => lane_.mk_lane__2 Jnn.I32 c'_2_11_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) →
    Forall (fun c'_1_12_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I32 c'_1_12_elem)) c'_1_lst →
    Forall (fun c'_2_12_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I32 c'_2_12_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I32 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_4 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_156_elem => (proj_lane__2 c_1_156_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_156_elem => narrow__ (lsize (lanetype_Jnn Jnn.I32)) (lsize (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_156_elem))) c_1_lst) →
    Forall (fun c_2_108_elem => (proj_lane__2 c_2_108_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_108_elem => narrow__ (lsize (lanetype_Jnn Jnn.I32)) (lsize (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_2_108_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ((Map (fun c'_1_14_elem => lane_.mk_lane__2 Jnn.I64 c'_1_14_elem) c'_1_lst) ++ (Map (fun c'_2_14_elem => lane_.mk_lane__2 Jnn.I64 c'_2_14_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) →
    Forall (fun c'_1_15_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I64 c'_1_15_elem)) c'_1_lst →
    Forall (fun c'_2_15_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I64 c'_2_15_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_5 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_158_elem => (proj_lane__2 c_1_158_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_158_elem => narrow__ (lsize (lanetype_Jnn Jnn.I64)) (lsize (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_158_elem))) c_1_lst) →
    Forall (fun c_2_110_elem => (proj_lane__2 c_2_110_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_110_elem => narrow__ (lsize (lanetype_Jnn Jnn.I64)) (lsize (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_2_110_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ((Map (fun c'_1_17_elem => lane_.mk_lane__2 Jnn.I64 c'_1_17_elem) c'_1_lst) ++ (Map (fun c'_2_17_elem => lane_.mk_lane__2 Jnn.I64 c'_2_17_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) →
    Forall (fun c'_1_18_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I64 c'_1_18_elem)) c'_1_lst →
    Forall (fun c'_2_18_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I64 c'_2_18_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_6 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_160_elem => (proj_lane__2 c_1_160_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_160_elem => narrow__ (lsize (lanetype_Jnn Jnn.I8)) (lsize (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_160_elem))) c_1_lst) →
    Forall (fun c_2_112_elem => (proj_lane__2 c_2_112_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_112_elem => narrow__ (lsize (lanetype_Jnn Jnn.I8)) (lsize (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_2_112_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ((Map (fun c'_1_20_elem => lane_.mk_lane__2 Jnn.I64 c'_1_20_elem) c'_1_lst) ++ (Map (fun c'_2_20_elem => lane_.mk_lane__2 Jnn.I64 c'_2_20_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) →
    Forall (fun c'_1_21_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I64 c'_1_21_elem)) c'_1_lst →
    Forall (fun c'_2_21_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I64 c'_2_21_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_7 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_162_elem => (proj_lane__2 c_1_162_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_162_elem => narrow__ (lsize (lanetype_Jnn Jnn.I16)) (lsize (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_162_elem))) c_1_lst) →
    Forall (fun c_2_114_elem => (proj_lane__2 c_2_114_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_114_elem => narrow__ (lsize (lanetype_Jnn Jnn.I16)) (lsize (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_2_114_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ((Map (fun c'_1_23_elem => lane_.mk_lane__2 Jnn.I64 c'_1_23_elem) c'_1_lst) ++ (Map (fun c'_2_23_elem => lane_.mk_lane__2 Jnn.I64 c'_2_23_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) →
    Forall (fun c'_1_24_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I64 c'_1_24_elem)) c'_1_lst →
    Forall (fun c'_2_24_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I64 c'_2_24_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I64 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_8 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_164_elem => (proj_lane__2 c_1_164_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_164_elem => narrow__ (lsize (lanetype_Jnn Jnn.I32)) (lsize (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_164_elem))) c_1_lst) →
    Forall (fun c_2_116_elem => (proj_lane__2 c_2_116_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_116_elem => narrow__ (lsize (lanetype_Jnn Jnn.I32)) (lsize (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_2_116_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ((Map (fun c'_1_26_elem => lane_.mk_lane__2 Jnn.I8 c'_1_26_elem) c'_1_lst) ++ (Map (fun c'_2_26_elem => lane_.mk_lane__2 Jnn.I8 c'_2_26_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) →
    Forall (fun c'_1_27_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I8 c'_1_27_elem)) c'_1_lst →
    Forall (fun c'_2_27_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I8 c'_2_27_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_9 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_166_elem => (proj_lane__2 c_1_166_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_166_elem => narrow__ (lsize (lanetype_Jnn Jnn.I64)) (lsize (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_166_elem))) c_1_lst) →
    Forall (fun c_2_118_elem => (proj_lane__2 c_2_118_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_118_elem => narrow__ (lsize (lanetype_Jnn Jnn.I64)) (lsize (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_2_118_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ((Map (fun c'_1_29_elem => lane_.mk_lane__2 Jnn.I8 c'_1_29_elem) c'_1_lst) ++ (Map (fun c'_2_29_elem => lane_.mk_lane__2 Jnn.I8 c'_2_29_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) →
    Forall (fun c'_1_30_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I8 c'_1_30_elem)) c'_1_lst →
    Forall (fun c'_2_30_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I8 c'_2_30_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_10 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_168_elem => (proj_lane__2 c_1_168_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_168_elem => narrow__ (lsize (lanetype_Jnn Jnn.I8)) (lsize (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_168_elem))) c_1_lst) →
    Forall (fun c_2_120_elem => (proj_lane__2 c_2_120_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_120_elem => narrow__ (lsize (lanetype_Jnn Jnn.I8)) (lsize (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_2_120_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ((Map (fun c'_1_32_elem => lane_.mk_lane__2 Jnn.I8 c'_1_32_elem) c'_1_lst) ++ (Map (fun c'_2_32_elem => lane_.mk_lane__2 Jnn.I8 c'_2_32_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) →
    Forall (fun c'_1_33_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I8 c'_1_33_elem)) c'_1_lst →
    Forall (fun c'_2_33_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I8 c'_2_33_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_11 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_170_elem => (proj_lane__2 c_1_170_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_170_elem => narrow__ (lsize (lanetype_Jnn Jnn.I16)) (lsize (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_170_elem))) c_1_lst) →
    Forall (fun c_2_122_elem => (proj_lane__2 c_2_122_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_122_elem => narrow__ (lsize (lanetype_Jnn Jnn.I16)) (lsize (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_2_122_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ((Map (fun c'_1_35_elem => lane_.mk_lane__2 Jnn.I8 c'_1_35_elem) c'_1_lst) ++ (Map (fun c'_2_35_elem => lane_.mk_lane__2 Jnn.I8 c'_2_35_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) →
    Forall (fun c'_1_36_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I8 c'_1_36_elem)) c'_1_lst →
    Forall (fun c'_2_36_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I8 c'_2_36_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I8 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_12 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_172_elem => (proj_lane__2 c_1_172_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_172_elem => narrow__ (lsize (lanetype_Jnn Jnn.I32)) (lsize (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_172_elem))) c_1_lst) →
    Forall (fun c_2_124_elem => (proj_lane__2 c_2_124_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_124_elem => narrow__ (lsize (lanetype_Jnn Jnn.I32)) (lsize (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_2_124_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ((Map (fun c'_1_38_elem => lane_.mk_lane__2 Jnn.I16 c'_1_38_elem) c'_1_lst) ++ (Map (fun c'_2_38_elem => lane_.mk_lane__2 Jnn.I16 c'_2_38_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) →
    Forall (fun c'_1_39_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I16 c'_1_39_elem)) c'_1_lst →
    Forall (fun c'_2_39_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I16 c'_2_39_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I32 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_13 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_174_elem => (proj_lane__2 c_1_174_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_174_elem => narrow__ (lsize (lanetype_Jnn Jnn.I64)) (lsize (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_174_elem))) c_1_lst) →
    Forall (fun c_2_126_elem => (proj_lane__2 c_2_126_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_126_elem => narrow__ (lsize (lanetype_Jnn Jnn.I64)) (lsize (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_2_126_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ((Map (fun c'_1_41_elem => lane_.mk_lane__2 Jnn.I16 c'_1_41_elem) c'_1_lst) ++ (Map (fun c'_2_41_elem => lane_.mk_lane__2 Jnn.I16 c'_2_41_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) →
    Forall (fun c'_1_42_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I16 c'_1_42_elem)) c'_1_lst →
    Forall (fun c'_2_42_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I16 c'_2_42_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I64 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_14 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_176_elem => (proj_lane__2 c_1_176_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_176_elem => narrow__ (lsize (lanetype_Jnn Jnn.I8)) (lsize (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_176_elem))) c_1_lst) →
    Forall (fun c_2_128_elem => (proj_lane__2 c_2_128_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_128_elem => narrow__ (lsize (lanetype_Jnn Jnn.I8)) (lsize (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_2_128_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ((Map (fun c'_1_44_elem => lane_.mk_lane__2 Jnn.I16 c'_1_44_elem) c'_1_lst) ++ (Map (fun c'_2_44_elem => lane_.mk_lane__2 Jnn.I16 c'_2_44_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) →
    Forall (fun c'_1_45_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I16 c'_1_45_elem)) c'_1_lst →
    Forall (fun c'_2_45_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I16 c'_2_45_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I8 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) v_sx v_1 v_2 v
  | fun_vnarrowop___case_15 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (v_2 : uN) (c_1_lst : List lane_) (c_2_lst : List lane_) (c'_1_lst : List iN) (c'_2_lst : List iN) (v : vec_) :
    c_1_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_1) →
    c_2_lst = (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_2) →
    Forall (fun c_1_178_elem => (proj_lane__2 c_1_178_elem) ≠ none) c_1_lst →
    c'_1_lst = (Map (fun c_1_178_elem => narrow__ (lsize (lanetype_Jnn Jnn.I16)) (lsize (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_178_elem))) c_1_lst) →
    Forall (fun c_2_130_elem => (proj_lane__2 c_2_130_elem) ≠ none) c_2_lst →
    c'_2_lst = (Map (fun c_2_130_elem => narrow__ (lsize (lanetype_Jnn Jnn.I16)) (lsize (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_2_130_elem))) c_2_lst) →
    v = (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ((Map (fun c'_1_47_elem => lane_.mk_lane__2 Jnn.I16 c'_1_47_elem) c'_1_lst) ++ (Map (fun c'_2_47_elem => lane_.mk_lane__2 Jnn.I16 c'_2_47_elem) c'_2_lst))) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) →
    Forall (fun c'_1_48_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I16 c'_1_48_elem)) c'_1_lst →
    Forall (fun c'_2_48_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (lane_.mk_lane__2 Jnn.I16 c'_2_48_elem)) c'_2_lst →
    fun_vnarrowop__ (shape.X lanetype.I16 (dim.mk_dim M_1)) (shape.X lanetype.I16 (dim.mk_dim M_2)) v_sx v_1 v_2 v


inductive vnarrowop___is_wf : shape → shape → sx → vec_ → vec_ → vec_ → Prop where
  | vnarrowop___is_wf_0 (shape_1 : shape) (shape_2 : shape) (v_sx : sx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_) :
    fun_vnarrowop__ shape_1 shape_2 v_sx v_vec_ vec__0 var_0 →
    wf_shape shape_1 →
    wf_shape shape_2 →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    ret_val = var_0 →
    wf_uN 128 ret_val →
    vnarrowop___is_wf shape_1 shape_2 v_sx v_vec_ vec__0 ret_val


def ivadd_pairwise_ (v_N : N) (var_0_lst : List iN) : List iN :=
  (concat_ N (Map₂ (fun j_1_1_elem j_2_1_elem => [j_1_1_elem, j_2_1_elem]) j_1_lst j_2_lst)) = (Map (fun i_42815_elem => proj_uN_0 i_42815_elem) var_0_lst) → Map₂ (fun j_1_elem j_2_elem => iadd_ v_N (uN.mk_uN j_1_elem) (uN.mk_uN j_2_elem)) j_1_lst j_2_lst

inductive ivadd_pairwise__is_wf : N → List iN → List iN → Prop where
  | ivadd_pairwise__is_wf_0 (v_N : N) (var_0_lst : List iN) (ret_val_lst : List iN) :
    Forall (fun var_0_elem => wf_uN v_N var_0_elem) var_0_lst →
    ret_val_lst = (ivadd_pairwise_ v_N var_0_lst) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) ret_val_lst →
    ivadd_pairwise__is_wf v_N var_0_lst ret_val_lst


def ivextunop__ (shape_1 : shape) (shape_2 : shape) (f_ : N → List iN → List iN) (v_sx : sx) (v_vec_ : vec_) : Option vec_ :=
  match shape_1, shape_2 with
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_180_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_180_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I32)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (Map (fun c_146_elem => lane_.mk_lane__2 Jnn.I32 c_146_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_182_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_182_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I32)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (Map (fun c_148_elem => lane_.mk_lane__2 Jnn.I32 c_148_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_184_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_184_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I32)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (Map (fun c_150_elem => lane_.mk_lane__2 Jnn.I32 c_150_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_186_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_186_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I32)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (Map (fun c_152_elem => lane_.mk_lane__2 Jnn.I32 c_152_elem) c_lst))
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_188_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_188_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I64)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (Map (fun c_154_elem => lane_.mk_lane__2 Jnn.I64 c_154_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_190_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_190_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I64)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (Map (fun c_156_elem => lane_.mk_lane__2 Jnn.I64 c_156_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_192_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_192_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I64)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (Map (fun c_158_elem => lane_.mk_lane__2 Jnn.I64 c_158_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_194_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_194_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I64)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (Map (fun c_160_elem => lane_.mk_lane__2 Jnn.I64 c_160_elem) c_lst))
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_196_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_196_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I8)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (Map (fun c_162_elem => lane_.mk_lane__2 Jnn.I8 c_162_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_198_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_198_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I8)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (Map (fun c_164_elem => lane_.mk_lane__2 Jnn.I8 c_164_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_200_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_200_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I8)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (Map (fun c_166_elem => lane_.mk_lane__2 Jnn.I8 c_166_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_202_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_202_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I8)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (Map (fun c_168_elem => lane_.mk_lane__2 Jnn.I8 c_168_elem) c_lst))
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_204_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_204_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I16)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (Map (fun c_170_elem => lane_.mk_lane__2 Jnn.I16 c_170_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_206_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_206_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I16)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (Map (fun c_172_elem => lane_.mk_lane__2 Jnn.I16 c_172_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_208_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_208_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I16)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (Map (fun c_174_elem => lane_.mk_lane__2 Jnn.I16 c_174_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2) => let c_1_lst := lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_vec_
  let c'_1_lst := Map (fun c_1_210_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_210_elem))) c_1_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I16)) c'_1_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (Map (fun c_176_elem => lane_.mk_lane__2 Jnn.I16 c_176_elem) c_lst))
  | _, _ => none

inductive ivextunop___is_wf (f_ : N → List iN → List iN) : shape → shape → sx → vec_ → vec_ → Prop where
  | ivextunop___is_wf_0 (shape_1 : shape) (shape_2 : shape) (v_sx : sx) (v_vec_ : vec_) (ret_val : vec_) :
    wf_shape shape_1 →
    wf_shape shape_2 →
    wf_uN 128 v_vec_ →
    (ivextunop__ shape_1 shape_2 f_ v_sx v_vec_) ≠ none →
    ret_val = (Option.get! (ivextunop__ shape_1 shape_2 f_ v_sx v_vec_)) →
    wf_uN 128 ret_val →
    ivextunop___is_wf f_ shape_1 shape_2 v_sx v_vec_ ret_val


inductive fun_vextunop__ : ishape → ishape → vextunop__ → vec_ → vec_ → Prop where
  | fun_vextunop___case_0 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I32 M_1_0 Jnn.I32 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_1 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I64 M_1_0 Jnn.I32 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_2 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I8 M_1_0 Jnn.I32 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_3 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I16 M_1_0 Jnn.I32 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_4 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I32 M_1_0 Jnn.I64 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_5 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I64 M_1_0 Jnn.I64 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_6 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I8 M_1_0 Jnn.I64 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_7 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I16 M_1_0 Jnn.I64 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_8 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I32 M_1_0 Jnn.I8 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_9 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I64 M_1_0 Jnn.I8 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_10 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I8 M_1_0 Jnn.I8 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_11 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I16 M_1_0 Jnn.I8 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_12 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I32 M_1_0 Jnn.I16 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_13 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I64 M_1_0 Jnn.I16 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_14 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I8 M_1_0 Jnn.I16 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))
  | fun_vextunop___case_15 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (v_1 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextunop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextunop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 Jnn.I16 M_1_0 Jnn.I16 M_2_0 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE v_sx)) v_1 (Option.get! (ivextunop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivadd_pairwise_ v_sx v_1))


inductive vextunop___is_wf : ishape → ishape → vextunop__ → vec_ → vec_ → Prop where
  | vextunop___is_wf_0 (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop__ : vextunop__) (v_vec_ : vec_) (ret_val : vec_) (var_0 : vec_) :
    fun_vextunop__ ishape_1 ishape_2 v_vextunop__ v_vec_ var_0 →
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextunop__ ishape_1 ishape_2 v_vextunop__ →
    wf_uN 128 v_vec_ →
    ret_val = var_0 →
    wf_uN 128 ret_val →
    vextunop___is_wf ishape_1 ishape_2 v_vextunop__ v_vec_ ret_val


def ivdot_ (v_N : N) (var_0_lst : List iN) (var_1_lst : List iN) : List iN :=
  (concat_ iN (Map₂ (fun j_1_2_elem j_2_2_elem => [j_1_2_elem, j_2_2_elem]) j_1_lst j_2_lst)) = (Map₂ (fun i_1_2_elem i_2_2_elem => imul_ v_N i_1_2_elem i_2_2_elem) var_0_lst var_1_lst) → Map₂ (fun j_1_elem j_2_elem => iadd_ v_N j_1_elem j_2_elem) j_1_lst j_2_lst

inductive ivdot__is_wf : N → List iN → List iN → List iN → Prop where
  | ivdot__is_wf_0 (v_N : N) (var_0_lst : List iN) (var_1_lst : List iN) (ret_val_lst : List iN) :
    Forall (fun var_0_elem => wf_uN v_N var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_uN v_N var_1_elem) var_1_lst →
    ret_val_lst = (ivdot_ v_N var_0_lst var_1_lst) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) ret_val_lst →
    ivdot__is_wf v_N var_0_lst var_1_lst ret_val_lst


def ivdot_sat_ (v_N : N) (var_0_lst : List iN) (var_1_lst : List iN) : List iN :=
  (concat_ iN (Map₂ (fun j_1_3_elem j_2_3_elem => [j_1_3_elem, j_2_3_elem]) j_1_lst j_2_lst)) = (Map₂ (fun i_1_4_elem i_2_4_elem => imul_ v_N i_1_4_elem i_2_4_elem) var_0_lst var_1_lst) → Map₂ (fun j_1_elem j_2_elem => iadd_sat_ v_N sx.S j_1_elem j_2_elem) j_1_lst j_2_lst

inductive ivdot_sat__is_wf : N → List iN → List iN → List iN → Prop where
  | ivdot_sat__is_wf_0 (v_N : N) (var_0_lst : List iN) (var_1_lst : List iN) (ret_val_lst : List iN) :
    Forall (fun var_0_elem => wf_uN v_N var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_uN v_N var_1_elem) var_1_lst →
    ret_val_lst = (ivdot_sat_ v_N var_0_lst var_1_lst) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) ret_val_lst →
    ivdot_sat__is_wf v_N var_0_lst var_1_lst ret_val_lst


def ivextbinop__ (shape_1 : shape) (shape_2 : shape) (f_ : N → List iN → List iN → List iN) (v_sx : sx) (sx_0 : sx) (v_laneidx : laneidx) (laneidx_0 : laneidx) (v_vec_ : vec_) (vec__0 : vec_) : Option vec_ :=
  match shape_1, shape_2 with
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_212_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_212_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_132_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I32)) sx_0 (Option.get! (proj_lane__2 c_2_132_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I32)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (Map (fun c_178_elem => lane_.mk_lane__2 Jnn.I32 c_178_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_214_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_214_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_134_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I32)) sx_0 (Option.get! (proj_lane__2 c_2_134_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I32)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (Map (fun c_180_elem => lane_.mk_lane__2 Jnn.I32 c_180_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_216_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_216_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_136_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I32)) sx_0 (Option.get! (proj_lane__2 c_2_136_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I32)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (Map (fun c_182_elem => lane_.mk_lane__2 Jnn.I32 c_182_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_218_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 c_1_218_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_138_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I32)) sx_0 (Option.get! (proj_lane__2 c_2_138_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I32)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (Map (fun c_184_elem => lane_.mk_lane__2 Jnn.I32 c_184_elem) c_lst))
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_220_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_220_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_140_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I64)) sx_0 (Option.get! (proj_lane__2 c_2_140_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I64)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (Map (fun c_186_elem => lane_.mk_lane__2 Jnn.I64 c_186_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_222_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_222_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_142_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I64)) sx_0 (Option.get! (proj_lane__2 c_2_142_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I64)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (Map (fun c_188_elem => lane_.mk_lane__2 Jnn.I64 c_188_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_224_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_224_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_144_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I64)) sx_0 (Option.get! (proj_lane__2 c_2_144_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I64)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (Map (fun c_190_elem => lane_.mk_lane__2 Jnn.I64 c_190_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_226_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 c_1_226_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_146_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I64)) sx_0 (Option.get! (proj_lane__2 c_2_146_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I64)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (Map (fun c_192_elem => lane_.mk_lane__2 Jnn.I64 c_192_elem) c_lst))
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_228_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_228_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_148_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I8)) sx_0 (Option.get! (proj_lane__2 c_2_148_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I8)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (Map (fun c_194_elem => lane_.mk_lane__2 Jnn.I8 c_194_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_230_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_230_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_150_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I8)) sx_0 (Option.get! (proj_lane__2 c_2_150_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I8)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (Map (fun c_196_elem => lane_.mk_lane__2 Jnn.I8 c_196_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_232_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_232_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_152_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I8)) sx_0 (Option.get! (proj_lane__2 c_2_152_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I8)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (Map (fun c_198_elem => lane_.mk_lane__2 Jnn.I8 c_198_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_234_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 c_1_234_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_154_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I8)) sx_0 (Option.get! (proj_lane__2 c_2_154_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I8)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (Map (fun c_200_elem => lane_.mk_lane__2 Jnn.I8 c_200_elem) c_lst))
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_236_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_236_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_156_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I32)) (lsizenn2 (lanetype_Jnn Jnn.I16)) sx_0 (Option.get! (proj_lane__2 c_2_156_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I16)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (Map (fun c_202_elem => lane_.mk_lane__2 Jnn.I16 c_202_elem) c_lst))
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_238_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_238_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_158_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I64)) (lsizenn2 (lanetype_Jnn Jnn.I16)) sx_0 (Option.get! (proj_lane__2 c_2_158_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I16)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (Map (fun c_204_elem => lane_.mk_lane__2 Jnn.I16 c_204_elem) c_lst))
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_240_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_240_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_160_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I8)) (lsizenn2 (lanetype_Jnn Jnn.I16)) sx_0 (Option.get! (proj_lane__2 c_2_160_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I16)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (Map (fun c_206_elem => lane_.mk_lane__2 Jnn.I16 c_206_elem) c_lst))
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2) => let c_1_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) v_vec_))
  let c_2_lst := List.take (proj_uN_0 laneidx_0) (List.drop (proj_uN_0 v_laneidx) (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) vec__0))
  let c'_1_lst := Map (fun c_1_242_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 c_1_242_elem))) c_1_lst
  let c'_2_lst := Map (fun c_2_162_elem => extend__ (lsizenn1 (lanetype_Jnn Jnn.I16)) (lsizenn2 (lanetype_Jnn Jnn.I16)) sx_0 (Option.get! (proj_lane__2 c_2_162_elem))) c_2_lst
  let c_lst := f_ (lsizenn2 (lanetype_Jnn Jnn.I16)) c'_1_lst c'_2_lst
  wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) → some (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (Map (fun c_208_elem => lane_.mk_lane__2 Jnn.I16 c_208_elem) c_lst))
  | _, _ => none

inductive ivextbinop___is_wf (f_ : N → List iN → List iN → List iN) : shape → shape → sx → sx → laneidx → laneidx → vec_ → vec_ → vec_ → Prop where
  | ivextbinop___is_wf_0 (shape_1 : shape) (shape_2 : shape) (v_sx : sx) (sx_0 : sx) (v_laneidx : laneidx) (laneidx_0 : laneidx) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) :
    wf_shape shape_1 →
    wf_shape shape_2 →
    wf_uN 8 v_laneidx →
    wf_uN 8 laneidx_0 →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    (ivextbinop__ shape_1 shape_2 f_ v_sx sx_0 v_laneidx laneidx_0 v_vec_ vec__0) ≠ none →
    ret_val = (Option.get! (ivextbinop__ shape_1 shape_2 f_ v_sx sx_0 v_laneidx laneidx_0 v_vec_ vec__0)) →
    wf_uN 128 ret_val →
    ivextbinop___is_wf f_ shape_1 shape_2 v_sx sx_0 v_laneidx laneidx_0 v_vec_ vec__0 ret_val


def ivmul_ (v_N : N) (var_0_lst : List iN) (var_1_lst : List iN) : List iN :=
  Map₂ (fun i_1_elem i_2_elem => imul_ v_N i_1_elem i_2_elem) var_0_lst var_1_lst

inductive ivmul__is_wf : N → List iN → List iN → List iN → Prop where
  | ivmul__is_wf_0 (v_N : N) (var_0_lst : List iN) (var_1_lst : List iN) (ret_val_lst : List iN) :
    Forall (fun var_0_elem => wf_uN v_N var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_uN v_N var_1_elem) var_1_lst →
    ret_val_lst = (ivmul_ v_N var_0_lst var_1_lst) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) ret_val_lst →
    ivmul__is_wf v_N var_0_lst var_1_lst ret_val_lst


inductive fun_vextbinop__ : ishape → ishape → vextbinop__ → vec_ → vec_ → vec_ → Prop where
  | fun_vextbinop___case_0 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I32 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_1 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I32 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_2 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I32 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_3 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I32 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_4 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I64 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_5 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I64 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_6 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I64 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_7 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I64 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_8 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I8 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_9 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I8 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_10 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I8 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_11 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I8 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_12 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I16 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_13 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I16 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_14 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I16 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_15 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I16 M_2_0 (vextbinop__Jnn_1_M_1_Jnn_2_M_2.EXTMUL v_half v_sx)) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivmul_ v_sx v_sx (uN.mk_uN (fun_half v_half 0 M_2)) (uN.mk_uN M_2) v_1 v_2))
  | fun_vextbinop___case_16 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I32 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_17 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I32 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_18 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I32 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_19 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I32 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_20 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I64 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_21 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I64 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_22 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I64 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_23 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I64 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_24 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I8 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_25 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I8 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_26 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I8 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_27 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I8 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_28 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I16 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_29 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I16 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_30 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I16 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_31 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I16 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_ sx.S sx.S (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_32 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I32 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_33 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I32 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_34 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I32 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_35 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I32 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_36 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I64 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_37 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I64 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_38 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I64 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_39 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I64 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_40 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I8 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_41 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I8 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_42 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I8 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_43 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I8 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_44 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1_0 Jnn.I16 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_45 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1_0 Jnn.I16 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_46 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1_0 Jnn.I16 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))
  | fun_vextbinop___case_47 (M_1 : Nat) (M_2 : Nat) (v_1 : uN) (v_2 : uN) (M_1_0 : Nat) (M_2_0 : Nat) :
    (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2) ≠ none →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1_0 Jnn.I16 M_2_0 vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) v_1 v_2 (Option.get! (ivextbinop__ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1)) (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) ivdot_sat_ sx.S (fun_relaxed2 R_idot sx sx.S sx.U) (uN.mk_uN 0) (uN.mk_uN M_1) v_1 v_2))


inductive vextbinop___is_wf : ishape → ishape → vextbinop__ → vec_ → vec_ → vec_ → Prop where
  | vextbinop___is_wf_0 (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop__ : vextbinop__) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_) :
    fun_vextbinop__ ishape_1 ishape_2 v_vextbinop__ v_vec_ vec__0 var_0 →
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextbinop__ ishape_1 ishape_2 v_vextbinop__ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    ret_val = var_0 →
    wf_uN 128 ret_val →
    vextbinop___is_wf ishape_1 ishape_2 v_vextbinop__ v_vec_ vec__0 ret_val


inductive fun_vextternop__ : ishape → ishape → vextternop__ → vec_ → vec_ → vec_ → vec_ → Prop where
  | fun_vextternop___case_0 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I32 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I32 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I32))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I32 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I32 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I32 M_1_0 Jnn.I32 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_1 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I32 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I32 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I64))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I32 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I32 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I64 M_1_0 Jnn.I32 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_2 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I32 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I32 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I8))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I32 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I32 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I8 M_1_0 Jnn.I32 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_3 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I32 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I32 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I16))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I32 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I32 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I16 M_1_0 Jnn.I32 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_4 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I64 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I64 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I32))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I64 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I64 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I32 M_1_0 Jnn.I64 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_5 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I64 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I64 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I64))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I64 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I64 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I64 M_1_0 Jnn.I64 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_6 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I64 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I64 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I8))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I64 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I64 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I8 M_1_0 Jnn.I64 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_7 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I64 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I64 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I16))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I64 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I64 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I16 M_1_0 Jnn.I64 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_8 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I8 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I8 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I32))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I8 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I8 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I32 M_1_0 Jnn.I8 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_9 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I8 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I8 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I64))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I8 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I8 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I64 M_1_0 Jnn.I8 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_10 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I8 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I8 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I8))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I8 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I8 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I8 M_1_0 Jnn.I8 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_11 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I8 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I8 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I16))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I8 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I8 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I16 M_1_0 Jnn.I8 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_12 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I16 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I16 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I32))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I32 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I16 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I16 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I32 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I32 M_1_0 Jnn.I16 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_13 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I16 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I16 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I64))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I64 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I16 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I16 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I64 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I64 M_1_0 Jnn.I16 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_14 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I16 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I16 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I8))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I8 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I16 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I16 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I8 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I8 M_1_0 Jnn.I16 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c
  | fun_vextternop___case_15 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (c_3 : uN) (c : uN) (v_Jnn : Jnn) (M_1_0 : Nat) (M_2_0 : Nat) (v_M : M) (c' : vec_) (c'' : vec_) (var_2 : List vec_) (var_1 : vec_) (var_0 : vec_) :
    fun_vbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I16 M_2 vbinop_Jnn_M.ADD) c'' c_3 var_2 →
    fun_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I16 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) c' var_1 →
    fun_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) c_1 c_2 var_0 →
    (jsizenn v_Jnn) = (2 * (lsizenn1 (lanetype_Jnn Jnn.I16))) →
    v_M = (2 * M_2) →
    c' = var_0 →
    c'' = var_1 →
    (List.length var_2) > 0 →
    List.contains var_2 c →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) →
    wf_vextbinop__ (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (vextbinop__.mk_vextbinop___0 Jnn.I16 M_1 v_Jnn v_M vextbinop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOTS) →
    wf_ishape (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) →
    wf_vextunop__ (ishape.mk_ishape (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_M))) (ishape.mk_ishape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2))) (vextunop__.mk_vextunop___0 v_Jnn v_M Jnn.I16 M_2 (vextunop__Jnn_1_M_1_Jnn_2_M_2.EXTADD_PAIRWISE sx.S)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) →
    wf_vbinop_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim M_2)) (vbinop_.mk_vbinop__0 Jnn.I16 M_2 vbinop_Jnn_M.ADD) →
    M_1 = M_1_0 →
    M_2 = M_2_0 →
    fun_vextternop__ (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_1))) (ishape.mk_ishape (shape.X lanetype.I16 (dim.mk_dim M_2))) (vextternop__.mk_vextternop___0 Jnn.I16 M_1_0 Jnn.I16 M_2_0 vextternop__Jnn_1_M_1_Jnn_2_M_2.RELAXED_DOT_ADDS) c_1 c_2 c_3 c


inductive vextternop___is_wf : ishape → ishape → vextternop__ → vec_ → vec_ → vec_ → vec_ → Prop where
  | vextternop___is_wf_0 (ishape_1 : ishape) (ishape_2 : ishape) (v_vextternop__ : vextternop__) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val : vec_) (var_0 : vec_) :
    fun_vextternop__ ishape_1 ishape_2 v_vextternop__ v_vec_ vec__0 vec__1 var_0 →
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextternop__ ishape_1 ishape_2 v_vextternop__ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    wf_uN 128 vec__1 →
    ret_val = var_0 →
    wf_uN 128 ret_val →
    vextternop___is_wf ishape_1 ishape_2 v_vextternop__ v_vec_ vec__0 vec__1 ret_val


inductive num : Type where
  | CONST (v_numtype : numtype) (_ : num_) : num
deriving Inhabited, BEq

def val_num (var_0 : num) : val :=
  match var_0 with
  | num.CONST x0 x1 => val.CONST x0 x1

inductive wf_num : num → Prop where
  | num_case_0 (v_numtype : numtype) (var_0 : num_) :
    wf_num_ v_numtype var_0 →
    wf_num (num.CONST v_numtype var_0)


inductive vec : Type where
  | VCONST (v_vectype : vectype) (_ : vec_) : vec
deriving Inhabited, BEq

def val_vec (var_0 : vec) : val :=
  match var_0 with
  | vec.VCONST x0 x1 => val.VCONST x0 x1

inductive wf_vec : vec → Prop where
  | vec_case_0 (v_vectype : vectype) (var_0 : vec_) :
    wf_uN (vsize v_vectype) var_0 →
    wf_vec (vec.VCONST v_vectype var_0)


inductive result : Type where
  | _VALS (val_lst : List val) : result
  | REF_EXN_ADDRTHROW_REF (v_exnaddr : exnaddr) : result
  | TRAP : result
deriving Inhabited, BEq

inductive wf_result : result → Prop where
  | result_case_0 (val_lst : List val) :
    Forall (fun v_val_elem => wf_val v_val_elem) val_lst →
    wf_result (result._VALS val_lst)
  | result_case_1 (v_exnaddr : exnaddr) : wf_result (result.REF_EXN_ADDRTHROW_REF v_exnaddr)
  | result_case_2 : wf_result result.TRAP


inductive hostfunc : Type where
  | mk_hostfunc : hostfunc
deriving Inhabited, BEq

inductive funccode : Type where
  | FUNC (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) : funccode
  | mk_funccode : funccode
deriving Inhabited, BEq

inductive wf_funccode : funccode → Prop where
  | funccode_case_0 (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) :
    wf_uN 32 v_typeidx →
    Forall (fun v_local_elem => wf_local v_local_elem) local_lst →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_funccode (funccode.FUNC v_typeidx local_lst v_expr)
  | funccode_case_1 : wf_funccode funccode.mk_funccode


structure taginst where
  MKtaginst ::
  TYPE : tagtype
deriving Inhabited, BEq

inductive wf_taginst : taginst → Prop where
  | taginst_case_ (var_0 : tagtype) :
    wf_typeuse var_0 →
    wf_taginst ({
      TYPE := var_0 : taginst
    })


structure globalinst where
  MKglobalinst ::
  TYPE : globaltype
  VALUE : val
deriving Inhabited, BEq

inductive wf_globalinst : globalinst → Prop where
  | globalinst_case_ (var_0 : globaltype) (var_1 : val) :
    wf_globaltype var_0 →
    wf_val var_1 →
    wf_globalinst ({
      TYPE := var_0
      VALUE := var_1 : globalinst
    })


structure meminst where
  MKmeminst ::
  TYPE : memtype
  BYTES : List byte
deriving Inhabited, BEq

inductive wf_meminst : meminst → Prop where
  | meminst_case_ (var_0 : memtype) (var_1_lst : List byte) :
    wf_memtype var_0 →
    Forall (fun var_1_elem => wf_byte var_1_elem) var_1_lst →
    wf_meminst ({
      TYPE := var_0
      BYTES := var_1_lst : meminst
    })


structure tableinst where
  MKtableinst ::
  TYPE : tabletype
  REFS : List ref
deriving Inhabited, BEq

inductive wf_tableinst : tableinst → Prop where
  | tableinst_case_ (var_0 : tabletype) (var_1_lst : List ref) :
    wf_tabletype var_0 →
    Forall (fun var_1_elem => wf_ref var_1_elem) var_1_lst →
    wf_tableinst ({
      TYPE := var_0
      REFS := var_1_lst : tableinst
    })


structure funcinst where
  MKfuncinst ::
  TYPE : deftype
  MODULE : moduleinst
  CODE : funccode
deriving Inhabited, BEq

inductive wf_funcinst : funcinst → Prop where
  | funcinst_case_ (var_0 : deftype) (var_1 : moduleinst) (var_2 : funccode) :
    wf_moduleinst var_1 →
    wf_funccode var_2 →
    wf_funcinst ({
      TYPE := var_0
      MODULE := var_1
      CODE := var_2 : funcinst
    })


structure datainst where
  MKdatainst ::
  BYTES : List byte
deriving Inhabited, BEq

inductive wf_datainst : datainst → Prop where
  | datainst_case_ (var_0_lst : List byte) :
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    wf_datainst ({
      BYTES := var_0_lst : datainst
    })


structure eleminst where
  MKeleminst ::
  TYPE : elemtype
  REFS : List ref
deriving Inhabited, BEq

inductive wf_eleminst : eleminst → Prop where
  | eleminst_case_ (var_0 : elemtype) (var_1_lst : List ref) :
    wf_reftype var_0 →
    Forall (fun var_1_elem => wf_ref var_1_elem) var_1_lst →
    wf_eleminst ({
      TYPE := var_0
      REFS := var_1_lst : eleminst
    })


inductive packval : Type where
  | PACK (v_packtype : packtype) (_ : iN) : packval
deriving Inhabited, BEq

inductive wf_packval : packval → Prop where
  | packval_case_0 (v_packtype : packtype) (var_0 : iN) :
    wf_uN (psize v_packtype) var_0 →
    wf_packval (packval.PACK v_packtype var_0)


inductive fieldval : Type where
  | CONST (v_numtype : numtype) (_ : num_) : fieldval
  | VCONST (v_vectype : vectype) (_ : vec_) : fieldval
  | REF_I31_NUM (v_u31 : u31) : fieldval
  | REF_NULL_ADDR : fieldval
  | REF_STRUCT_ADDR (v_structaddr : structaddr) : fieldval
  | REF_ARRAY_ADDR (v_arrayaddr : arrayaddr) : fieldval
  | REF_FUNC_ADDR (v_funcaddr : funcaddr) : fieldval
  | REF_EXN_ADDR (v_exnaddr : exnaddr) : fieldval
  | REF_HOST_ADDR (v_hostaddr : hostaddr) : fieldval
  | REF_EXTERN (v_ref : ref) : fieldval
  | PACK (v_packtype : packtype) (_ : iN) : fieldval
deriving Inhabited, BEq

def fieldval_packval (var_0 : packval) : fieldval :=
  match var_0 with
  | packval.PACK x0 x1 => fieldval.PACK x0 x1

def fieldval_val (var_0 : val) : fieldval :=
  match var_0 with
  | val.CONST x0 x1 => fieldval.CONST x0 x1
  | val.VCONST x0 x1 => fieldval.VCONST x0 x1
  | val.REF_I31_NUM x0 => fieldval.REF_I31_NUM x0
  | val.REF_NULL_ADDR => fieldval.REF_NULL_ADDR
  | val.REF_STRUCT_ADDR x0 => fieldval.REF_STRUCT_ADDR x0
  | val.REF_ARRAY_ADDR x0 => fieldval.REF_ARRAY_ADDR x0
  | val.REF_FUNC_ADDR x0 => fieldval.REF_FUNC_ADDR x0
  | val.REF_EXN_ADDR x0 => fieldval.REF_EXN_ADDR x0
  | val.REF_HOST_ADDR x0 => fieldval.REF_HOST_ADDR x0
  | val.REF_EXTERN x0 => fieldval.REF_EXTERN x0

inductive wf_fieldval : fieldval → Prop where
  | fieldval_case_0 (v_numtype : numtype) (var_0 : num_) :
    wf_num_ v_numtype var_0 →
    wf_fieldval (fieldval.CONST v_numtype var_0)
  | fieldval_case_1 (v_vectype : vectype) (var_0 : vec_) :
    wf_uN (vsize v_vectype) var_0 →
    wf_fieldval (fieldval.VCONST v_vectype var_0)
  | fieldval_case_2 (v_u31 : u31) :
    wf_uN 31 v_u31 →
    wf_fieldval (fieldval.REF_I31_NUM v_u31)
  | fieldval_case_3 : wf_fieldval fieldval.REF_NULL_ADDR
  | fieldval_case_4 (v_structaddr : structaddr) : wf_fieldval (fieldval.REF_STRUCT_ADDR v_structaddr)
  | fieldval_case_5 (v_arrayaddr : arrayaddr) : wf_fieldval (fieldval.REF_ARRAY_ADDR v_arrayaddr)
  | fieldval_case_6 (v_funcaddr : funcaddr) : wf_fieldval (fieldval.REF_FUNC_ADDR v_funcaddr)
  | fieldval_case_7 (v_exnaddr : exnaddr) : wf_fieldval (fieldval.REF_EXN_ADDR v_exnaddr)
  | fieldval_case_8 (v_hostaddr : hostaddr) : wf_fieldval (fieldval.REF_HOST_ADDR v_hostaddr)
  | fieldval_case_9 (v_ref : ref) :
    wf_ref v_ref →
    wf_fieldval (fieldval.REF_EXTERN v_ref)
  | fieldval_case_10 (v_packtype : packtype) (var_0 : iN) :
    wf_uN (psize v_packtype) var_0 →
    wf_fieldval (fieldval.PACK v_packtype var_0)


structure structinst where
  MKstructinst ::
  TYPE : deftype
  FIELDS : List fieldval
deriving Inhabited, BEq

inductive wf_structinst : structinst → Prop where
  | structinst_case_ (var_0 : deftype) (var_1_lst : List fieldval) :
    Forall (fun var_1_elem => wf_fieldval var_1_elem) var_1_lst →
    wf_structinst ({
      TYPE := var_0
      FIELDS := var_1_lst : structinst
    })


structure arrayinst where
  MKarrayinst ::
  TYPE : deftype
  FIELDS : List fieldval
deriving Inhabited, BEq

inductive wf_arrayinst : arrayinst → Prop where
  | arrayinst_case_ (var_0 : deftype) (var_1_lst : List fieldval) :
    Forall (fun var_1_elem => wf_fieldval var_1_elem) var_1_lst →
    wf_arrayinst ({
      TYPE := var_0
      FIELDS := var_1_lst : arrayinst
    })


structure exninst where
  MKexninst ::
  TAG : tagaddr
  FIELDS : List val
deriving Inhabited, BEq

inductive wf_exninst : exninst → Prop where
  | exninst_case_ (var_0 : tagaddr) (var_1_lst : List val) :
    Forall (fun var_1_elem => wf_val var_1_elem) var_1_lst →
    wf_exninst ({
      TAG := var_0
      FIELDS := var_1_lst : exninst
    })


structure store where
  MKstore ::
  TAGS : List taginst
  GLOBALS : List globalinst
  MEMS : List meminst
  TABLES : List tableinst
  FUNCS : List funcinst
  DATAS : List datainst
  ELEMS : List eleminst
  STRUCTS : List structinst
  ARRAYS : List arrayinst
  EXNS : List exninst
deriving Inhabited, BEq

inductive wf_store : store → Prop where
  | store_case_ (var_0_lst : List taginst) (var_1_lst : List globalinst) (var_2_lst : List meminst) (var_3_lst : List tableinst) (var_4_lst : List funcinst) (var_5_lst : List datainst) (var_6_lst : List eleminst) (var_7_lst : List structinst) (var_8_lst : List arrayinst) (var_9_lst : List exninst) :
    Forall (fun var_0_elem => wf_taginst var_0_elem) var_0_lst →
    Forall (fun var_1_elem => wf_globalinst var_1_elem) var_1_lst →
    Forall (fun var_2_elem => wf_meminst var_2_elem) var_2_lst →
    Forall (fun var_3_elem => wf_tableinst var_3_elem) var_3_lst →
    Forall (fun var_4_elem => wf_funcinst var_4_elem) var_4_lst →
    Forall (fun var_5_elem => wf_datainst var_5_elem) var_5_lst →
    Forall (fun var_6_elem => wf_eleminst var_6_elem) var_6_lst →
    Forall (fun var_7_elem => wf_structinst var_7_elem) var_7_lst →
    Forall (fun var_8_elem => wf_arrayinst var_8_elem) var_8_lst →
    Forall (fun var_9_elem => wf_exninst var_9_elem) var_9_lst →
    wf_store ({
      TAGS := var_0_lst
      GLOBALS := var_1_lst
      MEMS := var_2_lst
      TABLES := var_3_lst
      FUNCS := var_4_lst
      DATAS := var_5_lst
      ELEMS := var_6_lst
      STRUCTS := var_7_lst
      ARRAYS := var_8_lst
      EXNS := var_9_lst : store
    })


inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq

inductive wf_state : state → Prop where
  | state_case_0 (v_store : store) (v_frame : frame) :
    wf_store v_store →
    wf_frame v_frame →
    wf_state (state.mk_state v_store v_frame)


inductive config : Type where
  | mk_config (v_state : state) (instr_lst : List instr) : config
deriving Inhabited, BEq

inductive wf_config : config → Prop where
  | config_case_0 (v_state : state) (instr_lst : List instr) :
    wf_state v_state →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_config (config.mk_config v_state instr_lst)


def Ki : Nat :=
  1024

def packfield_ (v_storagetype : storagetype) (v_val : val) : Option fieldval :=
  match v_storagetype, v_val with
  | storagetype.BOT, _ => some (fieldval_val v_val)
  | storagetype.REF null_opt v_heaptype, _ => some (fieldval_val v_val)
  | storagetype.V128, _ => some (fieldval_val v_val)
  | storagetype.F64, _ => some (fieldval_val v_val)
  | storagetype.F32, _ => some (fieldval_val v_val)
  | storagetype.I64, _ => some (fieldval_val v_val)
  | storagetype.I32, _ => some (fieldval_val v_val)
  | storagetype.I8, val.CONST numtype.I32 (num_.mk_num__0 addrtype.I32 i) => some (fieldval.PACK packtype.I8 (wrap__ 32 (psize packtype.I8) i))
  | storagetype.I16, val.CONST numtype.I32 (num_.mk_num__0 addrtype.I32 i) => some (fieldval.PACK packtype.I16 (wrap__ 32 (psize packtype.I16) i))
  | _, _ => none

inductive packfield__is_wf : storagetype → val → fieldval → Prop where
  | packfield__is_wf_0 (v_storagetype : storagetype) (v_val : val) (ret_val : fieldval) :
    wf_storagetype v_storagetype →
    wf_val v_val →
    (packfield_ v_storagetype v_val) ≠ none →
    ret_val = (Option.get! (packfield_ v_storagetype v_val)) →
    wf_fieldval ret_val →
    packfield__is_wf v_storagetype v_val ret_val


def unpackfield_ (v_storagetype : storagetype) (var_0_opt : Option sx) (v_fieldval : fieldval) : Option val :=
  match v_storagetype, var_0_opt, v_fieldval with
  | storagetype.BOT, none, fieldval.REF_EXTERN v_ref => some (val.REF_EXTERN v_ref)
  | storagetype.REF null_opt v_heaptype, none, fieldval.REF_EXTERN v_ref => some (val.REF_EXTERN v_ref)
  | storagetype.V128, none, fieldval.REF_EXTERN v_ref => some (val.REF_EXTERN v_ref)
  | storagetype.F64, none, fieldval.REF_EXTERN v_ref => some (val.REF_EXTERN v_ref)
  | storagetype.F32, none, fieldval.REF_EXTERN v_ref => some (val.REF_EXTERN v_ref)
  | storagetype.I64, none, fieldval.REF_EXTERN v_ref => some (val.REF_EXTERN v_ref)
  | storagetype.I32, none, fieldval.REF_EXTERN v_ref => some (val.REF_EXTERN v_ref)
  | storagetype.BOT, none, fieldval.REF_HOST_ADDR v_hostaddr => some (val.REF_HOST_ADDR v_hostaddr)
  | storagetype.REF null_opt v_heaptype, none, fieldval.REF_HOST_ADDR v_hostaddr => some (val.REF_HOST_ADDR v_hostaddr)
  | storagetype.V128, none, fieldval.REF_HOST_ADDR v_hostaddr => some (val.REF_HOST_ADDR v_hostaddr)
  | storagetype.F64, none, fieldval.REF_HOST_ADDR v_hostaddr => some (val.REF_HOST_ADDR v_hostaddr)
  | storagetype.F32, none, fieldval.REF_HOST_ADDR v_hostaddr => some (val.REF_HOST_ADDR v_hostaddr)
  | storagetype.I64, none, fieldval.REF_HOST_ADDR v_hostaddr => some (val.REF_HOST_ADDR v_hostaddr)
  | storagetype.I32, none, fieldval.REF_HOST_ADDR v_hostaddr => some (val.REF_HOST_ADDR v_hostaddr)
  | storagetype.BOT, none, fieldval.REF_EXN_ADDR v_exnaddr => some (val.REF_EXN_ADDR v_exnaddr)
  | storagetype.REF null_opt v_heaptype, none, fieldval.REF_EXN_ADDR v_exnaddr => some (val.REF_EXN_ADDR v_exnaddr)
  | storagetype.V128, none, fieldval.REF_EXN_ADDR v_exnaddr => some (val.REF_EXN_ADDR v_exnaddr)
  | storagetype.F64, none, fieldval.REF_EXN_ADDR v_exnaddr => some (val.REF_EXN_ADDR v_exnaddr)
  | storagetype.F32, none, fieldval.REF_EXN_ADDR v_exnaddr => some (val.REF_EXN_ADDR v_exnaddr)
  | storagetype.I64, none, fieldval.REF_EXN_ADDR v_exnaddr => some (val.REF_EXN_ADDR v_exnaddr)
  | storagetype.I32, none, fieldval.REF_EXN_ADDR v_exnaddr => some (val.REF_EXN_ADDR v_exnaddr)
  | storagetype.BOT, none, fieldval.REF_FUNC_ADDR v_funcaddr => some (val.REF_FUNC_ADDR v_funcaddr)
  | storagetype.REF null_opt v_heaptype, none, fieldval.REF_FUNC_ADDR v_funcaddr => some (val.REF_FUNC_ADDR v_funcaddr)
  | storagetype.V128, none, fieldval.REF_FUNC_ADDR v_funcaddr => some (val.REF_FUNC_ADDR v_funcaddr)
  | storagetype.F64, none, fieldval.REF_FUNC_ADDR v_funcaddr => some (val.REF_FUNC_ADDR v_funcaddr)
  | storagetype.F32, none, fieldval.REF_FUNC_ADDR v_funcaddr => some (val.REF_FUNC_ADDR v_funcaddr)
  | storagetype.I64, none, fieldval.REF_FUNC_ADDR v_funcaddr => some (val.REF_FUNC_ADDR v_funcaddr)
  | storagetype.I32, none, fieldval.REF_FUNC_ADDR v_funcaddr => some (val.REF_FUNC_ADDR v_funcaddr)
  | storagetype.BOT, none, fieldval.REF_ARRAY_ADDR v_arrayaddr => some (val.REF_ARRAY_ADDR v_arrayaddr)
  | storagetype.REF null_opt v_heaptype, none, fieldval.REF_ARRAY_ADDR v_arrayaddr => some (val.REF_ARRAY_ADDR v_arrayaddr)
  | storagetype.V128, none, fieldval.REF_ARRAY_ADDR v_arrayaddr => some (val.REF_ARRAY_ADDR v_arrayaddr)
  | storagetype.F64, none, fieldval.REF_ARRAY_ADDR v_arrayaddr => some (val.REF_ARRAY_ADDR v_arrayaddr)
  | storagetype.F32, none, fieldval.REF_ARRAY_ADDR v_arrayaddr => some (val.REF_ARRAY_ADDR v_arrayaddr)
  | storagetype.I64, none, fieldval.REF_ARRAY_ADDR v_arrayaddr => some (val.REF_ARRAY_ADDR v_arrayaddr)
  | storagetype.I32, none, fieldval.REF_ARRAY_ADDR v_arrayaddr => some (val.REF_ARRAY_ADDR v_arrayaddr)
  | storagetype.BOT, none, fieldval.REF_STRUCT_ADDR v_structaddr => some (val.REF_STRUCT_ADDR v_structaddr)
  | storagetype.REF null_opt v_heaptype, none, fieldval.REF_STRUCT_ADDR v_structaddr => some (val.REF_STRUCT_ADDR v_structaddr)
  | storagetype.V128, none, fieldval.REF_STRUCT_ADDR v_structaddr => some (val.REF_STRUCT_ADDR v_structaddr)
  | storagetype.F64, none, fieldval.REF_STRUCT_ADDR v_structaddr => some (val.REF_STRUCT_ADDR v_structaddr)
  | storagetype.F32, none, fieldval.REF_STRUCT_ADDR v_structaddr => some (val.REF_STRUCT_ADDR v_structaddr)
  | storagetype.I64, none, fieldval.REF_STRUCT_ADDR v_structaddr => some (val.REF_STRUCT_ADDR v_structaddr)
  | storagetype.I32, none, fieldval.REF_STRUCT_ADDR v_structaddr => some (val.REF_STRUCT_ADDR v_structaddr)
  | storagetype.BOT, none, fieldval.REF_NULL_ADDR => some val.REF_NULL_ADDR
  | storagetype.REF null_opt v_heaptype, none, fieldval.REF_NULL_ADDR => some val.REF_NULL_ADDR
  | storagetype.V128, none, fieldval.REF_NULL_ADDR => some val.REF_NULL_ADDR
  | storagetype.F64, none, fieldval.REF_NULL_ADDR => some val.REF_NULL_ADDR
  | storagetype.F32, none, fieldval.REF_NULL_ADDR => some val.REF_NULL_ADDR
  | storagetype.I64, none, fieldval.REF_NULL_ADDR => some val.REF_NULL_ADDR
  | storagetype.I32, none, fieldval.REF_NULL_ADDR => some val.REF_NULL_ADDR
  | storagetype.BOT, none, fieldval.REF_I31_NUM v_u31 => some (val.REF_I31_NUM v_u31)
  | storagetype.REF null_opt v_heaptype, none, fieldval.REF_I31_NUM v_u31 => some (val.REF_I31_NUM v_u31)
  | storagetype.V128, none, fieldval.REF_I31_NUM v_u31 => some (val.REF_I31_NUM v_u31)
  | storagetype.F64, none, fieldval.REF_I31_NUM v_u31 => some (val.REF_I31_NUM v_u31)
  | storagetype.F32, none, fieldval.REF_I31_NUM v_u31 => some (val.REF_I31_NUM v_u31)
  | storagetype.I64, none, fieldval.REF_I31_NUM v_u31 => some (val.REF_I31_NUM v_u31)
  | storagetype.I32, none, fieldval.REF_I31_NUM v_u31 => some (val.REF_I31_NUM v_u31)
  | storagetype.BOT, none, fieldval.VCONST v_vectype var_1 => some (val.VCONST v_vectype var_1)
  | storagetype.REF null_opt v_heaptype, none, fieldval.VCONST v_vectype var_1 => some (val.VCONST v_vectype var_1)
  | storagetype.V128, none, fieldval.VCONST v_vectype var_1 => some (val.VCONST v_vectype var_1)
  | storagetype.F64, none, fieldval.VCONST v_vectype var_1 => some (val.VCONST v_vectype var_1)
  | storagetype.F32, none, fieldval.VCONST v_vectype var_1 => some (val.VCONST v_vectype var_1)
  | storagetype.I64, none, fieldval.VCONST v_vectype var_1 => some (val.VCONST v_vectype var_1)
  | storagetype.I32, none, fieldval.VCONST v_vectype var_1 => some (val.VCONST v_vectype var_1)
  | storagetype.BOT, none, fieldval.CONST v_numtype var_0 => some (val.CONST v_numtype var_0)
  | storagetype.REF null_opt v_heaptype, none, fieldval.CONST v_numtype var_0 => some (val.CONST v_numtype var_0)
  | storagetype.V128, none, fieldval.CONST v_numtype var_0 => some (val.CONST v_numtype var_0)
  | storagetype.F64, none, fieldval.CONST v_numtype var_0 => some (val.CONST v_numtype var_0)
  | storagetype.F32, none, fieldval.CONST v_numtype var_0 => some (val.CONST v_numtype var_0)
  | storagetype.I64, none, fieldval.CONST v_numtype var_0 => some (val.CONST v_numtype var_0)
  | storagetype.I32, none, fieldval.CONST v_numtype var_0 => some (val.CONST v_numtype var_0)
  | storagetype.I8, some v_sx, fieldval.PACK packtype.I8 i => some (val.CONST numtype.I32 (num_.mk_num__0 addrtype.I32 (extend__ (psize packtype.I8) 32 v_sx i)))
  | storagetype.I16, some v_sx, fieldval.PACK packtype.I16 i => some (val.CONST numtype.I32 (num_.mk_num__0 addrtype.I32 (extend__ (psize packtype.I16) 32 v_sx i)))
  | _, _, _ => none

inductive unpackfield__is_wf : storagetype → Option sx → fieldval → val → Prop where
  | unpackfield__is_wf_0 (v_storagetype : storagetype) (var_0_opt : Option sx) (v_fieldval : fieldval) (ret_val : val) :
    wf_storagetype v_storagetype →
    wf_fieldval v_fieldval →
    (unpackfield_ v_storagetype var_0_opt v_fieldval) ≠ none →
    ret_val = (Option.get! (unpackfield_ v_storagetype var_0_opt v_fieldval)) →
    wf_val ret_val →
    unpackfield__is_wf v_storagetype var_0_opt v_fieldval ret_val


inductive fun_tagsxa : List externaddr → List tagaddr → Prop where
  | fun_tagsxa_case_0 : fun_tagsxa [] []
  | fun_tagsxa_case_1 (a : Nat) (xa_lst : List externaddr) (var_0 : List tagaddr) :
    fun_tagsxa xa_lst var_0 →
    fun_tagsxa ([externaddr.TAG a] ++ xa_lst) ([a] ++ var_0)
  | fun_tagsxa_case_2 (v_externaddr : externaddr) (xa_lst : List externaddr) (var_0 : List tagaddr) :
    fun_tagsxa xa_lst var_0 →
    fun_tagsxa ([v_externaddr] ++ xa_lst) var_0


inductive fun_globalsxa : List externaddr → List globaladdr → Prop where
  | fun_globalsxa_case_0 : fun_globalsxa [] []
  | fun_globalsxa_case_1 (a : Nat) (xa_lst : List externaddr) (var_0 : List globaladdr) :
    fun_globalsxa xa_lst var_0 →
    fun_globalsxa ([externaddr.GLOBAL a] ++ xa_lst) ([a] ++ var_0)
  | fun_globalsxa_case_2 (v_externaddr : externaddr) (xa_lst : List externaddr) (var_0 : List globaladdr) :
    fun_globalsxa xa_lst var_0 →
    fun_globalsxa ([v_externaddr] ++ xa_lst) var_0


inductive fun_memsxa : List externaddr → List memaddr → Prop where
  | fun_memsxa_case_0 : fun_memsxa [] []
  | fun_memsxa_case_1 (a : Nat) (xa_lst : List externaddr) (var_0 : List memaddr) :
    fun_memsxa xa_lst var_0 →
    fun_memsxa ([externaddr.MEM a] ++ xa_lst) ([a] ++ var_0)
  | fun_memsxa_case_2 (v_externaddr : externaddr) (xa_lst : List externaddr) (var_0 : List memaddr) :
    fun_memsxa xa_lst var_0 →
    fun_memsxa ([v_externaddr] ++ xa_lst) var_0


inductive fun_tablesxa : List externaddr → List tableaddr → Prop where
  | fun_tablesxa_case_0 : fun_tablesxa [] []
  | fun_tablesxa_case_1 (a : Nat) (xa_lst : List externaddr) (var_0 : List tableaddr) :
    fun_tablesxa xa_lst var_0 →
    fun_tablesxa ([externaddr.TABLE a] ++ xa_lst) ([a] ++ var_0)
  | fun_tablesxa_case_2 (v_externaddr : externaddr) (xa_lst : List externaddr) (var_0 : List tableaddr) :
    fun_tablesxa xa_lst var_0 →
    fun_tablesxa ([v_externaddr] ++ xa_lst) var_0


inductive fun_funcsxa : List externaddr → List funcaddr → Prop where
  | fun_funcsxa_case_0 : fun_funcsxa [] []
  | fun_funcsxa_case_1 (a : Nat) (xa_lst : List externaddr) (var_0 : List funcaddr) :
    fun_funcsxa xa_lst var_0 →
    fun_funcsxa ([externaddr.FUNC a] ++ xa_lst) ([a] ++ var_0)
  | fun_funcsxa_case_2 (v_externaddr : externaddr) (xa_lst : List externaddr) (var_0 : List funcaddr) :
    fun_funcsxa xa_lst var_0 →
    fun_funcsxa ([v_externaddr] ++ xa_lst) var_0


def fun_store (v_state : state) : store :=
  match v_state with
  | state.mk_state s f => s

inductive store_is_wf : state → store → Prop where
  | store_is_wf_0 (v_state : state) (ret_val : store) :
    wf_state v_state →
    ret_val = (fun_store v_state) →
    wf_store ret_val →
    store_is_wf v_state ret_val


def fun_frame (v_state : state) : frame :=
  match v_state with
  | state.mk_state s f => f

inductive frame_is_wf : state → frame → Prop where
  | frame_is_wf_0 (v_state : state) (ret_val : frame) :
    wf_state v_state →
    ret_val = (fun_frame v_state) →
    wf_frame ret_val →
    frame_is_wf v_state ret_val


def fun_tagaddr (v_state : state) : List tagaddr :=
  match v_state with
  | state.mk_state s f => f.MODULE.TAGS

def fun_moduleinst (v_state : state) : moduleinst :=
  match v_state with
  | state.mk_state s f => f.MODULE

inductive moduleinst_is_wf : state → moduleinst → Prop where
  | moduleinst_is_wf_0 (v_state : state) (ret_val : moduleinst) :
    wf_state v_state →
    ret_val = (fun_moduleinst v_state) →
    wf_moduleinst ret_val →
    moduleinst_is_wf v_state ret_val


def fun_taginst (v_state : state) : List taginst :=
  match v_state with
  | state.mk_state s f => s.TAGS

inductive taginst_is_wf : state → List taginst → Prop where
  | taginst_is_wf_0 (v_state : state) (ret_val_lst : List taginst) :
    wf_state v_state →
    ret_val_lst = (fun_taginst v_state) →
    Forall (fun ret_val_elem => wf_taginst ret_val_elem) ret_val_lst →
    taginst_is_wf v_state ret_val_lst


def fun_globalinst (v_state : state) : List globalinst :=
  match v_state with
  | state.mk_state s f => s.GLOBALS

inductive globalinst_is_wf : state → List globalinst → Prop where
  | globalinst_is_wf_0 (v_state : state) (ret_val_lst : List globalinst) :
    wf_state v_state →
    ret_val_lst = (fun_globalinst v_state) →
    Forall (fun ret_val_elem => wf_globalinst ret_val_elem) ret_val_lst →
    globalinst_is_wf v_state ret_val_lst


def fun_meminst (v_state : state) : List meminst :=
  match v_state with
  | state.mk_state s f => s.MEMS

inductive meminst_is_wf : state → List meminst → Prop where
  | meminst_is_wf_0 (v_state : state) (ret_val_lst : List meminst) :
    wf_state v_state →
    ret_val_lst = (fun_meminst v_state) →
    Forall (fun ret_val_elem => wf_meminst ret_val_elem) ret_val_lst →
    meminst_is_wf v_state ret_val_lst


def fun_tableinst (v_state : state) : List tableinst :=
  match v_state with
  | state.mk_state s f => s.TABLES

inductive tableinst_is_wf : state → List tableinst → Prop where
  | tableinst_is_wf_0 (v_state : state) (ret_val_lst : List tableinst) :
    wf_state v_state →
    ret_val_lst = (fun_tableinst v_state) →
    Forall (fun ret_val_elem => wf_tableinst ret_val_elem) ret_val_lst →
    tableinst_is_wf v_state ret_val_lst


def fun_funcinst (v_state : state) : List funcinst :=
  match v_state with
  | state.mk_state s f => s.FUNCS

inductive funcinst_is_wf : state → List funcinst → Prop where
  | funcinst_is_wf_0 (v_state : state) (ret_val_lst : List funcinst) :
    wf_state v_state →
    ret_val_lst = (fun_funcinst v_state) →
    Forall (fun ret_val_elem => wf_funcinst ret_val_elem) ret_val_lst →
    funcinst_is_wf v_state ret_val_lst


def fun_datainst (v_state : state) : List datainst :=
  match v_state with
  | state.mk_state s f => s.DATAS

inductive datainst_is_wf : state → List datainst → Prop where
  | datainst_is_wf_0 (v_state : state) (ret_val_lst : List datainst) :
    wf_state v_state →
    ret_val_lst = (fun_datainst v_state) →
    Forall (fun ret_val_elem => wf_datainst ret_val_elem) ret_val_lst →
    datainst_is_wf v_state ret_val_lst


def fun_eleminst (v_state : state) : List eleminst :=
  match v_state with
  | state.mk_state s f => s.ELEMS

inductive eleminst_is_wf : state → List eleminst → Prop where
  | eleminst_is_wf_0 (v_state : state) (ret_val_lst : List eleminst) :
    wf_state v_state →
    ret_val_lst = (fun_eleminst v_state) →
    Forall (fun ret_val_elem => wf_eleminst ret_val_elem) ret_val_lst →
    eleminst_is_wf v_state ret_val_lst


def fun_structinst (v_state : state) : List structinst :=
  match v_state with
  | state.mk_state s f => s.STRUCTS

inductive structinst_is_wf : state → List structinst → Prop where
  | structinst_is_wf_0 (v_state : state) (ret_val_lst : List structinst) :
    wf_state v_state →
    ret_val_lst = (fun_structinst v_state) →
    Forall (fun ret_val_elem => wf_structinst ret_val_elem) ret_val_lst →
    structinst_is_wf v_state ret_val_lst


def fun_arrayinst (v_state : state) : List arrayinst :=
  match v_state with
  | state.mk_state s f => s.ARRAYS

inductive arrayinst_is_wf : state → List arrayinst → Prop where
  | arrayinst_is_wf_0 (v_state : state) (ret_val_lst : List arrayinst) :
    wf_state v_state →
    ret_val_lst = (fun_arrayinst v_state) →
    Forall (fun ret_val_elem => wf_arrayinst ret_val_elem) ret_val_lst →
    arrayinst_is_wf v_state ret_val_lst


def fun_exninst (v_state : state) : List exninst :=
  match v_state with
  | state.mk_state s f => s.EXNS

inductive exninst_is_wf : state → List exninst → Prop where
  | exninst_is_wf_0 (v_state : state) (ret_val_lst : List exninst) :
    wf_state v_state →
    ret_val_lst = (fun_exninst v_state) →
    Forall (fun ret_val_elem => wf_exninst ret_val_elem) ret_val_lst →
    exninst_is_wf v_state ret_val_lst


def fof (v_state : state) : frame :=
  fun_frame v_state

inductive fof_is_wf : state → frame → Prop where
  | fof_is_wf_0 (v_state : state) (ret_val : frame) :
    wf_state v_state →
    ret_val = (fof v_state) →
    wf_frame ret_val →
    fof_is_wf v_state ret_val


def fun_type (v_state : state) (v_typeidx : typeidx) : deftype :=
  ((fof v_state).MODULE.TYPES)[proj_uN_0 v_typeidx]!

def sof (v_state : state) : store :=
  fun_store v_state

inductive sof_is_wf : state → store → Prop where
  | sof_is_wf_0 (v_state : state) (ret_val : store) :
    wf_state v_state →
    ret_val = (sof v_state) →
    wf_store ret_val →
    sof_is_wf v_state ret_val


def fun_tag (v_state : state) (v_tagidx : tagidx) : taginst :=
  ((sof v_state).TAGS)[((fof v_state).MODULE.TAGS)[proj_uN_0 v_tagidx]!]!

inductive tag_is_wf : state → tagidx → taginst → Prop where
  | tag_is_wf_0 (v_state : state) (v_tagidx : tagidx) (ret_val : taginst) :
    wf_state v_state →
    wf_uN 32 v_tagidx →
    ret_val = (fun_tag v_state v_tagidx) →
    wf_taginst ret_val →
    tag_is_wf v_state v_tagidx ret_val


def fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
  ((sof v_state).GLOBALS)[((fof v_state).MODULE.GLOBALS)[proj_uN_0 v_globalidx]!]!

inductive global_is_wf : state → globalidx → globalinst → Prop where
  | global_is_wf_0 (v_state : state) (v_globalidx : globalidx) (ret_val : globalinst) :
    wf_state v_state →
    wf_uN 32 v_globalidx →
    ret_val = (fun_global v_state v_globalidx) →
    wf_globalinst ret_val →
    global_is_wf v_state v_globalidx ret_val


def fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
  ((sof v_state).MEMS)[((fof v_state).MODULE.MEMS)[proj_uN_0 v_memidx]!]!

inductive mem_is_wf : state → memidx → meminst → Prop where
  | mem_is_wf_0 (v_state : state) (v_memidx : memidx) (ret_val : meminst) :
    wf_state v_state →
    wf_uN 32 v_memidx →
    ret_val = (fun_mem v_state v_memidx) →
    wf_meminst ret_val →
    mem_is_wf v_state v_memidx ret_val


def fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
  ((sof v_state).TABLES)[((fof v_state).MODULE.TABLES)[proj_uN_0 v_tableidx]!]!

inductive table_is_wf : state → tableidx → tableinst → Prop where
  | table_is_wf_0 (v_state : state) (v_tableidx : tableidx) (ret_val : tableinst) :
    wf_state v_state →
    wf_uN 32 v_tableidx →
    ret_val = (fun_table v_state v_tableidx) →
    wf_tableinst ret_val →
    table_is_wf v_state v_tableidx ret_val


def fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
  ((sof v_state).FUNCS)[((fof v_state).MODULE.FUNCS)[proj_uN_0 v_funcidx]!]!

inductive func_is_wf : state → funcidx → funcinst → Prop where
  | func_is_wf_0 (v_state : state) (v_funcidx : funcidx) (ret_val : funcinst) :
    wf_state v_state →
    wf_uN 32 v_funcidx →
    ret_val = (fun_func v_state v_funcidx) →
    wf_funcinst ret_val →
    func_is_wf v_state v_funcidx ret_val


def fun_data (v_state : state) (v_dataidx : dataidx) : datainst :=
  ((sof v_state).DATAS)[((fof v_state).MODULE.DATAS)[proj_uN_0 v_dataidx]!]!

inductive data_is_wf : state → dataidx → datainst → Prop where
  | data_is_wf_0 (v_state : state) (v_dataidx : dataidx) (ret_val : datainst) :
    wf_state v_state →
    wf_uN 32 v_dataidx →
    ret_val = (fun_data v_state v_dataidx) →
    wf_datainst ret_val →
    data_is_wf v_state v_dataidx ret_val


def fun_elem (v_state : state) (v_tableidx : tableidx) : eleminst :=
  ((sof v_state).ELEMS)[((fof v_state).MODULE.ELEMS)[proj_uN_0 v_tableidx]!]!

inductive elem_is_wf : state → tableidx → eleminst → Prop where
  | elem_is_wf_0 (v_state : state) (v_tableidx : tableidx) (ret_val : eleminst) :
    wf_state v_state →
    wf_uN 32 v_tableidx →
    ret_val = (fun_elem v_state v_tableidx) →
    wf_eleminst ret_val →
    elem_is_wf v_state v_tableidx ret_val


def fun_local (v_state : state) (v_localidx : localidx) : Option val :=
  ((fof v_state).LOCALS)[proj_uN_0 v_localidx]!

inductive local_is_wf : state → localidx → Option val → Prop where
  | local_is_wf_0 (v_state : state) (v_localidx : localidx) (ret_val_opt : Option val) :
    wf_state v_state →
    wf_uN 32 v_localidx →
    ret_val_opt = (fun_local v_state v_localidx) →
    Forall (fun ret_val_elem => wf_val ret_val_elem) (Option.toList ret_val_opt) →
    local_is_wf v_state v_localidx ret_val_opt


def with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
  state.mk_state (sof v_state) ({
    fof v_state with
    LOCALS := List.modify ((fof v_state).LOCALS) (proj_uN_0 v_localidx) (fun elem_1 => some v_val)
  })

inductive with_local_is_wf : state → localidx → val → state → Prop where
  | with_local_is_wf_0 (v_state : state) (v_localidx : localidx) (v_val : val) (ret_val : state) :
    wf_state v_state →
    wf_uN 32 v_localidx →
    wf_val v_val →
    ret_val = (with_local v_state v_localidx v_val) →
    wf_state ret_val →
    with_local_is_wf v_state v_localidx v_val ret_val


def with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
  state.mk_state ({
    sof v_state with
    GLOBALS := List.modify ((sof v_state).GLOBALS) (((fof v_state).MODULE.GLOBALS)[proj_uN_0 v_globalidx]!) (fun elem_1 => {
      elem_1 with
      VALUE := v_val
    })
  }) (fof v_state)

inductive with_global_is_wf : state → globalidx → val → state → Prop where
  | with_global_is_wf_0 (v_state : state) (v_globalidx : globalidx) (v_val : val) (ret_val : state) :
    wf_state v_state →
    wf_uN 32 v_globalidx →
    wf_val v_val →
    ret_val = (with_global v_state v_globalidx v_val) →
    wf_state ret_val →
    with_global_is_wf v_state v_globalidx v_val ret_val


def with_table (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_ref : ref) : state :=
  state.mk_state ({
    sof v_state with
    TABLES := List.modify ((sof v_state).TABLES) (((fof v_state).MODULE.TABLES)[proj_uN_0 v_tableidx]!) (fun elem_1 => {
      elem_1 with
      REFS := List.modify (elem_1.REFS) nat (fun elem_2 => v_ref)
    })
  }) (fof v_state)

inductive with_table_is_wf : state → tableidx → Nat → ref → state → Prop where
  | with_table_is_wf_0 (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_ref : ref) (ret_val : state) :
    wf_state v_state →
    wf_uN 32 v_tableidx →
    wf_ref v_ref →
    ret_val = (with_table v_state v_tableidx nat v_ref) →
    wf_state ret_val →
    with_table_is_wf v_state v_tableidx nat v_ref ret_val


def with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
  state.mk_state ({
    sof v_state with
    TABLES := List.modify ((sof v_state).TABLES) (((fof v_state).MODULE.TABLES)[proj_uN_0 v_tableidx]!) (fun elem_1 => v_tableinst)
  }) (fof v_state)

inductive with_tableinst_is_wf : state → tableidx → tableinst → state → Prop where
  | with_tableinst_is_wf_0 (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) (ret_val : state) :
    wf_state v_state →
    wf_uN 32 v_tableidx →
    wf_tableinst v_tableinst →
    ret_val = (with_tableinst v_state v_tableidx v_tableinst) →
    wf_state ret_val →
    with_tableinst_is_wf v_state v_tableidx v_tableinst ret_val


def with_mem (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : List byte) : state :=
  state.mk_state ({
    sof v_state with
    MEMS := List.modify ((sof v_state).MEMS) (((fof v_state).MODULE.MEMS)[proj_uN_0 v_memidx]!) (fun elem_1 => {
      elem_1 with
      BYTES := ((elem_1.BYTES.take nat) ++ var_0_lst) ++ (elem_1.BYTES.drop (nat + nat_0))
    })
  }) (fof v_state)

inductive with_mem_is_wf : state → memidx → Nat → Nat → List byte → state → Prop where
  | with_mem_is_wf_0 (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : List byte) (ret_val : state) :
    wf_state v_state →
    wf_uN 32 v_memidx →
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val = (with_mem v_state v_memidx nat nat_0 var_0_lst) →
    wf_state ret_val →
    with_mem_is_wf v_state v_memidx nat nat_0 var_0_lst ret_val


def with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
  state.mk_state ({
    sof v_state with
    MEMS := List.modify ((sof v_state).MEMS) (((fof v_state).MODULE.MEMS)[proj_uN_0 v_memidx]!) (fun elem_1 => v_meminst)
  }) (fof v_state)

inductive with_meminst_is_wf : state → memidx → meminst → state → Prop where
  | with_meminst_is_wf_0 (v_state : state) (v_memidx : memidx) (v_meminst : meminst) (ret_val : state) :
    wf_state v_state →
    wf_uN 32 v_memidx →
    wf_meminst v_meminst →
    ret_val = (with_meminst v_state v_memidx v_meminst) →
    wf_state ret_val →
    with_meminst_is_wf v_state v_memidx v_meminst ret_val


def with_elem (v_state : state) (v_elemidx : elemidx) (var_0_lst : List ref) : state :=
  state.mk_state ({
    sof v_state with
    ELEMS := List.modify ((sof v_state).ELEMS) (((fof v_state).MODULE.ELEMS)[proj_uN_0 v_elemidx]!) (fun elem_1 => {
      elem_1 with
      REFS := var_0_lst
    })
  }) (fof v_state)

inductive with_elem_is_wf : state → elemidx → List ref → state → Prop where
  | with_elem_is_wf_0 (v_state : state) (v_elemidx : elemidx) (var_0_lst : List ref) (ret_val : state) :
    wf_state v_state →
    wf_uN 32 v_elemidx →
    Forall (fun var_0_elem => wf_ref var_0_elem) var_0_lst →
    ret_val = (with_elem v_state v_elemidx var_0_lst) →
    wf_state ret_val →
    with_elem_is_wf v_state v_elemidx var_0_lst ret_val


def with_data (v_state : state) (v_dataidx : dataidx) (var_0_lst : List byte) : state :=
  state.mk_state ({
    sof v_state with
    DATAS := List.modify ((sof v_state).DATAS) (((fof v_state).MODULE.DATAS)[proj_uN_0 v_dataidx]!) (fun elem_1 => {
      elem_1 with
      BYTES := var_0_lst
    })
  }) (fof v_state)

inductive with_data_is_wf : state → dataidx → List byte → state → Prop where
  | with_data_is_wf_0 (v_state : state) (v_dataidx : dataidx) (var_0_lst : List byte) (ret_val : state) :
    wf_state v_state →
    wf_uN 32 v_dataidx →
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val = (with_data v_state v_dataidx var_0_lst) →
    wf_state ret_val →
    with_data_is_wf v_state v_dataidx var_0_lst ret_val


def with_struct (v_state : state) (v_structaddr : structaddr) (nat : Nat) (v_fieldval : fieldval) : state :=
  state.mk_state ({
    sof v_state with
    STRUCTS := List.modify ((sof v_state).STRUCTS) v_structaddr (fun elem_1 => {
      elem_1 with
      FIELDS := List.modify (elem_1.FIELDS) nat (fun elem_2 => v_fieldval)
    })
  }) (fof v_state)

inductive with_struct_is_wf : state → structaddr → Nat → fieldval → state → Prop where
  | with_struct_is_wf_0 (v_state : state) (v_structaddr : structaddr) (nat : Nat) (v_fieldval : fieldval) (ret_val : state) :
    wf_state v_state →
    wf_fieldval v_fieldval →
    ret_val = (with_struct v_state v_structaddr nat v_fieldval) →
    wf_state ret_val →
    with_struct_is_wf v_state v_structaddr nat v_fieldval ret_val


def with_array (v_state : state) (v_arrayaddr : arrayaddr) (nat : Nat) (v_fieldval : fieldval) : state :=
  state.mk_state ({
    sof v_state with
    ARRAYS := List.modify ((sof v_state).ARRAYS) v_arrayaddr (fun elem_1 => {
      elem_1 with
      FIELDS := List.modify (elem_1.FIELDS) nat (fun elem_2 => v_fieldval)
    })
  }) (fof v_state)

inductive with_array_is_wf : state → arrayaddr → Nat → fieldval → state → Prop where
  | with_array_is_wf_0 (v_state : state) (v_arrayaddr : arrayaddr) (nat : Nat) (v_fieldval : fieldval) (ret_val : state) :
    wf_state v_state →
    wf_fieldval v_fieldval →
    ret_val = (with_array v_state v_arrayaddr nat v_fieldval) →
    wf_state ret_val →
    with_array_is_wf v_state v_arrayaddr nat v_fieldval ret_val


def add_structinst (v_state : state) (var_0_lst : List structinst) : state :=
  state.mk_state ({
    sof v_state with
    STRUCTS := ((sof v_state).STRUCTS) ++ var_0_lst
  }) (fof v_state)

inductive add_structinst_is_wf : state → List structinst → state → Prop where
  | add_structinst_is_wf_0 (v_state : state) (var_0_lst : List structinst) (ret_val : state) :
    wf_state v_state →
    Forall (fun var_0_elem => wf_structinst var_0_elem) var_0_lst →
    ret_val = (add_structinst v_state var_0_lst) →
    wf_state ret_val →
    add_structinst_is_wf v_state var_0_lst ret_val


def add_arrayinst (v_state : state) (var_0_lst : List arrayinst) : state :=
  state.mk_state ({
    sof v_state with
    ARRAYS := ((sof v_state).ARRAYS) ++ var_0_lst
  }) (fof v_state)

inductive add_arrayinst_is_wf : state → List arrayinst → state → Prop where
  | add_arrayinst_is_wf_0 (v_state : state) (var_0_lst : List arrayinst) (ret_val : state) :
    wf_state v_state →
    Forall (fun var_0_elem => wf_arrayinst var_0_elem) var_0_lst →
    ret_val = (add_arrayinst v_state var_0_lst) →
    wf_state ret_val →
    add_arrayinst_is_wf v_state var_0_lst ret_val


def add_exninst (v_state : state) (var_0_lst : List exninst) : state :=
  state.mk_state ({
    sof v_state with
    EXNS := ((sof v_state).EXNS) ++ var_0_lst
  }) (fof v_state)

inductive add_exninst_is_wf : state → List exninst → state → Prop where
  | add_exninst_is_wf_0 (v_state : state) (var_0_lst : List exninst) (ret_val : state) :
    wf_state v_state →
    Forall (fun var_0_elem => wf_exninst var_0_elem) var_0_lst →
    ret_val = (add_exninst v_state var_0_lst) →
    wf_state ret_val →
    add_exninst_is_wf v_state var_0_lst ret_val


inductive fun_growtable_before_fun_growtable_case_1 : tableinst → Nat → ref → Prop where
  | fun_growtable_case_0 (v_tableinst : tableinst) (v_n : Nat) (r : ref) (tableinst' : tableinst) (i' : uN) («at» : addrtype) (i : u64) (j_opt : Option u64) (rt : reftype) (r'_lst : List ref) :
    ({
      TYPE := tabletype.mk_tabletype «at» (limits.mk_limits i j_opt) rt
      REFS := r'_lst : tableinst
    }) = v_tableinst →
    tableinst' = ({
      TYPE := tabletype.mk_tabletype «at» (limits.mk_limits i' j_opt) rt
      REFS := r'_lst ++ (List.replicate v_n r) : tableinst
    }) →
    (proj_uN_0 i') = ((List.length r'_lst) + v_n) →
    Forall (fun j_3_elem => (proj_uN_0 i') ≤ (proj_uN_0 j_3_elem)) (Option.toList j_opt) →
    ((proj_uN_0 i') : Int) ≤ (((2 ^ (size (numtype_addrtype «at»))) : Int) - (1 : Int)) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype «at» (limits.mk_limits i j_opt) rt
      REFS := r'_lst : tableinst
    }) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype «at» (limits.mk_limits i' j_opt) rt
      REFS := r'_lst ++ (List.replicate v_n r) : tableinst
    }) →
    fun_growtable_before_fun_growtable_case_1 v_tableinst v_n r


inductive fun_growtable : tableinst → Nat → ref → Option tableinst → Prop where
  | fun_growtable_case_0 (v_tableinst : tableinst) (v_n : Nat) (r : ref) (tableinst' : tableinst) (i' : uN) («at» : addrtype) (i : u64) (j_opt : Option u64) (rt : reftype) (r'_lst : List ref) :
    ({
      TYPE := tabletype.mk_tabletype «at» (limits.mk_limits i j_opt) rt
      REFS := r'_lst : tableinst
    }) = v_tableinst →
    tableinst' = ({
      TYPE := tabletype.mk_tabletype «at» (limits.mk_limits i' j_opt) rt
      REFS := r'_lst ++ (List.replicate v_n r) : tableinst
    }) →
    (proj_uN_0 i') = ((List.length r'_lst) + v_n) →
    Forall (fun j_3_elem => (proj_uN_0 i') ≤ (proj_uN_0 j_3_elem)) (Option.toList j_opt) →
    ((proj_uN_0 i') : Int) ≤ (((2 ^ (size (numtype_addrtype «at»))) : Int) - (1 : Int)) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype «at» (limits.mk_limits i j_opt) rt
      REFS := r'_lst : tableinst
    }) →
    wf_tableinst ({
      TYPE := tabletype.mk_tabletype «at» (limits.mk_limits i' j_opt) rt
      REFS := r'_lst ++ (List.replicate v_n r) : tableinst
    }) →
    fun_growtable v_tableinst v_n r (some tableinst')
  | fun_growtable_case_1 (x0 : tableinst) (x1 : Nat) (x2 : ref) :
    ¬ fun_growtable_before_fun_growtable_case_1 x0 x1 x2 →
    fun_growtable x0 x1 x2 none


inductive growtable_is_wf : tableinst → Nat → ref → tableinst → Prop where
  | growtable_is_wf_0 (v_tableinst : tableinst) (nat : Nat) (v_ref : ref) (ret_val : tableinst) (var_0 : Option tableinst) :
    fun_growtable v_tableinst nat v_ref var_0 →
    wf_tableinst v_tableinst →
    wf_ref v_ref →
    var_0 ≠ none →
    ret_val = (Option.get! var_0) →
    wf_tableinst ret_val →
    growtable_is_wf v_tableinst nat v_ref ret_val


inductive fun_growmem_before_fun_growmem_case_1 : meminst → Nat → Prop where
  | fun_growmem_case_0 (v_meminst : meminst) (v_n : Nat) (meminst' : meminst) (i' : uN) («at» : addrtype) (i : u64) (j_opt : Option u64) (b_lst : List byte) :
    ({
      TYPE := memtype.PAGE «at» (limits.mk_limits i j_opt)
      BYTES := b_lst : meminst
    }) = v_meminst →
    meminst' = ({
      TYPE := memtype.PAGE «at» (limits.mk_limits i' j_opt)
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    ((proj_uN_0 i') : Rat) = ((((List.length b_lst) : Rat) / ((64 * Ki) : Rat)) + (v_n : Rat)) →
    Forall (fun j_8_elem => (proj_uN_0 i') ≤ (proj_uN_0 j_8_elem)) (Option.toList j_opt) →
    (proj_uN_0 i') ≤ (2 ^ (Int.toNat (((size (numtype_addrtype «at»)) : Int) - (16 : Int)))) →
    wf_meminst ({
      TYPE := memtype.PAGE «at» (limits.mk_limits i j_opt)
      BYTES := b_lst : meminst
    }) →
    wf_meminst ({
      TYPE := memtype.PAGE «at» (limits.mk_limits i' j_opt)
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    fun_growmem_before_fun_growmem_case_1 v_meminst v_n


inductive fun_growmem : meminst → Nat → Option meminst → Prop where
  | fun_growmem_case_0 (v_meminst : meminst) (v_n : Nat) (meminst' : meminst) (i' : uN) («at» : addrtype) (i : u64) (j_opt : Option u64) (b_lst : List byte) :
    ({
      TYPE := memtype.PAGE «at» (limits.mk_limits i j_opt)
      BYTES := b_lst : meminst
    }) = v_meminst →
    meminst' = ({
      TYPE := memtype.PAGE «at» (limits.mk_limits i' j_opt)
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    ((proj_uN_0 i') : Rat) = ((((List.length b_lst) : Rat) / ((64 * Ki) : Rat)) + (v_n : Rat)) →
    Forall (fun j_8_elem => (proj_uN_0 i') ≤ (proj_uN_0 j_8_elem)) (Option.toList j_opt) →
    (proj_uN_0 i') ≤ (2 ^ (Int.toNat (((size (numtype_addrtype «at»)) : Int) - (16 : Int)))) →
    wf_meminst ({
      TYPE := memtype.PAGE «at» (limits.mk_limits i j_opt)
      BYTES := b_lst : meminst
    }) →
    wf_meminst ({
      TYPE := memtype.PAGE «at» (limits.mk_limits i' j_opt)
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    fun_growmem v_meminst v_n (some meminst')
  | fun_growmem_case_1 (x0 : meminst) (x1 : Nat) :
    ¬ fun_growmem_before_fun_growmem_case_1 x0 x1 →
    fun_growmem x0 x1 none


inductive growmem_is_wf : meminst → Nat → meminst → Prop where
  | growmem_is_wf_0 (v_meminst : meminst) (nat : Nat) (ret_val : meminst) (var_0 : Option meminst) :
    fun_growmem v_meminst nat var_0 →
    wf_meminst v_meminst →
    var_0 ≠ none →
    ret_val = (Option.get! var_0) →
    wf_meminst ret_val →
    growmem_is_wf v_meminst nat ret_val


inductive Num_ok : store → num → numtype → Prop where
  | mk_Num_ok (s : store) (nt : numtype) (c : num_) :
    wf_store s →
    wf_num (num.CONST nt c) →
    Num_ok s (num.CONST nt c) nt


inductive Vec_ok : store → vec → vectype → Prop where
  | mk_Vec_ok (s : store) (vt : vectype) (c : vec_) :
    wf_store s →
    wf_vec (vec.VCONST vt c) →
    Vec_ok s (vec.VCONST vt c) vt


inductive Ref_ok : store → ref → reftype → Prop where
  | null (s : store) :
    wf_store s →
    wf_ref ref.REF_NULL_ADDR →
    wf_reftype (reftype.REF (some null.NULL) heaptype.BOT) →
    Ref_ok s ref.REF_NULL_ADDR (reftype.REF (some null.NULL) heaptype.BOT)
  | i31 (s : store) (i : u31) :
    wf_store s →
    wf_ref (ref.REF_I31_NUM i) →
    wf_reftype (reftype.REF none heaptype.I31) →
    Ref_ok s (ref.REF_I31_NUM i) (reftype.REF none heaptype.I31)
  | struct (s : store) (a : addr) (dt : deftype) :
    a < (List.length (s.STRUCTS)) →
    (((s.STRUCTS)[a]!).TYPE) = dt →
    wf_store s →
    wf_ref (ref.REF_STRUCT_ADDR a) →
    wf_reftype (reftype.REF none (heaptype_deftype dt)) →
    Ref_ok s (ref.REF_STRUCT_ADDR a) (reftype.REF none (heaptype_deftype dt))
  | array (s : store) (a : addr) (dt : deftype) :
    a < (List.length (s.ARRAYS)) →
    (((s.ARRAYS)[a]!).TYPE) = dt →
    wf_store s →
    wf_ref (ref.REF_ARRAY_ADDR a) →
    wf_reftype (reftype.REF none (heaptype_deftype dt)) →
    Ref_ok s (ref.REF_ARRAY_ADDR a) (reftype.REF none (heaptype_deftype dt))
  | func (s : store) (a : addr) (dt : deftype) :
    a < (List.length (s.FUNCS)) →
    (((s.FUNCS)[a]!).TYPE) = dt →
    wf_store s →
    wf_ref (ref.REF_FUNC_ADDR a) →
    wf_reftype (reftype.REF none (heaptype_deftype dt)) →
    Ref_ok s (ref.REF_FUNC_ADDR a) (reftype.REF none (heaptype_deftype dt))
  | exn (s : store) (a : addr) (exn : exninst) :
    a < (List.length (s.EXNS)) →
    ((s.EXNS)[a]!) = exn →
    wf_store s →
    wf_exninst exn →
    wf_ref (ref.REF_EXN_ADDR a) →
    wf_reftype (reftype.REF none heaptype.EXN) →
    Ref_ok s (ref.REF_EXN_ADDR a) (reftype.REF none heaptype.EXN)
  | host (s : store) (a : addr) :
    wf_store s →
    wf_ref (ref.REF_HOST_ADDR a) →
    wf_reftype (reftype.REF none heaptype.ANY) →
    Ref_ok s (ref.REF_HOST_ADDR a) (reftype.REF none heaptype.ANY)
  | extern (s : store) (v_ref : ref) :
    Ref_ok s v_ref (reftype.REF none heaptype.ANY) →
    v_ref ≠ ref.REF_NULL_ADDR →
    wf_store s →
    wf_ref (ref.REF_EXTERN v_ref) →
    wf_reftype (reftype.REF none heaptype.EXTERN) →
    wf_reftype (reftype.REF none heaptype.ANY) →
    wf_ref ref.REF_NULL_ADDR →
    Ref_ok s (ref.REF_EXTERN v_ref) (reftype.REF none heaptype.EXTERN)
  | sub (s : store) (v_ref : ref) (rt : reftype) (rt' : reftype) :
    Ref_ok s v_ref rt' →
    Reftype_ok ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) rt →
    Reftype_sub ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) rt' rt →
    wf_store s →
    wf_ref v_ref →
    wf_reftype rt →
    wf_reftype rt' →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    Ref_ok s v_ref rt


inductive Val_ok : store → val → valtype → Prop where
  | num (s : store) (v_num : num) (nt : numtype) :
    Num_ok s v_num nt →
    wf_store s →
    wf_num v_num →
    Val_ok s (val_num v_num) (valtype_numtype nt)
  | vec (s : store) (v_vec : vec) (vt : vectype) :
    Vec_ok s v_vec vt →
    wf_store s →
    wf_vec v_vec →
    Val_ok s (val_vec v_vec) (valtype_vectype vt)
  | ref (s : store) (v_ref : ref) (rt : reftype) :
    Ref_ok s v_ref rt →
    wf_store s →
    wf_ref v_ref →
    wf_reftype rt →
    Val_ok s (val_ref v_ref) (valtype_reftype rt)


inductive Packval_ok : store → packval → packtype → Prop where
  | mk_Packval_ok (s : store) (pt : packtype) (c : iN) :
    wf_store s →
    wf_packval (packval.PACK pt c) →
    Packval_ok s (packval.PACK pt c) pt


inductive Fieldval_ok : store → fieldval → storagetype → Prop where
  | val (s : store) (v_val : val) (t : valtype) :
    Val_ok s v_val t →
    wf_store s →
    wf_val v_val →
    wf_valtype t →
    Fieldval_ok s (fieldval_val v_val) (storagetype_valtype t)
  | packval (s : store) (v_packval : packval) (pt : packtype) :
    Packval_ok s v_packval pt →
    wf_store s →
    wf_packval v_packval →
    Fieldval_ok s (fieldval_packval v_packval) (storagetype_packtype pt)


inductive Externaddr_ok : store → externaddr → externtype → Prop where
  | tag (s : store) (a : addr) (v_taginst : taginst) :
    a < (List.length (s.TAGS)) →
    ((s.TAGS)[a]!) = v_taginst →
    wf_store s →
    wf_externtype (externtype.TAG (v_taginst.TYPE)) →
    Externaddr_ok s (externaddr.TAG a) (externtype.TAG (v_taginst.TYPE))
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
    wf_externtype (externtype.FUNC (typeuse_deftype (v_funcinst.TYPE))) →
    Externaddr_ok s (externaddr.FUNC a) (externtype.FUNC (typeuse_deftype (v_funcinst.TYPE)))
  | sub (s : store) (v_externaddr : externaddr) (xt : externtype) (xt' : externtype) :
    Externaddr_ok s v_externaddr xt' →
    Externtype_ok ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) xt →
    Externtype_sub ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) xt' xt →
    wf_store s →
    wf_externtype xt →
    wf_externtype xt' →
    wf_context ({
      TYPES := []
      TAGS := []
      GLOBALS := []
      MEMS := []
      TABLES := []
      FUNCS := []
      DATAS := []
      ELEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none
      REFS := []
      RECS := [] : context
    }) →
    Externaddr_ok s v_externaddr xt


inductive fun_inst_valtype : moduleinst → valtype → valtype → Prop where
  | fun_inst_valtype_case_0 (v_moduleinst : moduleinst) (t : valtype) (var_0 : valtype) :
    fun_subst_all_valtype t (Map (fun iter_val_3_elem => typeuse_deftype iter_val_3_elem) (v_moduleinst.TYPES)) var_0 →
    fun_inst_valtype v_moduleinst t var_0


inductive inst_valtype_is_wf : moduleinst → valtype → valtype → Prop where
  | inst_valtype_is_wf_0 (v_moduleinst : moduleinst) (v_valtype : valtype) (ret_val : valtype) (var_0 : valtype) :
    fun_inst_valtype v_moduleinst v_valtype var_0 →
    wf_moduleinst v_moduleinst →
    wf_valtype v_valtype →
    ret_val = var_0 →
    wf_valtype ret_val →
    inst_valtype_is_wf v_moduleinst v_valtype ret_val


inductive fun_inst_reftype : moduleinst → reftype → reftype → Prop where
  | fun_inst_reftype_case_0 (v_moduleinst : moduleinst) (rt : reftype) (var_0 : reftype) :
    fun_subst_all_reftype rt (Map (fun iter_val_4_elem => typeuse_deftype iter_val_4_elem) (v_moduleinst.TYPES)) var_0 →
    fun_inst_reftype v_moduleinst rt var_0


inductive inst_reftype_is_wf : moduleinst → reftype → reftype → Prop where
  | inst_reftype_is_wf_0 (v_moduleinst : moduleinst) (v_reftype : reftype) (ret_val : reftype) (var_0 : reftype) :
    fun_inst_reftype v_moduleinst v_reftype var_0 →
    wf_moduleinst v_moduleinst →
    wf_reftype v_reftype →
    ret_val = var_0 →
    wf_reftype ret_val →
    inst_reftype_is_wf v_moduleinst v_reftype ret_val


inductive fun_inst_globaltype : moduleinst → globaltype → globaltype → Prop where
  | fun_inst_globaltype_case_0 (v_moduleinst : moduleinst) (gt : globaltype) (var_0 : globaltype) :
    fun_subst_all_globaltype gt (Map (fun iter_val_5_elem => typeuse_deftype iter_val_5_elem) (v_moduleinst.TYPES)) var_0 →
    fun_inst_globaltype v_moduleinst gt var_0


inductive inst_globaltype_is_wf : moduleinst → globaltype → globaltype → Prop where
  | inst_globaltype_is_wf_0 (v_moduleinst : moduleinst) (v_globaltype : globaltype) (ret_val : globaltype) (var_0 : globaltype) :
    fun_inst_globaltype v_moduleinst v_globaltype var_0 →
    wf_moduleinst v_moduleinst →
    wf_globaltype v_globaltype →
    ret_val = var_0 →
    wf_globaltype ret_val →
    inst_globaltype_is_wf v_moduleinst v_globaltype ret_val


inductive fun_inst_memtype : moduleinst → memtype → memtype → Prop where
  | fun_inst_memtype_case_0 (v_moduleinst : moduleinst) (mt : memtype) (var_0 : memtype) :
    fun_subst_all_memtype mt (Map (fun iter_val_6_elem => typeuse_deftype iter_val_6_elem) (v_moduleinst.TYPES)) var_0 →
    fun_inst_memtype v_moduleinst mt var_0


inductive inst_memtype_is_wf : moduleinst → memtype → memtype → Prop where
  | inst_memtype_is_wf_0 (v_moduleinst : moduleinst) (v_memtype : memtype) (ret_val : memtype) (var_0 : memtype) :
    fun_inst_memtype v_moduleinst v_memtype var_0 →
    wf_moduleinst v_moduleinst →
    wf_memtype v_memtype →
    ret_val = var_0 →
    wf_memtype ret_val →
    inst_memtype_is_wf v_moduleinst v_memtype ret_val


inductive fun_inst_tabletype : moduleinst → tabletype → tabletype → Prop where
  | fun_inst_tabletype_case_0 (v_moduleinst : moduleinst) (tt : tabletype) (var_0 : tabletype) :
    fun_subst_all_tabletype tt (Map (fun iter_val_7_elem => typeuse_deftype iter_val_7_elem) (v_moduleinst.TYPES)) var_0 →
    fun_inst_tabletype v_moduleinst tt var_0


inductive inst_tabletype_is_wf : moduleinst → tabletype → tabletype → Prop where
  | inst_tabletype_is_wf_0 (v_moduleinst : moduleinst) (v_tabletype : tabletype) (ret_val : tabletype) (var_0 : tabletype) :
    fun_inst_tabletype v_moduleinst v_tabletype var_0 →
    wf_moduleinst v_moduleinst →
    wf_tabletype v_tabletype →
    ret_val = var_0 →
    wf_tabletype ret_val →
    inst_tabletype_is_wf v_moduleinst v_tabletype ret_val
